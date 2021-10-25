#include<R.h>
#include <Rmath.h>
#include<time.h>
#include<stdlib.h>
#include<stdio.h>



void principal(int CONFI[13],double FTOLV[1],double SCAV[1],double FACT1V[1],double ETAV[1],double DES[4500],double GRA[2400],double GRAF[90000],double MAXI[10200],double MINI[10200])
{

// Este programa realiza os c?lculos necess?rios para a elabora??o do VDG, do DVDG, e de seus respectivos FDSs.
  //md=300, mp=15
#define MP 15
#define MD 300
#define NR_END 1
#define FREE_ARG char*
#define TINY 1.0e-20
#define M1 8
#define M2 100
#define MG 142
#define MG2 420
#define PONTOS 60000

//10200=2*(md*(mp+2));
//90000=3*30000;
//2400=2*(md*4);
  
  
  double(TOLERANCIA)=1e-6;
  double(TOLERANCIA2)=1e-3;
  
  int EXECUTE,LNLOOPS,ITMAX,P,ORDER,CUBE,CONF,DF,MAX,RSQC,KP,K1,ITEST,INIT,NPTS3,NWT,PARC,SUBPARC,PRIN,SIMPLX,K,NRHO,NDPTS;
  double PTS[MG][MP],X[M1],X0[M2],XDC[M2],PTS2[MG][MP],PTS3[MG2][MP],XMAT[M2][M2],D[MD][M2],XBEST[MP],FACT1,SCA,FTOL,ETA,GRAPH[MD][4],MAXIMUM[MD][9],MINIMUM[MD][9];
  
  SIMPLX=CONFI[0];
  NDPTS=CONFI[1];
  K=CONFI[2];
  ORDER=CONFI[3];
  CUBE=CONFI[4];
  NWT=CONFI[5];
  NRHO=CONFI[6];
  CONF=CONFI[7];
  PARC=CONFI[8];
  SUBPARC=CONFI[9];
  PRIN=CONFI[10];
  LNLOOPS=CONFI[11];
  ITMAX=CONFI[12];
  P=CONFI[13];
  FTOL=FTOLV[0];
  SCA=SCAV[0];
  FACT1=FACT1V[0];
  ETA=ETAV[0];
  
 void hpsort(int n, double ra[PONTOS][2])
  {
    int i,ir,j,l;
    double rra;
	
	if(n<2)return;
	l=(n>>1)+1;
	ir=n;
	for(;;){
	   if(l>1){
	      rra=ra[--l-1][1];
		}else{
		   rra=ra[ir-1][1];
		   ra[ir-1][1]=ra[0][1];
		   if(--ir==1){
		      ra[0][1]=rra;
			  break;
			}
	    }
		i=l;
		j=l+l;
		while(j<=ir){
		    if(j<ir && ra[j-1][1]<ra[j+1-1][1])j++;
			if(rra<ra[j-1][1]){
			   ra[i-1][1]=ra[j-1][1];
			   i=j;
			   j<<=1;
			}else break;
	    }
		ra[i-1][1]=rra;
	}
  }
		  
  
  void LUDCMP (double A[M2][M2],int N,int INDX[M2],double *D)
  {
    //Esta fun??o realiza a decomposi??o LU da matriz A[M2][M2], guardando os efeitos de permuta??o de linha por pivoteamento parcial em INDX[M2]. D ter? valor de +1 ou -1 se o n?mero de permuta??es realizadas for par ou ?mpar, respectivamente.
	
    int I,IMAX,J,KX;
    double BIG,DUM,SUM,TEMP;
    double VV[N]; 
    IMAX=0;
    *D=1.;
    for(I=0;I<N;I++)
      {
	BIG=0.0;
	for(J=0;J<N;J++)
	  {
	    if((TEMP=fabs(A[I][J]))>BIG)BIG=TEMP;
	  }
	if(BIG==0.0)Rprintf("Singular matrix in routine LUDCMP");
	VV[I]=1./BIG;
      }
    for(J=0;J<N;J++)
      {
	for(I=0;I<J;I++)
	  {
	    SUM=A[I][J];
	    for(KX=0;KX<I;KX++)
	      {
		SUM-=A[I][KX]*A[KX][J];
	      }
	    A[I][J]=SUM;
	  }
	BIG=0.0;
	for(I=J;I<N;I++)
	  {
	    SUM=A[I][J];
	    for(KX=0;KX<J;KX++)
	      {
		SUM-=A[I][KX]*A[KX][J];
	      }
	    A[I][J]=SUM;
	    
	    if((DUM=VV[I]*fabs(SUM))>=BIG)
	      {
		BIG=DUM;
		IMAX=I;
	      }
	  }
	if(J!=IMAX)
	  {
	    for(KX=0;KX<N;KX++)
	      {
		DUM=A[IMAX][KX];
		A[IMAX][KX]=A[J][KX];
		A[J][KX]=DUM;
	      }
	    *D=-(*D);
	    VV[IMAX]=VV[J];
	  }
	INDX[J]=IMAX;
	if(A[J][J]==0.0)A[J][J]=TINY;
	if(J!=N)
	  {
	    DUM=1./(A[J][J]);
	    for(I=J+1;I<N;I++)A[I][J]*=DUM;
	  }
      }
  }
  
  void LUBKSB(double A[M2][M2],int N,int INDX[M2],double B[M2])
  {
    //Resolve o sistema AX=B, sendo A a matriz retornada da decomposi??o LU, e INDX o vetor com as informa??es de permuta??o de linhas retornado pela fun??o LUDMCM(), B ? um vetor de entrada que depende do sistema a ser resolvido, mas ? tamb?m ? usado para retornar X encontrado ao t?rmino desta fun??o.
    int I,II=0,IP,J;
    double SUM;
    
    for(I=1;I<=N;I++)
      {
	IP=INDX[I-1];
	SUM=B[IP];
	B[IP]=B[I-1];
	if(II!=0)
	  for(J=II;J<=I;J++) SUM -= A[I-1][J-1]*B[J-1];
	else if(SUM!=0) II=I;
	B[I-1]=SUM;
      }
    for(I=(N);I>=1;I--)
      {
	SUM=B[I-1];
	for(J=(I+1);J<=N;J++) SUM -= A[I-1][J-1]*B[J-1];
	B[I-1] = SUM/A[I-1][I-1];
      }
  }
  
  void NVERT(double A[M2][M2],double AINV[M2][M2],int INDX[M2],int DIMA)
  {
    
    //Inverte a matriz A[M2][M2] atrav?s da decomposi??o LU e resolu??o de sistema. A matriz invertida ? retornada em AINV[M2][M2].
    
    int I,J;
    double P,B[M2];
    LUDCMP(A,DIMA,INDX,&P);
    for(J=0;J<DIMA;J++)
      {   
	for(I=0;I<DIMA;I++)
	  {  
	    B[I] =0.0;
	  }
	B[J]=1.0;
	LUBKSB(A,DIMA,INDX,B);
	for(I=0;I<DIMA;I++)
	  {
	    AINV[I][J]=B[I];
	  }
      }
  }
  
  void OBTV(double V[M2][M2],double ETA, int *IZ)
  {
    //Obt?m a matriz V para o caso de parcelas subdivididas
    
    int I,J,I2,Z[M2][M2],ZZT[M2][M2],IDENTIDADE[PARC][PARC],IDENTIDADE2[M2][M2],UNITARIA[SUBPARC];
    for(I=0;I<PARC;I++)
      {
	for(J=0;J<PARC;J++)
	  {
	    IDENTIDADE[I][J]=0;
	  }
      }
    for(I=0;I<PARC;I++)
      {
	IDENTIDADE[I][I]=1;
      }
    for(I=0;I<SUBPARC;I++)
      {
	UNITARIA[I]=1;
      }
    *IZ=0; 
    for(I=0;I<PARC;I++)
      {
	for(J=0;J<PARC;J++)
	  {
	    
	    for(I2=0;I2<SUBPARC;I2++)
	      {
		Z[*IZ+I2][J]=UNITARIA[I2]*IDENTIDADE[I][J];  
	      } 
	  }  
	*IZ=*IZ+SUBPARC;      
      }
    for (I=0;I<*IZ;I++)
      {
	for(J=0;J<*IZ;J++)
	  {
	    ZZT[I][J]=0.0;
	    for(I2=0;I2<PARC;I2++)
	      {
		ZZT[I][J]=ZZT[I][J]+Z[I][I2]*Z[J][I2];
	      }
	  }
      }
    for(I=0;I<*IZ;I++)
      {
	for(J=0;J<*IZ;J++)
	  {
	    IDENTIDADE2[I][J]=0;
	  }
	IDENTIDADE2[I][I]=1;
      }
    for(I=0;I<*IZ;I++)
      {
	for(J=0;J<*IZ;J++)
	  {
	    V[I][J]=IDENTIDADE2[I][J]+ETA*ZZT[I][J];
	  }
      } 
  }
  
  void REJECT(double *RSQ, int *FLAG)
  {
    
    //Determina se o ponto proposto recai sobre a hiperesfera de interesse
    
    int J;
    double XLAST;
    
    *FLAG=0;
    XLAST = *RSQ;
    for(J=1;J<K;J++)
      {
	XLAST=XLAST-X[J]*X[J];
      }
    if(XLAST<0.)
      {
	*FLAG=1;
      }
    else
      {
	X[KP-1]=sqrt(XLAST);
      }
  }
  
  
  
  void MXPAND()
  {
    
    //Expande o vetor X de acordo com o modelo de regress?o linear escolhido pelo usu?rio. O vetor expandido ? retornado em X0.
    
    int I,INDEX,I2,J;
    
    //Se o modelo ? de primeira ordem a expan??o n?o ? requerida
    
    for(I=0;I<KP;I++)
      {
	   X0[I]=X[I];
      }
    
    if(ORDER!=1)
      {
	
	    //Cria os termos quadr?ticos puros para o modelo de segunda ordem
	
	    INDEX=K;
	    for(I=1;I<KP;I++)
	     {
	      INDEX=INDEX+1;
	      X0[INDEX]= X[I]*X[I];
	     }
	
	    //Cria a intera??o entre dois fatores
	
	    for(I=1;I<K;I++)
	     {
	      I2=I+1;
	      for(J=I2;J<KP;J++)
	       {
		    INDEX=INDEX+1;
		    X0[INDEX] = X[I]*X[J];
	       }
	     }
      }
  }
  
  void VMULT(double *VALUE)
  {
    
    //Calcula a vari?ncia da predi??o
    
    int I,J;
    double RIGHT,XD[M2];
    
    MXPAND();
    *VALUE=0.0;
    if((DF==0)||(DF==2))
      {
	   //Calcula a vari?ncia da predi??o para o VDG e seu respectivo FDS.
	   for(I=0;I<K1;I++)
	    {
	     RIGHT=0.0;
	     for(J=0;J<K1;J++)
	      {
		   RIGHT=RIGHT+X0[J]*XMAT[J][I];
	      }
	     *VALUE = *VALUE+RIGHT*X0[I];
	    }
      }
    else if((DF==1)||(DF==3))
      { 
	   //Calcula a vari?ncia da predi??o para o DVDG e seu respectivo FDS.
	   if(RSQC==1)
	   {
	    for(I=0;I<K1;I++)
	     {
		  XDC[I]=X0[I];
	     }
	    RSQC=0;
	   }
	   for(I=0;I<K1;I++)
	    {
	     XD[I]=X0[I]-XDC[I];
	    }
	
	   for(I=0;I<K1;I++)
	    {
	     RIGHT=0.0;
	     for(J=0;J<K1;J++)
	      {
		   RIGHT=RIGHT+XD[J]*XMAT[J][I];
	      }
	     *VALUE = *VALUE+RIGHT*XD[I];
	    }
      }
  }
  
  
  void EVAL(double *VALUE)
  {
    //Determina o valor para a k-?sima vari?vel requerida para localizar o 
    // ponto na hiperesfera de interesse
    
    double VALUE2;
    
    MXPAND();
    VMULT(&VALUE2);
    X[KP-1]=-X[KP-1];
    MXPAND();
    VMULT(VALUE);
    if (VALUE2<(*VALUE))
      {
	   X[KP-1]=-X[KP-1];
	   *VALUE=VALUE2;
      }
    if(MAX==0)
      {
	   *VALUE=-*VALUE;
      }
    
  }
  
  void AMOEBA(double *RSQ,double *VALUE)
  {
    
    double(ALPHA)=1.0;
    double(BETA)=0.5;
    double(GAMMA)=2.0;
    
    int J,I,J2,I2,FLAG,NDIM,MPTS,ITER,ILO,IHI,INHI;
    double FUNK,VALUE2,P[M1][MP],Y[M1],PR[M1],PRR[M1],PBAR[M1],FACT,RTOL,YPR,YPRR;
    
    
    //Esta rotina realiza a busca utilizando o m?todo Simplex de Nelder-Mead. Essencialmente ela ? uma 
    //rotina apresentada no Numerical Recipes (1986). O procedimento foi  
    //modificado para realizar a busca no espa?o dimensional K-1.
    
    NDIM=K-1;
    MPTS=K;
    ITER=0;
    X[0]=1.0;
    X0[0]=1.0;
    for(J=0;J<NDIM;J++)
      {
	   J2=J+1;
	   P[0][J]=X[J2];
      }
    REJECT(RSQ,&FLAG);
    EVAL(&VALUE2);
    Y[0]=VALUE2;
    FACT=0.25*sqrt(*RSQ);
    for(I=1;I<MPTS;I++)
      {
	   for(J=0;J<NDIM;J++)
	    {
	     P[I][J]=0.0;
	    }
	   I2=I-1;
	   P[I][I2]=FACT;
	   for(J=0;J<NDIM;J++)
	    {
	     J2=J+1;
	     X[J2]=P[I][J];
	    }
	   REJECT(RSQ,&FLAG);
	   EVAL(&VALUE2);
	   Y[I]=VALUE2;
      }    
    GOTO50:
    ILO=0;
    if(Y[0]>Y[1])
     {
	  IHI=0;
	  INHI=1;
     }
    else
     {
	  IHI=1;
	  INHI=0;
     }
    for(I=0;I<MPTS;I++)
     {
	  if(Y[I]<Y[ILO])
	   {
	    ILO=I;
	   }
	  if(Y[I]>Y[IHI])
	   {
	    INHI=IHI;
	    IHI=I;
	   }
	  else if(Y[I]>Y[INHI])
	   {
	    if(I!=IHI)
	     {
		  INHI=0;
	     }
	   }
     }
    
    
    RTOL=2.*fabs(Y[IHI]-Y[ILO])/(fabs(Y[IHI])+fabs(Y[ILO]));
    if(RTOL<FTOL)
     {
	  for(J=0;J<NDIM;J++)
	   {
	    J2=J+1;
	    X[J2]=P[ILO][J];
	   }
	  REJECT(RSQ,&FLAG);
	  EVAL(VALUE);
	  return;
     }
    
    if(ITER>=ITMAX)
     {
	  if(SIMPLX==1)
	   {
	    Rprintf("Problem encountered in AMOEBA\n");
	    Rprintf("You may wish to change either FTOL or ITMAX in AMOEBA\n");
	    Rprintf("Current values are:  ,FTOL=%10.6lf, ITMAX=%5d \n",FTOL,ITMAX);
            Rprintf("The problem may also be solved by changing the SEARCH to option 2"); 
	   }
	for(J=0;J<NDIM;J++)
	 {
	  J2=J+1;
	  X[J2]=P[ILO][J];
	 }
	REJECT(RSQ,&FLAG);
	EVAL(VALUE);
	return;
     }
    ITER=ITER+1;
    for(J=0;J<NDIM;J++)
     {
	  PBAR[J]=0.0;
     }
    for(I=0;I<MPTS;I++)
     {
	  if(I!=IHI)
	   {
	    for(J=0;J<NDIM;J++)
	     {
		  PBAR[J]=PBAR[J]+P[I][J];
	     }
	   }
     }
    for(J=0;J<NDIM;J++)
     {
	  PBAR[J]=PBAR[J]/((double)NDIM);
	  PR[J]=(1.+ALPHA)*PBAR[J]-ALPHA*P[IHI][J];
	  J2=J+1;
	  X[J2]=PR[J];
     }
    REJECT(RSQ,&FLAG);
    if(FLAG!=1)
     {
	  EVAL(&YPR);
     }
    else
     {
	  YPR=Y[IHI]+1.;
     }
    if(YPR<=Y[ILO])
     {
	  for(J=0;J<NDIM;J++)
	   {
	    PRR[J]=GAMMA*PR[J]-(1.0-GAMMA)*PBAR[J];
	    J2=J+1;
	    X[J2]=PRR[J];
	   }
	  REJECT(RSQ,&FLAG);
	  if(FLAG!=1)
	   {
	    EVAL(&YPRR);
	   }
	  else
	   {
	    YPRR=Y[IHI]+1.;
	   }
	  if(YPRR<Y[ILO])
	   {
	    for(J=0;J<NDIM;J++)
	     {
		  P[IHI][J]=PRR[J];
	     }
	    Y[IHI]=YPRR;
	   }
	  else
	   {
	    for(J=0;J<NDIM;J++)
	     {
		  P[IHI][J]=PR[J];
	     }
	    Y[IHI]=YPR;
	   }
     }
    
    else if(YPR>=Y[INHI])
     {
	  if(YPR<Y[IHI])
	   {
	    for(J=0;J<NDIM;J++)
	     {
		  P[IHI][J]=PR[J];
	     }
	    Y[IHI]=YPR;
	   }
	  for(J=0;J<NDIM;J++)
	   {	
	    PRR[J]=BETA*P[IHI][J]+(1.0-BETA)*PBAR[J];
	    J2=J+1;
	    X[J2]=PRR[J];
	   }
	  REJECT(RSQ,&FLAG);
	  if(FLAG!=1)
	   {
	    EVAL(&YPRR);
	   }
	  else
	   {
	    YPRR=Y[IHI]+1.;
	   }
	  if(YPRR<Y[IHI])
	   {
	    for(J=0;J<NDIM;J++)
	     {
		  P[IHI][J]=PRR[J];
	     }
	    Y[IHI]=YPRR;
	   }
	  else
	   {
	    for(I=0;I<MPTS;I++)
	     {
		  if(I!=ILO)
		   {
		    for(J=0;J<NDIM;J++)
		     {
			  PR[J]=0.5*(P[I][J]+P[ILO][J]);
			  P[I][J]=PR[J];
			  J2=J+1;
			  X[J2]=PR[J];
		     }
		    REJECT(RSQ,&FLAG);
		    if(FLAG!=1)
		     {
			  EVAL(&FUNK);
		     }
		    else
		     {
			  FUNK=Y[IHI]+1.0;
		     }
		    Y[I]=FUNK;
		   }
	     }
	   }
     }
    else
     {
	  for(J=0;J<NDIM;J++)
	   {
	    P[IHI][J]=PR[J];
	   }
	  Y[IHI]=YPR;
     }
    goto GOTO50;     
    
  }
  
  void BMAT(int NDPTS)
  {
    int I,J,I2,INDX[M2],IZ;
    double X11MAT[M2][M2],X11MAT0[M2][M2],V[M2][M2],VINV[M2][M2];
    
    if (CONF==0)
     {  
	   //Forma a matriz (D'D) para experimentos inteiramente ao acaso.
	
	   for (I=0;I<K1;I++)
	    {
	     for(J=0;J<K1;J++)
	      {
		   X11MAT[I][J]=0.0;
		   for(I2=0;I2<NDPTS;I2++)
		    {
		     X11MAT[I][J]=X11MAT[I][J]+D[I2][I]*D[I2][J];
		    }
	      }
	    }
     }
    else if(CONF==1)
      {
	   //Forma a matriz (D'V^{-1}D) para experimentos em dois estratos.
	
	   if(NDPTS!=(PARC*SUBPARC))
	    {
	     Rprintf("The value of NWPT and NSPT are not compatible with the rows number of the design!\n");
	     EXECUTE=1;
	     return;
	    } 
	   //Obtendo a matriz V^{-1}
	   OBTV(V,ETA,&IZ);
	   NVERT(V,VINV,INDX,IZ);
	   for (I=0;I<K1;I++)
	    {
	     for(J=0;J<NDPTS;J++)
	      {
		   X11MAT0[I][J]=0.0;
		   for(I2=0;I2<NDPTS;I2++)
		    {
		     X11MAT0[I][J]=X11MAT0[I][J]+D[I2][I]*VINV[I2][J];
		    }
	      }
	    }
	   for (I=0;I<K1;I++)
	    {
	     for(J=0;J<K1;J++)
	      {
		   X11MAT[I][J]=0.0;
		   for(I2=0;I2<NDPTS;I2++)
		    {
		     X11MAT[I][J]=X11MAT[I][J]+X11MAT0[I][I2]*D[I2][J];
		    }
	      }
	    }
      }
	else
	 {
	  Rprintf("The specified value for DES.TYPE is not valid!\n");
      EXECUTE=1;
	 }
	//Invertendo a matriz de informa??o para obter a de vari?ncias e covari?ncias
    NVERT(X11MAT,XMAT,INDX,K1);
  }
  
  void VSPH(double *VALUE, double *RSQ)
  {
    
    //Encontra a vari?ncia esf?rica m?dia da predi??o sobre uma  hiperesfera 
    //de um dado raio
        
    int I,J,I2,J2,FLAG,KLOC,KLOC2;
    double P[M2][M2],P2[M2][M2],DENOM,DENOM2;
    
    //Encontra a vari?ncia esf?rica para o caso de primeira ordem
    
    FLAG=0;
    if(DF==0)
     {
	  //Se ? VDG
	  if(ORDER==1)
	   {
	    *VALUE=XMAT[0][0];
	    for(I=1;I<KP;I++)
	     {
		  DENOM=(double)K;
		  *VALUE = *VALUE+XMAT[I][I]*(*RSQ)/DENOM;
	     }
	    FLAG=1;
	   }
	
	  //Encontra a vari?ncia esf?rica para o caso de segunda ordem
	
	  if(FLAG==0)
	   {
	    for(I=0;I<K1;I++)
	     {
		  for(J=0;J<K1;J++)
		   {
		    P[I][J]=0.0;
		   }
	     }
	    DENOM=(double)K;
	    DENOM2=(double)K*((double)K+2.);
	    P[0][0]=1.0;
	    for(I=0;I<K;I++)
	     {
		  I2=I+1;
		  P[I2][I2]=(*RSQ)/DENOM;
		  KLOC=KP+I;
		  P[0][KLOC]=(*RSQ)/DENOM;
		  P[KLOC][0]=(*RSQ)/DENOM;
		  for(J=0;J<K;J++)
		   {
		    KLOC2=KP+J;
		    P[KLOC][KLOC2]=(*RSQ)*(*RSQ)/DENOM2;
		   }
		  P[KLOC][KLOC]=3.*P[KLOC][KLOC];
	     }
	    //Inicia P para a se??o correspondente a intera??o entre dois fatores
	    KLOC=1+2*K;
	    for(I=KLOC;I<K1;I++)
	     {
		  P[I][I]=(*RSQ)*(*RSQ)/DENOM2;
	     }
	    for(I=0;I<K1;I++)
	     {
		  for(J=0;J<K1;J++)
		   {
		    P2[I][J]=0.0;
		    for(J2=0;J2<K1;J2++)
		     {
			  P2[I][J]=P2[I][J]+P[I][J2]*XMAT[J2][I];
		     }
		   }
	     }
	    //Encontra a vari?ncia esf?rica m?dia, que est? sobre o tra?o de P*XMAT
	    *VALUE=0.0;
	    for(I=0;I<K1;I++)
	     {
		  *VALUE = (*VALUE+P2[I][I]);
	     }
	   }
     }
    else if (DF==1)
     {
	  //Se ? DVDG
	  if(ORDER==1)
	   {
	    *VALUE=0.;
	    for(I=1;I<KP;I++)
	     {
		  DENOM=(double)K;
		  *VALUE = *VALUE+XMAT[I][I]*(*RSQ)/DENOM;
	     }
	    FLAG=1;
	   }
	
	  //Encontra a vari?ncia esf?rica para o caso de segunda ordem
	
	  if(FLAG==0)
	   {
	    for(I=0;I<K1;I++)
	     {
		  for(J=0;J<K1;J++)
		   {
		    P[I][J]=0.0;
		   }
	     }
	    DENOM=(double)K;
	    DENOM2=(double)K*((double)K+2.);
	    for(I=0;I<K;I++)
	     {
		  I2=I+1;
		  P[I2][I2]=(*RSQ)/DENOM;
		  KLOC=KP+I;
		  for(J=0;J<K;J++)
		   {
		    KLOC2=KP+J;
		    P[KLOC][KLOC2]=(*RSQ)*(*RSQ)/DENOM2;
		   }
		  P[KLOC][KLOC]=3.*P[KLOC][KLOC];
	     }
	    	    
	    //Inicia P para a se??o correspondente a intera??o entre dois fatores
	    
	    KLOC=1+2*K;
	    for(I=KLOC;I<K1;I++)
	     {
		  P[I][I]=(*RSQ)*(*RSQ)/DENOM2;
	     }
	    for(I=0;I<K1;I++)
	     {
		  for(J=0;J<K1;J++)
		   {
		    P2[I][J]=0.0;
		    for(J2=0;J2<K1;J2++)
		     {
			  P2[I][J]=P2[I][J]+P[I][J2]*XMAT[J2][I];
		     }
		   }
	     }
	    	    
	    //Encontra a vari?ncia esf?rica, que est? sobre o tra?o de P*XMAT
	    
	    *VALUE=0.0;
	    for(I=0;I<K1;I++)
	     {
		  *VALUE = (*VALUE+P2[I][I]);
	     }
	   }
     }
    return;
  }
  
  void NEWXK(double *STEP,double *R)
  {
    double THETA1,THETA2;
    
    //Determina a grade para a parte flutuante da busca, onde K=2
    
    THETA1=cos(XBEST[0]/(*R));
    THETA2=sin((*STEP)/(*R));
    NPTS3=2;
    PTS3[0][0]=(*R)*cos(THETA1+THETA2);
    PTS3[0][1]=(*R)*sin(THETA1+THETA2);
    PTS3[1][0]=(*R)*cos(THETA1-THETA2);
    PTS3[1][1]=(*R)*sin(THETA1-THETA2);
    
  }
  
  
  void NEWX(double *STEP,double *R2)
  {
    
    int KOUNT,J3,J4,J5,KPOS,KPOS1,KPOS2,KPOS3,KPOS4,INDEX,LDEX,STEP2;
    double MAXLEN,R,DIST,C3,C4,THETA,TEMP1,TEMP2,C2,SUM;
    
    //Determina a grade para a por??o flutuante da pesquisa
    
    MAXLEN=sqrt(1.0/(double)K);
    R=sqrt(*R2);
    if(K==2) NEWXK(STEP,&R);
    if(K!=2) 
     {
	  DIST=(*STEP)*(*STEP)/(2.*(*R2));
	  STEP2=(*R2)*(2.*DIST-DIST*DIST)*sqrt(.75);
	  KOUNT=0;
	  for(J3=1;J3<=(K-1);J3++)
	   {
	    for(J4=(J3+1);J4<=K;J4++)
	     {
		  for(J5=1;J5<=K;J5++)
		   {
		    if(J5==J3) goto nextJ5;
		    if(J5==J4) goto nextJ5;
		    KPOS=4*KOUNT;
		    KOUNT=KOUNT+1;
		    KPOS1=KPOS+1;
		    KPOS2=KPOS+2;
		    KPOS3=KPOS+3;
		    KPOS4=KPOS+4;
		    for(INDEX=0;INDEX<K;INDEX++)
		     {
			  PTS3[KPOS1-1][INDEX]=XBEST[INDEX];
			  PTS3[KPOS2-1][INDEX]=XBEST[INDEX];
			  PTS3[KPOS3-1][INDEX]=XBEST[INDEX];
			  PTS3[KPOS4-1][INDEX]=XBEST[INDEX];
		     }
		    
		    //Calcula o valor inicial para os dois modelos vari?veis escolhidos 
		    //para construir a parte fatorial
		    
		    C3=XBEST[J3-1]*(1.-DIST);
		    C4=XBEST[J4-1]*(1.-DIST);
		    
		    //Calcula o ?ngulo requerido para a rela??o geom?trica e encontra o 
		    //maior e o menor n?vel para os fatores, e ent?o constr?i o primeiro 
		    //ponto nesta parte.
		    
		    if(fabs(C3)<TOLERANCIA) THETA=0.7854;
		    else THETA=atan(C4/C3);
		    TEMP1=C3+STEP2*sin(THETA);
		    TEMP2=C4-STEP2*cos(THETA);
		    C2=(*R2)-TEMP1*TEMP1-TEMP2*TEMP2;
		    SUM=0.0;
		    for(LDEX=0;LDEX<K;LDEX++)
		     {
			  if((LDEX!=(J3-1)) && (LDEX!=(J4-1)) && (LDEX!=(J5-1)))
			   {
			    SUM=SUM+XBEST[LDEX]*XBEST[LDEX];
			   }
		     }
		    C2=C2-SUM;
		    if(C2<0.) goto TEMP40;
		    if(CUBE!=1) goto C230;
		    if(C2>MAXLEN) goto TEMP40;
		    if(fabs(TEMP1)>MAXLEN) goto TEMP40;
		    if(fabs(TEMP2)>MAXLEN) goto TEMP40;
		  C230:
		    C2=sqrt(C2);
		    if((CUBE==1)&&(C2>MAXLEN)) goto TEMP40;
		    if(XBEST[J5-1]<0.) C2=-C2;
		    PTS3[KPOS1-1][J3-1]=TEMP1;
		    PTS3[KPOS1-1][J4-1]=TEMP2;
		    PTS3[KPOS1-1][J5-1]=C2;
		    
		    //Construir o segundo ponto
		  TEMP40:
		    TEMP1=C3-STEP2*sin(THETA);
		    TEMP2=C4+STEP2*cos(THETA);
		    C2=(*R2)-TEMP1*TEMP1-TEMP2*TEMP2;
		    C2=C2-SUM;					  
		    if(C2<0.) goto TEMP60;
		    if(CUBE!=1) goto C250;
		    if(C2>MAXLEN) goto TEMP60;
		    if(fabs(TEMP1)>MAXLEN) goto TEMP60;
		    if(fabs(TEMP2)>MAXLEN) goto TEMP60;
		  C250:
		    C2=sqrt(C2);
		    if((CUBE==1)&&(C2>MAXLEN)) goto TEMP60;
		    if(XBEST[J5-1]<0.) C2=-C2;
		    PTS3[KPOS2-1][J3-1]=TEMP1;
		    PTS3[KPOS2-1][J4-1]=TEMP2;
		    PTS3[KPOS2-1][J5-1]=C2;
		    
		    //Construir o terceiro ponto
		  TEMP60:
		    TEMP1=C3-STEP2*sin(THETA);
		    TEMP2=C4-STEP2*cos(THETA);
		    C2=(*R2)-TEMP1*TEMP1-TEMP2*TEMP2;
		    C2=C2-SUM;			
		    if(C2<0.) goto TEMP80;
		    if(CUBE!=1) goto C270;
		    if(C2>MAXLEN) goto TEMP80;
		    if(fabs(TEMP1)>MAXLEN) goto TEMP80;
		    if(fabs(TEMP2)>MAXLEN) goto TEMP80;
		  C270:
		    C2=sqrt(C2);
		    if((CUBE==1)&&(C2>MAXLEN)) goto TEMP80;
		    if(XBEST[J5-1]<0.) C2=-C2;
		    PTS3[KPOS3-1][J3-1]=TEMP1;
		    PTS3[KPOS3-1][J4-1]=TEMP2;
		    PTS3[KPOS3-1][J5-1]=C2;
		    
		    //Construir o quarto ponto
		  TEMP80:
		    TEMP1=C3+STEP2*sin(THETA);
		    TEMP2=C4+STEP2*cos(THETA);
		    C2=(*R2)-TEMP1*TEMP1-TEMP2*TEMP2;
		    C2=C2-SUM;			
		    if(C2<0.) goto nextJ5;
		    if(CUBE!=1) goto C290;
		    if(C2>MAXLEN) goto nextJ5;
		    if(fabs(TEMP1)>MAXLEN) goto nextJ5;
		    if(fabs(TEMP2)>MAXLEN) goto nextJ5;
		  C290:
		    C2=sqrt(C2);
		    if((CUBE==1)&&(C2>MAXLEN)) goto nextJ5;
		    if(XBEST[J5-1]<0.) C2=-C2;
		    PTS3[KPOS4-1][J3-1]=TEMP1;
		    PTS3[KPOS4-1][J4-1]=TEMP2;
		    PTS3[KPOS4-1][J5-1]=C2;
		  nextJ5:
		    C2=C2;
		   }
	     }
	   }
	  NPTS3=4*KOUNT;
     }
  }
  
  void NEWX2(int *SAVE,double *STEP, double *R2)
  { 
    int I;
    
    //Encontra a melhor estimativa atual para m?ximo ou m?nimo xbest atual e 
    //ent?o inicia em cima de outra grade a parte flutuante da pesquisa.
    
    for(I=0;I<K;I++)
      {
	   XBEST[I]=PTS3[*SAVE][I];
      }
    NEWX(STEP,R2);
  }
  
  void MINLOC(double *ROLD, double *R2, double *RSQ, double *BEST, int NPTSF, int NPTSA)
  {
    // Encontra a vari?ncia da predi??o m?nima sobre uma hiperesfera de um dado raio.
    
    
    int TRUNC,J,J2,J3,JZ,I,J1,OVER[MP],SAVE,FLAG,FLAG2,NUM,JDEX,NEND,NLOOPS;
    double MAXLEN,MAX2,PROP[MP],TEMP2[MP],R,RP,RP2,SUM,PROP2,TEMP,TEMP1,VALUE,A,STEP;
    
    //Projeta a localiza??o do melhor valor de raio previsto com base no raio anterior.
    
    MAXLEN=sqrt((double)1.0/K);
    MAX2=1.0/(double)K;
    TRUNC=0;
    *BEST=9999999.0;
    *RSQ=K*(*R2);
    R=sqrt(*R2);
    RP=sqrt(*ROLD);
    RP2=sqrt(*RSQ);
    PROP2=0.;
    X[0]=1.0;
    X0[0]=1.0;
    if((CUBE==1) && (RP2>=MAXLEN))TRUNC=1;
    if(fabs(*ROLD)>0.)
     {
	  for(J=0;J<K;J++)
	   {
	    J2=J+1;
	    XBEST[J]=RP2*XBEST[J]/RP;
	    X[J2]=XBEST[J];
	   }
	  if(TRUNC!=0)
	   {
	    
	    //Encontra uma proje??o razo?vel do melhor ponto anterior quando a 
	    //regi?o ? cuboidal e a pesquisa deve ser restrita;
	    
	    NUM=0;
	    for(J=0;J<K;J++)
	     {
		  if(fabs(XBEST[J])>MAXLEN)
		   {
		    NUM=NUM+1;
		    OVER[NUM-1]=J;	      
		   }
	     }
	    if(NUM>0)
	     {
	      GOTO30:
		  for(J=0;J<K;J++)
		   {
		    PROP[J]=99.0;
		    TEMP2[J]=0.0;
		   }
		 SUM=0.0;
		 for(J=0;J<K;J++)
		  {
		   for(JDEX=0;JDEX<NUM;JDEX++)
		    { 
			 if(J==OVER[JDEX]) goto J60;
		    }
		   PROP[J]=XBEST[J]*XBEST[J];
		   SUM=SUM+PROP[J];
		   J60:
		   J=J;			   
		  }
		 if((fabs(SUM)<TOLERANCIA) && (NUM<K))PROP2=1.0/((double)(K-NUM));
		 if((fabs(SUM)<TOLERANCIA) && (NUM==K))PROP2=1.0/((double)K);
		 TEMP=(*RSQ)-(NUM*MAX2);
		 if(TEMP<0.)TEMP=0.;
		 for(J=0;J<K;J++)
		  {
		   if((PROP[J]<=1.) && (fabs(SUM)>0.)) TEMP2[J]=PROP[J]*TEMP/SUM;
		   if((PROP[J]<=1.) && (fabs(SUM)<TOLERANCIA)) TEMP2[J]=PROP2*TEMP;
		   if(PROP[J]>1.) TEMP2[J]=MAX2;
		   if(TEMP2[J]>MAX2)
		    {
			 NUM=NUM+1;
			 OVER[NUM-1]=J;
			 goto GOTO30;
		    }
		  }	  
		 for(J=0;J<K;J++)
		  {
		   J2=J+1;
		   TEMP1=sqrt(TEMP2[J]);
		   if(XBEST[J]>=0.) XBEST[J]=TEMP1;
		   if(XBEST[J]<0.) XBEST[J]=-TEMP1;
		   X[J2]=XBEST[J];
		  }
	     }
	    
	    MXPAND();
	    VMULT(BEST);
	    if(MAX==0) *BEST=-(*BEST);
	    if(INIT==1)
	     {
		  Rprintf("1)INIT no MINLOC\n");
		  Rprintf("%16.6lf  ",BEST);
		  for(J=1;J<KP;J++)
		   {	
		    Rprintf("%16.6lf   ",XBEST[J]);
		    Rprintf("%16.6lf   ",X[J]);
		   }
		  Rprintf("\n");
	     }
	   }
	  if((TRUNC==0) && (SIMPLX>=1))
	   {
	    for(J=0;J<K;J++)
	     {
		  J2=J+1;
		  X[J2]=XBEST[J];
	     }
	    AMOEBA(RSQ,&VALUE);
	    if(VALUE<(*BEST))
	     {
		  for(J=0;J<K;J++)
		   {
		    J2=J+1;
		    XBEST[J]=X[J2];
		   }
		*BEST=VALUE;
	     }
	   }
     }
    SAVE=0;
    if (TRUNC==0) NEND=NPTSF+NPTSA;
    if(TRUNC==1) NEND=NPTSF;
    if(TRUNC!=0)
     {
	  //Olha em outros refinamentos do melhor ponto projetado quando a regi?o 
	  //? cuboidal e a busca est? sobre uma esfera restrita;
	  FLAG=0;
	  for(J=0;J<K;J++)
	   {
	    TEMP=(*RSQ);
	    for(J2=0;J2<K;J2++)
	     {
		  J3=J2+1;
		  X[J3]=XBEST[J2];
		  if(fabs(XBEST[J2])>=MAXLEN) TEMP=TEMP-MAX2;
	     }
	    if(TEMP<=0.) TEMP=0.;
	    TEMP1=sqrt(TEMP);
	    if(TEMP1<=MAXLEN)
	     {
		  for(J2=0;J2<K;J2++)
		   {
		    if((J==J2) && (fabs(XBEST[J2])>=MAXLEN)) goto GOTO190;		      
		    J3=J2+1;
		    if(XBEST[J2]>=MAXLEN) X[J3]=MAXLEN;
		    if(XBEST[J2]<=MAXLEN) X[J3]=-MAXLEN;
		    if((J==J2) && (XBEST[J2]>=0.)) X[J3]=TEMP1;
		    if((J==J2) && (XBEST[J2]<0.)) X[J3]=-TEMP1;
		    if((J!=J2) && (fabs(XBEST[J2])<MAXLEN)) X[J3]=0.0;
		   }
		  MXPAND();
		  VMULT(&VALUE);
		  if(MAX==0) VALUE=-VALUE;
		  if(INIT==1)
		   {
		    Rprintf("2)INIT no MINLOC\n");
		    Rprintf("%16.6lf  ",VALUE);
		    for(J2=1;J2<KP;J2++)
		     {
			  Rprintf("%16.6lf  ",X[J2]);
		     }
		    Rprintf("\n");
		   }
		  if(VALUE<(*BEST))
		   {
		    FLAG=1;
		    for(J2=0;J2<K;J2++)
		     {
			  J3=J2+1;
			  TEMP2[J2]=X[J3];
		     }
		   }
	     }
	    else
	     {
		  for(J2=0;J2<K;J2++)
		   {
		    J3=J2+1;
		    X[J3]=XBEST[J2];
		   }
		  FLAG2=0;
	      GOTO150:
		  for(J2=0;J2<K;J2++)
		   {
		    J3=J2+1;
		    if((fabs(X[J3])<MAXLEN) && (J!=J2))
		     {
			  FLAG2=1;
			  SAVE=J2;
		     }
		   } 
		  if(FLAG2==1)
		   {
		    J3=SAVE+1;
		    if(XBEST[SAVE]<0.) X[J3]=-MAXLEN;
		    if(XBEST[SAVE]>=0.) X[J3]=MAXLEN;
		    TEMP=TEMP-MAX2;
		    if(TEMP<=0.) TEMP=0.;
		    TEMP1=sqrt(TEMP);
		    if(TEMP1>MAXLEN) goto GOTO150;
		    for(J2=0;J2<K;J2++)
		     {
			  J3=J2+1;
			  if((J==J2)&&(fabs(X[J3])>=MAXLEN)) goto GOTO190; 
			  if((J==J2) && (X[J3]>=0.)) X[J3]=TEMP1;
			  if((J==J2) && (X[J3]<0.))  X[J3]=-TEMP1;
			  if((J!=J2) && (fabs(X[J3])<MAXLEN)) X[J3]=0.;
		     }
		    MXPAND();
		    VMULT(&VALUE);
		    if(MAX==0) VALUE=-VALUE;
		    if(INIT==1)
		     {
			  Rprintf("3) INIT no MINLOC\n");
			  Rprintf("%16.6lf  ",VALUE);       
			  for(J2=1;J2<KP;J2++)
			   {
			    Rprintf("%16.6lf  ",X[J2]);
			   }
			  Rprintf("\n");
		     }
		    if(VALUE<(*BEST))
		     {
			  FLAG=1;
			  for(J2=0;J2<K;J2++)
			   {
			    J3=J2+1;
			    TEMP2[J2]=X[J3];
			   }
		     }
		   }
	     }
	    GOTO190:
	    J=J;
	   }
	  if(FLAG==1)
	   {
	    for(J=0;J<K;J++)
	     {
		  XBEST[J]=TEMP2[J];
	     }
	   }
     }
    
    //Realiza uma pesquisa de grade numa tentativa de melhorar o valor inicial.
    
    for(I=0;I<NEND;I++)
     {
	  PTS2[I][0]=1.;
	  for(J=0;J<K;J++)
	   {
	    J2=J+1;
	    PTS2[I][J]=R*PTS[I][J];
	    X[J2]=PTS2[I][J];
	   }
	  A=0.;
	  for(J=0;J<K;J++)
	   {
	    J2=J+1;
	    A=A+X[J2]*X[J2];
	   }
	  if((A>(*RSQ-TOLERANCIA2)) && (A<(*RSQ+TOLERANCIA2)))
	   {
	    MXPAND();
	    VMULT(&VALUE);
	    if(MAX==0) VALUE=-VALUE;
	    if(INIT==1)
	     {
		  Rprintf("4) INIT no MINLOC\n");
		  Rprintf("%16.6lf  ",VALUE);
		  for(J=1;J<KP;J++)
		   {
		    Rprintf("%16.6lf  ",X[J]);
		   }
		  Rprintf("\n");
	     }
	    if(VALUE<(*BEST))
	     {
		  *BEST=VALUE;
		  for(J=0;J<K;J++)
		   {
		    XBEST[J]=PTS2[I][J];
		   }
	     }
	   }
	  if((SIMPLX==2) && (TRUNC==0))
	   {
	    AMOEBA(RSQ,&VALUE);
	    if(VALUE<(*BEST))
	     {
		  for(J=0;J<K;J++)
		   {
		    J2=J+1;
		    XBEST[J]=X[J2];
		   }
		  *BEST=VALUE;
	     }
	   }
     }
    
	//Executa a parte flutuante da busca.
    
    if(TRUNC==0) STEP=2.*R;
    if(TRUNC==1) STEP=1.414*(1.-(*RSQ));
    for(I=0;I<5;I++)
     {
	  FLAG=0;
	  NLOOPS=0;
	  STEP=STEP/2.;
	  NEWX(&STEP,RSQ);
      GOTO250:
	  if(FLAG==1) NEWX2(&SAVE,&STEP,RSQ);
	  NLOOPS=NLOOPS+1;
	  if(NLOOPS>LNLOOPS)
	   {
	    Rprintf("Problem encountered in MINLOC \n");
	    Rprintf("You may wish to change NLOOPS \n");
	    Rprintf("Current value is:   ,%5d \n",NLOOPS);
	    return;    
	   }
	  FLAG=0;
	  for(J1=0;J1<NPTS3;J1++)
	   {
	    for(J2=0;J2<K;J2++)
	     {
		  J3=J2+1;
		  X[J3]=PTS3[J1][J2];
	     }
	    A=0.;
	    for(J=0;J<K;J++)
	     {
		  J2=J+1;
		  A=A+X[J2]*X[J2];
	     }
	    if((A>((*RSQ)-TOLERANCIA2)) && (A<((*RSQ)+TOLERANCIA2)))
	     {
		  MXPAND();
		  if(ITEST==1)
		   {
		    Rprintf("1)ITEST no MINLOC\n");
		    for(JZ=1;JZ<KP;JZ++)
		     {
			  Rprintf("%16.6lf  ",X0[JZ]);
		     }
		    Rprintf("\n");
		   }
		  VMULT(&VALUE);
		  if(MAX==0) VALUE=-VALUE;
		  if(VALUE<(*BEST))
		   {
		    FLAG=1;
		    SAVE=J1;
		    *BEST=VALUE;
		   }
	     }
	   }
	  if(FLAG==1) goto GOTO250;
	 }
  }
  
  void PROCV(int NRHO,int NDPTS,int NPTSF,int NPTSA,double GRAPH[MD][4],double MAXIMUM[MD][9],double MINIMUM[MD][9])
  {
    int I,I2,J;
    char XVECT[7][5]={"X[0]","X[1]","X[2]","X[3]","X[4]","X[5]","X[6]"};
    char TITULO[4][10]={"RSQ","MAX","MIN","MED"};
    double RSQ2,DENOM,AK,R,VALUE,ROLD,RSQ,R2,BEST;
    double PVAL[MD][MP];
    
    //Controla o estudo apropriadamente para produzir os gr?ficos.
    
    X[0]= 1.;
    X0[0]= 1.;
    PVAL[0][3]=(double)NDPTS;
    if(PRIN==1)Rprintf("\n\n\n Prediction Variance Results");
    for(MAX=0;MAX<3;MAX++)
     {
	  if(MAX==0)
	   {
	    if(PRIN==1)Rprintf("\n\n\n MAXIMUMS\n\n    R        VALUE");
	    for(I=0;I<K;I++)
	     {
		  if(PRIN==1)Rprintf("       %s",      XVECT[I]);
	     }
	    if(PRIN==1)Rprintf("\n\n");
	   }
	  if(MAX==1)
	   {
	    if(PRIN==1)Rprintf("\n\n\n MINIMUMS \n\n    R        VALUE");
	    for(I=0;I<K;I++)
	     {
		  if(PRIN==1)Rprintf("      %s",XVECT[I]);
	     }
	    if(PRIN==1)Rprintf("\n\n");
	   }
	  if(MAX==2)
	   {
	    if(PRIN==1)Rprintf("\n\n\n AVERAGES\n\n             R              VALUE");
	   }
	
	  //Encontra a vari?ncia da predi??o no centro do delineamento, 
	  //e ajusta este valor para refletir o n?mero de execu??es do 
	  //delineamento.
	
	  for(I=1;I<KP;I++)
	   {
	    X[I]=0.;
	   }
	  for(I=1;I<K1;I++)
	   {
	    X0[I]=0.;
	   }
	  RSQ=0.;
	  RSQC=1;
	  VMULT(&VALUE);
	  if(NWT!=1)
	   {
	    VALUE=NDPTS*VALUE;
	   }
	  PVAL[0][MAX]=VALUE;
	  if(MAX<2)
	   {
	    if(PRIN==1)Rprintf(" %8.4lf %10.6lf",RSQ,VALUE);
	    if(MAX==0)
	     {
		  GRAPH[0][0]=RSQ;
		  GRAPH[0][1]=VALUE;
		  MAXIMUM[0][0]=RSQ;
		  MAXIMUM[0][1]=VALUE;
	     }
	    else 
	     {
		  GRAPH[0][2]=VALUE;
		  MINIMUM[0][0]=RSQ;
		  MINIMUM[0][1]=VALUE;
	     }
	    for(I=1;I<KP;I++)
	     {
		  if(PRIN==1)Rprintf("%10.6lf ",X[I]);
		  if(MAX==0)MAXIMUM[0][I+1]=X[I];
		  else MINIMUM[0][I+1]=X[I];
	     }
	   }
	  if(PRIN==1)Rprintf("\n");
	  if(MAX==2)
	   {
	    if(PRIN==1)Rprintf(" %16.6lf %16.6lf\n",RSQ,VALUE);
	    GRAPH[0][3]=VALUE;
	   }
	  //Encontra a vari?ncia da predi??o m?xima, m?nima e m?dia para v?rios raios
	  //dentro de uma hiperesfera unit?ria, ajustando estes valores para refletir o 
	  //n?mero de execu??es usadas no delineamento, e ent?o imprimi.
	
	  ROLD=0.0;
	  for(I=1;I<=NRHO;I++)
	   {
	    I2=I+1;
	    DENOM=(double)NRHO;
	    AK=(double)K;
	    R=(double)I/DENOM;
	    RSQ=R*R;
	    R2=RSQ/AK;
	    RSQ2=SCA*R;
	    
	    if(MAX<2)
	     {
		  MINLOC(&ROLD,&R2,&RSQ,&BEST,NPTSF,NPTSA);
	     }
	    if(MAX==2)
	     {
		  VSPH(&BEST,&RSQ);
	     }
	    if(MAX==0)
	     {
		  BEST=-BEST;
	     }
	    if(NWT!=1)
	     {
		  BEST=NDPTS*BEST;
	     }
	    PVAL[I2-1][MAX]=BEST;
	    PVAL[I2-1][3]=(double)NDPTS;
	    if(MAX<2)
	     {
		  if(PRIN==1)Rprintf(" %8.4lf %10.6lf",RSQ2,BEST);
		  if(MAX==0)
		   {
		    GRAPH[I][0]=RSQ2;
		    GRAPH[I][1]=BEST;
		    MAXIMUM[I][0]=RSQ2;
		    MAXIMUM[I][1]=BEST;
		   }
		  else 
		   {
		    GRAPH[I][2]=BEST;
		    MINIMUM[I][0]=RSQ2;
		    MINIMUM[I][1]=BEST;
		   }
		  for(J=0;J<K;J++)
		   {
		    if(PRIN==1)Rprintf(" %10.6lf",XBEST[J]);
		    if(MAX==0)MAXIMUM[I][J+2]=XBEST[J];
		    else MINIMUM[I][J+2]=XBEST[J];
		   }
		  if(PRIN==1)Rprintf("\n");
	     }
	    if(MAX==2)
	     {
		  if(PRIN==1)Rprintf("%16.6lf %16.6lf\n",RSQ2,BEST);
		  GRAPH[I][3]=BEST;
	     }
	    ROLD=RSQ;
	   }
     }
    
    //Imprimindo o arquivo gr?fico
    if(PRIN==1)
     {
	  if(CONF==1)Rprintf("\n\n\n The value of 'eta' is: %lf \n\n\n", ETA);
	  else Rprintf("\n\n\n");
	  for(I=0;I<=3;I++)
	   {
	    Rprintf("      %s   ",TITULO[I]);
	   } 
	  Rprintf("\n\n");
	  for(I=0;I<=NRHO;I++)
	   {
	    for(J=0;J<=3;J++)
	     {
		  Rprintf(" %10.6lf ",GRAPH[I][J]);
	     }
	    Rprintf("\n");
	   }
	  Rprintf("\n\n");
     }
  }
  
  void GRID(int *NPTSF, int *NPTSA, int *NPTS)
  {
    
    //Inicia a grade usada na fase inicial da busca.
    
    int I,J,INDEX,KEXP,KDEN;
    double SQRTK,AK;  
    
    //Inicia os pontos fatoriais a serem usados na grade de busca.
    
    *NPTSF=1;
    *NPTSF=pow(2,K);
    *NPTSA=2*K;
    *NPTS=(*NPTSF) + (*NPTSA);
    for(I=1;I<=(*NPTS);I++)
     {
	  for(J=1;J<=K;J++)
	   {
	    PTS[I-1][J-1]=0.0;
	   }
     }
    for(I=1;I<=(*NPTSF);I++)
     {
	  for(J=1;J<=K;J++)
	   {
	    KDEN=I*pow(2,J);
	    KEXP= KDEN/(*NPTSF);
	    PTS[I-1][J-1]= pow(-1.,KEXP);
	   }
     }
    
    //Inicia os pontos axiais a serem usados na grade de busca
    
    INDEX= (*NPTSF);
    AK = (double)K;
    SQRTK= sqrt(AK);
    for(I=1;I<=K;I++)
     {
	  INDEX=INDEX+1;
	  PTS[INDEX-1][I-1]=-SQRTK;
	  INDEX=INDEX+1;
	  PTS[INDEX-1][I-1]=SQRTK;
     }
  }
  
  double MODULO(double X)
  {
   //Retorna o m?dulo de um n?mero de dupla precis?o.
       if(X<0.) X =- X;
       return X;
  }

  double sampleNormal() 
  {
    //Gera n?meros aleat?rios seguindo a distribui??o Normal de probabilidade.
    double u = ((double) rand() / (RAND_MAX)) * 2. - 1.;
    double v = ((double) rand() / (RAND_MAX)) * 2. - 1.;
    double r = u * u + v * v;
    if (r == 0. || r > 1.) return sampleNormal();
    double c = sqrt(-2. * log(r) / r);
    return u * c;
  }      

   void POINTS(int N, int K, int REGION, double DESIGN[MD][M1], int P, double MPOINTS[PONTOS][M1],double PNT[MD][9])
   {
    //Gera pontos aleatoriamente na regi?o experimental (esf?rica ou cuboidal) para a elabora??o do FDS.
	
     int i,j,i2,j2;
     double MAXMIN[2][M1],MAX,MIN,range,z,raio,u;
     int imp=0;
     
     //Gera pontos aleat?rios em regi?o experimental cuboidal.  
     if(REGION==1)
      {
	   for(j=1;j<K+1;j++)
        {
		 //Encontra o n?vel m?ximo e m?nimo para cada fator experimental.
         MAX=0.;
         MIN=9999.0;
         for(i=0;i<N;i++)
          {
           if(DESIGN[i][j]<MIN)MIN=DESIGN[i][j];
           if(DESIGN[i][j]>MAX)MAX=DESIGN[i][j];
          }
         MAXMIN[0][j-1]=MAX;
         MAXMIN[1][j-1]=MIN;
        }
        
       //Criando os pontos aleat?rios e armazenando em MPOINTS     
       srand((unsigned)time(NULL));
       for(j=0;j<K;j++)
        {
         if(MAXMIN[0][j]==0.)range=MAXMIN[1][j];
         else if(MAXMIN[1][j]==0.)range=MAXMIN[0][j];
         else range=(double)MAXMIN[0][j]-MAXMIN[1][j];
         if(range<0.)range=-range;
         for(i=0;i<(int)(P-NRHO);i++)
          {
           MPOINTS[i][j]=((double)(rand())/((double)(RAND_MAX)+1.))*range;
           if((MAXMIN[1][j]<0.)&&(MPOINTS[i][j]<0.))MPOINTS[i][j]=-(MODULO(MPOINTS[i][j])-MODULO(MAXMIN[1][j]));
           if((MAXMIN[1][j]<0.)&&(MPOINTS[i][j]>0.))MPOINTS[i][j]=MPOINTS[i][j]-MODULO(MAXMIN[1][j]);
          } 
		}
         
		   for(i2=0;i2<NRHO;i2++)
		    {
		     for(j2=0;j2<K;j2++)
              {
               if(DF==2)MPOINTS[i2+(P-NRHO)][j2]=PNT[i2][j2];
			   if(DF==3)MPOINTS[i2+(P-NRHO)][j2]=PNT[i2+NRHO][j2];
			  }
            }			 
		   		  
        
      } 
      
     //Gera pontos aleat?rios em regi?o experimental esf?rica que resultam em raio m?ximo igual ao unit?rio.

     if(REGION==0)
      {
       srand((unsigned)time(NULL));
       z=1./(double)K;
       for(i=0;i<(int)(P-NRHO);i++)
        {
         raio=0.;
         for(j=0;j<K;j++)
          {
           MPOINTS[i][j]=sampleNormal();
           raio=raio+pow(MPOINTS[i][j],2);           
          }
         u=((double)(rand())/((double)(RAND_MAX)+1.));
         u=(double)pow(u,z);
         raio=(double)sqrt(raio);
         for(j=0;j<K;j++)
          {
           MPOINTS[i][j]=(MPOINTS[i][j]*u)/raio;
          } 
        }
		
		   for(i2=0;i2<NRHO;i2++)
		    {
		     for(j2=0;j2<K;j2++)
              {
               if(DF==2)MPOINTS[i2+(P-NRHO)][j2]=PNT[i2][j2];
			   if(DF==3)MPOINTS[i2+(P-NRHO)][j2]=PNT[i2+NRHO][j2];
			  }
            }			 
		  
      }
	  
	if(imp==1)
    {
	 if(REGION==1)
      {        
	   for(i=0;i<2;i++)
	    {
		 for(j=0;j<K;j++)
		  {
		   Rprintf(" %lf",MAXMIN[i][j]);
		  }
		 Rprintf("\n");
	    }
	   
	    for(i=0;i<P;i++)
		 {
		  for(j=0;j<K;j++)
		   {
		    Rprintf(" %lf",MPOINTS[i][j]);
		   }
		  Rprintf("\n");
		 }
		 
		 } 
		 if(REGION==2)
		  {
		   
        
		 for(i=0;i<P;i++)
		  {
		   for(j=0;j<K;j++)
		    {
			 Rprintf("%lf ",MPOINTS[i][j]);
		    }
		   Rprintf("\n");
		  }
		  
		  } 
	}
      
     
   }
 
  
  //Continua??o da fun??o principal, que gerencia todas as fun??es acima.
  int I,I2,ATU,ATU2,ATU3,J,J1,J2,J3,J4,FLAG,FLAG2,NPTSF,NPTSA,NPTS;
  double DP[MD][M1],CHECK,FACT,A,SUM,VALUE,MPOINTS[PONTOS][M1], FDS[PONTOS][2], PNT[2*MD][9];
  ITEST=0;
  INIT=0;
  
  do
   {
    FLAG=0;
    do
	 {
	  FLAG2=0;
	  if((NDPTS<0) || (NDPTS>MD))
	   {
	    Rprintf("The specified number of runs is either negative or too large: %d \n",MD);
	    FLAG2=1;
	   }
	 }while(FLAG2==1);
    if(ORDER!=2)
	 {
	  ORDER=1;
	 }
    if(ORDER==1)
	 {
	  CHECK=(double)K+1.;
	 }
    if(ORDER==2)
	 {
	  CHECK=1.+2.*K+K*(K-1)/2.;
	 }
    if((double)NDPTS<CHECK)
	 {
	  Rprintf("The specified number of design points will not allow estimation of the model\n");
	  FLAG=1;
	 }
   }while(FLAG==1);
  KP=K+1;
  if(ORDER==1)
   {
    K1=K+1;
   }
  if(ORDER==2)
   {
    K1=1+2*K+K*(K-1)/2;
   }
  GRID(&NPTSF,&NPTSA,&NPTS);
  
  //L? no delineamento, em sua pr?pria escala, e a escalona na localiza??o 
  //desejada dentro da hiperesfera unit?ria  
  
  A=0.;
  I=0;
  I2=0;
  if(PRIN==1)Rprintf("Design\n\n");
  while(I<NDPTS)
    {
     D[I][0]=1.;
     DP[I][0]=1.;
     for(J1=0;J1<K;J1++)
	  {
	   J2=J1+1;
	   DP[I][J2]=DES[I2];
	   I2=I2+1;
	  }
     SUM=0.;
     for(J3=1;J3<KP;J3++)
	  {
	   SUM=SUM+DP[I][J3]*DP[I][J3];
	  }
     if(SUM>A)
	  {
	   A=SUM;
	  }
     if(PRIN==1)
	  {
	   for(J4=1;J4<KP;J4++)
	    {
	     Rprintf(" %lf ",DP[I][J4]);
	    } 
	   Rprintf("\n");
	  }
     I=I+1;
    }
  
  FACT=FACT1/sqrt(A);
  for(I=0;I<NDPTS;I++)
   {
    for(J=1;J<KP;J++)
	 {
	  DP[I][J]=FACT*DP[I][J];
	 }
   }
  
  //Inicia o delineamento no modelo espa?ado e encontra a inversa de D'D.
  
  for(I=0;I<NDPTS;I++)
   {
    for(J=0;J<KP;J++)
	 {
	  X[J]=DP[I][J];
	 }
    MXPAND();
    for(J=0;J<K1;J++)
	 {
	  D[I][J]=X0[J];
	 }
   }
  
  //Imprime apropriadamente os t?tulos e chama o procedimento para realizar a an?lise.
  CONF=CONF-1;
  if(CONF==0)
   {
    ETA=1;
   }
  
  if((CONF==1)&&(PRIN==1))Rprintf("\n\n\n The value of 'eta' is: %lf \n\n\n", ETA);
  EXECUTE=0;
  //Obt?m a matriz de vari?ncias e covari?ncias
  BMAT(NDPTS);
  if(EXECUTE==1)
   {
	goto EXECUTED;
   }
  ATU2=0;
  ATU3=0;
  for(DF=0;DF<4;DF++)
   {
    if(DF<2)
     {
	  //Chama as fun??es que calculam as vari?ncias de predi??es para a elabora??o do VDG e do DVDG.
      PROCV(NRHO,NDPTS,NPTSF,NPTSA,GRAPH,MAXIMUM,MINIMUM);
      //Atualiza??o de GRA, MAXI e MINI.
      ATU=ATU2;
      for(I=0;I<(NRHO+1);I++)
	   {
	    for(J=0;J<4;J++)
	     {
	      GRA[ATU]=GRAPH[I][J];
	      ATU=ATU+1;
	     }
	   }
      ATU2=ATU; 
      ATU=ATU3;
      for(I=0;I<(NRHO+1);I++)
	   {
	    for(J=0;J<(K+2);J++)
	     {
	      MAXI[ATU]=MAXIMUM[I][J];
	      ATU=ATU+1;
	     }
	   }
      ATU=ATU3;
      for(I=0;I<(NRHO+1);I++)
	   {
	    for(J=0;J<(K+2);J++)
	     {
	      MINI[ATU]=MINIMUM[I][J];
	      ATU=ATU+1;
	     }
       }
       ATU3=ATU; 
	   for(I=1;I<=NRHO;I++)
	   {
	    for(J=0;J<K;J++)
	     {
	      if(DF==0)PNT[I-1][J]=MAXIMUM[I][J+2];
		  if(DF==1)PNT[I-1+NRHO][J]=MAXIMUM[I+NRHO][J+2];	      
	     }
       }
     }
	 
         
    if(DF==2||DF==3)
     {
	  //Realiza os c?lculos necess?rios para a elabora??o do FDS para o VDG e para o DVDG.
      if(DF==2)POINTS(NDPTS,K,CUBE,DP,P,MPOINTS,PNT); 
      for(I=0;I<P;I++)
       {
	    X[0]=1.;
        for(J=0;J<K;J++)
         {
          X[J+1]=MPOINTS[I][J];
         } 
	    if((DF==3) && (I==0))
		 {
		  for(I=1;I<KP;I++)
	       {
	        X[I]=0.;
	       }
	      for(I=1;I<K1;I++)
	       {
	        X0[I]=0.;
	       }
		  RSQC=1;
		 }
	    VMULT(&VALUE);
	    if(NWT!=1)
	     {
	      VALUE=NDPTS*VALUE;
         }
        FDS[I][1]=VALUE;
       }       
	  hpsort(P, FDS);
	  for(I=0;I<P;I++)
	   {
	    FDS[I][0]=(double)(I+1)/(double)(P+1);
	   }
      if(DF==2)
       {
        ATU=0;
        for(I=0;I<P;I++)
	     {
	      for(J=0;J<2;J++)
	       {
	        GRAF[ATU]=FDS[I][J];
	        ATU=ATU+1;
	       }
         }
       }
       if(DF==3)
       {
        for(I=0;I<P;I++)
         {
          GRAF[ATU]=FDS[I][1];
          ATU=ATU+1;
         }
       } 
                       
     }       
   }   
  EXECUTED:
  if(PRIN==1)Rprintf("executed");
}
