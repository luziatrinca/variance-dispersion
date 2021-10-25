vardispersion <-
function (N,K,DESIGN,REGION,DES.TYPE,ORDER,NWPT,NSPT,ETA,PRIN,RADII,WEIGHTING,SCALE,FRACTION,SEARCH,FTOL,ITMAX,NLOOPS,NSAMPLE)
{
 #DESIGN [matrix with design] 
 #REGION [experimental region of interest]: 1(spherical) ou 2(cuboidal) 
 #DES.TYPE [the type of the design]: 1 (completely randomized) ou 2 (split-plot) 
 #ORDER [order of the polynomial model intended to be fitted]:1 ou 2 
 #NWPT [number of whole plots]: 1 for design completely randomized 
 #NSPT [number of subplots within each whole plot]: 1 for design completely randomized 
 #ETA [a prior value for the variance component ratio] 
 #PRIN [ENABLES(1) or DISABLES(2) print of the titles and results in the R command prompt] 
 #RADII [number of radii that the user want the search to be performed] 
 #WEIGHTING [an indicator for weighting the variances by the experiment size (N)]: 1(YES) ou 2(NO) 
 #SCALE [Allows the user to scale the size of the region of interest]: standard 1 
 #FRACTION [a scaling factor between 0 and 1 to specify where, within the region of interest, the designs resides]: standard 1 
 #SEARCH [0(Quick),1(Standard),2(Enhanced)] 

 
 if(missing(N) | missing(K))stop("The number of runs (N) and factors (K) are compulsory!")
 if(N!=dim(DESIGN)[1])stop("The number of runs (N) should be equal to the number of rows of the design matrix!")
 if(K!=dim(DESIGN)[2])stop("The number of factors (K) should be equal to the number of columns of the design matrix!")
 
 
 if(missing(REGION))REGION=2 
 if(missing(DES.TYPE))DES.TYPE=1 
 if(missing(ORDER))ORDER=2 
 if(missing(NWPT))NWPT=1 
 if(missing(NSPT))NSPT=dim(DESIGN)[1] 
 if(missing(ETA))ETA=1 
 if(missing(PRIN))PRIN=2 
 if(missing(RADII))RADII=20 
 if(missing(WEIGHTING))WEIGHTING=2 
 if(missing(SCALE))SCALE=1 
 if(missing(FRACTION))FRACTION=1 
 if(missing(SEARCH))SEARCH=1 
 if(missing(FTOL))FTOL=0.00001 
 if(missing(ITMAX))ITMAX=5000 
 if(missing(NLOOPS))NLOOPS=10000 
 if(missing(NSAMPLE))NSAMPLE=10000
 
 
 
 if(NSAMPLE>30000)
 {
  warning("NSAMPLE should be less than 30000. The calculations will procced with NSAMPLE=10000.")
  NSAMPLE=10000
 }
 
 
 


 MAX=matrix(1,ncol=dim(DESIGN)[2]+2,nrow=(2*(RADII+1))) 
 MIN=matrix(1,ncol=dim(DESIGN)[2]+2,nrow=(2*(RADII+1))) 
 GRAPH=matrix(1,ncol=4,nrow=(2*(RADII+1)))
 GRAPHF1=matrix(1,ncol=3,nrow=NSAMPLE) 
 NDPTS=N
 DESIGN2=as.double(t(DESIGN)) 
 WEIGHTING=WEIGHTING-1 
 REGION=REGION-1 
 NETA=1 
 MAX2=as.double(t(MAX)) 
 MIN2=as.double(t(MIN)) 
 GRAPH2=as.double(t(GRAPH)) 
 GRAPHF2=as.double(t(GRAPHF1)) 
 Confi=c(SEARCH,NDPTS,K,ORDER,REGION,WEIGHTING,RADII,DES.TYPE,NWPT,NSPT,PRIN,NLOOPS,ITMAX,NSAMPLE) 
 RESULTS=(.C("principal",as.integer(Confi),as.double(FTOL),as.double(SCALE),as.double(FRACTION),as.double(ETA),as.double(DESIGN2),as.double(GRAPH2),as.double(GRAPHF2),as.double(MAX2),as.double(MIN2)))
 GRAPH2=RESULTS[[7]] 
 GRAPHF2=RESULTS[[8]]
 MAX2=RESULTS[[9]] 
 MIN2=RESULTS[[10]] 
 dim(MAX2)=c((K+2),(2*(RADII+1)))
 dim(MIN2)=c((K+2),(2*(RADII+1))) 
 dim(GRAPH2)=c(4,(2*(RADII+1))) 
 GRAPHF1[,-3]=matrix(GRAPHF2[1:(2*NSAMPLE)],nrow=NSAMPLE,ncol=2,byrow=TRUE) 
 GRAPHF1[,3]=matrix(GRAPHF2[(2*NSAMPLE+1):(3*NSAMPLE)],nrow=NSAMPLE,ncol=1,byrow=TRUE) 
 MAX=t(MAX2) 
 MIN=t(MIN2) 
 GRAPH=t(GRAPH2)
 POS=c("X[0]","X[1]","X[2]","X[3]","X[4]","X[5]","X[6]") 
 POSITION=c(rep("X[0]",K)) 
 for(I in 1:K)POSITION[I]=POS[I] 
 dimnames(MAX)=list(rep(0:RADII,2),c("RAD","MAXIMUM",POSITION)) 
 dimnames(MIN)=list(rep(0:RADII,2),c("RAD","MINIMUM",POSITION)) 
 dimnames(GRAPH)=list(rep(0:RADII,2),c("RAD","MAXIMUM","MINIMUM","AVERAGE")) 
 dimnames(GRAPHF1)=list(rep(1:NSAMPLE),c("FRACTION","VAR","DIFFVAR"))
 OPTIONS=rep("NOTHING",3) 
 if(DES.TYPE==1)OPTIONS[1]="completely randomized design" 
 if(DES.TYPE==2)OPTIONS[1]="split-plot design" 
 if(REGION==0)OPTIONS[2]="spherical region" 
 if(REGION==1)OPTIONS[2]="cuboidal region" 
 if(ORDER==1)OPTIONS[3]="first-order polynomial" 
 if(ORDER==2)OPTIONS[3]="second-order polynomial" 
 GRAPHV=GRAPH[1:(RADII+1),]
 GRAPHD=GRAPH[(RADII+2):((2*RADII)+2),]
 if(REGION==1)GRAPHV=GRAPHV[,-4]
 if(REGION==1)GRAPHD=GRAPHD[,-4]
 SCALE1=c(min(c(GRAPHV[,3],GRAPHF1[,2])),max(c(GRAPHV[,2],GRAPHF1[,2])))
 SCALE2=c(min(c(GRAPHD[,3],GRAPHF1[,3])),max(c(GRAPHD[,2],GRAPHF1[,3])))
 # par(mfrow=c(2,2))
 # plot(main="VDG",xlab="Radius",ylab="Variance of estimated response",GRAPHV[,1],GRAPHV[,2],type="l",ylim=SCALE1)
 # lines(GRAPHV[,1],GRAPHV[,3])
 # if(REGION==0)lines(GRAPHV[,1],GRAPHV[,4],lty=3)
 # plot(main="DVDG",xlab="Radius",ylab="Variance of estimated difference",GRAPHD[,1],GRAPHD[,2],type="l",ylim=SCALE2)
 # lines(GRAPHD[,1],GRAPHD[,3])
 # if(REGION==0)lines(GRAPHD[,1],GRAPHD[,4],lty=3)
 # plot(main="FDS",xlab="Fraction of space",ylab="Variance of estimated response",GRAPHF1[,1],GRAPHF1 # [,2],type="l",ylim=SCALE1)
 # plot(main="FDS",xlab="Fraction of space",ylab="Variance of estimated difference",GRAPHF1[,1],GRAPHF1 # [,3],type="l",ylim=SCALE2)

 return(list(MAX=MAX,MIN=MIN,VDG=GRAPHV,DVDG=GRAPHD,FDS=GRAPHF1,OPTIONS=OPTIONS)) 
}
