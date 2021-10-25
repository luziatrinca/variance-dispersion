\name{dispersion-package}
\alias{dispersion-package}
\alias{dispersion}
\docType{package}
\title{Variance Dispersion Graphs (VDGs), Difference VDGs, Fraction Design Space (FDS) and Difference FDS for Unblocked, Blocked and Split-Plot Designs.}

\description{The dispersion package calculates variances for constructing VDG, DVDG, FDS and DFDS (FDS for difference prediction) for various types of response surface designs in cuboidal or spherical region. By default it plots plain graphs. Enhanced graphs may be easily plotted by the user using the results that are returned. It handles unblocked, blocked and split-plot designs. For more information on VDGs see [2] and [5]; on DVDG see [5]; on FDS see [6] and on split-plot experiments see [1] and [3].}

\details{The package is composed by the function variance.dispersion() which calls a C routine for finding the minimum, maximum and average variances of mean responses and of differences between response predictions (VDG and DVDG). It is an extension of the Vining's FORTRAN program for VDG of unblocked designs [5].}

\author{Cesar Buchile Abud de Oliveira and Luzia Aparecida Trinca.

Maintainer: Cesar Buchile Abud de Oliveira <cesar.abud.b@gmail.com>.}

\references{
[1] GOOS, P.; JONES, B. I-optimal versus D-optimal split-plot response surface designs.
Journal of Quality Technology. v. 44, n. 2, p. 85-101, 2012.

[2] JENSEN, G.; MYERS, R. H. Graphical Assessment of the Prediction Capability of Response Surface Designs. Technometrics. v. 31, n. 2, p. 159-171, 1989.

[3] LETSINGER, J. D.; MYERS, R. H.; LENTNER, M. Response Surface of Bi-Randomization Structures. Journal of Quality Technology. v. 28, n. 4, p. 381-397, 1996.

[4] TRINCA, L. A. and GILMOUR, S. G. Difference variance dispersion graphs for comparing response surface designs with applications in food technology. Applied Statistics. v. 48, p. 441-455, 1999.

[5] VINING, G. G. Computer Program for Generating Variance Dispersion Graphs. Journal
of Quality Technology. v. 25, n. 1, p. 45-58, 1993.

[6] ZAHRAN, A.; ANDERSON-COOK, C. M.; MYERS, R. H. Fraction of design space to assess prediction capability of response surface designs. Journal of Quality Technology. v. 35, n. 4, p. 377-386, 2003.
}

\keyword{ VDG }
\keyword{ variance }
\keyword{ DVDG }
\keyword{ FDS }
\keyword{ prediction }
\keyword{ split-plot }
\keyword{ blocked }
\keyword{ design }
\keyword{ response }
\keyword{ surface }
\keyword{ polynomial }


\examples{
  \dontrun{
# Example 1: VDG for a completely randomized design in spherical region

data(DES1)
RES1 <- vardispersion(N=18,K=3,DES1,REGION=1)
names(RES1)
head(RES1$VDG)

# VDG
par(bty="n",mar=c(5, 5, 2, 2) + 0.1)
plot(RES1$VDG[,2]~RES1$VDG[,1], type="l", ylim=c(0,1),
ylab=expression(sigma^{-2}*Var(hat(y)[x])), xlab="Distance")
lines(RES1$VDG[,3]~RES1$VDG[,1])

# Example 2: DFDS for a completely randomized design in spherical region

data(DES2)
RES2 <- vardispersion(N=18,K=3,DES2,REGION=1)
head(RES2$FDS)

# DFDS
par(bty="n",mar=c(5, 5, 2, 2) + 0.1)
plot(RES2$FDS[,3]~RES2$FDS[,1], type="l", ylim=c(0,1.4),
ylab=expression(sigma^{-2}*Var(hat(y)[x]-hat(y)[0])),
xlab="Fraction of design space")
  }
  \dontrun{
# Example 3: a split-plot design in cuboidal region, eta=1

data(DES3)
RES3=vardispersion(N=42,K=5,DES3,DES.TYPE=2,NWPT=21,NSPT=2)

# Example 4: a split-plot design in cuboidal region, eta=2

data(DES4)
RES4=vardispersion(N=42,K=5,DES4,DES.TYPE=2,NWPT=21,NSPT=2, ETA=2)} 
  }

