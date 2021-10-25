\name{vardispersion}
\alias{vardispersion}
\title{Calculates variances for VDG, DVDG, FDS and DFDS for response surface designs (unblocked, blocked and split-plot)
}
\description{
Calls a C routine that finds the maximum and minimum prediction variances for spheres with several different radii within an experimental region (spherical or cuboidal), for unblocked, blocked (random effects) and split-plot designs. The C routine is an adaptation and extension of G. Vining's FORTRAN code [3]. It calculates variances of predicted responses and of differences between two predicted responses (at the design centre and elsewhere) allowing the construction of VDG (Giovannitti-Jensen and Myers, 1989) and the DVDG (Trinca and Gilmour, 1999). For the cube, restricted searches are performed for radii that extrapolate the interest region. For split-plot and blocked designs, a given value of the ratio of variance components, 'eta', is assumed. The ratio is a measure related to the intra-class correlation (correlation between observations within the same whole plot or the same block), large 'eta' means strong correlation. The C routine also calculates the fractions of the design space with variances smaller than a given value for FDS (Zahran, Anderson-Cook and Myers, 2003) as well as DFDS plots. Random sampling is used to assess the distribution of the variances. All the numerical results are also returned for further use.
}
\usage{
vardispersion(N, K, DESIGN, REGION, DES.TYPE, ORDER, NWPT, NSPT, ETA, PRIN, 
RADII, WEIGHTING, SCALE, FRACTION, SEARCH, FTOL, ITMAX, NLOOPS, NSAMPLE)
}

\arguments{
   \item{N}{the number of rows of the DESIGN matrix (see below). The maximum value allowed is 99.}

   \item{K}{the number of columns of the DESIGN matrix (number of factors). The maximum value allowed is 7.}

   \item{DESIGN}{a matrix containing the treatment design (each row is a combination of the K factor levels).}

   \item{REGION}{the type of the experimental region of interest. REGION=1 is for spherical and REGION=2 for cuboidal.}

   \item{DES.TYPE}{the type of the design. TYPE.DES=1 is for completely randomized design and 2 is for blocked or split-plot type design.}

   \item{ORDER}{the order of the polynomial model intended to be fitted once the experiment is performed and data collected. ORDER=1 is for the first and ORDER=2 is for the second order model.}

   \item{NWPT}{the number of whole plots (blocks) for the split-plot (blocked) type design (DES.TYPE=2). If missing, NWPT is taken to be 1 (DES.TYPE=1).}

   \item{NSPT}{the number of units within each whole plot (block) for the split-plot (blocked) type design (DES.TYPE=2). If missing, NSPT is taken to be N (DES.TYPE=1). Only equal sizes are allowed.}

  \item{ETA}{a prior value for the ratio of variance components (DES.TYPE=2). If missing, ETA is taken to be 1.}

  \item{PRIN}{TRUE/FALSE for automatic listing the results in the R command prompt. PRIN=1 is for TRUE and PRIN=2 is for FALSE. If missing, PRIN is taken to be 2.}

   \item{RADII}{the number of radii that the user wants the search to be performed for VDG and DVDG. If missing, RADII is taken to be 20.}

   \item{WEIGHTING}{an indicator for weighting the variances by the design size (N). WEIGHTING=1 is for YES and WEIGHTING=2 is for NO. If missing, WEIGHTING is taken to be 2.}

   \item{SCALE}{a scaling factor. Allows the user to scale the size of the region of interest. For example, SCALE=1 will report results in the unit hyper-sphere or the unit hypercube. If missing, SCALE is taken to be 1.}

   \item{FRACTION}{a scaling factor between 0 and 1 to specify where, within the region of interest, the design resides. For example, FRACTION=1 means the furthest design point falls in the perimeter of the region of interest. Values smaller than 1 are useful to explore how the design performs at extrapolations, e.g. outside the design region. If missing, FRACTION is taken to be 1.}

   \item{SEARCH}{the search method as in Vining (1993). SEARCH=0 is the "Quick", SEARCH=1 is the "Standard" and SEARCH=2 is the "Enhanced" method. If missing, SEARCH is taken to be 1.}

   \item{FTOL}{the tolerance factor used in AMOEBA subroutine. If missing, FTOL is taken to be 0.00001.}

   \item{ITMAX}{the maximum value of iterations used in AMOEBA subroutine. If missing, ITMAX is taken to be 5,000.}

   \item{NLOOPS}{the maximum value of iterations used in MINLOC subroutine. If missing, NLOOPS is taken to be 10,000.}

   \item{NSAMPLE}{number of points randomly chosen in the experimental region for the calculations related to FDS and DFDS. If missing or higher than 30,000, NSAMPLE is taken to be 10,000.}
}

\details{
%%  ~~ If necessary, more details than the description above ~~
}
\value{
The function variance.dispersion() return a "list" with six components (MAX, MIN, VDG, DVDG, FDS and OPTIONS).
  \item{MAX}{matrix with the maximum variance values and their locations in the region for each radii for VDG and DVDG.}
  \item{MIN}{matrix with the minimum variance values and their locations in the region for each radii for VDG and DVDG.}
  \item{VDG}{matrix summarizing the results for VDG construction.}
  \item{DVDG}{matrix summarizing the results for DVDG construction.}
  \item{FDS}{matrix with the results for FDS and DFDS construction.}
  \item{OPTIONS}{vector with the main input settings.}
}
\references{
1. GIOVANNITTI-JENSEN, A.; MYERS, R. H. Graphical assessment of the prediction capability of response surface designs. Technometrics. v. 31, p. 159-171, 1989.

2. TRINCA, L. A.; GILMOUR, S. G. Difference variance dispersion graphs for comparing response surface designs with applications in food technology. Applied Statistics. v. 48, p. 441-455, 1999.

3. VINING, G. A Computer Program for Generating Variance Dispersion Graphs. Journal of Quality Technology. v. 25, n. 1, p. 45-58, 1993. 2. Vining, G. Corrigenda. Journal of Quality Technology. v. 25, n. 4, p. 333-335, 1993.

4. ZAHRAN, A.; ANDERSON-COOK, C. M.; MYERS, R. H. Fraction of design space to assess prediction capability of response surface designs. Journal of Quality Technology. v. 35, n. 4, p. 377-386, 2003.
}
\author{Cesar Buchile Abud de Oliveira}
\note{
%%  ~~further notes~~
}

%% ~Make other sections like Warning with \section{Warning }{....} ~

\seealso{
%% ~~objects to See Also as \code{\link{help}}, ~~~
}
\examples{
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

# Example 3: a split-plot design in cuboidal region, eta=1

data(DES3)
RES3=vardispersion(N=42,K=5,DES3,DES.TYPE=2,NWPT=21,NSPT=2)

# Example 4: a split-plot design in cuboidal region, eta=2

data(DES4)
RES4=vardispersion(N=42,K=5,DES4,DES.TYPE=2,NWPT=21,NSPT=2, ETA=2)
}
% Add one or more standard keywords, see file 'KEYWORDS' in the
% R documentation directory (show via RShowDoc("KEYWORDS")):
% \keyword{ ~kwd1 }
% \keyword{ ~kwd2 }
% Use only one keyword per line.
% For non-standard keywords, use \concept instead of \keyword:
% \concept{ ~cpt1 }
% \concept{ ~cpt2 }
% Use only one concept per line.
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
