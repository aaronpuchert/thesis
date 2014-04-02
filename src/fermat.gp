/*
	CONVENTIONS
Plücker coordinates are represented as vectors [p_01, p_02, p_03, p_12, p_13, p_23].
Sets of vectors are represented by matrices, the vectors being the columns of the matrix.
We have in general d-1 = q = p^n, p being the characteristic.
*/

/* GENERAL FUNCTIONS */
\\ Convert a Plücker vector into the more readable matrix
\\
\\ If ord=0, we have ordinary coordinates, for ord!=0 their exponents corresponding
\\ to a primitive root with order ord
plmat(p, ord=0) =
{
	my(inv);
	if(ord,
		inv = x->x+ord/2,
	\\ else
		inv = x->-x
	);

	[0,p[1],p[2],p[3];
	inv(p[1]), 0, p[4], p[5];
	inv(p[2]), inv(p[4]), 0, p[6];
	inv(p[3]), inv(p[5]), inv(p[6]), 0]
}

\\ Test if two lines intersect
intersect(p, q) =
{
	my(res);
	res = sum(n=1,6,-(-1)^n*p[n]*q[7-n]);
	return(res==0)
}

testperms = [[1,2,3,4],[1,3,2,4],[1,4,2,3]];
\\ Test if a line is on F_d
test(p, d) =
{
	my(M, a, b);
	M = plmat(p);
	a = apply(x->vecsum(x),Vec(apply(x->x^d,M)));
	b = apply(x->M[x[2],x[3]]^(d-1)*M[x[1],x[3]] + M[x[2],x[4]]^(d-1)*M[x[1],x[4]], testperms);
	concat(a,b)
}

/* SPECIFIC FUNCTIONS */
\\ Compute appropriate field F_p^2n
cyclofield(p, n) =
{
	my(pol, root);
	pol = ffinit(p, 2*n);
	root = ffprimroot(ffgen(pol,a));
	return(root)
};

\\ Enumerate elements of a field
ffelem(primroot) = vector(fforder(primroot),n,primroot^(n-1));

\\ Compute a "cartesian product" of two vector sets
cartesian(x, y) =
{
	my(a=matsize(x)[2], b=matsize(y)[2], res=matrix(matsize(x)[1]+matsize(y)[1], a*b));
	for(i=1, a,
		for(j=1, b,
			res[,(i-1)*b+j] = concat(x[,i], y[,j])
		)
	);
	return(res)
};

\\ Compute zero sums of n units.
\\ Assume primroot is the generator of a finite field's unit group.
\\ This is clearly the case for what we want.
sumofunits(primroot, n, exponents, normed=1) =
{
	my(res, elem=ffelem(primroot));

	\\ possibilities for the first coordinate
	if (normed,
		res = Mat([primroot^0]),
	\\ else
		res = Mat(elem)
	);

	\\ possibilities for the middle n-2 coordinates
	for(i=2, n-1,
		res = cartesian(res, Mat(elem))
	);

	\\ now compute the last coordinate and throw everything out that doesn't work
	resvec = Vec(res);
	resvec = apply(x -> concat(x,-vecsum(x)), resvec);
	resvec = select(x->x[n], resvec);
	res = Mat(resvec);

	\\ compute logarithms, if wanted
	if (exponents,
		apply(x->fflog(x,primroot), res),
	\\ else
		res
	)
};

shiftthree = concat(matrix(3,6)~, concat(matid(3), matrix(3,3))~)~;
coordmat(d, modulo=0) =
{
	my(F,G,S,B);
	F=matdiagonal([d/2,d/2,d/2]);
	G=matdiagonal([(d-2)/2,(d-2)/2,(d-2)/2]);
	B=concat(F,G);
	S = [0,0,1,0,0,0;0,1,0,0,0,0;1,0,0,0,0,0;0,0,0,0,0,-1;0,0,0,0,-1,0;0,0,0,-1,0,0];
	B=concat(B~,(B*S)~)~;
	if(modulo,
		B=concat(B,matdiagonal(vector(6,n,d*(d-2))))
	);
	concat(B,d*(d-2)/4*[1,0,1,1,0,1]~)
};

\\ compute all irregular lines, i.e. their parameters or logarithmic Plücker coordinates
\\ output flag: 0=parameters, 1=log. coord., 2=coord.
lines(primroot, output=0) =
{
	my(q=sqrtint(fforder(primroot)+1), abc, parvec, param, res);

	\\ get all (normed, uniquely lifted) possibilities for a,b,c
	abc = sumofunits(primroot^(q+1), 3, 1);

	\\ combine with all possible alpha, beta, gamma
	\\ first build a preliminary list of alpha, beta, gamma; then adjust
	parvec = vector(q+1, n, 2*n-2);
	param = cartesian(cartesian(Mat(parvec), Mat(parvec)), Mat(parvec));
	res = cartesian(abc, param);
	res = Mat(apply(x -> x+shiftthree*x+(q+1)/2*[0,0,0,1,0,1]~, Vec(res)));

	\\ compute coordinates, if desired
	if(output,
		res = coordmat(q+1)*concat(res,vector(length(res),n,1)) % fforder(primroot));
	if(output > 1,
		res = apply(x->primroot^x, res));
	return(res)
};
