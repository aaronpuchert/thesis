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

\\ Compute whether a line (p_ij) goes through a certain point (a_i) on the surface
linethroughpoint(a, p) =
{
	return(p[1]*a[3] - p[2]*a[2] + p[4]*a[1] == 0 &&
	p[2]*a[4] - p[3]*a[3] + p[6]*a[1] == 0 &&
	p[1]*a[4] - p[3]*a[2] + p[5]*a[1] == 0 &&
	p[4]*a[4] - p[5]*a[3] + p[6]*a[2] == 0)
}

testperms = [[1,2,3,4],[1,3,2,4],[1,4,2,3]];
\\ Test if a line is on F_d
lineonsurface(p, d, dbg=0) =
{
	my(M, a, b);
	M = plmat(p);
	a = apply(x->vecsum(x),Vec(apply(x->x^d,M)));
	b = apply(x->M[x[2],x[3]]^(d-1)*M[x[1],x[3]] + M[x[2],x[4]]^(d-1)*M[x[1],x[4]], testperms);
	if (dbg,
		concat(a,b),
	\\ else
		concat(a,b) == vector(7)	\\ compare with vector of seven zeros
	)
}

/* SPECIFIC FUNCTIONS */
\\ Compute appropriate field F_p^2n
cyclofield(p, n) =
{
	my(pol, root);
	pol = ffinit(p, 2*n);
	root = ffprimroot(ffgen(pol,a));
	return(root)
}

\\ Enumerate elements of a field
ffelem(primroot) = vector(fforder(primroot),n,primroot^(n-1));

\\ Compute a "cartesian product" of two vector sets
cartesian(x, y) = Mat(setbinop(concat, Vec(x), Vec(y)));

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
		res = cartesian(res, elem)
	);

	\\ now compute the last coordinate and throw everything out that doesn't work
	resvec = Vec(res);
	resvec = apply(x -> concat(x,-vecsum(x)), resvec);
	resvec = select(x->x[n], resvec);
	res = Mat(resvec);

	\\ compute logarithms, if wanted
	if (exponents,
		apply(x->fflog(x,primroot,fforder(primroot)), res),
	\\ else
		res
	)
}

\\ Helper for point enumeration
read("comb.gp");
expand(n) = pt->{
	my(m, c, i=1);
	m = matrix(4, binomial(4,n));
	c = comb(4, n);
	until((c = c.nextcomb) == 0,
		for(j=1, n,
			m[c.comb[j],i] = pt[j];
		);
		i += 1
	);
	return(m)
}

\\ Enumerate the points on F_d(F_q^2)
points(primroot) =
{
	my(q=sqrtint(fforder(primroot)+1), str, liftv=vector(3), temp);

	\\ compute sums of primroot^{q+1}
	str = vector(3, n, sumofunits(primroot^(q+1), n+1, 1, 1));

	\\ create lifting spaces
	liftv[1] = Mat(vector(q+1, n, (q-1)*(n-1)));
	for(n=2, 3,
		liftv[n] = cartesian(liftv[n-1], liftv[1])
	);

	\\ lift solutions and exponentiate
	for(n=1, 3,
		temp = cartesian(str[n], liftv[n]);
		temp = Mat(apply(x -> x[1..n+1] + concat(0, x[n+2..2*n+1]), Vec(temp)));
		str[n] = apply(x -> primroot^x, temp)
	);

	\\ expand solutions
	for(n=1, 2,
		str[n] = matconcat(apply(expand(n+1), Vec(str[n])));
	);

	\\ return them all together
	matconcat(str)
}

\\ Some matrices for line computations
distmat(comb) = vecextract(matid(6), comb);
dists = [[2,3,4,5], [1,3,4,6], [1,2,5,6]];

shiftthree() = {
	my(z = matrix(3,3), id = matid(3));
	matconcat([id,z;id,id])
}
coordmat(d, modulo=0) =
{
	my(F,G,S,B);
	F = matdiagonal([d/2,d/2,d/2]);
	G = matdiagonal([(d-2)/2,0,(d-2)/2]);
	K = (d-2)/2*[1,1,1]~*[0,1,0];
	S = [0,0,1;0,1,0;1,0,0];
	B = matconcat([F, G; S*F, -S*G + K]);
	if(modulo,
		B=concat(B,matdiagonal(vector(6,n,d*(d-2))))
	);
	concat(B,d*(d-2)/4*[1,0,1,1,0,1]~)
}

\\ Compute all (irregular) lines, i.e. their parameters or (logarithmic)
\\ Plücker coordinates. The output flag stands for:
\\	0 = parameters [a, b, c, alpha, k, gamma] (only irregular lines),
\\	1 = logartihmic coordinates (only irregular lines),
\\	2 = coordinates (both)
lines(primroot, output=0) =
{
	my(q=sqrtint(fforder(primroot)+1), abc, parvec, param,
		res=vector(4, n, matrix(6, 0)));

	\\ REGULAR LINES
	if(output > 1,
		parvec = vector(q+1, n, (q-1) * (n-1/2));
		param = cartesian(Mat(parvec), Mat(parvec));
		for(n=1, 3,
			res[n] = matdiagonal([1,1,(-1)^(n>1),(-1)^(n>2)]) *
				apply(x->primroot^x, [0,0;1,0;0,1;1,1] * param);
			res[n] = distmat(dists[n]) * res[n]
		)
	);

	\\ IRREGULAR LINES
	\\ get all (normed, uniquely lifted) possibilities for a,b=1,c
	abc = [0,1,0;1,0,0;0,0,1]*sumofunits(primroot^(q+1), 3, 1);

	\\ combine with all possible alpha, k, gamma
	\\ first build a preliminary list of alpha, k, gamma; then adjust
	parvec = vector(q+1, n, 2*n-2);
	param = cartesian(cartesian(Mat(parvec), Mat(parvec)), Mat(parvec));
	res[4] = cartesian(abc, param);
	res[4] = Mat(apply(x -> shiftthree()*x + (q+1)/2*[0,0,0,1,0,1]~, Vec(res[4])));

	\\ compute coordinates, if desired
	if(output,
		res[4] = coordmat(q+1)*concat(res[4],vector(length(res[4]),n,1)) % fforder(primroot));
	if(output > 1,
		res[4] = apply(x->primroot^x, res[4]));

	matconcat(res)
}

/* TESTING */
\\ Are the points/lines on the surface?
testpoints(p, n) =
{
	my(q=p^n, r=cyclofield(p,n), pts, vec);
	pts = points(r);
	vec = [1,1,1,1]*apply(x->x^(q+1), pts);
	vec == vector(length(pts))
}

testlines(p, n) =
{
	my(q=p^n, r=cyclofield(p,n), lin, vec);
	lin = lines(r,2);
	vec = apply(x->lineonsurface(x, q+1), Vec(lin));
	vec == vector(length(lin), n, 1)
}

\\ Are certain objects in projective space distinct from each other?
\\ Otherwise, return index pairs of duplicates.
delta(mat) = (n,m) -> matrank(vecextract(mat, [n,m])) != 2 - (n==m);
distinct(mat) =
{
	my(num=length(mat), del=delta(mat), sel);
	sel = select(n -> (n\num < n%num) && del(n\num+1,n%num+1),
		vector(num^2, n, n-1));
	if(sel, matconcat(apply(n->[n\num+1;n%num+1], sel)), 1)
}

/* EXAMINE DATA, TRY CONJECTURES */
\\ Aggregate statistics
stat(mat) =
{
	my(set, count);
	set = Set(Vec(mat));
	count = apply(x->sum(n=1, length(mat), x==mat[,n]), set);
	concat(Mat(set), count)
}

\\ How many lines go through any given one?
countintersections(primroot) =
{
	my(q=sqrtint(fforder(primroot)+1), lin, num);
	lin = lines(primroot,2);
	num = length(lin);
	vector(num, n, sum(m=1, num, intersect(lin[,n],lin[,m])))
}

\\ Which lines intersect exactly?
intersections(primroot) =
{
	my(q=sqrtint(fforder(primroot)+1), lin, num, coded_pairs);
	lin = lines(primroot,2);
	num = length(lin);
	coded_pairs = select(v->intersect(lin[,v\num+1], lin[,v%num+1]),
		vector(num^2,n,n-1));
	matconcat(apply(v->[v\num+1;v%num+1], coded_pairs))
}

\\ How many lines go through a certain point?
countlines(primroot) =
{
	my(q=sqrtint(fforder(primroot)+1), pts, lin, vec);
	pts = points(primroot);
	lin = lines(primroot,2);
	vec = vector(length(pts), n,
		sum(m=1, length(lin), linethroughpoint(pts[,n], lin[,m])));
	vec == vector(length(pts), n, q+1)
}

