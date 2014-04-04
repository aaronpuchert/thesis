\\ Enumerating combinations (subsets with k elements of a set with n elements)
comb(n,k) = [n,k,vectorv(k,i,i)]
v.nextcomb = {
	my(n=v[1], k=v[2], j=k);
	if(v[3][1]==n-k+1, return(0));
	while(v[3][j]==n+j-k, j--);
	v[3][j]++;
	for(i=j+1,k,v[3][i]=v[3][j]+i-j);
	return(v)
}
v.comb = v[3]
