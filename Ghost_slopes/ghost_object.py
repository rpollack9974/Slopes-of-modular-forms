from sage.geometry.newton_polygon import NewtonPolygon
#load("recursive_dimension_formulas.sage")
load("rhobar.sage")

class ghost(SageObject):
	"""This class represents a single (ghost) power series whose zeroes are determined
		by two 'abstract' functions f1,f2 playing the role of the dimension of level N
		forms and p-new level Np forms.

		The following are the data fields of ghost:

		p -- prime
		comp -- index of fixed component (between 0 and p-2 inclusive)
		series -- shell containing info of zeroes
		f1,f2 -- functions determining zeroes
		num_coefs -- number of coefficients computed
	"""

	def compute_ghost_series(self,terms):
		"""This function computes and stores the relevant ghost seris in 'shell' form --- that is,
			it sets self.series to a list whose i-th term is a list of the zeroes of the i-th coefficient
			with multiplicities.

			Inputs:
				terms -- an integer representing how much coefficients are computed.
		"""
		p=self.p
		comp=self.comp
		f1=self.f1
		f2=self.f2

		ghost_coefs = [[] for i in range(terms+1)]


		k=comp;
		if k==0 or k==1:
			k=k+p-1

		## Precompute the needed dimensions
		self.f1v = [f1(k)]
		self.f2v = [f2(k)]
		k = k + p-1
		while self.f1v[len(self.f1v)-1] <= terms+1:
			self.f1v += [f1(k)]
			self.f2v += [f2(k)]
			k = k + p-1
		
		## Starting at weight 2, we run through weights in the component,
		## compute the associated indices, and then record the weights at those
		## indices with appropriate multiplicities

		k = comp;
		if k==0 or k==1:
			k=k+p-1
		n = 0

		inds = range(self.f1v[n]+1,self.f1v[n]+self.f2v[n])
		while (len(inds)==0 or inds[0]<=terms+1):
			## This loops adds the weights to the appropriate indices with the appropriate multiplicities
			for m in range(floor((len(inds)+1)/2)):
				if m < floor(len(inds)/2):
					if inds[m]<=terms:
						ghost_coefs[inds[m]] += [(k,m+1)]
					if (inds[len(inds)-1-m]<=terms):
						ghost_coefs[inds[len(inds)-1-m]] += [(k,m+1)]
				else:
					if inds[m]<=terms:
						ghost_coefs[inds[m]] += [(k,m+1)]
			k = k + p-1
			n = n + 1
			inds = range(self.f1v[n]+1,self.f1v[n]+self.f2v[n])
		self.series=ghost_coefs

	def __init__(self,terms=50,rbdata=None,twist=None,p=None,f1=None,f2=None,comp=None,N=None,new=False):
		"""To initialize a ghost series one can either:
				(A) enter 'rbdata' and 'twist'.
					Here 'rbdata' encodes the relevant info of a fixed rhobar.  Namely,
					rbdata is 3-tuple of the form [p,k,m] where p is a prime, 
					k is an integer between 2 and p+1, and m denotes the 
					multiplicity that rhobar occurs in weight k.
					The variable 'twist' denotes a twist so that we would be working with 
					rhobar otimes omega^twist.

				or

				(B) enter 'p', 'f1', 'f2', 'comp' where p is a prime, f1 and f2 are the functions
					determining the zeroes of the ghost series, that is, f1 corresponds to the dimension
					of the "tame level space" and f2 to the "new space", and comp is the component we are working on.

				We note that in case (A) the functions f1 and f2 are computed directly from rbdata and
				stored.
		"""
		if rbdata!=None:
			assert twist != None, "If you specify rbdata, you must also specify twist"
			self.twist = twist
			self.p=rbdata.p
			self.rbdata=rbdata
			self.comp=(rbdata.krbar+(self.p+1)*twist)%(self.p-1) 
			def f1(k):
				return rbdata.tame(k,twist)
			def f2(k):
				return rbdata.new(k,twist)
		else:
			if N!=None:
				if not new:
					def f1(k):
						return dimension_cusp_forms(N,k)
					def f2(k):
						return dimension_cusp_forms(N*p,k)-2*f1(k)
				else:
					def f1(k):
						return dimension_new_cusp_forms(N,k)
					def f2(k):
						return dimension_new_cusp_forms(N*p,k)
			self.p=p
			self.comp=comp

		self.f1=f1
		self.f2=f2
		self.num_coefs=terms
		self.compute_ghost_series(terms)
		self.deltas=[[] for i in range(terms)]

	def __repr__(self):
		"""Displays the first three coefficients"""
		return repr([self.series[0],self.series[1],self.series[2],"..."])

	def __getitem__(self,i):
		"""Returns the i-th coefficient"""
		return self.series[i]

	def __add__(self,right):
		def f1(k):
			return self.f1(k) + right.f1(k)
		def f2(k):
			return self.f2(k) + right.f2(k)
		h = copy(self)
		h.deltas = [[] for i in range(h.num_coefs)]
		h.f1 = f1
		h.f2 = f2
		h.compute_ghost_series(self.num_coefs)
		return h

	def slopes(self,k,terms=None):
		"""Returns the slopes in weight k --- term-many or all if term==None"""
		NP = []
		p=self.p
		if terms==None:
			d = len(self.series)
		else:
			d = min(len(self.series),2*terms+10) ### HACKING HERE
		if p == 2:
			e = 2
		else:
			e = 1
		for i in range(d):
			y = 0
			for ss_wt in self[i]:
				k_ss = ss_wt[0]
				mult = ss_wt[1]
				if ss_wt[0] == "p":
					y += ss_wt[1]
				else:						
					#### added by john 10/17, see form_ghost_shell for instructions
					if k_ss >= 0:
						y += (valuation(k-k_ss,p)+e)*mult
					if k_ss < 0:
						y += mult
			NP += [(i,y)]

		if terms==None:
			return NewtonPolygon(NP).slopes()
		else:
			return NewtonPolygon(NP).slopes()[0:terms]

	def multiplicity(self,i):
		"""Returns the total number of zeroes with multiplicity in the i-th coefficient"""
		return sum([self[i][a][1] for a in range(len(self[i]))])

	def wadic_slopes(self,terms=None):
		"""Returns the w-adic slopes of the mod p reduction of the ghost series"""
		NP = [(a,self.multiplicity(a)) for a in range(self.num_coefs)]
		if terms==None:
			return NewtonPolygon(NP).slopes()
		else:
			return NewtonPolygon(NP).slopes()[0:terms]

	def deltai(self,i):
		"""Returns (in shell form) g[i]/g[i-1] --- VERY VERY SLOW!!"""
		if self.deltas[i]!=[]:
			return self.deltas[i]
		else:
			h=[]
			zgi = [self[i][j][0] for j in range(len(self[i]))]
			zgim1 = [self[i-1][j][0] for j in range(len(self[i-1]))]

			for z in zgim1:
				if zgi.count(z)>0:
					h+=[[z,self[i][zgi.index(z)][1]-self[i-1][zgim1.index(z)][1]]]
				else:
					h+=[[z,-self[i-1][zgim1.index(z)][1]]]
			for z in zgi:
				if zgim1.count(z)==0:
					h+=[[z,self[i][zgi.index(z)][1]]]
			self.deltas[i]=h
			return h

	def deltai_plus(self,i):
		"""Returns numerator of Delta_i"""
		h = self.deltai(i)
		return [z for z in h if z[1]>0]

	def deltai_minus(self,i):
		"""Returns denominator of Delta_i"""
		h = self.deltai(i)
		return [z for z in h if z[1]<0]

	def HZp(self,i):
		"""Returns the highest zero of Delta_i^+"""
		v=self.deltai_plus(i)
		return v[len(v)-1][0]

	def HZm(self,i):
		"""Returns the highest zero of Delta_i^-"""
		v=self.deltai_minus(i)
		return v[len(v)-1][0]

	def LZp(self,i):
		"""Returns the lowest zero of Delta_i^+"""
		v=self.deltai_plus(i)
		return v[0][0]

	def LZm(self,i):
		"""Returns the lowest zero of Delta_i^-"""
		v=self.deltai_minus(i)
		return v[0][0]


def mult(v):
	"""Returns the total number of zeroes with multiplicity in the i-th coefficient"""
	return sum([v[a][1] for a in range(len(v))])



#***********************

def periodic(list,diff):
	def f(k):
		period=len(list)
		k0=k%period
		q=(k-k0)/period
		return list[k0]+q*diff
	return f



###adds together lists of zeroes with mults
def add(v1,v2):
	z1 = [v1[a][0] for a in range(len(v1))]	
	z2 = [v2[a][0] for a in range(len(v2))]
	zs = list(set(z1 + z2))
	zs.sort()
	ans = []
	for z in zs:
		if z1.count(z)==0:
			i2 = z2.index(z)
			ans += [(z,v2[i2][1])]
		elif z2.count(z)==0:
			i1 = z1.index(z)
			ans += [(z,v1[i1][1])]
		else:
			i1 = z1.index(z)
			i2 = z2.index(z)
			ans += [(z,v1[i1][1]+v2[i2][1])]
	return ans



def serre_weight(rb,t):
	p = rb.p
	t = t%(p-1)
	k = rb.krbar
	assert k%(p-1)!=2, "Weight 2 not programmed"
	beta = (k-1+t-1)%(p-1)+1
	alpha = t
	a = min(alpha,beta)
	b = max(alpha,beta)
	return 1 + p*a + b



