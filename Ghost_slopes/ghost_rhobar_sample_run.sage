p = 7
krbar = 4

rb = rbdata(p,krbar) #creates a rhobar with serre weight 4 and multiplicity 1

g = ghost(rbdata=rb,twist=0)

print "Rhobar ghost slopes to 100";

for k in range(4,100,6):
	print k,g.slopes(k,terms=rb.tame(k,0))