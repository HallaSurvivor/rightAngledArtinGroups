import itertools

def raag(G):
    # the default notion of raag is backwards...
    return RightAngledArtinGroup(G.complement())

def words(G):
    """
    A lazy list of all the words in the generators of G
    """
    gens = list(G.gens()) + [g.inverse() for g in list(G.gens())]
    i = 1
    while 1:
        for g in itertools.product(*([gens] * i)):
            yield g
        i += 1

def extensionGraph(G, n=10):
    """
    Kim and Koberda define the 'extension graph' and give a related conjecture, which we're testing.
    
    The conjecture is that raag(G) embeds in raag(H) if and only if G embeds in extension(H),
    and is stated in their paper "embedability between right angled artin groups"
    
    @n controls how big we want this finite approximation to extension(G) to be.
    """
    AG = raag(G)
    gens = list(AG.gens())
    
    colors = {gens[i]: rainbow(len(gens))[i] for i in range(len(gens))}
    
    new_vertices = list(AG.gens())
    color = {colors[g]: [g] for g in gens}
    for g in itertools.islice(words(AG),n):
        g = product(list(g))
        for v in gens:
            x = g*v*g.inverse()
            if x not in new_vertices:
                new_vertices.append(x)
                color[colors[v]] += [x]

    return (Graph([new_vertices, lambda x,y: x*y == y*x and x != y]), color)

def monadGraph(G, n=10, onlyPrimitive=True):
    """
    Send G to comm(ragg(G))
    
    @n controls how big we want the finite approximation to be
    
    @onlyPrimitive will filter out only the primitive elements
    of the graph. Each of these corresponds to a complete countable
    graph given by its powers. But if you want an embedding, you 
    can only pick one vertex from each of these clusters, so for
    clarity of the image, we might as well only show one. 
    """
    AG = raag(G)
    gens = list(AG.gens())
    
    colors = {gens[i]: rainbow(len(gens))[i] for i in range(len(gens))}
    
    new_vertices = list(AG.gens())
    color = {colors[g]: [g] for g in gens}
    color['white'] = []
    for g in itertools.islice(words(AG),n//2):  # make the conjugates be of about the right length
        g = product(list(g))
        for v in gens:
            x = g*v*g.inverse()
            if x not in new_vertices:
                keep = True
                if onlyPrimitive:
                    for (seen, i) in itertools.product(new_vertices,range(-n,n+1)):
                        if seen^i == x:
                            keep = False
                            break
                if keep:            
                    new_vertices.append(x)
                    color[colors[v]] += [x]

    for g in itertools.islice(words(AG),n):
        g = product(list(g))
        if g not in new_vertices:
            keep = True
            if onlyPrimitive:
                for (seen, i) in itertools.product(new_vertices, range(-n,n+1)):
                    if seen^i == g:
                        keep = False
                        break
            if keep:
                new_vertices.append(g)
                color['white'] += [g]

    return (Graph([new_vertices, lambda x,y: x*y==y*x and x != y]), color)

def cliqueGraph(G):
    """
    Return a graph whose vertices are cliques in G 
    Two cliques are related iff their union is again a clique.
    """
    cliques = sage.graphs.cliquer.all_cliques(G,1,0) # min clique size 1, max clique size unbounded

    return Graph([[tuple(clique) for clique in cliques], lambda x,y: G.subgraph(x + y).density() == 1])


# example of interest -- this is the counterexample from Cassals-Ruiz, Duncan, Kazachkov: 
Gamma = Graph([['a1','a2','b','c','d','e'],[('a1','a2'),('a1','d'),('a1','e'),('a2','d'),('a2','e'),('d','e'),('c','d'),('c','a1'),('b','e'),('b','a2')]])
AGamma = raag(Gamma)

def testOnlyObviousRelations(G, n=100):
    """
    Check if the only ways for u and v to commute are:

    1. every letter in u commutes w/ every letter in v
    2. u = w^n, v = w^m for some word w

    @param G A group
    @param n the number of group elements to try
    @return: TODO

    """
    found = False
    for u in itertools.islice(words(G),n):
        for v in itertools.islice(words(G),n):
            pu = product(u)
            pv = product(v)
            if pv*pu == pu*pv:
                # check if their letters commute
                alphu = list(set(u))
                alphv = list(set(v))
                firstWay = all([x*y == y*x for x in alphu for y in alphv])

                # check if they are powers of the same element
                secondWay = False
                for i in range(len(u)):
                    sub = product(u[0:i+1])
                    if pu == sub^(len(u)//(i+1)):
                        if pv == sub^(len(v)//(i+1)):
                            secondWay = True

                if not firstWay and not secondWay:
                    found = True
                    print("We found one!")
                    print(u)
                    print(v)
    if found == False:
        print("only obvious relations existed")

def centerless(G, w, n=10000):
    """
    Test if w commutes with anything other than w^n

    @param G the raag to check inside
    @param w the word (as a list of generators) to check
    @param n how many to check
    @return: None
    """
    found = False
    W = product(w)
    ws = words(G)
    i = 0
    for wd in ws:
        if i % 1000 == 0:
            print(i, "/", n)

        if i == n:
            return

        evaledwd = product(list(wd))

        index = len(wd) // len(w)

        if evaledwd == W^index or evaledwd == W^(-index):
            print("skipped", wd)
            continue

        if W*evaledwd == evaledwd*W:
            print("Found one!")
            print(wd)
            return
        else:
            i += 1

def testSageevPentagon(n=10000):
    """
    Test if 01234 in the raag of a pentagon has trivial centralizer.

    This answers a question (exercise 3.22) in the sageev paper you're
    reading with Matt, Jacob, and Elliott.

    In particular, it shows that the element 01234 is a rank 1 isometry.

    @param n how many things to check
    @return: None

    """
    
    # the pentagon graph
    P = Graph([(0,1), (1,2), (2,3), (3,4), (4,0)])
    G = raag(P)

    v0,v1,v2,v3,v4 = G.gens()
    w = [v0,v1,v2,v3,v4]

    centerless(G,w,n)
