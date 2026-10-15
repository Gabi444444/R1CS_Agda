
def verify_simple(v_1,v_2,abst):
    size = len(abst)
    relation_1 = sum([v_1[0][i]*abst[i] for i in range(size)])*sum([v_1[1][i]*abst[i] for i in range(size)])
    relation_2 = sum([v_2[0][i]*abst[i] for i in range(size)])+sum([v_2[1][i]*abst[i] for i in range(size)])
    print(relation_1,relation_2)
    return relation_1 == relation_2

def verify(abst,equations,constraints,*args):
    size = len(abst)
    vectors = [arg for arg in args]
    relations = []
    for j,k in enumerate(equations):
        if k == "*":
            relation = sum([vectors[j][0][i]*abst[i] for i in range(size)])*sum([vectors[j][1][i]*abst[i] for i in range(size)])
        else:
            relation = sum([vectors[j][0][i]*abst[i] for i in range(size)])+sum([vectors[j][1][i]*abst[i] for i in range(size)])
        relations.append(relation)
    print(relations)
    statement = True 
    if len(relations) > 2:
        if relations[len(relations)-3] != relations[len(relations)-1]:
            statement = False
    elif relations[len(relations)-2] != relations[len(relations)-1]:
        statement = False
    if statement:
        for i in range(len(abst)-2,len(abst)-2-constraints,-1):
            print(abst[i])
            if abst[i] not in relations:
                statement = False
    return statement

if __name__ == '__main__':
    ## EQUATION: 5x^2 - y.  5x^2 = z+y
    
    x = int(input())
    y = int(input())
    z = 5*(x**2)-y
    
    vector_1 = [[0,5,0,0],[0,1,0,0,]]
    vector_2 = [[0,0,0,1],[0,0,1,0]]
    
    equations = ["*","+"]
    abst = [1,x,y,z]
        
    
    print(verify(abst,equations,0,vector_1,vector_2,),"\n")
    
    ## EQUATION: xy+8.  xy = z-8
    
    new_vec1 = [[0,1,0,0],[0,0,1,0]]
    new_vec2 = [[-8,0,0,0],[0,0,0,1]]
    z = x*y+8
    
    equations = ["*","+"]
    new_abst = [1,x,y,z]
    
    print(verify(new_abst,equations,0,new_vec1,new_vec2),"\n")
    
    ## EQUATION: xy+z. xy = w-z
    
    z = int(input())
    w = x*y+z
    vars_1 = [[0,1,0,0,0],[0,0,1,0,0]]
    vars_2 = [[0,0,0,-1,0],[0,0,0,0,1]]
    
    equations = ["*","+"]
    vars_abst = [1,x,y,z,w]
    
    print(verify(vars_abst,equations,0,vars_1,vars_2),"\n")
    
    ## EQUATION: xy+zw. xy = sigma-v1. v1 = zw
    
    w = int(input())
    sigma = x*y+z*w
    v1 = z*w
    
    long_vec1 = [[0,1,0,0,0,0,0],[0,0,1,0,0,0,0]]
    long_vec2 = [[0,0,0,1,0,0,0],[0,0,0,0,1,0,0]]
    long_vec3 = [[0,0,0,0,0,-1,0],[0,0,0,0,0,0,1]]
    
    equations = ["*","*","+"]
    long_abst = [1,x,y,z,w,v1,sigma]
    
    print(verify(long_abst,equations,1,long_vec1,long_vec2,long_vec3),"\n")
    
    # EQUATION xy+zw+8.   v1+8 = sigma-v2. v1 = xy, v2 = zw
    
    sigma = x*y+z*w+8
    v1 = x*y
    v2 = z*w
    
    attempt_1 = [[0,1,0,0,0,0,0,0],[0,0,1,0,0,0,0,0]]
    attempt_2 = [[0,0,0,0,0,1,0,0],[8,0,0,0,0,0,0,0]]
    attempt_3 = [[0,0,0,1,0,0,0,0],[0,0,0,0,1,0,0,0]]
    attempt_4 = [[0,0,0,0,0,0,0,1],[0,0,0,0,0,0,-1,0]]
    
    equations = ["*","+","*","+"]
    attempt_abst = [1,x,y,z,w,v1,v2,sigma]
    
    print(verify(attempt_abst,equations,2,attempt_1,attempt_2,attempt_3,attempt_4),"\n")
