
class Enviornment:

    def __init__(self, env = None) -> None:
        self.assignments = {}
        if env != None:
            for var in env:
                self.assignments[var] = env[var]

    def __getitem__(self, var):
        if var in self.assignments:
            return self.assignments[var]
        else:
            return None
    
    def __setitem__(self, var, value):
        self.assignments[var] = value

    def update(self, env):
        for var in self.assignments:
            if var in env:
                self[var] = env[var]
    
    def __contains__(self, var):
        return var in self.assignments


