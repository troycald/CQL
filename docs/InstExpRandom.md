Not recommended; returns a random instance that may not satify the given path equations.  Constructs a random instance with the specified number of generators per entity or type. Then for each generator  e:s  and fk/att  f : s -> t , it adds equation  f(e) = y , where  y:t  is a randomly selected generator (or no equation if t has no generators).
See option random_seed.