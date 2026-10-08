+++
id = "lem-kun-algebraic-separable-smooth"
kind = "lemma"
title = "Algebraic separable extensions are filtered colimits of finite etale algebras"
order = 1756
uses = ["def-sbc-smooth-morphisms"]
+++
Let $L/K$ be an algebraic separable extension of fields. Then $L$ is a
filtered colimit of finite separable extensions of $K$; each of those is a
finite etale $K$-algebra, hence a smooth $K$-algebra, so $L$ is a
filtered colimit of smooth $K$-algebras.

## Proof

Every element of $L$ generates a finite extension of $K$, and the
compositum of two finite subextensions is finite, so the finite subextensions
of $L/K$ form a filtered system whose union is $L$. They are separable
because $L/K$ is, and a finite separable extension of a field is a finite
etale algebra over that field. A finite etale algebra over a field is smooth:
it is of finite presentation and flat, and after base change to an algebraic
closure of $K$ it becomes a finite product of copies of that field, so its
geometric fibres are regular; this is smoothness in the sense of
[def-sbc-smooth-morphisms]. Hence $L$, being the filtered colimit of
these finite etale $K$-algebras, is a filtered colimit of smooth
$K$-algebras.
