+++
id = "sk-def-smooth"
kind = "section"
title = "Smooth and allowed coefficients"
order = 1373
lean = ["AlgebraicGeometry.Scheme.IsTorsionSheafOfInvertibleOrder"]
+++
*Definition (sketch).*

A morphism is *smooth* if it is flat, locally of finite
presentation and its geometric fibres are smooth varieties; finitely
many coordinates always give
$\Aaf^d_S\to S$ smooth. A sheaf has *allowed torsion* if all
its geometric stalks are torsion of orders invertible on the base.
"On the base" is read globally: each element of each geometric
stalk is killed by some integer invertible on all of $S$, with no
common annihilator required (this is what the filtered union below
expresses); it is stronger than invertibility of the orders near the
support — on $S=\Spec\Z$ the sheaf $j_!(\Z/2)$,
$j:D(2)\hookrightarrow S$, has the latter property but not the
former. The sheaves $\Z/d\Z$ ($d$ invertible) and their filtered
unions are the coefficient objects used below
($\mathcal F=\varinjlim_d\mathcal F[d]$ over the $d$ invertible on
$S$, and inverse image and $R^q$ of qcqs morphisms commute with the
filtered colimit).
