+++
id = "sk-def-curve"
kind = "section"
title = "Curves and genus"
lean = ["AlgebraicGeometry.IsCurve", "AlgebraicGeometry.Scheme.Hom.genus"]
order = 417
+++
*Definition (sketch).*

Let $k$ be algebraically closed. A *curve* over $k$ is a
separated scheme of finite type over $k$ of dimension $\le1$; it is
*smooth* (resp. *proper*) if its structure morphism is
smooth (resp. proper). A *connected curve* is a nonempty
connected curve of dimension exactly $1$ (so $\Spec k$ is a curve but
not a connected curve; a statement about a "connected" curve below
is a statement about a nonempty connected curve of dimension $1$).
For $C$ smooth proper connected, the
*genus* of $C$ is $g=\dim_{k}H^0(C,\Omega^1_{C/k})$ (invariant
under algebraically closed extension of $k$).
