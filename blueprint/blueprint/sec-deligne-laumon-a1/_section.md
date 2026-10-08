+++
id = "sec-deligne-laumon-a1"
kind = "section"
title = "Deligne–Laumon on the Affine Line: Proof Sketch"
order = 2721
uses = ["sec-algebraic-groups-lie-algebras", "sec-fourier-transform", "sec-poincare-duality", "sec-purity-real-sheaves", "sec-six-functors", "sec-smooth-purity", "sec-trace-formula"]
+++
content: a sketch of the affine-line weight estimate via curve perverse sheaves,
Fourier transform, real-sheaf purity, and positive squared traces.  
key result: Theorem [sk-thm-dl-a1-upper].  
references: `weil2curves_blueprint.tex`, especially
`sk-thm-dl-a1-upper`; source labels below are provenance.

The target is the affine-line step in the source: if $j:U_0\hookrightarrow \mathbf A^1_{\mathbf F_q}$ is dense and $F$ is pure of weight $w$ and
unramified at infinity, then $H_c^r(\mathbf A^1,j_*F)$ has weights at most
$w+r$. The essential case is degree one. The proof first treats
irreducible nonconstant sheaves by Fourier transform, and then passes
through a composition filtration. The unramifiedness hypothesis belongs
to this intermediate theorem; the source's later reduction to general
curves is a further argument.
