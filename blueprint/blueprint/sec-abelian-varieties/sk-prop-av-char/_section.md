+++
id = "sk-prop-av-char"
kind = "section"
title = "Abelian varieties are the complete group varieties"
lean = ["AlgebraicGeometry.IsAbelianScheme.geometricallyIntegral", "AlgebraicGeometry.IsAbelianScheme.irreducibleSpace"]
order = 471
uses = ["sk-def-av", "sk-def-av-group-scheme"]
+++
*Proposition (sketch).*

Let $G$ be a group scheme over a field $k$ which is proper, connected
and smooth over $k$. Then $G$ is irreducible and geometrically
integral, and is therefore an abelian variety in the sense of
[sk-def-av]; conversely every abelian variety is a proper connected
smooth group scheme. Hence ``abelian variety'' and ``complete group
variety'' describe the same class.

## Proof

$G$ is locally irreducible because it is smooth, so connectedness
makes it irreducible; being connected it is its own identity component,
which for a group scheme of finite type over a field is geometrically
irreducible; smoothness gives geometric reducedness. Hence $G$ is
geometrically integral, and the two notions agree. The smoothness
hypothesis cannot be dropped: for $\operatorname{char}k=p>0$ the
finite group schemes $\alpha_p=\Spec k[x]/(x^p)$ and
$\mu_p=\Spec k[x]/(x^p-1)$ are proper and connected but not reduced.

Uses: [sk-def-av-group-scheme], [sk-def-av]
