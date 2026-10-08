+++
id = "sk-prop-nagata-sketch-approximation"
kind = "section"
title = "Absolute approximation and descent"
order = 326
lean = ["AlgebraicGeometry.Scheme.nonempty_noetherianApproximation", "AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated"]
+++
*Proposition (sketch).*

A qcqs scheme $S$ is an inverse limit $S=\varprojlim S_\lambda$
with affine transitions and each $S_\lambda$ of finite type over
$\Z$. A separated finitely presented $X\to S$ descends, at a
sufficiently large index, to a separated finitely presented
$X_\lambda\to S_\lambda$.

## Proof

On an affine chart, write its ring as the filtered union of its finitely
generated $\Z$-subalgebras. A finite affine cover and finite affine
refinements of its overlaps allow the gluing data to be recorded at a
finite stage, giving absolute approximation (01ZA).
For $X\to S$, descend the finitely many generators, relations,
overlap maps and cocycle equalities (01ZM).
The diagonal of a finitely presented morphism is finitely presented;
its being a closed immersion holds at a sufficiently large stage
because it holds after passage to the limit (01ZQ).
This supplies separatedness of the descended model.
