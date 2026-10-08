+++
id = "lemma-nagata-scheme-image-ideal-qc"
kind = "lemma"
title = "Mathlib scheme-theoretic image interface"
order = 64
lean = ["AlgebraicGeometry.Scheme.Hom.image"]
+++
For a morphism $g\colon T\to Y$, Mathlib defines its scheme-theoretic image
as the closed subscheme cut out by the ideal sheaf $\operatorname{ker}(g)$.
It also supplies the closed immersion
$g_{\mathrm{im}}\colon\operatorname{SIm}(g)\hookrightarrow Y$ and the
factor map $g^{\mathrm{im}}\colon T\to\operatorname{SIm}(g)$.
When $g$ is quasi-compact, the stalk maps of $g^{\mathrm{im}}$ are
injective and the support of $\operatorname{ker}(g)$ is the closure of the
topological range of $g$.

*Implementation note.* The verified declarations are
`AlgebraicGeometry.Scheme.Hom.image`, `Scheme.Hom.imageι`,
`Scheme.Hom.toImage`, `Scheme.Hom.toImage_imageι`,
`Scheme.Hom.toImage_app_injective` (under quasi-compactness), and
`AlgebraicGeometry.Scheme.IdealSheafData.support_map` together with
`Scheme.IdealSheafData.map_bot` (under quasi-compactness). No
invented `Scheme.Hom.support_ker` or
`schemeTheoreticImageIdeal_isQuasiCoherent` declaration is assumed.

## Proof

This block records the existing Mathlib construction. The closed
subscheme is `Scheme.Hom.image g`, its inclusion is the declaration
`Scheme.Hom.imageι g`, and the factor map is
`Scheme.Hom.toImage g`; the displayed composite is the theorem
`Scheme.Hom.toImage_imageι`. The additional quasi-compact
assertions are exactly the two declarations named in the implementation
note, so no direct-image calculation is silently imported here.
