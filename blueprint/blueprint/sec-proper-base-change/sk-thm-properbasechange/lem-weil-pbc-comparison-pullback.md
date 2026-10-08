+++
id = "lem-weil-pbc-comparison-pullback"
kind = "lemma"
title = "Comparison inverse image commutes with scheme pullback"
order = 1290
uses = ["def-weil-pbc-cartesian-square", "def-weil-pbc-inverse-image", "def-weil-pbc-site-comparison-morphism", "lem-weil-pbc-comparison-sections"]
+++
For $u:U\to V$ there is a natural isomorphism

$$
 \nu_U^*u_{\Et}^{-1}\xrightarrow{\sim}
 u_{\Proet}^{-1}\nu_V^*.
$$

It is compatible with identity maps, composites, and the cartesian
identification in [def-weil-pbc-cartesian-square].

## Proof

On a representable etale sheaf $h_W$, both inverse-image composites give the
pro-etale sheaf represented by $W\times_VU$. To check the comparison inverse
image in this assertion, work on affine charts and write a basis object as a
limit of affine etale schemes. Maps from this limit into an affine etale
scheme of finite presentation descend to a stage, so the formula of
[lem-weil-pbc-comparison-sections] is exactly the representable sheaf of the
base change. General etale $W$ follows by its affine covering and sheaf
gluing. Scheme inverse image on a representable is its base change by the
defining base-change functor on sites.

Every sheaf is a colimit of representable sheaves over its sections.
Explicitly, the coproduct of these representables maps epimorphically to the
sheaf, and the two projections from its relation sheaf give a coequalizer
presentation. In module sheaves use free modules on those representables and
a cokernel presentation instead. Inverse images preserve these colimits. Thus
the just specified identifications extend uniquely to an isomorphism on every
sheaf for the morphism of [def-weil-pbc-site-comparison-morphism]. On
representables the identity and composition equations are the identity and
associativity of scheme base change, including the chosen cartesian
identification in [def-weil-pbc-cartesian-square]. The colimit presentations
extend these equations to all sheaves. Exactness gives the same coherent
isomorphisms on complexes.
