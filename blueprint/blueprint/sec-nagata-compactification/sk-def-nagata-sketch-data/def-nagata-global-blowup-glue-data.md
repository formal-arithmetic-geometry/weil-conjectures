+++
id = "def-nagata-global-blowup-glue-data"
kind = "definition"
title = "Raw global blow-up gluing datum"
order = 54
lean = ["AlgebraicGeometry.Scheme.IdealSheafData.blowupGluingData", "AlgebraicGeometry.Scheme.IdealSheafData.blowupNatTrans_equifibered"]
uses = ["def-nagata-affine-blowup", "def-nagata-affine-blowup-restriction-map", "def-nagata-affine-proj", "def-nagata-global-blowup-local-model", "def-nagata-global-blowup-overlap-basic-map", "def-nagata-homogeneous-localization-degree-zero", "def-nagata-rees-algebra", "def-nagata-rees-localization-map", "def-nagata-rees-piece", "lemma-nagata-global-blowup-overlap-basic", "lemma-nagata-global-blowup-overlap-cocycle", "lemma-nagata-global-blowup-overlap-id-symm", "lemma-nagata-global-blowup-overlap-independent", "lemma-nagata-localization-ideal-pow", "lemma-nagata-rees-degree-zero", "lemma-nagata-rees-piece-membership", "lemma-nagata-rees-piece-mul", "prop-nagata-rees-graded"]
+++
Fix an affine cover $(V_i)_i$ of $X$. Define
$\mathsf G(X,\mathcal I,(V_i))$ to consist of the local schemes
$\mathsf B_{V_i}(\mathcal I)$, their inverse images of $V_i\cap V_j$, and
the overlap maps obtained by gluing the maps $\omega_{ij,s}$ on a chosen
basic affine cover of every intersection. The equality on intersections
required to glue these local maps is
[lemma-nagata-global-blowup-overlap-independent].

## Validity of the global blow-up gluing datum

The raw datum $\mathsf G(X,\mathcal I,(V_i))$ has isomorphism-valued
overlap maps satisfying the identity, symmetry, and triple-overlap cocycle
axioms; hence it is a scheme gluing datum.

*Proof.*
The overlap maps are isomorphisms by
[lemma-nagata-global-blowup-overlap-basic]; independence of refinements,
identity, symmetry, and the triple cocycle are given by the cited coherence
lemmas. Hence the hypotheses of
`AlgebraicGeometry.Scheme.GlueData.glued` are satisfied.
