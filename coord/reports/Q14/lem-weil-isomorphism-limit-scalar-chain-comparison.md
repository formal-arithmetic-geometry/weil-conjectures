## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtale.LimitScalarChainComparison` states
`AlgebraicGeometry.Scheme.limitScalarChainComparison`, with its whole proof `sorry`.
Its five auxiliary declarations expand the transported module action, local section,
two termwise functors, and the exact normalization and homotopy predicate. Their data
are explicit; no map is selected from a mere existence assertion.

The source read is `literature/stacks-project/sites-modules.tex`,
`lemma-tensor-product-pullback` (Tag 03EL), together with all five calculations of
this node's proof. The lemma supplies functorial tensor pullback; the projection,
scalar-transport, differential and homotopy calculations are the node's own extension.
No correction of the mathematical statement is needed.

The hypothesis and conclusion correspondence is as follows.

- The scheme isomorphism is `{X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]`.
  The small sites are exactly `X.ProEt`, `Y.ProEt`, with `ProEt.topology`.
  They retain object universe `t+1` and morphism universe `t`. Coefficient rings and
  modules have universe `max r (t+1)` with independent `r`.
- Inverse image `F` is `isoSectionwiseInverseImage g CommRingCat`, the recorded
  canonical sectionwise presentation under the isomorphism-site identification.
  Its value at U is the original sheaf at `proEtaleIsoPostcompose g |>.obj U`.
  It works for arbitrary, nonconstant ring sheaves, not just constant coefficients.
- The four inverse systems are `AX BX AY BY : ℕᵒᵖ ⥤ Sheaf ... CommRingCat`.
  Index `op n` means the positive stage m=n+1. Their functor maps encode all
  transitions and their composites. `iX`, `iY` are natural transformations, so
  the finite coefficient maps commute with every transition.
- `cA`, `cB` are natural isomorphisms from the inverse-image diagrams to the X
  diagrams. Naturality is exactly transition compatibility of all stage ring
  isomorphisms. `hstage` is the displayed coefficient square as an equality of
  natural transformations, equivalently its equality at every stage.
- `R_W`, `S_W` are `limit AY`, `limit BY`, `limit AX`, `limit BX` respectively;
  the projections are the existing `limit.π`. `j_W` is `limMap iY` or `limMap iX`,
  the actual limit-induced map, not an arbitrary map with an extra hypothesis.
- `cR`, `cS` are the specified ring isomorphisms at the limits. The two projection
  equations are `hR`, `hS`, quantified over every `m : ℕᵒᵖ`.
- `scalarChainTransport g cR` and `... cS` are the functors G_R and G_S.
  They use `isoSectionwiseModuleInverseImage` with the image of c under forgetting
  commutativity. Its action on sections is by c inverse, leaving underlying groups
  and elements unchanged. `scalarChainSection` is the unchanged underlying element.
- The first conclusion is `F.map (limMap iY) ≫ cS.hom = cR.hom ≫ limMap iX`,
  i.e. c_S F(j_Y)=j_X c_R in Lean's left-to-right composition convention.
- `scalarChainLeft` is G_R followed by `extensionFunctor jX`;
  `scalarChainRight` is `extensionFunctor jY` followed by G_S. These are the actual
  sheafified balanced scalar extensions. Applying `mapHomologicalComplex (.up ℤ)`
  gives their unbounded cochain versions, with differential the image of d_P,
  namely d_P tensor 1. This is the canonical termwise model of direct-sum total
  tensor with the coefficient sheaf concentrated in degree zero: each degree has
  only the summand (n,0), so no boundedness restriction is introduced.
- `∃! b : left.mapHomologicalComplex ... ≅ right.mapHomologicalComplex ...`
  gives b_P at every complex, its S_X-linear components and inverse, compatibility
  with differentials in both directions, and naturality for every chain map.
  Uniqueness expresses the node's phrase 'characterized on local tensors'.
  This node explicitly needs an actual chain comparison before localization,
  with a local section formula and homotopies; a derived-only isomorphism would
  discard the information the node and its users request.
- The first conjunct of `ScalarChainComparisonRules` is the forward rule for
  every P, degree n, site object U, local p, and local s_0. `extensionTmul` puts
  the scalar first, so its input is c_S(s_0) tensor Fp, representing the node's
  Fp tensor c_S(Fs_0) by the canonical commutative tensor convention. The output
  is `scalarChainSection ... (extensionTmul jY ... s_0 p)`, exactly F(p tensor s_0).
  The second conjunct gives the reverse displayed rule for b inverse, with the
  same local variables and specified c_S. Surjectivity of c_S covers every
  transported scalar, and local tensors generate after sheafification.
- The final conjunct quantifies over all P,Q, chain maps a,a', and homotopies h.
  The existing `Functor.mapHomotopy` constructs the homotopies under the two
  additive termwise functors, with components their images of h's components.
  The two equations intertwine these homotopies with b and b inverse in every
  pair of integer degrees. Thus both directions and the actual transported
  homotopies are specified, rather than only existence of some homotopy.
- There is no flatness, K-flatness, boundedness, finite coefficient or nonempty
  scheme assumption anywhere in the signature.

Dependency declarations used, with source signatures and docstrings inspected:

- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `Scheme.proEtaleSheafInverseImage`, `proEtaleBaseChange` and module inverse image.
  They are reexported by the sectionwise dependency. The sectionwise model is the
  canonical isomorphism-site model, not a separately postulated inverse image.
- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`:
  `Scheme.isoSectionwiseInverseImage`, `isoSectionwiseModuleInverseImage`, and its
  additive/exact instances; `ProEtaleIsomorphismInverseImage` supplies
  `proEtaleIsoPostcompose` and its comma-normalized section identification.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently Mathlib `SheafOfModules` and its category of sectionwise linear maps.
- `Sheaf.SecSmoothPurity.CochainCoefficientArrows`: `CochainPullback.extensionFunctor`,
  `extensionTmul`, `extensionFunctorAdditive`, and the existing `Modules`, `Complex`
  abbreviations inherited from `CochainTensorCoherenceData`. The extension object
  is `SheafOfModules.changeOfRings`, its map is `changeOfRingsHom`, and its generator
  is the actual sheafification-unit image of the balanced tensor.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: the existing
  sheaf tensor and its independent-universe monoidal/additive structures, reexported
  through the cochain coefficient module. `CochainComplex.mapBifunctor` is the
  recorded total tensor; extension by the degree-zero ring is expressed by its
  canonical termwise model, retaining its differential.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `limit`, `limit.π`, `limMap`;
  `Mathlib.Algebra.Category.Ring.Limits` supplies ring limits.
- `Mathlib.Algebra.Homology.Homotopy`: `Functor.mapHomotopy`;
  `Mathlib.Algebra.Homology.Additive`: `Functor.mapHomologicalComplex`.
- Proof-only import `Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison`
  retains the tensor-comparison proof dependency. Its primary theorem and the
  `inverse`, `tensor`, `pure`, `comparison` interfaces were inspected. The module
  sheafification proof dependency is already reexported by scalar extension.
- The scheme-properties and size nodes are conventions with no declaration;
  `Scheme`, `IsIso` and the explicit universe binders implement the relevant parts.

The item cites the already landed definition node
`def-weil-proetale-iso-sectionwise-inverse-image` for the canonical sectionwise
site, sheaf and module constructions, and `def-pur-cochain-coefficient-arrows`
for scalar extension. It also cites `def-pur-cochain-tensor-coherence-data` for
the `Modules` and `Complex` abbreviations. The theorem node
`lem-weil-proetale-isomorphism-inverse-image` stays in `proof_deps` only.
No new node, duplicate declaration or statement correction is needed.

Edge cases checked by reading the fully elaborated signature and the constructions:
empty X and Y; zero coefficient rings or modules; constant and nonconstant sheaves;
identity and arbitrary scheme isomorphisms; arbitrary transition maps, including
non-surjective maps; n=0 for the first positive coefficient stage; complexes
unbounded in both directions; arbitrary integer degrees of homotopies; independent
larger coefficient universe r. None requires an additional hypothesis. No
inverse-image/limit interchange is assumed: cR and cS are supplied with precisely
the node's projection equations, and the ring square is a conclusion.

Searches performed before writing:

- `msearch.py leansearch`, 'Inverse image along an isomorphism commutes with
  extension of scalars for complexes of sheaves of modules': eight generic hits,
  including module inverse-section formulas and pushforward natural isomorphisms;
  no inverse-limit coefficient square plus normalized chain comparison.
- `msearch.py leanfinder`, 'Inverse limit coefficient transport and natural scalar
  extension chain isomorphism for inverse image of module sheaves under a scheme
  isomorphism': eight hits about scheme and module isomorphism sections, no match.
  A second query 'Inverse image scalar extension chain comparison sheaves modules'
  found scalar restriction and generic module pullback generators, no exact result.
- `msearch.py loogle`, 'SheafOfModules.changeOfRings, HomologicalComplex.Homotopy.map',
  and then 'SheafOfModules.changeOfRings': no hit; the project-specific identifier
  is not in Mathlib's Loogle index.
- `msearch.py grep`, 'changeOfRings|mapHomotopy' and 'changeOfRings', restricted to
  Mathlib `Algebra/Category/ModuleCat`: generic scalar extension/restriction files.
- `rg` of Mathlib homology found the existing `Functor.mapHomotopy` and total
  tensor APIs. `rg` of `lean/WeilConjectures` and `lean/Sheaf` for changeOfRings,
  scalar/chain comparison and limit/scalar transport found the existing balanced
  tensor, cochain coefficient arrows, and specialized completed-coefficient results
  (`PbcAutomorphismTransport`, `IsomorphismComparisonScalarExtension`), not this
  arbitrary four-system statement. These existing definitions are reused.
- `grep -rn` of the item id in `lean/WeilConjectures`: no match. Exact searches for
  the six new declaration names in `dag/lean_names_upstream.json`, Mathlib,
  `lean/WeilConjectures` and `lean/Sheaf`: no collisions.

Validation: the prescribed `scompile.py` compiled both the sandbox and named library
module cleanly (13.2 and 13.1 seconds). All variables and universes are explicit.
The only postponed theorem is `limitScalarChainComparison`, whose docstring contains
all five natural-language proof steps. No STATEMENT-DISPUTED issue was found.


## Repair of independent return H2

The returned head is c4f540dc7154. The initial saved-packet dry run passed as
18b06cbbab1, but it still contained the ownership defect described by the return;
that commit was not pushed. Comparing the saved packet with current shared main
showed only `lean` and `stmt_deps` differences, so the accepted split is retained.

The requested definition node has meanwhile landed from Q15:
`def-weil-proetale-iso-sectionwise-inverse-image`. Its complete TeX explicitly
defines the functor `(U,u) ↦ (U,g∘u)`, sectionwise precomposition, and the module
action `a • x = c⁻¹(a) • x`. Its `existing: true` record on
`Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage` lists
`proEtaleIsoPostcompose`, `proEtaleIsoPostcompose_isContinuous`,
`isoSectionwiseInverseImage`, `isoSectionwiseModuleInverseImage` and the additive
instance. Its source is Stacks 09A5, 00WX and 03D2. I read its full node and the
existing declarations, including the current server source obtained with
`scompile.py --source`. This is exactly the ownership node requested in the
return. Following one definition per notion, this delivery cites that landed node
instead of creating a duplicate. The theorem node is removed from `stmt_deps` and
retained unchanged in `proof_deps`. The advisory concerning the cochain
abbreviations is addressed by citing `def-pur-cochain-tensor-coherence-data`.
No Lean source, mathematical statement, or proof step changes.

Repair searches actually run:

- `tools/blueprint_refs.py ancestor` returned
  `def-weil-global-geometric-frobenius`; search `sectionwise inverse image`
  returned zero blueprint nodes.
- `rg` for `isoSectionwiseInverseImage|isoSectionwiseModuleInverseImage|proEtaleIsoPostcompose`
  in definition-node files found the now-landed Q15 ownership node; the other
  textual matches are specialized point, adic and Weil-structure constructions.
  `rg` in `lean/WeilConjectures` and `lean/Sheaf/AlgebraicGeometry` located the
  existing Sheaf definitions, with no new upstream copy needed.
- `msearch.py leansearch`, query "Sectionwise inverse image of sheaves along a
  scheme isomorphism by precomposition and transport of a module action through
  the inverse ring isomorphism": eight generic scheme/module-section hits,
  including `Scheme.inv_app` and `Scheme.Modules.pullback`.
- `msearch.py leanfinder`, query "Inverse image of sheaves along an isomorphism
  computed by precomposition of sites and restriction of scalars along the inverse
  coefficient map": eight hits including `Equivalence.sheafCongr.inverse_obj_val_obj`
  and `Functor.sheafPushforwardContinuousIso_inv`; none supersedes the exact
  existing project specialization.
- `msearch.py grep`, query `sheafPushforwardContinuous|pushforward.*inv`:
  25 hits including Mathlib `CategoryTheory/Sites/Continuous.lean:362`.
  Direct reading of Mathlib `SheafOfModules.pushforward` at
  `Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean:44` confirms its
  explicit data; the existing specialization uses `inv c`.

## Second reading by Q14

This is the dispatcher's required worker self-check; the independent maintainer
review remains separate. I reread the saved Lean file against the node and the
now-landed definition node. Scheme isomorphism and independent universes match;
the four diagrams and coefficient maps match; `cA`, `cB`, `hstage` give all finite
compatibilities; `cR`, `cS`, `hR`, `hS` give exactly the projection conditions.
The coefficient-square orientation is `F(limMap iY) ≫ cS.hom = cR.hom ≫ limMap iX`.
The unique natural chain isomorphism, its forward and inverse `extensionTmul`
formulas, and both `mapHomotopy` intertwining equations remain unchanged. Empty
schemes, identity isomorphisms, zero rings, non-flat coefficient maps and unbounded
complexes are still admitted. The only mismatch found in the return was definition
ownership; it is repaired by the new citation, with the theorem kept proof-only.
The cochain-abbreviation advisory is also repaired. There is no new mathematical
or Lean declaration and no new sorry.
