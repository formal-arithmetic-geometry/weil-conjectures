## Worker report

The delivery states the entire node, with one postponed theorem,
`SheafOfModules.ProjectionCoherence.ringedProjectionTensorComposition`, in
`Sheaf.Paper.RingedProjectionTensorComposition`. All helper definitions have real data.
There are no arbitrary proposition parameters and none of the projection identities
is an assumption. The node's mathematical statement is unchanged.

The source read is `sites-cohomology.tex`, the paragraph and displayed equation
`equation-projection-formula-map` (Tag 0B56), and `categories.tex`,
`lemma-compose-counits` (Tag 0DV0), including its explicit counit equation. The five
proof steps of the node give the formal tensor and section specializations.

Hypotheses and objects:

- A corner `X : RingedTensorCorner.{u,w}` contains a small site, topology, commutative
  ring sheaf, ordinary unbounded module derived category with localization Hom universe
  `w`, and a tensor bifunctor. Its `RingedTensorModel` identifies that bifunctor with
  signed direct-sum total tensor on every pair of flat K-flat representatives. The
  theorem quantifies over three such corners and models, without any scheme,
  geometric-point, constant-coefficient, or boundedness restriction.
- `f : RingedTensorEdge Y X` and `g : RingedTensorEdge Z Y` are geometric morphisms
  with left-exact inverse image, structural ring maps, induced module scalar extension,
  its module adjunction, and its total left derived functor with comparison. Their
  right adjoints and derived adjunctions are the recorded derived interface. No
  morphism between the presenting sites is required.
- `f.tensorComparison b a` is the existing canonical tensor comparison, fixed by its
  total-complex representative square and ordinary pure-tensor normalization. The
  formula uses `f.projection b a E Q`, the existing canonical counit mate, rather than
  making another definition of projection.
- `TensorConstraints` specifies the associator and symmetry, with equations on every
  flat K-flat representative. `totalAssociator` is the existing chain associator;
  `totalSymmetry` is the existing Koszul chain braiding. The theorem **produces** these
  constraints for X and Y, so their existence is not an extra hypothesis. The
  representative equations determine the maps; no arbitrary isomorphism is substituted.

Conclusions, in the conjunction order of the Lean signature:

1. The first conjunct is simultaneous naturality for f: the source map is
   `Y.tensor.map (Prod.mkHom (f.right.map v) z)`, and the target map is
   `f.right.map (X.tensor.map (Prod.mkHom v (f.left.map z)))`.
2. The next conjunct is the same equation for g.
3. The third conjunct is simultaneous naturality for gf, after its canonical
   pullback and direct-image composition comparisons.
4. `identityProjection X E Q = 𝟙 _` is the identity-morphism clause under the canonical
   identity comparisons. It is the mate of the identity tensor comparison through
   `Adjunction.id`, rather than an assumed identity property of f.
5. The next conjunct treats every actual identity presentation
   `h : RingedTensorEdge X X` and `s : Identity h`. Its underlying geometric and module
   comparisons, with structural-ring insertion compatibility, specify that h is the
   identity ringed morphism. The theorem produces `l : h.left ≅ id` with
   `s.Normalized l`; `identityRight h l` is the canonical adjunction conjugate. The
   equation says that `π_h` becomes the identity after precisely these source and
   target comparisons. This retains the actual identity case as well as the normalized
   `Adjunction.id` case.
6. The tensor identity compares `π_f(E,Q⊗T)` followed by `Rf(1⊗t_f(Q,T))` and the
   inverse target associator, with the inverse source associator followed by
   `π_f(E,Q) ⊗ 1_T` and `π_f(E⊗Lf Q,T)`. Both sides have source
   `Rf E ⊗ (Q⊗T)` and target `Rf ((E⊗Lf Q)⊗Lf T)`. This spells out exactly the
   associators and target pullback comparison suppressed by the TeX equation.
7. The composition equation in the normalized presentation is
   `compositeProjection f g a b c E Q = π_g(Rf E,Q) ≫ Rg.map(π_f(E,Lg Q))`.
   The left side is independently constructed as the mate of the **composite tensor
   comparison followed by the composite counit**. It is not defined to be the right
   side. Here `P_gf = g.left ⋙ f.left` and `R_gf = f.right ⋙ g.right`, which is the
   canonical-comparison normal form used explicitly in proof step 4. Mathlib's
   `g.derivedAdjunction.comp f.derivedAdjunction` supplies exactly the canonical
   composite Hom bijection and the counit of Tag 0DV0.
8. The next conjunct also gives the full transported equation for every presented
   composite `h : RingedTensorEdge Z X` and `s : Composition f g h`. The ordinary
   composite map is fixed by its insertion equation. The theorem produces
   `l : h.left ≅ g.left ⋙ f.left` with `s.Normalized l`, the full K-flat representative
   equation. `compositionRight f g h l` is the adjunction-compatible canonical
   `h.right ≅ f.right ⋙ g.right`. In that equation the left side applies `π_h`, the
   right comparison at its target, and `Rg Rf(1⊗l_Q)`; the right side applies the
   right comparison at E tensored with `1_Q`, then `π_g`, then `Rg π_f`. Thus it
   compares the actual composite projection as well as its normal form. This
   conjunct also states simultaneous naturality for the actual h.
9. For every W, i, p and specified ringed section `s : Section i p`, the theorem
   produces both W's canonical tensor constraints and a pullback comparison
   `l : p.left ⋙ i.left ≅ 𝟭 _`. `s.Normalized l` fixes its value on every flat
   K-flat representative to the termwise **specified** ordinary section map.
   `sectionRight i p l` is its adjunction conjugate, giving the corresponding
   `Ri ⋙ Rp ≅ id` comparison, including counits. The final equality says that
   `sectionComposite ... M V` is `𝟙 (M⊗V)` for arbitrary unbounded M,V. Its definition
   inserts the inverse right comparison on V, the symmetry-ordered projection for p,
   Rp of the symmetry-ordered projection for i, the right comparison on the resulting
   tensor, and the pullback comparison l on M. Thus every arrow of the displayed
   section composite, including tensor symmetries, is retained.

Both kinds of comparison data are specified at the ordinary level. `Composition`
specifies `h ≅ gf` using the underlying geometric comparison and its induced module
comparison, with the same structural-ring insertion normalization.
The section data is specified at the ordinary level: `Section.sets` is the underlying
geometric 2-isomorphism, `Section.modules` its module comparison, and `Section.insertion`
requires compatibility with the structural scalar-extension insertions on every module.
This is the same generator normalization as the existing `RingedTensorSquare` interface;
it does not assume a derived tensor coherence or a projection formula. The derived
comparison and its normalization are conclusions, not supplied as an arbitrary map.

Dependencies used, with modules and declarations:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  used transparently by the existing corner's module category.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, and `Qh`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`.
  This current recorded primary module is publicly imported, retaining its independent
  site-universe interface. The existing corner/edge specialization uses the canonical
  comparison from the same representative construction.
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`:
  `CategoryTheory.ringedToposDerivedPushforwardComposition`, imported for the normalized
  identification `R_gf ≅ R_f ⋙ R_g`. The Lean composition clause is written after this
  and the canonical pullback comparison, as permitted by the node's explicit convention.
- `Sheaf.Paper.ProjectionMateExact`: `SheafOfModules.ringedProjectionMateExact` and
  its transparent `RingedTensorCorner.mateModules`, `.mateDerived`, `.mateTensor`,
  and `.mateFlat` interfaces.
- `Sheaf.Paper.RingedTensorSquarePresentation`: `RingedTensorCorner`,
  `RingedTensorModel`, `RingedTensorEdge`, `.tensorComparison`, and `.insertion`.
- `Sheaf.Paper.RingedExchangeTensorCoherence`: the already published
  `RingedTensorEdge.projection`, reused verbatim. The two corresponding landed nodes
  are added to `stmt_deps` because their interfaces appear in the signature.
- `Mathlib.CategoryTheory.Adjunction.Basic` and `.Mates`: `Adjunction.comp`,
  `Adjunction.id`, `Adjunction.homEquiv`, and `conjugateIsoEquiv`. These are the recorded
  Mathlib matches for the composite-adjunction and adjunct-counit proof dependencies.
- `WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat` is a proof import.
  The structural proof node `lem-sfb-ringed-derived-monoidal-comparisons` currently has
  no recorded module, so it contributes no import; no new declaration is copied from it.

Edge cases checked: the identity geometric morphism and identity adjunction; i and p
both identities; M=0 or V=0; zero coefficient sheaves; tensor units and shifted objects;
nonflat structural ring maps such as Z to Z/2 on the point site; and unbounded complexes.
None requires inverting a projection map. There is no boundedness, perfectness, flatness
of a ring map, or projection-isomorphism hypothesis. The tensor symmetry is the signed
Koszul symmetry, so odd shifts are included rather than silently treated as unsigned.
The site/ring/module bound is the existing corner's common small-site universe u; the
localization Hom universe w remains explicit and independent. This uses the recorded
small-site presentation, not an equality imposed on a pro-etale site's native universes.

Searches actually run during this work:

- `msearch.py leanfinder`, query “Projection formula morphisms tensor associativity
  compatibility with composition and section in unbounded derived categories of ringed
  topoi”: eight unrelated resolution/tensor hits, including projective-resolution
  composition, cochain CM5b, `Tor'_map_app`, and chain unitors; no match.
- `msearch.py loogle`, query `"rightAdjointProjectionMap"`: zero hits.
- `msearch.py grep`, query `rightAdjointProjectionMap|projectionFormula` in
  `CategoryTheory/Monoidal`: zero hits.
- `rg` in upstream `WeilConjectures` for `rightAdjointProjectionMap` found
  `Adjunction/ProjectionMap.lean` and `ProjectionMapCompat.lean`. Their full interfaces
  were read: the composition theorem is abstract, with no ringed-site tensor models or
  tensor/section clause. It is used for the proof rather than falsely attached as the
  whole node.
- `rg` in Mathlib and the project for derived monoidal structures, projection,
  tensor comparisons, and the item ID found the existing `RingedTensorEdge.projection`
  and `RingedTensorSquare` interfaces; these are reused. The scheme and constant-sheaf
  derived monoidal structures do not cover arbitrary ringed topoi.
- The live source of `Sheaf.Paper.RingedExchangeTensorCoherence` was read with
  `scompile.py --source`; it agrees with the projection declaration used here.

No statement correction, disputed mathematical statement, new DAG node, or dependency
record repair is needed. The additions in the owning module only expose the canonical
constraints and the composites that the node's equations already mention. The sole
postponed theorem's docstring contains the complete five-step proof plan.

Validation: the final module compiles cleanly through the prescribed `scompile.py`
interface used by `deliver2.py`. The required `deliver2.py --no-push` dry run returned
OK: the final packet passes the server preflight and per-file compilation. There is
one named postponed theorem and no postponed definition data. The node record's
signature was checked against the source verbatim.

## Second reading by Q48

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
