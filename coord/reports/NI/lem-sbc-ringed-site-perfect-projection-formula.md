## Worker report

The module `Sheaf.Paper.RingedSitePerfectProjectionFormula` states
`SheafOfModules.ringedSitePerfectProjectionFormula`, with one named theorem and
`by sorry` as its whole proof. It adds no definitions, no assumptions about exact
module pullback, and no new nodes. The node is unchanged except for `lean`.

Source read: `literature/stacks-project/sites-cohomology.tex`, the Projection formula
section, equation-projection-formula-map and lemma-projection-formula (Tag 0944),
including the proof. The source allows arbitrary ringed-topos morphisms and unbounded E.
Its local finite-free-retract argument matches the node's more explicit proof.

Hypothesis and clause correspondence:

- The two small ringed sites are `Y X : RingedTensorCorner.{u,w}`. Their fields
  `site`, `category`, `topology`, and `ring` give small sites and sheaves of
  commutative rings. This is the already recorded presentation used by the
  statement dependency `lem-weil-pbc-ringed-projection-mate-exact`, rather than a
  new definition of a site, a ringed topos, or a module category. The convention
  node `def-weil-size-convention` is rendered by explicit universes `u w`:
  `u` bounds the small presentations and their coefficients and `w` is the
  chosen derived Hom universe. Both are unrestricted universes. The sites are
  presented in the same chosen bound, as in `RingedToposMorphism`'s small-site
  interface; there is no universe equation supplied as an extra hypothesis.
- The ringed-topos morphism is `e : RingedTensorEdge Y X`, oriented so that
  its inverse image goes from the target Y to the source X. Its `inverse`,
  `direct`, `adjunction`, and `finiteLimits` fields give the geometric
  morphism. Its `inverseRing`, `algebraic`, and `ringMap` give the induced
  inverse-image ring and the structural ring map to X's ring. These are
  precisely the algebraic presentation fields of the existing dependency,
  without requiring a continuous functor between the presenting sites.
  `pullback`, `object_eq`, and `map_eq` specify extension of scalars after
  inverse image, rather than an arbitrary module functor. `ordinaryTensor`
  specifies the ordinary comparison on generators. `moduleAdjunction`
  presents its induced module right adjoint. These fields are construction
  data for the operations named in the node, not flatness assumptions.
- The ordinary unbounded derived categories are `X.mateDerived` and
  `Y.mateDerived`, transparent abbreviations for `DerivedCategory` of
  `ringedSiteModules` (in turn exactly Mathlib's `SheafOfModules`). The
  corner's `derived` field chooses `HasDerivedCategory.{w}`.
- `e.left` with `epsilon` and `isLeftDerived` is the total derived module
  pullback; `e.right` and `e.derivedAdjunction` are its right adjoint.
  These are the derived adjunction presentation of mate-exact, not additional
  exactness or boundedness assumptions.
- `a : RingedTensorModel Y` and `b : RingedTensorModel X` identify `Y.tensor`
  and `X.tensor` with direct-sum total tensor on flat-term K-flat
  representatives. Hence the theorem concerns derived tensor, not arbitrary
  bifunctors. The comparison `e.tensorComparison a b` is the existing unique
  representative-characterized canonical comparison, not a chosen arbitrary
  tensor isomorphism. The models specify the operation already named by the
  node; no resolution or tensor comparison is assumed to satisfy this theorem.
- `E : X.mateDerived` is arbitrary. It has no amplitude, boundedness,
  constructibility, or geometric condition.
- `P : Y.mateDerived` and
  `hP : IsPerfectOnRingedSiteOfUniverses.{u,u,u,w} Y.ring P` give exactly local
  perfectness from the recorded coefficient-package dependency. Unfolding this
  predicate gives a representative K, and for every target site object V a
  covering sieve on which bounded complexes F with degreewise finite-free
  retract packages map quasi-isomorphically to the restrictions of K.
  The existential bounds and degreewise ranks are inside the quantification
  over the members of each cover. No common bound or rank is imposed.
- The conclusion `IsIso (e.projection a b E P)` concerns the specified map
  `Y.tensor.obj (e.right.obj E,P)` to
  `e.right.obj (X.tensor.obj (E,e.left.obj P))`. Its existing definition is
  `e.derivedAdjunction.homEquiv` applied to
  `(e.tensorComparison a b).hom.app (e.right.obj E,P)` followed by
  `X.tensor.map (Prod.mkHom (e.derivedAdjunction.counit.app E) (𝟙 _))`.
  This is verbatim the adjunct characterization in the node and Stacks 0944.
  Isomorphism is asserted for this map, not merely existence of some isomorphism.
- There are no hypotheses on geometric finiteness, cartesianness, or exactness
  of module pullback. The edge requires finite-limit preservation only for
  inverse image of sheaves of sets, as a geometric morphism must.

Recorded dependencies read and used:

- `Sheaf.CategoryTheory.RingedToposMorphism`,
  `CategoryTheory.RingedToposMorphism`: full signature and generalized-element
  structural map/module-action docstring read; publicly imported. The theorem
  uses the already existing algebraic/derived presentation of this same notion
  from mate-exact, not a second independently defined morphism.
- `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules`: exact transparent `SheafOfModules`
  abbreviation, used by the corner's `mateModules`/`mateDerived` interface.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory` and
  `HasDerivedCategory`: full signatures/docstrings read and used through the
  public mate-exact interface.
- `Sheaf.Paper.ProjectionMateExact`, `SheafOfModules.ringedProjectionMateExact`,
  `RingedTensorCorner.mateDerived`, and its public
  `Sheaf.Paper.RingedTensorSquarePresentation` declarations
  `RingedTensorCorner`, `RingedTensorModel`, `RingedTensorEdge`, and
  `RingedTensorEdge.tensorComparison`: the full fields, theorem, and
  representative normalization docstrings were read.
- `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`,
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses` and
  `IsLocallyStrictPerfectComplexOfUniverses`: full definitions read, together
  with `StrictPerfectCoefficientRepresentationOfUniverses` and the underlying
  `StrictPerfectCoefficientPackageOnSite` from
  `Sheaf.Paper.StrictPerfectPackageOnSite`. Their degreewise maps split finite
  powers of the unit, with no chain-map requirement.
- `Sheaf.Paper.RingedExchangeTensorCoherence`,
  `SheafOfModules.RingedTensorEdge.projection`: existing canonical map used
  directly in the theorem statement. This proof dependency is publicly
  imported because it supplies the map actually appearing in the signature.

All other stated proof-dependency modules are imported without `public`, as
required for the future proof plan: degreewise-split homotopy triangles,
triangulated two-out-of-three, `ElementRestrictionHom`, canonical tensor
pullback of universes, exact functor/homology comparison, sheaf local
isomorphism detection, and derived cohomology isomorphism detection.
`lem-sbc-ringed-topos-sheaf-slice-derived-comparison` has no recorded Lean
module in this read clone and is therefore the only omitted proof import.
It supplies no object needed to type this statement, and is retained in the
natural-language proof and DAG proof dependencies for stage 3.

Edge cases checked before drafting:

- P = 0 and rank-zero free terms are allowed: package ranks range over all
  natural numbers, including zero; bounded representatives can be zero.
- All positive and negative integer shifts of the coefficient ring are allowed.
- Different cover members may have arbitrarily different finite intervals and
  ranks. The perfectness predicate has the existential bounds inside the cover.
- E may have cohomology in infinitely many positive and negative degrees.
- The structural map need not be flat or invertible: the point-site example
  Z -> Z/2 is permitted. With P = Z the map is the unit normalization; with
  P = Z/2 its two-term perfect resolution is permitted, and derived, rather
  than exact ordinary, scalar extension is the operation used.
- Empty site presentations, zero rings and zero module categories are not
  excluded by any binder. Local perfectness is appropriately vacuous on the
  empty site; the unique map is invertible in its zero derived category.

Searches for existing declarations (all before writing):

1. `msearch.py ... leanfinder`: “The canonical derived projection formula for a
   morphism of ringed topoi is invertible for a locally perfect coefficient
   complex”. Eight results on K-projective/K-injective localization and
   zeroth derived functors; no perfect-coefficient ringed-site theorem.
2. `msearch.py ... loogle`: `CategoryTheory.Adjunction,
   CategoryTheory.MonoidalCategory`. Twelve results on (op)lax monoidal
   adjunctions; no derived ringed-site perfect projection theorem.
3. `msearch.py ... grep`: `projectionFormula|projection_formula|Perfect.*[Tt]ensor`
   in `CategoryTheory`. Zero Mathlib matches.
4. `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item ID,
   perfect/projection theorem names and projection_formula. No existing
   declaration for this item. Read `Sheaf.Paper.PerfectProjectionFormula`
   through `perfect_projection_formula`: that result specializes to pro-etale
   scheme morphisms with an adic completed coefficient datum, so cannot replace
   this arbitrary-small-ringed-site theorem. Other hits impose properness or
   concern different sheaf categories. Read the existing generic canonical
   projection definition and reused it instead of writing any map again.

No statement correction, disputed statement, missing definition, dependency
module repair, or other node change is needed.

## Second reading by NI

A separate pass by the same worker reopened the node, the source lemma,
`RingedTensorSquarePresentation`, the full perfectness predicate and its package,
and the delivered theorem. This is a self-check; no independent worker was
started, in accordance with the dispatcher instruction. Independent review is
left to the maintainer's delivery review.

The source/target order was checked against the declaration of `projection`:
`e : RingedTensorEdge Y X` is the inverse-image direction for X -> Y; E is on X,
P on Y, and the conclusion returns to Y. The canonical map is exactly the
adjunct of mu followed by counit tensor identity. The existing predicate was
unfolded to check both quasi-isomorphic local representatives and the placement
of the boundedness quantifiers. The statement has no globally chosen strict
perfect representative and no bound on E. The package splitting is degreewise,
not a splitting of complexes. The ring map is not assumed invertible, and no
exactness of module pullback or site functor is assumed. The tensor models and
derived-edge fields present canonical operations; the conclusion does not
assume their projection map is invertible. No mismatch requiring a node
correction was found.

Validation: the prescribed `scompile.py NI
lem-sbc-ringed-site-perfect-projection-formula` compiled the delivered file as
both its sandbox module (17.6 seconds) and its library module (20.5 seconds).
Both completed without errors or warnings. All variables and universes are
bound explicitly, with `autoImplicit false` in the delivered module.
