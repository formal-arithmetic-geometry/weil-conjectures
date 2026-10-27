## Worker report

This stage-2 delivery states `SheafOfModules.normalized_ringIso_derived_transport` in
`Sheaf.Algebra.Homology.NormalizedRingIsoDerivedTransport`. Its only postponed proof is
that named theorem, with `sorry` and all six accepted proof steps in its docstring.
The structure and six Prop-valued definitions only package the stated comparison data
and equations; they contain no chosen or postponed construction. No existing node,
accepted proof split, or source statement is corrected.

The inherited BLOCKED ending concerned stage-1 unchanged-item preflight. The current
node has a Q22-reviewed split, no Lean record, and no repair note. The maintenance
handoff in brief-stage2 §0 explicitly says to continue stage 2 in this situation.

Hypothesis and clause correspondence:

- An arbitrary relatively small site is `{C : Type u} [Category.{v} C]
  [EssentiallySmall.{r} C] (J : GrothendieckTopology C)`. Object, morphism and coefficient
  universes remain independent. `HasSheafify`, `WEqualsLocallyBijective`, and
  `HasSheafCompose` expose the standard module-sheaf category and its tensor; these
  are the usual sheafification properties on the small site, not geometric hypotheses.
- Ring sheaves are `R S : Sheaf J CommRingCat.{r}`, and alpha is `a : R ≅ S`.
  All rings are quantified together because the node asks for composition of two
  and three isomorphisms. `∀ R, HasDerivedCategory.{w} (scalarModules J R)` selects
  the ordinary derived categories at a common localization size; the standard
  localization construction supplies this family without an extra mathematical
  assumption. `w` is independent of the site universes.
- `T_alpha` is exactly `scalarRestriction a.inv`: the existing abbreviation expands to
  `SheafOfModules.restrictScalars` on the forgotten ring-sheaf map. Its module action
  is therefore alpha inverse applied to the scalar, and its morphisms are unchanged.
- `ordinary a : RingIsoTensorTransport a.symm` supplies its actual additive exact
  equivalence (`equivalence`, `functor_eq`, `inverse_eq`, `additive`, `exact`). Its inverse
  is restriction along alpha. It also supplies the two ordinary tensor maps, their
  pure-section normalization (`pure_hom`, `pure_inv`), unit map alpha (`unit_hom`),
  termwise total-tensor isomorphism and summand formula, flatness (`flat_iff`) and
  K-flatness (`kflat_iff`). Both tensor directions are isomorphisms; take the inverse
  of its displayed oplax comparison for the direction in this item's display.
- The derived functor is the existing `(scalarRestriction a.inv).mapDerivedCategory`.
  `equivalence` asserts `IsEquivalence` for precisely this functor. Its canonical
  `CommShift ℤ` and `IsTriangulated` instances are in ExactFunctor. No alternative
  triangulation or arbitrary derived functor is introduced.
- The specified `Q_R D(T) ≅ Ch(T) Q_S` is the existing
  `(scalarRestriction a.inv).mapDerivedCategoryFactors`. It is a natural isomorphism
  on the actual complex category, so its naturality identifies localized chain maps.
  Inverting the same equation at a quasi-isomorphism identifies the roof denominator;
  all roof maps are composites of these localized maps and inverses.
- `identityChain` and `compositionChain` are complex-functor natural isomorphisms.
  `NormalizedRingIsoChainSpec` requires their underlying local maps to be the identity
  for every degree and every section. `identity` and `composition` are their derived
  comparisons. `NormalizedRingIsoLocalizationSpec` gives the exact conjugation by
  the canonical localization factors, including the first factor mapped through the
  second derived transport. This is descent of those specified chain maps.
- `NormalizedRingIsoCocycleSpec` states both identity equations and the full
  three-isomorphism equation on arbitrary derived objects. `eqToIso` accounts for
  `Iso.refl_trans`, `Iso.trans_refl`, and `Iso.trans_assoc`; no strict identification
  of separately composed ring isomorphisms is assumed.
- The existential `m,b` give monoidal and symmetric structures on the same derived
  categories. `tensor_eq` identifies the entire bifunctor (including morphisms) with
  the published `siteDerivedTensorIndependentCoefficients`. `localization` is lax
  braided. `NormalizedRingIsoLocalizationTensorSpec` makes its unit and its tensor
  maps on all K-flat pairs invertible, so these are actual K-flat tensor models and
  the coefficient ring in degree zero is the unit. Lax braided localization identifies
  the usual associator, unitors and signed complex symmetry on those models.
- `braided a` is a strong braided structure on the actual derived restriction functor.
  It therefore identifies associators, symmetry and unitors. In
  `NormalizedRingIsoNormalizationSpec`, the canonical localization factor is a
  monoidal natural transformation for the ordinary transport's actual monoidal
  structure, its standard termwise extension, and those localization structures.
  Its tensor equation fixes the derived map by the same pure-tensor formula on
  K-flat models; its unit equation fixes it by the ordinary unit alpha.
- `NormalizedRingIsoMonoidalSpec` says the derived identity and composition
  isomorphisms are monoidal natural transformations. Mathlib's `IsMonoidal` includes
  both the tensor and unit equations. This is exactly the compatibility with the
  preceding composition comparisons requested in the final clause.
- Every complex is `CochainComplex ... ℤ`, and the theorem uses the full
  `DerivedCategory`. There are no boundedness, constructibility, flat-coefficient-map,
  or invertibility assumptions on modules.

Dependencies used (recorded module and declaration read):

- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `Precoverage.IsSiteForCoverings`; arbitrary
  site encoded here by the associated `GrothendieckTopology`, as in the other generic
  ringed-site modules.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the
  transparent Mathlib `SheafOfModules` category used by `scalarModules`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`, including its additive instance.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`; publicly reached by ExactFunctor.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `cochainModulesMonoidal`, `cochainModulesSymmetric`, `cochainModulesPreadditive` and
  the tensor-colimit instances, used for complex tensor structures.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `IsFlatOnSite`, appearing in
  the reused ordinary transport witness's `flat_iff`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`:
  `site_derived_tensor_descent_independentCoefficients` and
  `siteDerivedTensorIndependentCoefficients`, used in `tensor_eq` and the proof plan.
- `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`:
  `ringedDerived_closed_symmetric_monoidal` and its representative-coherence definitions,
  providing the source proof route for the standard derived constraints. The theorem's
  imported interface fixes coefficients at `max c v u`; this delivery does not impose
  that restriction. The same constraints at independent universes are stated through
  lax braided localization and the existing independent-coefficient total tensor.
- Proof input `Sheaf.Algebra.Homology.RingIsomorphismTensorTransport`:
  `RingIsoTensorTransport`, `ringIso_tensor_transport`, with `c=a.symm`.
- Proof input `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `mapDerivedCategory`, `mapDerivedCategoryFactors`, and its shift/triangulated instances.
- Proof input `Mathlib.CategoryTheory.Localization.Predicate`:
  `lift`, `liftNatIso`, `natTrans_ext`, used in the proof docstring's descent argument.

Sources read: current blueprint `def-pur-section-invariant.md`, Stacks
sites-modules.tex lemma-adjoint-pullback-pushforward-modules (03D7), and derived.tex
lemma-right-derived-exact-functor (015F). The complete six-step Q22-reviewed node proof
was read, including its inverse-direction application and normalization equations.

Edge cases checked before writing: identity isomorphism and its two composition laws;
nontrivial coefficient automorphism (the action uses the inverse, but the unit map uses
alpha); zero ring sheaf; empty site; zero complex; arbitrary negative and positive complex
degrees; three composable isomorphisms; independent site object/morphism sizes. All are
included. The pointwise cocycle has the same source and target on both sides after the
explicit ring-isomorphism reassociation. No STATEMENT-DISPUTED issue remains.

Searches actually made with msearch.py under this item:

- LeanFinder: `Coherent normalized derived restriction of scalars along ring sheaf
  isomorphisms with identity composition cocycle and symmetric monoidal comparisons`:
  eight hits on ordinary sheaf pullback/free objects/pushforward congruence, no exact
  statement. The first interrupted query lost its process handle; the rerun completed.
- Loogle: `SheafOfModules.restrictScalars, Functor.mapDerivedCategoryCompIso`: zero hits;
  unknown `Functor.mapDerivedCategoryCompIso` in Mathlib. The upstream project's
  generic composition API was subsequently read, but does not package this normalized
  sheaf tensor/coherence statement.
- Mathlib grep: `restrictScalars.*(Comp|comp|Equivalence)|mapDerivedCategory.*(Comp|comp|Id|id)`
  in Algebra: 25 hits on module restriction/pseudofunctors and ordinary composition,
  none giving the requested combined statement.
- LeanSearch: `Restriction of scalars along isomorphisms of ring sheaves induces coherent
  symmetric monoidal equivalences of unbounded derived categories`: eight hits on
  ordinary restriction, no derived coherent sheaf statement.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for scalar restriction composition,
  derived composition and ring-isomorphism transport found the reused
  `RingIsomorphismTensorTransport` and the upstream generic mapDerivedCategory APIs.
  Grep for this node id in WeilConjectures found no declaration. Final rg for the new
  names in both libraries and `dag/lean_names_upstream.json` found no existing name.

The first combined record elaborated too slowly. Factoring the identical equations
into six named Prop predicates and explicitly supplying the ordinary `Monoidal`
projection resolved the instance search. The single delivered module compiles through
scompile.py; only the single expected sorry warning is permitted. No global build or
live source mutation was performed. All scratch probes were removed.

## Second reading by Q20

A separate reading pass by this dispatched worker reopened the node and the final
module. No other agent was launched, as the dispatcher brief explicitly forbids that;
this is not claimed to be a second person's independent review. The maintainer's
independent delivery review remains required.

The pass checked each quantified site/ring against the binders, the inverse direction
in ordinary restriction, the actual canonical derived factor, the local identity maps,
its derived conjugation formula, both unit laws and the three-factor cocycle. It checked
that braided functors supply all associator/unit/symmetry laws, that monoidal natural
transformations include unit equations, and that normalization uses the ordinary
transport's same tensor and unit data. The earlier tensor identification merely used a
natural isomorphism of bifunctors; this was tightened to `tensor_eq`, so the published
K-flat bifunctor itself is the tensor. That change adds no mathematical restriction:
transport the presented monoidal structure onto that canonically isomorphic bifunctor.
The earlier large record was factored without deleting an equation. Definitions have
real bodies, only the owning theorem is sorry, and no target, node statement, accepted
proof step or dependency record was modified. The file uses no auto-bound variables,
file-local notations, local instances, or private copies of module/tensor notions.
