## Worker report

The module `Sheaf.Paper.PrescribedResidueCellConeModel` states
`WeilConjectures.sf_prescribed_residue_cell_cone_model`. Its sole postponed theorem is
this theorem, with proof `sorry`; its docstring contains all six DAG proof steps.
Every auxiliary abbreviation or instance is an actual specialization of the existing
constructions. No definition chooses data from an uncharacterized existence theorem.
The repair adds one definition record for existing explicit constructions; there is no
statement correction or disputed statement.

Hypotheses and objects, clause by clause:

- `T : Scheme.{u}` and `T.ProEt` with `Scheme.ProEt.topology T` give the scheme and its
  small pro-etale site. `_hEval` quantifies over every epimorphism of set sheaves and
  asserts surjectivity of its component at `Scheme.ProEt.mk (𝟙 T)`.
- `k : Type v` with `[Field k]` is independent of the scheme universe.
  `sfResidueCoefficients T k` is precisely `constantSheaf` of `CommRingCat.of (ULift k)`
  in universe `max (u+1) v`. The lift changes only size. `sfSplitRings` forgets
  commutativity. `sfResidueModules` is the recorded `ringedSiteModules` category.
  `sfResidueDerived` uses `HasDerivedCategory.standard`; no extra derived-existence
  assumption, compactness, affine hypothesis, integral coefficient, quotient tower,
  or completeness hypothesis is added.
- `a b : ℤ`, `hab : a ≤ b`, `rank : ℤ → ℕ` give the ordered interval and finite
  nonnegative ranks; values outside the interval are unused. `_hN` states vanishing
  outside the closed interval using the recorded `DerivedCategory.homologyFunctor`.
  `theta q hq` is the prescribed free-sheaf isomorphism for each degree in the interval.
- `sfResidueFree` is `SheafOfModules.free` on `ULift (Fin n)`. `sfResidueCell` is its
  single complex in degree b, hence the conventional free sheaf shifted by -b.
  `sfResidueSplit` reuses `sfSplitComplex` verbatim; its terms are the prescribed
  free sheaves on the interval and zero elsewhere, with zero differentials.
  Thus the choices `(a,b)` and `(a,b-1)` are V and W respectively.
  `sfResidueInclusion` reuses the actual top `sfSplitCell`, not an arbitrary arrow.
- `uTop` has domain the localization of the specified A. `_huTop` uses the canonical
  `sfFreeCohomologyMap` comparison to say it induces theta_b. `C`, `g`, `delta` and
  `_htriangle` quantify over any distinguished triangle with this first arrow.

Conclusions, in the order of the conjunctions:

1. The existential `phi` is an isomorphism `Q(V) ≅ N`; its equations use the canonical
   cell/cohomology comparisons to impose every theta_q, not just abstract cohomology
   ranks.
2. The next conjunct quantifies over EVERY such `phi`, with all its prescribed
   cohomology equations. It gives `uTop = Q(i) ≫ phi.hom` and an actual triangle
   isomorphism to `Q.mapTriangle.obj (mappingCone.triangle i)` with
   `e.hom.hom₁ = 𝟙 _` and `e.hom.hom₂ = phi.inv`. No uniqueness of its third map is asserted.
3. The literal complex cone is isomorphic to the binary direct sum (coproduct in this
   additive category) of W and `sfResidueIdentityPair`, the literal cone of `𝟙 A`.
4. The next conjunct identifies both nonzero terms of D with the top free sheaf and
   states that its differential becomes the identity. The next two conjuncts say all
   remaining terms are zero and every differential except `(b-1,b)` is zero.
5. A `Homotopy (𝟙 D) 0` expresses exactly `dh+hd=id`. The additional equations force
   every component with source degree different from b to vanish. The Homotopy shape
   law forces all other targets to vanish. The equation through `mappingCone.inr`
   and `mappingCone.fst` says its sole surviving component is the identity on A^b.
   This uses the canonical cone summand identifications and avoids arbitrary choices
   of a contracting homotopy.
6. Two separate `Nonempty` derived isomorphisms give `C ≅ Q(Cone(i)) ≅ Q(W)`.
7. `∀ U : T.ProEt` uses the actual slice site. `sfResidueComplexRestriction` is
   `overFunctor.mapHomologicalComplex` with the existing zero-preservation witness;
   its applied lower split complex is required to satisfy the recorded
   `IsKFlatIndependentCoefficients`. The ring is `(sfResidueCoefficients T k).over U`.
8. For EVERY module sheaf F over that ring in degree zero, the existing canonical
   `siteDerivedTensorIndependentCoefficients` of `C|U` and `singleFunctor _ 0 F` is
   isomorphic in the derived category to the localization of the finite coproduct
   over `Set.Icc a (b-1)` of single complexes with `Fin (rank q)` copies of F.
   `C|U` is precisely the recorded `ringedSiteDerivedRestrictionOfUniverses`.
9. Under `a < b`, the recorded `HasRingedSiteTorAmplitudeOfUniverses` on each slice
   gives `[a,b-1]`. The following two conjuncts give the free cohomology in `a ≤ q < b`
   and zero cohomology everywhere else. Finally `a=b` implies both W and C are zero.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory.standard`, `DerivedCategory.Q` and its triangle functor.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`, `homologyFunctorFactors`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.overFunctor`, and `CategoryTheory.Sheaf.over` from Sites.Over.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`. Size witnesses reuse
  `SheafOfModules.hasSheafify_coefficientUniverse` and
  `wEqualsLocallyBijective_coefficientUniverse` from its imported coefficient interface.
- `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations` publicly retains
  `CategoryTheory.HasRingedSiteTorAmplitudeOfUniverses` from
  `Sheaf.AlgebraicGeometry.RingedProEtaleTorAmplitudeOfUniverses`.
- `Sheaf.Paper.ProjectiveCohomologySplitModel`: `sfSplitRings`, `sfSplitComplex`,
  `sfSplitCell`, `sfFreeCohomologyMap`, `sf_projective_cohomology_split_model`,
  `sf_shifted_free_generator_bijective_natural`. The new definition node
  `def-sf-prescribed-split-complex` owns the four concrete definitions and is cited in
  stmt_deps. The theorem node remains in proof_deps only.
- `Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses`:
  `CategoryTheory.ringedSiteDerivedRestrictionOfUniverses`. Its landed node is added
  to stmt_deps for the actual derived restriction object.
- The intrinsic tensor is the one already used by the landed
  `def-weil-proetale-tor-amplitude` record, with construction owner
  `lem-weil-pbc-site-derived-tensor-descent`; no tensor record is rebound. The cone and triangle
  constructions are Mathlib's `mappingCone`, `mappingCone.triangle`, `Homotopy`,
  `Triangle.mk` and `distTriang`. Proof imports retain the existing weakly-etale
  localization, exact restriction, constant restriction compatibility, tensor-complex
  and tensor-sheaf modules. TR3 and the three-component isomorphism lemma are in
  Mathlib's Pretriangulated imports. Constant restriction is the recorded
  `Functor.pushforwardContinuousSheafificationCompatibility` in Sites.CoverLifting.

Edge cases checked before writing: a=b makes `Icc a (b-1)` empty; a=b-1 leaves
exactly the degree-a term. rank b=0 makes the top cell and its identity pair zero;
all ranks zero give zero split complexes. Negative b uses integer degrees and the
same b-1,b identity pair without truncation. The empty scheme is not excluded: its
constant free module sheaves are zero, and all the statements specialize to zero
objects. No nonempty index type or positive rank is assumed. U is arbitrary, with
no weak-contractibility assumption on U.

Searches for existing statements (all on 2026-10-23):

- msearch leanfinder: `A bounded complex of sheaves with prescribed finite free
  cohomology splits and the cone of the top cell is the lower split complex`.
  Eight hits include projective/injective single-term splittings and generic
  degreewise-split mapping cones; none supplies this full prescribed theorem.
- msearch loogle: `"mappingCone", "Homotopy"`. Twelve hits give generic
  descHomotopy/liftHomotopy, rotated cone homotopy equivalence and triangle maps;
  no combined prescribed splitting/restricted tensor theorem.
- msearch grep: `mappingCone.*(biprod|split|contract)|Homotopy.*mappingCone`
  under Algebra/Homology. Twenty-two hits include `homotopyToZeroOfId` and generic
  mapping cone factorizations. Their definitions are reused, not restated as helpers.
- msearch leansearch: `The cone of a prescribed top cohomology free cell of a split
  bounded sheaf complex is the lower split complex, with the identity pair contractible`.
  Eight generic cone and degreewise-splitting hits; no exact statement.
- rg in lean/WeilConjectures and lean/Sheaf for prescribed residue, residue cone,
  sfSplitComplex, sfSplitCell and the item's id: no existing item declaration.
  Found and read ProjectiveCohomologySplitModel, reused its definitions; found
  CompleteTopResidueCellCone, which requires completed integral coefficients and
  is not this unrestricted field-coefficient assertion.

Source read: literature/stacks-project/proetale.tex, lemma-local-structure-constructible-complex
(Tag 09C3), lines 5825-5940, especially the final induction paragraph and its
`(details omitted)` assertion. The module's expanded proof follows the accepted DAG
steps and the existing cone convention. No source hypothesis from the integral
parent is added to this field-only auxiliary lemma.

Validation: server `scompile.py` checks both the sandbox and final library module.
The first complete signature passed with no error or warning. Initial universe errors
were resolved using explicit coefficient-sized witnesses and fully specified derived
restriction universes, preserving independent scheme and field sizes. The free sheaf
passes its actual coefficient-sized sheafification witness explicitly. No universe
equality or mathematical hypothesis was added.

## New nodes

`def-sf-prescribed-split-complex` records the explicit definitions `sfSplitRings`,
`sfSplitComplex`, `sfSplitCell` and `sfFreeCohomologyMap` already in
`Sheaf.Paper.ProjectiveCohomologySplitModel`, lines 46-91, with `existing: true`.
It introduces the underlying ring sheaf, the zero-differential finite free model,
its actual single-cell inclusions, and the canonical free-to-cohomology map.
The source is Stacks 09C3, lemma-local-structure-constructible-complex, final
induction paragraph (shifted top free cell and generator lifting). No evaluation
hypothesis is needed to construct these data. The ambient scheme and arbitrary
commutative coefficient sheaf are the section parameters U and C of the existing
module; `a b : ℤ` and `r : ℤ → ℕ` specify the model, `q` and `hq` specify a cell,
and `q`, rank, N and f specify the canonical cohomology map. The latter uses the
existing singleObjHomologySelfIso and homologyFunctorFactors, then H^q(f).
No new Lean module, duplicate definition or theorem is introduced.

Searches on the repair date: msearch LeanSearch for "A zero differential bounded
cochain complex of finite free module sheaves with its summand inclusions and the
canonical cohomology map from a single free complex" returned eight generic
zero-differential/cochain hits. msearch LeanFinder for "The zero differential split
complex of finite free sheaves on a ringed site, with its cell inclusion and canonical
derived cohomology map" returned eight generic sheaf/cochain hits. Neither gives
these combined definitions. msearch grep for
`sfSplitRings|sfSplitComplex|sfSplitCell|sfFreeCohomologyMap|mkHomFromSingle|singleObjHomologySelfIso`
in Mathlib Algebra/Homology returned 19 hits for the generic single-complex tools.
The exact queries and results are recorded in the node and the wrapper search log.
Direct rg in both lean/WeilConjectures and lean/Sheaf found the four definitions
only in the existing ProjectiveCohomologySplitModel module. A DAG search for the
four names found only the theorem node's auxiliary-declaration list, no definition
node. Blueprint searches for "split complex" found none; "zero differential" found
only def-kun-bc-property, and "prescribed" found thirteen unrelated unit statements.
The new node's blueprint ancestor and via are inherited from the item, with the item
prepended to via. Empty and reversed intervals, zero ranks, negative degrees and
empty schemes are all covered by the actual if-then-else terms and zero differentials.

## Repair of returned delivery

F1 (H2), immutable head 09f94468ef69: removed the added theorem node
`lem-sf-projective-cohomology-split-model` from stmt_deps and replaced it with
`def-sf-prescribed-split-complex`, the existing-definition record above. The theorem
remains in the original proof_deps. The statement uses only the four plain
constructions; it never obtains the model via a theorem's choose.

F2 (H13): removed `dag/nodes/sec-picard-framework/def-weil-derived-tensor.json`
from the packet. The live NE fixed-ring ProEtale.derivedTensor record is untouched.
The item's lean.note explicitly identifies the intrinsic tensor as the one used by
HasRingedSiteTorAmplitudeOfUniverses in the landed
`def-weil-proetale-tor-amplitude` record. I read that predicate's full definition in
RingedProEtaleTorAmplitudeOfUniverses: its degree-zero module test applies exactly
siteDerivedTensorIndependentCoefficients. The construction's source owner is
`lem-weil-pbc-site-derived-tensor-descent`, whose recorded declaration list includes
this functor and whose representative comparison characterizes the K-flat tensor.
The theorem's existing tensor clause therefore already uses the same intrinsic
construction and needs no mathematical change or record rebinding.

Required self-check: the saved packet's first dry run passed as 22d8f28fbaf.
Compared with the current shared node, the repaired item changes only lean and
stmt_deps; proof, proof_deps, statement and all remaining fields are identical.
The Lean module is unchanged from the saved returned packet. The new node is an
existing:true record with no file; no dependency-node repair is delivered.

Repair validation: scompile.py compiled the unchanged item as both the sandbox
and final library module with exit code 0 and no diagnostics. The self-check also
verified the stored item signature against the complete source declaration and removed
a trailing newline from the new definition signature; neither changes any Lean declaration.

## Second reading by Q120

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
