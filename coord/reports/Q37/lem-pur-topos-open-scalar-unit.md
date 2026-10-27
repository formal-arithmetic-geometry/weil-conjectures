## Worker report

States `SheafOfModules.ToposOpenScalar.exists_toposOpenScalarUnit` in
`Sheaf.CategoryTheory.ToposOpenScalarUnit`, with `sorry` as its whole proof.
All seven helper declarations have real data and belong to this comparison: the
restricted coefficient map, typed aliases of the recorded extension and restriction,
the actual Mathlib sheaf pullback adjunction and its typed normalization, and the
original extension and scalar tensor sections. No dependency is restated or repaired.
The natural-language statement is unchanged.

Hypothesis and clause correspondence:

- The fixed small presentation of T is `{C : Type u} [SmallCategory C]` and
  `{J : GrothendieckTopology C}`. The theorem is expressed on this chosen
  presentation, identifying T with `Sheaf J (Type u)`; this uses precisely the
  small-site presentation in `CategoryTheory.IsGrothendieckTopos`. It assumes
  neither subcanonicity nor a site object representing the open.
- The arbitrary subterminal is `A : Sheaf J (Type u)` with `hA : IsSubterminal A`.
  Mathlib's predicate says there is at most one map into A from any sheaf,
  equivalently that A maps monomorphically to the terminal sheaf.
- V is the sheaf topos on the existing `elementTopology A`, whose equivalence
  with T/A is the recorded ringed-slice theorem. Its objects are the original
  pairs (U,f) for sections f of A. This retains opens not represented on C.
- R, S are `Sheaf J CommRingCat.{u}`, and `a : R ⟶ S` is a unital ring-sheaf
  morphism. Restricted rings are `presentationElementRing R A` and its S version;
  `sliceMap A a` is the actual precomposition of the ring map.
- Module categories are the recorded `ringedSiteModules.{u}`. The four
  `HasDerivedCategory.{w}` instances select their ordinary, unbounded derived
  categories, with no relationship imposed between u and w.
- `extension R A` and `restriction R A` are typed abbreviations of
  `elementModuleExtension` and `elementModulePullback`, and likewise for S.
  The additivity and finite-limit/finite-colimit instance parameters express
  the node's specified exact additive extension and restriction. They are
  properties of these fixed functors, not arbitrary operation functors.
- `adjunction R A` is exactly Mathlib's
  `SheafOfModules.pullbackPushforwardAdjunction` for the identity of the
  restricted ring along `elementProjection A`. `normalizedAdjunction` only
  exposes the definitionally equal commutative-ring endpoints. Thus the unit
  is fixed, not a supplied arbitrary natural transformation. The two `IsIso`
  conjuncts express the stated invertible units and hence full faithfulness
  of the derived extension functors.
- ET and EV are the existing `DerivedChangeOfRingsCochainModel` for a and
  `sliceMap A a`. Their `E` is prescribed by `changeOfRings` and
  `changeOfRingsHom`; `T` is its everywhere-defined triangulated total left
  derived functor; `ε` is its universal counit, invertible at K-flat complexes.
  Thus these parameters present precisely E_T and E_V, with no extra
  coefficient-flatness assumption and no arbitrary derived functor.
- The natural isomorphism `rho` is ordinary tensor/restriction balancing. The
  first generator equality fixes it by m tensor s mapping to the same tensor
  at (U,f). `lambda` is its derived comparison; the third conjunct fixes its
  value on every K-flat P via the actual universal counits and exact-functor
  factorization isomorphisms. This specifies the canonical comparison from
  the recorded tensor-pullback dependency, rather than assuming an arbitrary
  isomorphism with the same endpoints.
- The natural isomorphism `tau` is ordinary scalar/extension balancing. The
  second generator equality is exactly `[m]_f tensor s ↦ [m tensor s|_f]_f`.
  On the element site, the restricted scalar s|_f is definitionally s.
  `tensorSection` uses the actual scalar presheaf's sheafification unit and
  the model's prescribed object equality. `extensionSection` uses the actual
  extension adjunction's unit, which is the original summand inclusion
  followed by sheafification. Mathlib orders this scalar tensor as s tensor m;
  this is the same scalar extension as the node's m tensor s convention.
- `beta` has type `D(I_R) ⋙ ET.T ≅ EV.T ⋙ D(I_S)`: functor composition in
  Lean is in application order, so this is E_T I_R ≅ I_S E_V. Its fourth
  conjunct identifies beta on K-flat representatives with termwise tau.
  All its maps live in the S-module derived category, so they retain S-linearity.
- The next-to-last conjunct is
  `E_V(η_R) ≫ lambda.inv ≫ L_S(beta.hom) = η_S`.
  Since both units and lambda are invertible, this is exactly the node's
  inverse-unit normalization
  `L_S(beta.hom) ≫ η_S⁻¹ = lambda.hom ≫ E_V(η_R⁻¹)`.
  No replacement adjunction or newly chosen unit occurs.
- The final conjunct uses the actual derived adjunction's `homEquiv` on
  `beta.inv`: its value is `E_V(η_R) ≫ lambda.inv`, exactly the equivalent
  adjunct description in the node.
- No flatness, boundedness, enough-points, scheme, finite-ring, or nontrivial-ring
  parameter is present. All complexes are indexed by ℤ. The theorem applies
  uniformly to arbitrary ordinary derived-change-of-rings presentations.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.Sites.GrothendieckTopos`:
  `CategoryTheory.IsGrothendieckTopos` (small-presentation interpretation).
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`; Mathlib's existing `SheafOfModules` and
  its abelian category are retained.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.CategoryTheory.RingedSheafSliceAdjunction` and its public construction:
  `RingedSheafSliceAdjunctionData`, `ringed_sheaf_slice_adjunction`,
  `elementTopology`, `elementProjection`, `elementRing`, `elementModulePullback`,
  `elementModuleExtension`, `elementObj`, `elementDirectSumPresheaf`.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings` publicly retains
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and its existence theorem
  from `DerivedChangeOfRingsCochainModel`; this is the general sheaf interface,
  not the unrelated ordinary ModuleCat specialization in the primary record.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`,
  with its ordinary generator normalization and unique K-flat representative
  characterization. The delivered lambda is specified by that specialization's
  actual tensor/restriction square, not by a bare Nonempty choice.
- Added the two already-landed statement dependencies used explicitly:
  `def-weil-pbc-ringed-presentation-comparison-data`, module
  `Sheaf.CategoryTheory.RingedPresentationData`, declaration
  `CategoryTheory.presentationElementRing`; and
  `def-weil-exact-derived-adjunction`, module
  `Sheaf.SixFunctors.OpenTensorNormalizationData`, declaration
  `SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction`.
  No new notion or dependency module was needed.
- All stated proof dependencies are imported, including
  `exists_binaryCoverSitePresentation`, `exists_ringedSliceTensorGenerators`,
  `PresheafOfModules.sheafification`, the recorded sheaf tensor product,
  `exists_isKFlatResolutionIndependentCoefficients`, `ringedOpen_totalTensor_kFlat`,
  and `ringedOpen_preserves_flat_resolution`. The docstring gives all five
  steps of the node's proof, including the R×S/idempotent presentation step.

Sources read locally: Stacks `sites-cohomology.tex`, lemma-j-shriek-and-tensor
(Tag 0GL1); `sites-modules.tex`, lemma-j-shriek-and-tensor (0E8I), and the recorded
04IE element-site localization construction. Also read the current blueprint
`main-20261015/.../sk-thm-purity-transport/_section.md`. The scalar-linear actual-unit
refinement is attributed as agent-formulated, exactly as the node's source says.

Edge cases checked mathematically: A=0 gives the zero slice module category
and vacuous section-generator quantifiers; A=1 gives the identity localization
up to its actual adjunction identifications; M=0 gives zero arrows. The identity
ring map, zero rings, non-flat maps such as ℤ/4→ℤ/2, and unbounded complexes are
all allowed. No original representability or enough-points assumption enters.
The K-flat squares use the same counits for all representatives and thus do not
replace derived tensor by ordinary tensor for a non-flat coefficient map.

Searches for reuse (2026-10-23):

1. `msearch.py ... leanfinder "Derived extension of scalars commutes with
   extension by zero for an open subtopos with actual adjunction unit"`:
   eight hits, including ModuleCat.homEquiv_extendScalarsComp,
   SheafOfModules.pushforwardPushforwardAdj_unit_app_val_app,
   PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app,
   ModuleCat.ExtendRestrictScalarsAdj.unit and scheme restriction adjunctions.
   None gives the arbitrary-open derived S-linear unit-normalized statement.
2. `msearch.py ... loogle "SheafOfModules, CategoryTheory.Adjunction.unit"`:
   four hits, the presheaf-sheafification unit and three continuous-pushforward
   adjunction declarations. These do not state the requested comparison.
3. `msearch.py ... grep "extensionByZero|extendByZero|jShriek"
   Algebra/Category/ModuleCat`: zero hits.
4. Source `rg` in `lean/Sheaf` and `lean/WeilConjectures` for
   `openScalar|OpenScalar|scalar.*balanc|scalar.*Balanc`, and the exact node id
   in `lean/WeilConjectures`: no existing exact theorem. Inspected
   OpenScalarExchangeMate (generic categorical square, with unit formulas as
   assumptions), RingedOpenScalarAdjunction (scalar restriction, not derived
   extension), OpenScalarSiteCoherence (finite coefficient scheme sites), and
   the generic ringed-slice and tensor-pullback interfaces. They do not duplicate
   this arbitrary subterminal assertion. DAG/source search identified the
   existing presentationElementRing and exactDerivedAdjunction definitions,
   which are reused instead of copied. New declaration names were checked
   against the project and upstream names index.

No STATEMENT-DISPUTED flag, statement correction, new definition node, or
unusable-dependency repair is needed.

## Second reading by Q37

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
