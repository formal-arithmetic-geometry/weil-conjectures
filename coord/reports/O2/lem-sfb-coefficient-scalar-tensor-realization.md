## Worker report

Item: lem-sfb-coefficient-scalar-tensor-realization. Stage 2, O2, 2026-10-22.
Module: Sheaf.Paper.CoefficientScalarTensorRealization.
Main declaration: AlgebraicGeometry.ProEtale.CondensedRing.coefficientScalarTensorRealization.

The theorem states the two scalar section realizations and the tensor equation for the
canonical pullback path comparison. Its only proof is `sorry`; its docstring gives all
five steps of the DAG proof. The helper definitions have real data. The scalar realization
predicate is a packaging of this node's clauses, not another module-category encoding or
an independent mathematical notion. Its witnesses are existentially quantified in a
proposition; no definition chooses an object from an unproved existence assertion.

Hypothesis and clause correspondence:

- A prime ell is `(ℓ : ℕ) [Fact ℓ.Prime]`. The field is `(k : Type u) [Field k]`,
  with `[Fact (ringChar k).Prime]` and `[Fact (ringChar k ≠ ℓ)]`, encoding the positive
  prime characteristic p different from ell.
- `X Y : Over (Spec (.of k))` and `f : X ⟶ Y` give the schemes and k-morphism.
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` on each structure morphism
  say separated finite type over k. There is no properness hypothesis on f.
- `R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u+1}`, their `MonObj` and
  `IsCommMonObj` structures, and `a : R ⟶ S` with `IsMonHom a` are the actual
  commutative condensed rings and their coefficient map.
- Exactness on every scheme is the existing shared typeclass
  `[∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]`.
  Extension is already a left adjoint, hence preserves finite colimits. This is
  exactness, not a new flatness or finiteness assumption on the inputs.
- `internalScalarExtension a Z`, `(Mod.comap (coefficientMap a Z)).mapDerivedCategory`,
  `moduleObjectDerivedPullback R f.left` and the recorded derived adjunctions are
  T, U, P, G. All use ordinary unbounded `DerivedCategory`, never its bounded or
  constructible subcategory.
- The sites are exactly `Scheme.ProEt.topology Z`: objects in universe u+1 and
  morphisms in u, with coefficient values and derived Hom types in u+1. The two
  families of `HasDerivedCategory.{u+1} (ModuleRingedComparison.modules _ Z)` are
  the size instances used by the recorded section-derived realization. No equality
  of the site's object and morphism universes is imposed.
- The fixed ordinary and derived equivalences are
  `ModuleRingedComparison.equivalence` and `.derivedEquivalence`. The map
  `coefficientSectionScalarMap` is precisely the recorded `sectionScalarMap`
  applied to `coefficientMap a Z`, not a new ring map.
- `CoefficientScalarSectionRealization a Z` quantifies a normalized `ScalarDerivedPair`
  for that map. Its extension objects and maps are the existing sheafified
  `changeOfRings`, and its derived functor has the existing universal property.
  Ordinary comparisons `o,r` preserve every balanced generator and have identity
  restriction components. The ordinary Hom-bijection equality identifies units and
  counits, not just objects or abstract adjunction existence.
- Derived comparisons `p,q` compare the actual T and U to that same normalized pair.
  The equality defining q localizes r. The representative equation for p localizes
  o on flat-term K-flat complexes. The derived Hom-bijection equality uses
  `Mod.derivedExtendMapDerivedCategoryAdjunction`; it identifies both derived units
  and counits with those of the section pair. These are the identity-underlying-topos
  coefficient morphisms phi_Z in section coordinates.
- The ordinary tensor structure `m` is normalized on ALL generalized balanced
  tensors: its delta sends `s tensor (x tensor y)` to `(s tensor x) tensor (1 tensor y)`.
  `coefficientSectionScalarPure` is the actual sheafification generator, with only
  the pair's specified extension-object equality used for transport.
- The natural isomorphism `t` is independently pinned by its representative equation:
  `qTensor`, `scalarPairComplexComparison`, and `coefficientSectionScalarTotal`
  compare the derived map to the signed direct-sum total of that ordinary delta.
  The hypotheses use the recorded `IsKFlatIndependentCoefficients` and `IsFlatOnSite`.
  This is the canonical 07A4 map for phi_Z, with the full local pure-tensor normalization.
  The last equality of the realization predicate identifies this t with the specified
  `internalScalarTensorComparison`, using the recorded `tensorComparison` of the
  fixed equivalence. Thus no arbitrary tensor map is substituted for t_phi.
- `coefficientScalarPathIso` is built with `Functor.leftDerivedFunctorCompNatIso`
  from the inverse of the ordinary `pullIso`. The latter is the normalized ordinary
  path comparison of the coefficient square, whose restriction paths commute by
  `comapLowerStarIso`. The derived construction localizes that ordinary comparison
  and its composition identifications. It is independent of `derivedPullIso` and
  of the derived direct-image comparison. Under the recorded operation and
  adjunction identifications it is precisely the canonical ringed path comparison
  theta, in direction P_S T_Y to T_X P_R. This uses the existing comparison
  construction and retains the unequal site universes.
- The final equality follows the node in composition order (Lean writes compositions
  left to right): `P_S(mu_Y)`, then the actual geometric
  `leftDerivedUpperStarTensor S f.left`, displayed pointwise by the real-data helper
  `coefficientGeometricTensorComparison`, then theta on the two factors, equals
  theta on `A tensor B`, then `T_X(d_R)`, then `mu_X`. The tensor of the two theta
  components is written as the two curried tensor maps. The source is
  `P_S T_Y(A tensor_R B)` and the target `T_X P_R A tensor_S T_X P_R B`.

Dependency interfaces read and used:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  the scheme-over-field setting of `compactificationOverField`; only its setting is
  relevant, so no compactification is introduced in this theorem.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`:
  `coefficientMap`, `pullIso`, `comapLowerStarIso`, and the two coefficient square
  naturality equations. Their docstrings specify the actual adjunction comparisons.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  the recorded unbounded derived convention; public import retained.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `moduleObjectDerivedPullback`, `moduleObjectDerivedPushforward`, and the imported
  `derivedUpperStarLowerStarAdjunction`.
- Mathlib `AlgebraicGeometry.Scheme.ProEt` in
  `Mathlib.AlgebraicGeometry.Sites.Proetale`; the size node is a metatheoretic
  convention, with no Lean definiendum to import.
- `Sheaf.Paper.ModuleRingedToposDerivedComparison`:
  `module_ringed_topos_derived_comparison`, `derived_homEquiv`, `delta_comparison`,
  and the fixed equivalence/tensor and representative constructions it publicly imports.
- `Sheaf.CategoryTheory.InternalSectionScalarAdjunction`:
  `internal_section_scalar_adjunction`, `sectionScalarMap`, `internalScalarGenerator`;
  its actual ordinary and derived normalization clauses are retained in this realization.
- `Sheaf.Paper.RingedComparisonTensorAdjunction`:
  `ringedComparisonTensorAdjunction` and its canonical path normalization; public
  import retained for the specified ringed comparison convention.
- `Sheaf.Paper.ModuleObjectProjectionMap`:
  the publicly imported `leftDerivedUpperStarTensor`, the actual d used to define
  `moduleObjectProjectionMap`, rather than an arbitrary strong monoidal structure.
- `Sheaf.Paper.InternalScalarTensorComparison`:
  `internalScalarMonoidal`, `internalScalarExtension`, `internalScalarTensorComparison`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`.
  `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`. Both are publicly available through
  the recorded comparison modules.

Plain imports retain the stated proof dependencies: the scalar derived adjunction,
internal/section tensor comparison, representative-normalized ringed tensor presentation,
ringed tensor pullback, and independent-coefficient tensor descent. The proof dependency
lem-pd-sheaf-scalar-extension-constraint-coherence currently has neither a Lean record nor
an upstream declaration; there is no module to import for it. Its elementary balanced
formula is retained explicitly in this statement, not used as an unrecorded assumption.

Edge cases checked before writing: a is the identity; f is the identity; either input
is zero; S is the zero ring; X or Y is empty when a morphism exists; unbounded inputs;
arbitrary nonconstant local scalar sections. All formulas remain typed in these cases.
The pure-tensor normalization uses sheafification generators, so does not require enough
points. No boundedness, constructibility, properness or nonzero-ring assumption occurs.

Searches for existing declarations:

- msearch leanfinder: "Canonical tensorators for derived scalar extension and geometric
  pullback commute with the composition comparison of ringed topoi" returned eight
  hits, including ordinary `SheafOfModules.pullbackComp`, the presheaf counterpart,
  and scheme pseudofunctor coherence. These do not identify the scalar derived
  tensorator with the ringed section tensorator on unbounded internal modules.
- msearch loogle: "SheafOfModules.pullback, SheafOfModules.pullbackComp" returned
  five ordinary pullback composition/identity/associativity and conjugacy results.
  I opened pullbackComp and conjugateEquiv_pullbackComp_inv: they supply the ordinary
  comparison convention but do not state this node.
- msearch grep: "pullback.*[Tt]ensor|[Tt]ensor.*pullback|extendScalars.*[Mm]onoidal"
  returned twelve hits including the ordinary ModuleCat scalar monoidality,
  PullbackCarrier, and unrelated monoidal category results. None is this statement.
- msearch leansearch: "Derived extension restriction of scalars adjunction for ringed
  topoi with canonical monoidal tensor comparison" returned eight ordinary ModuleCat
  adjunction results, not the internal/section realization.
- Local rg searched `lean/WeilConjectures` and `lean/Sheaf` for the item id and declaration
  name, and for leftDerivedFunctorCompNatIso and scalar/tensor realization/comparison.
  No existing exact statement was found. The generic
  `Functor.map_leftDerivedTensorComparison_comp_eq_of_iso` supplies a reusable tensor
  square theorem, but does not assert the scalar/section realization or identify the
  specified coefficient comparison. Its existing path construction is reused.

No statement correction, new DAG node, dependency rebinding, or disputed statement.
The previous worker's stage-1 live-wins objection does not apply: no split is changed;
this delivery adds only the stage-2 Lean binding to the reviewed live node.

## Validation

The complete final module passed scompile.py against the published live library in both
sandbox and library modes (33.8 s and 32.3 s), with no errors or warnings. The helper
constructions and scalar realization predicate were also checked incrementally. The only
postponed proof is the main theorem, with the five-step natural-language proof in its
docstring. The node copy differs from the live node only in lean; its recorded signature
is copied verbatim from the final module. All Lean lines are at most 100 characters.

The prescribed deliver2.py dry run checks this packet's server preflight and per-file
compilation before the same delivery wrapper pushes it.

## Second reading by O2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
