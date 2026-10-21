## Worker report

The module `Sheaf.CategoryTheory.DerivedCategory.ExactTensorNormalization` states
`CategoryTheory.Functor.exactDerivedTensorComparison_normalization`, with its proof `sorry`.
Its helper `CategoryTheory.Functor.exactDerivedTensorUnitIso` constructs the prescribed
unit comparison by composing existing canonical isomorphisms. No definition has postponed data.
The node's natural-language statement, dependencies, and proof are unchanged.

Hypothesis and clause correspondence:

- C and D: separate `Type uC`, `Type uD`, `Category.{vC}`, `Category.{vD}`, and `Abelian`
  binders. `IsGrothendieckAbelian.{vC}` / `.{vD}` give Grothendieck categories, including
  their small colimits. `MonoidalCategory`, `SymmetricCategory`, `MonoidalClosed`, and
  `MonoidalPreadditive` give exactly the specified closed symmetric additive tensors.
- Functorial flat resolutions: `Abelian.HasFunctorialFlatResolution C` and the D analogue.
  These are the existing functorial flat-cover structures used by the K-flat resolution API.
- Ordinary unbounded derived categories: `DerivedCategory C`, `DerivedCategory D`, with
  independent `HasDerivedCategory.{wC}` / `.{wD}` binders. No object universe, hom universe,
  or derived localization universe is equated with one from the other category.
- The fixed derived tensors: inferred native K-flat monoidal structures from
  `DerivedCategory.hasDerivedMonoidalCategory`, not a supplied arbitrary monoidal structure.
- F additive and exact: `[F.Additive]`, `[PreservesFiniteLimits F]`, and
  `[PreservesFiniteColimits F]`. Left adjoint: `[F.IsLeftAdjoint]`. Specified ordinary
  strong monoidal structure: `[F.Monoidal]`, equivalent to the dependency's `CoreMonoidal`.
  No `F.Braided` or symmetry-compatibility assumption appears.
- Preservation of flat objects: `[F.PreservesFlat]`. Its predicate is the existing two-sided
  exactness of tensoring, as in the node. Preservation of K-flat complexes: `hKFlat` using
  the recorded `CochainComplex.IsKFlatForTotalTensor` definition on both sides.
- The termwise functor is `F.mapHomologicalComplex (.up ℤ)`. The prescribed total comparison
  τ is `(F.mapCochainComplexμIso P Q).inv`. Upstream `mapCochainComplexμIso_inv` identifies
  it with the signed total extension of `OplaxMonoidal.δ F`, the inverse ordinary tensorator.
  The summand specification is fixed upstream, rather than introduced as an arbitrary map.
- E is `F.mapDerivedCategory`; Q_C and Q_D are `DerivedCategory.Q`; κ is
  `F.mapDerivedCategoryFactors`, with its canonical direction E Q_C → Q_D F_Ch.
- The given comparison is the explicit family `t`, and `ht` is its full two-variable
  naturality. This is the same kind of family used by the recorded derived-comparison
  declaration; there is no new copy of its definition. An explicit family permits the
  independent universes of this item, whereas the existing `ComparisonHom` abbreviation
  fixes both coefficient and localization hom universes to one common successor.
- Normalization: `hnorm` quantifies over *every* pair P,Q satisfying the dependency's
  two-sided K-flat predicate, without termwise-flatness or boundedness assumptions.
  Write c_C = `LaxMonoidal.μ Q_C P Q`, and similarly c_D on FP,FQ. These are the native
  localization counits, inverse to the node's m_C,m_D on the K-flat pairs at issue.
  The node's equation, in Lean composition order, is
  `E(m_C) ≫ t ≫ (κ_P ⊗ₘ κ_Q) = κ_(P⊗Q) ≫ Q_D(τ) ≫ m_D`.
  Multiplying on the left by `E(c_C)` and on the right by `c_D` gives exactly `hnorm`:
  `E(c_C) ≫ κ_(P⊗Q) ≫ Q_D(τ) = t ≫ (κ_P ⊗ₘ κ_Q) ≫ c_D`.
  This is an equivalent normalization, not an assumption on non-K-flat pairs.
- Native unit model: `(singleFunctorIsoCompQ A 0).symm.app (𝟙_ A) ≪≫
  singleFunctorObjUnitIso A` is Q_A(1_A[0]) ≅ 1_D(A), for A=C,D. Both constituents are
  existing canonical maps. `F.mapCochainComplexεIso.symm` is the specified ordinary
  inverse unit map in degree zero, with the canonical termwise single-complex comparison.
  `exactDerivedTensorUnitIso` is literally E(u_C⁻¹), then κ_I, then Q_D of that inverse
  unit map, then u_D. Its forward map is precisely e; its inverse is e⁻¹.
- Every t_K,L invertible: the first conjunct is `∀ K L, IsIso (t K L)`.
- Associativity: the second conjunct is the displayed equation with `α_` the native
  derived associator. Lean's `≫` reverses the paper's written function-composition order;
  `◁` supplies `1 ⊗ t`, and `▷` supplies `t ⊗ 1`.
- Left and right unit identities: the next two conjuncts use the native `λ_` and `ρ_`,
  tensoring `(F.exactDerivedTensorUnitIso).hom` on the specified side.
- The final clause is `∃ s : F.mapDerivedCategory.CoreMonoidal` with
  `s.εIso = (F.exactDerivedTensorUnitIso).symm` and `(s.μIso K L).inv = t K L` for every
  K,L. Thus the forward tensorators and unit are exactly t⁻¹ and e⁻¹, not merely some
  unrelated strong monoidal structure. No braiding equation is asserted.

Recorded dependencies and declarations read and used:

- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`,
  `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q`.
- `lem-sfb-derived-monoidal`: `WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`,
  `DerivedCategory.hasDerivedMonoidalCategory`, supplying the fixed native tensor.
- `def-sfb-preserves-kflat-quasi-iso`: `Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso`,
  `CochainComplex.IsKFlatForTotalTensor`. The exact functor already preserves quasi-isomorphisms;
  the item additionally assumes objectwise K-flat preservation, stated explicitly.
- `def-sfb-strong-monoidal-functor`: `Mathlib.CategoryTheory.Monoidal.Functor`,
  `CategoryTheory.Functor.CoreMonoidal` and its equivalent `Monoidal` interface.
- `lem-pur-derived-tensor-comparison`: `Sheaf.CategoryTheory.DerivedTensorComparison`,
  `AlgebraicGeometry.ProEtale.SupportedTensorDerivation.exists_unique_comparison`,
  `ComparisonHom`, `ComparisonCondition`, and `ComparisonFamilyCondition` were read in full.
  The imported theorem provides the provenance of the given normalized family; this theorem
  is conditional on that family's naturality and K-flat normalization and constructs no second one.
- `def-sp-grothendieck-abelian`: Mathlib's `CategoryTheory.IsGrothendieckAbelian` and
  its `hasColimits` instance.
- Proof infrastructure is imported: `Mathlib.CategoryTheory.Adjunction.Limits` for
  `Adjunction.leftAdjoint_preservesColimits`;
  `WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex` for
  `mapCochainComplexMonoidal`, `mapCochainComplexμIso`, `mapCochainComplexεIso`;
  `WeilConjectures.CategoryTheory.DerivedCategory.FlatModel` for
  `CochainComplex.exists_quasiIso_flat_kFlat` and `DerivedCategory.singleFunctorObjUnitIso`;
  `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal` for the recorded
  total-tensor/homotopy constraints. The theorem docstring gives all nine DAG proof steps.

Edge cases checked before writing: zero complexes and zero objects cause no exclusions;
all complexes and objects are unbounded; arbitrary integer shifts are allowed, including
odd degrees, because the termwise tensorator uses the existing signed total tensor.
The unit complex is included in the K-flat normalization and its comparison is fixed, not
chosen by existence. Identity F with identity ordinary tensorators gives the native unit
comparison and the expected localization equations. A strong monoidal structure without
braiding compatibility remains admissible. No nonemptiness or degree restrictions occur.
The source and target coefficient object/hom universes and both localization hom universes
are independent, including small hom universes.

Searches made:

- `msearch.py leanfinder`, query "An exact strong monoidal functor preserving K-flat complexes
  induces a strong monoidal derived functor with normalized tensor and unit comparisons":
  eight hits, including `mapDerivedCategory`, its factorization isomorphisms, Tor and Ext;
  none states normalized derived associativity and both unit equations.
- `msearch.py loogle`, query `"mapDerivedCategory", "Monoidal"`: zero hits.
- `msearch.py grep`, query `mapDerivedCategory.*[Mm]onoidal|[Nn]ormalized.*[Tt]ensor`:
  zero Mathlib hits.
- `msearch.py leansearch`, query "A normalized derived tensor comparison for an exact monoidal
  left adjoint obeys associativity and left and right unit coherence": eight ordinary monoidal
  coherence/adjunction/localization hits, no K-flat derived normalization theorem.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for normalized tensor comparisons,
  exact monoidal functors, and `mapCochainComplexMonoidal`: found the ordinary termwise
  construction reused here, ringed-site-specific coherence statements, and
  `rightExact_tensorComparison_existsUnique` (binary comparison only, no unit/coherence
  conclusion), but no exact match of this item.
- `grep -rn` of the item ID in `lean/WeilConjectures`: no match.
- Native unit searches found `singleFunctorObjUnitIso`; it is reused in the actual composite.
  No new independent definition node or dependency repair is needed.

Source read: `literature/stacks-project/sites-cohomology.tex`,
`lemma-symmetric-monoidal-cat-complexes` (0FPQ) and `lemma-symmetric-monoidal-derived` (0FPT).
Their proofs are omitted in Stacks; the abstract cross-functor theorem and its explicit
cancellation proof are correctly attributed to the DAG's agent extraction.
No statement dispute or source correction was found.

Validation: every compile uses the prescribed server wrapper. The first compile diagnosed
field notation on a `HomologicalComplex` result; this was repaired by spelling out
`CochainComplex.IsKFlatForTotalTensor` on the termwise image. No mathematical statement changed.
The repaired module passed both server checks without errors or warnings (sandbox 48.2 s,
final module 32.2 s). The delivery dry run recompiles the final source with the explicit
statement-dependency and proof-dependency imports and runs server preflight.

## Second reading by NW

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
