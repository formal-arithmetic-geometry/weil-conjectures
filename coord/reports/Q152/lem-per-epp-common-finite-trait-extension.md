## Worker report

The module `Sheaf.RingTheory.CommonFiniteTraitExtension` states
`IsDiscreteValuationRing.exists_common_finite_trait_extension`, with a single
`sorry` proof. It constructs no new notion and makes no node correction.

Clause-by-clause reading:

- The complete DVR W₀ is `(W₀ : Type u) [CommRing W₀] [IsDomain W₀]
  [IsDiscreteValuationRing W₀] [IsAdicComplete (maximalIdeal W₀) W₀]`.
- Its fraction field is `K₀`, with `Field`, `Algebra W₀ K₀`, and
  `IsFractionRing W₀ K₀`. Its residue field k₀ is the canonical
  `IsLocalRing.ResidueField W₀`, so an extra name or arbitrary field
  identification is unnecessary.
- The finite set is `(I : Type w) [Finite I]`. There is no nonemptiness
  assumption. The upper traits and their fraction fields are the families
  `Wᵢ : I → Type v` and `Kᵢ : I → Type v₁`.
- Every upper ring has `CommRing`, `IsDomain`, `IsDiscreteValuationRing` and
  maximal-ideal `IsAdicComplete` instances.
- Its specified W₀-map is `algebraMap W₀ (Wᵢ i)`, from its `Algebra` instance.
  `IsLocalHom` states locality; `hinj` states injectivity.
- The fraction field of Wᵢ i has `Field`, `Algebra (Wᵢ i) (Kᵢ i)` and
  `IsFractionRing (Wᵢ i) (Kᵢ i)`. Its extension over K₀ is `Algebra K₀ (Kᵢ i)`
  and `Module.Finite K₀ (Kᵢ i)`. The equality `hK` says the two maps from W₀
  into Kᵢ i agree, so this really is the fraction-field extension induced by
  the given trait map. This is the meaning of the node's fraction-field
  extension, rather than an additional mathematical restriction.
- The existential W has `CommRing`, `IsDomain`, `IsDiscreteValuationRing`,
  maximal-ideal `IsAdicComplete`, and `Algebra W₀ W`. The existential
  `IsLocalHom (algebraMap W₀ W)` and the first conjunction's
  `Function.Injective (algebraMap W₀ W)` give the injective local base map.
- `Module.Finite W₀ W` is exactly the asserted module finiteness.
- `∀ i : I, ∃ f : Wᵢ i →ₐ[W₀] W, Function.Injective f ∧ IsLocalHom f.toRingHom`
  gives every local injective W₀-map. `AlgHom` enforces its compatibility with
  the specified base maps.
- `(ResidueField.map (algebraMap W₀ W)).Finite` is finiteness for the induced
  residue-field map. `RingHom.Finite` is definitionally `Module.Finite` with
  the algebra structure of that very map; no arbitrary scalar action is used.
- `PerfectField (ResidueField W₀) → PerfectField (ResidueField W)` is exactly
  the conditional perfectness assertion. Mathlib's perfect-field predicate
  agrees with the node's characteristic-zero-or-surjective-Frobenius meaning:
  `PerfectField.ofCharZero`, `PerfectRing.ofSurjective`,
  `PerfectRing.toPerfectField`, and `PerfectField.toPerfectRing` are the two
  directions, as documented in `lem-per-algebraic-extension-perfect`.

Dependency declarations read and used:

- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing`, in
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`; the definition includes
  local PID and nonzero maximal ideal and requires an integral domain.
- `def-weil-pbc-adically-complete-ring`: `IsAdicComplete`, in
  `Mathlib.RingTheory.AdicCompletion.Basic`, specialized to the maximal ideal
  and the ring as its own module; separatedness is included.
- `def-weil-finitely-generated-module`: `Module.Finite`, in
  `Mathlib.RingTheory.Finiteness.Defs`, and its map-specific form
  `RingHom.Finite` in that same file.
- `def-pc-field-extension`: `Algebra`, in `Mathlib.Algebra.Algebra.Defs`,
  specialized to fields for K₀ → Kᵢ i; base trait maps also use this structure.
- `def-weil-residue-field`: the recorded
  `AlgebraicGeometry.Scheme.residueField` in
  `Mathlib.AlgebraicGeometry.ResidueField` is literally
  `IsLocalRing.ResidueField` of the stalk. For the explicitly local rings in
  this item we use that same underlying quotient construction directly from
  `Mathlib.RingTheory.LocalRing.ResidueField.Basic`, and its canonical `map`.
  No scheme is introduced and no copy of the residue-field definition is made.
- `def-weil-field`: `Field`, in `Mathlib.Algebra.Field.Defs`.
- Fraction-field representations use Mathlib's `IsFractionRing`, in
  `Mathlib.RingTheory.Localization.FractionRing`.

The module imports the stated proof inputs
`Sheaf.FieldTheory.CommonExtensionFields` (`Field.exists_common_extension`),
`Mathlib.FieldTheory.IntermediateField.Adjoin.Basic`
(`IntermediateField.adjoin_rank_le_of_isAlgebraic_right`),
`Mathlib.RingTheory.IntegralClosure.Algebra.Basic` (`integralClosure`),
and `Mathlib.FieldTheory.Perfect` (`Algebra.IsAlgebraic.perfectField`).
The uniformizer factorization input is in the already public DVR import.
`lem-per-complete-dvr-finite-normalization` is an unstated proof dependency;
its module is not imported. It is not needed to state this theorem. The
natural-language docstring retains all five proof steps and names that input.

Source checked: ILO, Travaux de Gabber, Exposé IV §4.2.3, printed p. 58,
sentence beginning “De tels idéaux p étant en nombre fini”. It chooses one
finite W₀′/W₀ for finitely many Epp extensions, using stability under further
finite base change. The node spells out the common-extension algebra needed
there. No statement defect or STATEMENT-DISPUTED issue was found.

Edge cases checked before writing: for I empty, take W = W₀, with the identity
base map and degree-one residue extension; all upper-family assertions are
vacuous. Repeated or identity extensions cause no additional condition. Both
mixed characteristic (e.g. Z_p and finitely many ramified finite extensions)
and equal characteristic (including a purely inseparable extension
k[[t]] → k[[t^(1/p)]]) are included: no characteristic or separability
assumption appears. Perfectness is conditional and imposes no restriction on
imperfect residue fields. Local means the inverse image of the maximal ideal
is the source maximal ideal, equivalent to Mathlib's unit-reflection
`IsLocalHom` for local rings. W can live in `Type u`, because a finite extension
of Frac(W₀) and its integral closure have cardinality at most that of the
infinite DVR W₀; this imposes no bound on degrees. The index, base fraction
field, upper rings and upper fraction fields all have explicit independent
universes. All variables are explicitly bound and `autoImplicit` is false.

Searches made through msearch.py (recorded in searches.jsonl):

- LeanFinder: “finitely many finite extensions of a complete discrete valuation
  ring admit a common finite complete discrete valuation ring extension”:
  8 hits on valued-field compactness and adic completions, none stating a
  common finite extension for a finite family.
- Loogle: `IsDiscreteValuationRing, Module.Finite`: 0 hits.
- Mathlib grep: `common.*extension|finite.*extension` restricted to
  `RingTheory/DiscreteValuationRing`: 0 hits.
- LeanSearch: “common finite complete discrete valuation ring extension
  dominating finitely many finite trait extensions”: 8 hits on DVR criteria
  and valuation-extension predicates, none giving this theorem.
- Direct rg over upstream WeilConjectures and project lean/Sheaf for
  `common.*(trait|dvr)|finite.*trait.*extension|epp-common-finite|completeDvr|complete_dvr`:
  only the existing consumer EppFiniteFamilyTraits and an unrelated alteration
  reference, no declaration of this item. A direct item-id search upstream
  found nothing. The intended declaration name was also searched in both
  libraries and dag/lean_names_upstream.json, with no hit.

Validation: scompile.py compiled this module both as sandbox and as the named
library module in 2.3 s and 2.1 s respectively, with no warnings or errors.

## Second reading by Q152

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
