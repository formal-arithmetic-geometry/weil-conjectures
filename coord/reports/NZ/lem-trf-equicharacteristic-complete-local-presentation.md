## Worker report

The module `Sheaf.RingTheory.EquicharacteristicCompleteLocalPresentation` states
`IsLocalRing.exists_equicharacteristic_complete_local_presentation` with proof `sorry`.
It introduces no definitions and leaves the accepted node statement and split unchanged.
The source was read in algebra.tex: Definition 0326 and the following field-containing
case, Theorem 032A (1) and its final proof paragraph, and Remark 032C, first sentence.

Hypothesis and conclusion correspondence:

- The nonzero commutative local ring `(C,n)` is `(C : Type v) [CommRing C]
  [IsLocalRing C]`; Mathlib's `IsLocalRing` extends `Nontrivial`, so nonzeroness
  is included. Here `n = IsLocalRing.maximalIdeal C`.
- Noetherianity is `[IsNoetherianRing C]`, and completeness for the maximal ideal
  is `[IsAdicComplete (maximalIdeal C) C]`. The latter includes Hausdorffness.
- The field and its unital ring map are `(k : Type u) [Field k] (_ι : k →+* C)`.
  Universes u and v are independent. No algebra structure is imposed on C.
- The arbitrary integer r >= 0 is `(r : ℕ)`, and the tuple is `(y : Fin r → C)`.
  Membership in n is `hy : ∀ i : Fin r, y i ∈ maximalIdeal C`; generation is
  `hgen : Ideal.span (Set.range y) = maximalIdeal C`.
- F is exactly `ResidueField C`, definitionally `C ⧸ maximalIdeal C`, and rho is
  exactly `residue C`, the quotient ring homomorphism. Neither is an arbitrary field/map.
- The two existential unital ring maps are
  `α : ResidueField C →+* C` and
  `ψ : MvPowerSeries (Fin r) (ResidueField C) →+* C`.
- The section identity is `(residue C).comp α = RingHom.id (ResidueField C)`.
- Restriction to constants is `∀ a : ResidueField C, ψ (MvPowerSeries.C a) = α a`.
- Prescribed variables are `∀ i : Fin r, ψ (MvPowerSeries.X i) = y i`.
- Surjectivity is `Function.Surjective ψ`.
- Kernel containment is `RingHom.ker ψ ≤ Ideal.span (Set.range MvPowerSeries.X)`,
  with the variables' domain/codomain fully annotated in the statement.
- The moreover clause uses the same Q throughout: `MvPowerSeries (Fin r) (ResidueField C)`.
  It asserts `IsNoetherianRing Q`, `IsAdicComplete (maximalIdeal Q) Q`,
  `IsRegularLocalRing Q` (which includes localness), and
  `maximalIdeal Q = Ideal.span (Set.range MvPowerSeries.X)`.
  Mathlib's local-ring instance on Q comes from `MvPowerSeries.Inverse`.
- No equation involves the original field map and α; the final sentence of the node
  therefore holds without adding an unwanted k-linearity condition. No continuity,
  dimension, minimality of the tuple, or finite-generation conclusion on the kernel
  has been added.

Dependency declarations read and reused:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`; its docstring identifies this with all ideals being finitely generated.
- `def-weil-pbc-adically-complete-ring`: `Mathlib.RingTheory.AdicCompletion.Basic`,
  `IsAdicComplete`, extending `IsHausdorff` and `IsPrecomplete`.
- `def-weil-pbc-multivariate-power-series`: `Mathlib.RingTheory.MvPowerSeries.Basic`,
  `MvPowerSeries`, `C`, and `X`; finite variables are indexed by `Fin r`.
- `def-weil-regular-scheme`: its recorded module
  `Sheaf.AlgebraicGeometry.IsRegularScheme` is imported. The node's ring clause is
  supplied by its retained Mathlib match `Mathlib.RingTheory.RegularLocalRing.Defs`,
  `IsRegularLocalRing`. The scheme definition is not specialized to an unrelated object.
- Residue field and reduction: `Mathlib.RingTheory.LocalRing.ResidueField.Defs`,
  `IsLocalRing.ResidueField` and `IsLocalRing.residue`.
- Stated proof dependencies are imported privately:
  `WeilConjectures.RingTheory.ExistsCoefficientSubring`,
  `IsLocalRing.exists_coefficient_subring`, and
  `WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete`,
  `MvPowerSeries.power_series_field_cohen_regular_complete`. Their full signatures
  and proof docstrings were read. `lem-trf-coefficient-field-generator-presentation`
  has no recorded Lean module yet, so there is no import for that proof dependency;
  it is referenced by id in the complete proof docstring. The present statement
  does not need any new notion from it.

Edge cases checked before writing:

- r = 0: the empty tuple generates precisely the zero ideal. Thus n = 0, C is a
  field, Q is canonically F, α is the residue inverse and ψ has zero kernel.
  No positive-variable hypothesis excludes this case.
- Redundant/zero generators are permitted. For example, for a field C and a
  one-element tuple y = 0, ψ is evaluation at zero and its kernel is the variable ideal.
- A nonregular C such as F[ε]/(ε²) is allowed. With y = ε, the presentation has
  kernel (z²), contained in (z); regularity is asserted only of Q.
- Positive characteristic and imperfect residue fields are permitted; no
  characteristic-zero/perfectness or separability hypothesis is imposed.
- Mixed characteristic rings do not admit the unital field map in the hypotheses.
  The zero ring is excluded by `IsLocalRing` itself.

Searches performed (the wrapper logs are in searches.jsonl):

- LeanFinder query: "A complete equicharacteristic Noetherian local ring admits a
  residue field section and a surjective formal power series presentation with
  prescribed maximal ideal generators". Eight hits, including `HenselianLocalRing`
  and Weierstrass preparation/division theorems; no presentation theorem of this form.
- Loogle query: `MvPowerSeries, Function.Surjective`. Only `MvPowerSeries.C_surjective`,
  which assumes an empty variable type and does not present an arbitrary complete ring.
- Mathlib grep query: `equicharacteristic|coefficient.field|exists.*presentation`
  in RingTheory. Returned finite module/algebra presentations and smooth presentations,
  none giving the required coefficient section and power-series surjection.
- LeanSearch query: "A complete Noetherian local ring containing a field has a residue
  field section and is a quotient of formal power series with prescribed variable images".
  Eight hits, including `IsLocalRing.residue`, `ResidueField`, residue-surjectivity,
  Weierstrass division and `PowerSeries.residueFieldOfPowerSeries`; no exact match.
- `rg` searches in both `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  equicharacteristic/coefficient-field terminology and complete local presentations,
  and the upstream-name table. Read the candidate modules
  `PowerSeriesFullCoordinatesField`, `FirstOrderPowerSeriesComparison`,
  `RegularCompleteCoefficientCoordinates`, `FormalLocalPresentation` and
  `CompletionLocalCompleteIntersection`. The coordinates results assume regularity;
  the private first-order section theorem supplies only the section; the formal
  presentation structure is over a completion with k-linearity and at least two variables;
  the complete-intersection criterion is a different theorem. None states this node.

Validation: scompile.py compiled the module cleanly against the live server sources
(4.7 seconds). The wrapper's local attempt reported a full-device OSError; its
normal server fallback succeeded. The module contains exactly one postponed named
 theorem with its source and the node's three-step natural-language proof. There
are no statement corrections, new nodes, dependency repairs, or disputed statements.

## Second reading by NZ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
