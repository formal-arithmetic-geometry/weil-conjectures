## Worker report

The module `Sheaf.RingTheory.PrescribedPBasisCoefficientSection` states
`IsLocalRing.existsUnique_coefficientSection_prescribed_pBasis`, with its proof `sorry`.
No definitions, helper theorems, new nodes, dependency repairs, or statement corrections
are introduced. Only the item's `lean` field changes. The former declaration recorded
in `lean_removed` is absent from the current source; it is restored as a new statement,
not attached to a nonexistent declaration. No released repair note exists for this item.

Source read: ILO, Travaux de Gabber, Exposé IV 2.1.4, printed page 50 (PDF page 56),
with the surrounding 2.1.1–2.1.6. It prescribes arbitrary lifts of a residue p-basis and
asserts a unique coefficient subfield containing them and mapping onto the residue
field. A residue section is equivalent: the quotient map on such a subfield is an
isomorphism, whose inverse is the section; conversely the section's image is that
subfield. The node already states the general complete Noetherian local-ring version,
including nilpotents, rather than the reduced setting of the surrounding application.
The six-step proof in the node works in this generality and is reproduced in the
theorem docstring.

Hypothesis and clause correspondence:

- Prime positive characteristic: `(p : ℕ) [Fact p.Prime]` and `[CharP A p]`.
  Primality includes `p > 0`; no extra positivity assumption is required.
- Nonzero commutative local ring: `(A : Type u) [CommRing A] [IsLocalRing A]`.
  Mathlib's `IsLocalRing` extends `Nontrivial`, so the zero ring is excluded exactly
  as in the node. Its canonical maximal ideal is `maximalIdeal A`.
- Noetherian: `[IsNoetherianRing A]`, the recorded declaration of
  `def-weil-pbc-noetherian-ring`.
- Complete for the maximal-ideal topology: `[IsAdicComplete (maximalIdeal A) A]`,
  the recorded declaration of `def-weil-pbc-adically-complete-ring`. This includes
  separatedness, and `AdicCompletion.of_bijective_iff` identifies it with the node's
  bijective canonical completion map.
- Actual residue field: `ResidueField A`, defined as `A ⧸ maximalIdeal A`, with
  canonical quotient homomorphism `residue A`. No arbitrary residue-field model is used.
- Arbitrary p-basis family: `(E : Type v) (b : E → ResidueField A)`. The universes
  `u v` are explicitly bound and independent. There is no finiteness or nonemptiness
  restriction on `E`.
- Finitely supported bounded monomials forming a basis: the index of `B` is
  `{n : E →₀ ℕ // ∀ i : E, n i < p}`. Its coefficient field is
  `Subfield.closure (Set.range (fun x : ResidueField A ↦ x ^ p))`. In a characteristic-p
  field the p-th powers already form a subfield: Frobenius preserves sums, products,
  0 and 1, and `(x^p)⁻¹ = (x⁻¹)^p`. Thus this closure is exactly the node's `k^p`.
  This is the inline `Module.Basis` convention, with `Subfield.closure` avoiding a
  file-local prime-field algebra instance. It is mathematically the same coefficient
  subfield as the `IntermediateField.adjoin (ZMod p)` convention used by p-basis
  existence modules; no p-basis predicate or private definition is introduced.
- The identification with the specified monomials is
  `(hB : ∀ n, B n = n.val.prod (fun i e ↦ b i ^ e))`. A bare arbitrary basis would
  not suffice; this hypothesis explicitly gives the monomial values.
- Arbitrary prescribed lifts: `(β : E → A)` with
  `(hβ : ∀ i : E, residue A (β i) = b i)`. No independence or compatibility is
  required of these lifts beyond their residues.
- Existence and uniqueness: `∃! s : ResidueField A →+* A`.
  A unital ring map from a field to a nonzero ring is injective, so this is the
  node's field homomorphism into A, without wrongly requiring A to be a field.
- Residue composite equals the identity:
  `(residue A).comp s = RingHom.id (ResidueField A)`.
- Every specified value: `∀ i : E, s (b i) = β i`. Both properties are inside
  the single unique-existence predicate, so uniqueness is among precisely the
  sections satisfying the prescribed values.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, its docstring and
  `isNoetherianRing_iff_ideal_fg` (lines 195–208): all ideals finitely generated.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `IsAdicComplete` (lines 36–56) and
  `AdicCompletion.of_bijective_iff` (line 647): complete and separated, equivalent
  to the canonical-map definition. This is a public statement import.
- `WeilConjectures.Mathlib.Algebra.CharP.Lemmas`: `iterateFrobeniusOfPrime` and
  `iterateFrobeniusOfPrime_apply`, the recorded proof dependency
  `def-weil-ring-frobenius`, read in full and imported without `public`.
- `Mathlib.RingTheory.LocalRing.ResidueField.Basic` and its `Defs` import:
  `IsLocalRing.ResidueField` and `IsLocalRing.residue`; the exact quotient and map.
- `Module.Basis`, `Finsupp.prod`, and `Subfield.closure` are existing Mathlib notions;
  the p-basis is stated inline as in the node, with no second definition.

Edge cases checked mathematically against the signature and node proof:

1. `E` empty: its only exponent is zero, so the hypothesis means `k = k^p`, and
   the theorem gives the unique coefficient section for a perfect residue field.
2. Infinite `E`: only finitely supported exponent families occur, and each expansion
   given by a module basis is finite. No finite-p-basis assumption is introduced.
3. `A` a field: the maximal ideal is zero; the residue isomorphism forces the section,
   and every prescribed lift is already forced by its residue.
4. Imperfect field example `F_p(u)[[t]]`: a lift of the p-basis element may be `u+t`;
   the signature permits this, with no fixed coefficient subfield assumption.
5. Nilpotent example `F_p(u)[ε]/(ε²)`: `u+ε` is also permitted. No reduced or domain
   assumption is imposed, and the Frobenius argument kills lift errors in the
   appropriate ideal powers.
6. The zero ring is excluded by the explicitly requested nonzero local-ring
   condition. Composite characteristic and characteristic zero are excluded by
   the node's prime-characteristic assumption, not by an accidental type choice.

Searches actually run with `batch2/msearch.py Q94` for this item (the wrapper's
search log is in the sandbox):

- LeanFinder: `complete Noetherian local ring characteristic p unique residue field
  section prescribed lifts p-basis`: eight hits, primarily `PreTilt.untiltFun`,
  `PreTilt`, `PreTilt.exists_smodEq_untiltAux`, `HenselianLocalRing`; no matching
  prescribed-p-basis residue section.
- Loogle: `IsAdicComplete, RingHom, IsLocalRing.ResidueField`: twelve hits, all
  power-series Weierstrass preparation/division constructions; no matching theorem.
- LeanSearch: `coefficient field section with prescribed p basis lifts complete local
  ring`: eight hits, including `IsLocalRing.ResidueField.lift`,
  `IsAdicComplete.liftRingHom`, and `PowerSeries.residueFieldOfPowerSeries`.
  These descend maps into fields, lift compatible quotient maps, or identify a
  power-series residue field; none supplies this section or its prescribed values.
- Mathlib grep: `coefficientSection|pBasis|p_basis|coefficient.field`, restricted to
  `RingTheory`: five reported hits concerning `basisOfBasisRight`; no matching theorem.
- Direct `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `prescribed_pBasis`, `coefficientSection`,
  `p-basis`, `pBasis`, `p_basis`, and `CoefficientResidueSection`. The named former
  declaration and the item id have no hit in the current Lean sources. Existing
  p-basis results include `WeilConjectures.FieldTheory.ExistsPBasis` (read its full
  statement and docstring); those give a p-basis, not this section.
  `WeilConjectures.RingTheory.CoefficientResidueSection` was read: its
  `IsLocalRing.exists_residue_section` assumes characteristic zero in the residue
  field and gives existence without prescribed p-basis values or uniqueness, so is
  not a match. Other hits concern unrelated coefficient sections of sheaves or
  power-series/Artinian presentations.

No statement dispute or node fault was found. The existing accepted node statement,
proof and dependency lists are preserved verbatim. The `lean_removed` history and
old review metadata are preserved as maintainer-owned fields.

Validation: prescribed `scompile.py` on the delivered file compiled both sandbox and
library module forms cleanly (1.1 s and 1.0 s respectively), with no diagnostics.
`set_option autoImplicit false` checks all binders; universes are explicitly declared.
Only the named theorem has `sorry`; there are no data definitions or proved lemmas.

## Second reading by Q94

Author's separate final reading (not an independent-agent review; the dispatcher brief
forbids starting other agents). Reopened the node and Lean file and checked the above
correspondence in order. `IsLocalRing` supplies nonzeroness, the residue type is the
actual quotient, and completeness uses exactly the maximal ideal. The basis's index
bounds every exponent by p while retaining arbitrary finite support; `hB` identifies
its vectors with the given monomials, rather than assuming an unrelated basis. The
closure of p-th powers equals the image subfield, so no coefficient-field hypothesis
has been changed. `hβ` imposes precisely the residue-lift condition. The unique
existence predicate includes both the quotient-map identity and every prescribed
value; uniqueness is not accidentally restricted to algebra maps for a preselected
coefficient field. No dimension, reducedness, finite p-rank, or finite index-set
hypothesis appears. Each of the six proof steps is present in the theorem docstring,
and the recorded Frobenius proof dependency is a plain import. No mismatch was found,
and no correction was made in this reading. The maintainer's review remains the
independent review of this delivery.
