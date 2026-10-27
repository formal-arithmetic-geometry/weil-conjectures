## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteTypeFieldPointCharacterization` states
`AlgebraicGeometry.finite_type_field_point_characterization`, with its sole proof
`sorry`. No definition, helper theorem, or new node is needed. The original node
is unchanged except for its `lean` record. There is no statement dispute.

Source read in full: `literature/stacks-project/morphisms.tex`,
`lemma-point-finite-type` (Tag 01TA), lines 2827–2875. The node selects its
conditions (1), (2), (4). The final canonical-point assertion follows from
condition (4) with the identity residue extension, as the node's proof explains.

Hypotheses and clauses, matched individually:

- A scheme V is `(V : Scheme.{u})`.
- A field l is `(l : Type u) [Field l]`; this includes nontriviality and excludes
  the zero ring, exactly as a field should.
- The specified morphism is `(f : Spec (.of l) ⟶ V)`.
- Its image v is the term `f (IsLocalRing.closedPoint l)`: the source has exactly
  one point. There is no independently supplied point or unnecessary equality.
- The residue field k is Mathlib's `V.residueField` at that image. The actual
  induced embedding k → l is `(V.descResidueField
  (Scheme.stalkClosedPointTo f)).hom`. This is the local stalk map induced by f,
  followed by its descent to the residue field. It is precisely the map occurring
  in `Scheme.SpecToEquivOfField` and the recorded affine-point dependency.
- Condition (i) is `LocallyOfFiniteType f ∧ QuasiCompact f`, the recorded
  definition of finite type (there is no separate bundled finite-type class).
- Condition (ii) is `LocallyOfFiniteType f`.
- The first equivalence is the first conjunct. The second conjunct equates (ii)
  with (iii), so together they state equivalence of all three conditions.
- The affine open neighbourhood W is `∃ W : V.Opens, IsAffineOpen W ∧
  f (IsLocalRing.closedPoint l) ∈ W ∧ ...`. The ring A is its section ring,
  implicit in `IsAffineOpen`; an additional chosen affine presentation is not
  mathematical data required by the node.
- Closedness of v in W is `IsClosed (Subtype.val ⁻¹'
  {f (IsLocalRing.closedPoint l)} : Set W)`. Membership in W is separately
  required, so this is its actual singleton in the subspace topology.
- `[l:k] < ∞` is `RingHom.Finite` of the canonical embedding above. By
  `Mathlib.RingTheory.Finiteness.Defs`, `RingHom.Finite` means `Module.Finite`
  using that ring map's `toAlgebra`. Over fields this is finite-dimensionality;
  no arbitrary scalar structure and no separability assumption is introduced.
- The final conjunct is an implication from (ii), one of the equivalent
  conditions, to `LocallyOfFiniteType (V.fromSpecResidueField v) ∧
  QuasiCompact (V.fromSpecResidueField v)`. It is exactly the finite-type
  assertion for the canonical morphism Spec κ(v) → V.
- All universes and variables are explicitly bound. Schemes and their coefficient
  rings use the common ambient universe u required by Mathlib's category of
  schemes; there is no independently quantified test universe or equality of
  site universes.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-field`: Mathlib `Field` in `Mathlib.Algebra.Field.Defs`.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`, `Spec` and
  `Spec.map`; for the source, `IsLocalRing.closedPoint l`.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `Scheme.residueField`, `Scheme.Hom.residueFieldMap`,
  `Scheme.descResidueField`, and `Scheme.fromSpecResidueField`. The descent uses
  `Scheme.stalkClosedPointTo` from `Mathlib.AlgebraicGeometry.Stalk`, whose
  signature and local-hom instance were read.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `LocallyOfFiniteType`; `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`,
  `QuasiCompact`. Both are the recorded notions; their conjunction is finite type.

All stated proof dependencies are imported. In particular:

- `lem-weil-pbc-lft-affine-pairs`: Mathlib `locallyOfFiniteType_iff`, in the
  public finite-type import.
- `lem-weil-pbc-spec-field-point-residue-field`:
  `WeilConjectures.AlgebraicGeometry.SpecFieldPointResidueField`, all four
  `spec_field_point_residue_field*` declarations and their docstrings read.
- `lem-sfb-field-finite-type-over-subring-localization`:
  `Sheaf.RingTheory.FieldFiniteTypeSubringLocalization`,
  `Subring.exists_isField_away_finite_of_finiteType`, signature and docstring read.
- `lem-weil-pbc-affine-open-section-vanishing-prime`: the recorded Mathlib
  `Scheme.evaluation_eq_zero_iff_notMem_basicOpen`,
  `IsAffineOpen.fromSpec_preimage_basicOpen`, `fromSpec_primeIdealOf`,
  `PrimeSpectrum.mem_basicOpen`, `IsAffineOpen.basicOpen`, and
  `IsAffineOpen.isLocalization_basicOpen`, from the residue-field and affine
  imports. The public affine import also supplies the statement's `IsAffineOpen`.
- `lem-weil-pbc-localization-quotient-commute`: recorded quotient-localization
  instance from `Mathlib.RingTheory.Localization.Ideal`, with `IsLocalization.algEquiv`
  and `Algebra.algebraMapSubmonoid_powers` available through its imports.
- `lem-weil-pbc-lft-pointwise-criterion`:
  `Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties`,
  `HasRingHomProperty.iff_exists_appLE` specialized to `LocallyOfFiniteType`.

The module docstring identifies the source; the theorem docstring contains all
five natural-language proof steps, with their node references. No mathematical
proof was implemented in stage 2.

Edge cases checked before writing:

- An empty target admits no map from Spec l; no artificial nonemptiness
  hypothesis is needed. An empty W cannot witness (iii) because it must contain v.
- For V = Spec k and the field inclusion k → l, closedness is automatic and
  finite type is precisely finiteness of l/k. An infinite algebraic extension
  fails the finite-dimensional clause as required. No separability is needed.
- For the generic point of the spectrum of a DVR with fraction field l, v is
  closed in D(π), though not in V. The subspace-closed condition deliberately
  preserves this example; no Jacobson hypothesis is added.
- For a closed point with l = κ(v), the residue extension is the identity,
  of degree one, and the final canonical-point assertion agrees with the
  equivalences. Arbitrary characteristic and imperfect fields are allowed.

Searches for existing statements (2026-10-24 UTC):

- `msearch.py ... leanfinder "A morphism from the spectrum of a field to a scheme
  is finite type iff locally finite type iff the image is closed in an affine
  open and the residue field extension is finite"`: eight hits, including
  `isClosed_singleton_iff_locallyOfFiniteType` and
  `isFinite_iff_locallyOfFiniteType_of_jacobsonSpace`. Both require a Jacobson
  target, so neither is the arbitrary-scheme characterization.
- `msearch.py ... loogle "AlgebraicGeometry.LocallyOfFiniteType,
  AlgebraicGeometry.Scheme.fromSpecResidueField"`: three hits, the Jacobson
  criterion and two algebraically closed base-field identities. No exact match.
- `msearch.py ... leansearch "Finite type field valued point is closed in some
  affine open with finite residue field extension"`: eight hits, the same
  Jacobson criterion and closed-point/quasi-finite residue lemmas. No exact match.
- `msearch.py ... grep "finiteType.*[Rr]esidue|finite.*[Pp]oint|
  [Rr]esidueField.*[Ff]inite" AlgebraicGeometry`: eight Mathlib hits concerning
  Jacobson closed points, fibres, and quasi-finiteness. None states this node.
- `rg -n` with that pattern over both `lean/WeilConjectures` and `lean/Sheaf`
  found many unrelated field-point and residue statements; narrowing to
  `finite_type_field_point_characterization|finiteType_field_point|
  finite_type_point_iff|finite_type.*closed.*affine|01TA` and to finite-type
  field/point declaration names found no exact statement. The narrower search
  also covered `dag/lean_names_upstream.json` and the proposed full name was
  searched in Mathlib, the upstream library, and Sheaf without a collision.
- `rg -n "lem-sfb-finite-type-field-point-characterization"
  lean/WeilConjectures` returned no occurrence.

Validation: `scompile.py Q125 lem-sfb-finite-type-field-point-characterization`
compiled this file as both its sandbox module and its library module without
errors or warnings. The delivery dry run is performed after the final import
visibility check and node/report preparation.

## Second reading by Q125

Worker's final reread against the original node and Tag 01TA: the first conjunct
is (i) iff (ii), the second is (ii) iff (iii), and the last gives finite type of
the exact canonical residue-field point under those conditions. In (iii) the
membership clause prevents the empty-preimage closedness issue, closedness is
relative to W, and `RingHom.Finite` uses f's induced embedding. None of the
Jacobson assumptions in the nearby Mathlib search hits was imported as a
hypothesis. No definition was copied, no clause omitted, and no statement
correction was necessary. The affine-open import was made public because its
notion appears in the statement. This is the worker's own reread; independent
review is supplied by the maintainer as specified by the dispatch brief.
