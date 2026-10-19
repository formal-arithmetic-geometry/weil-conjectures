## Worker report

The module `Sheaf.RingTheory.HenselianSmoothAlgebraLifting` states
`Algebra.Smooth.exists_lift_of_henselianRing`, with its whole proof `sorry`.
It introduces no definitions. The natural statement and dependency lists are unchanged.
The source is Stacks Project, More on Algebra, Tag 0H74,
`lemma-lift-smooth-henselian`, read in `literature/stacks-project/more-algebra.tex`.
The source asserts precisely this lifting statement for arbitrary henselian pairs.
There is no repair note for this item.

Hypothesis and conclusion correspondence:

- A commutative ring R: `(R : Type u) [CommRing R]`.
- A smooth R-algebra S: `(S : Type v) [CommRing S] [Algebra R S]
  [Algebra.Smooth R S]`. This is the exact smoothness declaration recorded by
  `def-weil-pbc-smooth-ring-map`, including finite presentation; formal smoothness
  alone is not substituted for it.
- A commutative R-algebra A: `(A : Type w) [CommRing A] [Algebra R A]`.
- An ideal I in A: `(I : Ideal A)`.
- The henselian pair (A,I): `[HenselianRing A I]`, the pair notion explicitly
  recorded in `def-weil-pbc-henselian-terminology`. That record identifies the
  equivalent root-lifting and finite-algebra idempotent-lifting definitions.
  Neither henselian locality nor strict henselianity is required here.
- Every R-algebra homomorphism τ to A/I: `(τ : S →ₐ[R] A ⧸ I)`.
  The quotient carries its canonical induced R-algebra structure.
- Existence of an R-algebra lift: `∃ τ' : S →ₐ[R] A`.
- The composite is τ: `(Ideal.Quotient.mkₐ R I).comp τ' = τ`.
  `Ideal.Quotient.mkₐ` is the canonical quotient map, so this is exactly the
  specified compatibility, as equality of R-algebra homomorphisms.

All universes and variables are explicit. The independent universes `u v w`
allow arbitrary sizes for all three rings; there is no quantification over test
objects in an undersized universe.

Dependency declarations read and used:

- `def-weil-pbc-smooth-ring-map`: `Algebra.Smooth`, from
  `Mathlib.RingTheory.Smooth.Basic`, publicly imported. Its docstring identifies
  smoothness with formal smoothness plus finite presentation, and the recorded
  match explains its equivalence to the cotangent formulation in the node.
- `def-weil-pbc-henselian-terminology`: `HenselianRing`, publicly exported by
  `WeilConjectures.Mathlib.RingTheory.Henselian`, which is publicly imported.
  Read the Mathlib class fields and the upstream module's explanation of the
  blueprint pair terminology, as well as its strictly henselian declaration.
- Proof dependency `lem-weil-pbc-smooth-ring-map-base-change-composition`:
  `Algebra.Smooth.baseChange` (and its sibling `Algebra.Smooth.comp`), already in
  the publicly imported smooth module.
- Proof dependency `lem-weil-pbc-smooth-ring-map-iff-smooth-affine`:
  `AlgebraicGeometry.HasRingHomProperty.Spec_iff`, with the instance for
  `AlgebraicGeometry.Smooth` and `RingHom.Smooth`. Its owning comparison module
  is imported through `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, a proof import.
- Proof dependency `lem-weil-pbc-smooth-section-etale-lift`:
  `AlgebraicGeometry.exists_etale_lift_of_smooth` in
  `Sheaf.Paper.SmoothSectionEtaleLift`, imported for the proof plan.
- Proof dependency `lem-weil-pbc-henselization-stage-map`:
  `RingTheory.existsUnique_henselization_stage_map` in
  `Sheaf.RingTheory.HenselizationStageMap`, imported for the proof plan.

The theorem's docstring gives all five DAG proof steps: smooth tensor-product
base change and its quotient map; affine smoothness comparison; lifting over an
etale neighbourhood with quotient isomorphism; its henselian retraction; and
descent of the retraction to the quotient, giving the composite equality.
It records passage to a common universe when using the proof dependencies whose
interfaces put their rings in a single universe.

Edge cases checked mathematically before writing:

- For I = bottom, the quotient is canonically A and the assertion is immediate.
- For I = top, the Jacobson-radical condition of a henselian pair forces A to
  be the zero ring, so the unique homomorphisms provide the lift.
- Zero A is permitted, with no `Nontrivial` or domain hypothesis. If S is the
  zero ring and τ exists, A/I is zero, hence the preceding top-ideal case applies.
- Zero R is permitted; its unital algebra structures force S and A to be zero.
- No locality, Noetherian condition, nilpotence, or adic completeness was added.
  In particular the statement covers nonlocal henselian pairs.

Searches for an existing statement (run with `msearch.py`, group Q158 and this
item, and source searches):

- LeanFinder: "For a smooth R algebra S and a henselian pair A I every R algebra
  homomorphism S to A modulo I lifts to A". Eight hits, including
  `Algebra.FormallySmooth.exists_lift`, `Algebra.FormallySmooth.lift`,
  `Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete`, and
  `Algebra.FormallySmooth.exists_adicCompletionEvalOneₐ_comp_eq`.
  Read the source signatures: the first requires a nilpotent ideal; the
  complete-ring version assumes `IsAdicComplete`; the completion version lands
  in the completion. None is the arbitrary-henselian-pair statement.
- LeanSearch: "For a henselian pair A I and smooth R algebra S every R algebra
  map S to A modulo I lifts to A". Eight hits, again formal-smoothness lifting,
  adic-completion lifting, and square-zero standard-etale lifting. No match.
- Loogle: `HenselianRing, Algebra.Smooth`. Zero hits.
- Mathlib grep through msearch: `[Hh]ensel.*[Ss]mooth|[Ss]mooth.*[Hh]ensel`.
  Zero hits.
- `rg` in `WeilConjectures/` and `lean/Sheaf/` for
  `hensel.*smooth|smooth.*hensel`: only unrelated smooth-curve local-ring text
  in `OpenCurveBoundaryHigherDirectImageVanishing.lean`. No lifting theorem.
- `grep -rn` for the exact item id in `WeilConjectures/`: no hits.
- `rg` for `exists_lift_of_henselianRing`, `exists_lift_of_smooth`,
  `exists_smooth_lift`, `exists_henselian_lift`, and the proposed module name
  in Mathlib, upstream sources, `lean/Sheaf/`, and `dag/lean_names_upstream.json`:
  no collision or existing match.

Validation: the prescribed `scompile.py` compiled both the isolated sandbox
statement and its actual module cleanly, with no errors or warnings. No global
build or direct write to either read-only checkout was performed. There are no
new nodes, dependency repairs, statement corrections, or disputed statements.

## Second reading by Q158

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
