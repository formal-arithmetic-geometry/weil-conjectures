## Worker report

The module `Sheaf.RingTheory.PerfectCohenResidueMap` states
`IsLocalRing.existsUnique_cohenRing_lift_of_perfect`, with its whole proof `sorry`.
It introduces no definitions, auxiliary theorems, new nodes, or dependency repairs.
Only the item's `lean` field changes.

Hypothesis and conclusion correspondence:

- The prime `p` and Cohen ring `A` are `(p : ℕ) (A : Type u) [CommRing A]`
  and `(hA : IsCohenRing p A)`. The existing predicate includes `Nat.Prime p`,
  the domain and DVR structures, maximal ideal `Ideal.span {(p : A)}`, and completeness.
  No separate primality, locality, domain, or completeness hypotheses on A are added.
- The field `K = A/pA` is literally `A ⧸ Ideal.span {(p : A)}`. Perfectness is
  `[PerfectRing (A ⧸ Ideal.span {(p : A)}) p]`. The sole field of Mathlib's
  `PerfectRing` is `bijective_frobenius : Function.Bijective (fun x ↦ x ^ p)`,
  exactly the node's definition of perfectness. No characteristic hypothesis is added.
- The Noetherian local ring R is `(R : Type v) [CommRing R] [IsNoetherianRing R]`
  and `[IsLocalRing R]`. Its maximal-ideal completeness is
  `[IsAdicComplete (maximalIdeal R) R]`, including separatedness.
- The given field homomorphism is
  `(j : (A ⧸ Ideal.span {(p : A)}) →+* ResidueField R)`.
  A field homomorphism in Mathlib is a unital ring homomorphism. The source quotient
  is a field by the Cohen hypothesis; it needs no chosen field instance to form this type.
  The target is Mathlib's actual residue field. Injectivity follows and is not assumed.
- Existence and uniqueness of a local lift is `∃! f : A →+* R, ...`.
  Its locality clause is `(maximalIdeal R).comap f = Ideal.span {(p : A)}`,
  exactly the explicit inverse-image equality in the node.
- The prescribed residue equality is
  `(residue R).comp f = j.comp (Ideal.Quotient.mk (Ideal.span {(p : A)}))`.
  Here `residue R` is defined as the quotient map onto `R ⧸ maximalIdeal R`.
  Both quotient maps are canonical. Uniqueness is equality of ring homomorphisms
  satisfying both clauses, as in the node, with no arbitrary choice of a lift.

Dependencies read and used:

- `WeilConjectures.RingTheory.CohenRing`, `IsCohenRing`: complete definition and docstring read.
- `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`: all ideals finitely generated.
- `Mathlib.RingTheory.AdicCompletion.Basic`, `IsAdicComplete`: Hausdorff and precomplete.
- `Mathlib.RingTheory.LocalRing.ResidueField.Defs`, `IsLocalRing.ResidueField`,
  `IsLocalRing.residue`: quotient by the maximal ideal and its quotient map.
- `Mathlib.FieldTheory.Perfect`, `PerfectRing`: bijectivity of the p-th power map.
- Proof-only import `WeilConjectures.RingTheory.CohenRingModPowFormallySmooth`:
  `IsDiscreteValuationRing.cohenRing_mod_pow_formallySmooth`, whose full signature
  supplies the explicit square-zero lifting assertion in independent target universes.

The module docstring cites ILO IV 4.1.8(i), 4.1.9, printed pp. 57–58.
I read these pages in the local PDF (text extracted into the sandbox scratchpad).
Apply 4.1.8(i) to `I = maximalIdeal R` and `u = j ∘ q_A`; this u is local
because j is injective and `ker q_A = pA`. Perfectness gives vanishing differentials
by 4.1.9, hence uniqueness. The theorem docstring includes all five node proof steps:
the initial residue map, square-zero induction, inverse-limit assembly and locality,
binomial induction for uniqueness, and separatedness.

Edge cases checked before writing:

- `R` a field: its maximal ideal is zero, the lift is `j ∘ q_A`, with kernel pA;
  completeness and locality give exactly this case.
- `R = A` and j the identity: the unique lift is the identity; independent universes
  do not exclude this case.
- `R = A/p^eA`, e ≥ 1: p may vanish or be a zero divisor; no nonvanishing or
  torsion-freeness assumption on R was introduced.
- A proper field extension j is allowed: j is not required to be an isomorphism
  or surjective. Ramified complete local targets are also allowed.
- p = 2, n = 1: the binomial proof has its quadratic term in m² as required.
- The zero ring is excluded precisely by the existing `IsLocalRing` convention,
  matching the node's local ring with a maximal ideal and residue field.
- `u` and `v` are independent, and all variables and universes are bound explicitly.

Searches made (2026-10-24):

- `msearch.py ... leanfinder "A Cohen ring with perfect residue field admits a unique
  local ring homomorphism to a complete Noetherian local ring lifting a prescribed
  residue field homomorphism"`: eight hits, including HenselianLocalRing,
  IsLocalRing.ResidueField.lift, PreTilt.untilt, PerfectionMap.lift, and
  PerfectRing.liftEquiv_apply. None is the stated universal property of a Cohen ring.
- `msearch.py ... leansearch "Unique lifting of residue field maps from a Cohen ring
  with perfect residue field to a complete local ring"`: eight hits on residue-field
  induced maps and fraction-field lifts, none with this conclusion.
- `msearch.py ... loogle '"Cohen", "lift"'`: zero hits.
- `msearch.py ... grep 'Cohen.*unique|unique.*Cohen|Cohen.*perfect|perfect.*Cohen'`:
  zero Mathlib hits.
- `rg` of `CohenRing|Cohen.*lift|perfect.*Cohen|cohen.*residue` in both
  `lean/WeilConjectures` and `lean/Sheaf` found Cohen-ring constructions and the
  existing existence-only `IsLocalRing.exists_cohenRing_lift`. Its full signature
  and docstring were read: it requires a residue isomorphism and does not assert
  uniqueness, so it cannot replace this theorem. The formal-smoothness dependency
  is a lifting tool, also not the same statement.
- `grep -rn 'lem-per-perfect-cohen-residue-map' lean/WeilConjectures`: no match.
- Further `rg` for `Cohen.*unique|unique.*Cohen|Cohen.*perfect|perfect.*Cohen`
  in the two project roots, and for `perfect_cohen_residue_map|existsUnique_cohenRing_lift`
  in Mathlib, both project roots and `dag/lean_names_upstream.json`: no matches.
- Source inspection found and reused `PerfectRing`; no perfectness predicate is copied.

No statement fault or STATEMENT-DISPUTED issue was found. The prescribed server
`scompile.py` compiled both sandbox and library forms cleanly, with no warnings.

## Second reading by Q110

This is a second pass by the same dispatcher-started worker, not an independent
agent review; the assignment explicitly forbids starting other agents and reserves
the independent review for the maintainer. I reopened the node and the Lean file.
The Cohen predicate includes prime p and all the source-ring hypotheses; the quotient
is literally A/pA; PerfectRing's single field is the specified bijectivity. R retains
Noetherianity, locality and maximal-ideal completeness. The given j is any field map,
not an isomorphism. The existential uniqueness quantifier applies to ring maps f,
with exactly the locality equality and canonical quotient-map equality. There is no
extra continuity hypothesis or restriction on the characteristic of R. No mismatch
was found and no statement correction was needed. The proof-only import is the
recorded formal-smoothness dependency; all three statement dependency declarations
are used directly. The proof docstring covers every node proof step.
