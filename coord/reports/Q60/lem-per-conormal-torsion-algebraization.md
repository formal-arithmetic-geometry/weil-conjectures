## Worker report

The module `Sheaf.RingTheory.ConormalTorsionAlgebraization` states
`AdicCompletion.exists_finiteType_algebraization_of_conormal_torsion`, with its entire
proof postponed by `sorry`. It introduces no definition and no additional theorem.
The node is unchanged except for its `lean` field. No statement correction, new node,
or dependency repair is needed.

Source read: `literature/stacks-project/more-algebra.tex`, lines 32036–32102,
Tag 0ALR, `lemma-quotient-by-idempotent`, including its proof. The module's docstring
contains all nine steps of the accepted DAG proof, with the dependency identifiers.

Every hypothesis and clause has the following rendering:

| Node clause | Lean rendering |
| --- | --- |
| A, B, C commutative rings | `{A : Type u} {B : Type v} {C : Type w}` and the three `CommRing` instances |
| A Noetherian | `[IsNoetherianRing A]` |
| An ideal I of A | `(I : Ideal A)` |
| B a finite type A-algebra | `[Algebra A B]`, `(hB : (algebraMap A B).FiniteType)` |
| I-adic completion of B | `AdicCompletion (I.map (algebraMap A B)) B` |
| Surjection from the completion to C | `(f : AdicCompletion (I.map (algebraMap A B)) B →ₐ[A] C)` and `(hf : Function.Surjective f)` |
| The induced A-algebra on C | `[Algebra A C]` with `f` an `A`-algebra map; every ring surjection admits precisely this induced structure, so this adds no hypothesis |
| Kernel J | `RingHom.ker f.toRingHom` |
| Conormal J/J² as a module over the completed ring | `(RingHom.ker f.toRingHom).Cotangent`; Mathlib defines it as J modulo J acting on J, and `Ideal.map_toCotangent_ker` identifies the denominator's image with J² |
| Some c ≥ 0 | `∃ c : ℕ` in `hJ`; zero is allowed |
| Every element of extended I^c acts by zero | `∀ r ∈ (I ^ c).map (algebraMap A (AdicCompletion (I.map (algebraMap A B)) B)), ∀ x : (RingHom.ker f.toRingHom).Cotangent, r • x = 0` |
| Finite type A-algebra that algebraizes C | `∃ (D : Type (max u v)) (_ : CommRing D) (_ : Algebra A D), (algebraMap A D).FiniteType ∧ ...` |
| Its I-adic completion is isomorphic to C as an A-algebra | `Nonempty (AdicCompletion (I.map (algebraMap A D)) D ≃ₐ[A] C)` |

All three input rings have independent explicit universes. The witness can be taken
in `Type (max u v)`: a finite type algebra has a presentation as a quotient of a
finite-variable polynomial algebra over A, and can be transported into that universe.
No bound on the universe of C, no `Nontrivial`, no completeness hypothesis on C,
and no nonzero-ideal hypothesis is imposed.

Dependency declarations read and used:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing` and its ideal-finiteness characterization, lines 192–210.
- `def-weil-pbc-adic-completion`: `Mathlib.RingTheory.AdicCompletion.Basic`,
  `AdicCompletion`, lines 167–174 (compatible residue sequences); ring and canonical
  A-algebra structures from `Mathlib.RingTheory.AdicCompletion.Algebra`, lines 101–134.
- `def-weil-pbc-finite-type-algebra`: `Mathlib.RingTheory.FiniteType`,
  `RingHom.FiniteType`, lines 213–222. This is the recorded declaration; its
  equivalence with `Algebra.FiniteType` for `algebraMap` is `RingHom.finiteType_algebraMap`.
- `Mathlib.RingTheory.Ideal.Cotangent`, `Ideal.Cotangent`, lines 35–71, supplies
  the already existing quotient module rather than a new conormal definition.

Public imports are exactly the statement notions. Plain imports supply the stated
proof dependencies (including their Mathlib matches): étaleness and flatness;
formal gluing data; Noetherian completion; henselian terminology and complete-pair
henselianity; completion modulo the ideal and finite-module tensor comparison;
finitely generated idempotent ideals and localization; finite-algebra integrality;
finite-module completeness; flat quotient-power comparison; and lifting idempotents
upstairs. The two proof dependencies `lem-per-formal-glueing-finite-algebras` and
`lem-per-punctured-idempotent-complement` have neither a Lean record nor a Mathlib
match in the read DAG and therefore supply no import. They are proof prerequisites,
not notions needed to state this theorem; this delivery does not restate them.

Edge cases checked against the source and formula:

- `c = 0`: the extended zeroth power is the unit ideal, so `hJ` says the whole
  conormal is zero, equivalently J is idempotent. This is the source's idempotent case.
- `I = ⊥`: the completion is B; take a finite type quotient B/J as algebraization.
  The annihilation condition is automatic for any positive c, as it should be.
- `I = ⊤`: the completion is the zero ring, so its surjective image C is zero;
  a zero finite type algebra witnesses the conclusion.
- `J = ⊥`: the conormal is zero, and B itself is an algebraization.
- `C = 0` or `A = 0`: no nontriviality assumption excludes these cases.
- `B = 0`: again the conclusion concerns the zero algebra; all binders remain valid.

Searches actually run through the prescribed `msearch.py` wrapper:

1. LeanFinder: "A quotient of an adic completion with conormal module killed by a
   power of the ideal is the completion of a finite type algebra". Eight hits:
   completion evaluation, canonical algebra structures, and formally smooth lifting;
   none is the algebraization theorem.
2. Loogle: `"AdicCompletion", "FiniteType"`. Zero hits.
3. Mathlib grep: `algebraiz|algebrais|conormal`, subdirectory `RingTheory`.
   Twenty-five hits, mostly the `algebraize` tactic; no matching theorem.
4. LeanSearch: "Algebraization of a quotient of an adic completion with torsion
   conormal module". Eight hits: completion definitions, structures, and finite-module
   tensor comparison; no matching theorem.
5. Direct `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
   `conormal.*torsion|ConormalTorsion|finiteType_algebraization`, then
   `conormal.*torsion|conormal_torsion|algebraization|algebraisation|0ALR`.
   No existing declaration states this theorem. Other algebraization occurrences
   concern unrelated sheaf or formal-geometry statements.
6. `grep -rn "lem-per-conormal-torsion-algebraization" lean/WeilConjectures`
   and exact-name search in `dag/lean_names_upstream.json`: no hits.

The node's `lean_removed` records a deleted earlier statement with this declaration
name. Direct searches confirm it has no surviving declaration; restoring the
statement under its natural module path creates no duplicate. There is no released
repair note for this item. No STATEMENT-DISPUTED issue was found.

Validation: prescribed `scompile.py Q60 lem-per-conormal-torsion-algebraization`
compiled this module in sandbox and library module modes, cleanly, in 12.2 s and
2.2 s respectively, with no diagnostics. Every variable and universe is explicit.

## Second reading by Q60

A separate pass reread the node, the source statement, the imported definitions,
and the finished Lean signature. This is a self-check: the dispatcher expressly
forbids starting another agent, and the maintainer supplies the independent review.
The pass checked the completed ideal is IB, the kernel is that of the actual f,
the scalar r belongs to extended I^c (not just to the image of I), and the action
is on the genuine J/J² quotient. It checked that the conclusion is an A-algebra
equivalence, the existential D carries its own ring and algebra structures, and
c = 0 and zero rings are included. All hypotheses and conclusions match the table
above; no mismatch or correction was found. The only proof is the named theorem's
`sorry`; no data is postponed. The dependency records and original node fields
are preserved.
