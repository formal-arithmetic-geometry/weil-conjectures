## Worker report

The module `Sheaf.RingTheory.TateResidueLatticeIdentity` states
`TateResidue.residue_lattice_identity`, with its whole proof postponed by `sorry`.
It adds no definitions, helper theorems, or nodes. The informal statement is unchanged.

Hypothesis and conclusion correspondence:

- “k a field”: `{k : Type u} [Field k]`.
- “C a commutative k-algebra”: `{C : Type v} [CommRing C] [Algebra k C]`.
- “V a C-module”: `{V : Type w} [AddCommGroup V] [Module C V]`, together with
  `[Module k V] [IsScalarTower k C V]` expressing the induced compatible k-vector-space
  structure. These are exactly the structures used by the recorded residue calculus;
  compatibility determines the k-action from the C-action, so this adds no restriction.
- “A,B k-subspaces of V”: `(A B : Submodule k V)`.
- “(fA+A)/A and (fB+B)/B finite-dimensional for every f”: `(hA : Admissible C A)` and
  `(hB : Admissible C B)`. The existing definition is `∀ f, E A (act k f)`;
  `E A T` is `(A.map T).AlmostLE A`, and `AlmostLE X A` means
  `∃ W, W.FG ∧ X ≤ A ⊔ W`. Over a field this is equivalent to finite-dimensionality
  of `(X+A)/A`: lift a finite quotient basis in one direction and take the quotient
  image of W in the other. Thus the existing predicate has precisely the node's meaning.
- “A+B has the same admissibility property”: `Admissible C (A ⊔ B)`.
- “A∩B has the same admissibility property”: `Admissible C (A ⊓ B)`.
- The displayed equality of k-linear residue maps is
  `res C A + res C B = res C (A ⊔ B) + res C (A ⊓ B)`.
  Each `res C L` has type `KaehlerDifferential k C →ₗ[k] k`, so the equality is of
  whole functionals, with the sides in exactly the order written in the node.

Dependencies read and used:

- `lem-pc-tate-abstract-residue-calculus` records
  `Sheaf.RingTheory.TateAbstractResidueCalculus`, declaration
  `TateResidue.abstract_residue_calculus`. Its full signature and docstring were read.
  The module is publicly imported. It supplies the upstream `TateResidue.Admissible`,
  `TateResidue.res`, and their commutator characterization. The actual defining bodies
  in `WeilConjectures.RingTheory.TateResidue.Residue` and `TateIdeals` were also read.
- Proof dependency `lem-pc-finite-potent-trace-calculus`: imported
  `Sheaf.RingTheory.TateResidue.FinitePotentTraceCalculus`, declaration
  `Module.End.finitePotent_trace_calculus`; its full signature and proof plan were read.
- Proof dependency `def-weil-endomorphism-trace`: its Mathlib match is
  `LinearMap.trace` in `Mathlib.LinearAlgebra.Trace`, imported for the proof plan.
  Its definition and `LinearMap.trace_eq_matrix_trace` were read.
- Proof dependency `def-weil-pbc-kahler-differentials`: its recorded declarations are
  `KaehlerDifferential`, `KaehlerDifferential.D`, and
  `KaehlerDifferential.linearMapEquivDerivation` in `Mathlib.RingTheory.Kaehler.Basic`,
  imported for the generator argument; their definitions and docstrings were read.

Source: read the local Tate PDF with `pdftotext`, including printed pp. 150–153,
particularly R5 on p. 153. It explicitly states both admissibility conclusions and
exactly the displayed residue identity. The docstring carries all eight DAG proof
steps, including the finite invariant spaces for trace subtraction; it does not assume
additivity for arbitrary finite-potent operators.

Edge cases checked mathematically against the signature: A=B (including characteristic
2), A⊆B, A=0, B=V, V=0, and finite-dimensional V. No distinctness, nontriviality, finite
rank, domain, faithful action, or characteristic restriction is imposed. The zero
commutative C-algebra is allowed; its unital modules are zero, for which the statement
still holds. Independent explicit universes u,v,w allow arbitrary field, algebra, and
module sizes; no hidden implicit variables, local notation, or instances occur.

Searches (2026-10-21):

- `msearch.py ... leanfinder` query “Tate residues for admissible subspaces sum and
  intersection identity and admissibility of their sum and intersection”: eight hits
  concerning heights, ideal classes, Nobeling products, and Dedekind zeta residues;
  none concerns the abstract Tate residue or its admissibility clauses.
- `msearch.py ... loogle` query `TateResidue.Admissible, TateResidue.res`: zero hits,
  unknown identifier `TateResidue.Admissible` in the Mathlib index.
- `msearch.py ... grep` query
  `res_sup_add_res_inf|namespace TateResidue|def Admissible`: three Mathlib hits for
  unrelated admissibility predicates (ABC, t-structures, box integrals); no Tate residue.
- `msearch.py ... leansearch` query “Tate abstract residues inclusion exclusion for sum
  and intersection of admissible subspaces”: eight hits on sums over unions/intersections,
  pointwise sets, and dual annihilators; no match.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  found the canonical upstream `TateResidue.res_sup_add_res_inf` in
  `WeilConjectures.RingTheory.TateResidue.ResidueProperties`. Its full signature and
  proof were read. It gives only the equality (with the sides reversed), without
  admissibility of sum or intersection; thus it is not an exact whole-node match.
  The module's local admissibility proofs for images/preimages are not exported
  declarations. No existing declaration states the three conclusions together.
- `grep -rn 'lem-pc-tate-residue-lattice-identity' lean/WeilConjectures`: no hits.
- `rg` in project and Mathlib for `residue_lattice_identity|admissible_sup_inf|Admissible\.(sup|inf)`:
  no hits; the new declaration name is free and no matching closure theorem was found.

No statement fault or STATEMENT-DISPUTED issue was found. No dependency repair is needed.

## Second reading by NK

This is a second pass by the same worker, not a claimed independent agent review;
the dispatcher's maintainer performs the independent reading after delivery.
Reopened the node and generated module and checked each binder and all three conjuncts:
the field, commutative algebra, compatible module structures, k-subspaces and two
admissibility assumptions match, and both closure properties precede equality of the
actual k-linear maps. In particular the equality-only upstream result does not discharge
the first two clauses. The docstring includes the injection for intersection admissibility,
compatible projections, both length-three-word invariant subspaces, restricted trace
subtraction and extension from f dg to all differentials. No mismatch or correction
was found. Only the node's lean field changes.
