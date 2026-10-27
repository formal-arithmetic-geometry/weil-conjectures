## Worker report

The module `Sheaf.FieldTheory.SmallFieldEmbeddingsConjugate` states
`IsAlgClosed.exists_ringEquiv_comp_eq_of_small`, with exactly one postponed theorem
and no new definitions. Its proof is `sorry`, as required for stage 2.
The module and theorem docstrings cite Stacks Tag 04LR, more-groupoids.tex,
lemma-groupoid-on-field-explain-points, construction (3), read at lines 1070–1106.
The theorem docstring includes all six accepted DAG proof steps, including the
cardinal argument valid for singular cardinals, coefficient substitution,
fraction extension, and uniqueness of algebraic closures with a twisted base map.

Hypotheses and conclusion, clause by clause:

- Fields F and K: `(F : Type u) (K : Type v) [Field F] [Field K]`.
  The universes u and v are declared explicitly and independently.
- K algebraically closed: `[IsAlgClosed K]`. This is precisely the polynomial-root
  condition via Mathlib's equivalent splitting definition, not algebraicity over F.
- Embeddings a and b: `(a b : F →+* K)`. Unital ring homomorphisms from a field
  to a nontrivial field are injective by `RingHom.injective`; no injectivity or
  scalar compatibility assumption is added. Separate homomorphisms are necessary
  because the two copies of F in K need not coincide.
- Prime subfield P, the smallest subfield containing 1:
  `(⊥ : Subfield K)`. Every subfield contains 1, so the bottom subfield is exactly P.
  Its algebra structure on K is `Subfield.toAlgebra`, whose algebra map is its subtype
  inclusion (`Subfield.algebraMap_ofSubfield`). No new prime-field notion is introduced.
- Cardinal inequality: `hsmall : max Cardinal.aleph0
  (Cardinal.lift.{v} (Cardinal.mk F)) <
  Cardinal.lift.{u} (Algebra.trdeg (⊥ : Subfield K) K)`.
  Both operands live in `Cardinal.{max u v}`. These lifts change no mathematical
  cardinal, and impose no equality of universes. `Cardinal.aleph0` denotes |ℕ|.
- A field automorphism of K: `∃ τ : K ≃+* K, ...`; a ring equivalence supplies
  bijectivity and the full field isomorphism structure.
- The prescribed extension equality: `τ.toRingHom.comp a = b`. Equality of ring
  homomorphisms is exactly equality on every element of F, namely τ(a(c)) = b(c).

Dependency declarations read and used:

- def-weil-field: `Field`, Mathlib.Algebra.Field.Defs, full class signature/docstring read.
- def-weil-algebraic-closure: `IsAlgClosed`, Mathlib.FieldTheory.IsAlgClosed.Basic,
  as explicitly specified by its mathlib_match; also read `AlgebraicClosure` in
  Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure. Only the algebraic-closedness
  clause is needed to state this item.
- def-pc-field-extension: `Algebra`, Mathlib.Algebra.Algebra.Defs; its recorded
  given-map presentation is `RingHom.toAlgebra`. Here a and b are the specified
  extension maps. No global F-algebra instance is chosen, so neither embedding
  is silently identified with the other. The dependency module is publicly
  available through the imports of the field and transcendence-degree APIs.
- def-kun-transcendence-degree: `Algebra.trdeg`,
  Mathlib.RingTheory.AlgebraicIndependent.Basic, full definition read.
- Canonical subfield inclusion: Mathlib.Algebra.Field.Subfield.Basic,
  `Subfield.toAlgebra`, `Subfield.algebraMap_ofSubfield`, and its bottom lattice.

All currently stated proof dependencies are imported non-publicly through
Mathlib.FieldTheory.IsAlgClosed.Classification (the cardinal bound and algebraic
closure of a transcendence basis),
Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure (existence),
Mathlib.FieldTheory.IsAlgClosed.Basic (uniqueness, already a public statement
import), and Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
(existence of a basis and IsTranscendenceBasis). Definitions used in a statement
remain public; proof-only imports remain plain imports.

Edge cases checked before writing:

- Finite fields F are included; |F| is dominated by ℵ₀, as in the node.
- Countable F is included with the same inequality; no uncountability of F is assumed.
- Any characteristic is allowed, including characteristic zero; P is not replaced
  by ℚ or by a fixed finite field. The existence of a and b already enforces equal
  characteristics, so no additional characteristic hypothesis is needed.
- Transcendence degree zero, finite, or ℵ₀ makes the strict size premise false,
  exactly as in the node, without excluding these types by the binders.
- The case a = b is included and admits the identity automorphism.
- No regularity assumption on the infinite cardinal is imposed; the proof compares
  maxima and does not subtract infinite cardinals.
- Independent field universes are handled by explicit cardinal lifts.
- Zero rings are excluded by Field, precisely as the node requires.

Searches for an existing exact statement:

- msearch.py leanfinder: “Two embeddings of a small field into an algebraically
  closed field with larger transcendence degree are conjugate by a field automorphism”.
  Eight hits, principally Field.embEquivOfIsAlgClosed, Field.embEquivOfEquiv,
  Field.Emb.Cardinal.succEquiv, and IsAlgClosed.ringEquiv_of_equiv_of_charZero.
  The embedding equivalences assume algebraicity, and field classification does
  not assert the prescribed restriction to F. No exact match.
- msearch.py loogle: `IsAlgClosed, RingEquiv`. Six hits, including
  IsAlgClosed.equivOfTranscendenceBasis and the uncountable-field classification
  theorems. The first needs equipotent bases already chosen; neither states the
  present size-hypothesis/conjugacy conclusion. Its full implementation was read.
- msearch.py leansearch: “Extend an isomorphism between small subfields to an
  automorphism of a large algebraically closed field”. Eight hits, including
  IsAlgClosure.equivOfEquiv.congr_simp, AlgEquiv.liftNormal, and algebraic closure
  transport. None gives conjugacy from this transcendence-degree size hypothesis.
- msearch.py grep, FieldTheory:
  `equivOfTranscendenceBasis|equivOfEquiv|small.*[Ee]mbed|embeddings.*conjugate`.
  Fourteen hits. Classification and equivOfEquiv are relevant proof tools, but
  not existing statements of this item.
- rg in Mathlib FieldTheory, WeilConjectures, and Sheaf:
  `prime(Field|Subfield)|[Pp]rime.*[Ss]ubfield|small.*[Ee]mbed|embeddings.*conjugate`.
  Found prime-field APIs and unrelated separable-embedding or Frobenius results;
  no exact conjugacy theorem. Existing project examples use ⊥ : Subfield K for P.
- rg for the item id and proposed declaration name in WeilConjectures, Sheaf,
  Mathlib, and dag/lean_names_upstream.json: no existing declaration or name clash.

There are no new nodes, dependency repairs, statement corrections, or disputed
statements. Only the item's lean field changes. The inherited stage-1 BLOCKED
ending is superseded by the stage handoff in brief-stage2.md §0: the accepted
split is preserved in full and this is its stage-2 statement delivery.

Validation: scompile.py Q86 lem-sfb-small-field-embeddings-conjugate compiled this
file in sandbox mode (4.1 s) and module mode (1.5 s), both without errors or warnings.
No direct Lean command, local build, or direct Git command was run.

## Second reading by Q86

A second pass by the same dispatched worker opened the completed module alongside
the full node; no other agent was started, as the dispatcher explicitly prohibits
subagents. The maintainer's independent delivery review remains separate.
The comparison checked every binder and conclusion: two fields in independent
universes, IsAlgClosed K only, two arbitrary ring embeddings, bottom subfield
with its canonical inclusion, the maximum with ℵ₀, the strict inequality with
transcendence degree after lifting to a common universe, and an existential
bijective ring homomorphism with precisely the required restriction. No extra
scalar structure, characteristic, cardinal regularity, or basis hypothesis occurs.
The prime-subfield expression is Mathlib's canonical object, not a private copy.
The theorem signature agrees verbatim with lean.statement. The full accepted
six-step proof is present in the docstring, and all recorded proof dependencies
with Lean declarations or Mathlib matches are imported. No mismatch was found,
and no change to the accepted DAG split was needed.
