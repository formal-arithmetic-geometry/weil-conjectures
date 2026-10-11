## Worker report

The module `Sheaf.RingTheory.GlobalDimensionFiniteModules` states
`Ring.hasGlobalDimensionLE_iff_finite_iff_cyclic`, with proof `sorry`.
It states the three-way equivalence as `(1 ↔ 2) ∧ (2 ↔ 3)`.
No new definitions or dependency modules are needed.

Hypotheses and clauses:

- The ring `R` is `(R : Type u) [CommRing R]`. Stacks Algebra's standing convention
  [00AQ](https://stacks.math.columbia.edu/tag/00AQ) says that rings are commutative
  with identity and allows the zero ring. This is also the ring assumption in the
  recorded dependency. Thus this is the source's ring, with no additional assumption.
- The nonnegative integer bound is `(n : ℕ)`; this includes zero.
- Condition (1), every module admits a projective resolution of length at most `n`, is
  `Ring.HasGlobalDimensionLE.{u, max u v} R n`.
- Condition (2), every finite module admits such a resolution, is
  `∀ M : ModuleCat.{max u v} R, Module.Finite R M →
  ModuleCat.HasProjectiveResolutionLE M n`. Finite means finitely generated, not a
  finite underlying set. No Noetherian assumption is imposed.
- Condition (3) is `∀ I : Ideal R, ModuleCat.HasProjectiveResolutionLE
  (ModuleCat.of R (ULift.{v} (R ⧸ I))) n`. All ideals, including bottom and top,
  occur. The natural scalar action is used. `ULift.moduleEquiv` identifies this
  lifted module linearly with `R/I`; this is a change of carrier universe only.
- Both `↔` clauses together express exactly the three conditions being equivalent.
  Modules have universe `max u v`, with `u` and `v` explicit and arbitrary; cyclic
  quotients live in that same universe after lifting. The module universe is never
  forced below the ring universe, so a too-small module universe cannot make a
  test vacuous.

Dependency declarations read and used:

- `def-weil-pbc-finite-global-dimension`: `Sheaf.RingTheory.GlobalDimension`,
  `Ring.HasGlobalDimensionLE` and `ModuleCat.HasProjectiveResolutionLE`.
  Read the whole module, including the main recorded declaration
  `Ring.HasFiniteGlobalDimension`. The resolution predicate is existence of a
  `CategoryTheory.ProjectiveResolution` with zero terms above `n`, not Mathlib's
  Ext-defined projective dimension. The global bound quantifies over every module.
- `def-weil-finitely-generated-module`: `Mathlib.RingTheory.Finiteness.Defs`,
  `Module.Finite`. Its signature and docstring identify finite generation with
  `(⊤ : Submodule R M).FG`.
- Quotients use `Mathlib.RingTheory.Ideal.Quotient.Defs`; lifting uses the actual
  `Module R (ULift M)` instance in `Mathlib.Algebra.Module.ULift`.

Source and proof: the local Stacks checkout is absent on this machine. Read the
full statement and proof at [Stacks 065T](https://stacks.math.columbia.edu/tag/065T).
The declaration docstring carries all four DAG proof steps: implications to
finite and cyclic modules; a well-ordered exhaustive filtration; cyclic successive
quotients identified by the kernel of the generator map, including the zero quotient;
and the well-ordered-union projective-dimension lemma. It names the proof nodes.

Edge cases checked before writing: `n = 0` means projective modules and is not excluded;
`I = ⊥` gives the regular module; `I = ⊤` gives zero; the zero ring is permitted;
the zero module is tested as well. No nontriviality, locality, characteristic,
finite cardinality, proper ideal, or Noetherian restriction occurs. Empty generating
sets in the proof give the zero module and admit the zero resolution.

Searches made on 2026-10-11 (the remote search log is `searches.jsonl`):

- `msearch.py leansearch`: “A ring has global dimension at most n iff every finitely
  generated module or every cyclic quotient module has a projective resolution of
  length at most n”. Service unavailable (Internal Server Error); no verdict inferred.
- `msearch.py leanfinder`: “global dimension at most n iff all cyclic modules have
  projective dimension at most n”. Eight hits, all general categorical projective
  dimension facts; none tests all modules using finite or cyclic modules.
- `msearch.py loogle`: `CategoryTheory.HasProjectiveDimensionLE, Module.Finite`.
  Two localization tests for a single finite module over a Noetherian ring, not this
  global equivalence.
- `msearch.py grep`: `globalDimension|HasGlobalDimension|hasProjectiveDimensionLT_of_forall_finite`.
  Only the regular-ring finite-module Ext test appears; it is not the statement here.
- `rg` searched `WeilConjectures` and `lean/Sheaf` for global-dimension names, the
  phrase global dimension, and this node id. No source declaration matches. The
  project provides the reused global-dimension definition and regular-local-ring
  results, but no copy of this theorem. The exact theorem name is new.
- Read the two statement-dependency node records and their full recorded declarations.
  Checked all JSON statement/proof dependency lists for citers: only
  `lem-weil-pbc-regular-local-finite-gl-dim` cites this item. No correction is needed:
  source convention 00AQ supplies the meaning of “ring” already.

Validation: `scompile.py C1 lem-weil-pbc-global-dimension-finite-modules-suffice`
compiled the module on the server in 1.2 seconds, with no errors or warnings.
No statement dispute or node fault found. The worker does not deliver or write a
second-reading section; that belongs to the independent reader.

## Second reading by C1

The node introduces a commutative ring with identity `R : Type u` (zero ring allowed),
then `n : ℕ` (so `n = 0` is included), and asserts a conjunction of two equivalences.
The Lean theorem `Ring.hasGlobalDimensionLE_iff_finite_iff_cyclic` renders these items as
`(R : Type u) [CommRing R] (n : ℕ)` and the following clauses:

- Condition (1) is `HasGlobalDimensionLE.{u, max u v} R n`, using the dependency's
  predicate that quantifies over every `ModuleCat.{max u v} R`.
- Condition (2) is `∀ M : ModuleCat.{max u v} R, Module.Finite R M →
  ModuleCat.HasProjectiveResolutionLE M n`, exactly finite generation plus the same
  resolution bound.
- Condition (3) is `∀ I : Ideal R, ModuleCat.HasProjectiveResolutionLE
  (ModuleCat.of R (ULift.{v} (R ⧸ I))) n`, ranging over every ideal and using the
  lifted quotient only to place it in the module universe. The outer conjunction is
  exactly `(1 ↔ 2) ∧ (2 ↔ 3)` in the node.

The dependency declarations were reread: `Ring.HasGlobalDimensionLE` and
`ModuleCat.HasProjectiveResolutionLE` in `Sheaf.RingTheory.GlobalDimension`, and
`Module.Finite` from `Mathlib.RingTheory.Finiteness.Defs`. Their meanings match the
node. The quotient and `ULift` constructions use Mathlib's standard ideal quotient
and module lift; no private notion is introduced. The theorem has explicit `u` and `v`
through the universe levels in its type, so no module universe is accidentally too small.

Edge cases are covered: `n = 0`; bottom and top ideals (regular and zero quotients);
the zero ring and zero module; empty generating sets in the proof; and arbitrary
universe `v`. No characteristic, Noetherian, locality, properness, or finite-cardinality
hypothesis is added. The source place, Stacks Algebra Lemma 065T, assumes only the
standing commutative-ring convention 00AQ, which is exactly `[CommRing R]` here.

I repeated the three existing-definition searches (LeanSearch/LeanFinder or Loogle,
and grep over Mathlib, `WeilConjectures`, and `lean/Sheaf`) for global-dimension
reduction, finite-module testing, and cyclic-quotient testing. They found only the
recorded global-dimension definitions and general projective-dimension APIs; no
matching theorem exists. The theorem therefore remains a new declaration.

No mismatch was found between the node and the Lean signature; no statement correction,
new definition node, or dependency module was needed. Compilation with `scompile.py`
was clean (only the intentional `sorry` proof is present).
