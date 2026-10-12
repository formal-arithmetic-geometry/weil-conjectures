## What changed

Proved `Algebra.isQuasiFiniteAtPrime_iff_principalLocalization` in
`Sheaf.RingTheory.QuasiFiniteAtPrimePrincipalLocalization`, preserving its signature.
The proof establishes finite type and primality directly from Mathlib, then restricts the
localization open embedding to the topological fibre. Injectivity of the base localization
spectrum map identifies that fibre with the required inverse image. Two proved private helpers
handle the elementary topology and the existing `preimageHomeomorphFiber` identification.
The node's proof, proof dependencies and proof origin now describe this route.
The original theorem signature and docstring are retained.
Added the proof-only import `Mathlib.RingTheory.Localization.Away.AdjoinRoot`.
Both original public imports remain. The second reader removed the redundant explicit
`Mathlib.Topology.LocalAtTarget` import; its declarations are already available transitively.

## Proved and sorry left

Closed the sole original hole:
`Algebra.isQuasiFiniteAtPrime_iff_principalLocalization`
(node `lem-weil-pbc-quasi-finite-at-prime-principal-localization`).
Added zero holes; no `sorry` remains in the delivered module. Both private helpers are proved.
This is a proof, not a decomposition: all ingredients are proved in Mathlib.
The resumed worker independently recompiled the module without warnings through `lcompile.py`.

## No longer needed

The second reader also removed the redundant proof-only import
`Mathlib.Topology.LocalAtTarget` added by the first worker. This is import cleanup,
not pruning a project DAG node.

Removed the proof-only import `Sheaf.RingTheory.LocalizationPrimeResidueFieldIso`.
Its theorem `IsLocalization.prime_localRing_residueField_iso` is unnecessary; the two
prime-correspondence clauses used here are proved directly by Mathlib.
Whether this module becomes unreachable globally depends on other importers.

Removed from this node's proof dependencies:
- `lem-weil-pbc-localization-away-universal-property`: the supplied map and square suffice;
  no induced ring map or inverse map is constructed.
- `lem-weil-pbc-localization-prime-residue-field-iso`: no local-ring or residue-field
  isomorphism is needed; the prime extension and contraction use Mathlib directly.
- `def-weil-pbc-localization-at-prime`: no explicit local-ring construction is needed.
- `lem-weil-pbc-algebra-tensor-pushout-universal-property`: no tensor-product maps or
  fibre-ring isomorphism need be constructed.
- `def-weil-affine-spectrum` and `def-weil-open-immersion`: scheme-level constructions are
  unnecessary; the needed localization open embedding is a Mathlib PrimeSpectrum theorem.

The principal-localization open-immersion node stays as the source of the open-embedding fact;
its Mathlib topological specialization is used. The fibre-ring-primes-bijection node stays:
`PrimeSpectrum.preimageHomeomorphFiber` provides the relevant homeomorphism.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The old nine-step plan constructs a fibre-ring isomorphism, but
this is unnecessary for the openness conclusion. The topological commuting-square argument
implements the same open-subset argument of Stacks 077H with a shorter route.
This node is not among the unit's `realized` statement or steps; no unit route is bypassed.
No other module, definition or statement was adapted.


## Second reading by K1

1. **Interface: PASS.** Compared the delivered module with the repository version by diff
   and checked the complete existing theorem signature byte for byte. Its signature,
   visibility, docstring and both public imports are unchanged. No definition or other
   module is changed; there are no statement changes or change records.
2. **Proof and axioms: PASS.** Independently compiled the module with `lcompile.py` without
   warnings. A scratch copy with `#print axioms` for the main theorem and both private
   helpers shows exactly `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`.
   The delivered source contains no `sorry`, axiom, unsafe, opaque, implemented_by or extern.
   Checked the scalar tower against the square equation, avoidance of every power of the
   localization element, prime extension and contraction, and the restricted open embedding.
   Every object is constructed from actual data; no unproved existence theorem is used.
3. **Split statements: PASS (none).** No holes or split-off statements were added. Both
   private helpers are proved and strictly intermediate: singleton openness under a fibre
   restriction, and transport along the existing fibre homeomorphism. Their edge cases are
   sound: no topology is required on the bases; an empty source admits no specified point;
   singleton fibres and identity embeddings satisfy the equivalence. For the main theorem,
   units `f = 1`, `g = 1` cause no exception, while zero or nilpotent elements are excluded
   by the nonmembership hypotheses; a zero target ring has no prime `q`.
4. **Route and pruning: PASS after cleanup.** Read Stacks Tag 077H and its open-fibre proof,
   plus the pinned Mathlib declarations. Searched the project/upstream RingTheory modules,
   Mathlib QuasiFinite and topology files, Loogle for open-embedding openness lemmas, and
   Lean Finder for open embeddings between fibres in commuting squares. The available
   restriction and image-openness lemmas are already used; category-theoretic pullback
   results would add machinery. No shorter exact theorem for this statement was found.
   The removed six old proof-dependency nodes are all listed in `No longer needed`.
   Inspected `dag/units/sk-thm-p1.json`: this node is not a realized statement or step,
   and the unit's route is preserved. Removing AdjoinRoot in a scratch copy makes finite
   type synthesis fail. Removing LocalAtTarget still compiles, so removed that import.
   The retained public imports provide the statement's definition and localization API.
5. **DAG: PASS.** Compared the delivered node with the repository node: only `proof`,
   `proof_deps`, `proof_origin` differ. The dependency list equals the union of step uses.
   The steps describe the actual finite-type instance, prime correspondence, square,
   restriction and homeomorphism argument. The retained open-immersion dependency is used
   through Mathlib's topological specialization, as the report and node explicitly explain.
   No new node is required for a holed theorem because there are no remaining holes.

Second-reading changes: removed one redundant proof-only import,
`Mathlib.Topology.LocalAtTarget`, and updated this report. The mathematical proof and DAG
were correct and were retained. Closed one original hole, added zero holes: proved 1 of 1,
zero split off. Final compilation and the delivery tool's axiom/preflight checks passed
in the dry run (review class CODEX because the proof-route node file changes).
