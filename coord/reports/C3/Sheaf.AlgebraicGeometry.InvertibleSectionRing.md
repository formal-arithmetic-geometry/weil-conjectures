## What changed

Completed all four remaining multiplicative laws in
`Sheaf.AlgebraicGeometry.InvertibleSectionRing`, without changing any existing signature,
visibility, or ring operation. Added the proof-only import
`Mathlib.Tactic.CategoryTheory.Monoidal.Basic`.

The unit proofs evaluate the unitors. A private induction identifies the exponent-zero
isomorphism with the right unitor. Associativity follows from a private induction on the
exponent isomorphisms, including their arithmetic casts, and evaluation on tensor sections.
Commutativity is proved on a covering sieve of local free generators: tensor powers of the
same generator multiply compatibly, and scalar coefficients commute. Sheaf separatedness
glues these equalities. All private helpers are fully proved; the private local tensor-power
section construction is explicit recursive data and uses no unproved existence theorem.
The node's proof and proof_origin now describe these arguments.

The module compiles without warnings through `lcompile.py`. The arguments include degree
zero and the empty scheme (the covering-sieve condition is then vacuous). No tactic skips
kernel checking. The public construction and all four theorem statements are unchanged.

## Proved and sorry left

Closed four holes, all under node `def-sc-invertible-section-ring`:

- `AlgebraicGeometry.Scheme.Modules.sectionRing_one_mul`
- `AlgebraicGeometry.Scheme.Modules.sectionRing_mul_one`
- `AlgebraicGeometry.Scheme.Modules.sectionRing_mul_assoc`
- `AlgebraicGeometry.Scheme.Modules.sectionRing_mul_comm`

No `sorry` remains in the item. No holes were added or split off. This is a proof, not a
decomposition. The previously proved additive and grading laws remain complete.

## No longer needed

None. No imports were removed and no planned dependency nodes or modules were pruned.
Both original public imports remain necessary for statements and definitions. The new
private import supplies the monoidal tactic actually used in the associativity proof.
The DAG already had empty proof_deps; it remains empty.

## Where the brief, the DAG or earlier work was wrong

The previous node described the four homogeneous laws as open and had no named dependencies
for them. Its plan is now fully realized using the existing tensor-section API and proved
private helpers. The local free-generator API's `exists_isFreeGenerator` assumes the
SheafOfModules invertibility class, whereas this item assumes Scheme.Modules.IsInvertible.
The proof explicitly converts the latter's pullback trivialization through overEquiv and
restrictFunctorIsoPullback before applying exists_isFreeGenerator_of_iso; it does not assume
an unprovided instance connecting these classes.

The cited Stacks pages 01PZ and 01N8 use the graded section ring rather than give a detailed
proof of its ring laws. The delivery supplies these details directly, retaining the
specified construction and the unit's route. No statement correction was needed.

## Second reading by C3

1. Compared the entire delivered module with the repository version using `diff -u`.
   Verdict: every existing signature, visibility, public import, operation and construction
   is unchanged. The only Lean changes are four proof bodies, proved private helpers,
   a proof-only monoidal tactic import, and the module overview. No change record is needed.
2. Independently compiled the module with `lcompile.py`: clean, 13.4 seconds. Compiled a
   scratch copy with `#print axioms` for all 26 declarations, including all private helpers
   and final instances: each uses only `propext`, `Classical.choice`, and `Quot.sound`.
   There is no remaining `sorry`, prohibited declaration, kernel-checking bypass, or
   hollow definition. The local tensor-power section is explicit recursion; the local
   generator is used within a proof, not chosen as data from an unproved existence claim.
   Verdict: all four originally open laws are proved without inherited `sorryAx`.
3. No statements were split off and no holes were added. Read each private helper and its
   use: exponent transport follows by equality elimination; the two coherence inductions
   evaluate the specified exponent isomorphisms; tensor powers of a local generator are
   generators and their products agree. Degree zero is handled by the unit generator;
   the empty scheme is covered vacuously and separatedness still applies. Verdict: the
   helpers are true and suffice for precisely the unchanged laws.
4. Searched the repository and Mathlib for exponent associativity, commutativity and unit
   results, and independently queried Lean Finder for rank-one tensor commutativity.
   Its `Module.Invertible.tmul_comm` and `tensorProductComm_eq_refl` concern ordinary
   modules, not sections of these sheaf tensor powers or their exponent casts; they do
   not replace this local calculation directly. The existing tensor-section API supplies
   the evaluation, restriction and bilinearity formulas actually used. Both public imports
   support constructions, and the private tactic import is used. Original `proof_deps`
   was empty, so `No longer needed` is complete. Read the unit record
   `dag/units/sk-thm-curveestimate.json`, including `realized`: the delivery proves this
   supporting construction and bypasses no unit statement or step. Verdict: route and
   pruning requirements pass.
5. Compared the delivered node with its repository version. Only `proof` and
   `proof_origin` change; `proof_deps` remains empty. The steps faithfully describe the
   Lean inductions, evaluation, local-generator construction, covering sieve and
   separatedness argument. The recorded declarations and statement are unchanged; no
   new nodes are needed for fully proved private implementation helpers. Verdict: the
   DAG agrees with the Lean proof.

Second reading changed only this report, adding the independent review and verification
results. No Lean or node repair was necessary. Four holes closed, zero holes added,
zero split off, and no imports or dependency modules pruned.
