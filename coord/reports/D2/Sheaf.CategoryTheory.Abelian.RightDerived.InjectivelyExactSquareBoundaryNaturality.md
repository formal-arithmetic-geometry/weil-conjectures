## What changed

Proved the object-variable naturality clause in `boundary_object_naturality`, using a
map of the explicit short exact resolution sequences and homology connecting-map
naturality. The target theorem now combines this proved clause with the named
`square` clause. Added the proof-only import
`Mathlib.Algebra.Homology.HomologySequenceLemmas`.

## Proved and sorry left

`CategoryTheory.InjectivelyExactSquare.boundary_object_naturality` is proved.
The target `CategoryTheory.InjectivelyExactSquare.boundary_naturality` is proved from
its two component lemmas. The remaining sorry is
`CategoryTheory.InjectivelyExactSquare.boundary_square_naturality`, recorded as node
`lem-sc-injectively-exact-square-boundary-square-naturality`.

## No longer needed

No imports or existing DAG nodes were pruned; the resolution short-exactness node and
complex long-exact naturality node remain required.

## Where the brief, the DAG or earlier work was wrong

The original target bundled two independent naturality assertions. The object-variable
assertion can be proved directly by the existing resolution-sequence and connecting-map
API; the square-variable assertion is split into a strictly smaller named theorem for a
parallel worker.

## New nodes

`lem-sc-injectively-exact-square-boundary-square-naturality` records the remaining
square-morphism naturality theorem and its short-exact-sequence proof route.

The required dry run is blocked: deliver3.py raises ImportError because tools/import_cycles.py lacks refuse_missing. No delivery was pushed.

## Second reading by D2

1. Compared both delivered modules with the repository versions. The target theorem's
   statement is byte-for-byte unchanged; the added square-naturality module and the
   proof-only imports are declared in this report.
2. Compiled both sandbox modules with `lcompile.py --all`; they compile without errors.
   The only remaining `sorry` is the named public theorem
   `boundary_square_naturality`, and its split node and docstring are present. The
   object-variable helper is private and fully proved.
3. The split statement is the square-morphism clause of the target, with the same
   hypotheses and conclusion and no weakening. Its node records the short-exact
   sequence and connecting-map naturality source; no duplicate library theorem was
   found.
4. The proof follows the existing explicit resolution-sequence route and uses the
   homology connecting-map naturality API. The added Mathlib import is proof-only;
   no unused imports or old proof dependencies were pruned.
5. The target node's proof dependencies include the split square clause and the
   resolution/long-exact dependencies used by the proof. The split node's Lean
   declaration and statement match its module exactly, and the unit route is retained.

I changed the object-variable helper to a private theorem so the delivery adds no
   untracked public declaration; no mathematical statement or target interface changed.
