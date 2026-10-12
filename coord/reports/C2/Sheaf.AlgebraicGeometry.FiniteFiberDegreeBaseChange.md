## What changed

Closed `AlgebraicGeometry.Scheme.Hom.finite_fiber_degree_pullback` in
`Sheaf.AlgebraicGeometry.FiniteFiberDegreeBaseChange`, preserving its complete signature.
The existing bound theorem is unchanged. No imports were added or removed; the sole public
import supplies both the statements and the already proved source-library comparison.
Updated the node proof and dependencies to match this shorter implementation.

The fibre square comes from Mathlib. Finiteness follows directly by base-change stability.
The finite old fibre is affine, so the source library's already proved
`nonempty_algEquiv_tensorProduct_Γ_of_isPullback` applies to that fibre square.
Its underlying linear equivalence and `Module.finrank_baseChange` prove the degree equality.
This comparison needs the old fibre affine, without assuming the original morphism affine.
No construction chooses data from an unproved existence theorem: the algebra equivalence used
here is provided by a proved theorem, and is used only to prove dimension equality.

## Proved and sorry left

Closed the only original hole:
`AlgebraicGeometry.Scheme.Hom.finite_fiber_degree_pullback`
(node `lem-weil-pbc-fibre-degree-base-change`).
`AlgebraicGeometry.Scheme.Hom.boundsFiberDegrees_pullback_snd` remains proved by its existing
assembly. No sorries remain in this module; no holes or modules were added.
The local single-file compile passes without warnings. The delivery dry run also checks
all declarations for forbidden axioms.

## No longer needed

No imports were removed. The following original proof dependencies are not needed by this
proof and were removed from the node's `proof_deps`:

- `def-pc-fibre-product`: the fibre square and section comparison already supply this glue.
- `def-weil-finitely-generated-module`: finiteness uses scheme base-change stability directly.
- `lem-weil-pbc-spec-finite-ring-map-finite`: no separate spectrum finiteness calculation.
- `def-weil-finite-integral-morphism`: remains a statement dependency, but no independent
  proof step uses it beyond the finite-morphism permanence and affine-source leaves.
- `lem-weil-pbc-isomorphism-finite`: no finiteness transport through an isomorphism.
- `lem-weil-pbc-finite-composition`: no composition argument for finiteness.

No extra Sheaf proof modules corresponding to these dependencies are imported.
This prunes dependencies of this node, without claiming they are globally unreachable.
The affine-spectrum and global-section compatibility nodes remain represented by the
existing proved algebra-equivalence argument. The unit's realized statement and steps are
untouched: this item is below that level.

## Where the brief, the DAG or earlier work was wrong

The DAG's search notes correctly say `fiberDegree_of_isPullback` needs a globally affine
morphism, but the underlying `nonempty_algEquiv_tensorProduct_Γ_of_isPullback` only needs
the old fibre affine. That weaker requirement is supplied by the given finite fibre and
allows the entire argument without new intermediate statements. The original longer plan
is valid, but its separate proof of finiteness after the tensor calculation is unnecessary.
The statement includes empty fibres and degree zero; both the general base-change theorem
and the general finrank theorem apply to these cases. No statement or definition changed.


## Second reading by C2

1. PASS: compared the delivered module with the repository using `diff -u`.
   The only Lean change is the body of `finite_fiber_degree_pullback`; both existing
   declaration signatures, all definitions, visibility and imports are byte-for-byte
   unchanged. There are no new modules or change records. The node changes only
   `proof`, `proof_deps` and `proof_origin`.
2. PASS: compiled the delivered file with `lcompile.py`, without errors or warnings.
   Compiled a scratch copy with `#print axioms` for both public lemmas: each uses exactly
   `propext`, `Classical.choice` and `Quot.sound`, with no `sorryAx`.
   No sorry, forbidden declaration or data definition was added. The algebra equivalence
   comes from a proved theorem, not an unproved existence statement.
3. PASS: no statements are split off, so no new statements or nodes require validation
   or duplicate searches. The old finite fibre supplies affineness without requiring
   global affineness of the original morphism. The argument includes an empty fibre:
   zero global sections tensor to zero, giving degree zero. It also specializes to
   identity base change and a nonempty degree-one fibre without additional hypotheses.
4. PASS: read the source-library global-sections comparison and its
   `fiberDegree_of_isPullback` proof. The latter assumes global affineness; the delivered
   proof uses its underlying comparison with only the finite fibre affine, followed by
   `Module.finrank_baseChange`. This is the direct existing-library route. The sole public
   import is required by the signature's `BoundsFiberDegrees` and `finrankΓ`.
   Compared old and new proof dependencies: all six removed dependencies are listed
   under `No longer needed`. No module import is removed. Read `dag/units/sk-thm-p1.json`:
   this node does not realize its statement or steps, and its unit route is unchanged.
5. PASS: checked all retained dependency records against the proof. They cover the fibre
   square, finite base-change stability, affineness, the affine global-sections comparison
   and scalar-extension dimension. The node describes the actual shorter proof and its
   source-library origin; there are no new nodes. The existing declaration docstring
   still records the original longer mathematical plan, while the node and this report
   record the implemented shorter route.

Second reading changed only this report: no repair of the Lean proof or DAG was needed.
Closed one original hole, added zero holes; the existing bound lemma stays proved.
