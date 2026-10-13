## What changed

Replaced the hole in `AlgebraicGeometry.affine_finite_free_dual_complex_comparison`
with a reduction through an explicit finite-basis dual comparison. The original
signature, universes, visibility, and public imports are unchanged.

Added `Sheaf.AlgebraicGeometry.AffineFiniteFreeDualNaturality`. Its
`affineBasisSheafIso` constructs the transported associated sheaf identification
from a basis representation, Mathlib's `tildeFinsupp`, and the source library's
`restrictFreeIso`. Its `affineBasisDualIso` constructs the dual identification
from that isomorphism, `homObjFreeUnitIso`, and the dual-basis representation.
Neither definition uses a hole or data chosen from an unproved theorem.

The item's private `signed_dual_iso_of_components` handles the complex argument
for an abstract additive functor. It uses canonical `extendXIso` and
`extend_d_eq`, proves equality of the module and sheaf differential signs,
handles all negative degrees by zero objects (including the boundary from
-1 to 0), and assembles the isomorphism with `isoOfComponents`. The public
proof supplies the constructed isomorphisms and their precomposition naturality.

Updated the parent's proof plan and dependencies to this route. The unit
`sk-thm-picard-duality` has empty realized statement and step lists; this
reduction stays within the parent's local finite free Hom calculation.

## Proved and sorry left

Closed the item's original hole:
`AlgebraicGeometry.affine_finite_free_dual_complex_comparison`
(node `lem-sc-affine-finite-free-dual-complex-comparison`).

Added one hole:
`AlgebraicGeometry.affineBasisDualIso_naturality`
(node `lem-sc-affine-finite-free-dual-naturality`), in its own module. It states
only naturality of the explicit term comparison for a single linear map
between two modules with specified finite bases; it states nothing about
complexes, their extension, differential signs, or a complex isomorphism.
Its proof is exactly `by sorry` and its docstring contains the source and full
coordinate proof.

This is a decomposition: one upper hole closed and one strictly simpler
lower hole added, not a net reduction of the number of holes. There are no
holes in either new definition or the private complex assembly lemma, and
none remains in the item's module.

Edge cases: the construction accepts different finite basis index types,
empty index types, and the zero ring. The proof assumes no boundedness.
Negative dual terms are proved zero separately, so no inference about an
infinite sum is needed.

## No longer needed

No original imports, nodes, or modules are pruned. Both original signed-dual
definition modules remain necessary, and the affine tilde import occurs in
the unchanged statement. The new proof imports only the term comparison
module and the finite free basis support it uses.

No bypass of any unit statement or realized unit step was made.

## Where the brief, the DAG or earlier work was wrong

The original proof plan named only the two signed-dual definitions. Those
supply neither the affine term comparison nor its naturality. The explicit
term comparison is constructed here from closed library isomorphisms;
the missing naturality calculation is now its own named node. The complex
assembly, indexing, and sign argument are proved rather than moved to a
second existence theorem.

The cited Stacks source files were not present in this machine's read-only
literature directory. Read the cited pages directly:
https://stacks.math.columbia.edu/tag/01HV (localized sections and functorial
restriction maps) and https://stacks.math.columbia.edu/tag/0BQZ (local finite
free Hom computation). LeanSearch returned Internal Server Error; LeanFinder,
Loogle, local source searches, and the blueprint search were used. No exact
comparison/naturality theorem was found.

## New nodes

`lem-sc-affine-finite-free-dual-naturality`, in
`dag/nodes/sec-picard-framework/lem-sc-affine-finite-free-dual-naturality.json`,
states precomposition naturality of the constructed finite-basis term
comparisons. Its module is `Sheaf.AlgebraicGeometry.AffineFiniteFreeDualNaturality`.
It inherits the parent's chapter and unit, cites the affine localization and
local Hom sources, records all searches and the elementary matrix calculation,
and names the exact public theorem with its verbatim Lean signature.

No existing statement or definition changed, no forced adaptations, and no
change record is needed.

Validation: `lcompile.py --all` compiled both delivered modules with exit code
0 and no warnings. The final assigned module compiled in 16.3 seconds.
The only delivered `sorry` is the public term-naturality theorem named above.
Every delivered Lean line has at most 100 characters. The original node changes
only `proof`, `proof_deps`, and `proof_origin`.

The final interface diff reports no interface changes and no statement changes.

## Second reading by W3

1. **Interface and accidental changes.** Compared both delivered modules and the
existing repository module byte-for-byte at declaration signatures. The target
statement and all existing declarations are unchanged; only proof bodies and
proof-only imports changed. The added declaration is in a new module and has a
matching DAG node.

2. **Proof validity.** Compiled the sandbox with `lcompile.py --all`; both files
compile without errors or warnings. The target has no `sorry`; the sole remaining
`sorry` is `affineBasisDualIso_naturality`, exactly the named split-off theorem.
No forbidden declarations or hollow definitions occur. The complex assembly is
fully proved; only the explicitly documented naturality calculation remains open.

3. **Split-off statement.** Checked that
`affineBasisDualIso_naturality` is a true, strictly simpler finite-basis
precomposition statement, with complete proof documentation, source citation,
and a corresponding `status: split` node. It is used once per differential and
introduces no complex-level restatement. The edge cases recorded in the report
(empty bases and zero rings) are included in the statement's scope.

4. **Pruning and route.** Checked imports and proof dependencies against the
actual proof. The added `Mathlib.LinearAlgebra.FreeModule.Finite.Basic` import is
proof-only; no unused original import or dependency was removed. The route uses
the explicit basis constructions and the private generic complex assembly, and
keeps the unit route (whose realized lists are empty for this local node).

5. **DAG agreement.** The target node's proof, dependencies, and origin match the
new Lean route. The new naturality node records its exact theorem signature,
source, proof steps, searches, module, and declaration. No statement or
 definition change record is required.

**Changes made during second reading:** none; the delivered proof and DAG passed
all checks as written.
