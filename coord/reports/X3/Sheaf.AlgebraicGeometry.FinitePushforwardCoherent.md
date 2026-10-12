## What changed

Proved both declarations of `Sheaf.AlgebraicGeometry.FinitePushforwardCoherent`,
with their signatures unchanged. Added a proved private helper `isFiniteType_over`
that restricts finite local generating families through the slice sites. The main
proof follows Stacks 01Y6: finite coordinate algebras, finite module sections,
restriction of scalars, quasi-coherent pushforward, and the locally Noetherian
coherence criterion. The companion uses Mathlib's locally finite-type Noetherian
source theorem and the source library's invertible-unit and finite-presentation
instances. Updated the existing node's proof, proof_deps and proof_origin.

Added proof imports:
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism`

The file compiles locally. The slice-generator construction needs higher
elaboration heartbeat limits; a comment explains this, and the wall time remains
under 60 seconds. No target, definition, or public theorem signature changed.

## Proved and sorry left

Closed two original holes:
- `AlgebraicGeometry.Scheme.Modules.isCoherent_pushforward_of_isFinite`
- `AlgebraicGeometry.Scheme.Modules.isCoherent_unit_of_finite_to_locallyNoetherian`

Both belong to `lem-weil-pbc-finite-pushforward-coherent`. Zero sorries remain
in the delivered module; zero holes were added or split off. The private
restriction helper is completely proved. This is a proof from existing
statements, not a claim that all reachable dependencies are sorry-free:
`AlgebraicGeometry.Scheme.Modules.quasicoherent_finite_type_affine`
(node `lem-weil-pbc-quasi-coherent-finite-type-affine`) remains an existing
unproved dependency. The coherence criterion and affine-pushforward theorem
used here have complete proofs in the sources.

## No longer needed

The second reading also removed the redundant proof import
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`;
its declarations remain available through an existing upstream public import.

Removed proof imports:
- `Sheaf.AlgebraicGeometry.AffinePushforwardBaseChange`
- `Sheaf.AlgebraicGeometry.TensorPullback`

The proof no longer needs the node
`lem-weil-pbc-affine-pushforward-base-change`, its affine tensor formula,
algebra compatibility or composition statements. Its degree-zero assertion is
supplied by the already proved `lem-pc-affine-morphism-hi`. The tensor-pullback
module was unused; its node `def-pc-module-pullback` is also removed from
`proof_deps` (its unchanged occurrence in `stmt_deps` describes the statement). No claim is made that these modules are globally unreachable;
other consumers may still need them.

Removed explicit proof dependencies `def-weil-finitely-generated-module`
(the existing affine criterion already supplies Module.Finite) and
`lem-weil-pbc-finite-algebra-noetherian` (the Mathlib scheme-level theorem
supplies local Noetherianity directly). No finite-algebra Noetherian proof or
base-change theory needs to be developed for this delivery. The unit's realized
statement and steps are preserved: this auxiliary node is not itself listed in
`dag/units/sk-thm-p1.json`'s realized fields.

## Where the brief, the DAG or earlier work was wrong

The original plan routed degree-zero quasi-coherence through the much stronger
unproved affine base-change theorem. The source library already proves exactly
the needed preservation result. It also supplies the scheme-level Noetherian
source theorem, making the explicit finite-algebra Noetherian covering argument
unnecessary. These are route simplifications, not statement corrections.

Restriction of finite type had no directly usable named instance in the visible
API; the private helper proves it by transporting finite generators, rather than
adding an unproved intermediate theorem. Lean's default elaboration of several
structure constructors selected universe zero, so the proof uses explicit
universes and parameters where needed.

The source texts read were Stacks `coherent.tex`, lemma-finite-pushforward-coherent
(01Y6), and lemma-coherent-Noetherian (01XZ), available in the local read-only
Stacks review copy. Searches ran through the launcher: LeanFinder for finite
coherent direct images, Loogle for Module.Finite.trans, and grep for finite-type
and coherence criteria, followed by direct source searches. The proof uses
`lem-pc-affine-morphism-hi` as an already proved tool from another unit; no open
unit route is bypassed.


## Second reading by X3

1. **Visible declarations:** compared the complete module and node with the repository.
   Both existing theorem signatures are byte-for-byte unchanged. No definitions,
   target statements, or other modules change. Verdict: pass.
2. **Proof and trust:** compiled the original module without warnings (30.8 seconds),
   then compiled a scratch copy with the redundant import removed and explicit
   `#print axioms` for both public theorems and the private restriction helper.
   The helper uses only `propext`, `Classical.choice`, and `Quot.sound`.
   Both public theorems additionally use `sorryAx` through existing imports;
   these are local holes closed, not axiom-free targets. There are no sorries,
   hollow definitions, axioms, unsafe code, opaque declarations, externs, or
   implementation overrides in the delivered module. The finite-generator choices
   occur inside a proved theorem, not inside a definition. Verdict: pass.
3. **Split statements:** none were added. Read the restriction construction:
   the pullback covering covers each slice object, and each generating family keeps
   its finite index set. Empty opens, zero modules, and identity finite maps cause
   no extra assumptions. Independent LeanFinder, Loogle, and grep searches for
   finite type under restriction found the generating-data API, but no existing
   restriction theorem replacing the helper. Verdict: pass; zero split-off holes.
4. **Route and pruning:** read the affine criterion, the proved source affine
   pushforward theorem, and the locally Noetherian coherence proof. The proof
   uses scalar restriction and `Module.Finite.trans` directly. Checked
   `dag/units/sk-thm-p1.json`: this auxiliary node is not a realized unit step,
   and the unit's realized route is unchanged. Removed the redundant proof import
   `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`,
   already publicly available through `QuasicoherentKernel`; the scratch copy
   compiled without it. All four removed old proof dependencies are reported:
   `def-weil-finitely-generated-module`,
   `lem-weil-pbc-affine-pushforward-base-change`,
   `lem-weil-pbc-finite-algebra-noetherian`, and `def-pc-module-pullback`.
   Verdict: pass after pruning correction.
5. **DAG agreement:** read each retained dependency's statement and Lean/Mathlib
   record. The node's proof follows the actual construction and its `proof_deps`
   equals the union of step dependencies. Only `proof`, `proof_deps`, and
   `proof_origin` differ from the repository node. Removed the stale
   `def-pc-module-pullback` proof dependency and its step citation: no declaration
   of `TensorPullback` is used. No new nodes or change records are needed.
   Verdict: pass after metadata correction.

Second reading changed only the redundant private import, the stale tensor-pullback
proof dependency, and this report. Both original proofs were retained.
