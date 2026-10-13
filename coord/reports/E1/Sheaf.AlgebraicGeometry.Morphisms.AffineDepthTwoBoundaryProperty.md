## What changed

Repair of return X-99112: replaced the duplicated private local-depth equality
helper by `ideal_depth_le_of_equiv_of_le`, a genuine generalization to arbitrary
ideals I ≤ J, commutative rings without a local-ring assumption, and modules in
independent universes. It transports a depth lower bound directly; the boundary
proof specializes both ideals to the maximal ideal and uses the inverse stalk
equivalence. The existing `depth_equiv` in DepthTwoAffineFiniteQuotientDepth is
private and cannot be reused through an ordinary import. No other existing
module is changed by this repair. All public signatures stay as in the reviewed
delivery. A fresh independent second reading is required for this repaired proof.

Repaired reviewer X-7ea0b's review point 4 structurally. The false arbitrary coherent-H
assertion is replaced by the boundary depth assertion for the associated sheaf of the
actual finite A-module `Hom_A(Hom_A(M,A),A)`. The owned theorem is proved by comparing
stalks with local double duals, applying the local dual-depth theorem, and transporting
finiteness and depth through a linear equivalence. Updated its node's statement,
`lean.statement`, proof, proof dependencies, proof origin and statement-change record.

Added `Sheaf.RingTheory.DualDepthTwo`: a direct regular-pair proof of the local dual-depth
bound, including pointwise division through the inverse of an injective multiplication
map and the zero-dual case. Added `AffineDoubleDualStalk` for localization of both duals.
Added `AffineDoubleDualRestriction` for preservation of a finite locally free restriction;
this geometric comparison is the remaining open step, with its source and proof in words.

Forced adaptation of `AffineDepthTwoLocallyFreeModel`: retain the coherent-extension core
as an initial input, set M to its actual global-section module, construct D=M** and H=tilde D,
prove finiteness of both duals by Noetherianity, use the tilde global-section isomorphism
and finite-presentation API to prove finite affine sections, and establish the restriction
isomorphism before applying the corrected helper. Its existing theorem signature and
visibility are unchanged. The parent's node now follows this construction.

No target declaration, definition, axiom or arbitrary witness-based data definition changed.
The change record is `coord/changes/affine_depth_two_boundary_property.md`.

## Proved and sorry left

Owned hole closed: `AlgebraicGeometry.Scheme.affine_depth_two_boundary_property`
(node `new-affine-depth-two-boundary-property`), 1 of 1, for its corrected true statement.
This is a statement correction with a complete proof of the corrected assertion, not a
proof of the false former assertion.

Also proved: `IsLocalRing.dual_depth_ge_two` (node `new-local-dual-depth-two`) and
`AlgebraicGeometry.Scheme.affine_double_dual_stalk`
(node `new-affine-double-dual-stalk`), including their private helpers.

The unchanged parent `AlgebraicGeometry.Scheme.exists_affine_depth_two_locally_free_model`
has a complete combining proof from the corrected boundary helper, the existing extension
core and the new restriction comparison. The extension core already contains a sorry and
is not changed or counted as a newly added hole.

New hole: `AlgebraicGeometry.Scheme.affine_double_dual_restriction`
(node `new-affine-double-dual-restriction`), exactly `:= by sorry` in its own module.
It asserts only preservation of the finite locally free restriction, with no boundary
depth assertion. Thus 1 lower hole is split off. No sorry remains inside the owned theorem
or the forced caller's combining proof. The delivery's closed-minus-added count is 1-1=0;
the structural truth repair and the proved local algebra/stalk comparison are not claimed
as an increase in that net count.

Edge cases: the zero module and zero dual are allowed; the local proof assigns infinite
depth to the zero dual. The spectrum of the zero ring is empty. W empty has no restriction
points, and W equal to the whole spectrum has no boundary points. The old counterexample
M=A/(x) has zero first dual, so its actual double dual has zero stalk and infinite depth,
which is consistent with the corrected theorem. Neither integrality nor normality is added.

## No longer needed

Removed the duplicated private `AlgebraicGeometry.Scheme.depth_equiv` from the
owned module. No import of DepthTwoAffineFiniteQuotientDepth is added: its private
helper is inaccessible, and its unrelated quotient argument is unnecessary.
The more general ideal-depth inequality is proved in place; no new hole is added.

Removed the owned module's public import
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`:
the corrected statement no longer takes an arbitrary quasicoherent H or hypotheses about
its affine sections. The actual sheaf is specified by Mathlib's tilde construction.
No pre-existing proof-dependency node or module is pruned from the target closure: the
initial extension core is still needed, and the parent's original depth route remains.
No claim is made that the removed direct import removes its module from the global closure.

Second reading made the owned Mathlib.AlgebraicGeometry.Noetherian import plain,
with public Mathlib.RingTheory.Noetherian.Basic for the signature. It also replaced
Mathlib.AlgebraicGeometry.Noetherian by
Mathlib.RingTheory.Noetherian.Basic in the two new stalk/restriction modules,
and removed redundant plain Basic imports from the stalk module and adapted caller.
These are import cleanups; no additional DAG node or target-closure module is pruned.

## Where the brief, the DAG or earlier work was wrong

The prior second reading missed a word-for-word duplicate of a private helper;
import_prune_check refused the landing. The repair uses the return's explicit
alternative of generalizing in place, rather than renaming the same statement.

The first delivery merely marked the false theorem as disputed. That did not repair its
truth or the caller. The old DAG described a double-dual kernel argument while the Lean
statement quantified over an arbitrary coherent sheaf. The return's example proves the
mismatch: A=k[x,y,z], W=D(x) union D(y), H=tilde(A/(x)); at (x,y), structure depth is two
and H-depth is one. This delivery removes that assertion, rather than attempting to prove it.

Checked the cited Stacks sources: Tag 0583 provides localization of Hom for finitely
presented modules; Tag 01HV(7) identifies associated-sheaf stalks. The precise local Hom
depth source is Tag 0AV5(2), used via 0EBA and 0EBI by 0EY6. Tags 0EBI and 0EBJ themselves
state integral-scheme results; the proved local regular-pair argument avoids imposing
integrality on this caller. The unit's extension-in-depth-two route is preserved.

## Forced adaptations

`Sheaf.AlgebraicGeometry.Morphisms.AffineDepthTwoLocallyFreeModel` is unclaimed in the
repository snapshot. Its original line 80 fails against the corrected helper:

```text
Application type mismatch: The argument H has type (Spec A).Modules
but is expected to have type ModuleCat A
in the application @affine_depth_two_boundary_property A ... W hboundary H.
```

Changed only necessary proof imports and the old proof body (original lines 76-80):
construct the global-section module M and its actual double dual D, prove the resulting
sheaf H quasicoherent and finite on affine opens, transport the initial restriction
isomorphism, establish preservation by double dualization, then apply the helper to M.
Every binder, universe, conclusion, name and visibility of the existing theorem is
unchanged, verified with `stage3_delivery.diff_module` (no statement changes).
The record lists all 132 transitive downstream modules and both direct users; other users
need no adaptation because the parent's signature is unchanged. Its node's proof route
changes but its statement and `lean.statement` do not.

## New nodes

`new-local-dual-depth-two`: the finite local dual-depth theorem, proved directly from
Mathlib regular-sequence, Noetherian-finiteness and Nakayama APIs. No geometric hypothesis.

`new-affine-double-dual-stalk`: the finite-stalk and local-double-dual comparison, using
Mathlib's associated-sheaf and finite-presentation localization-Hom APIs. No depth hypothesis.

`new-affine-double-dual-restriction`: preservation of a finite locally free restriction,
using canonical localization-Hom comparisons and finite free biduality. This is strictly
one part of the model construction, with no boundary depth claim. Its proof remains open.

The statement-change and forced-adaptation record is
`coord/changes/affine_depth_two_boundary_property.md`.

## Second reading by E1

1. Compared every delivered module with the repository versions. Existing declaration signatures are unchanged except for the declared correction of `affine_depth_two_boundary_property`; the forced caller adaptation preserves its interface. Verdict: pass.
2. Compiled all five sandbox modules with `lcompile.py --all`. There are no prohibited commands or hollow definitions. Axiom checks show only `propext`, `Classical.choice`, and `Quot.sound` for the proved declarations. The sole remaining `sorry` is the named `affine_double_dual_restriction` split-off theorem with its DAG node. Verdict: pass.
3. Checked the corrected boundary statement and the three new statements against their source and edge cases (zero module, empty spectrum/open, and whole-spectrum boundary). The corrected theorem is true for the actual finite double dual; the restriction statement is strictly simpler and exactly the remaining geometric comparison. No duplicate existing declarations were found. Verdict: pass.
4. Reviewed the proof route and imports. The local dual-depth proof and stalk comparison are used directly; the private duplicated helper was replaced by the generalized in-place helper. Imports made proof-only are plain imports, and removed imports are recorded above. The unit route through the actual double-dual model is retained. Verdict: pass.
5. Checked all DAG `proof`, `proof_deps`, `proof_origin`, Lean declarations, statement-change data, and the split node against the source. They agree with the code, including the forced adaptation record and the remaining restriction hole. Verdict: pass.

Changed during this second reading: no Lean proof changes were needed. I verified the repaired generalized helper, corrected statement, split-off restriction theorem, imports, DAG metadata, and caller adaptation, and added this review record.

## Forced adaptations

### Sheaf.AlgebraicGeometry.Morphisms.AffineDepthTwoLocallyFreeModel
Original against changed dependencies failed:
```
/tmp/forced-adaptation-jigkuz_i/lean/Sheaf/AlgebraicGeometry/Morphisms/AffineDepthTwoLocallyFreeModel.lean:80:57: error: Application type mismatch: The argument
  H
has type
  (Spec A).Modules
but is expected to have type
  ModuleCat ↑A
in the application
  @affine_depth_two_boundary_property A ?m.152 W hboundary H

(with the modules compiled into /tmp/forced-adaptation-jigkuz_i/.lbuild) [3.6 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
