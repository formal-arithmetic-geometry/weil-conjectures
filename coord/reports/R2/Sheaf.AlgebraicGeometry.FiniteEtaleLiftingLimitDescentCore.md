## What changed

Replaced the sole proof placeholder in
`Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore` with a complete Lean proof
from a compatible henselian G-ring stage. The existing declaration, every binder,
its universe, hypotheses, conclusion, and public import are unchanged.

The proof obtains the stage, installs its ring/henselian/proper instances, and applies
H to its finite etale closed-fibre cover W. It pulls the resulting cover T back along
s:Y -> Z; Mathlib supplies finiteness and etaleness. Two pullback-pasting isomorphisms
and pullback.congrHom identify its closed fibre with the pullback along k of T's
closed fibre. Over.isoMk checks the projection equation, and Over.pullback k transports
H's isomorphism to the original closed fibre. Composition with the stage isomorphism
recovers V as a scheme over that fibre. Iso.refl Y supplies the last witness.

Added the new module `Sheaf.AlgebraicGeometry.FiniteEtaleHenselianGRingStage` for the
preparatory approximation/descent statement only, independent of H. It asserts no
lift over Y and no lift over Z. Its single public theorem has a source, a complete
proof in words, and a new DAG node. Updated the core node's proof, proof_deps, and
proof_origin to the actual argument, removing its circular proof dependency.

Source read: [Stacks Project, Tag 0GS2](https://stacks.math.columbia.edu/tag/0GS2),
proof, General case. The local pione.tex is absent. Read the existing Lean signatures
of proper approximation, affine-transition limits, spreading out, finite/etale stage
descent, pair henselization, the henselization universal property, and G-ring permanence.
These supply the new stage theorem's plan; its missing glue is isolated in that theorem.

Validation: both sandbox modules compile through lcompile.py, the core without a
proof placeholder. deliver3.py --no-push printed OK: local and server compilation
and preflight passed except for the second-reading section reserved for the next
worker. No nonstandard axiom was flagged. Nothing was pushed.

## Proved and sorry left

Proved, from the named preparatory stage theorem:
`AlgebraicGeometry.Scheme.exists_finiteEtale_lift_of_henselianPair_of_gRing_lifting_core`
(node `lem-weil-pbc-finite-etale-lifting-limit-descent-core`). No sorry remains in the
item's module. This is a reduction, not an axiom-free completion of the whole branch.

The delivery adds exactly one sorry:
`AlgebraicGeometry.Scheme.exists_finiteEtale_henselian_gRing_stage`, in
`Sheaf.AlgebraicGeometry.FiniteEtaleHenselianGRingStage`, node
`lem-weil-pbc-finite-etale-henselian-g-ring-stage`. Its proof is exactly `:= by sorry`.
The remaining work is proper approximation, closed-fibre limit identification,
descent of V, and compatible passage to a henselized G-ring stage. Applying H,
constructing the lift, and the final closed-fibre pullback calculation are proved here.

Edge cases checked before stating the new theorem: no nonemptiness or connectedness
is assumed on Y or V, so empty schemes and empty covers are allowed. I=0 causes no
problem: the closed-fibre inclusion is an isomorphism and the same descent applies.
I=top in a henselian pair forces A to be the zero ring by Jacobson containment;
empty proper schemes are still allowed. No Noetherian hypothesis is placed on A.
No cartesian property of the square (s,k,j_Y,j_Z) is claimed or needed: only its
commutativity and the isomorphism of covers over Y_0 are required. B and all schemes
are in universe u; finite-type models and a small presentation of their henselizations
fit in that universe, including u=0. W is a cover of Z_0, not a falsely asserted
already lifted cover of Z. IsProper is used for the new stage g, as H requires.

## No longer needed

Removed the item's private import `Sheaf.AlgebraicGeometry.DescendFinite`: its theorem
is needed by the preparatory stage plan, but the core proof does not invoke it directly.
This module is not claimed to be globally unnecessary; its node remains a proof
dependency of the new stage.

Removed the core node's proof edge to
`lem-weil-pbc-finite-etale-lifting-limit-descent` (module
`Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent`). It is the caller of the core,
not a usable dependency. The caller is not pruned from the project and is not modified.

The new stage's plan needs only
`lem-weil-pbc-henselization-universal-property` to extend the chosen stage map to A;
it does not need `lem-weil-pbc-henselization-colimit` or its module
`Sheaf.RingTheory.HenselizationColimit`. This is a local simplification of the
preparatory plan; the colimit lemma may remain needed elsewhere.

No unit-level node is bypassed: the core and new stage lie below the realized nodes
of sk-thm-p1, whose statement and proof steps stay intact. All other approximation,
spreading-out, finite/etale descent and G-ring steps used by the stage remain in its
DAG dependencies. No other imports or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

The core node's original proof says to apply its parent reduction. But the parent's
Lean proof already calls this core theorem. Following that instruction would create
both a logical dependency cycle and an import cycle. The parent-to-core Lean call
stays unchanged; this delivery replaces the core-to-parent proof edge with a genuine
preparatory stage and writes the formal deduction itself.

The existing extra Nonempty (Y isomorphic to Y) witness is trivial and does not encode
a limit diagram. Its signature is nevertheless preserved exactly, with Iso.refl Y.
The new stage records the actual compatibility equality that the pullback proof uses.

The upstream HenselianFiniteEtale equivalence is not a shortcut: its proof uses
FiniteEtaleLiftingEssentialSurjectivity, which calls the parent reduction and this core.
The G-ring approximation theorem applies only when A is a G-ring, which is not a
hypothesis here; it cannot be applied directly to the arbitrary henselian ring.

LeanSearch was attempted and returned Internal Server Error. No negative search
conclusion is drawn from that service. LeanFinder, Loogle, Mathlib grep, project
search, and whole-blueprint search found no existing compatible-stage theorem.

## New nodes

`lem-weil-pbc-finite-etale-henselian-g-ring-stage`, at
`dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-etale-henselian-g-ring-stage.json`,
states the compatible stage before lifting: B,J,Z,g,s,k,W, commutativity, and the
isomorphism of W pulled back along k with V. It groups steps 1--5 of the parent plan
and the quotient/pullback transport needed to apply H. It has no H hypothesis and
no lift in its conclusion, so it is strictly a preparatory part of the argument.
The core combines it with H and a checked categorical calculation. The node's six
proof steps retain the existing named dependencies. There is no change record,
since no existing statement, definition, or public import changes.

## Second reading by R2

1. **Statements unchanged.** Compared the delivered core module with the repository version: the theorem signature, binders, universes, hypotheses, conclusion, and existing public import are byte-for-byte unchanged. The added stage theorem is a separate preparatory statement and does not alter an existing declaration.

2. **Proof validation.** Compiled both sandbox modules with `lcompile.py --all`; both compile without errors. The core theorem has no `sorry`, and the only remaining `sorry` is the named stage theorem, with its source, proof plan, and DAG node. No forbidden declarations or hollow definitions were added.

3. **New statement review.** The stage theorem states only the compatible henselian G-ring approximation and the closed-fibre cover isomorphism needed by the core. It asserts neither a lift over the original scheme nor a lift over the approximating scheme, so it is strictly weaker than the core target. Edge cases and universe consistency are documented in the report above; no existing Mathlib or library declaration duplicates it.

4. **Pruning and route.** The core proof follows the stage theorem, base-change stability, and pullback pasting. The removed private `DescendFinite` import is not used by the core; the former circular dependency on the parent theorem is removed. The stage node retains the approximation/descent dependencies required by its documented route, and the unit `sk-thm-p1` route remains represented.

5. **DAG agreement.** The core node proof, proof dependencies, and proof origin match the Lean proof. The new stage node contains the required statement, source, proof steps, dependencies, Lean declaration record, and split status.

Changed only the two Lean modules, their two DAG node records, and this report. No theorem statements or definitions were changed; no additional repairs were needed.
