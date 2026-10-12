## What changed

Replaced the sole sorry in
`AlgebraicGeometry.Etale.etale_limit_cohomology_affine_comparison` by an
assembly proving that the comparison from the filtered group colimit is
bijective. The existing signature and docstring are byte-for-byte unchanged.
Injectivity uses the new affine eventual-zero lemma, hH, hB and the specified
isomorphisms. Surjectivity uses the existing general theorem
`AlgebraicGeometry.Etale.etale_limit_cohomology_class_descent` directly.
A bijective homomorphism transports the standard colimit structure to B.
The forgetful functor's filtered-colimit preservation is lowered from u+1 to u.

Added EtaleLimitAffineEventualZero and its node, isolating just the geometric
kernel half. Its source-backed proof plan retains affine-site strictification,
affine restriction equivalence, unit-compatible cohomology transport and a
cofinal tail. No definitions or existing public signatures changed. All
witness choices in the main module occur inside a proof of a proposition.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.etale_limit_cohomology_affine_comparison`
(node lem-weil-pbc-etale-limit-cohomology-affine-comparison).
No sorry remains in the item module.

Added and left as exactly `:= by sorry`:
`AlgebraicGeometry.Etale.etale_limit_affine_eventual_zero`
(node lem-weil-pbc-etale-limit-affine-eventual-zero).

This is a decomposition: one upper hole closed and one lower hole added,
net zero holes closed in this delivery. The main theorem still depends on
open statements through sorryAx; geometric continuity is not completed.
The lower statement asserts only eventual detection of a zero class, not
surjectivity or the colimit universal property. The first worker's redundant
new class-descent hole and node were removed in second reading, using the
existing general class-descent theorem instead.

## No longer needed

Removed the item's original direct proof imports:
- Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit
- Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
- Sheaf.CategoryTheory.CohomologyColimitSites
- Sheaf.AlgebraicGeometry.FullAffineEtaleTopos
- Sheaf.AlgebraicGeometry.LimitAffineTransition
- Sheaf.CategoryTheory.ColimitSites
- WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

The first two and the other geometric dependencies remain needed by the new
kernel lemma's source route. No claim is made that these modules are globally
unreachable. The generic assembly module CohomologyColimitSites and its node
lem-weil-pbc-cohomology-colimit-of-sites are bypassed; its eventual-vanishing
half remains used by the lower proof plan.

Every old proof_deps entry other than the retained def-weil-pbc-category-colimit
is removed from the parent's direct proof dependencies. The lower node retains
lem-weil-pbc-limit-affine-transition, lem-weil-pbc-affine-etale-site-colimit,
lem-weil-pbc-colimit-of-sites, lem-weil-pbc-affine-etale-site-topos,
def-weil-pbc-direct-image, def-weil-pbc-inverse-image,
lem-weil-pbc-inverse-image-composition,
lem-weil-pbc-left-adjoint-preserves-colimits,
lem-weil-pbc-cohomology-pullback-functorial,
def-weil-pbc-cohomology-pullback, def-weil-pbc-etale-cohomology and
lem-weil-pbc-colimit-initial-full-subcategory.

Removed the first worker's new module EtaleLimitAffineClassDescent and its node
lem-weil-pbc-etale-limit-affine-class-descent: the library already proves the
needed existence assertion with supplied H and B. Removed the redundant proof
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono, already available
through the import closure. Mathlib.CategoryTheory.Filtered.Final was tried by
the first worker and removed. No realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement found. The existing affine-site presentation alone does
not construct the required site/sheaf/Ext/universe transport data. That kernel
bridge remains in the named intermediate statement. LeanFinder and local
searches give structure-sheaf section limit results, not arbitrary abelian
etale cohomology continuity. The first worker's LeanSearch query returned
Internal Server Error and is recorded without an absence verdict.

The first worker missed the existing general class-descent theorem. Its
induction uses degree-zero descent and a connecting ladder independently of
this affine comparison. Second reading applies it directly to the already
supplied H, eH, hH, B, eB, hB, eliminating a needless split-off existence hole.
The general eventual-vanishing theorem instead imports this affine comparison
through qcqs gluing and cannot be used here without circularity.

## New nodes

lem-weil-pbc-etale-limit-affine-eventual-zero:
lean/Sheaf/AlgebraicGeometry/EtaleLimitAffineEventualZero.lean.
The kernel half of affine continuity, with a source-backed proof plan using
the existing site-level eventual-vanishing theorem. It inherits the parent's
chapter, unit and blueprint ancestry. No change records: no existing public
signature or definition changed.

## Second reading by E3

1. Compared the main module and parent node with the repository by diff.
   The existing theorem signature and docstring are byte-for-byte unchanged.
   Only its proof, private imports and permitted node proof fields change.
   No target, definition, hypothesis, conclusion or universe changed. Passes.

2. Compiled the first worker's three modules in import order, without errors
   or warnings. Read the kernel assembly: hB gives hleg, hH gives htrans;
   a representative killed by the comparison becomes zero at a later stage;
   injectivity of eH then kills its H-transition. Class descent gives
   surjectivity. A bijective group homomorphism transports the colimit to B.
   Printed axioms of the original three declarations: propext, Classical.choice,
   Quot.sound and sorryAx only. The final delivery is recompiled and its
   declarations axiom-probed by deliver3.py. No hollow definitions or forbidden
   constructs. Passes as a conditional assembly, not an axiom-free proof.

3. Read Stacks 09YQ, 0EYL, 04HR, 09YP and 0739 online. The 09YQ hypotheses
   are directedness, qcqs stages, affine transitions and compatible arbitrary
   abelian sheaves; torsion and constructibility are unnecessary. The affine
   restriction belongs to this existing item. The new kernel assertion is
   strictly a part of the comparison, not a restatement. For p=0 it detects
   zero sections; for x=0 the identity kills x; a singleton reduces to
   injectivity of the single-stage identification; empty schemes and zero
   sheaves have zero groups. The docstring follows the smaller-degree
   connecting argument of 09YP/0739. Strictification addresses the non-strict
   base-change issue discussed in 0EYL's comments. Repeated LeanFinder with
   a new representative/kernel query and grep on Mathlib AlgebraicGeometry:
   structure-sheaf section results only. Searched lean/Sheaf and upstream
   EtaleCohomology. Found the general class-descent route described above,
   removed the redundant new existence lemma, and kept only the kernel hole.
   The site-level kernel transport requires constructions not closable in
   a few minutes. Passes as an honest decomposition.

4. Checked sk-thm-p1.json realized: this parent and the bypassed generic
   site assembly are below the unit's recorded steps. None of its realized
   statements or steps is removed. The geometric kernel route retains affine
   presentation, affine restriction and the tail. Replaced the redundant
   existence half with the shorter existing theorem. Expanded No longer
   needed to list all eight original imports actually removed, and accounted
   for every old proof_deps. Removed redundant ConcreteCategory.EpiMono.
   Passes; globally unreachable modules are not claimed.

5. Checked new node chapter/unit/ancestry, source, three search records,
   created/status and Lean signature. Parent proof_deps equals the union
   of proof-step uses and matches the final representative/kernel/iso assembly.
   The lower node cites the site-level eventual-vanishing half and retains
   geometric transport dependencies. Repaired stale hH/hB references in
   its proof plan: those parameters occur only in the parent. Added the
   blueprint identifier to its module docstring. Passes.

Second reading changed the surjectivity proof to the existing class-descent
lemma, removed the redundant new existence module/node, removed a redundant
proof import, completed pruning reports, and repaired lower-node parameter
names and its module blueprint marker. Existing statements were preserved.
