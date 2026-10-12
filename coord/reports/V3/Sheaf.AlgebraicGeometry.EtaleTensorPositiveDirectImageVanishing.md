## What changed

The unchanged target `AlgebraicGeometry.Scheme.Modules.etaleTensorPositiveDirectImageVanishing`
reduces to affine-open object-cohomology vanishing and the generic direct-image criterion
`AlgebraicGeometry.Scheme.Modules.positiveDirectImageOfObjectAcyclic`. The latter is now
proved using the existing `CategoryTheory.objectCohomologyPresheaf_resolution`, local
injectivity of the zero map, exact additive sheafification, and `isoRightDerivedObj`.
The two universe-transport helpers are proved private lemmas, following the existing
`PushedResolutionPositiveHomologyZero` argument. No data definition was added or changed.

The proposed object-cohomology lemma was false on arbitrary opens. Its new, unlanded
interface now assumes `IsAffineOpen U`, as does the hypothesis of the generic criterion.
All existing signatures and declaration visibility are byte-for-byte unchanged. The
original target node now records this actual two-step reduction. Old private proof imports
move to the remaining affine lemma; the obsolete sheafified-presheaf theorem import is
removed. A private `GrothendieckCategory.HasExt` import supplies the proof's Ext instance.
The proof-only public import of `SheafCohomology.Basic` is removed from the target.

Import change record: `coord/changes/etaleTensorPositiveDirectImageVanishing-imports.md`.

## Proved and sorry left

Closed original hole:
`AlgebraicGeometry.Scheme.Modules.etaleTensorPositiveDirectImageVanishing`
(node `lem-sc-etale-tensor-positive-direct-image-vanishing`). Its proof is complete as a
reduction, but its axiom closure still contains `sorryAx` through the following affine lemma.

New proved declaration:
`AlgebraicGeometry.Scheme.Modules.positiveDirectImageOfObjectAcyclic`
(node `lem-sc-etale-positive-direct-image-object-acyclic`). Its axiom check contains only
`propext`, `Classical.choice`, and `Quot.sound`; neither it nor its private helpers has a hole.

Added and sole remaining local hole:
`AlgebraicGeometry.Scheme.Modules.etaleTensorPositiveObjectCohomology`
(node `lem-sc-etale-tensor-positive-object-cohomology`), restricted to affine opens.
Its entire proof is `by sorry`, with a source and complete natural-language proof in its
docstring. There is no sorry in the item's own module or inside any definition.

This is a decomposition: one original hole closed and one genuinely smaller hole added,
net zero local holes against the repository baseline. Compared with the first worker's
sandbox, the second reading closes the generic criterion hole and corrects the false
all-open hole. No ledger-wide progress or global pruning count is asserted here.

## No longer needed

The target's six original direct `proof_deps` are all replaced by the two new nodes:

- `lem-weil-pbc-cohomology-over-object-localization`: now a dependency of the affine lemma.
- `lem-weil-pbc-etale-open-object-cohomology-natural`: now a dependency of the affine lemma.
- `lem-sc-etale-ulift-injective-resolution`: now a dependency of the affine lemma.
- `lem-sc-etale-affine-qcoherent`: now a dependency of the affine lemma.
- `lem-sc-etale-qcoherent-presheaf-functorial`: now a dependency of the affine lemma.
- `lem-weil-pbc-site-higher-direct-image-sheafified-presheaf`: no longer needed by this
  argument. Exact sheafification, the existing object-resolution comparison, and
  `isoRightDerivedObj` prove this step directly in the new generic criterion.

Removed direct proof imports from the target:

- `Sheaf.CategoryTheory.Sites.CohomologyOverObjectLocalization`
- `Sheaf.AlgebraicGeometry.EtaleOpenObjectCohomologyNatural`
- `Sheaf.AlgebraicGeometry.EtaleULiftInjectiveResolution`
- `Sheaf.AlgebraicGeometry.EtaleAffineQcoherent`
- `Sheaf.Paper.SiteHigherDirectImageSheafifiedPresheaf`
- `Sheaf.AlgebraicGeometry.EtaleAffineQcoherentULift`
- `Sheaf.AlgebraicGeometry.EtaleTensorSections`

Also removed the target's public `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`
import; the direct importer already publicly imports it itself. Most modules above remain
reachable through the affine lemma. Global target-closure module pruning is for the ledger
to determine; no entire library module is claimed to be pruned by this report.

## Where the brief, the DAG or earlier work was wrong

The first worker inferred global positive object-cohomology vanishing on every open from
vanishing on affine opens. An affine cover only makes these cohomology-presheaf sections
locally zero; positive cohomology on a non-affine open can be nonzero. For example take
X = P^1 over a field, U = X, F = O(-2), and n = 0: the standard two-chart Cech calculation
gives H^1(X,F) equal to the field. Etale cohomology is the same by Stacks 03P2, contradicting
the originally proposed all-open lemma. This erroneous proposed statement was never landed
and is removed from both the new Lean signature and its new node.

The original target and its original docstring already used the correct local-vanishing
argument, and are unchanged. The original claim that no dependency was removed was also
incorrect after the new generic proof. The new lemma docstrings now cite the source and
explain localization, affine acyclicity, coefficient transport, and sheafification separately.

The generic theorem `pushed_resolution_positive_homology_isZero` is a related existing
proved argument, but is declared for `Scheme.{u+1}` and all positive degrees. The target
requires arbitrary `Scheme.{u}` and only one degree. The new criterion uses its generic
object-resolution dependency and the same elementary universe-transport reasoning, with
an affine-basis hypothesis; it neither restates the item nor introduces another open
sheafification statement.

## New nodes

`lem-sc-etale-tensor-positive-object-cohomology` states only affine-open acyclicity,
with the original localization/affine dependencies and the existing open quasi-coherent
identification. It is strictly the geometric part of the original argument and remains open.

`lem-sc-etale-positive-direct-image-object-acyclic` is the proved generic affine-basis
criterion, for any etale abelian sheaf. Its only non-elementary proof dependency is
`lem-weil-pbc-object-cohomology-presheaf-resolution`; the node records the actual
local-injectivity, universe transport, homology, sheafification, and resolution steps.

## Second reading by V3

1. Compared the original and delivered target with `diff` and checked its signature bytes
   explicitly. Verdict: the existing theorem's signature and visibility are unchanged;
   there are no altered definitions, new hypotheses on the existing theorem, weakened
   conclusions, or forced adaptations. Only unlanded new lemma interfaces were corrected.
2. Read the complete proofs and compiled all delivered modules through `lcompile.py`.
   Verdict: the generic criterion is a real proof with standard axioms only; the target
   depends on its single named affine lemma hole. No axiom, unsafe, opaque, implemented_by,
   extern, hollow definition, or arbitrary data from an unproved existence statement.
3. Tested the proposed lemmas mathematically at the empty open, degree n=0, zero sheaf,
   affine opens, and non-affine opens. Verdict: the original all-open statement was false
   and has been corrected; the affine statement and generic criterion are true and exactly
   sufficient. Repeated LeanFinder, Loogle, Mathlib grep, and library searches using
   different queries. Reused the generic object-resolution theorem. Each new node has its
   exact signature and source; the sole sorry has a complete docstring proof. This is a
   geometric/formal reduction, not a renamed copy of the original theorem.
4. Reviewed the shorter routes and imports. Verdict: the formal sheafification step can
   be proved with existing library/Mathlib tools and is now closed; only affine localization
   remains. The generic existing pushed-resolution theorem has a successor-universe
   interface, so it cannot directly replace this arbitrary-universe criterion. All six
   original direct proof dependencies are accounted for above. The unit `sk-prop-cd` has
   empty `realized.statement` and `realized.steps`; no realized unit route is bypassed.
   Its quasi-coherent etale comparison support still follows localization and affine
   acyclicity. The sole direct importer is checked against the delivered overlay.
5. Compared all node records with the Lean. Verdict: the existing node has only proof,
   proof_deps and proof_origin changed; the two new nodes have the required creation,
   blueprint, search, source and Lean fields. Their proof_deps equal the union of step uses.
   The generic criterion's dependency is the resolution comparison it actually applies.

Validation: all three delivered modules compile cleanly in import order. Scratch
`#print axioms` checks give the standard three axioms for the generic criterion and
those three plus `sorryAx` for the target and its affine lemma. The unchanged direct
importer compiles against the delivered overlay in 45.1 seconds, below the file limit.

Second reading changed: corrected all-open acyclicity to affine-open acyclicity; proved
`positiveDirectImageOfObjectAcyclic`; supplied complete source/docstring proofs; pruned
obsolete direct imports; repaired the parent and new-node metadata and this report.
