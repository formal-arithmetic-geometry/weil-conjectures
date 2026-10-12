## What changed

Replaced the sorry in AlgebraicGeometry.etaleSetStageSheaf_isColimit with a complete
Lean proof from two separate local comparison assertions. Its signature, public
imports and original docstring are unchanged. The proof forms the presheaf colimit,
sheafifies its cocone, and proves that its induced map to the supplied cocone point
is an isomorphism. The essential glue is the coprojection calculation identifying
the presheaf comparison with the sheafification unit followed by that map.
Mathlib then transfers local injectivity and local surjectivity through the unit,
and IsColimit.ofPointIso proves the original universal property.

Added two modules, one theorem in each: EtaleSetStagePresheafLocallyInjective and
EtaleSetStagePresheafLocallySurjective. They separate the equality and existence
portions of the affine-site section argument, respectively. Neither asserts an
isomorphism, a colimit universal property, or the conjunction of those two local
properties. Both have exact mathematical statements, sources, numbered proof
instructions, and new DAG nodes. Updated the original node's proof route.

All three modules compiled together without errors or warnings through lcompile.py.
Each compiled in approximately five seconds. No existing definition, theorem
signature, visibility, target, or module held by another group was changed.

## Proved and sorry left

Original hole closed by decomposition:
AlgebraicGeometry.etaleSetStageSheaf_isColimit
(lem-weil-pbc-sets-stage-sheaf-colimit). Its proof has no sorry.

Two holes added, each exactly the whole proof of its public named theorem:

- AlgebraicGeometry.etaleSetStagePresheaf_locallyInjective
  (lem-weil-pbc-sets-stage-presheaf-locally-injective).
- AlgebraicGeometry.etaleSetStagePresheaf_locallySurjective
  (lem-weil-pbc-sets-stage-presheaf-locally-surjective).

There are no other delivered sorries. This is a decomposition, not a complete
sorry-free mathematical proof: one original hole is replaced by two strictly
separate local assertions. The delivered set has net holes closed minus added = -1;
no claim of positive sorry-ledger progress is made.

Edge cases checked mathematically: the indexing tail is nonempty and directed;
empty affine objects and empty limit objects use the empty covering and the sheaf
axiom, not a nonempty section-set assumption. The coefficient universe stays
Type (u + 1). Local statements permit covering sieves and do not assume that
evaluation of arbitrary sheaf colimits preserves colimits. No data are chosen
from a theorem of mere existence: the only new objects used in the proof are
Mathlib's presheaf colimit, its sheafification and their universal maps.

## No longer needed

Removed from the original module's direct proof imports:
Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit and
Sheaf.AlgebraicGeometry.AffineEtaleInverseImageComparison. They are relocated into
both local comparison modules, where their geometric and unit-transport arguments
remain needed. Added the two local comparison imports and the Mathlib Sites.Limits
and Sites.LocallyBijective proof imports to the original module.

The original five planned geometric/site nodes remain needed below the new local
nodes: lem-weil-pbc-affine-etale-site-colimit,
lem-weil-pbc-sets-affine-etale-inverse-image-comparison,
lem-weil-pbc-affine-etale-site-topos, lem-weil-pbc-colimit-of-sites, and
lem-weil-pbc-sets-etale-inverse-image-composition-units. Thus no entire geometric
node or module is pruned. The final universal-property construction and gluing
require no new holed theorem: Mathlib's sheafification and local-isomorphism APIs
replace that portion of the plan. The unit sk-thm-iff and all its realized nodes
are preserved.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The broad original proof step did not provide a
ready-to-apply Lean bridge from its site presentation to the stage push-pull
comparison. In particular ColimitSites uses Cat.{u,u} and Type u, whereas the
full-affine site presentation uses Cat.{u,u+1} and this item uses Type (u+1).
The new local statements isolate the transport and section argument instead of
changing any of those existing signatures or importing a cyclic theorem.

The apparent shorter route through EtaleSetSectionContinuity is circular:
import_direction.py reports that it already reaches this module. The existing
affine eventual-equality theorem also relies on the affine section colimit,
which relies on this module. These results were not imported. LeanSearch returned
an Internal Server Error; this is recorded as unavailable, not as evidence of
absence. LeanFinder, Loogle, Mathlib/source grep and blueprint searches found the
generic tools but no directly applicable geometric comparison.

The repository does not contain the cited Stacks tex files on this machine.
The relevant source paragraphs were read from the available local source copy,
including sites.tex lemma-compute-pullback-to-limit and etale-cohomology.tex
lemma-colimit-affine-sites. The existing project literature paths are retained
in the citations; no source checkout was changed.

## New nodes

lem-weil-pbc-sets-stage-presheaf-locally-injective states the equality portion of
the presheaf comparison: equal images become equal on a covering sieve. Its source
is Sites 0A35, transported using the affine-site and unit comparison lemmas. The
node includes the same-stage presentation, finite witness descent, covering
separatedness and empty-cover cases needed to prove it independently.

lem-weil-pbc-sets-stage-presheaf-locally-surjective states the existence portion:
sections of the limit push-pull sheaf lift locally to the presheaf colimit. Its
source is the existence portion of Sites 0A35, applied to affine etale sites via
09YQ. The node describes finite local representative descent, overlap equations,
stage gluing, and insertion through a presheaf coprojection. Three search kinds
are recorded for each new node. No change record is needed because no existing
statement or definition was changed.

## Second reading by Q3

Independent second reader; I did not write this proof.

1. **Interface unchanged — pass.** Read the complete diff of the only existing
   delivered module against the repository. Only plain imports and the theorem's
   proof changed. Compared the text from `theorem etaleSetStageSheaf_isColimit`
   through its `:=` byte for byte: identical. The public imports and original
   docstring are also identical. The other two modules and their declarations
   are new; no existing data definition, target or downstream module is edited.
   Read the landed section-comparison relocation and affine-lift elaboration
   change records; neither requires an adaptation here.

2. **Formal reduction — pass, with two deferred mathematical assertions.**
   Independently compiled all three files together with lcompile.py. All compiled
   without errors or warnings. Inspected every delivered declaration: the only
   two sorries are the entire named local-comparison theorems listed above;
   there are no definitions or forbidden declarations/attributes in this set.
   A scratch import file printed axioms of all three theorems: each has exactly
   propext, Classical.choice, Quot.sound and sorryAx. Removed the scratch file.
   In the upper proof, hH is the sheafification of a genuine presheaf colimit.
   The coprojection calculation proves that its unit followed by q is precisely
   the supplied comparison a. Local surjectivity of the unit transfers local
   injectivity of a to q; local surjectivity of a transfers directly to q.
   Mathlib then makes q an isomorphism, and ofPointIso gives the requested K.
   No geometric property is inferred merely from the existence of a colimit,
   and no arbitrary witness is extracted from a holed existence theorem.

3. **Split statements — pass as a decomposition.** Read both statements,
   docstrings and new nodes. They retain the original geometric hypotheses and
   component equations but ask separately for equality and existence on covering
   sieves; neither alone states the original colimit property. Their conjunction
   is assembled by an actual sheafification proof. Read Sites
   lemma-compute-pullback-to-limit and its displayed formula, and Etale Cohomology
   lemma-colimit-affine-sites, in the available Stacks source copy under
   /home/ubuntu/work-bp/sheaf/literature/stacks-project/. The formula is
   sectionwise on a base-changed affine object; its equality and existence parts
   imply the weaker local properties stated here. Finite covering descent and
   finite overlap equations justify the common-stage gluing in the docstrings.
   In particular, covers over a stage or limit need not descend to the fixed
   base: the argument glues at a later stage, producing a section on the base
   change of W. Checked the singleton index (identity comparison), arbitrary
   directed tails (nonempty and common later stages), empty affine test objects
   (empty-cover sheaf condition), and empty limit (finite covering descent).
   None requires a nonempty coefficient sheaf. Independent LeanFinder query
   "local monomorphism epimorphism inverse image sheaves cofiltered scheme limit
   section comparison", Loogle query CategoryTheory.Presheaf.IsLocallyInjective,
   and grep query "compute.*pullback|inverseImage.*section|stage.*comparison"
   returned generic tools or structure-sheaf results, not this comparison.
   Also searched both project source roots. The abelian SectionContinuity
   theorem has different coefficients, and the set-section lifting/equality
   results import this item, so they cannot close these holes without a cycle.
   Neither geometric transport proof is a few-minute application of the
   available declarations, whose site/coefficient universes differ.

4. **Route and pruning — pass.** The formal sheafification portion uses the
   existing Mathlib APIs directly, with proof-only imports written as plain
   imports. FullAffineEtaleTopos is needed in the signatures for the inclusion's
   continuity instance. The new deferred modules retain the geometric imports
   for their stated proof plans. All five old direct proof dependencies are
   named under No longer needed: they leave the upper node's direct dependency
   list and remain below the new local nodes. No whole module is pruned.
   Read dag/units/sk-thm-iff.json: its realized statement and proof step remain
   lemma-weil-pbc-property-iff-acyclicity; this reduction lies strictly below
   that unit and changes neither its route nor its realized records.

5. **DAG agreement — pass.** Compared each new Lean signature verbatim with
   its node's lean.statement. For each delivered node, proof_deps is exactly
   the union of its steps' uses. The upper node records the two local assertions,
   the coprojection factorization and the Mathlib local-isomorphism criterion;
   its cited local-bijection node records that exact Mathlib declaration. Each
   new node has its source, full proof plan, searches, origin, creation record,
   blueprint ancestry, chapter, unit and Lean location. Sources and proof plans
   match the corresponding docstrings.

Changes by this reader: added this independent review and the explicit direct
pruning clarification. No Lean or node repair was warranted. The original hole
is closed only by decomposition; both new local-comparison holes remain, and
this delivery has no positive net sorry-ledger progress (one closed, two added).
