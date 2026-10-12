## What changed

The existing theorem signature is unchanged. Its proof now constructs the canonical
stage section functor and limit cocone, invokes their affine colimit universal property,
and applies Mathlib's filtered-colimit equality criterion. The returned arrows are
opposed to give exactly the requested arrows in the over category; the transition
maps agree definitionally with the displayed section comparisons.

Added three modules: EtaleStageSectionDiagram (a real functor with proved identity and
composition equations), EtaleStageSectionCocone (a real cocone with proved naturality),
and EtaleAffineSectionColimit (the geometric universal-property step). Each construction
has its own definition node. Only the universal-property theorem remains open.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.etaleSetSectionAffineEventualEquality`.
Added one hole, `AlgebraicGeometry.etaleStageSectionCocone_isColimit`, node
`lem-weil-pbc-affine-section-cocone-colimit`. No other delivered declaration contains
`sorry`. This is a decomposition: one hole closed, one hole added, net zero. The new
hole isolates step 1 of the original plan; the filtered-colimit argument of step 2,
and the actual functor/cocone coherence, are proved.

The colimit theorem is not a renamed eventual-equality assertion: it has no stages j,k,
sections s,t, or equality hypothesis. It asserts the universal property of the whole
specified cocone, including existence of descents, which is the geometric section
presentation used by the original plan. The original conclusion is derived by the
independent generic filtered-colimit equality theorem in a complete Lean proof.

Edge cases checked: I may be a directed preorder rather than a partial order; Mathlib
supplies filteredness for the opposite over category. The upper tail is nonempty because
i₀ belongs to it. No section or affine object is assumed nonempty. On the empty affine
object, section sets are singletons; for a singleton index the canonical cone comparison
is an isomorphism. These are consistent with the new universal-property statement.

## No longer needed

Removed direct proof imports from the original module:
`Sheaf.AlgebraicGeometry.AffineEtaleInverseImageComparison`,
`Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit`,
`Sheaf.AlgebraicGeometry.EtaleSetSectionComparisonLaws`,
`Sheaf.CategoryTheory.ColimitSiteSections`,
`Mathlib.CategoryTheory.Limits.Connected`, and
`Mathlib.CategoryTheory.Sites.Equivalence`,
`Sheaf.AlgebraicGeometry.FullAffineEtaleTopos`, and
`Sheaf.AlgebraicGeometry.LimitAffineTransition`.
All eight original proof-dependency nodes are removed from the item's direct
`proof_deps`: `lem-weil-pbc-affine-etale-site-colimit`,
`lem-weil-pbc-affine-etale-site-topos`,
`lem-weil-pbc-colimit-constant-connected-diagram`,
`lem-weil-pbc-colimit-of-sites-sections`,
`lem-weil-pbc-limit-affine-transition`,
`lem-weil-pbc-sets-affine-etale-inverse-image-comparison`,
`lem-weil-pbc-sets-section-comparison-laws`, and
`lem-weil-pbc-site-equivalence-sheaf-transport`.
They remain dependencies of the new open geometric theorem, whose module now
imports their modules as proof imports. ComparisonLaws also supplies the construction
proofs. None is obsolete, and no module is claimed pruned from target closure.
No unit or chapter route has been bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing `colimitSite_sections_bijective` theorem, advertised as Tag 09YN, concerns
filtered colimits of sheaves on one fixed site. It does not by itself identify the
sections on varying stage sites with the canonical full-site inverse-image comparisons.
The original DAG's first step includes these identifications but has no concrete
section functor/cocone interface. The delivery supplies the constructions and isolates
that first step, rather than pretending the fixed-site theorem already supplies it.

The source files under literature/stacks-project are absent on this machine. The
source statements and proofs were checked read-only at
https://stacks.math.columbia.edu/tag/0EYL and
https://stacks.math.columbia.edu/tag/09YN (also Tag 09YQ).
The three search services and local grep were used; LeanSearch returned an internal
server error, which is recorded as unavailable without a mathematical verdict.

## New nodes

`def-weil-pbc-affine-section-diagram`, in EtaleStageSectionDiagram, constructs the stage
section functor from the canonical comparisons and existing comparison laws.

`def-weil-pbc-affine-section-cocone`, in EtaleStageSectionCocone, constructs the limit
section cocone using the existing cone compatibility law.

`lem-weil-pbc-affine-section-cocone-colimit`, in EtaleAffineSectionColimit, isolates the
affine-site universal-property argument, with the source, complete argument in words,
and original geometric dependencies. This is the only new open theorem.

## Second reading by M3

1. **Existing interface: PASS.** Diffed the original module and node against the
repository. The existing theorem signature, including all hypotheses and the
comparison maps, is byte-identical. Only its proof and private imports change.
No existing definition or target statement is changed; no change record is needed.
The three added modules are new interfaces with matching new nodes.

2. **Proof and constructions: PASS.** Compiled all four modules locally in import
order through lcompile.py. Exactly the named geometric colimit theorem remains
`sorry`; there is no sorry in either constructed definition, no arbitrary witness
chosen for their data, and no forbidden axiom or implementation escape. Their
objects, arrows and cocone legs are explicit. Coherence uses the existing comparison
laws. The target applies Mathlib's equality criterion to the specified cocone,
and opposites give exactly the required over-category arrows. The axiom checks
are recorded below after compilation of the scratch copy.

3. **Split statement: PASS as a decomposition.** Read the source arguments at
https://stacks.math.columbia.edu/tag/09YN and
https://stacks.math.columbia.edu/tag/0EYL and the related Tag 09YQ. The geometric
colimit statement isolates the first step of the original proof plan, rather than
renaming eventual equality; the generic equality step is proved separately.
Affine base change preserves the affine objects, and the qcqs assumptions ensure
finite presentation and the finite-cover site argument applies. The upper tail
contains i₀ even for a non-antisymmetric preorder. For a singleton index, the
comparison is an isomorphism; for an empty affine object, all the section sets
are singletons. No nonemptiness of objects or section sets is assumed.
Repeated LeanFinder and Loogle searches with compact-object/sheaf-colimit queries,
and local searches for cocones and continuity. Results concern structure-sheaf
sections or generic sheaf colimits, not this varying-site set-valued statement.
The upstream SectionContinuity theorem is for abelian sheaves, not arbitrary sets.
The fixed-site ColimitSiteSections theorem does not supply the missing varying-site
identification. Closing the new hole therefore requires substantial geometric work,
not a few-minute application of an existing theorem.

4. **Route and pruning: PASS after report repair.** Checked sk-thm-iff.json and its
realized statement and step. The delivery only factors a node-level argument; all
original geometric dependencies remain in the new open theorem's plan. Completed
No longer needed with FullAffineEtaleTopos and LimitAffineTransition and all eight
old direct proof-dependency node identifiers. No module is claimed pruned from the
target closure. Restored the planned dependencies as private imports of the open
geometric theorem. The public ComparisonLaws import is necessary for the exposed
functor's definitional body, including its coherence fields: a private import was
tested and Lean rejected it. It is not merely a tactic-only theorem import.

5. **DAG agreement: PASS after metadata repair.** The existing node changes only
proof, proof_deps and proof_origin. Checked the three new nodes' source, statement,
Lean records, creation/blueprint provenance, unit/chapter, and search records.
Added explicit construction proof steps and dependency lists to both definition
nodes: their coherence actually uses ComparisonLaws. Checked that every proof_deps
list is exactly the union of its proof steps' uses. The sole open node retains
all eight original geometric dependencies and describes the varying-site gap.

Second reading changed: completed the pruning report, restored planned proof
imports in EtaleAffineSectionColimit, recorded the definition-node proof dependencies,
and removed excess blank lines in the two construction modules. No theorem
signature or mathematical proof was rewritten. Net holes closed minus added: zero;
this is a one-for-one decomposition, not a completed geometric proof.

Scratch-copy `#print axioms` checks passed for all four delivered declarations:
only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` occur. The two
constructions still transitively depend on upstream open statements, and the
item also depends on the new open colimit statement; no claim of axiom-free
completion is made. The scratch copy was removed before delivery. Final local
compilation of all four modules passed without warnings.
