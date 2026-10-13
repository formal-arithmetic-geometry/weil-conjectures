## What changed

Replaced the hole in
`AlgebraicGeometry.Scheme.Modules.exists_finset_generatingSections_on_compact`
with a proof from the local finite-selection step of its plan. Added the proof-only
import `Sheaf.AlgebraicGeometry.ModuleGeneratingSectionsLocalSelection`.
The original statement, universe, binders and visibility are unchanged.
Compilation of the item and the new module is checked with lcompile.py;
the final dry run also checks every delivered declaration with the axiom probe.

The proof chooses generating neighbourhoods indexed by the points of K, takes a
finite subcover using `IsCompact.elim_finite_subcover`, and forms the finset
`biUnion` of their supports. A proved private helper uses the free coproduct
universal property and `epi_of_epi_fac` to enlarge each support. Another proved
private helper identifies epimorphisms after `overMap` with pointwise local
lifting on the slice site. Intersecting a test open with a selected neighbourhood
and composing restriction maps proves the final epimorphism. This includes empty K.

Proof-only imports of the underlying abelian-sheaf colimit result, the sites
abelian/epimorphism API, and the abelian-group factorization API supply the
local-lifting criterion. The existing public import of Coherent is unchanged.
The item node now records the implemented route.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.exists_finset_generatingSections_on_compact`
(node `lem-weil-pbc-module-generating-sections-compact-selection`).
No sorry remains in the item's module or in its private helpers.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.exists_finset_generatingSections_near_point`
(node `lem-weil-pbc-module-generating-sections-local-selection`, module
`Sheaf.AlgebraicGeometry.ModuleGeneratingSectionsLocalSelection`).
Its proof is exactly `by sorry` and its docstring gives the complete local
argument and sources. It concludes generation only near a single point and has
no compactness hypothesis; it is strictly the first step of the original plan.

This is a decomposition: one original hole closed, one local hole added, net
zero holes closed. The compact finite-subcover and local-to-global argument is
now checked by Lean; the local finite-support step remains to prove. No data
definition or arbitrary witness chosen from a holed existence theorem was added.

## No longer needed

No literal import was removed: the original file had only its statement import
of Coherent. No whole module is claimed pruned from the targets' closure.

The following former direct proof dependencies are now needed only in the local
helper's proof plan, not in the compactness assembly:
`def-weil-pbc-module-finite-type-presentation`,
`lem-weil-pbc-ringed-space-module-exactness-local-lifting`
(`Sheaf.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting`),
`lem-weil-pbc-module-stalk-filtered-colimit`
(`Sheaf.AlgebraicGeometry.ModuleStalkFilteredColimit`), and
`lem-weil-pbc-module-restriction-open-immersion-colimits`
(`Mathlib.AlgebraicGeometry.Modules.Sheaf`). These are retained as dependencies
of the new local node; they are not claimed globally unnecessary.

The old dependency `lem-weil-pbc-locally-surjective-iff-stalks` is no longer
needed by this argument: the proved private slice-site criterion uses
`Mathlib.CategoryTheory.Sites.EpiMono` directly and does not form stalks.
The proof-only import was narrowed from
`Mathlib.Topology.Sheaves.LocallySurjective` to
`Mathlib.CategoryTheory.Sites.EpiMono`. No other module is claimed to leave the
whole targets' closure, since it may have other users.

The parent no longer needs to compare restriction of a free sheaf with a newly
constructed free sheaf over K: it factors the original basis maps before applying
`overMap`. The local-to-global step uses local lifting directly, with no stalk
construction and no affineness or quasi-coherence lemmas.

## Where the brief, the DAG or earlier work was wrong

The DAG's mathematical argument is valid, but its listed dependencies do not
state the local finite-support conclusion for an arbitrary specified generating
family. The local-lifting theorem addresses a single epimorphism, and the stalk
colimit theorem addresses a supplied colimit diagram; neither directly constructs
the finite-sub-coproduct diagram or a common support for finitely many lifted
local generators. The new theorem isolates exactly that missing first step.

LeanFinder found only finite-type/local-generators definitions; Loogle found no
matching selection lemma. LeanSearch was unavailable (Internal Server Error),
recorded as unavailable rather than as evidence of absence. The whole blueprint
search for finite subfamilies and finite support found no matching node. The
unit sk-thm-p1 and all its realized statements and proof steps remain unchanged;
this reduction is below the unit level.

## New nodes

`lem-weil-pbc-module-generating-sections-local-selection`, in
`dag/nodes/sec-proper-base-change/`, states the neighbourhood finite-selection
step. It inherits the chapter, unit and blueprint ancestor of the item. Its
source is Stacks Modules 01BB, first paragraph of the proof, and 01B8. The
natural-language argument uses local finite generators, local lifting, finite
support in the free-sheaf stalk, and a common shrinking neighbourhood. Empty
local generator families, empty original index types and empty K are covered.
It has a complete Lean statement, one public named sorry, and recorded searches.
No statement/interface change record is needed: existing signatures are unchanged.

## Second reading by V2

1. Unchanged interface: compared the whole compact-selection module by diff and
   checked its theorem signature byte for byte. Its universe, scheme, opens,
   compactness, containment, module, finite-type instance, specified family and
   finite-subfamily epimorphism are unchanged. The original docstring and public
   import are unchanged; all added imports are proof-only. There are no changed
   definitions, target statements, or forced adaptations. Verdict: pass.

2. Proof audit: read both private helpers and the complete compact proof. The
   slice helper converts an epi to a covering image sieve after forgetting to
   abelian sheaves; `overEquiv` gives exactly neighbourhood lifts inside K. The
   support helper proves the coproduct factorization before applying overMap;
   `epi_of_epi_fac` enlarges the support. The final proof restricts a test section
   to W intersect U_i, lifts there, and composes restrictions, so it proves the
   original morphism is epi. The only literal sorry is the named local theorem;
   no forbidden declaration form or data definition was introduced. Compiler
   and axiom results are recorded below. Verdict: the reduction is sound, with
   the explicitly reported local hole still open.

3. Local split: read Stacks 01BB, first proof paragraph, and 01B8 online. On K,
   finite type gives finitely many local generators. Lift their germs through
   the specified epi, take the union of their finite basis supports, represent
   them in that finite free sheaf, and shrink until their images equal all local
   generators. The resulting map is epi near the point. No quasi-coherence,
   finite presentation or affineness is used. Empty K has no point; an empty
   generator family forces the target to be zero and permits empty support;
   the same applies to a zero target with no local generators. The statement
   and docstring express this local step only, with no compactness or global
   selection, so it is strictly a part of the original argument. Its node has
   the required source, complete proof, searches and exact Lean statement.
   Independent msearch LeanFinder query: “An epimorphism from a coproduct of
   copies of a ring sheaf to a locally finitely generated module is surjective
   from finitely many summands near a fixed point”; results were generator
   transport and local-generator definitions. Loogle query
   `SheafOfModules.free, SheafOfModules.IsFiniteType` returned zero hits. The
   msearch grep query `free.*(finite|Finset)|IsFiniteType.*(epi|free)|finite.*support`
   in ModuleCat/Sheaf returned only finite-presentation generator instances.
   Also searched lean/Sheaf, lean/WeilConjectures and the upstream module and
   algebraic-geometry sources. FiniteGlobalGeneratingFamily requires an
   invertible module and chooses a new family; FiniteFreeStalkMapLocal lifts a
   finite matrix, not an arbitrary coproduct section. Neither states this step.
   Closing the local hole requires constructing and identifying the finite
   sub-coproduct stalk diagram; it is not a short application of those APIs.
   Verdict: true, needed, not a restatement or an existing matching result.

4. Route and pruning: reviewed the proof from the compact target down to the
   local hole, and checked the old six direct proof dependencies against
   “No longer needed”. Compactness stays; four dependencies move to the local
   proof plan; the stalkwise-surjectivity comparison is bypassed by the proved
   slice-site helper. No literal original import or whole module is pruned.
   All added imports have a proof role: module-to-abelian colimit preservation,
   abelian/balanced sheaves, abelian-group surjective/injective factorization,
   the local lemma, and the sites epi criterion. A scratch attempt to omit
   Sites.EpiMono failed at `Sheaf.isLocallySurjective_iff_epi'`, confirming its
   necessity. Read dag/units/sk-thm-p1.json, including realized statements and
   all four realized steps: neither the item nor its local split replaces a
   realized unit node, and the reduction stays below the unit level.
   Verdict: pass; no module pruning claimed.

5. Node agreement: checked exact Lean statements and the union of every proof
   step's uses against proof_deps. The parent records the local lemma, finite
   subcover, support enlargement and proved slice-site local-to-global step;
   proof_origin identifies the same Stacks argument. The local node retains
   finite type, local lifting, stalk colimits and restriction in its unfinished
   plan. Read those dependency declarations: finite type supplies local finite
   generators, local lifting supplies neighbourhood preimages, stalk colimits
   applies after constructing the finite-sub-coproduct diagram, and open
   restriction is left adjoint. The latter is a plan dependency, not an
   assertion that it alone constructs the free comparison. Existing node
   fields changed only in proof, proof_deps and proof_origin. Verdict: pass.

Second reading changes: added this independent review and its search evidence.
No mathematical proof, signature, definition, or node repair was needed.

Verification results: both delivered modules compile cleanly with lcompile.py
in import order. A successful scratch copy with the unchanged full import list
and explicit `#print axioms` shows that both private helpers use only propext,
Classical.choice and Quot.sound. The compact theorem and the named local theorem
use those axioms plus sorryAx, as expected from the single reported local hole.
The failed import-removal probes are not delivered: omitting Sites.EpiMono loses
the criterion; omitting Grp.EpiMono loses the AddCommGrpCat functorial
surjective/injective factorization instance. All Lean lines meet the 100-character
limit. The successful proof and its imports were kept unchanged.
