## What changed

Replaced the hole in `AlgebraicGeometry.localDerived_stalk_transport` by a complete
Lean proof from two separate parts. All existing signatures and public imports stay
unchanged. Added two proof-only imports, of the new modules
`Sheaf.AlgebraicGeometry.LocalPullbackAdjointStalkIso` and
`Sheaf.AlgebraicGeometry.LocalDirectImageStalkCohomology`.

The first new module proves `AlgebraicGeometry.localPullback_adjoint_stalk_isIso`
for arbitrary module sheaves G and H, without a derived functor or cohomology.
It uses the already proved `Scheme.fromSpecStalk_module_stalk`, Mathlib's
`stalkPushforward_iso_of_isInducing`, equality on germs, cancellation of
isomorphisms, and the adjunction-unit formula. The point equality c(z)=y is
handled explicitly. No new hole is introduced in this underived argument.

The second new module isolates the remaining derived evaluation comparison.
It has no auxiliary module G, no beta, and no hypothesis about the action of an
arbitrary adjoint. Its normalization evaluates only the given target section-class
map. The original proof composes the stalk isomorphism of the adjoint with this
comparison and proves the desired implication by the explicit equality
`stalkMap a (germ s) = germ (a_V s)` followed by the assumed section equality.
This is a reduction with a proved underived part, not a claim of a sorry-free
local cohomology comparison.

The node copy records this route. The new nodes retain the original chapter and
unit; neither is a statement or realized step of the blueprint unit. No unit-level
route is bypassed. No definition, target, or existing theorem signature changes.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.localDerived_stalk_transport`
(node `lem-weil-pbc-local-derived-stalk-transport`). Its body has no sorry.

Also proved the new theorem:
`AlgebraicGeometry.localPullback_adjoint_stalk_isIso`
(node `lem-weil-pbc-local-pullback-adjoint-stalk-iso`). Its body has no sorry.

Added exactly one hole, and this is every sorry left in the delivered files:
`AlgebraicGeometry.localDirectImage_stalk_cohomology`
(node `lem-weil-pbc-local-direct-image-stalk-cohomology`), with body exactly
`:= by sorry`. Its docstring gives the source and the complete argument, including
scalar normalization, exact evaluation, the restricted-resolution component and
augmentation conditions, and independence of resolution choices.

Accounting: one original hole closed, one new hole added; net zero holes. The
original theorem is a decomposition, not a completed sorry-free proof. The
underived local adjunction step is proved from existing declarations.

The new comparison was checked mathematically in degree zero (the ordinary
section/germ map), for zero modules and empty X', and for arbitrary compatible
resolution choices. The latter is why the component and augmentation fields of D
must both appear in its proof: an arbitrary unnormalized equivalence would not
suffice. The underived theorem also includes the zero-module case and does not
use properness, coherence, flat base change, or finiteness assumptions.

## No longer needed

No original import was removed, and no global module pruning is claimed.

The original proof-dependency edges are replaced by the two new nodes and the
ringed-space module-stalk node. The local-spectrum, higher-direct-image,
exact-functor-homology, open-choice, resolution-construction and cohomology-map
nodes remain needed through the new parts; they are not pruned.

`pqf-def-cohomology` / `Sheaf.Paper.PQFCohomology` is not needed as a theorem
in the new proof: module cohomology is already defined as a right derived functor.
However, it remains transitively imported by `ModuleCohomologyFMap`, so this is
not a globally pruned module.

`lem-weil-pbc-module-open-restriction-injectives` /
`Sheaf.AlgebraicGeometry.ModuleOpenRestrictionInjectives` is not a separate
proof dependency of the new comparison: D already supplies an injective resolution
of the restriction and an augmented comparison. No existence of new restriction
choices is required by the quantified statement.

`def-weil-pbc-module-stalk` / `Sheaf.Topology.PresheafModuleStalkFunctor` is
not needed for the upper combination; it uses the existing ringed-space sheaf
stalk functor (`def-pc-module-stalk-functor`). The general presheaf stalk functor
still occurs in `HigherDirectImagePresheaf`, so it is not globally pruned.

The complete list of old direct proof-dependency edges removed from the upper node is:
`lem-weil-pbc-spec-local-ring-canonical-morphism`, `def-weil-pbc-module-stalk`,
`lem-weil-pbc-higher-direct-image-presheaf`, `pqf-def-cohomology`,
`lem-weil-pbc-exact-functor-complex-cohomology`,
`def-weil-pbc-flat-base-change-open-choices`,
`def-weil-pbc-flat-base-change-resolution-construction`,
`lem-weil-pbc-module-open-restriction-injectives`, and
`def-weil-pbc-module-cohomology-fmap`. Most remain dependencies of the new parts
or occur in the unchanged public signature; removal of a direct edge is not
removal from the import closure. No module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The DAG step 1 can be completed using
the already proved canonical pullback-unit stalk theorem, rather than restating
the stalk scalar transport. The original import list does not itself provide the
local exact-evaluation normalization in steps 2 and 3, so that narrower derived
comparison is stated separately.

The blueprint searches for "closed point stalk" and "local total cohomology"
returned no matching imported blueprint node. The ancestor command returned None
for this newly introduced stage-3 item; the new records therefore preserve the
explicit ancestor and via chain already recorded in its node.

LeanSearch returned Internal Server Error and is recorded as unavailable, not
as evidence of absence. LeanFinder returned structure-sheaf stalk maps, not the
module-derived comparison; Loogle did not recognize the abbreviated identifier
Scheme.fromSpecStalk. Mathlib source search supplied the inducing-map stalk
comparison and the germ naturality lemma actually used in the proved part.
Sources were read at Stacks Tags 02OD, 01E4, 01J7 and 0098; the local source .tex
files are absent on this machine.

Lean's rewrite elaboration on the nested right-derived module types exhausted
heartbeats. Replacing the section rewrite with explicit `congrArg` equalities
made the proof compile; the main theorem has a documented local heartbeat limit.
No project tool was edited or bypassed.

## New nodes

`lem-weil-pbc-local-pullback-adjoint-stalk-iso` records the proved underived
adjoint-stalk isomorphism, in
`lean/Sheaf/AlgebraicGeometry/LocalPullbackAdjointStalkIso.lean`. It is strictly
separate from total cohomology and applies to any H on the local spectrum.

`lem-weil-pbc-local-direct-image-stalk-cohomology` records the remaining local
derived evaluation equivalence and section-class normalization, in
`lean/Sheaf/AlgebraicGeometry/LocalDirectImageStalkCohomology.lean`. It removes
all arbitrary comparison data G and beta from the problem. The argument can be
proved independently of the now completed adjunction and germ-naturality glue.

No change record is required: no existing interface or statement changes and
there are no forced adaptations.

## Second reading by H3

1. **Interface preservation: pass.** Read all three delivered modules and diffed
   the upper module and its node against the repository. The existing theorem
   signature and docstring are byte-for-byte unchanged. The changes are two plain
   proof imports, a local heartbeat limit, and its proof body. There are no new
   definitions, forced adaptations, or changes requiring a change record. The
   original public imports provide the ringed module stalk, local-spectrum
   morphism, resolution choices, section-class and cohomology map in the signature.
   The new underived module imports SpecLocalRingCanonicalMorphism privately.

2. **Kernel and holes: pass as a decomposition.** Compiled the three files in
   import order through lcompile.py, with no errors or warnings. Compiled scratch
   copies with #print axioms for each theorem: localPullback_adjoint_stalk_isIso
   uses exactly propext, Classical.choice and Quot.sound; the upper theorem and
   localDirectImage_stalk_cohomology also use sorryAx. The latter is the only
   syntactic sorry in the delivered Lean, in a named public theorem with source,
   full prose proof and matching node. There is no axiom, unsafe, opaque,
   implemented_by, extern, or data definition with a hole. In particular the
   existential equivalence is eliminated inside a proposition proof, not used
   to define an arbitrary object. One original hole closes and one new hole opens.

3. **New statements and sources: pass.** Read Stacks 02OD (the displayed local
   stalk/global-section/total-cohomology identification), 01E4 (the sheafified
   cohomology presheaf), 01J7 and 0098, and the actual declarations
   fromSpecStalk_module_stalk, RestrictedResolutionSections, targetClass,
   resolutionSectionClass and moduleCohomologyFMap. Although 02OD's surrounding
   formal-functions theorem assumes properness and coherence, this particular
   evaluation argument needs neither: every open containing the closed point of
   a local spectrum is top, so evaluation is a stalk and is exact. Every V
   containing y pulls back to top, and the pullback-square identity makes W top.
   The comparison's scalar map has the direction A to Gamma(Spec A) to Gamma(X').
   D.target.components fixes the section identification; D.target.augmentation
   prevents a resolution automorphism from changing the cohomology class.
   Tested the argument in degree zero (ordinary sections and germs), for zero
   modules, for a field stalk (one-point spectrum), and for empty X'. Arbitrary
   compatible resolution changes induce the same cohomology map by homotopy of
   augmented comparisons. The underived theorem has no cohomology, I, K, D or p;
   the remaining theorem has no G, beta or section-equality hypothesis. They are
   separate parts of the original argument, not a renaming of it.

   Independent searches used the new phrases "exact global sections at closed
   point local scheme derived direct image module sheaf" (LeanFinder),
   "TopCat.Presheaf.stalkPushforward" (Loogle), and
   "globalSections.*stalk|stalk.*globalSections|IsLocalRing.*closedPoint" (grep)
   through msearch.py. Loogle confirms the inducing-map stalk isomorphism already
   used; the other hits concern structure sheaves and algebraic localization,
   not the derived comparison. Also searched lean/Sheaf, lean/WeilConjectures and
   the upstream AlgebraicGeometry sources for stalk/cohomology and local-spectrum
   formulations. No replacement for the remaining normalized comparison was
   found. HigherDirectImagePresheaf supplies the sheafification comparison, but
   not the complete scalar-normalized equivalence and compatibility with the
   resolution-defined moduleCohomologyFMap; closing that hole requires more than
   a short application of an existing theorem.

4. **Route and pruning: pass.** In the underived proof, equality on every germ
   identifies the unit followed by q with the already proved canonical module
   stalk isomorphism. Cancellation of invertible q proves the unit invertible;
   homEquiv_unit then handles beta, and fromSpecStalk_closedPoint transports the
   point to y. In the upper proof the stalk map of the adjoint is composed with
   the derived equivalence. stalkFunctor_map_germ_apply, congrArg and the supplied
   section equality prove the normalization exactly. The two new imports are
   plain imports used by these steps. Checked dag/units/sk-thm-p1.json: neither
   the item nor either helper is a realized unit statement or step, and no
   realized route is removed. Expanded No longer needed to enumerate all nine
   removed old direct edges; no global module pruning is claimed.

5. **DAG agreement: pass after repair.** The upper node's three elementary steps
   match invertibility, composition and germ naturality in the Lean body. Its
   proof_deps are the two helpers and the ringed-space module stalk node. The
   underived node cites the adjunction and canonical local-spectrum module-stalk
   results actually used. The derived node records the still-open evaluation,
   homology and normalization argument rather than pretending it is proved.
   New records have source, statement dependencies, proof steps and their union,
   proof_origin, search records, creation data, chapter/unit, blueprint ancestry
   and Lean records. Compared recorded Lean signatures with file text: fixed
   one trailing space after a comma in the derived comparison's lean.statement.
   No mathematical statement or Lean proof was changed in this second reading.

Second-reading changes: corrected the new node's verbatim signature whitespace,
completed the direct dependency-edge list, and added this independent review.
