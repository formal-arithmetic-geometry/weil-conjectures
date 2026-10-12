## What changed

Completed the retained attempt as a decomposition of
`Sheaf.AlgebraicGeometry.EtaleResolutionSectionCanonicalRestriction` into its two
restriction identities. The original theorem's signature and docstring are unchanged.
Its proof imports `EtaleResolutionSectionCanonicalWholeToOpen` and
`EtaleResolutionSectionCanonicalOpenToOpen` privately and combines their conclusions
by conjunction introduction. Each new module has one public theorem, a source,
a detailed cocycle proof in words, and a matching DAG node. The parent node's proof
and proof dependencies now follow this Lean reduction.

Repaired the earlier attempt's placeholder `lean.statement` records using the exact
Lean signatures, replaced the non-self-contained node statements, and recorded the
searches actually run for this item (LeanFinder, Loogle, grep, and an unavailable
LeanSearch request). Removed the unchanged sandbox copy of
`EtaleResolutionSectionCanonicalComparison`; no adaptation or interface change is needed.

The source pages read were Stacks Tags
[03F3](https://stacks.math.columbia.edu/tag/03F3) and
[0A50](https://stacks.math.columbia.edu/tag/0A50). They justify localization and the
resolution-section interpretation. The detailed Hom-cocycle calculations in the new
docstrings expand the parent node's proof; these computations remain unformalized.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Etale.resolutionSection_canonical_restriction`
(node `lem-weil-pbc-etale-resolution-section-canonical-restriction`).
There is no `sorry` in the item module.

Added two holes, both the entire proof of a public theorem:

- `AlgebraicGeometry.Etale.resolutionSection_canonical_whole_to_open`, node
  `lem-weil-pbc-etale-resolution-section-canonical-whole-to-open`.
- `AlgebraicGeometry.Etale.resolutionSection_canonical_open_to_open`, node
  `lem-weil-pbc-etale-resolution-section-canonical-open-to-open`.

This is a decomposition, not a completed proof of either cocycle calculation:
one upper hole closed and two lower holes added, net minus one.
Each new statement proves only one conjunct of the parent, and neither assumes
or restates the full parent conjunction. No definitions or existing signatures changed.

The edge cases were checked against the definitions: degree zero uses the same
cycle-to-homology epimorphism; an empty open requires no selected point; identity
inclusions classify the identity generator; zero sheaves give zero cohomology groups.
No positivity, covering, nonemptiness, or nonzero-sheaf hypothesis is introduced.

## No longer needed

No original import is removed; the public import of
`Sheaf.AlgebraicGeometry.EtaleResolutionSectionCanonicalComparison` is required by
all three statements. Both added private imports are used by the item's proof.
No module is claimed globally pruned.

The parent no longer directly needs proof edges to
`def-weil-pbc-cohomology-pullback`, `def-weil-pbc-etale-open-comparison-data`,
`def-weil-pbc-etale-open-object-cohomology-map`,
`def-weil-pbc-etale-resolution-section-canonical-comparison`, or
`lem-weil-pbc-open-cohomology-whole-restriction-naturality`.
These dependencies remain needed below the two new restriction lemmas; this is
relocation of the work, not elimination. No unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The previous delivery-tool import failure no longer occurs. The first new dry run
compiled the retained reduction and reached preflight, which rejected placeholder
Lean-signature records for the two new nodes. Both records are repaired.
The earlier attempt also omitted the changed parent proof route and provided only
short descriptions in place of self-contained node statements and detailed proof sketches.

Search and inspection found Mathlib's `InjectiveResolution.mk₀_comp_extMk` and
`HomologicalComplex.homologyπ_naturality`, and the library's
`EtaleOpenComparison.sectionsEquiv_naturality`. These are ingredients rather than
the required constant/free-generator and inverse-image-composition identifications.
`EtaleResolutionSectionHomologyNaturality` already imports this item and uses its
theorem, so importing that consumer would be cyclic. The two new obligations expose
the separate whole-to-open and open-to-open computations for subsequent workers.

## New nodes

`lem-weil-pbc-etale-resolution-section-canonical-whole-to-open` states only the
whole-to-open identity. Its proof computes the map from the free sheaf on W to
the constant integer sheaf, then identifies its pulled-back identity generator
with the constant-sheaf comparison defining `cohomologyMap`.

`lem-weil-pbc-etale-resolution-section-canonical-open-to-open` states only the
open-to-open identity. Its proof computes precomposition by the free-sheaf map
for A contained in B and tracks the inverse-image composition transport defining
`openCohomologyRestriction`.

Both nodes retain the parent's chapter and unit. There are no change records:
no existing statement, definition, or public visibility changed.

## Second reading by J3

1. **Interfaces unchanged — pass.** Read and diffed all delivered modules against
   the repository. The only existing module is CanonicalRestriction: its original
   theorem signature is byte-for-byte identical, as are its docstring and public
   import. Its only changes are two private proof imports and conjunction
   introduction. The two new modules each state exactly one conjunct, with the
   same scheme universe, G, I, normalized comparison c, all natural-number
   degrees and all classes. No target, definition, visibility or hypothesis changes;
   no change record or forced adaptation is required. Read the landed comparison
   normalization and open-object construction change records as well.
2. **Kernel checks — pass as a decomposition.** Compiled all three modules in
   import order with lcompile.py: no errors or warnings. A scratch copy with
   #print axioms for all three declarations reports only propext, Classical.choice,
   Quot.sound and sorryAx. The latter is expected: the two new declarations have
   exactly their whole proof `by sorry`, and the parent applies them. Text inspection
   found exactly those two holes, no forbidden declaration or attribute, and no
   new definition or data chosen from an unproved existence theorem. The scratch
   copy was removed. This is one original hole closed, two added, net minus one;
   none of the restriction identities is yet proved without sorryAx.
3. **Split statements — pass, proof sketch improved.** Read the comparison's
   global_cocycle and open_cocycle fields, the actual identity-generator construction,
   cohomologyMap and openCohomologyRestriction. The new conclusions are respectively
   the first and second conjunct; neither merely renames the full parent. The Hom
   cocycle proof sketches use an epi homologyπ in abelian groups, additive sections
   adjunctions, and the Ext precomposition formula. Degree zero still has this epi;
   the cycle equation uses the outgoing differential in every degree. Empty opens
   need no point or selected generator of a nonempty set: the construction uses
   their identity morphism. Identity inclusions and zero coefficients introduce
   no extra assumptions. Checked Stacks 03F3(2) and 0A50 online: these supply
   localization and resolution-section interpretation, while the explicit Ext
   computations are the stated agent expansion, not verbatim claims of those tags.
   Repeated searches with different words using LeanFinder, Loogle and grep.
   LeanFinder returned module-sheaf free-pullback results, not this AddCommGrpCat
   comparison. Loogle found Ext.mapExactFunctor_comp and related transport lemmas.
   Local searches found a relevant previously proved generator identity: see point 4.
4. **Route and pruning — pass, existing ingredients identified.** Read
   EtaleOpenObjectCohomologyNatural, EtaleOpenFreeSheafUnitCoherence and
   ExtExactFunctorCompositionComparison. The first has a private canonical-map
   naturality proof; its public theorem asserts existence of natural isomorphisms,
   not equality for the particular normalized comparison c. The latter two give
   precisely the generator coherence and Ext transport needed in the open-to-open
   sketch. Updated that sketch to use these declarations rather than recompute
   them. They do not finish the section-cycle-to-Ext identification in a few minutes;
   both new holes remain. ObjectCohomologyPresheafResolution and
   InjectiveResolutionCohomologyPresheafData use coefficients in the site's Hom
   universe, rather than this module's larger lifted coefficient universe, and
   do not give the particular normalization identity. The downstream
   CanonicalRestriction consumer is not usable as a dependency (cycle).
   All actual Lean imports are needed: the public comparison import supplies the
   signatures and the two private imports supply the parent's two proof terms.
   The newly identified declarations occur only in the remaining natural-language
   plan; no unused import is added for them. The five removed direct parent proof
   edges are all listed in No longer needed, and their work remains below the split.
   Read dag/units/sk-thm-p1.json, including realized: neither the parent nor the
   two new nodes is a realized unit statement/step. This reduction stays below the
   unit route and keeps the parent used by its downstream Mayer-Vietoris argument.
5. **DAG — pass after repair.** Parsed each delivered node, checked proof_deps
   equals the union of proof-step uses, and compared each lean.statement against
   its actual normalized signature. The existing node changes only proof,
   proof_deps and proof_origin. The new nodes have their source, complete argument,
   searches, split status, creation record, blueprint ancestry, chapter, unit and
   Lean record. Added the two existing ingredient nodes to the open-to-open plan's
   uses/proof_deps, and clarified its proof_origin. No new statement or hole was
   introduced by this second reading.

Second-reading changes: expanded the new open-to-open docstring and matching node
proof to cite etaleOpenFreeSheafUnit_coherence and
Ext.exactFunctorCompositionComparison; added their existing nodes as planned proof
dependencies; documented this review and searches. The parent Lean proof and all
three signatures are unchanged from the first worker's delivery.
