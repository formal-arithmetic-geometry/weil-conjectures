## What changed

Proved `AlgebraicGeometry.coherentFormalModule_isIso_of_isIso_restrict` in
`Sheaf.AlgebraicGeometry.CoherentFormalModuleIsomorphismLocal`, with its signature and
visibility unchanged. The proof uses the existing source lemma
`Scheme.Modules.bijective_stalk_of_isIso_restrict`, Mathlib's stalk criterion, the
componentwise natural-transformation isomorphism criterion, and reflection of
isomorphisms by the full-subcategory inclusion. The inverse is `inv α`; its level
components are identified using `ObjectProperty.hom_inv` and `NatTrans.inv_app`.

Removed the proof import `Sheaf.Topology.GlueSheavesOfModules`. The second reading
also removed redundant new proof imports
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf` and
`Mathlib.Topology.Sheaves.Stalks`: the unchanged public import of
`CoherentFormalModule` already exposes both needed APIs.
Updated the theorem docstring and its node's proof, proof dependencies, and proof
origin to describe the compiled route. No definitions or statements changed.

The shorter route stays below unit `sk-thm-p1`: neither this node nor the glueing
node realizes a fixed unit statement or step. All realized nodes of the unit stay.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.coherentFormalModule_isIso_of_isIso_restrict`
(node `lem-weil-pbc-coherent-formal-modules-isomorphism-local`).

One hole closed; zero holes added; zero split off. There are no remaining `sorry`s
in the delivered Lean module and no new Lean modules. This is a proof, not a
replacement of the hole by new holed statements. The new DAG node records a
pre-existing theorem whose pinned sorry-map entry has `s=false` and `ts=false`.

The local compiler accepts the full proof without warnings. The proof handles
arbitrary index universes and arbitrary covers: empty members cause no problem;
an empty index with supremum top implies that the scheme has no points, so the
stalk criterion applies vacuously. The proof uses no additional nonemptiness,
affineness, or coherence hypotheses. All original binders remain unchanged.

## No longer needed

Removed baseline import: `Sheaf.Topology.GlueSheavesOfModules`.
Removed redundant imports from the first draft:
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf` and
`Mathlib.Topology.Sheaves.Stalks`. Neither removal changes a public import.
Removed proof dependency: `lem-weil-pbc-glue-sheaves-of-modules`.

The original proof's local inverse construction, overlap comparison, morphism
glueing, and glueing uniqueness are unnecessary. Consequently the object descent
and derived Mayer–Vietoris theory imported by the glueing module are also not
needed by this proof. Their modules `Sheaf.Topology.ModuleObjectOpenDescent` and
`Sheaf.Paper.DerivedHomMayerVietoris` were not added. These are statements about
this item's proof dependency, not claims that other targets cease to use them.
The two definition dependencies in the old plan remain needed.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable interface was found. The DAG's glueing plan is
valid but longer than necessary: the source library already has the local-stalk
bijection theorem. The old Mathlib-search note says single-sheaf criteria do not
prove a formal-module assertion; combining them with Mathlib's componentwise
natural-transformation criterion does prove it.

LeanFinder found the stalk criteria; Loogle found
`NatTrans.isIso_iff_isIso_app`; source and Mathlib searches located the restriction
stalk theorem. LeanSearch returned an internal-server error, recorded without an
absence verdict. Import-cycle checking allows the source-module proof import.

## New nodes

`lem-weil-pbc-module-restriction-iso-stalk-bijective` records the existing declaration
`AlgebraicGeometry.Scheme.Modules.bijective_stalk_of_isIso_restrict` in
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf`. Its proof is already
complete in the source library and uses Mathlib's restriction-stalk natural
isomorphism. The record supplies the exact signature, a self-contained statement,
proof steps, source, and three search kinds (including the unavailable LeanSearch
attempt). It introduces no statement, object, Lean module, or hole. Existing
`lem-weil-pbc-module-iso-on-stalks` records the stalk criterion used next.

No change records or forced adaptations are needed.


## Second reading by X2

1. **Interface preservation: PASS.** Compared the sole delivered Lean module with
   the repository version. Its only declaration's signature is byte-for-byte
   identical, including universes, binders, hypotheses, conclusion and visibility.
   There are no new declarations or definitions, no change records, and no forced
   adaptations. The docstring describes the new proof; the public import stays.
2. **Kernel proof: PASS.** Compiled the whole module locally without warnings.
   A scratch copy with `#print axioms` for
   `AlgebraicGeometry.coherentFormalModule_isIso_of_isIso_restrict` and
   `AlgebraicGeometry.Scheme.Modules.bijective_stalk_of_isIso_restrict`
   reports exactly `propext`, `Classical.choice`, and `Quot.sound`, without
   `sorryAx`. There are no `sorry`s, axioms, unsafe declarations, opaque
   declarations, implementation overrides, or external implementations. The only
   chosen data are the categorical inverses of proved isomorphisms; those are
   uniquely determined, so no arbitrary unproved existence witness is used.
3. **Split-off statements: PASS (none).** No holes were split off or added.
   Read the existing source stalk-restriction theorem and its proof through
   `restrictStalkNatIso`; the new node records that already proved declaration,
   rather than restating the item. Its point-in-open hypothesis handles empty
   opens vacuously, and requires neither coherence nor Noetherian hypotheses.
   Independent searches used `msearch.py ... grep` with
   `isIso.*stalk|isIso.*coversTop|isIso.*restrict` and `rg` over the library;
   the existing declaration is reused, and no existing DAG lean record duplicates
   it. No new Lean statement needed a duplicate or edge-case check.
4. **Route and pruning: PASS after import cleanup.** Read the proof from the
   conclusion down: componentwise isomorphisms, reflected full-subcategory
   isomorphism, and its unique inverse prove every requested clause. The cover
   supplies a stalk bijection at every point, with no nonemptiness assumption;
   an empty index covering top forces an empty space. The existing
   `sheaf_module_isIso_iff_isIso_over_open_cover` uses the over-site restriction
   and imports derived-category machinery, while the chosen source/Mathlib
   argument directly matches `Scheme.Modules.restrictFunctor`. A private stalk
   helper elsewhere is unavailable. The current proof is short and sound.
   `sk-thm-p1.json` realizes neither this node nor the removed glueing node, so
   its statement and all fixed steps remain. The old proof dependency set loses
   exactly `lem-weil-pbc-glue-sheaves-of-modules`; both old definition dependencies
   remain. Removed both redundant new imports after compiling scratch copies
   without each and without both.
5. **DAG agreement: PASS.** The existing node changes
   only `proof`, `proof_deps`, and `proof_origin`. Its dependency set equals the
   union of its steps' `uses` and matches the source theorem, the Mathlib stalk
   criterion, and the two definitions used in Lean. Checked the referenced
   Mathlib-match node and unit record. The new node records the exact existing
   source signature, complete proof in words, source, searches, creation data,
   blueprint ancestry, chapter and unit. The preflight requires `lean.file` to be
   absent when `lean.existing` is true, since no source file is delivered for that
   declaration; verified that representation.

Second reading changed only the two redundant proof imports and this report. The proof itself required no repair. One original
hole closed, zero holes added, zero split off.
