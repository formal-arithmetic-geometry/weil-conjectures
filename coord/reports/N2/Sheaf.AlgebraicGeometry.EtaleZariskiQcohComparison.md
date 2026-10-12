## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.Scheme.Modules.etale_zariski_qcoh_comparison` with a complete
Lean reduction. Its existing signature, universe and public imports are unchanged.
The tensor-pullback components now form actual sheaf morphisms: the proof derives
naturality from the adjunction unit, module restriction naturality, the natural
composition isomorphism, and equality transport.

Degree zero is constructed directly. The chosen terminal etale object's structure
morphism is an isomorphism; its pushforward is an equivalence. Consequently the
actual tensor-pullback unit on sections is an isomorphism. Compose it with the
right-derived-zero isomorphism and the inverse of `Sheaf.H.equiv₀`. The proof
checks both its naturality and its value on the canonical image of every section.
It uses the chosen terminal object itself, with no assumption that it unfolds to
`id_X`.

Positive degrees compose the existing
`AlgebraicGeometry.zariskiModuleAbelianCohomologyAgree` natural isomorphism with
one new, strictly smaller statement about abelian sheaves in positive degrees,
`AlgebraicGeometry.Scheme.Modules.etaleZariskiAbelianPositiveComparison`, in
`Sheaf.AlgebraicGeometry.EtaleZariskiAbelianPositiveComparison`.
The latter does not compare derived sections in the module category, does not
construct the sheaf maps, and asserts nothing in degree zero. The main proof
composes the naturality equations in Lean and assembles all degrees with
`Nat.casesOn`.

Private generic lemmas first prove the section naturalities with the left adjoints
kept abstract, then specialize to `tensorPullback`. Direct specialization had
forced the kernel to unfold the large tensor/sheafification construction and
exceeded the file limit. The generic proofs and the specialization avoid this
expansion without changing any library definition. All private helpers are proved;
no data is supplied by a new unproved existence theorem.

The item's module compiled without errors or warnings using `lcompile.py`.
The positive-degree statement compiled as well. The dry run also compiled both files and ran the axiom probes. Its static preflight
requires a second-reading section even with `--no-push`; the worker brief forbids
me from writing that section. Nothing has been pushed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.etale_zariski_qcoh_comparison`
(node `lem-sc-etale-zariski-qcoh-comparison`). No `sorry` remains in the item's
module or its private helper declarations.

Added exactly one hole:
`AlgebraicGeometry.Scheme.Modules.etaleZariskiAbelianPositiveComparison`
(node `lem-sc-etale-zariski-abelian-positive-comparison`). Its whole proof is
`:= by sorry`, with the source and complete mathematical argument in its docstring.
This is a decomposition: one original hole closed and one lower hole added,
not a claim that the cohomology comparison is axiom-free. Existing lower holes
reached through the module/abelian comparison and tensor/descent definitions are
unchanged and are not newly added holes.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.EtaleTensorSections` (redundant through the public sheaf import)
- `Sheaf.AlgebraicGeometry.EtaleAffineQcoherent`
- `Sheaf.AlgebraicGeometry.EtaleAffineQcoherentULift`
- `Sheaf.AlgebraicGeometry.EtaleCohomologyOverOpen`
- `Sheaf.AlgebraicGeometry.EtaleQuasiCoherentDescent`
- `Sheaf.CategoryTheory.SiteCohomologyPullback`
- `Sheaf.CategoryTheory.SiteLerayDegenerate`
- `Sheaf.Paper.SiteHigherDirectImageSheafifiedPresheaf`
- `Sheaf.Paper.ZariskiEtaleInclusionMorphismOfSites`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`

Every old `proof_deps` absent from the new direct proof is accounted for:
`def-sc-etale-qcoherent-module`, `lem-sc-etale-qcoherent-descent` and
`def-weil-pbc-abelian-etale-sheaves` remain definition/statement inputs through
`etaleTensorSectionsSheaf`; `def-sc-zariski-cohomology`,
`def-weil-pbc-sites-and-cohomology` and `def-weil-pbc-sheafification` remain
background definitions of the lower abelian comparison. The following have moved
into that lower node's mathematical proof plan:
`lem-weil-pbc-zariski-etale-inclusion-morphism-of-sites`,
`lem-weil-pbc-site-cohomology-pullback`,
`lem-weil-pbc-open-immersion-module-pullback-restriction`,
`lem-sc-etale-affine-qcoherent`,
`lem-weil-pbc-site-higher-direct-image-sheafified-presheaf` and
`lem-weil-pbc-site-leray-degenerate`. Only
`lem-weil-pbc-etale-cohomology-over-open` is rejected from the argument entirely.
These are direct dependency removals, not claims of pruning the target closure.

The disputed node `lem-weil-pbc-etale-cohomology-over-open` and its module
`Sheaf.AlgebraicGeometry.EtaleCohomologyOverOpen` are not used, either by the
implemented proof or by the new node's plan. The new plan uses actual cohomology
over an object and localization, including
`lem-weil-pbc-etale-open-object-cohomology-natural`, instead of the false global
cohomology statement.

The affine-acyclicity, site-inclusion, higher-direct-image and Leray nodes remain
mathematical inputs to the new positive-degree block. Their direct imports have
been removed from this module, but they are not claimed to be unnecessary to the
remaining argument. Descent and the tensor-sections definitions remain visible
through `EtaleTensorSectionsSheaf`. No blueprint unit statement or realized proof
step is bypassed: `dag/units/sk-prop-cd.json` has no realized node for these steps,
and the original comparison remains available at its existing name and type.
No claim is made that any removed module disappears from every target's closure;
that is the maintainer's ledger calculation.

## Where the brief, the DAG or earlier work was wrong

`etaleCohomologyOverOpen` is already marked `STATEMENT-DISPUTED`: its Lean
statement compares global cohomology on X with global cohomology on an arbitrary
open, whereas its DAG requires object cohomology over that open. For the empty
open, this fails even in degree zero. It is deliberately not used.

`siteLeray_degenerate` supplies unspecified objectwise isomorphisms, without
identifying them with the canonical edge map and without coefficient naturality
or degree-zero normalization. Those conclusions are described in its docstring
but cannot be extracted from its type. In addition, some existing site-cohomology
interfaces assume equal object and morphism universes; the small etale site has
objects in u+1 and morphisms in u. The new positive-degree block records the
remaining natural comparison in the actual coefficient and Ext universes required
here, rather than silently choosing unrelated isomorphisms from Leray.

The local `literature/` checkout contains indexes but not the Stacks tex files.
The sources were read from the official Stacks pages
https://stacks.math.columbia.edu/tag/03DW and
https://stacks.math.columbia.edu/tag/03P2; their paths and tag/label references are
preserved in the node and docstring. LeanSearch returned an Internal Server Error
and is recorded as unavailable. LeanFinder and Loogle returned only general
cohomology/Ext definitions and resolution lemmas; the grep search returned no
comparison. Direct searches of the library found the parent and downstream uses,
and the differently sized canonical Leray interface, not this positive abelian
comparison.

## New nodes

`lem-sc-etale-zariski-abelian-positive-comparison` states the natural additive
comparison only for positive degrees of the underlying Zariski abelian sheaf.
Its Lean signature explicitly fixes the small enough-injectives Zariski Ext model
and the standard large etale Ext model. The supplied maps m are constrained at
every etale object, so they are the actual tensor-pullback sheaf maps. The
mathematical proof constructs the direct-image identification, establishes
positive higher-direct-image vanishing on the affine basis, then uses the natural
canonical Leray edge map. It uses no separatedness assumption.

Edge cases checked before stating it: zero modules and empty schemes give zero
groups; affine schemes give zero positive groups on both sides; non-separated
schemes require only affine local vanishing, not affine intersections of an
arbitrary global cover. Naturality has the same orientation as the parent, and
components determine the prescribed m uniquely. The node carries real search
results, its source, proof steps, and the item's nearest blueprint ancestor
`lem-sc-artin-schreier-dimension`. Blueprint searches for the Zariski/etale
comparison and quasi-coherent statements found no separate positive-degree
abelian-sheaf statement to reuse. The conservative header-command check requires the record
`coord/changes/etale-zariski-qcoh-proof-transparency.md`, which documents the local
proof transparency commands and all downstream modules. No existing statement,
public definition or public import changed, and no forced adaptation is needed.

## Second reading by N2

1. Compared the entire parent module with the repository using `diff -u` and
   separately compared the text from `theorem etale_zariski_qcoh_comparison` to
   `:= by` byte for byte: identical. Existing universes, namespaces and public
   imports are unchanged. The edits are private helpers, proof, proof-only imports,
   the updated proof explanation, one new theorem module/node, and the declared
   proof-transparency record. No existing public definition changes.

2. Read all nine private helpers and the parent proof. The generic unit lemma
   follows the adjunction-unit and presheaf-map naturality equations; the generic
   restriction lemma additionally uses naturality of the composition isomorphism
   and `eqToHom`. Thus the `app` components really define a sheaf morphism.
   `terminal_structure_isIso` compares the chosen terminal object with the identity
   object rather than assuming definitional equality. The pushforward equivalence
   makes its adjunction unit invertible. Degree zero composes actual isomorphisms
   and cancels `toRightDerivedZero`, giving the exact requested section value.
   Positive naturality composes the evaluated equation of alpha with `hβ`.
   Both files compile locally without warnings. There is exactly one new named
   `sorry`, in `etaleZariskiAbelianPositiveComparison`, and none in any definition
   or private helper. The canonical adjunction witness is determined by the
   sectionwise unit formula in `exists_tensorPullbackAdjunction`; the new private
   definitions construct their objects explicitly. No arbitrary data witness is
   selected from the new open theorem. Axiom probes are recorded below.

3. Read the new theorem, its node and its docstring together with official
   [Stacks 03DW](https://stacks.math.columbia.edu/tag/03DW),
   [03P2](https://stacks.math.columbia.edu/tag/03P2) and
   [0733](https://stacks.math.columbia.edu/tag/0733).
   The only geometric hypothesis is quasi-coherence; no separatedness or
   nonemptiness is introduced. The new theorem compares abelian-sheaf groups only
   in degrees n+1, conditional on prescribed component maps. It omits the module
   derived-section comparison, map construction and degree-zero normalization
   which the parent genuinely supplies. Therefore it is a strict decomposition,
   with zero net holes closed, rather than a renamed whole item. The component
   constraint determines m uniquely by sheaf morphism extensionality. Zero modules,
   empty schemes and affine schemes have zero positive cohomology; the proof on
   arbitrary schemes uses affine local vanishing and never assumes that arbitrary
   affine-open intersections are affine. Reading the localization and open-object
   nodes confirmed that they concern cohomology over an object, not global
   cohomology on X. The Ext-resolution Mathlib leaf supplies resolution independence.
   Leray's existing Lean signature provides only objectwise isomorphisms, not
   naturality: the new hole still includes the explicit canonical-resolution-map
   argument and universe transport described in its docstring. I did not count
   those assertions as already formally proved.
   Independent searches with different wording used LeanFinder (natural isomorphism
   between etale and Zariski sites for an O_X module; only general equivalence/sheaf
   hits) and Mathlib grep (quasicoherent cohomology/acyclicity; no hits), plus rg of
   lean/Sheaf and upstream WeilConjectures. No matching available comparison was
   found. `ZariskiEtaleCanonicalLeray` was read: its scheme/coefficient universes and
   required canonical fstar data do not specialize directly to this theorem.
   Closing the remaining comparison is substantial work, not a short omitted lemma.

4. Checked the reduction top down and read `dag/units/sk-prop-cd.json`: its
   `realized.statement` and all `realized.steps` are empty; the existing comparison
   name and type remain in the unit's Artin-Schreier route. The proof uses the
   existing module/abelian comparison before the new strictly smaller statement.
   The report now lists every old dependency removed from the parent directly,
   distinguishing inputs moved into the lower plan from the disputed unused node.
   No whole-closure pruning or axiom-free proof is claimed.

5. Compared both JSON records with the Lean: parent `proof`, `proof_deps` and
   `proof_origin` describe map construction, the positive composite and explicit
   degree zero; unchanged fields remain unchanged. The new node's verbatim Lean
   signature, named hole, source, complete proof plan, searches, creation, blueprint,
   chapter and unit agree with the new module. Its uses are mathematical proof-plan
   inputs; their universe-restricted Lean versions are not claimed already applicable.

Second-reading repairs: removed the redundant parent proof import
`Sheaf.AlgebraicGeometry.EtaleTensorSections`. In the new module replaced the broad
public import `Sheaf.Paper.ZariskiModuleAbelianCohomologyAgree` by the actual
signature inputs: `DerivedHomMayerVietoris` for `moduleRings`, sheaf cohomology,
Grothendieck sheaves, enough injectives and abelian-group Grothendieck structure.
Retained `AffineEtale`: testing its removal showed it supplies the small-etale
sheafification and abelian instances used in the signature. No proof was rewritten.
Completed the removed-dependency accounting above. Verdict: valid decomposition,
one parent hole closed, one strictly lower hole added, pending delivery checks.

Axiom audit in `scratchpad/lean/QcohAxiomAudit.lean`: `#print axioms` for all
nine private declarations and the parent returned only `propext`,
`Classical.choice`, `Quot.sound`; `etaleSectionsMap` and the parent additionally
use `sorryAx` from open imported sheaf/comparison facts. No other axiom appeared.
