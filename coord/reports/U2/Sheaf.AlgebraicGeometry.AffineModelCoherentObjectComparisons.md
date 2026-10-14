## What changed

Replaced `AlgebraicGeometry.exists_affineModelCoherentObjectComparisons`'s hole with
an explicit construction from a composition-compatible affine-coordinate comparison
family. Scalar extension preserves the acyclic-tensor criterion by the existing
`CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat` theorem. Specializing the
family gives the full two-label natural isomorphisms `θ` and `θlim`. Direct comparisons
from the bottom, followed by pullback of the supplied `aE` and `aK` and inverse
projection comparisons, construct `αE`, `αK`, `βE` and `βK`.

The four coherence triangles use a proved categorical transport lemma: naturality
moves the bottom isomorphism past the composition comparison. Ring equalities are
`F.map_comp` and `C.w`; `Spec.map_comp` proves the two over-arrow compositions.
Added the proved projection triangle module
`Sheaf.AlgebraicGeometry.PerfectHomComparisonTriangle`. Its proof imports and evaluates the existing private
`PerfectHomTransport.cc_assoc` theorem using a proof-only `import all` and transports the projection equations.

Kept the earlier attempt's intermediate module
`Sheaf.AlgebraicGeometry.AffineCoordinateComparisonCoherence`; it isolates the natural
coordinate comparisons and their composition law, independently of target objects,
diagrams, cocones or propagated bottom identifications. The private `affineModel_coordinate` abbreviation packages the supplied coordinate
data once, avoiding repeated elaboration of the functor record. Local irreducibility for
`derivedPullback` and `perfectHomComposition` protects proof elaboration from unfolding
their choice constructions; these attributes do not escape the file.

Both new modules are imported
privately by the parent. Existing public signatures and definitions are unchanged.
All coordinate data are supplied and the comparison-family witness is eliminated
inside a theorem; no definition chooses data from a mere unproved existence theorem.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.exists_affineModelCoherentObjectComparisons`
(node `lem-pc-affine-model-coherent-object-comparisons`). Its complete proof constructs
all eight fields and proves all four triangles from the remaining affine-family law.
This is a decomposition: one original hole closed and one new hole added, net zero.

Proved without additional holes:
`AlgebraicGeometry.perfectHomComparison_triangle`
(node `lem-pc-perfect-hom-comparison-triangle`), from the existing associativity API;
`AlgebraicGeometry.exists_affineCoordinateComparisonTransportFamily`
(node `lem-pc-affine-coordinate-comparison-coherence`), from the affine-family law
and proved categorical naturality. All private helpers are proved.

The only delivered sorry is
`AlgebraicGeometry.exists_affineCoordinateComparisonFamily`
(node `lem-pc-affine-coordinate-comparison-coherence`). It isolates natural affine
coordinate comparisons and their composition law. It has no diagram, cocone,
propagated target objects or bottom identifications. The parent module contains no sorry.

## No longer needed

Removed the duplicate private theorem `composition_assoc` from the new projection
triangle module; its use now calls the existing `PerfectHomTransport.cc_assoc`.
The projection triangle no longer directly needs
`lem-pc-ringed-spaces-derived-pullback-composition`; it is reached through
`lem-pc-perfect-hom-transport`.
No existing imports are removed, and no existing reachable modules are claimed pruned.
The old direct proof dependencies `lem-pc-affine-derived-pullback-tensor-tilde` and
`lem-pc-ringed-spaces-derived-pullback-composition` are no longer direct dependencies
of the parent: the former is needed by the affine-family node, and the latter by
that node. The proved projection triangle now uses only the perfect-Hom transport
node directly, reusing its existing associativity theorem. They remain reachable through these
intermediates and are not claimed as pruned modules.
The parent no longer directly needs the one-square object-existence theorem
`nonempty_affineSquareKFlatModelIso`; its conclusion supplies no composition law.
The natural affine computation remains part of the intermediate comparison-family
node's proof plan. Identity scalar extension and its tensor unitor are unnecessary
in the parent: bottom-to-stage comparisons apply directly to `E` and `K`.
No unit statement or realized unit step is bypassed; the unit record has no realized
nodes for this construction. The parent node's proof dependencies now match the
family, scalar-extension preservation, projection triangle, scalar reassociation
and the existing perfect-Hom API actually used.

## Where the brief, the DAG or earlier work was wrong

Repair of reviewer X-6a909 / failed landing 6a9096476: the new private
`composition_assoc` restated `PerfectHomTransport.cc_assoc` word for word.
Removed that duplicate and reused `cc_assoc` through a proof-only `import all`,
which makes the existing private theorem available without changing its visibility
or adapting PerfectHomTransport. The ordinary public import remains for types.
The delivery tool rebases its generated commit on freshly fetched sheaf-dag.


The first sandbox attempt added a useful intermediate but left the parent `:= by sorry`;
its report incorrectly described a completed assembly. The recovered sandbox now contains
the complete parent assembly. This continuation checked the recovered construction and
its unchanged public interfaces against the original module. Explicit scalar-map arguments and a proved transport-family wrapper avoid
expensive comparison of induced functor components. Existing definitions and signatures
are unchanged. Temporary profiler settings and partial-proof sorries were removed.
The existing affine natural-isomorphism API supplies one affine comparison but no
composition equation pinned to `perfectHomComposition`. That missing part remains
in the intermediate comparison-family theorem, rather than assuming arbitrary
object comparisons are coherent.

Read the statements and proofs of Stacks Tags
[08DW](https://stacks.math.columbia.edu/tag/08DW) and
[0D5S](https://stacks.math.columbia.edu/tag/0D5S). They give the affine scalar-extension
calculation and the derived-composition calculation used by the two new nodes.
Checked identity arrows, coincident labels, zero complexes, zero rings and empty
spectra: the comparison formula needs no distinctness, flatness, boundedness,
directedness or colimit assumption. The abstract projection triangle requires only
composition of over arrows and the existing derived-category instances.

Actual searches are recorded in `searches.jsonl` and the new nodes: LeanFinder,
Loogle and Mathlib grep found the generic functor/isomorphism and scalar-associativity
APIs. LeanSearch returned Internal Server Error and is recorded as unavailable.
The imported blueprint search for derived-pullback composition returned no match;
the nearest blueprint ancestor is null, as reported by `blueprint_refs.py ancestor`.

The source-based import-direction checks now pass for both added imports.

## New nodes

`lem-pc-affine-coordinate-comparison-coherence`, in
`dag/nodes/sec-picard-framework/lem-pc-affine-coordinate-comparison-coherence.json`,
records the remaining natural affine comparison and composition step. Its module is
`lean/Sheaf/AlgebraicGeometry/AffineCoordinateComparisonCoherence.lean`.

`lem-pc-perfect-hom-comparison-triangle`, in
`dag/nodes/sec-picard-framework/lem-pc-perfect-hom-comparison-triangle.json`, records
the proved projection comparison identity and its derivation from the existing
associativity theorem. Its module is
`lean/Sheaf/AlgebraicGeometry/PerfectHomComparisonTriangle.lean`.

Change record: `coord/changes/affine-model-coherent-local-transparency.md`.
Preflight requires it for the added file-local irreducibility command; existing
interfaces and exported visibility are unchanged, and no downstream adaptation is needed.

Validation recovery: do not run `lcompile.py --all` concurrently with the delivery
dry run for this sandbox. Both rebuild the same `.lbuild` outputs, and one compiler
can temporarily fail to find a sibling that the other process is replacing.
The delivery dry run is the final sequential validation of the complete set.


## Earlier second reading (a previous round; superseded)

1. **Unchanged interfaces — PASS.** Diffed the parent against the repository and
   compared all 21 parsed existing declaration signatures byte for byte. Only the
   existing final theorem body changes; every existing definition body and visibility
   is unchanged. The added coordinate helper is private and packages supplied data.
   The two added parent imports are private. The recorded irreducibility commands
   are local; their change record describes the conservative preflight classification.
2. **Proof and trust — PASS.** Compiled each new module and the parent locally with
   lcompile.py. The only textual sorry in the delivery is the entire named theorem
   exists_affineCoordinateComparisonFamily. No forbidden declaration or hollow
   definition occurs. A scratch import with #print axioms verifies that
   perfectHomComparison_triangle uses only propext, Classical.choice and Quot.sound;
   the affine family and transport wrapper additionally use sorryAx, as reported.
   The parent closes one original hole by adding one strictly intermediate hole:
   this remains a decomposition, net zero, rather than an axiom-free target proof.
   The delivery's declaration probes check the complete set, including the parent.
3. **Split statement — PASS.** Read the full comparison-family statement and its
   sourced docstring proof, the supplied coordinate fields, the existing natural
   affine comparison and single-square object comparison, and the counit-pinned
   derived composition API. The remaining obligation is natural affine comparison
   plus its scalar-composition law, with no diagram, cocone, bottom identification
   or propagated target object. The parent proves those additional steps explicitly;
   it does not simply rename and apply its original statement. The family is true
   by the canonical counit/tilde construction, conjugated through the supplied hd
   and hH, whose middle factors cancel. Identity arrows force the same comparison
   unit; coincident labels retain all cross morphisms; zero models and zero rings
   add no nonzero or distinctness requirement. Re-read Stacks Tags 08DW, 06Y1 and
   0D5S. Independent LeanFinder searches for compatible affine scalar extension
   found the module-category pseudofunctor; Loogle found mapIso_trans and related
   generic transport results; grep of Mathlib, Sheaf and upstream sources found
   no theorem supplying the missing geometric composition law. Searches are in
   searches.jsonl. This remaining law is not a few-minute consequence of the
   object-only single-square API, which supplies no naturality or coherence.
4. **Route, imports, pruning — PASS after report repair.** Read the construction
   top down: K-flat scalar extension, the natural family, direct bottom comparisons,
   naturality transport, and the proved projection triangle supply all eight fields.
   All original public imports occur in public statements/definitions, and the
   added parent imports are proof-only. KFlatModuleBaseChange is public in the new
   affine module because its preservation proof terms occur in the public theorem
   type; it is not merely a proof-body dependency there. No module is pruned.
   The old direct affine-computation and derived-composition dependency nodes are
   now explicitly listed as no longer directly needed; they remain indirect
   dependencies. The unit sk-thm-picard-semicon has empty realized statement/step
   lists; no realized route is bypassed or changed.
5. **DAG agreement — PASS.** Checked all three records against their modules and
   verified that each proof_deps list equals the union of its proof steps' uses.
   The parent records the comparison family, K-flat extension, scalar reassociation,
   perfect-Hom transport and projection triangle. The new nodes carry sources,
   complete proof plans, search records, creation/blueprint/chapter/unit metadata,
   and Lean declarations matching the files. The projection triangle is proved
   by evaluating existing associativity and transporting projection equations;
   its helper choice eliminations read the fixed comparison's specification.

Changed the parent's four final simpa steps to unfold only scalar reassociation and
iso associativity, retaining local data instead of redundantly expanding α, β, θ,
γ and the extended models. The original failed the 60-second compile limit twice;
the repaired parent compiled without warnings in 52.8 seconds. No statement,
definition, import or mathematical proof route changed. Also completed the old
proof-dependency inventory under No longer needed. No additional hole was added
or removed during the second reading.


## Second reading by U2

1. **Interfaces — PASS.** Independently diffed the delivered parent against this
   repository and parsed its 21 existing declarations: every signature, public
   import and existing definition body is unchanged. Only the final existence
   theorem's proof body changes. The added coordinate abbreviation is private,
   uses supplied data and proves its natural identification. The other two modules
   are new. The local irreducibility attribute is covered by the change record and
   changes no exported declaration or target meaning.
2. **Proof and trust — PASS.** Compiled all three delivered files with lcompile.py
   in import order, without errors or warnings (44.4, 24.6 and 55.9 seconds).
   A separate scratch copy with explicit #print axioms also compiled: the projection
   triangle uses only propext, Classical.choice and Quot.sound; the affine family,
   transport wrapper and parent additionally use sorryAx. The only delivered sorry
   is the entire named exists_affineCoordinateComparisonFamily theorem. Checked
   every definition and private helper: no hollow definition, forbidden declaration,
   hidden partial-proof sorry or arbitrary existential witness chosen as data.
   One original hole is closed and one strictly intermediate hole added; this is
   a decomposition, net zero, rather than an axiom-free proof of the target.
3. **Remaining statement — PASS.** Read the full family statement, its docstring
   proof and node, derivedPullback_tilde_kFlat_natIso,
   nonempty_affineSquareKFlatModelIso, and the counit equation defining the fixed
   composition comparison. Read Stacks Tags [08DW](https://stacks.math.columbia.edu/tag/08DW),
   [06Y1](https://stacks.math.columbia.edu/tag/06Y1) and
   [0D5S](https://stacks.math.columbia.edu/tag/0D5S). The affine computation is
   transported through supplied hd and hH; their intermediate inverse factors
   cancel. The fixed counit equation identifies successive derived comparisons,
   while scalar reassociation identifies the underived tensors. The statement
   removes the diagram, cocone, P,Q, bottom identifications and propagated object
   triangles; the parent actually constructs these, so this is not a renamed item.
   Checked identity arrows (the same scalar and derived unit laws), coincident
   labels (the induced category retains cross morphisms), zero complexes and zero
   rings/empty spectra (no nonzero premise occurs). No flatness, boundedness or
   directedness is silently required. Independent LeanFinder, Loogle and grep
   queries used different words and are recorded in searches.jsonl. Inspected the
   resulting Mathlib sheaf pullback associativity and upstream tildePullbackIso:
   they are underived APIs, not the missing counit-pinned localized family law.
   The existing single-square theorem supplies no family coherence. Closing this
   remaining law requires substantial natural comparison construction, not a
   few-minute application of an existing theorem.
4. **Route, imports and pruning — PASS.** Followed the parent from the comparison
   family to K-flat extended models, θ/θlim, direct bottom comparisons and α/β,
   then its finite-stage and cocone triangles. F.map_comp, C.w and Spec.map_comp
   supply precisely the required composite equations; the generic transport
   predicate uses naturality and the projection triangle. The latter evaluates
   the existing cc_assoc theorem through proof-only import all, without duplicating
   it. Public imports support the statement/definition APIs; the parent's added
   imports are proof-only. In the family module KFlatModuleBaseChange is needed
   publicly because its preservation proof appears in the theorem's type.
   No shorter proved geometric comparison was found. No module is pruned.
   No longer needed lists both removed old direct dependencies; they remain
   indirect dependencies of the family. The unit sk-thm-picard-semicon has empty
   realized statement/step lists, so no realized route is bypassed.
5. **DAG — PASS.** Compared all three node records with their Lean declarations.
   Each proof_deps list equals the union of its proof steps' uses. The parent node
   changes only proof, proof_deps and proof_origin. The new nodes record the
   sourced affine-family argument and the proved projection triangle, with the
   required creation, chapter, unit, blueprint, search and Lean metadata.
   The parent steps match the actual specializations and categorical transport;
   the triangle step matches evaluation of existing associativity and explicit
   equality transport.

This second reading changed no Lean proof, signature, definition, import or node:
no repair was needed. It added this independent review and fresh search evidence.
No additional hole was closed or added. Scratch audit copies are outside the
set delivered by deliver3.py.
