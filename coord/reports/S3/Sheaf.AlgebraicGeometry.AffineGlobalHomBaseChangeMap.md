## What changed

This is a partial data-normalization repair, not a new proof of a former hole.
The second reader replaced `affineDerivedExtension` by the concrete source-library
`ModuleCat.extendScalars.leftDerivedFunctor` and replaced
`affineDerivedExtensionAdjunction` by the descent of the specified
`ModuleCat.extendRestrictScalarsAdj`, transported along the unit-compatible exact
restriction comparison. `exists_affineDerivedExtension` keeps its signature and
now follows from these definitions. The original sheaf-derived-category instance
parameter is retained explicitly in the constructed definition body.

The new module `Sheaf.Algebra.Homology.ExtensionKFlatQuasiIso` exposes the proved
property `ModuleCat.extendScalars_preservesKFlatQuasiIso`. It packages the existing
private `CochainComplex.scalarExtension_quasiIso_of_kFlat` by a proof-only
`import all`; no scalar-extension argument is repeated. The public property bridge
is needed because private helpers cannot occur in an exposed definition body.
The item publicly imports this property module and the derived-adjunction and
flat-resolution modules used by its exposed concrete definitions. A local
irreducibility attribute keeps their resolution machinery out of unrelated
elaboration; it is not exported to downstream modules. The final map definition
uses local transparency settings so its elaboration respects those attributes.
The diagnostic profiler copy compiled in 45.8 seconds. The end-of-file linter
waits for pending kernel checks, so its reported time includes that work. The
actual delivered set compiled without warnings in 2.7 and 56.8 seconds.

The change record is
`coord/changes/affineDerivedExtensionAdjunction-concrete.md`. It enumerates the
users and reopens semantic review for targets using the changed scalar data.
No target text is edited. The pullback shared-counit repair remains open.

## Proved and sorry left

Original local holes closed: none (the repository module already has zero).
New holes added: none. The new property theorem
`ModuleCat.extendScalars_preservesKFlatQuasiIso` is proved.
The existing `exists_affineDerivedExtension`, `exists_canonicalTensorHomAdjunction`,
and `exists_globalHomPullbackComparison` remain proved; all definitions have bodies
without `sorry`. This delivery repairs scalar adjunction data and contributes no
net hole closure. There are no split-off unproved statements.

Remaining non-hole repair: `AlgebraicGeometry.canonicalPullbackAdjunction` still
selects a fresh counit through `exists_derivedPullbackComposition`. Repairing it
requires shared upstream counit/composition changes and adaptation of the model
unit equations and the independently chosen `schemeHomPullbackAdjunction`.
This delivery does not claim to have repaired that part of the queue item.

## No longer needed

The item's direct proof-only import
`Sheaf.Algebra.Homology.MixedTensorKFlatQuasiIso` is replaced by the public property
module. The old direct proof dependency `lem-pc-mixed-tensor-kflat-quasi-iso` is
replaced by `lem-pc-extension-kflat-quasi-iso`; mixed tensor remains an indirect
proof dependency through the reused existing private theorem.
No module is claimed pruned from target closure, and no other old proof dependency
is removed. The three other old dependencies and their argument steps stay.

## Where the brief, the DAG or earlier work was wrong

Repair of reviewer C3: corrected `lem-pc-extension-kflat-quasi-iso` to cite
`lem-pc-mixed-tensor-kflat-quasi-iso` in both the proof step and `proof_deps`,
and replaced the step text exactly as requested. The homology-equivalence
statement does not assert preservation of the specified morphism. The reused
private helper instead specializes clause (i) of the mixed-tensor theorem and
transports the specified arrow through natural comparison isomorphisms.
No Lean statement, definition, proof, or import changed in this repair.

The first report falsely called both canonical adjunction choices normalized and
claimed the undetermined-data repair was complete. Its only source change was an
unsupported comment. The scalar existential did not constrain adjunction data;
a minus-one twist preserves existence but changes the literal comparison arrow.
The pullback normalization is only relative to the freshly selected composition
counit, not the original presentation of `derivedPullback`.
The report and module repair note now describe the partial repair accurately.

## New nodes

`lem-pc-extension-kflat-quasi-iso` records the proved public preservation-class
bridge to the existing private lemma, in its own new module. Mathlib searches
used grep, Loogle, Lean Finder, and LeanSearch (the latter was unavailable).
Library searches found the existing private implementation, which is reused.
The existing affine global-Hom node now records the concrete scalar construction.
Change record: `coord/changes/affineDerivedExtensionAdjunction-concrete.md`.

## Earlier second reading (a previous round; superseded)

1. Compared the complete delivered item with the repository using diff. The first
   worker changed only a comment, with no repair. Every existing textual signature
   is retained; the two scalar definition-body changes are recorded in the change
   record. Their original implicit sheaf instance parameter is explicitly retained.
   No hypothesis is added or conclusion weakened. The scalar normalization change
   requires target semantic review; the record expressly reopens it.
2. Read each body and checked the forbidden constructs and local holes. The module
   and property bridge compile locally with no errors or warnings. There is no
   `sorry`, axiom declaration, unsafe code, opaque declaration, implemented_by,
   extern, or arbitrary data chosen from a new unproved existence theorem. The
   scalar adjunction is an explicit descent using the fixed counit and unit.
   Axiom checks and downstream single-file compilation are recorded below.
3. No unproved statement is split off. The property bridge is exactly the class
   needed for the explicit construction; its proof reuses the library's private
   scalar-extension lemma rather than reproving it. Zero rings, zero complexes,
   identity maps, and non-flat maps are covered without extra assumptions.
4. The old global-comparison proof is already a genuine reduction through the
   normalized internal-Hom and sections comparison lemmas. Its equations determine
   the selected global map relative to the existing fixed adjunctions. The tensor-Hom
   adjunction is constructed by mkOfHomEquiv with the normalized evaluation family.
   The unit record sk-thm-picard-duality has empty realized fields; no realized
   unit/step or chapter route is bypassed. No module is claimed pruned. The removed
   direct mixed-tensor import and dependency are listed above.
5. The existing node records the three proof routes actually used. Its scalar step
   and proof dependency now name the property bridge and the concrete descent.
   The new node records the bridge's existing private implementation and includes
   its source, complete argument, search results, Lean signature, and provenance.

Changed on second reading: removed the false comment/report claims, constructed
scalar derived extension and its specified adjunction, reused the existing private
preservation proof through a public property bridge, preserved the implicit API,
updated the DAG, and recorded the definition change and its users. The remaining
pullback shared-counit defect is explicitly reported.

Verification so far: the delivered modules compiled without warnings (2.7 and
56.8 seconds). A scratch import of the built delivery printed axioms for all 16
existing item declarations and the new property theorem: every list is exactly
`propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`. The elaborated
`#check @` outputs of both scalar definitions and the preserved existence theorem
match the original baseline, including the original section instance parameters.

All six direct users compiled unchanged against copies of the repaired module's
actual build artifacts in the scratch overlay: AffineExtensionModelUnit (31.6 s),
AffineExtensionSectionsModelFactorization (39.7 s),
AffineExtensionSectionsModelMate (15.0 s), AffineExtensionSectionsUnit (11.8 s),
AffineSectionsBaseChangeMate (13.3 s), and
AffineGlobalHomBaseChangeFactorization (28.3 s). No adaptation is required.
The delivery dry run printed OK and passed the compilation, axiom probe, and
preflight checks. Review class: CODEX, because this is a recorded definition-data
repair with a new proved property module/node, rather than a proof-only delivery.

## Forced adaptations

- `Sheaf.AlgebraicGeometry.AffineSectionsSquareComparisonCoherence`
  (`lean/Sheaf/AlgebraicGeometry/AffineSectionsSquareComparisonCoherence.lean`, unclaimed) is included as a forced adaptation. The reviewer reported an original theorem-elaboration timeout against the concrete affine-derived extension (A10). Immediately before the theorem docstring, the changed line adds `set_option maxHeartbeats 800000 in` and the explanatory comment `-- The concrete affine-derived extension requires extra elaboration heartbeats.`; the theorem signature and body are unchanged. This adaptation is required for the module to compile against the repaired affine-derived extension.

## Earlier second reading (a previous round; superseded)

1. Compared both existing delivered modules with repository sources using diff
   and the declaration-table signature comparison. Every existing signature is
   unchanged, with no declaration removed or added in either existing module.
   The only existing definition-body changes are the two scalar constructions
   covered by the change record. The retained sheaf-derived instance is visible
   in the elaborated signatures. No target text or hypothesis changed.
2. Compiled all three delivered modules in dependency order: 2.6, 51.5 and
   54.7 seconds, without errors or warnings. Read every changed body and scanned
   the delivered Lean files for forbidden constructs and sorry: none occur.
   A fresh scratch import against the actual current delivery artifacts printed
   axioms for all 16 item declarations and the property theorem; every list is
   exactly propext, Classical.choice, Quot.sound. The scalar data come from the
   concrete derived construction, not an arbitrary existential witness.
3. There are no split-off unproved statements. Read the private implementation
   reused by the new preservation theorem and its class definition. The bridge
   packages that implementation exactly, without flatness or boundedness
   assumptions. Zero rings and complexes and identity maps introduce no exception.
   Fresh msearch grep, Loogle and Lean Finder searches plus rg on both library
   roots found the existing private proof and local class wrappers, but no public
   preservation theorem to use instead. The proof reuses the private result.
4. Read the complete top-level assembly, its two normalized helper routes and
   the scalar derived-adjunction and exact-restriction comparison definitions.
   The shortest existing scalar proof is reused. Public imports provide exposed
   definition data or signature instances; the private implementation import is
   proof-only. The old direct mixed-tensor dependency removal is fully reported;
   no target-closure module is claimed pruned. The unit's realized fields are
   empty, and no realized statement or step is bypassed.
5. Compared the existing node and read the new node: proof steps, dependencies,
   provenance, verbatim new Lean statement, source and searches agree with the
   code. The remaining pullback shared-counit defect is explicitly left open.
   The downstream adaptation changes only a theorem-local heartbeat option;
   the original against the current changed artifacts fails deterministically
   at whnf with the default 200000 heartbeats, while the adaptation compiles.

Changed in this reading: corrected the change record's conflicting claims that
no downstream file was adapted, and added this fresh independent verification.
No Lean proof or definition needed further repair. Original holes closed: none;
new holes added: none. The repair is partial and has zero net hole closure.

## Forced adaptations

### Sheaf.AlgebraicGeometry.AffineSectionsSquareComparisonCoherence
Original against changed dependencies failed:
```
/tmp/forced-adaptation-a800k82v/lean/Sheaf/AlgebraicGeometry/AffineSectionsSquareComparisonCoherence.lean:31:0: error: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.

(with the modules compiled into /tmp/forced-adaptation-a800k82v/.lbuild) [22.6 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

## Second reading by S3

1. Compared all three delivered modules with the repository. Declaration-table
   comparison finds no changed existing signature in either existing module.
   Read both concrete scalar definition bodies against the change record's Old
   and New sections: they agree. No target, hypothesis or conclusion changed.
   Verdict: pass for this recorded partial definition-data repair; target semantic
   review remains reopened, and the shared pullback-counit repair remains open.
2. Read every declaration body, scanned all delivered Lean for forbidden
   constructs and local sorry, and compiled the three modules in import order.
   The first run hit the 60-second main-file timeout; an unchanged retry compiled
   cleanly in 3.3, 56.2 and 49.3 seconds. No new data are chosen from an unproved
   existence statement. The scalar functor uses leftDerivedFunctor directly;
   the specified underived adjunction descends with leftDerivedFunctorCounit
   and rightDerivedFunctorUnit, then uses the unit-compatible exact-restriction
   isomorphism. Verdict: pass, with a narrow main-file compile timing margin.
3. No unproved statement is split off. Read PreservesKFlatQuasiIso and the private
   scalarExtension_quasiIso_of_kFlat implementation: the new public bridge
   packages preservation of the actual mapped arrow. The mixed-tensor clause (i),
   single-complex comparison, tensor unitor and naturality justify this for zero
   complexes, zero rings, identity maps and non-flat maps alike. Fresh grep,
   Loogle and Lean Finder searches and rg on both library roots found the private
   proof and local wrappers, with no public replacement. Verdict: pass.
4. Read the complete global-comparison assembly and its existing helper routes.
   It applies normalized internal-Hom pullback and affine sections pushforward
   normalization; the tensor-Hom adjunction is constructed from the normalized
   Hom equivalence. Concrete scalar descent reuses the shortest existing route.
   Public imports support exposed definition data; import all of the private
   helper is proof-only. No longer needed lists the replaced direct mixed-tensor
   import/dependency, and no closure pruning is claimed. The unit record
   sk-thm-picard-duality has empty realized fields; its route is preserved.
   Verdict: pass.
5. Compared the existing node and read the new node, checking proof steps,
   dependencies, provenance and verbatim Lean statement. The C3 return is repaired
   exactly: the new node cites lem-pc-mixed-tensor-kflat-quasi-iso, not the
   homology-equivalence statement, and describes the natural isomorphism of arrows.
   The changed item's other three proof dependencies stay. The forced adaptation
   changes only maxHeartbeats and its comment, with unchanged statement and proof.
   Verdict: pass, subject to the delivery tool's fresh counterfactual check.

Changed in this reading: added this independent review and fresh verification.
No further Lean or DAG repair was needed. Original holes closed: none (0 of 0);
new holes added: none; no unproved split-off statement; no module pruned. This
remains a partial scalar-data repair, not completion of the pullback-data repair.

Fresh axiom scratch import against this reading's actual built artifacts: all 16
item declarations and ModuleCat.extendScalars_preservesKFlatQuasiIso use exactly
propext, Classical.choice, Quot.sound, with no sorryAx. The elaborated scalar
signatures retain both original derived-category section parameters.

## Forced adaptations

### Sheaf.AlgebraicGeometry.AffineSectionsSquareComparisonCoherence
Original against changed dependencies failed:
```
/tmp/forced-adaptation-olz8gb2w/lean/Sheaf/AlgebraicGeometry/AffineSectionsSquareComparisonCoherence.lean:31:0: error: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.

(with the modules compiled into /tmp/forced-adaptation-olz8gb2w/.lbuild) [23.9 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
