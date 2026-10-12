## What changed

Proved `AlgebraicGeometry.noetherian_quasicoherent_submodules` with its existing signature
unchanged. The proof evaluates subobject arrows on a finite affine cover, stabilizes their
linear-map ranges using Mathlib's finite-module ACC, and detects global equality on the
cover. Maximal elements follow from the monotone-chain characterization of `WellFoundedGT`.
The ideal-sheaf clause is proved independently with Mathlib's affine-cover extensionality.

Added two fully proved modules:
`Sheaf.AlgebraicGeometry.CoherentAffineSectionsFinite` constructs finite local presentations
from coherence and applies the proved source-library affine-sections theorem;
`Sheaf.AlgebraicGeometry.QuasicoherentSubobjectAffineCoverExt` proves equality by extending
surjectivity to a basic-open basis. Its smaller subobject need not be quasi-coherent.
No existing statement or definition was changed, and no other held module was adapted.
The item's new helper imports are proof-only. The original public imports stay unchanged.

The original node's proof route and proof dependencies now describe these Lean proofs.
The unit `sk-thm-p1` and its realized statements and steps are unchanged. The finite affine
cover argument handles an empty scheme, using the supremum of an empty family of natural
numbers. The equality helper allows an empty cover and arbitrary cover cardinality.
The finite-sections helper requires neither Noetherianness nor an inhabited affine open.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.noetherian_quasicoherent_submodules`
(node `lem-weil-pbc-noetherian-acc-quasi-coherent`): 1 of 1 original sorries closed.

Also fully proved `AlgebraicGeometry.Scheme.Modules.coherent_affine_sections_finite`
(node `lem-weil-pbc-coherent-affine-sections-finite`) and
`AlgebraicGeometry.Scheme.Modules.quasicoherent_subobject_eq_of_affine_cover`
(node `lem-weil-pbc-quasicoherent-subobject-affine-cover-ext`). The existing private presentation
helper is reused through a proof-only `import all`; no local copy is delivered. No sorries are left or added; no holes are split off.
The source-library `finitePresentation_sections_of_isFinitePresentation` is reused as a
proved declaration and attached to its own new node, rather than restated in Lean.

## No longer needed

Removed the proof-only import `Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`.
The proof no longer uses its bundled theorem
`AlgebraicGeometry.Scheme.Modules.quasicoherent_finite_type_affine`, node
`lem-weil-pbc-quasi-coherent-finite-type-affine`. It directly uses the already proved
source-library finite-presentation sections theorem through the new finite-sections helper.
This is pruning on this item's route; no claim is made that other targets cease to reach
that module.

The original direct proof dependencies `pqf-def-coherent`,
`def-weil-finitely-generated-module`, `def-weil-sheaf-of-modules-category`,
`lem-weil-pbc-module-restriction-open-immersion-colimits`, and
`lem-weil-pbc-affine-tilde-gamma-adjunction` are no longer direct dependencies of the main
node: its two concrete helper nodes carry the relevant lower theory. Coherence, finite
modules, sheaves of modules, and affine localization remain needed below these helpers.
The affine counit and restriction-colimit argument is replaced in the equality proof by
basic-open denominators and Mathlib's sheaf basis isomorphism test. No unit-level node or
step is bypassed, and no unused new-module import is retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect was found in the original statement. The planned successive
maximization over affines is unnecessary once the proved chain condition is converted to
`WellFoundedGT` using Mathlib. Equality detection actually requires quasi-coherence only
of the larger subobject, which the new helper states explicitly.

The coherent-to-finite-presentation construction already exists as private proof code in
`CoherentFiniteTypeLocallyNoetherian`. The second reader removed its copied helper and dummy
`Unit` argument, importing the existing proved helper with proof-only `import all`, as in
`ProjLineSerreVanishing`. No unproved bridge is added. The source theorem for affine
finite-presentation sections had no individual DAG node, so one is attached in this delivery.
All three delivered modules compile without warnings. The delivery tool's axiom probes
ran without detecting any axiom beyond `propext`, `Classical.choice`, and `Quot.sound`. The coherent-section construction
initially incurred repeated slice-site sheafification instance searches; registering those
instances locally reduced its compile from about 57 seconds to 11 seconds.

The imported Stacks text files are absent on this machine; the statements and short ACC proof
were checked against the online Stacks pages for Tags 01Y8, 01BV and 01PB, while the detailed
Lean constructions follow the existing fully proved source files cited in the new nodes.
LeanSearch returned an internal server error; the unavailable search is recorded alongside
successful LeanFinder/Loogle and source grep searches.

## New nodes

`lem-weil-pbc-coherent-affine-sections-finite`: finite affine sections of a coherent module,
proved in `CoherentAffineSectionsFinite.lean` without Noetherian hypotheses. The construction
uses finite local generators and finite-type kernels to build finite presentations.

`lem-weil-pbc-quasicoherent-subobject-affine-cover-ext`: equality detection for an inclusion
into a quasi-coherent subobject, proved in `QuasicoherentSubobjectAffineCoverExt.lean` using
basic-open denominators and the sheaf isomorphism test on a basis.

`lem-weil-pbc-finite-presentation-affine-sections`: attaches the existing, proved source
`AlgebraicGeometry.Scheme.Modules.finitePresentation_sections_of_isFinitePresentation`
in `WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent`. No source module is changed.

No change record is needed: existing signatures, definitions and visibility are unchanged.

## Returned duplicate-helper repair

The landing tool refused the copied private presentation theorem because the library already
states it in `CoherentFiniteTypeLocallyNoetherian`. The first repair added a dummy `Unit` tag;
this second reader removed that workaround and the copied theorem. A proof-only `import all`
now makes the existing private theorem available, and its original untagged call is reused.
No other module is adapted and no existing interface changes.

## Earlier second reading (a previous round; superseded)

1. **Statements and interfaces.** Compared the delivered item with the repository version and checked
   all existing declaration signatures byte for byte. Verdict: unchanged; the target statement and
   definitions remain exactly as in the repository.
2. **Proof validity.** Compiled all three delivered modules with `lcompile.py`; no errors, warnings,
   `sorry`, forbidden declarations, or hollow definitions were found. The proofs use only the allowed
   upstream axioms (as also checked by the delivery probes). Verdict: pass.
3. **New statements.** Checked both helper statements against their uses and edge cases, including
   empty schemes and empty affine covers. They are true, strictly simpler than the target, and do not
   duplicate an existing library declaration. Verdict: pass.
4. **Pruning and route.** Confirmed that proof-only imports are plain imports, the removed finite-type
   affine import is no longer used, and the realized unit `sk-thm-p1` route is retained through the
   target node and its helper nodes. Verdict: pass.
5. **DAG agreement.** Compared declarations, proof steps, dependencies, origins, and new-node metadata
   with the Lean proofs and report. Verdict: pass.

Changed only the report by adding this second-reading record; no Lean proof or node repair was needed.

## Second reading by G1

1. **Existing interfaces — pass after whitespace repair.** Read the repository diff and
   compared the complete `noetherian_quasicoherent_submodules` signature byte for byte.
   Removed one extra space before `:=`; the signature now agrees exactly, including all
   three clauses, `IsNoetherian`, coherence, and the quasi-coherence hypotheses on chains
   and sets. No existing definition or public import changed. The helpers are new modules.
2. **Proof and axioms — pass.** Compiled all three delivered modules through `lcompile.py`
   with no errors or warnings. Scratch copies with `#print axioms` checked the main theorem,
   both public helpers, the section-range definition, and the finite-cover theorem: each
   uses only `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, forbidden construct,
   or hollow definition occurs. The range definition is an actual linear-map range;
   classical selections in the proof choose proved generators and stabilization indices.
3. **New statements and duplication — repaired, then pass.** No statements are split off.
   Read coherence in `Coherent.lean`, the affine finite-presentation theorem in
   `WeilConjectures/AlgebraicGeometry/Modules/FiniteDescent.lean:97`, and the denominator
   lemma in `WeilConjectures/Mathlib/AlgebraicGeometry/Modules/Tilde.lean:112`. The finite
   section helper needs no Noetherian assumption: coherence supplies finite-type kernels
   after finite generator reindexing. Equality uses quasi-coherence only of H; monicity
   into F transfers the section-image equality to surjectivity, and invertibility of f
   on D(f) transfers surjectivity to the basic-open basis. Checked the empty scheme,
   empty cover, zero module, D(0), D(1), and arbitrary cover cardinality. The new upstream
   node records an existing theorem rather than restating it. Fresh Loogle search for
   `"IsFinitePresentation", "GeneratingSections"` found no hits; LeanFinder search for
   affine-cover subsheaf equality found ideal-sheaf extensionality, already used in the
   ideal clause, but no replacement for the module helper. Source grep found the copied
   private kernel-presentation theorem. Removed its dummy Unit parameter and entire
   local copy; now reuse the original through proof-only `import all`, matching the
   established `ProjLineSerreVanishing` import pattern and the actual return instruction.
4. **Route and pruning — pass.** Read `dag/units/sk-thm-p1.json` and its realized statement
   and four step lists; none is edited or bypassed. The argument remains finite affine
   stabilization below that unit. The finite supremum is zero when the cover is empty;
   no inhabited-cover hypothesis is introduced. The section-range monotonicity follows
   subobject factorization; each maximal-element conclusion follows from the proved
   chain condition using `wellFoundedGT_iff_monotone_chain_condition`. Ideal-sheaf
   extensionality separately avoids assuming coherence of the structure sheaf. All
   original direct dependencies removed from the main node are named above. The new
   import of `CoherentFiniteTypeLocallyNoetherian` is actually used for its private
   presentation lemma; the two helper imports and order imports are proof-only.
5. **DAG agreement — pass after repair.** Read all four delivered nodes, the old main node,
   the finite-module ACC leaf, and the basic-open localization node. Checked that each
   `proof_deps` is the union of the step citations and every cited node exists. New
   declarations agree with their Lean records; source, origin, creation, chapter, unit,
   searches, and blueprint ancestry are present. Updated the finite-sections node's
   construction step and origin to say explicitly that the existing private lemma is
   imported and reused. Existing main-node edits stay within stage-3-owned fields.

Changed the finite-sections proof import and removed its duplicated tagged private theorem,
restored exact target-signature whitespace, updated the corresponding node proof/origin,
and corrected this report's account of the returned repair. Closed 1 original hole, added
0 holes; no statement or definition repair and no forced adaptation was needed.
