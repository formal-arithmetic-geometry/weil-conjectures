## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.StrictLocalInjectiveSourceDerivedRestriction`
with a compiling reduction. Its theorem signature, original docstring, and existing public import are unchanged.
The new proof-only import is `Sheaf.AlgebraicGeometry.StrictLocalComplexSectionsMate`.

The proof installs K-injectivity of the termwise direct image of the given bounded-below
injective complex. It applies a generic localized-Hom/germ compatibility on the base, then
a separate complex-sections/mate compatibility, and finally the existing cone-leg clause of
`injectiveSections_strictLocal_comparison`. Unfolding the two explicit source comparisons
and reassociating identifies the resulting factors with the original source isomorphism.

Added two modules, each with one remaining theorem, and updated the parent node's proof,
proof_deps and proof_origin. The first module constructs the raw localized sections
isomorphism and the degreewise strict-local restriction map. Naturality of the latter is
proved as the named theorem `strictHenselizationSectionRestriction_naturality` from adjunction-unit, presheaf-map and terminal-sections naturality. These definitions
contain no sorry and choose no arbitrary witness. The second module uses these maps in a
statement about the mate on the actual complex of base sections.

Sources checked: https://stacks.math.columbia.edu/tag/03Q8 and
https://stacks.math.columbia.edu/tag/03Q9, especially the final injective-complex paragraph
of 03Q9. The precise comparison of these explicit Lean constructions is an agent-written
compatibility argument from those sources and the library's generic derived-adjunction
factorizations. LeanFinder, Loogle and grep searches ran; LeanSearch returned HTTP 500 and
is recorded as unavailable. The library's `Adjunction.derivedPlus_mateEquiv_app_fac` is
relevant to the remaining mate compatibility, but does not include its neighbourhood
sections and target homology transports.

The unit record `sk-prop-h2` has empty realized lists, and neither new statement bypasses a
unit statement or step. No existing definition, statement, signature or visibility changed.
No other existing module was adapted.

## Proved and sorry left

Closed the hole in
`AlgebraicGeometry.Etale.strictLocalInjectiveSourceIso_derivedRestriction`
(node `lem-weil-pbc-strict-local-injective-source-derived-restriction`).
The item's module now contains no sorry.

Added these two holes, each exactly a named public theorem with `:= by sorry`:

- `AlgebraicGeometry.Etale.sourceLocalizedSectionsIso_germ`, in
  `Sheaf.AlgebraicGeometry.StrictLocalLocalizedHomGerm`, node
  `lem-weil-pbc-strict-local-localized-hom-germ`.
- `AlgebraicGeometry.Etale.strictLocalComplexSectionRestriction_mate`, in
  `Sheaf.AlgebraicGeometry.StrictLocalComplexSectionsMate`, node
  `lem-weil-pbc-strict-local-complex-sections-mate`.

This is a decomposition, not a proof free of sorry dependencies: one upper hole closed,
two strictly separate lower holes added, net minus one hole closed. The first lower statement
has no direct image, fibre or mate and applies to any K-injective complex on S; the second
has no derived Hom class or canonical germ and starts with cohomology of a sections complex.
Neither is the original statement renamed or repackaged.

Edge cases were checked mathematically before stating the lemmas: boundaries restrict to
boundaries; zero complexes give zero maps; negative integer degrees use the same shift and
homology comparisons; no acyclicity or injectivity of the complex at the limit is assumed.
A geometric point on an empty base cannot exist, while an empty fibre has zero sections.
Only exact strict-local sections and the original representative's K-injectivity are used.
The two new modules compiled in 39.9 and 23.7 seconds, and the repaired parent compiled
in 42.6 seconds, without errors or warnings. The parent previously exceeded the 60-second
limit at the final `unfold`/`dsimp` step. Replacing it with `delta` on the two source
comparison definitions followed by the explicit isomorphism-projection simplifications
avoids the expensive broad definitional simplification. This changes only the proof.
The new comparison definitions remain irreducible outside explicit unfolding. The named
naturality theorem supplies the proof required by the restriction natural transformation.
The required `deliver3.py ... --no-push` printed OK: the modules compile and preflight
passes except for the second reading, which the next worker writes. Nothing was pushed.
The two new modules passed the axiom probe. The parent axiom probe exceeded 60 seconds;
the tool reports that the merge runs it again. Thus the parent probe is not certified by
this local dry run, although its ordinary compilation passed. No definition or existing
signature was changed to address this performance issue.

## No longer needed

Removed these redundant direct proof imports from the parent:

- `Sheaf.AlgebraicGeometry.EtaleInjectiveSectionsComparison`
- `Sheaf.AlgebraicGeometry.StrictHenselizationRestriction`
- `Sheaf.AlgebraicGeometry.StrictLocalCohomologyGerms`
- `Sheaf.AlgebraicGeometry.StrictLocalMateProjectionData`
- `Sheaf.AlgebraicGeometry.StrictLocalNeighbourhoodGeometry`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction`

Their required declarations remain available through the existing public source-comparison
import and the new complex-sections-mate import. No existing node or module is pruned from
the transitive argument. These are redundant direct imports, not whole-module pruning.
A redundant new direct import of `Sheaf.AlgebraicGeometry.StrictLocalLocalizedHomGerm`
was also removed during development; the mate module exposes it for its statement.

The canonical-germs, strict-henselization-restriction, neighbourhood-geometry, mate-target
and derived-adjunction proof steps now belong to the new compatibility nodes. The parent
retains the source-comparison and injective-sections-comparison nodes.

The old parent proof dependencies absent from the new parent's `proof_deps` are:

- `def-weil-pbc-canonical-derived-cohomology-germs`
- `def-weil-pbc-strict-henselization-restriction`
- `def-weil-pbc-strict-local-mate-projection-data`
- `def-weil-pbc-strict-local-neighbourhood-geometry`
- `prop-weil-pbc-derived-inverse-image-adjunction`

These are redistributed to the lower compatibility nodes, not pruned from the
transitive proof or target import closure.

## Where the brief, the DAG or earlier work was wrong

The parent node's single prose step combined two different comparison problems without
named Lean interfaces: localization of Hom classes versus the canonical germ, and the
sections-complex restriction versus the derived mate. The delivery makes these separate
and gives a complete Lean combination of them with the existing sections naturality theorem.
No statement was found false and no source hypothesis was added or removed.

The local checkout contains only the literature lists, so the two Stacks tags were read
on the official site. `blueprint_refs.py ancestor` returned None for the already split parent;
following the recorded blueprint.from chain gives the imported ancestor
`prop-weil-pbc-strict-henselization-stalk-formula`, used by both new nodes. The blueprint
search for "injective complex" found generic exchange and support lemmas, but none states
either concrete strict-local compatibility.

## New nodes

`lem-weil-pbc-strict-local-localized-hom-germ` records the generic factorization of a canonical
source germ through cohomology of an actual complex of neighbourhood sections. Its module
constructs the comparison and degreewise restriction explicitly and proves their naturality.
Its only sorry is the compatibility of localized Hom evaluation with that restriction.

`lem-weil-pbc-strict-local-complex-sections-mate` records the mate compatibility starting
from those base sections. It separates the derived adjunction and Leray computation from
all free-sheaf Hom and canonical-germ constructions. Its right-hand side contains the
underived stage sections comparison, termwise cone restriction, and limit sections unit.

Both nodes have complete proof sketches, source places, searches, verbatim Lean signatures,
and the same chapter/unit as the parent. No change record is needed: all existing interfaces
are preserved and the import added to the original module is proof-only.

## Second reading by J3

1. Compared every delivered module with the repository version. Only the parent
   exists there; its existing declaration signature is byte-for-byte unchanged,
   with no definition, hypothesis, conclusion, or visibility change. The two other
   modules are new. Restored the parent's original docstring; its added explanation
   belongs in this report. No change record is required.
2. Compiled all three modules locally in dependency order: no errors or warnings.
   Read every construction and the complete reduction. No forbidden declarations,
   hollow definitions, arbitrary existence witnesses, or hidden sorry occur. The
   two listed compatibility theorems are the only new holes. A scratch module
   importing the exact sandbox compiled objects printed axioms for all seven
   delivered declarations: the three comparison theorems use only propext,
   Classical.choice, Quot.sound and sorryAx; the naturality theorem and all three
   constructions use only the three permitted axioms. This independently checks
   the parent's axioms despite the earlier full-probe timeout.
3. Read both new statements, their docstring proofs, nodes, and explicit maps.
   Verdict: true compatibility statements and strictly separate parts of the
   argument, not a renaming of the parent. The germ statement is for an arbitrary
   K-injective representative on S; the mate statement begins with actual complex
   sections and contains no canonical germ. Checked zero complexes/classes,
   negative degrees, arbitrary representative isomorphisms, and empty fibres.
   Neither statement asserts acyclicity of the limit pullback or invertibility
   of the mate, so neither requires quasi-compactness or quasi-separatedness.
   Read Stacks Tags 03Q8 and 03Q9 on the official site. Their comparison maps
   motivate the argument; 03Q9's isomorphism conclusion has additional qcqs
   hypotheses and is not applied here. Repeated LeanFinder, Loogle and grep with
   different queries. Free-sheaf evaluation results and the generic derived-mate
   factorization are available, but do not state these concrete compatibilities.
   Also read SourceDerivedSectionsNaturality (neighbourhood arrows only),
   StrictLocalMateProjectionFormulas (depends downstream on this item), and
   StrictLocalBaseChangeModelGlobalHomology (invertibility with qcqs hypotheses).
   None closes either hole directly; neither is reasonably closed in a few minutes.
4. Reviewed the reduction from the top: K-injectivity, germ factorization, mate
   compatibility, existing cone-leg comparison, and explicit source-iso unfolding.
   All imports are needed for statements/definitions or the proof and have the
   appropriate public/plain visibility. Added the exact five old proof-dependency
   IDs absent from the new parent's list to No longer needed, distinguishing their
   redistribution from pruning. No whole module is pruned. sk-prop-h2's realized
   statement and step lists are empty; no realized unit route is bypassed.
5. Checked node signatures against the Lean, the proof steps and the union of their
   uses against proof_deps, and the proof origins, sources, searches, blueprint,
   chapter/unit, created and lean fields of both new nodes. Verdict: consistent
   with the reduction and remaining holes. Existing node statement fields remain
   unchanged. This delivery closes one upper hole and adds two lower holes: a
   decomposition, net minus one, not a completed proof without sorry dependencies.

Second reading restored the parent docstring, completed the old dependency list,
and recorded the independent review and axiom checks. Two delivery compiles hit
the 60-second timeout under concurrent load. Replaced the parent proof's local
bounded-below wrappers M and L by explicitly typed raw cochain complexes;
boundedness now comes from J.property and is transported by the termwise functors.
This avoids repeated wrapper unfolding and the revised proof compiled in 47.4 s
in the scratch check (line wrapping then repaired). The mathematical reduction,
all signatures, and all node dependencies are unchanged.

Final second-reader dry run printed OK: all three modules compile cleanly, all
three full declaration/axiom probes completed without a timeout note or forbidden
axiom, and stage-3 preflight passes (CODEX because it adds nodes and modules).
