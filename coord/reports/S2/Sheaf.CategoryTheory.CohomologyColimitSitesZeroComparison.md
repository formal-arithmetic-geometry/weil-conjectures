## What changed

Proved `CategoryTheory.cohomology_colimit_sites_zero_comparison_injective` with its
signature unchanged. Its proof now represents a kernel element at a stage, evaluates
the degree-zero class as a section, detects zero at a later stage, uses injectivity
of degree-zero evaluation, and applies the colimit transition equation.
A private proved lemma handles the endpoint equalities encoded by `Arrow.mk`.
The existing public imports are preserved. Added proof-only imports of
`Mathlib.CategoryTheory.Filtered.Final`, `SiteCohomologyZeroSections`, and
`VaryingSiteSectionsZeroDetection`.

Added three modules and corresponding nodes. `SiteCohomologyZeroSections` defines
identity-generator evaluation and proves its injectivity, zero preservation and
naturality directly from Mathlib's Ext-Hom, sheafification, free-forgetful and
Yoneda equivalences. `VaryingSiteSectionsZeroDetection` proves the outer comparison:
Q-coverings are finite images, the existing fixed-site abelian section comparison
is an isomorphism, and the filtered group-colimit equality criterion supplies a
later zero inverse-image section. `VaryingSiteInverseImageZeroDetection` isolates
the remaining inner inverse-image section argument, without Ext, cohomology maps,
a group diagram D, a group cocone c, or a colimit K of the sheaf system.

Updated the item's DAG proof and proof dependencies to the implemented argument.
All four modules compile using lcompile.py, with no warnings.
No target, existing definition, theorem signature, or public import changed.

## Proved and sorry left

Proved in the item:
`CategoryTheory.cohomology_colimit_sites_zero_comparison_injective`
(node `lem-weil-pbc-colimit-sites-zero-comparison-injective`). The item's sole sorry
is removed. One old hole is closed and one new hole is added: this is a
decomposition, with zero net reduction from these changes, not a completed
axiom-free proof of the item.

Also proved:
`CategoryTheory.siteCohomology_zero_section_properties`
(node `lem-weil-pbc-object-cohomology-zero-evaluation`) and
`CategoryTheory.varyingSite_sections_zero_detection`
(node `lem-weil-pbc-varying-site-sections-zero-detection`).

The only sorry introduced or left in delivered modules is
`CategoryTheory.varyingSite_inverseImage_zero_detection`
(node `lem-weil-pbc-varying-site-inverse-image-zero-detection`). It is exactly
`:= by sorry` in its own module, with a detailed source proof in its docstring.
The outer proof also uses the already-stated
`CategoryTheory.siteFilteredColimit_sections_isIso`, which remains an existing
open dependency rather than a theorem reintroduced by this delivery.

Checked the new statements on zero sheaves and zero sections, a singleton index,
and empty coverings. Zero images and endpoint transports are additive; no
monicity of individual units or system maps is asserted. Empty coverings are
allowed in the finite-image argument. J remains filtered, with no additional
nonemptiness, strictness, or injectivity hypothesis. The new evaluation theorem
requires the actual sheafification and Ext instances and does not assume an
injective sheaf. These edge-case checks are mathematical checks of statements,
not claims that the remaining sorry has been proved.

## No longer needed

Removed the original proof-only import `Sheaf.CategoryTheory.ColimitSiteSections`.
Both original public imports supply the existing statement's vocabulary and
instance environment and are preserved. The second reading also removed the
redundant proof-only import `Mathlib.CategoryTheory.ConcreteCategory.EpiMono`
from `VaryingSiteSectionsZeroDetection`; its used declaration is already available.

The planned wrapper `lem-weil-pbc-colimit-of-sites-sections` and its module
`Sheaf.CategoryTheory.ColimitSiteSections` are not used by this proof. The outer
argument uses the more general existing fixed-site theorem directly from
`Sheaf.CategoryTheory.SiteFilteredColimitSections`, for a diagram indexed by J.
The wrapper instead takes a diagram indexed by Under i. This pruning concerns
this proof route; it does not claim other users of the wrapper disappear.

The pullback-cohomology construction theorem
`CategoryTheory.siteCohomology_pullback` is not invoked: the required degree-zero
unit equations are already hypotheses of the item. Its module is retained as
an original public import, so it is not a pruned module. The colimit-site
construction remains needed for the remaining inverse-image argument, and the
finite-cover section theorem remains needed for the proved outer argument.
The removed direct proof dependencies are
`def-weil-pbc-sites-and-cohomology`,
`lem-weil-pbc-site-cohomology-pullback`,
`lem-weil-pbc-colimit-of-sites`, and
`lem-weil-pbc-colimit-of-sites-sections`. The first supplies vocabulary and is
used in the evaluation/section subproofs; the third remains an inner-lemma
dependency. Only `Sheaf.CategoryTheory.ColimitSiteSections` is pruned from this
module's import route; no whole-library unreachability is claimed.
No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The DAG correctly identified the need for an inner inverse-image section
argument. `colimitSite_sections_isIso` is only a fixed-limit-site comparison,
not a comparison with sections of the varying stage sheaves. Applying it alone
would not prove this item. The delivery proves the outer argument in Lean and
makes the inner argument an explicit independent item.

`exists_colimit_site` provides a constructed cocone and its section formula;
the item instead supplies arbitrary V and Q with object/arrow colimit witnesses.
The remaining inverse-image lemma must transport that formula to the supplied
site, as its proof docstring now specifies. We did not assume that existential
construction immediately supplies a formula for arbitrary V.

The local literature/stacks-project sources are absent on this machine.
WANTED: the locally regenerated `sites.tex` and `sites-cohomology.tex`, Tags
0A35, 09YN and 09YP. Read their official web versions:
https://stacks.math.columbia.edu/tag/0A35,
https://stacks.math.columbia.edu/tag/09YN,
https://stacks.math.columbia.edu/tag/09YP.
The new node proofs are marked agent-written. The generic evaluation proof
uses the actual Mathlib source declarations rather than attributing this Ext
presentation to a Stacks statement. No literature files were changed.
LeanSearch queries returned Internal Server Error and are recorded as unavailable;
LeanFinder, Loogle and grep searches are recorded with their actual results.

## New nodes

`lem-weil-pbc-object-cohomology-zero-evaluation`, module
`Sheaf.CategoryTheory.SiteCohomologyZeroSections`: proved generic identity-generator
evaluation properties. It includes the explicit evaluation definition and its
proved theorem, and has no sorry.

`lem-weil-pbc-varying-site-sections-zero-detection`, module
`Sheaf.CategoryTheory.VaryingSiteSectionsZeroDetection`: proved outer finite-stage
zero detection using the existing fixed-site section theorem and the new inner
lemma. The finite-covering image and filtered-colimit algebra are implemented.

`lem-weil-pbc-varying-site-inverse-image-zero-detection`, module
`Sheaf.CategoryTheory.VaryingSiteInverseImageZeroDetection`: the sole remaining
sorry, the inner inverse-image step of 0A35/09YN. A later inverse-image section
vanishing is detected by a stage transition; no system colimit or cohomology
is assumed. The docstring specifies the intermediate section w, the unit
naturality and cocycle equations, the identity presentation, the further arrow
d, and the resulting Under morphism with right component a ≫ d.

All node files are under `dag/nodes/sec-proper-base-change/` and retain the item's
chapter and unit. No change records are needed because existing interfaces
were preserved.


## Second reading by S2

1. Compared every delivered module with the repository. Only the item previously
   exists; its entire existing theorem signature and docstring are byte-for-byte
   unchanged. Its two public imports are unchanged. The three other modules and
   their declarations are new. The existing node changes only proof, proof_deps
   and proof_origin. No existing definition or target changes. Verdict: pass.
2. Compiled all four modules through lcompile.py, without errors or warnings.
   Scanned the delivered source: exactly one sorry, in the named public theorem
   varyingSite_inverseImage_zero_detection; no forbidden declarations or hollow
   definitions. Compiled scratch copies with #print axioms for all five public
   declarations. Evaluation and its properties use only propext, Classical.choice
   and Quot.sound. The inner lemma, outer detection and item additionally use
   sorryAx, as reported; the outer proof also uses the existing open fixed-site
   section comparison. Verdict: a sound conditional decomposition, not a finished
   proof independent of sorry.
3. Read each new statement and proof, and independently checked the official
   Stacks pages https://stacks.math.columbia.edu/tag/0A35,
   https://stacks.math.columbia.edu/tag/09YN and
   https://stacks.math.columbia.edu/tag/09YP. The inner lemma is precisely eventual
   zero detection for one inverse-image section, strictly below the item: no Ext,
   cohomology, D, c, K or system-colimit hypothesis. Its proof accounts for the
   supplied V and Q rather than mistaking an existential construction for them.
   Zero sections, zero sheaves, the singleton index and empty coverings cause no
   exception; filteredness excludes an empty index. The equations he/heV fix the
   unit compatibility of the otherwise supplied composition isomorphisms.
   Searched Mathlib with new LeanFinder, Loogle and grep queries in searches.jsonl,
   and searched the repository and upstream category-theory source with rg.
   No existing varying-site detection theorem was found. The degree-zero descent
   theorem concerns existence of representatives, not equality detection; the
   existing ColimitSiteSections wrapper is only the fixed-site outer comparison.
   The remaining inner proof needs substantial colimit-site transport, so it was
   not closed in this review. Verdict: true, needed, sourced, strictly simpler.
4. Read the proof from the item downward: filtered representation, faithful
   degree-zero evaluation, outer section-colimit comparison, inner detection,
   then the colimit transition equation. The evaluation proof uses the actual
   Mathlib equivalences directly. Checked sk-thm-p1's realized statement and all
   four steps: this reduction is below those steps and bypasses none of them.
   Original public imports remain needed for the unchanged interface. Removed
   the redundant EpiMono proof import after a successful scratch compilation.
   Completed No longer needed with every removed old direct proof dependency.
   Verdict: pass; pruning is local to this route.
5. Read all four nodes against their Lean signatures and proof bodies. New nodes
   have source, searches, split status, created, blueprint, chapter, unit and Lean
   records; every proof_deps list equals the union of proof-step uses. The old
   node records the implemented kernel argument and both new dependencies.
   Verdict: pass.

Changed in this reading: removed one redundant proof-only import; completed the
pruning report and made its decomposition/zero-net-hole count explicit. No
mathematical statement, definition, proof body or DAG route was changed.
