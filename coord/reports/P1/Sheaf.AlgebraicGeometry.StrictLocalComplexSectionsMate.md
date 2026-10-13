## What changed

Replaced the sorry in `AlgebraicGeometry.Etale.strictLocalComplexSectionRestriction_mate`
with a complete Lean reduction, preserving its signature and existing docstring.
The proof imports `Sheaf.AlgebraicGeometry.StrictLocalDerivedMateSectionsFactorization`
privately. It computes the mate by the underived sections transformation, rewrites
that transformation as stage comparison followed by cone restriction, verifies the
resulting chain-map identity degreewise, applies homology functoriality, and uses
naturality of the inverse localization/homology comparison. All three delivered
modules compile together through lcompile.py.

Added two modules, each with one public theorem left with `:= by sorry`, a source,
a proof in words, and its own node. `StrictLocalUnderivedSectionsMate` also defines
`strictLocalUnderivedMateSections` by actual composition of natural transformations;
its construction has no sorry or choice of data. The second module computes the
derived mate using this actual transformation. Its statement does not use Q, cone
legs, termwiseSectionsRestriction, or a claimed equality with cone restriction.
The first theorem is entirely underived, for all sheaves, without complexes,
cohomology, injectivity, q, or derived mates. These are separate substantive parts
of the original argument, not renamed versions of its conclusion.

Updated the original node's proof, proof_deps, and proof_origin to match the Lean
reduction. No existing definition, theorem signature, visibility, or public import
changed. The extra heartbeat allowance is local to the theorem and addresses
conversion between composite section functors under localization.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.strictLocalComplexSectionRestriction_mate`
(node `lem-weil-pbc-strict-local-complex-sections-mate`). There are no sorries left
in the item's module.

Added exactly two holes:

- `AlgebraicGeometry.Etale.strictLocalUnderivedMateSections_eq`, in
  `Sheaf.AlgebraicGeometry.StrictLocalUnderivedSectionsMate`, node
  `lem-weil-pbc-strict-local-underived-sections-mate`.
- `AlgebraicGeometry.Etale.strictLocalComplexSectionRestriction_derivedMate`, in
  `Sheaf.AlgebraicGeometry.StrictLocalDerivedMateSectionsFactorization`, node
  `lem-weil-pbc-strict-local-derived-mate-sections-factorization`.

This is a decomposition, not a complete proof from sorry-free dependencies:
one original hole closed, two new holes added (net minus one). The actual
combination, including the degreewise equality and the localization naturality
step, is proved in Lean. No sorry occurs in a definition or private declaration.

Edge cases: the underived identity uses only adjunction and pullback identities
and applies to the zero sheaf or an empty fibre; no etaleness of a cone leg is
assumed. The derived statement permits every n in ℤ, including negative degrees
and zero complexes. Only the derived direct-image unit on the original injective
representative is inverted. The potentially nonacyclic limit pullback retains
its derived-sections unit. No qcqs or torsion assumption is used in these
compatibilities; they do not assert a continuity isomorphism.

## No longer needed

No imports removed, and no whole node or module is claimed pruned. The item's
original public import `StrictLocalLocalizedHomGerm` remains required for the
section-restriction definitions. The theorem `sourceLocalizedSectionsIso_germ`
is not used: this item is about sections complexes, before localized Hom or
germs. The theorem `injectiveSections_strictLocal_comparison` is not used either;
its module provides the definitions of termwise restriction and representative
comparison. Both modules therefore remain in the import closure.

The original node's seven direct proof dependencies have been replaced by the
two new comparison nodes. Their constructions and proof plans still use the
original definitions and derived-adjunction infrastructure. This change is a
factorization of the plan, not pruning of those underlying modules.

For completeness, every original direct proof dependency replaced is:

- `def-weil-pbc-strict-local-injective-source-comparison`
- `def-weil-pbc-strict-local-mate-projection-data`
- `def-weil-pbc-strict-local-neighbourhood-geometry`
- `def-weil-pbc-underived-exchange`
- `lem-weil-pbc-injective-sections-pullback-comparison`
- `lem-weil-pbc-strict-local-localized-hom-germ`
- `prop-weil-pbc-derived-inverse-image-adjunction`

These remain statement/construction dependencies or dependencies of the new
lemmas; none is claimed removed from the targets' import closure.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or unusable existing signature was found. The node's
three prose steps are not immediate applications of its named declarations:
they also need an underived evaluation identity and the compatibility of
exact sections/Leray with the derived mate factorization. Those are the two
statements isolated here. Generic mate formulas and the upstream
`Adjunction.derivedPlus_mateEquiv_app_fac` do not by themselves state either
sections identity. Downstream source restriction theorems import this item,
so using them would be circular.

Read the final paragraph of [Stacks, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9).
The new lemmas spell out the compatibility of its neighbourhood-section maps
with the separately constructed mate; their detailed mate computations are
agent-written. The proof does not use the source paragraph's assertion that
the complex of sections at the limit already represents derived sections.

The inherited unit is `sk-prop-h2`; its realized.statement and realized.steps
are empty in the checkout. No unit statement or realized step was bypassed.
The original node's blueprint ancestor pointer to
`prop-weil-pbc-strict-henselization-stalk-formula` is retained and used for the
new nodes. The ancestor script follows created.item, which is a module name
for this stage-3 item, and returned None; the explicit inherited blueprint
pointer identifies the intended source paragraph.

LeanSearch returned Internal Server Error for both new comparisons. LeanFinder,
Loogle, direct rg of the source library and Mathlib, and blueprint searches were
also performed. No existing theorem with either exact sections identity was
found; the generic upstream mate factorization and square compatibility are
recorded in the new derived node's proof plan.

## New nodes

`lem-weil-pbc-strict-local-underived-sections-mate`:
`dag/nodes/sec-curve-estimates/lem-weil-pbc-strict-local-underived-sections-mate.json`.
This isolates evaluation of the actual underived exchange on pointed
neighbourhood sections as a natural-transformation identity. It supplies the
geometric part using Q.first and Q.over, independently of any derived theory.

`lem-weil-pbc-strict-local-derived-mate-sections-factorization`:
`dag/nodes/sec-curve-estimates/lem-weil-pbc-strict-local-derived-mate-sections-factorization.json`.
This isolates the derived-unit, exact-sections, and Leray compatibility on the
fixed injective representative. It computes the derived mate by the underived
exchange transformation without identifying that transformation with geometric
cone restriction. No change records or forced adaptations are needed.


## Second reading by P1

1. **Unchanged interface: pass.** Compared the delivered item with the repository
   using diff and checked the existing theorem signature byte for byte. Its
   docstring, visibility and public import are unchanged. The only additions to
   the existing module are a private proof import, local elaboration options,
   and the proof body. No other existing module or target is changed.
2. **Lean proof and axioms: pass, with the reported open dependencies.** All three
   modules compile in import order through lcompile.py without warnings. A scratch
   copy with #print axioms checked the original theorem, both split theorems and
   the new definition. The definition uses only propext, Classical.choice and
   Quot.sound; the three theorems additionally use sorryAx, as expected from the
   two named open lemmas. The item contains no sorry; exactly the two reported
   public theorems contain sorry. No forbidden declaration or hollow definition
   occurs. The underived map is an actual composition, with no witness chosen
   from an unproved existence theorem.
3. **Split statements: pass as a decomposition.** Read the sections restriction,
   sourceStageSectionsIso, sectionsPullbackNat, representativeSectionsComparison
   and exact-sections/Leray definitions, the upstream mate formulas in Square,
   and derivedPlus_mateEquiv_app_fac and DerivedComparison. The underived lemma
   isolates the geometric evaluation identity for all sheaves; Q.first and Q.over
   fix the cone leg uniquely by the two pullback projections. The derived lemma
   instead isolates compatibility with localization, derived units and Leray,
   without Q or cone restriction. Neither is a renamed copy of the item; the
   degreewise composition and homology-naturality argument combining them is
   present in Lean. Zero sheaves/complexes, empty fibres, arbitrary integer
   degrees, identity squares and nonetale cone legs require no extra hypotheses.
   In particular no unit at the limit pullback is inverted. Both new holes have
   docstring proofs, sources and matching nodes. Independently searched Loogle
   for mateEquiv_apply, LeanFinder for evaluation of base change on sections,
   and Mathlib by mate/naturality patterns, and searched lean/ and the upstream
   source with different section/base-change terms. Generic mate formulas and
   SourceStageSectionsNaturality do not state either new identity; downstream
   source restriction results would be circular. No few-minute closure of
   either split statement was found. Read [Stacks Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9);
   its section maps motivate the construction, while the new nodes explicitly
   mark the mate compatibility details as agent-written. Its stronger
   representative assertion is not assumed here.
4. **Route and pruning: pass.** The proof uses exactly the two new comparisons,
   degreewise chain-map equality, homology functoriality and naturality of the
   inverse homology localization comparison. Imports are needed for public
   statements/constructions except the item's additional private proof import.
   No module is claimed pruned. Completed the report by naming all seven
   replaced original direct proof dependencies, while explaining that their
   definitions and infrastructure remain needed below the factorization. The
   inherited sk-prop-h2 realized statement and step lists are empty; no realized
   unit statement or step is bypassed and no unit record is changed.
5. **DAG: pass.** The existing node changes only proof, proof_deps and proof_origin.
   Its three steps describe the actual Lean reduction. Both new nodes have
   matching verbatim Lean signatures, chapter/unit and inherited blueprint
   pointers, source, creation record, searches and proof origin. All referenced
   dependencies exist, and each proof_deps is exactly the union of its step uses.
   The derived node uses the underived node's constructed transformation, not
   its equality theorem.

Second reading changed only this review, the explicit replaced-dependency list
in the report, and the author attribution of the new derived-factorization
module from J3 to P1. No proof, statement, definition or node needed repair.
The delivery closes one original hole and adds two strictly smaller holes:
this is a decomposition with net holes closed minus added equal to -1.
