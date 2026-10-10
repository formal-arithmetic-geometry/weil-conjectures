# Stage 1 report

1. Files written:

- `dag/nodes/sec-smooth-purity/prop-pur-kinjective-resolutions-exist.json`, statement, split using two unsplit dependencies; Mathlib searches found no direct theorem.
- `dag/nodes/sec-smooth-purity/lem-pur-ringed-site-grothendieck-abelian.json`, statement, no Mathlib match (only the general sheaf-valued Grothendieck instance).
- `dag/nodes/sec-smooth-purity/lem-pur-kinjective-degreewise-existence.json`, statement, no Mathlib match (only bounded-below or individual-object injective resolutions).
- `citations.json`, verbatim statement quotes for every proof citation.

2. Attachments: none.

3. WANTED: none; the cited Stacks sources are named in each node.

4. The item had no sorry-free declaration in `WeilConjectures/`. Existing `lem-weil-pbc-kinjective-functorial-existence` is for a general Grothendieck category but states only K-injectivity, not the degreewise-injective clause of this item. Existing etale-site Grothendieck nodes do not cover an arbitrary small ringed site, so two strictly smaller generic statements were created. The item blueprint had an unspecified `same_as`; the whole blueprint search found no duplicate.

## Review by G1

I read the item source reference, Stacks `sites-cohomology.tex` Section 07A5 and `injectives.tex` Theorem 079P, and compared both clauses hypothesis by hypothesis with the item. Step 1 cites the new ringed-site statement, whose hypotheses explicitly introduce the small site and ring sheaf and whose conclusion supplies all colimits, exact filtered colimits, and the displayed generator. Step 2 cites that Grothendieck conclusion and the new generic functorial-resolution statement; the latter explicitly supplies the natural transformation, quasi-isomorphism, K-injectivity, and injectivity of every term, so every clause used by the step is present verbatim in the cited statements. I checked the existing DAG for the Stacks tags and for `Grothendieck`, `K-injective`, and `functorial resolution` before creating either node; the only nearby result was the etale-specific theorem and the weaker generic K-injective replacement. I tested the statements on the zero complex and on a one-term injective complex: the resolution can be the identity and all requested properties reduce correctly. Mathlib searches were run for the item and both new nodes with LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable and recorded as such, while the other searches returned only general sheaf or bounded-below ingredients.

## Not duplicates

lem-pur-kinjective-degreewise-existence vs prop-pur-kinjective-resolutions-exist: the new node is a generic Grothendieck-category theorem, while the existing item is specialized to sheaves on a small ringed site and also asserts the Grothendieck generator clause.
lem-pur-kinjective-degreewise-existence vs lem-sc-bounded-below-injective-resolution: the new node treats arbitrary unbounded complexes and gives a functorial replacement; the existing node treats a bounded-below complex and only proves K-injectivity.
lem-pur-kinjective-degreewise-existence vs lem-weil-derived-limit-existence: the new node constructs resolutions, while the existing node computes derived inverse limits and uses 079P only as an input.
lem-pur-kinjective-degreewise-existence vs prop-weil-pbc-rlim-functoriality: the new node is the resolution theorem, while the existing proposition concerns functoriality of derived inverse limits.
lem-pur-kinjective-degreewise-existence vs prop-weil-pbc-derived-inverse-limit-computation: the new node is a generic resolution existence statement, while the existing proposition identifies a particular inverse-limit computation.
lem-pur-kinjective-degreewise-existence vs def-pur-derived-internal-hom: the new node asserts existence with injective terms, while the existing definition merely uses a K-injective resolution to define derived internal Hom.
lem-pur-kinjective-degreewise-existence vs prop-weil-pbc-kinjective-resolutions-exist: the new node is generic and explicitly requires injectivity in every degree; the existing node is etale-module-specific and states comparison and bounded-below clauses instead.
lem-pur-kinjective-degreewise-existence vs lem-weil-pbc-kinjective-functorial-existence: the existing node gives a generic functorial K-injective replacement but does not state that its terms are injective; the new node includes that additional clause.
lem-pur-ringed-site-grothendieck-abelian vs prop-pur-kinjective-resolutions-exist: the new node isolates only the Grothendieck-category clause, while the existing item also asserts K-injective resolutions.
lem-pur-ringed-site-grothendieck-abelian vs lem-weil-pbc-module-sheaves-colimits-forgetful: the new node covers arbitrary small ringed sites; the existing node concerns colimits and forgetful functors for the small etale site.
lem-pur-ringed-site-grothendieck-abelian vs lem-weil-pbc-module-sheaves-enough-injectives: the new node proves the Grothendieck property; the existing node derives enough injectives for etale module sheaves.
lem-pur-ringed-site-grothendieck-abelian vs lem-weil-pbc-module-sheaves-grothendieck-abelian: the new node is the arbitrary ringed-site statement; the existing node is specialized to constant coefficients on a scheme's etale site and gives an affine generating set.
lem-pur-ringed-site-grothendieck-abelian vs def-weil-sheaf-of-modules-category: the new node is a theorem about the category; the existing node is only its definition.
lem-pur-ringed-site-grothendieck-abelian vs lem-pc-module-filtered-colimits-tensor: the new node proves all Grothendieck axioms; the existing node uses filtered-colimit exactness for tensor products.
lem-pur-ringed-site-grothendieck-abelian vs lem-weil-pbc-module-sheaves-limits-sectionwise: the new node proves the categorical Grothendieck structure; the existing node addresses sectionwise limits.
lem-pur-ringed-site-grothendieck-abelian vs lem-weil-pbc-presheaf-modules-colimits-sectionwise: the new node concerns sheaf modules and exact filtered colimits; the existing node concerns presheaf colimits sectionwise.
lem-pur-ringed-site-grothendieck-abelian vs def-pur-sheaf-inverse-limit: the new node is a Grothendieck theorem; the existing node defines inverse limits of sheaves.
lem-pur-ringed-site-grothendieck-abelian vs lem-pc-sites-modules-quotient-j-shriek: the new node proves the ambient Grothendieck category; the existing node proves a quotient construction involving extensions by zero.
lem-pur-ringed-site-grothendieck-abelian vs lem-weil-pbc-separating-family-epi-coproduct: the new node states existence of a generator; the existing node proves an epimorphism from a particular coproduct in the etale setting.
lem-pur-ringed-site-grothendieck-abelian vs def-weil-pbc-sheaf-free-separator: the new node gives the full Grothendieck axioms; the existing node defines a free separator for etale sheaves.
lem-pur-ringed-site-grothendieck-abelian vs lem-weil-pbc-sheaf-free-separator: the new node is the arbitrary ringed-site Grothendieck theorem; the existing node only defines a free separator construction in the etale setting.

## Second reading by G1

- Item statement: checked against Stacks `sites-cohomology.tex` Section 07A5 and `injectives.tex` Theorem 079P, hypothesis by hypothesis; the small-site, Grothendieck, generator, K-injective, degreewise-injective, and functorial clauses agree.
- Step 1: checked against the statement of `lem-pur-ringed-site-grothendieck-abelian`; it supplies exactly the category, colimits, exact filtered colimits, and generator used by the step.
- Step 2: checked against the statements of both cited nodes and Theorem 079P; the Grothendieck hypothesis, natural transformation, quasi-isomorphism, K-injectivity, degreewise injectivity, and functoriality are all present.
- `lem-pur-ringed-site-grothendieck-abelian`: checked B1-B7, the source paragraph and Modules on Sites lemmas 03DA, 03DB, 03EW, and searches for duplicate or Mathlib statements; tested on the empty site and a one-object site. Added explicit definitions for restriction to `\\mathcal C/U` and extension by zero.
- `lem-pur-kinjective-degreewise-existence`: checked B1-B7 against Theorem 079P lines 1811-1815; tested on the zero complex and a one-term injective complex. Added the missing cochain-complex and injective-object definition dependencies.
- `prop-pur-kinjective-resolutions-exist`: checked the item source, all cited node statements, source tags, blueprint metadata, and Mathlib search records; no duplicate or Lean attachment found.

Changes made: added the missing definition citations and self-contained explanations for extension-by-zero notation; updated the item dependencies and statement accordingly. No proof step was weakened or moved, and no source error was found.
