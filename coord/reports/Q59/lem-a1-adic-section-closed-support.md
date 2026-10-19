# Worker report — Q59

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-a1-adic-section-closed-support.json`: statement unchanged, seven proof steps, status split; not in Mathlib.
- `dag/nodes/sec-deligne-laumon-a1/lem-a1-integral-constructible-reduction-fibres.json`: one new statement-only lemma, status unsplit; no Mathlib match. It compares ordinary integral quotients, their common-stratification etale origins, and adic coefficient fibres. It asserts no support closedness.
- `citations.json`: verbatim statement quotations for every item-step citation.

The sandbox initially contained only dispatcher markers, with no earlier item, report or searches. The item was copied from the current shared DAG. No shared-repository file, launcher file, Lean file or unit record was changed. No git command or compiler was run by this worker; packaging and server validation are delegated to the required delivery command.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact item tag and for closed support, section/support, integral fibre and reduction/fibre phrases found no declaration stating either the whole item or the new comparison. The curve and affine-line endpoint declarations concern special lisse curve vanishings, not this assertion for an arbitrary constructible heart object on a separated finite-type scheme. The archived master is reference material, not completion evidence.

## WANTED

None. The Bhatt–Scholze PDF and Stacks TeX sources needed here are available in the repository.

## Corrections and scope

The item statement is true as written and is retained. Its unsplit source note suggests uniform finite reduction detection but does not supply that argument. The proof now explains the uniformity: for each fixed power of the uniformizer, all finite-level supports are unions of the same finite set of connected strata, so their increasing union equals one finite-level closed support. Rational support is then an intersection over all powers of the uniformizer. This avoids treating the support of an arbitrary constructible sheaf as closed, and avoids claiming that increasing closed subsets stabilize merely because the scheme is Noetherian.

There is no hypothesis change, no statement dispute and no change of unit route. This item serves the first two sentences of `sk-l-dl-a1-endpoints`, through `lem-a1-constructible-degree-zero-proper-support`: a section on the proper compactification needs closed nonzero-fibre support before properness can be used. The parent and compactification-realization nodes are not cited back, so no circular support argument is introduced.

The new lemma is the remaining coefficient comparison, not a relabelling of the support claim. In particular it distinguishes the ordinary quotient `F / pi^n F` from the derived reduction; the latter can have degree minus one when the local model has torsion. It gives natural morphism/fibre normalization as well as a stratification that works simultaneously for every ordinary quotient. These are required before the support calculation can be performed in the exact raw rationalized heart of the item.

## Searches and sources

Read Bhatt–Scholze, *The pro-étale topology for schemes*, arXiv:1309.1198, §§5.1 and 6.8, specifically Lemmas 5.1.1–5.1.4, Corollary 5.1.5, Lemma 6.8.2, Proposition 6.8.4, Definition 6.8.10, Proposition 6.8.11, and Proposition 6.8.14. The integral definition explicitly allows finitely presented scalar modules, including torsion. Read Stacks `etale-cohomology.tex`, Tag 04FR, `lemma-zero-over-image`, all three clauses and its proof, and Tag 04FT, `lemma-support-section-closed`. These support assertions are used only for ordinary finite-coefficient etale sheaves. The rational extension is the written agent argument, not a claim that 04FT applies directly to arbitrary pro-etale sheaves.

Read the chapter record, the endpoint unit record and its current `main-20261015` blueprint text. Searched the whole DAG by `04FR`, `04FT`, `lemma-zero-over-image`, integral local model, ordinary quotient, finite reduction/fibre and inverse-limit/stalk phrases. Ran blueprint searches for section support, closed support, integral constructible, integral fibre, finite models, reduction fibres, adic stalk, quotient stalk and stratification reductions, plus the ancestor command. No blueprint node states the new comparison. The exact search commands and outcomes of real Mathlib searches are in `searches.jsonl` and the relevant node records.

Mathlib semantic searches found structure-sheaf zero loci and ideal-sheaf support, and for the new comparison profinite inverse-limit and locally constant function constructions. Read the returned signatures. Also read `Mathlib/AlgebraicGeometry/Sites/ElladicCohomology.lean` lines 57–78: `Scheme.ellAdicSheaf` constructs the continuous integral coefficient sheaf; it does not identify quotients or fibres of arbitrary constructible modules. Read `Mathlib/AlgebraicGeometry/Scheme.lean` lines 740–761: `zeroLocus_isClosed` concerns the zero locus of structure-sheaf sections, not their nonzero adic coefficient-fibre locus. The broad adic grep's ideal-sheaf results were also excluded by their object and statement. None is an exact match or one-line specialization for either node.

## Not duplicates

- lem-a1-integral-constructible-reduction-fibres vs lem-weil-pbc-integral-stratified-perfect-characterization: the existing theorem characterizes the integral category by perfect/local finitely presented models; it does not state the ordinary quotient etale origins with their natural adic fibre and section-map normalization. The new comparison is on precisely its witnessed completed category, not a silently different coefficient category.
- lem-a1-integral-constructible-reduction-fibres vs sk-lem-int-integral-heart: the existing statement gives integral heart closure and finite-module models; it does not identify inverse limits of ordinary quotient stalks with the rational coefficient fibres or the fibre of a specified morphism.
- lem-a1-integral-constructible-reduction-fibres vs lem-per-lisse-completed-system-comparison: that theorem treats locally finite free integral modules; the new lemma treats arbitrary constructible integral heart objects, including torsion models and jumps across strata, and their ordinary quotients globally.
- lem-a1-integral-constructible-reduction-fibres vs lem-sf-proetale-constructible-origin: that theorem is a comparison at a fixed finite ring. It provides neither simultaneous integral quotient data nor the comparison of their inverse-limit fibres with raw rationalized fibres.
- lem-a1-integral-constructible-reduction-fibres vs lem-pod-adic-limit-finite-modules: that theorem reconstructs abstract finite-module towers; it does not assert the sheaf-level ordinary quotients, a uniform geometric stratification, or their compatibility with the prescribed rational adic fibre functor.
- lem-a1-integral-constructible-reduction-fibres vs lem-per-adic-heart-pullback-fibres: that theorem specifies exact conservative rational fibres and their geometric/scalar compatibility. It does not give the ordinary quotient tower of an arbitrary torsion-allowing integral representative, or identify the section values of that tower with a specified integral sheaf morphism.
- lem-a1-integral-constructible-reduction-fibres vs lem-a1-adic-section-closed-support: the new lemma has no closedness or support/restriction assertion; it supplies coefficient reduction data for arbitrary integral heart objects and maps, on which the item's support argument depends.

## Review by Q59

I checked the item against the sources above with its exact hypotheses: finite type over the fixed field makes the schemes Noetherian and finite dimensional, and ell is invertible. No smoothness, properness, normality, lisseness of the whole object, or Weil structure is used. I kept the rationalized/common-stage categories of the statement; integral representatives come from the witnessed completed category, not from discrete non-torsion etale coefficients.

For step 1 I opened `prop-weil-localized-tstructure`: its statement says that every rational heart object is isomorphic to the localization of an integral heart object. I opened `def-weil-pbc-rational-category`: its actual Hom module is the integral Hom tensored with E, so the single denominator and the integral sheaf map follow. These are tools for choosing a representative, not a substitute route for the endpoint unit.

For step 2 I read the new comparison statement and the Bhatt–Scholze passages defining integral constructibility and relating the completed coefficient categories. The new lemma explicitly supplies every datum used there: the ordinary quotients, one stratification for all levels, the inverse-limit modules and the natural fibre value of u. Its proof obligation is a smaller comparison lemma with no support conclusion. I also opened `lem-sfb-noetherian-connected-components-open`: it states exactly the finiteness and openness of the connected components needed to refine the Noetherian strata without losing local closedness. This is why the later finite-union argument has only finitely many possibilities.

For step 3 I opened both cited statements. `lem-sc-etale-section-zero-open` characterizes zero geometric germs by a largest Zariski open; its complement gives closedness of C(m,n). `lem-pur-lisse-morphism-rigidity` clause 2 applies to the finite coefficient ring A/pi^n and maps between finite local systems. I checked that both its source and target on each stratum are finite locally constant by the comparison lemma, and that each connected stratum remains a separated finite-type k-scheme. A vanishing germ is the zero map because the source is generated by 1. Thus the closed finite-level support contains either a whole connected stratum or none of it. No rational version of the finite rigidity lemma is assumed.

Steps 4 and 5 use no new lemma: I wrote out the maximum of one witness level for each of finitely many occurring strata, the coordinatewise zero criterion in an inverse limit, the equality criterion for localization of a module element, and the intersection of the closed sets A(m). These are elementary arguments from the data already cited. They do not require a uniform torsion exponent or a global lisse integral lattice. Every proof step is below 2000 characters.

For step 6 I opened `lem-per-adic-heart-pullback-fibres` and checked that its statement gives natural geometric-point independence, pullback compatibility, exactness and joint conservativity on the constructible hearts. Applying exactness to the image of the restriction and conservativity to that image proves zero of the morphism; merely checking stalks on arbitrary pro-etale sheaves would have been insufficient. The complementary open is still finite type since T is Noetherian.

For step 7 I checked the same fibre statement's finite-extension normalization and common-stage heart description, and the actual pair/morphism definition in `def-weil-pbc-qbar-category`. An object and a morphism are represented at a common finite stage, and vector-space scalar extension detects zero. This proves equality of the underlying support sets, preservation and reflection of the zero-restriction assertion, and independence of the common-stage representative. It does not identify the common-stage category with a discrete Omega-coefficient etale category.

I tested the new comparison on the empty scheme, the zero sheaf, a free module, a pure torsion local model A/pi^r, and a mixed model A plus A/pi^r. In the torsion case the ordinary quotient is A/pi^min(n,r), its inverse limit is A/pi^r, and the rational fibre is zero. This specifically checks the distinction from derived reduction. For the support argument, zero sections give the empty set; a nonzero constant rational section on a connected scheme gives the whole scheme; a torsion integral section disappears after the intersection over powers; and a section with valuation d can first be detected only at level d+1. The latter checks why a single predetermined reduction cannot prove closedness. Nonclosed support of the sheaf j_!E on a proper dense open is not a counterexample: it is sheaf support, not the support of a global section that extends by zero.

I checked delivery-errors B–E against the files: the new node is self-contained, statement-only with empty proof and proof_deps, uses TeX once, records real searches without invented outcomes, and supplies blueprint provenance. Existing nodes are reused for finite supports, finite rigidity and connected components rather than recreated. Every cited statement was opened and its used part copied verbatim to citations.json. No SGA source is used. Nothing remains unfinished in this one-level split; the new comparison lemma is deliberately unsplit for the next DAG level.

## Validation

The first required dry run exited 0 and printed `OK (not pushed)` with preflight passed at `3f6a418a5e`. I then added explicit definition citations for module sheaves, geometric points and finitely generated modules to the new comparison statement, refreshed its verbatim quotation, and reran the required dry run before delivery.
