# Q89: lem-sfb-constant-field-tor-bounds

## 1. Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-constant-field-tor-bounds.json`: existing statement, now split in five proof steps; statement and statement dependencies unchanged; not a Mathlib leaf.
- `citations.json`: twelve verbatim statement quotations, one for every step/node citation.
- `report.md`: this report. `searches.jsonl` is the unmodified search-command log.

New nodes: 0. New Mathlib leaves: 0. The existing Mathlib leaf `lem-sfb-bounded-representative` is reused.

## 2. Attachments

None. The project-source searches for the blueprint tag and the constant-field/flatness/Tor notions found no finished declaration under WeilConjectures that states the entire item. In particular the general TorAmplitude and TorAmplitudeResidue APIs do not supply this site-level interval equivalence. The existing local Sheaf declarations for constant-field flatness and bounded-flat K-flatness support the cited nodes; they do not state the item.

## 3. WANTED

None. All sources needed are available in the read clone.

## 4. Findings and changes

The supplied statement is correct, including the absence of an enough-points assumption. I preserved its text and all original provenance and Mathlib searches. There was no earlier sandbox split or report to recover. I added the explicit argument missing from the empty proof. The unit route is unchanged: this proves the sentence in the first paragraph of `sk-lem-integral-models.proof.md` that bounded residue-field complexes have finite Tor dimension.

DAG and blueprint searches found existing statements for all three substantive tools: `lem-exc-constant-field-module-flat`, `lem-sfb-bounded-representative`, and `lem-weil-pbc-independent-bounded-flat-kflat`. The ringed-space version `lem-pc-bounded-above-flat-kflat` would not apply to an arbitrary site, so I use the independent-universe site version instead. A K-flat resolution is also cited explicitly in the converse; choosing the coefficient unit must work before boundedness of B has been proved. I wrote the unit comparison on representatives instead of leaving it implicit.

The logged Mathlib searches use LeanFinder twice, Loogle, LeanSearch and two concept grep queries, followed by grep queries locating the actual cohomological-bound and ordinary-module tensor-exactness candidates. I read the returned hits and the relevant source types. `DerivedCategory.isGE_iff` and `isLE_iff` at TStructure.lean:90,107 concern cohomological bounds only. The bounded representative at line 180 is already the existing Mathlib leaf. `Module.Flat.lTensor_shortComplex_exact` and `rTensor_shortComplex_exact` at RingTheory/Flat/CategoryTheory.lean:41,46 concern ordinary modules, not the entire sheaf derived-tensor assertion. The constant-sheaf and light-condensed hits do not state it either. All successful queries are recorded with their actual query text and results; no unavailable service was reported as a negative match.

Whole-blueprint searches for constant field, bounded flat, Tor amplitude, finite Tor dimension, field coefficients and constant field sheaf found no equivalent blueprint statement to record as same_as. In particular `lem-weil-field-tor-amplitude` has field-stage constructible inputs and asserts existence of bounds for their specified realizations; it does not state the arbitrary discrete constant-field interval equivalence here.

## 5. Unfinished work

None in the requested one-level split. No Lean was written or compiled. No new statements await splitting from this delivery.

## Not duplicates

No new nodes. The potential duplicate constant-field flatness, bounded-representative and site K-flat lemmas are reused directly. No clause of the item was moved to a new node.

## Review by Q89

I read the current chapter and `sk-lem-integral-models` unit records, the main-20261015 unit proof first paragraph, and the actual sources of the facts used: Modules on Sites, Tags 03ER (`definition-flat`) and 08FC (`lemma-flat-eq`); Cohomology on Sites, Tags 06YQ (`lemma-bounded-flat-K-flat`), 06YS (`lemma-K-flat-resolution`) and 08FZ (`definition-tor-amplitude` and the paragraph immediately after it); Modules on Sites, Section 03EK (the sheafified sectionwise tensor formula); and Homology, Tag 012Z (the total-complex formula). There are no new nodes needing separate source review. The proof origin is agent because the blueprint gives only the short field sentence; the expanded proof assembles these existing tools.

For step 1 I opened `lem-exc-constant-field-module-flat` and checked its statement, not just its proof. It asserts flatness for every module over the associated constant field sheaf, with no finiteness condition and no points. On the item's small representative, the module universe contains the site. Thus the site is essentially small in that universe, and the standard ring and abelian-group sheafifications, composition with the forgetful functor, and local-bijectivity property used by that node are available. These are the usual sheafification structures on a small site, not additional geometric hypotheses. I also read the attached ConstantFieldFlat source: the local relation argument includes objects with empty covering sieves. This checks that the zero ring of sections on such an object is harmless; it does not claim that every ring of sections of the constant field sheaf is itself a field.

For step 2 I checked that `lem-sfb-bounded-representative` gives a representative with TERMS zero outside the SAME interval [a,b], rather than merely bounded cohomology or a larger interval. Its Mathlib declaration at TStructure.lean:180–186 has both strict degree bounds; the hypotheses are exactly the item's cohomology bounds in an abelian category. I then checked that `lem-weil-pbc-independent-bounded-flat-kflat` states the ringed-SITE result, accepts independent site and coefficient sizes, and requires only the upper term bound and the flatness supplied by step 1. This avoids misapplying the similar ringed-space statement.

For step 3 the cited derived-tensor definition permits the K-flat representative from step 2, and the cited total-tensor definition has only the summand (i,0) for N[0]. I wrote its term and differential explicitly. Zero terms outside [a,b] have zero kernels modulo images there, precisely the cohomology-sheaf definition cited. This is an elementary computation from those definitions: it does not assume tensoring arbitrary sheaf sections is exact, nor a cohomology/tensor interchange theorem.

For step 4 I checked that `lem-pc-kflat-resolution` applies to an arbitrary complex of modules on a ringed site without any boundedness assumption. It gives the K-flat quasi-isomorphism used, so the argument does not assume its conclusion. The other citations give exactly the representative-level derived tensor, total tensor, sheafification of ordinary sectionwise tensor, and invariance of cohomology under derived isomorphisms. The inverse unit maps p tensor r to rp and p to p tensor 1 commute with restrictions and differentials, so they give a genuine complex isomorphism after sheafification. Testing N=R is allowed by the universal quantifier and proves the reverse implication.

For step 5 I checked both clauses of `def-weil-proetale-tor-amplitude`: the fixed interval condition and existence of an ordered interval. Taking existence preserves the equivalence already proved. The zero complex works in [0,0]; for a nonzero degree-zero sheaf the singleton interval [0,0] works; shifts move both endpoints together. The empty scheme has only zero module sheaves, so both universal vanishing conditions hold, with no illicit nonempty-object assumption. Infinite fields, nonconstructible sheaves, arbitrary schemes and unbounded B in the converse require no added hypothesis.

Against delivery-errors B–E: no new definitions, duplicate lemmas or clause restatements were introduced; every non-elementary invocation is a cited existing statement with the stated hypotheses checked above; every citation has a verbatim quotation in citations.json. Proof dependencies are exactly the union of the uses lists. Generic off-unit tools are declared only in split_report.tool_uses for maintainer review. All five steps are below 2000 characters and none hides a comparison or auxiliary lemma. The statement was not changed, so there is no STATEMENT-DISPUTED. No SGA source, alternate coefficient category or stalk-conservativity argument is used.
