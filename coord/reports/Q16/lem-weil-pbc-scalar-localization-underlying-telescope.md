# Q16 stage-1 delivery

Item: lem-weil-pbc-scalar-localization-underlying-telescope.

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-scalar-localization-underlying-telescope.json`: statement, split; not a Mathlib leaf. Eight proof steps; no statement change.
- `citations.json`: one verbatim statement excerpt for every step/node citation (25 entries).
- `searches.jsonl`: actual Q16 search records, retained alongside the inherited searches in the item.
- `report.md`: this report. `write_split.py` is a sandbox-only preparation script, not a delivered node.

## New nodes

None. Zero Mathlib leaves created. The fraction computation, tensor-adjunction calculation, degreewise compatibility of the colimit isomorphism, and the leg equations are elementary consequences of cited statements and definitions. The substantial general telescope comparison already exists as lem-kun-complex-colimit-hocolim; creating another version would duplicate it.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint id, telescope/hocolim, and scalarLocalization/scalar_localization. The only telescope word hits are unrelated alternating-sum calculations in AlgebraicGeometry/Cohomology/LongExact.lean. There is no exact project declaration to attach. The item has no recorded Lean declaration/audit to import. No master sorry declaration is being treated as a proof.

## WANTED

None. All sources used were available locally.

## What was wrong or incomplete

The item was statement-only. Its statement is correct for an arbitrary small ringed site; it does not require nonzero t, t acting injectively, enough points, any finiteness condition, or a terminal object of the site. I retained every hypothesis and conclusion. The two tensor orders in its display of extension and its unit are related by the existing tensor symmetry; the proof spells this out.

Bhatt--Scholze Lemma 6.8.2 identifies the continuous coefficient ring after inverting the scalar, while Proposition 6.8.14(2) concerns constructible coefficient categories. Neither states the arbitrary-ringed-site telescope lemma verbatim. The proof therefore follows the item's already specified Stacks 0949 expansion, with 093W and 0A5L, and proves the scalar colimit by fractions and sheafification rather than asserting that the Bhatt--Scholze propositions supply it directly.

The ancestor's main-20261015 proof is the single paragraph beginning “Choose an integral lattice for K”, followed by rationalization of an integral isomorphism. I read that paragraph and the chapter and unit records. This child supplies a categorical scalar-localization ingredient of the existing derived-Hom/realization branch; it does not replace proper base change by a different geometric route and does not modify the unit record.

## Not duplicates

No new nodes, hence no new/existing tag pairs. I searched the whole DAG and the imported blueprint by homotopy colimit, telescope, scalar localization and localization telescope. I read lem-pc-complex-hocolim-colimit, lem-pc-telescope-shift-mono, lem-pc-cone-short-exact-quasi-iso and the fuller lem-kun-complex-colimit-hocolim. I reuse the last one because its statement includes the actual derived coproducts and the canonical cone projection, in addition to the quasi-isomorphism. The integral-module and integral-complex telescope nodes instead concern continuous E coefficients; they are not statements about every small site and every commutative algebra sheaf. I do not silently identify those coefficient settings.

## Mathlib searches

Q16 ran and read two semantic formulations with LeanFinder, a natural-language LeanSearch query, two Loogle queries, and two source greps using the required msearch.py command. All services answered successfully. Semantic hits concern sheaf module presentations, scalar linearity of derived functors, ordinary localized modules, tensor-unit complexes, and unrelated mapping-cone constructions. The first Loogle query finds Lean's binder telescopes; the second finds localization at quasi-isomorphisms, rather than ring-element localization. The telescope/hocolim grep has no hits in Algebra/Homology. The broader derived-category grep finds the exact-functor construction and short-exact-sequence cone comparison, not this theorem. I read the relevant Mathlib DerivedCategory/ShortExact.lean lines 25--68 and ExactFunctor.lean lines 25--61. Those tools cover parts already present in the DAG, not the whole item. Every appended record uses precisely the logged query; preexisting research entries remain unchanged.

## Review by Q16

I checked delivery-errors B through E against the eight proof steps and their cited statements. The source reading included Stacks algebra.tex, the fraction equivalence before Tag 07JZ in Section 00CM; sites-modules.tex, Tags 03CY (sheafification), 03DA/03DB (module categories and exact filtered colimits), 03EK (tensor product), and 03EO (tensor--Hom); derived.tex, Tags 093W, 0A5L, 0949 and 014A. I verified these tag-to-label assignments in the local tags table. I also read the local Bhatt--Scholze PDF at Lemma 6.8.2 and Proposition 6.8.14, and the current blueprint ancestor proof. There is no SGA source in this delivery.

Step 1 uses the actual fraction equivalence in def-weil-pbc-module-localization, the sheafified section construction in def-weil-pbc-ringed-section-localization, the factorization/adjunction in def-weil-presheaf-modules-sheafification, and the colimit universal property in def-weil-pbc-category-colimit. Equality of fractions is checked at stage n+m+k, which handles zero divisors and torsion. Maps out of the presheaf factor uniquely through its sheafification; I never equate a sheaf colimit with a sectionwise colimit without sheafification. This explicit calculation does not need a new lemma node.

Step 2 uses precisely the natural tensor--Hom adjunction, symmetry and unit isomorphism asserted by lem-pc-sheaf-modules-tensor-closed. The three displayed Hom bijections prove this colimit assertion directly. def-pur-sheaf-tensor-product describes the scalar-extension object and its local generators, and def-pc-sheaf-restrict-scalars explains its underlying R-module. The colimit universal property identifies the actual nth leg with t^(-n) tensor m, not just an unspecified isomorphism of objects.

Step 3 uses the arbitrary-small-ringed-site statement of lem-pur-ringed-site-grothendieck-abelian, not the narrower theorem about constant coefficients on an etale site. Its exact filtered-colimit clause applies since N is small, nonempty and filtered. The faithful exact forgetful functor, including kernels and cokernels, is explicitly in lem-weil-pbc-module-sheaves-colimits-forgetful. The definition of restriction says the underlying abelian sheaf is unchanged, so exactness is preserved and detected. This proves scalar extension exact by the colimit in step 2. Only after checking this hypothesis do I invoke lem-weil-pbc-exact-functor-derived-factorization for quasi-isomorphisms, the termwise model and its coherent shift isomorphisms.

Step 4 uses the definition of the derived category to choose any representative C. The universal-property comparison from step 2 commutes with the differential on each leg; this gives a chain isomorphism, with inverse checked by its degreewise inverses. The exact-functor factorization statement applies to both functors established exact in step 3 and identifies its image with UFL. No claim that every bounded-below object was already supplied with a strictly bounded representative is used; the existing telescope theorem accepts unbounded representatives.

Step 5 cites lem-kun-complex-colimit-hocolim for exactly what its statement says: the cone projection to the termwise colimit is a quasi-isomorphism, the actual termwise coprojections give a derived coproduct, and transporting the cone triangle gives the colimit's homotopy-colimit triangle. All hypotheses match Mod(R) on the given small site. Its explicit restriction of p to the unshifted summand identifies the resulting triangle arrow with the original colimit legs. I do not extract a construction merely from another node's proof.

Step 6 uses only the already cited tensor and localization definitions to calculate all legs. The inverse t action exists in the localized sheaf of rings even when t is zero or nilpotent. The unit and t^(-n) commute in the specified order, giving j_(n+1)t=j_n. Both tensor conventions give the same map under symmetry.

Step 7 uses TR3 as actually included in def-weil-triangulated-category and the full statement of lem-sf-triangle-morphism-iso. The first two comparison maps are identities after the coproduct identifications, hence isomorphisms. The second triangle square fixes every leg of the desired third comparison. This addresses an arbitrary supplied telescope triangle without asserting uniqueness of triangulated cones.

Step 8 writes the naturality equation on chain maps and extends it using the fully faithful precomposition/natural-transformation clause of lem-weil-pbc-localization-universal-property. The exact-functor factorization statement supplies the shift comparisons and their compatibility with representatives. The explicit degree-r shift equation and the common sign (-1)^k on differentials prove the leg compatibility. This asserts exactly naturality of the legs, not a functorial choice of arbitrary cone comparisons.

I tested the constructions for M=0, the zero ring, t=0, t nilpotent, t a unit, and t a zero divisor (for example t=2 in Z/6). For t=0 or nilpotent every fraction and colimit class becomes zero at a later stage and UF=0; for t a unit the sequence colimit is M with legs t^(-n); for zero divisors the fraction relation includes the necessary killing power. None of the proofs uses transition monicity. I checked n=0 separately and k negative for shifts. All new-step lengths are below 2000 characters; no long step hides an uncited comparison theorem. There are no statement-only new nodes requiring small-case checks or additional Mathlib searches.

The off-unit generic tools are declared in split_report.tool_uses: ringed-site Grothendieck exactness, the module forgetful interface, exact-functor derived factorization, tensor--Hom adjunction, and the sequence-of-complexes telescope theorem. None replaces a geometric step in the unit's proper-base-change proof. Definitions and the Mathlib triangle-isomorphism lemma are already permitted generic notions/tools.

## Unfinished work

None in the mathematical split. Independent maintainer review remains the prescribed next review after direct delivery. The mandatory server dry run and push are performed with deliver.py; no local DAG validators, git commands, Lean edits, or compilation commands are run.
