# Stage-1 worker report: lem-sfb-adic-stratified-perfect

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-adic-stratified-perfect.json — item, split into six proof steps; no Mathlib match; statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-adic-residue-lisse-perfect-lift.json — new statement, unsplit; Mathlib searches found no match.
- dag/nodes/sec-six-functors-basics/lem-sfb-discrete-noetherian-constructible-serre.json — new statement, unsplit; Mathlib searches found no match.
- citations.json — one verbatim quotation for each step/node citation, including definitions.

Two new nodes, zero Mathlib leaves. No unit file changed: the item is a created intermediate, not the unit key statement. The local text extraction and preparation scripts in this sandbox are working notes, not delivery files.

## Attachments

None. I searched WeilConjectures/ in the read-only slopmaster2 source by the exact blueprint id, adic/stratified-perfect terms, constructible equivalences and adic lisse names. The adic sheaf files concern integral coefficients and degree-zero sheaves, not this arbitrary-Noetherian-ring derived statement. SixFunctors/ProEtale/ConstructibleSheaf.lean:190–196 has a sorry and requires Finite Λ. Its finite set-valued stalks also do not mean finitely presented modules over an infinite field. The exact master source was checked as reference, not as proof evidence.

## WANTED

None. The Bhatt–Scholze PDF, current main-20261015 blueprint and the relevant Stacks TeX/tag table are present.

## Problems found and repaired

The input has an empty proof; its broad statement needs more than the existing integral DVR inputs. In particular the adic datum in lem-weil-pbc-residue-lisse-perfect-lift requires finite perfect quotients, and lem-weil-pbc-finite-ring-constructible-derived-origin requires a finite ring. Neither applies to every complete Noetherian local ring in the item. For instance A=Q[[t]] has infinite residue field; A=F_p[e]/(e²), I=(e), is complete local but its residue module is not perfect over A. I did not strengthen the item's hypotheses to match those existing nodes.

The two new nodes state the missing local lifting and weak Serre inputs, not the equivalence, boundedness or triangulatedness clauses of the item. The proof actually constructs the common strata, verifies coefficient restriction, detects the completion-unit cone, derives boundedness from a finite selection of local models, and descends residue cohomology. Thus it does not move the conclusion to a renamed child. Completion is interpreted with the unrestricted local ringed-ideal definition, not a restricted finite-coefficient definition.

I read the chapter and sk-lem-integral-models unit. This is below the integral-criterion step of det-lem-integral-models-stacks, whose proof invokes sk-prop-integral-criterion and then compares constructibility. The split follows Bhatt–Scholze 6.6.11: local perfect lifting on residue strata, then completeness and residue descent in the reverse direction. It does not change the unit route. Generic off-unit tools are declared only in split_report.tool_uses, leaving maintainer-owned tool_uses alone. No SGA source is used.

## Unfinished work

No missing argument in the item's split is left implicit behind a new conclusion-sized node. The two new input statements are deliberately unsplit, as required for a one-level split. Their eventual proofs remain stage-1 items. The item's natural statement, original metadata and hypotheses are retained.

## Review by NU

I read Definition 6.5.1, Lemmas 6.5.3 and 6.5.8, Lemma 6.6.8 and Proposition 6.6.11 in the local Bhatt–Scholze PDF extraction, together with Definitions 6.3.1/Remark 6.3.2 and the proof of the current blueprint's det-lem-integral-models-stacks. For the new lifting input I read Stacks proetale.tex, Tag 09C6 (lemma-connected-adic-lisse), including its construction of the perfect coefficient complex and compatible isomorphisms, and the 099L constant/completed coefficient paragraph. For the new weak Serre input I read proetale.tex 09B5 (lemma-constructible-serre) and etale-cohomology.tex 03RZ (lemma-constructible-abelian), clause (3). These explicitly allow a Noetherian coefficient ring, without requiring that it be finite as a set. Derived comparison itself is not new: I opened and reused sk-thm-pe-constructible-comparison, which states the needed arbitrary-Noetherian equivalence, and read 09AL and 09B1 as its supporting source material. On a Noetherian scheme the constructible condition used here is the finite stratification condition, with finitely generated = finitely presented values.

For step 1 I opened the seven cited node statements. Immersion-limit preservation actually states exactness on modules over the inverse-image ring; slice localization actually identifies the sites. The constant/completed lemma supplies the Koszul unit for local completeness and the comparison with finite reductions, without finite/perfect quotient hypotheses. The countable-product lemma supplies exact products for every ring sheaf; the derived-product lemma identifies their termwise model; the strict-tower lemma supplies the Roos triangle and exact Rlim. The finite-stratum detection lemma detects zero derived objects over an arbitrary ring sheaf. These statements justify comparing the cone of the completion unit, rather than simply asserting that completeness is stalkwise. I also checked Stacks 093M and the 099L/099M completion paragraphs against this use. All restrictions are to immersions or localized sites, where the coefficient map is an isomorphism.

For step 2 I opened exact geometric stalks, conservative geometric stalks and ringed-topos derived tensor pullback. The last is for an arbitrary morphism of topoi and arbitrary ring sheaves, so it applies to a geometric point and to the constant residue field, including infinite fields. The exact stalk functor turns its derived pullback into ordinary stalks. Tensoring with a vector space is exact by a basis; this proves finite Tor amplitude with the same interval, rather than assuming perfection of the residue field over A. I marked this step non-elementary because the general derived-tensor comparison is an invoked theorem.

For step 3 I opened the intersection-stratification lemma, comparison-pullback, and the new lifting statement. The refinement theorem provides actual fibre-product immersions, not a false scheme-theoretic factorization from set containment. Only finitely many residue cohomology sheaves occur. Every resulting stratum is a quasi-compact locally closed subscheme of the Noetherian X, so the lifting input's Noetherian hypothesis holds; a quotient of a Noetherian affine ring is Noetherian. Complete A and finitely generated I are already hypotheses of the item. The comparison-pullback statement has no finite-ring restriction. Step 2 proves the Tor hypothesis of the lifting input on each stratum. This is exactly where the new local lemma, which has no global stratification conclusion, is needed.

For step 4 I opened torsion-limit completeness, the constant/completed equivalence, the pro-étale site definition and finite-stratum detection. The first really covers arbitrary Noetherian A, arbitrary finitely generated I and bounded complexes of limits of I^n-torsion sheaves, with no finite-set requirement. Idempotent summands commute with the displayed limit, so each finite-projective term is such a limit. The equivalence reflects local completeness. The covering axiom gives finitely many quasi-compact open pieces above a quasi-compact stratum, which is sufficient for uniform term bounds; the original trivializing family need not itself be finite. I take the bounds before using finite-stratum detection. No dimension of X enters.

For step 5 I opened completed-constant reduction, finite-stratum detection, constant-module section properties and the existing constructible comparison statement. The reduction lemma explicitly gives B tensor^L_A A/I = (A/I)_X for arbitrary Noetherian coefficients, including quotients not perfect over A. For a finite-projective model reduction is termwise; a bounded complex of projective terms is K-flat by its finite stupid filtration, since tensoring an acyclic complex with a projective term is acyclic. Exact constant realization gives constant cohomology. This makes the residue cohomology intrinsically constructible with finite-dimensional, hence finitely presented, values. The same finite set of models bounds the residue complex globally. The existing comparison gives precisely the required bounded étale origin, and step 2 supplies its finite Tor amplitude. No unstated finite-coefficient comparison is substituted.

For step 6 I opened the completion-unit statement, exact strict-tower Rlim, derived change of rings, the existing sk-thm-pe-constructible-comparison, the new weak Serre statement and the derived cohomology long exact sequence. Exact completion and its natural unit imply two-out-of-three on unit isomorphisms by a natural map of triangles. Residue reduction is explicitly an exact triangulated functor. The existing comparison identifies bounded constructible étale origin with intrinsic bounded constructible cohomology. For an arbitrary ambient morphism, the kernel/cokernel/extension formula for the cone's cohomology uses exactly the new weak Serre statement; no assertion about arbitrary nonconstructible subobjects is needed. The long exact sequence also bounds the cone. The residue-field calculation removes finite Tor as an extra obstruction. This proves ambient triangle closure, zero and shift closure without citing a definition for a theorem.

The first dry run rejected three quotations as shorter than its 40-character evidence minimum. I replaced these with the full cited statements, without changing the arguments. For C4 I checked every quotation in citations.json literally against the relevant statement, not against its proof; the quoted sentence/formula identifies the part used, and the full statement was read for hypotheses. For C1 I added the general derived-tensor pullback, exact constant realization, and cohomology long exact sequence as explicit existing citations during this review. I used no definition as a replacement for these results. For B I checked standalone objects, definition dependencies, unsplit children with empty proofs, source tag/label pairs, exact logged search strings, ordinary TeX escapes and blueprint ancestry. For D I checked that the local lemma and the weak Serre input are strictly smaller input facts and that the item itself contains the local-to-global argument. For E I checked empty X, zero complex, I=0 (A a field), nilpotent I, infinite residue fields, nonregular complete local A, one stratum and non-finite trivializing families. Empty X uses a vacuous stratification and bound [0,0]. Nilpotent I does not cause a false demand that A/I be perfect over A. Tensor Tor bounds are over the residue field sheaf and not over A. No invertibility of characteristic and no finite-dimensionality of X is introduced.

Mathlib searches used msearch.py only. I ran LeanFinder, LeanSearch, Loogle and source grep for the item and each retained new input, then a second LeanFinder phrasing for each. Searches for the removed draft comparison remain only in the raw search log; its node was removed after finding the broader existing theorem. All services returned successfully for these queries. I read the hits: they concern ordinary étale algebras, abstract derived/triangulated functors, classical completion or condensed profinite sheaves. None states a new input or a one-line generalization of it. The exact query strings and returned declaration names are recorded from searches.jsonl, never invented. Whole-DAG and blueprint searches included the relevant source tags, 'adic lisse', 'locally constant perfect', 'compare-constructible-derived', 'constructible comparison', 'Noetherian ring' and 'perfect'; I also checked the project Lean source before creating the children. The nearest blueprint ancestor and via chain were confirmed with blueprint_refs.py ancestor. Similar declarations were inspected and were either sorried, finite-coefficient, or about sheaves rather than arbitrary derived complexes.


The project KernelCokernel.lean was also inspected for the Serre input: constructible kernels/cokernels are present for Noetherian rings, but the extension theorem has [Finite Λ] and rests on a sorry in IsFiniteLocallyConstantSheaf.of_shortExact (lines 372–383). Thus it does not attach the arbitrary-Noetherian weak Serre statement. This distinguishes finite generation of stalk modules from finiteness of the coefficient set.

## Not duplicates

lem-sfb-adic-residue-lisse-perfect-lift vs def-weil-pbc-adic-coefficient-datum: the existing Tower category and adic coefficient datum concerns integral operations, a specified map, or completion/tower structure under its own hypotheses; it does not assert local perfect lifting from lisse residue cohomology over arbitrary complete Noetherian A,J.

lem-sfb-adic-residue-lisse-perfect-lift vs def-weil-pbc-completed-base-change-map: the existing Completed base-change map concerns integral operations, a specified map, or completion/tower structure under its own hypotheses; it does not assert local perfect lifting from lisse residue cohomology over arbitrary complete Noetherian A,J.

lem-sfb-adic-residue-lisse-perfect-lift vs def-weil-pbc-completed-pullback: the existing Completed pullback concerns integral operations, a specified map, or completion/tower structure under its own hypotheses; it does not assert local perfect lifting from lisse residue cohomology over arbitrary complete Noetherian A,J.

lem-sfb-adic-residue-lisse-perfect-lift vs def-weil-pbc-intrinsic-completion: the existing Intrinsic derived completion concerns integral operations, a specified map, or completion/tower structure under its own hypotheses; it does not assert local perfect lifting from lisse residue cohomology over arbitrary complete Noetherian A,J.

lem-sfb-adic-residue-lisse-perfect-lift vs lem-weil-pbc-constant-completion-equivalence: the existing scalar-restriction/completion calculus is cited; it constructs no local constant perfect coefficient model.

lem-sfb-adic-residue-lisse-perfect-lift vs lem-weil-pbc-normalized-constructible-local-effectivity: the existing theorem starts with a normalized tower over a restrictive adic datum and does not assert projective local terms; the new lift starts with one complete complex and lisse residue cohomology.

lem-sfb-adic-residue-lisse-perfect-lift vs lem-weil-pbc-reconstruction-uniform-tower: the existing input is an already uniform restrictive adic tower on a finite-type field scheme; the new lift permits arbitrary Noetherian complete coefficients and any Noetherian scheme.

lem-sfb-adic-residue-lisse-perfect-lift vs lem-weil-pbc-residue-lisse-perfect-lift: the existing lift assumes a finite perfect-quotient adic datum and a constant-perfect residue complex; the new local theorem permits arbitrary Noetherian quotients and lisse residue cohomology of finite Tor amplitude.

lem-sfb-adic-residue-lisse-perfect-lift vs prop-weil-pbc-direct-image-limits: the existing Direct image, derived limits, and completeness concerns integral operations, a specified map, or completion/tower structure under its own hypotheses; it does not assert local perfect lifting from lisse residue cohomology over arbitrary complete Noetherian A,J.

lem-sfb-adic-residue-lisse-perfect-lift vs prop-weil-pbc-koszul-reconstruction: the existing Koszul and quotient reconstruction concerns integral operations, a specified map, or completion/tower structure under its own hypotheses; it does not assert local perfect lifting from lisse residue cohomology over arbitrary complete Noetherian A,J.

lem-sfb-adic-residue-lisse-perfect-lift vs det-prop-diagonal-tower-limit: the existing The $\ell$-adic diagonal class over the completed coefficient sheaf concerns integral operations, a specified map, or completion/tower structure under its own hypotheses; it does not assert local perfect lifting from lisse residue cohomology over arbitrary complete Noetherian A,J.

lem-sfb-adic-residue-lisse-perfect-lift vs det-thm-sf-pf-adic-open: the existing Integral open direct image preserves constructibility concerns integral operations, a specified map, or completion/tower structure under its own hypotheses; it does not assert local perfect lifting from lisse residue cohomology over arbitrary complete Noetherian A,J.

lem-sfb-adic-residue-lisse-perfect-lift vs sk-thm-sf-pf-adic: the existing Open direct image and projection formula concerns integral operations, a specified map, or completion/tower structure under its own hypotheses; it does not assert local perfect lifting from lisse residue cohomology over arbitrary complete Noetherian A,J.

lem-sfb-discrete-noetherian-constructible-serre vs lem-v2-constructible-prime-field-filtration: the existing Finite coefficients admit prime-field extension trees is a finite-stage operation, coefficient identification, or particular morphism result; it does not state kernel, cokernel and extension closure of constructible sheaves over every discrete Noetherian ring.

lem-sfb-discrete-noetherian-constructible-serre vs lem-weil-pbc-constructible-module-finite-presentation: the existing A constructible sheaf of modules on a qcqs scheme is a cokernel of a map between finite sums of extensions by zero of Lambda from affine etale objects is a finite-stage operation, coefficient identification, or particular morphism result; it does not state kernel, cokernel and extension closure of constructible sheaves over every discrete Noetherian ring.

lem-sfb-discrete-noetherian-constructible-serre vs lem-weil-pbc-constructible-stratification-intersection: the existing Common refinement of two stratifications with constructible strata is a finite-stage operation, coefficient identification, or particular morphism result; it does not state kernel, cokernel and extension closure of constructible sheaves over every discrete Noetherian ring.

lem-sfb-discrete-noetherian-constructible-serre vs lem-weil-pbc-module-sheaf-colimit-constructible-data: the existing Filtered constructible maps with factorization and relations is a finite-stage operation, coefficient identification, or particular morphism result; it does not state kernel, cokernel and extension closure of constructible sheaves over every discrete Noetherian ring.

lem-sfb-discrete-noetherian-constructible-serre vs lem-weil-pbc-pullback-preserves-bounded-constructible: the existing Pullback preserves bounded constructibility is a finite-stage operation, coefficient identification, or particular morphism result; it does not state kernel, cokernel and extension closure of constructible sheaves over every discrete Noetherian ring.

lem-sfb-discrete-noetherian-constructible-serre vs thm-constructible-serre: the existing weak Serre theorem requires a finite ring Λ; the new statement allows all discrete Noetherian rings, including Q.

lem-sfb-discrete-noetherian-constructible-serre vs lem-kun-03sa: the existing Constructible generation is a finite-stage operation, coefficient identification, or particular morphism result; it does not state kernel, cokernel and extension closure of constructible sheaves over every discrete Noetherian ring.

lem-sfb-discrete-noetherian-constructible-serre vs lem-weil-pbc-constant-subsheaf-generic: the existing Generic constancy of a subsheaf of a constant finite sheaf is a finite-stage operation, coefficient identification, or particular morphism result; it does not state kernel, cokernel and extension closure of constructible sheaves over every discrete Noetherian ring.

lem-sfb-discrete-noetherian-constructible-serre vs lem-weil-pbc-constructible-subobjects-noetherian: the existing Subsheaves of a constructible sheaf on a Noetherian scheme is a finite-stage operation, coefficient identification, or particular morphism result; it does not state kernel, cokernel and extension closure of constructible sheaves over every discrete Noetherian ring.

lem-sfb-discrete-noetherian-constructible-serre vs lem-weil-proetale-dbc-triangulated: the existing derived triangle-closure theorem assumes a finite ring; the new sheaf-level weak Serre theorem permits an infinite coefficient set.

Conceptual near-matches:

lem-sfb-discrete-noetherian-constructible-serre vs sk-thm-pe-constructible-comparison: the comparison theorem is reused verbatim for derived étale origin. Its statement asserts equivalence, not weak Serre closure of either subcategory, which is a separate smaller sheaf theorem.

lem-sfb-discrete-noetherian-constructible-serre vs sk-def-sfb-bounded-constructible: the definition includes a triangulatedness observation for its broader coefficient framework; the new statement supplies the sheaf-level weak Serre fact from Stacks 09B5/03RZ, so no definition is used as a theorem about constructibility.

lem-sfb-discrete-noetherian-constructible-serre vs det-pe-classical-derived-weak-serre: the latter concerns all classical sheaves; it does not impose or preserve finitely presented stalk models or finite constructible stratifications.

lem-sfb-adic-residue-lisse-perfect-lift vs lem-weil-pbc-integral-stratified-perfect-characterization: the latter requires DVR coefficients, finite-dimensional X and invertibility, and has global stratification conclusions; it cannot supply the general local input here.

lem-sfb-adic-residue-lisse-perfect-lift vs det-lem-int-integral-heart-local-model: the latter is integral-DVR and tied to the standing finite-type setting; the new input is local and permits arbitrary complete Noetherian A,J.

## Second reading by NU

- Item statement: checked against Bhatt–Scholze Definition 6.5.1, Lemma 6.5.3, and Proposition 6.6.11; hypotheses, finite stratification, boundedness, and triangulated closure agree, including empty schemes and zero complexes.
- Step 1: checked every cited statement for restriction, slice localization, completion units, products, Roos limits, and stratum detection; the cited nodes provide exactly the asserted limit and exactness facts.
- Step 2: checked geometric-stalk exactness/conservativity and derived tensor pullback; the field-vector-space argument gives the stated Tor interval, including infinite residue fields.
- Step 3: checked the intersection-refinement, comparison-pullback, and local lifting statements; fibre-product immersions and Noetherian strata supply all hypotheses, with no set-theoretic factorization used.
- Step 4: checked torsion-limit completeness, completion equivalence, pro-étale covering, and finite-stratum detection; idempotent finite-projective terms and the empty-stratum bound are justified.
- Step 5: checked completed reduction, exact constant realization, finite-projective K-flatness, comparison, and Tor amplitude; the reduction has finite-dimensional stalk values and the cited comparison applies to arbitrary Noetherian residue rings.
- Step 6: checked completion-unit triangles, exact change of rings, long exact cohomology, weak Serre closure, and comparison; the cone argument supplies bounded triangle closure without finite-coefficient assumptions.
- New node `lem-sfb-adic-residue-lisse-perfect-lift`: checked standalone B1–B7 form, Stacks 09C6 and Bhatt–Scholze Lemma 6.6.8 source, definition dependencies, duplicate searches, edge cases, and empty proof; verdict correct unsplit input.
- New node `lem-sfb-discrete-noetherian-constructible-serre`: checked standalone B1–B7 form, Stacks 09B5 and 03RZ source, definition dependencies, duplicate searches, edge cases, and empty proof; verdict correct unsplit input.
- Changes: none; the worker’s statements, six proof steps, citations, search log, and blueprint metadata were already consistent. The required dry run is being rerun through the delivery helper.
