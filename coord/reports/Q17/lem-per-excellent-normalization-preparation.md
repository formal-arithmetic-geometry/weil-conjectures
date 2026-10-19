# Worker report: lem-per-excellent-normalization-preparation

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-excellent-normalization-preparation.json: item, statement, split into eight steps. No Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-componentwise-normalization-affine-charts.json: new statement-only lemma, unsplit; no Mathlib match. Its role is the affine description of the componentwise construction, not any conclusion clause of the item.
- citations.json: one verbatim statement quotation for every proof-step citation. Search outputs, searches.jsonl and the earlier draft script are retained in the sandbox.

## Attachments

None. Searches of /home/ubuntu/weil-src-slopmaster2/WeilConjectures by the exact item tag and by excellent/normalization, including componentwise normalization, found no declaration giving all the clauses for arbitrary reduced Noetherian excellent schemes. Existing curve normalization interfaces are over fields and do not give this item. Upstream master is reference material only. No Lean was written or compiled.

## Wanted literature

None. All source material needed is in literature/stacks-project/.

## Findings and changes

The sandbox originally contained the unchanged unsplit item, saved search outputs and an unexecuted proof-writing script, but no report. I retained that work, checked it against the current repository and completed its proof. The repository item is still unsplit, with the same statement and ancestry. I clarified the existing conventions: Noetherian means locally Noetherian and quasi-compact, and excellent means excellent rings on every affine open. I added the definition of generic point to statement dependencies. These are expansions of the original hypotheses and conclusion, not changes to their mathematical meaning. No STATEMENT-DISPUTED correction was needed.

The argument follows morphisms.tex Tag 035S, lemma-nagata-normalization, directly on affine rings. It does not create a child asserting finiteness of normalization. Likewise normality is proved from the existing integral-closure and localization lemmas, excellence from finite-type stability and affine-cover locality, and the dense open from explicit denominators of finite module generators. Thus no child restates an item clause. No step exceeds 2000 characters.

The blueprint ancestor is lem-per-artin-gabber-affine-curve through lem-per-potential-dualizing-uniqueness, lem-per-finite-regular-reduction-dualizing, lem-per-qbar-generic-duality-model and lem-per-qbar-middle-tstructure. I read the chapter, unit and current main-20261015 ancestor text. This item is the algebraic normalization preparation requested by the dualizing-uniqueness descendant; it changes no unit route or unit realization. The inherited provenance refers to the original dimension-normalized duality expansion; it is not a claim that the current ancestor's Step 3 itself states this normalization lemma.

Generic tool uses from other units are declared in split_report.tool_uses: quasi-excellence implies Nagata; stability of excellence under finite type algebras; excellence on an affine cover; quasi-compactness of affine schemes; scheme sobriety; affine opens form a basis. These supply general algebra or scheme topology, with no replacement of a perverse unit argument. Definitions and the existing proper-base-change normalization algebra interfaces are reused.

## Search evidence

The saved searches.jsonl and all eight saved output files were read and retained. The item was searched with LeanFinder on excellent normalization, LeanSearch on Nagata normalization/excellence, Loogle on normalization and IsFinite, and grep for excellent|nagata|normalization. The child was searched with LeanFinder on the product of minimal-prime integral closures, LeanSearch on disjoint unions of component normalizations, Loogle for normalizationObjIso, and grep for the relative normalization affine/coproduct interfaces. The two natural-language formulations address each statement from different directions. The actual outputs are recorded verbatim in mathlib_searches, with their exact queries; no unavailable search is called a negative result.

I read Mathlib/AlgebraicGeometry/Normalization.lean, especially fromNormalization_preimage at line 184 and normalizationObjIso at line 220. They concern the relative normalization of a given qcqs morphism. Identifying that construction with the componentwise absolute normalization, and computing the product over minimal primes, needs additional mathematics, so the child is unsplit with these declarations recorded only as candidates. The searches did not return a general excellence/Nagata finiteness theorem. There are zero new Mathlib leaves.

Before creating the child I searched the whole DAG for 035P, 0CDV, 035S, 035Q, affine/component normalization, and examined the statements below. blueprint_refs.py ancestor confirmed its ancestry; blueprint_refs.py search for normalization, integral closure, 035P and componentwise normalization supplied no blueprint node stating the child. Existing def-sc-normalization specifies the integral function-field construction, not the comparison of componentwise normalization with an arbitrary reduced affine chart.

## Not duplicates

lem-per-componentwise-normalization-affine-charts vs def-weil-pbc-reduced-normalization: the existing node defines the componentwise disjoint-union construction; the new lemma identifies its inverse image on any affine open with the minimal-prime integral-closure product.

lem-per-componentwise-normalization-affine-charts vs lem-weil-pbc-reduced-normalization-over-normal-reduction: the existing node assumes a finite-type scheme over a field and a normal reduction on the chosen open; it gives an isomorphism over that open, not the general affine chart.

lem-per-componentwise-normalization-affine-charts vs lem-weil-pbc-reduced-algebraic-normalization-field-change: the existing node requires finite type over a field and asserts normalization and separable field-change properties; it does not assert the product formula and does not cover arbitrary locally Noetherian schemes.

lem-per-componentwise-normalization-affine-charts vs lem-exc-weakly-etale-normalization-tensor: the existing node is about a Noetherian universally catenary local domain and weakly etale normalization base change, not normalization charts of arbitrary reduced locally Noetherian schemes.

lem-per-componentwise-normalization-affine-charts vs lem-trf-conductor-smooth-base-change: the existing node treats finite-type schemes over Q and the conductor ideal; it does not state the general componentwise affine formula.

lem-per-componentwise-normalization-affine-charts vs lem-trf-normalization-singular-skyscraper: the existing node concerns reduced finite-type pure curves over an algebraically closed field, coherent normalization quotients and completions; the new statement imposes neither a field nor a dimension bound and describes full affine inverse images.

lem-per-componentwise-normalization-affine-charts vs lem-weil-pbc-reduced-curve-normalization: the existing node assumes separated finite type of dimension at most one over an algebraically closed field and constructs a smooth normalization; no product formula is stated.

lem-per-componentwise-normalization-affine-charts vs lem-sbc-finite-affine-normalization-coproduct: the existing node computes relative normalization of a morphism already presented as a finite coproduct of affine schemes; identifying the componentwise absolute normalization with the minimal-prime closure product is not in its statement.

lem-per-componentwise-normalization-affine-charts vs lem-sbc-normalization-affine-localization: the existing node compares relative normalization under a given localization morphism of affine bases; it does not identify componentwise normalization or the product of component closures.

## Review by Q17

I read morphisms.tex Tag 035P (lemma-description-normalization), including the four clauses and its proof, and Tag 0CDV (lemma-normalization-in-terms-of-components). Their hypotheses are satisfied for a reduced locally Noetherian scheme: every quasi-compact open has finitely many irreducible components. Parts (1), (3), (4) give precisely the minimal-prime closure product and its structural map; 0CDV identifies the normalization convention. A finite product spectrum is the disjoint union of factor spectra, including the zero-factor case. The new node states this comparison without asserting finiteness, normality, excellence or a dense isomorphism locus, has no proof, and defines minimal prime and fraction field explicitly. It cites the actual definitions of reducedness, local Noetherianness, componentwise normalization, spectrum, integral closure and coproduct.

For the item I read Tags 035S and 035Q (lemma-normalization-normal), Tag 0BAJ (lemma-birational-isomorphism-over-dense-open), more-algebra.tex Tags 07QV and 07QU, and morphisms.tex Tag 0HAB. All agree with the hypotheses here. No separatedness, finite type over a field, dimension bound or global integrality is added.

Step 1 uses the new chart statement for both the affine product and disjoint-union descriptions and the componentwise definition for the empty case. The finite-morphism definition gives the relevant affine criterion. Step 2 uses def-exc-excellent-ring to obtain quasi-excellence, lem-exc-quasi-excellent-nagata for Nagata, and the Nagata/Japanese definitions for finiteness of each closure in the degree-one field extension. The passage from quotient-module generators to A-module generators and then to the finite product is written out. No finiteness theorem is smuggled through a definition.

Step 3 uses precisely the injective-integral lying-over statement: each quotient domain embeds in its closure inside its own fraction field. Its spectral image is the component V(p_i), and the components cover. Step 4 applies lem-weil-pbc-integral-closure-finite-extension-normal only to a domain and the finite extension K_i/K_i, then lem-weil-pbc-spec-domain-stalks-function-field and lem-weil-pbc-localization-normal-domain to prime localizations. The prime complement excludes zero. These three statements actually assert all the needed normality and stalk identifications; Tag 034L and Tag 00GY in algebra.tex confirm them.

Step 5 uses the proved module finiteness, the elementary implication finite module algebra implies finite type, lem-exc-finite-type-localization-excellent with S={1}, and lem-trf-excellent-scheme-affine-cover with the actual normalization summand cover. Excellence implies Noetherianness by its definition. Quasi-compactness uses a finite affine subcover of X and the existing lem-weil-pbc-affine-scheme-qcqs on the finitely many inverse-image summands. I corrected the draft's previously uncited affine quasi-compactness here.

Step 6 uses lem-weil-pbc-noetherian-finitely-many-components, lem-weil-pbc-scheme-sober and lem-weil-pbc-affine-opens-basis, whose statements I opened, to choose the stated finite list and affine neighbourhoods avoiding the other components. The reduced/irreducible criterion is in def-pc-integral-scheme itself; the open W_i is nonempty because it contains eta_i. I added the sobriety and basis citations and marked this step non-elementary. The finite list of components makes the complement of the other components open; no intersection of arbitrary affines is assumed affine.

Step 7 uses the chart lemma and lem-weil-pbc-integral-closure-commutes-localization. I checked Tag 0307 in algebra.tex. There are finitely many module generators, all denominators are nonzero in the domain R_i, their product is nonzero, and localizing each generator gives both inclusions (C_i)_{s_i}=(R_i)_{s_i}. The formula supplies an isomorphism on the full inverse image of D(s_i), not a selected source open. This is the elementary denominator computation, written out, not a new birational-isomorphism lemma. Step 8 uses uniqueness of two-sided inverses on overlaps; I expanded the gluing into continuous maps and structure-sheaf maps glued by the sheaf axiom, with locality checked on stalks. Closure of the union contains every Z_i because the union contains eta_i. No unsupported exchange or base change is used.

Small cases checked: X empty and U empty give empty normalization and zero-factor product; a field gives its identity normalization and s=1; a normal domain has identity closure; k[x,y]/(xy) gives two normalization summands and the dense opens away from their intersection; k[t^2,t^3] gives k[t], and finitely many denominators give a nonzero principal isomorphism locus. The child also permits a locally Noetherian scheme with infinitely many global components: an affine open sees only finitely many, so the statement does not silently require global quasi-compactness. A non-Nagata domain does not contradict the child, since the child asserts no finite-module property.

I checked B1–B10, C1–C8, D1–D5 and E1–E7 against the written nodes and sources. The corrections above address actual citation gaps in the draft. There is one genuine new structural lemma, with no duplicate or item-clause child, exact logged searches and unchanged source provenance. citations.json quotes the full verbatim statement for each cited node so every use can be checked independently. No SGA source, compiler, live-project write or launcher modification is involved.

## Unfinished work

None for this stage-1 item. The new affine-chart lemma is deliberately statement-only for a later worker, as required by a one-level split. Delivery remains subject to the required remote dry run and maintainer review.
