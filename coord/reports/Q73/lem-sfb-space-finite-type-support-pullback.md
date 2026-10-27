# Stage-1 delivery by Q73

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-finite-type-support-pullback.json`: the unchanged statement, now split in six steps. No Mathlib match for the algebraic-space theorem.
- `citations.json`: a verbatim statement quotation for every node used by every proof step.
- `searches.jsonl`: actual msearch.py records, retained with this delivery.

New nodes: 0. New Mathlib leaves: 0. The scheme support theorem and all comparison inputs already exist. The sandbox had no previous node or report; I copied the current item and retained its citations, blueprint ancestry and earlier Mathlib searches.

## Attachments

None. I searched the live `lean/WeilConjectures/` by the exact blueprint id, finite-type support terminology, finiteTypeSupport/FiniteTypeSupport, and support/pullback terminology. The Chow algebraization docstring mentions a support pullback argument, but its declaration concerns a coherent algebraization on schemes and does not state this algebraic-space theorem. It is not an attachment. No Lean files were written and no compiler, Lake or build tool was run.

## WANTED

None. All sources used are present in `literature/stacks-project/`.

## Findings and corrections

No statement dispute and no change to the statement or its hypotheses. Stacks 07TZ (spaces-morphisms.tex, lemma-support-finite-type), clauses (1) and (3), says precisely what the item requires. In particular finite generation, rather than finite presentation or Noetherianity, suffices. The dependency lem-sfb-space-etale-chart-support supplies independence of the geometric representative and the comparison with ordinary scheme support.

The live item had no proof. I supplied its argument using compatible etale scheme charts and the existing scheme support theorem 056J. Closedness follows exactly by the chart argument in 07TZ. For arbitrary pullback, 07TZ's geometric-stalk/Nakayama calculation is already present at the scheme level in lem-weil-pbc-support-pullback-finite-type; I explicitly identify the two pullbacks on a common scheme chart and apply that theorem there. This is recorded as an agent assembly, not as a verbatim transcription of the source's geometric-stalk proof. It changes no blueprint chapter or unit route.

I corrected two potential citation gaps while planning: the quasi-coherent equivalence alone does not assert finite-type reflection, so step 1 also cites lem-sfb-scheme-etale-module-exact-finiteness-comparison; and a scheme pullback theorem cannot be applied directly to g:Y→X when the spaces need not be schemes, so steps 3–4 construct the actual scheme map a:V→U and identify its module. The fibre product Z=Y×_X U is allowed to be an algebraic space; only its atlas V is taken to be a scheme.

The generic tool uses outside the item's unit are declared in split_report.tool_uses: the scheme Zariski/etale equivalence, scheme support theorem, fibre products and cover permanence, representable etale scheme tests, canonical tensor composition, and scheme quasi-coherent pullback. These are basic comparison and geometry inputs, not any trace-formula or duality route. No SGA source is used.

## Not duplicates

No new nodes were created. Existing nodes reused instead of adding duplicates include lem-sfb-scheme-etale-module-exact-finiteness-comparison (05VG), lem-trf-scheme-zariski-etale-quasi-coherent-equivalence (03DX/03LC), lem-weil-pbc-support-pullback-finite-type (056J), and lem-trf-space-chart-adjunction-tensor-realization (03D8). The more specialized lem-sfb-space-module-base-change-flat-proper-support requires finite presentation, relative flatness and proper support, so it does not give this item under its hypotheses and is not cited.

## Sources and Mathlib searches

I read spaces-morphisms.tex 07TY (lemma-support-covering) and 07TZ (lemma-support-finite-type), including their proofs; morphisms.tex 056J and its proof; spaces-properties.tex section-properties-modules and 05VQ (lemma-stalk-pullback-quasi-coherent); descent.tex 03DX (proposition-equivalence-quasi-coherent), 03LC (proposition-equivalence-quasi-coherent-functorial), and 05VG (lemma-equivalence-quasi-coherent-properties); sites-modules.tex 03D7, 03D8 and 03DO; modules.tex 01BG; spaces.tex 02X2; spaces-topologies.tex 041F; and spaces-properties.tex 03EC. These supply respectively the chart reduction, scheme theorem, local module properties, comparison and finite-type reflection, tensor composition, scheme quasi-coherence, and compatible cover geometry.

Actual logged searches used leanfinder, leansearch, loogle and grep. The first item phrasing found scheme ideal-sheaf supports; a second natural-language phrasing found Module.isClosed_support and Module.mem_support_iff_nontrivial_residueField_tensorProduct. I read Mathlib/RingTheory/Spectrum/Prime/Module.lean:46, Mathlib/RingTheory/LocalRing/Module.lean:112, IdealSheaf/Basic.lean:319, and IdealSheaf/Functorial.lean:74. The ring-module theorems lack the algebraic-space/sheaf comparisons; ideal-sheaf support is the associated closed subscheme locus. None is a one-line specialization to this item. The extra local-presentation searches found only the generic pullback construction, its adjunction and definitions of finite type/quasi-coherence; they prompted reuse of the existing comparison nodes, not a new lemma. Every added search entry has the exact query text and tool from searches.jsonl; earlier imported search entries were retained as instructed.

The whole-DAG searches covered 07TZ, support-finite-type, the scheme support and pullback tags, and chart/finiteness keywords. blueprint_refs.py searches covered 07TZ, support-finite-type, closed support, finite type module, tensor pullback support, and the initial wider support finite type query. No blueprint node states this same algebraic-space result. The closed-support hits concern cohomological support, not finite-type structural modules. I read the latest chapter and sk-thm-sf-ctf-stability unit, plus its direct-images proof (3). The original null ancestor reported by blueprint_refs.py and the full existing via chain are preserved. This is a prerequisite below that route, not the unit's statement, so no unit realization fields are edited.

## Review by Q73

I checked the unchanged statement against 07TZ (1),(3), with 07TY for the support convention. There are no new-node statements needing source or small-case review. I read all eleven distinct cited nodes' statements, rather than their proofs alone, and copied them verbatim into citations.json. The proof's longest step is under 1000 characters and none hides a long argument.

Step 1 uses def-trf-algebraic-space for etale pullback as restriction, lem-trf-scheme-zariski-etale-quasi-coherent-equivalence for the actual inverse equivalence, and lem-sfb-scheme-etale-module-exact-finiteness-comparison for finite-type reflection. Each says that clause explicitly; the last statement makes no Noetherian assumption. Restriction of the given local presentations and generating families stays local, so the step introduces no flatness condition. It is not legitimate to get finite-type reflection from the equivalence's invertible-module clause, and I do not do so.

Step 2 uses (1) of the scheme theorem lem-weil-pbc-support-pullback-finite-type, the exact inverse-image identity of lem-sfb-space-etale-chart-support, and the all-chart final-topology definition def-a1-space-point-topology. The module on U is quasi-coherent and Zariski finite type by step 1. I checked every chart rather than assuming that the topology definition already supplied a quotient-map theorem for a particular atlas.

Step 3 uses the atlas existence in def-trf-algebraic-space, the fibre-product existence and base-changed covering clause of lem-trf-space-fibre-products-etale-covers, and composition of representable surjective etale maps from lem-trf-space-representable-etale-scheme-tests. These statements really allow Z to be an algebraic space. The composite p is surjective etale, a is a map between schemes, and gp=ea is an equality from the fibre product, not a set-theoretic factorization.

Step 4 uses the arbitrary tensor-composition and etale-restriction clauses of lem-trf-space-chart-adjunction-tensor-realization twice, then the arbitrary scheme-pullback comparison of lem-trf-scheme-zariski-etale-quasi-coherent-equivalence. I checked that the latter's quasi-compact separated hypotheses belong only to its pushforward clause, which is unused. The composition comparison applies to the canonical module functors in the item, not an independently chosen pullback. The local tensor formula is written, so no unspecified transport is used.

Step 5 uses lem-weil-pbc-module-pullback-quasi-coherent only for a:V→U, the finite-type pullback clause of lem-weil-pbc-support-pullback-finite-type only for the finite-type N_U, and the forward finite-type direction of lem-sfb-scheme-etale-module-exact-finiteness-comparison. It uses the equivalence already established in step 1 for the associated module's quasi-coherence. The locality assertion is the local-presentation definition def-trf-space-quasi-coherent-module plus the explicit finite-generation definition in the item. The representable etale scheme-test node supplies the covering W×_Y V→W on every chart W, so it is enough to use these local presentations on V. No general flatness-preservation or left-exactness of tensor pullback is used.

Step 6 applies lem-sfb-space-etale-chart-support to both M and g^*M, the latter only after quasi-coherence was proved in step 5. It applies exactly the arbitrary-pullback clause (3) of lem-weil-pbc-support-pullback-finite-type to a and N_U. The pointwise map in def-a1-space-point-topology respects gp=ea by its definition on field-valued representatives. Surjectivity was established for p in step 3. Equal preimages of subsets under this surjection imply equality by choosing a point above each y; no non-elementary descent claim is concealed here.

Against delivery-errors B1–B10: there are no new nodes, no duplicate or clause-relabelling node, the original notions are stated or have their actual definition dependencies, TeX is single-escaped on decoding, tags include their source labels, blueprint references are retained and searched, the item was checked for a completed project declaration, and searches are actual logged queries. Against C1–C8: all geometric/comparison/scheme inputs above are cited as nodes; no node's proof is used for a stronger assertion; uses and proof_deps agree; the generic off-unit tools are declared. Against D1–D5: the six steps actually assemble the result using existing smaller theorems; no content is transferred to an alias node or circularly assumed. Against E1–E7: I checked the precise scheme/space types and each hypothesis at the invocation, wrote the comparison formulas, and found no source error.

Small cases: zero module gives empty support on both sides; an empty X forces Y empty and the formulas are vacuous; an empty Y causes no surjection-of-points exception. Identity and etale g reduce to the already cited chart comparison. For the nonflat example Spec(Z/2)→Spec(Z), the finite module Z/2 has support V(2), and both supports after pullback are the entire one-point space. A localization avoiding 2 gives empty inverse-image support and zero tensor pullback. These check that no flatness or surjectivity of g was accidentally used. Finite generation is essential in the cited scheme theorem, and it is retained throughout.

## Unfinished work

None in the mathematical split. The required server dry run exited successfully: `OK (not pushed) deliver/Q73/lem-sfb-space-finite-type-support-pullback at ccab3003978: preflight passed`. The delivery command saved the durable dry-run receipt. This is the direct-delivery brief: Q73 performs the push and the maintainer supplies the independent review.
