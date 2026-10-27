# Stage-1 report: lem-sf-native-forget-constructible-criterion

## Files written

- dag/nodes/sec-six-functors/lem-sf-native-forget-constructible-criterion.json: statement, split into seven steps; no Mathlib match for the whole criterion.
- citations.json: a verbatim statement excerpt for all 15 step citations.
- searches.jsonl: actual msearch.py records; retained separately from the inherited searches.
- assemble.py: sandbox-only assembly script, not a delivery file.

No new nodes; no new Mathlib leaves. Every non-elementary input already has a node. The original statement, statement dependencies, source and inherited metadata are unchanged.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, the item id, IsAdicConstructibleSheaf, boundedAdicConstructible and native constructibility. The native definitions and the qcqs global-stratification theorem exist, but none of those declarations supplies the full coefficient-encoding, derived-cohomology and finite-Tor criterion. In particular the native predicates alone are not an attachment.

## WANTED

None. Read the local Bhatt-Scholze PDF, Definitions 6.8.3, 6.8.6 and 6.8.8; the existing coefficient and comparison nodes supply the additional interfaces. No SGA source was used.

## Issues found and corrected

The seed was statement-only. Its source correctly describes a native comparison extracted from earlier steps, rather than claiming Bhatt-Scholze states this particular equivalence. The proof is therefore marked agent-written. There is no imported blueprint ancestor: tools/blueprint_refs.py ancestor prints None; the inherited null ancestor and precise audit-seed place are retained. Searched the entire blueprint for constructibility, stratification, scalar local model, native bounded constructibility, and cohomology comparison, and read candidate DAG statements.

The generic sk-def-sfb-bounded-constructible uses a different general ring-object finite-presentation predicate. This proof uses the item's explicit finite-constant-scalar-model meaning of D^b_c, as specified precisely by det-def-sfb-constructible-tor-amplitude(1)-(2) and sk-def-sfb-constructible. It does not silently identify arbitrary ring-object finite presentations with scalar presentations. No statement repair is needed because the item explicitly fixes the coefficient-module meaning.

lem-sfb-noetherian-global-constructibility concerns a constant discrete ring sheaf, so it is not used for the non-discrete condensed coefficient. Instead lem-sfb-constructible-zariski-locality states the required condensed-module result. Likewise the bounded derived fixed-pair cohomology lemmas concern pairs in a derived category; this proof uses exact functors on ordinary derived categories of abelian fixed pairs instead.

## Not duplicates

No new nodes were created. Reused lem-sf-weil-verdier-module-constructibility-comparison for the same-stratum model comparison, lem-sfb-constructible-zariski-locality for the global refinement, lem-sf-native-weil-constructible-abelian for exact conservative forgetting, lem-pur-exact-derived-cohomology-coherence for the natural derived comparison, and det-def-localizing-closure-ctf-equals-bc for the Tor bound. None is a newly relabelled clause of this item.

## Review by N0

I read the native definitions in Adic/Constructible.lean (lisse, stratified lisse, and Zariski-local constructibility), the global finite-stratification construction in Adic/ExtensionByZero.lean, and the ordinary-derived-category setup in WeilSheaf/Category.lean. Bhatt-Scholze 6.8.3, 6.8.6 and 6.8.8 fix the local free, finite-stratification and bounded-cohomology conventions. The paper does not itself assert this project's native module encoding, so that part is explicitly assembled from existing DAG statements.

Step 1 uses exactly the geometric-fibre conclusion of lem-pod-separated-finite-type-base-change and the affine-base qcqs conclusion of lem-weil-pbc-qcqs-over-affine. The field spectrum is affine; separatedness and finite type are hypotheses on T_0 and are supplied after base change by the first node. Thus the later global-locality and Tor statements really have their qcqs hypothesis.

Step 2 uses the sectionwise action transport and preservation of restrictions stated by lem-sf-native-encoding-derived-operations. The tensor/free identification is written by mutually inverse basis formulas, including the balancing relation; no tensor comparison theorem is hidden. A finitely presented module over the scalar field has a finite basis, and rank zero gives the zero module. Ranks are chosen separately for each covering member.

Step 3 cites the statement of lem-sf-weil-verdier-module-constructibility-comparison, which explicitly gives restriction to locally closed strata, the same covering, and both directions of the model comparison. Its transport is the same action transport along theta as E_T, rather than an unspecified abstract equivalence. lem-sfb-constructible-zariski-locality explicitly treats condensed coefficient modules and equates affine-local constructibility with a single global finite stratification on a qcqs scheme; its hypotheses are Step 1. Restrict the local models to affine neighbourhoods and apply that node, then transfer its strata back by the inverse encoding. sk-def-sfb-constructible explicitly supplies the finite global coefficient stratification in the reverse direction. I read Stacks 095E, etale-cohomology.tex lemma-constructible-quasi-compact-quasi-separated, as background for finite refinement, without applying its discrete-sheaf statement directly to the condensed ring.

Step 4 uses only the exact and conservative forgetting clause of lem-sf-native-weil-constructible-abelian and the exact equivalence clause of lem-sf-native-encoding-derived-operations. The statement of lem-pur-exact-derived-cohomology-coherence supplies the natural comparison on unbounded derived categories and its composition normalization. I checked Stacks 015F, derived.tex lemma-right-derived-exact-functor, and the native source IsoAlgebra.lean and MapDerivedCategoryHomologyNatIso.lean. Applying the cohomology comparison twice is legitimate for every C, and requires no boundedness, K-injective choice or identification with pairs in a derived category. I also checked dependency reachability for the selected input nodes: none depends on this item.

Step 5 uses exactness and conservativity from those same statements. The proof exhibits the zero-object arrow whose image is invertible; conservativity then proves its source object zero. It does not claim that forgetting is faithful on derived morphisms. Degreewise vanishing detection gives every interval directly, including an empty-support complex.

Step 6 unfolds exactly the WCder predicate in def-sf-native-weil-derived-framework and the coefficient bounded-constructible predicate in det-def-sfb-constructible-tor-amplitude(1)-(2). Steps 3-5 identify all of their conditions in both directions. Step 7 applies clause (2) of det-def-localizing-closure-ctf-equals-bc with the finite-subextension-valued algebraically closed field coefficient and qcqs T; it gives precisely [a-1,b]. The converse follows from the inclusion in clause (4) of the Tor-amplitude definition. I read both complete statements, including their coefficient convention, rather than borrowing an integral or finite nonregular-ring assertion.

For small cases I checked T empty, the zero sheaf and complex, r=0, one-point schemes, different ranks on disjoint covering members, and a sheaf placed in a single arbitrary integer degree. The scalar maps and both constructibility directions work in all these cases, zero detection does not require trivial Frobenius, and the existing [a-1,b] bound remains valid (even when a sharper field bound is available). There is no new statement to falsify and no hidden lemma moved into a new node. All seven proof steps are below 2000 characters. All cross-unit statements used as generic tools are declared in split_report.tool_uses. No unit or chapter route is changed; this audit seed has no unit-key realization to fill.

## Unfinished work

None in the requested one-level stage-1 split. The reused unsplit nodes remain their own items; they are cited for their statements, not treated as proved Lean attachments.
