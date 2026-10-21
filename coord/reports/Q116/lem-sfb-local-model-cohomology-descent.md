# Stage-1 repair: lem-sfb-local-model-cohomology-descent

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-local-model-cohomology-descent.json`: unchanged statement; five-step assembly, 1 new dependency.
- `dag/nodes/sec-six-functors-basics/lem-sfb-condensed-localization-exact-cohomology.json`: statement, unsplit, no Mathlib match.
- `citations.json`: a verbatim statement extract for every step/node citation.
- `report.md`: this repair review and the retained complete original argument.

One new unsplit node, zero Mathlib leaves. The item is a child, not a unit key theorem; no unit record is changed.

## Attachments

None. The item tag and local-model/cohomology concepts were searched under `lean/WeilConjectures/`. The exact recorded declaration was read in `lean/Sheaf/AlgebraicGeometry/LocalModelCohomologyDescent.lean`: its whole proof is still `sorry`, so it is not an attachment. The upstream ModuleObject/UpperLowerStar/Defs.lean supplies exact condensed pullback but does not state the localization identification with its derived cohomology normalization. No Lean was written or compiled.

## WANTED

None. All Stacks source passages used here are present locally.

## Return repaired

The return asks to spread the 5563-character argument, not merely abbreviate it. I compared the current repository node, the existing Q118 stage-1 report and Q20 Lean record with the sandbox. The sandbox contained only dispatcher briefs: no node, report, or searches.jsonl survived, so the current repository version is the repair baseline. Its statement, provenance and historical searches are retained. Old Steps 1 and 2 (2218 characters) become the separate, self-contained task `lem-sfb-condensed-localization-exact-cohomology`; this is delivered statement-only with status unsplit, empty proof and proof_deps, and new logged searches. This child has neither scalar local models, covering families, common bounds nor constructibility in its conclusion, so it does not restate the parent or one of its main clauses. It can be proved independently for any site object, before the scalar and descent assembly is implemented.

The remaining old arguments stay explicit in parent Steps 2-5: scalar-extension cohomology and the original local-model isomorphisms; the zero-middle-term computation; sheaf uniqueness on a base-changed cover, including an empty cover; and finite scalar presentations, the identity stratum, affine-local restriction without quasi-separatedness, and membership in Dbc. The complete previous proof below records every argument, including the extracted comparison, for workers to reuse. The parent assembly is 2382 characters. No source intent, item statement, target or Lean signature was changed.

## Sources and new-node searches

I read the main-20261015 chapter and sk-prop-scalar-six unit and det-prop-scalar-six-ctf.proof.md paragraph (2). That paragraph motivates the scalar cohomology formula, but does not prove the complete local/global argument. This remains an agent assembly. For the new node I read sites.tex Tag 03CE, lemma-localize-given-products (base-change morphism equals localization), its preceding localization section and Tag 00Y0, definition-localize; sites-modules.tex Tag 04IX, definition-localize-ringed-site (sectionwise ring and module restriction); derived.tex Tag 015F, lemma-right-derived-exact-functor; and homology.tex Tag 010N, lemma-exact-functor. The source field explicitly calls the condensed and derived enhancements an agent specialization, not the statement of 03CE. I also read more-morphisms.tex Tags 094T and 0951, lemma-composition-weakly-etale and lemma-weakly-etale-permanence. The old source label 092A is a More on Algebra section, not the scheme stability lemma; its actual scheme argument is provided by these two tags and the existing localization/coefficient-sections nodes. The parent statement and old source metadata were not silently rewritten.

Whole-DAG statement searches covered exact sectionwise condensed pullback, localized cohomology, and restriction/cohomology. Whole-blueprint searches were `local model cohomology`, `restriction cohomology`, `localized`, `010N`, `03DH`, and `finite constant local model`. I read candidate statements, in particular the ordinary constant-ring inverse-image restriction node, condensed coefficient-sections localization, internal-module-operations transport, exact localized module restriction, and exact-functor cohomology/factorization. They supply ingredients, rather than the complete canonical condensed localization/cohomology assertion. The ancestor command gives det-prop-scalar-six-ctf, and the new via list is [lem-sfb-local-model-cohomology-descent].

Only msearch.py was used for the new Mathlib searches. Both semantic phrasings were read: the first returns structure-sheaf adjunction/pullback facts and light condensed module facts; the second returns general localization and homological-complex factorization. Loogle returns SheafOfModules.overFunctor and overFunctorMap and Scheme.Modules.overFunctorEquiv. The source at Mathlib/Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean:59-84 defines abstract slice restriction and successive restriction; it does not identify the geometric condensed coefficient pullback. The second grep also returns generic homology comparison APIs, already represented by the existing exact-functor nodes. These are not an exact or one-line match for the new ringed-pro-étale comparison, so it remains unsplit. All six searches in the new node are copied from the actual searches.jsonl records, with the exact query text.

## Not duplicates

- lem-sfb-condensed-localization-exact-cohomology vs lem-pe-comparison-etale-slice-abelian-pullback: the existing statement compares étale and pro-étale abelian pullbacks for an étale object; the new statement treats arbitrary pro-étale objects, condensed ring actions, exact module restriction and unbounded derived cohomology.
- lem-sfb-condensed-localization-exact-cohomology vs lem-trf-slice-subtopos-site-presentation: the existing statement constructs the set-valued slice geometric morphism and graph counit; it does not identify the specified condensed module pullback or give derived cohomology.
- lem-sfb-condensed-localization-exact-cohomology vs lem-sfb-proetale-object-inverse-image-restriction: the existing module clause is for a constant ordinary ring A_X and has no derived cohomology comparison; the new statement concerns the canonical possibly nonconstant condensed coefficient ring Gamma_S and the induced exact derived restriction.
- lem-sfb-condensed-localization-exact-cohomology vs lem-exc-finite-coefficient-open-restriction: the existing statement concerns an open immersion and finite possibly noncommutative coefficients and the Kan adjunction unit; the new statement allows every small pro-étale object and arbitrary commutative condensed coefficients and identifies unbounded derived cohomology.
- lem-sfb-condensed-localization-exact-cohomology vs lem-sfb-coefficient-sections-localization: the existing assertion supplies the geometric site identification and the coefficient section/multiplication comparison, but no equivalence on arbitrary module actions, exactness, or termwise/derived-cohomology comparison. It is an input to the extracted argument.
- lem-sfb-condensed-localization-exact-cohomology vs lem-pur-site-restriction-module-adjunction-exact: the existing assertion is exact slice restriction for a ring sheaf; the new task identifies the particular geometric condensed pullback with that functor before deriving it.
- lem-sfb-condensed-localization-exact-cohomology vs lem-weil-pbc-exact-functor-complex-cohomology: the existing assertion starts with an already exact functor on complexes; it does not construct the geometric condensed restriction comparison.

## Review by Q116

I read delivery-errors B through E against the JSON and source passages, including the old independent maintainer note which corrected the coefficient-identification gap in the original Step 1. The extracted task retains that correction: alpha_u is the actual canonical coefficient morphism, not an unspecified abstract isomorphism, and compatibility with sections and multiplication is part of its statement. Its two conclusions are a single localization argument and its induced cohomology comparison. It introduces S, V, u, Gamma, module categories, the precise module pullback and the induced derived functor itself, with definition dependencies; no bare phrase such as “in the setting of the item” remains. It has no proof sketch in its statement and no proof steps. The full argument for it is retained below rather than pretending it is finished. Its source agrees with localization for all site objects, not just open immersions. The derived extension uses all unbounded complexes, as Tag 015F explicitly permits. The cited generic exact-functor nodes were already available, so no duplicate generic category-theory node was created.

For parent Step 1 I checked both clauses of the new statement: clause (1) gives exact sectionwise module restriction with the coefficient action; clause (2) gives exactly the displayed restriction/cohomology isomorphism. The hypotheses hold since every V_i is an object of the given pro-étale covering, and Gamma is a commutative condensed ring. Step 2 cites the actual constant-sheaf tensor construction in det-def-sfb-constructible-local-model, the full natural cohomology isomorphism in lem-weil-pbc-exact-functor-complex-cohomology, and the derived-cohomology factorization/functoriality in def-weil-abstract-derived-category. Exactness is the item's explicit hypothesis on E_i, with no assertion that all arbitrary condensed coefficients are flat. The given model isomorphism has precisely this termwise E_i target, so applying cohomology and composing Step 1 gives every original local identification.

Step 3 uses the cited kernel/image formula: a zero middle term gives zero cohomology, and the exact additive functor preserves zero. Step 4 uses exactly the base-change covering and equalizer clauses in def-weil-pbc-sites-and-cohomology and the sectionwise rule in def-pur-localized-ringed-site. It compares each test section with zero; it does not confuse zero global sections with a zero sheaf. These are elementary steps, including the explicitly retained empty-cover argument.

In Step 5 I checked the finite scalar-module witnesses against both forms of det-def-sfb-constructible-local-model. The single identity immersion is a stratification under def-constructible-stratification. S and the empty set are retrocompact opens by the actual definition in def-weil-constructible-subset. Exactness in lem-pur-site-restriction-module-adjunction-exact preserves cokernels and finite sums, and lem-sfb-coefficient-sections-localization specifically says how multiplication endomorphisms restrict. Thus the same finite scalar matrices work on each base-changed cover of an affine open; no quasi-separatedness is inserted. Clauses (1) and (2) of det-def-sfb-constructible-tor-amplitude give exactly constructibility and Dbc from the finite interval. This last part remains an elementary assembly of the cited finite presentations and definitions, rather than a new duplicate pullback theorem. Every citation has a verbatim quote in citations.json. No parent proof step exceeds 2000 characters.

Small cases: u the identity; u an open immersion; u a non-monomorphic weakly étale covering object (the slice identification uses composition/cancellation, not injectivity); V or S empty; Gamma the zero ring; r=s; zero and exact scalar complexes; an unbounded representative of Q; and quasi-compact non-quasi-separated S. None requires extra scalar flatness or perfectness. The extracted result also makes sense for non-quasi-compact S. No new statement is disputed. The item statement and statement dependencies were compared byte-for-byte with the live baseline; Lean records and maintainer review fields are retained. No files in the shared repository or launcher were written, no git commands were run there, no agents were started, and no compiler/Lake/build tool was used.

## Complete retained argument and relocation map

The following is the previous live proof verbatim. Old Steps 1-2 are the argument assigned to the new unsplit localization/cohomology task; old Step 3 is parent Step 2, old Step 4 is parent Step 3, old Step 5 is parent Step 4, and old Step 6 is parent Step 5. This preserves the earlier worker's source work for the independent tasks without placing a proof inside the new node.

### Original step 1

For $u_i:V_i\to S$, identify $S_{\mathrm{proét}}/V_i$ with $(V_i)_{\mathrm{proét}}$. Indeed an object $W\to V_i$ weakly étale over $V_i$ is weakly étale over $S$ by composition; conversely a map to $V_i$ from a weakly étale $S$-scheme is weakly étale by [sk-lem-pe-weakly-etale-stability]. The arrows agree, and the covering families agree since both sites use the same fpqc covering condition [sk-def-pe-site]. By [def-pur-localized-ringed-site], localized inverse image of sheaves is sectionwise restriction. Under the identification just made, the abelian inverse image $u_{i,\mathrm{Ab}}^*$ along $u_i$ is this localized restriction, and the canonical isomorphism $\alpha_{u_i}:u_{i,\mathrm{Ab}}^*\Gamma_S\xrightarrow{\sim}\Gamma_{V_i}$ of [sk-def-sfb-coefficient-morphisms] gives ring isomorphisms $\theta_W:\Gamma_S(W)\cong\Gamma(W,\Gamma_W)$ compatible with restriction along every map $W'\to W$ over $V_i$, and carrying multiplication by a section to multiplication by its image [lem-sfb-coefficient-sections-localization]. Hence $\alpha_{u_i}$ identifies the restricted coefficient ring $\Gamma_S|_{V_i}$ with $\Gamma_{V_i}$. Renaming a module action along this ring isomorphism and along its inverse gives inverse equivalences of module categories. Thus the notation $Q|_{V_i}$ uses the exact localized restriction, with the coefficient ring renamed; at a test object $W\to V_i$, restriction of a module sheaf $F$ has sections $F(W)$.

Cited nodes: sk-lem-pe-weakly-etale-stability, sk-def-pe-site, def-pur-localized-ringed-site, sk-def-sfb-coefficient-morphisms, lem-sfb-coefficient-sections-localization

Source: literature/stacks-project/proetale.tex; Definition big-small-proetale; Stacks Tag 092A (weakly étale stability); sites-modules.tex, Tag 03DH, definition-localize-ringed-site; blueprint coefficient morphisms, final sentence

### Original step 2

Restriction on module sheaves is exact by [lem-pur-site-restriction-module-adjunction-exact]; the coefficient-ring renaming in Step 1 is an equivalence and hence preserves kernels and cokernels by their universal properties. Choose a complex $K^\bullet$ representing $Q$ in the localization [def-weil-abstract-derived-category]. Apply [lem-weil-pbc-exact-functor-derived-factorization] to restriction: its termwise image represents $Q|_{V_i}$. Applying [lem-weil-pbc-exact-functor-complex-cohomology] to that same exact functor gives
$$H^q(Q)|_{V_i}\cong H^q(Q|_{V_i}).$$
The two cohomology objects here are those of the representing complexes, since the cohomology functor on the derived category factors the complex cohomology functor [def-weil-abstract-derived-category].

Cited nodes: lem-pur-site-restriction-module-adjunction-exact, def-weil-abstract-derived-category, lem-weil-pbc-exact-functor-derived-factorization, lem-weil-pbc-exact-functor-complex-cohomology

Source: literature/stacks-project/derived.tex; Tag 015F, lemma-right-derived-exact-functor, combined with homology.tex Tag 010N, lemma-exact-functor, and localized-module exactness (sites-modules.tex Tag 03DH)

### Original step 3

Put $E_i(M)=\Gamma_{V_i}\otimes_{R_{V_i}}M_{V_i}$, where $R_{V_i}$ and $M_{V_i}$ are the constant sheaves specified in [det-def-sfb-constructible-local-model]. This is the functor assumed exact in the item. Apply [lem-weil-pbc-exact-functor-complex-cohomology] to $E_i:R\text{-}\operatorname{Mod}\to\operatorname{Mod}(\Gamma_{V_i})$ and the scalar complex $Q_i^\bullet$. It yields $H^q(E_i(Q_i^\bullet))\cong E_i(H^q(Q_i^\bullet))$. The given derived isomorphism $Q|_{V_i}\simeq E_i(Q_i^\bullet)$ induces an isomorphism on cohomology by functoriality [def-weil-abstract-derived-category]. Combining with Step 2 proves, for every $i,q$,
$$H^q(Q)|_{V_i}\cong\Gamma_{V_i}\otimes_R H^q(Q_i^\bullet).$$
Exactness is used only for the scalar extension functor in the hypothesis; no flatness of an arbitrary condensed coefficient ring is asserted.

Cited nodes: det-def-sfb-constructible-local-model, lem-weil-pbc-exact-functor-complex-cohomology, def-weil-abstract-derived-category

Source: literature/stacks-project/homology.tex; Tag 010N, lemma-exact-functor, applied to the scalar complex; the derived-category functoriality is the definition in the project node def-weil-abstract-derived-category.

### Original step 4

If $q\notin[r,s]$, the scalar middle term $Q_i^q$ is zero, so $H^q(Q_i^\bullet)=\ker d_i^q/\operatorname{im}d_i^{q-1}=0$ by the definition of complex cohomology [def-weil-abstract-derived-category]. An exact additive functor sends the zero object to zero. Hence Step 3 gives $H^q(Q)|_{V_i}=0$ for all $i$.

Cited nodes: def-weil-abstract-derived-category

Source: literature/stacks-project/homology.tex; Tag 010N, lemma-exact-functor, together with the elementary kernel/image formula for complex cohomology (project node def-weil-abstract-derived-category).

### Original step 5

Fix $q\notin[r,s]$ and write $F=H^q(Q)$. For every object $W\to S$ of the site, base change of the given covering is a covering $\{W\times_S V_i\to W\}_i$, by the covering axiom of [def-weil-pbc-sites-and-cohomology]. Step 4 and the sectionwise description [def-pur-localized-ringed-site] give $F(W\times_S V_i)=0$. For any section $x\in F(W)$, its restrictions and those of the zero section are therefore equal on this covering. The equalizer (in particular uniqueness) clause of the sheaf axiom in [def-weil-pbc-sites-and-cohomology] implies $x=0$. Thus every section module of $F$ is zero, so $F=0$. This also treats an empty covering: the sheaf axiom then makes $F(W)$ a singleton.

Cited nodes: def-weil-pbc-sites-and-cohomology, def-pur-localized-ringed-site

Source: literature/stacks-project/sites.tex; Tags 00VH and 00VM, definition-site (base change axiom) and definition-sheaf-sets (equalizer and uniqueness)

### Original step 6

For any $q$, the given modules $H^q(Q_i^\bullet)$ are finitely presented over $R$. The isomorphisms of Step 3 and the given pro-étale covering therefore satisfy exactly the definition of a finite constant local model [det-def-sfb-constructible-local-model]. The single immersion $\operatorname{id}_S:S\to S$ gives a finite stratification [def-constructible-stratification]: its sole image is all of $S$, which is locally closed and constructible. Explicitly, $S$ and $\varnothing$ are open and retrocompact, so $S=S\cap(S\setminus\varnothing)$ is constructible by [def-weil-constructible-subset]. Thus $H^q(Q)$ is constructible on that stratum by clause (1) of [det-def-sfb-constructible-tor-amplitude]. For the affine-local convention on a non-qcqs scheme, use the equivalent scalar-matrix cokernel presentations in [det-def-sfb-constructible-local-model]. Restrict them to the base-changed cover of an affine open: exact restriction [lem-pur-site-restriction-module-adjunction-exact] preserves these cokernels and finite direct sums, and the entries remain the same scalar entries under the canonical coefficient restrictions of Step 1, since multiplication by a section restricts to multiplication by its restriction [lem-sfb-coefficient-sections-localization]. The same finite scalar presentations then give finite constant local models on the affine open. Step 5 confines cohomology to the finite integer interval $[r,s]$. Clause (2) of [det-def-sfb-constructible-tor-amplitude] now gives $Q\in\Dbc(S,\Gamma)$.

Cited nodes: det-def-sfb-constructible-local-model, def-constructible-stratification, def-weil-constructible-subset, det-def-sfb-constructible-tor-amplitude, lem-pur-site-restriction-module-adjunction-exact, lem-sfb-coefficient-sections-localization

Source: literature/stacks-project/sites-modules.tex; Tag 03DH, restriction of module sheaves, combined with the finite-presentation and constructibility definitions recorded by the cited project nodes; the one-stratum and affine-local assembly is written out by the agent.

## Unfinished work

The new localization/cohomology task is intentionally unsplit for a later worker. The parent split is complete. The required remote dry run passed; the statement-only child remains intentional future work, not an unfinished parent split.

## Validation

The required `deliver.py Q116 lem-sfb-local-model-cohomology-descent --no-push` exited 0 and printed `OK (not pushed)` at a93b2130e54, with server preflight passed. It ran the remote DAG and split review checks; no local check_dag.py, review_split.py or preflight_delivery.py was run. The final report is included in the final dry run and direct push.
