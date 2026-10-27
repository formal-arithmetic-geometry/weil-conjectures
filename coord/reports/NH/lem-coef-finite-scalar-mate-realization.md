## Worker report

Files written:

- `dag/nodes/sec-six-functors/lem-coef-finite-scalar-mate-realization.json`: item statement unchanged byte-for-byte as a JSON string; three-step assembly, 1710 characters.
- `dag/nodes/sec-six-functors/lem-coef-ramified-scalar-system-transpose.json`: statement, unsplit; Mathlib no match. Coherent finite-free scalar-system functor, compact-support comparison and exceptional transpose.
- `dag/nodes/sec-six-functors/lem-coef-ramified-scalar-exceptional-limit.json`: statement, unsplit; Mathlib no match. Cofinal endpoints, constructibility and actual functor realizations.
- `dag/nodes/sec-six-functors/lem-coef-ramified-scalar-counit-limit.json`: statement, unsplit; Mathlib no match. Transport of the scalar-extended counit word with the specified reconstruction comparisons.
- `citations.json`: one verbatim quotation per step/cited-node pair.

Attachments: none. The exact blueprint tag and the notions scalar mate, coherent coefficient systems and semilinear systems were searched in the live `lean/WeilConjectures/` source. The finite derived scalar lower-star file has ordinary direct-image comparison results, not the required normalized integral exceptional-system assertion. No compiler was run.

WANTED: none. The source is the available current blueprint and the retained agent-written split; this remains an agent-origin argument. No SGA route or new literature is introduced.

What was wrong: the return concerns work distribution, not a new mathematical objection. The eight-step 7465-character proof required several independently formalizable arguments. The sandbox at entry contained only dispatcher marker files, no node/report/search log; I copied the current repository node, which contains exactly those eight returned steps, and retained them below. No earlier local report or search results were discarded. I read the current rational-operations blueprint_update (paragraph 8) and its on-disk proof rather than the older master source. Nothing is changed in the statement, coefficient categories, compactification, comparison direction or route.

Unfinished work: the three new nodes deliberately have status unsplit, proof [], proof_deps [], proof_origin null. Other workers can now split these independent argument obligations. The report carries the old arguments as working material, not as hidden proof steps in their statements.

## Repair of the returned point

The single numbered requirement asks to spread every old argument across at least two comparable statement-only nodes, retain the item statement, and leave an assembly of at most 3000 characters. Three nodes were created. Their statements are 3686, 4086 and 3884 characters including their repeated self-contained hypotheses; their substantive workloads are the system construction, cofinal realization, and counit-word comparison. None restates the whole item. The first works for arbitrary normalized finite-Tor-level systems, without an integral input or limit assertion; the second has no mate assertion; the third compares the pre-transpose left-adjoint word, without asserting that the limit of the exceptional mate has that adjunct. The item's steps perform that final assembly using the existing normalized reconstruction adjunction calculus.

Coverage of every returned step:

1. Old step 1, fixed compactification, finite freeness, basis normalization and independence: lem-coef-ramified-scalar-system-transpose, compact-support comparison clause.
2. Old step 2, finite Tor and the actual enriched finite transpose: lem-coef-ramified-scalar-exceptional-limit, integral input/Tor clause, and lem-coef-ramified-scalar-system-transpose, transpose clause.
3. Old step 3, simultaneous section realization, tensor-associative quotient transitions, normalization, conservative evaluations and retained en levels: lem-coef-ramified-scalar-system-transpose, scalar-system and compact-support clauses. Its future proof uses the existing semilinear-section construction and finite-free invertibility, not an arbitrary lift.
4. Old step 4, actual system transpose, evaluation, quotient cocycle: lem-coef-ramified-scalar-system-transpose, system transpose identity and finite evaluation/quotient clauses.
5. Old step 5, cofinal en subsystem, uniform Tor for M and G_R M, compatible compact-support and exceptional projections: lem-coef-ramified-scalar-exceptional-limit, cofinal and endpoint clauses.
6. Old step 6, completed-scalar comparison, preservation of the bounded constructible domains, source/target and alpha identification: lem-coef-ramified-scalar-exceptional-limit, all five displayed functor identifications and their naturality/projection normalization.
7. Old step 7, system adjunct word, actual reconstruction units/counits and comparison with the integral counit word: lem-coef-ramified-scalar-counit-limit, displayed total-limit equality and intermediate counit normalization. The generic passage from a map to its adjunct uses the already-existing lem-pur-normalized-reconstruction-adjunction-calculus in item step 3.
8. Old step 8, naturality and identity/zero/first-level/empty cases: naturality is asserted in all three new nodes; the explicit edge cases and actual map equality are in lem-coef-ramified-scalar-counit-limit. The n=1 evaluation is included by n>=1 in lem-coef-ramified-scalar-system-transpose; no special fibre or unramified hypothesis was inserted.

## Searches

I searched the whole DAG (not just this unit) by statement/title and coefficient-system, cofinal, scalar/counit and scalar/mate vocabulary. I ran blueprint_refs.py ancestor and searches for finite free, transpose, cofinal, coefficient systems and scalar extension. The ancestor remains lem-coef-rational-operations and every new via list is [lem-coef-finite-scalar-mate-realization]. No imported blueprint statement asserts any of these precise entire-system constructions and their projection-normalized integral transport. The general finite-free, system adjunction, evaluation and reconstruction nodes are reused as interfaces, not recreated.

Each new node has its own plain-language LeanFinder query, LeanSearch query, Loogle query, Mathlib grep and second LeanFinder phrasing; every query was actually executed with msearch.py and is in searches.jsonl. LeanSearch returned a 60/minute rate-limit error for all three requests and is recorded unavailable. Both LeanFinder phrasings and Loogle/grep succeeded. I read the returned signatures: ordinary free condensed modules and their adjunctions, arithmetic ramification/completion, and categorical mate formulas do not construct normalized pro-etale coefficient systems or the specified completed counit transport. I opened Mathlib/CategoryTheory/Adjunction/Mates.lean at lines 84 and 123 (mateEquiv and mateEquiv_counit), and RingTheory/AdicCompletion/AsTensorProduct.lean at line 328 (ofTensorProductEquivOfFiniteNoetherian). The former assumes the actual functors and transformations whose construction is part of the new statements; the latter concerns ordinary modules and adic completion, not total derived limits of sheaf systems. Neither gives a leaf by a one-line specialization. The item's pre-existing searches were retained verbatim.

## Not duplicates

lem-coef-ramified-scalar-system-transpose vs lem-coef-finite-free-compact-composition: the existing node asserts the composition equation for f,g,gf and its coherent realization; the new node constructs scalar extension on normalized systems and its coherent exceptional transpose with quotient/unit/counit equations for every normalized input. It reuses the existing finite comparison as its definition rather than reproducing the composition lemma.
lem-coef-ramified-scalar-system-transpose vs lem-coef-cartesian-section-adjoint-mates: that node constructs one coefficient tower's compact-support/exceptional adjunction and same-ring quotient mates; the new node is the cross-field ramified scalar square between two such adjunctions, with actual scalar-system realization and quotient compatibility.
lem-coef-ramified-scalar-system-transpose vs lem-coef-semilinear-derived-sections: the generic section calculus does not assert the finite-Tor normalized cross-coefficient exceptional transpose or its finite-free compact-support invertibility.
lem-coef-ramified-scalar-system-transpose vs lem-coef-finite-free-extension: the existing finite-level formulas and coefficient squares do not construct this actual derived-system map.
lem-coef-ramified-scalar-exceptional-limit vs lem-pur-compact-support-integral-coefficient-comparison: the existing node gives the compact-support scalar comparison, not the source/target exceptional-system identifications, nor the simultaneous realization of both with G_R and G_S.
lem-coef-ramified-scalar-exceptional-limit vs lem-pur-compact-support-scalar-limit-reduction: the existing node treats the compact-support strict scalar mate and its Roos reduction, not the two exceptional-system endpoints and the system-adjunction composite identifications here.
lem-coef-ramified-scalar-exceptional-limit vs lem-weil-finite-free-completed-scalar-comparison: that node compares strict scalar extension and ordinary tensor for one complete input; it does not identify the coherent exceptional and compact-support composite functors or their projections.
lem-coef-ramified-scalar-exceptional-limit vs lem-pur-normalized-scalar-comparison-realization: that node compares scalar extension with completed pullback and tensor; no exceptional/compact-support system realization is asserted.
lem-coef-ramified-scalar-counit-limit vs lem-pur-normalized-reconstruction-adjunction-calculus: the existing same-coefficient general adjunction theorem gives the transpose of a descended arbitrary system map. The new node compares the concrete two-coefficient scalar-extended R-counit composite, including cofinality and the actual completed-scalar comparison, with the integral left-adjoint word. It does not restate that general transpose theorem.
lem-coef-ramified-scalar-counit-limit vs lem-coef-dual-formula-scalar-transpose: the latter compares a duality-defined integral exceptional map to the integral mate, not the total limit of the concrete scalar system counit word; no duality-defined comparison occurs in the new node.
lem-coef-ramified-scalar-counit-limit vs lem-sf-constructible-exceptional-adjunction-coefficients: the latter asserts counit-normalized coefficient comparisons, but does not give this equality of the particular pre-transpose system word under the specified total-limit realizations. It is not used to prove the new result (that would risk circularity through the coefficient package).

## Review by NH

I read the current chapter and unit records, the rational-operations blueprint_update paragraph 8, and the on-disk main-20261015 rational-operations proof. The route is still finite free compact support, coherent finite adjunction, then completed limit and preservation of the counit word. These are agent-extracted support statements for that paragraph. Each new statement begins with the full field, ramification, scheme, site and coefficient-system hypotheses rather than referring to an unnamed setting. The ramification relation is equality of ideals; the retained B_n levels are en, not n. No smoothness, properness of f, local site-perfectness or ambient exceptional adjoint is assumed. Properness is used only for the chosen p. The right adjoints are on the finite-Tor constructible normalized categories.

For new node lem-coef-ramified-scalar-system-transpose I checked the statements of finite-free-extension (finite free B_n, coefficient squares and evaluation/counit normalization), semilinear-derived-sections (actual scalar-extension, tensor, proper/open comparison and transpose constructions on ordinary derived systems), finite-free-compact-composition (the same basis-normalized finite comparison before limit), derived-system-evaluation-calculus (simultaneous evaluation/transpose and conservative isomorphism detection), cartesian-section-adjoint-mates and finite-adjunction-diagram-realization (actual system adjunction and enriched evaluations), and finite-exceptional (quotient cocycle and both adjunction identities). The new statement separates the canonical construction from its equations: isomorphism detection only proves alpha invertible; it is never used for equality of arbitrary maps. No uniform bound is imposed on arbitrary normalized input N. This is the genuine system construction obligation of old steps 1–4, not a bare repetition of the item.

For new node lem-coef-ramified-scalar-exceptional-limit I checked integral-residue-tor (uniform finite-reduction Tor from the residue interval), integral-exceptional-adjoint (G_R M constructible, coherent E_R R M realization and its finite projections), integral-finite-extension (exact scalar extension preserving the constructible categories), finite-free-completed-scalar-comparison (canonical chi on derived-complete inputs), and compact-support-integral-coefficient-comparison (finite coefficient maps on cofinal strict towers before limit with ordinary/strict normalization). These supply the specific hypotheses and normalization requested in old steps 5–6. The endpoint statements are in the derived category; none are merely per-degree isomorphisms. They also state the necessary constructibility before F_S and G_S are applied. Uniform Tor is required only on actual integral inputs, including G_R M, where residue-tor applies.

For new node lem-coef-ramified-scalar-counit-limit I reopened the normalized-reconstruction-adjunction-calculus statement. Its counit is explicitly u^-1 L(epsilon) L F(e), and its descended-transpose formula uses the actual reconstruction counit e. The new obligation is therefore to identify the limit of the scalar-extended R-system counit and the inverse scalar compact comparison, retaining the intermediate e comparison, with T_Y epsilon_R and alpha^-1. It asserts exactly that composite equality, not equality merely of finite reductions. The old step 7 argument is retained below in full; its future splitter must use the actual functor comparison from lem-coef-ramified-scalar-exceptional-limit and this reconstruction formula. Naturality and the degenerate cases from old step 8 are explicit rather than silently discarded.

For item step 1, the cited residue-Tor statement gives the required normalized input's finite-Tor levels and lem-coef-ramified-scalar-system-transpose states exactly the system comparison, its evaluated finite transpose, and its quotient identities. For item step 2, lem-coef-ramified-scalar-exceptional-limit gives precisely the source, target and alpha total-limit identifications with the stated constructible domains; lem-coef-ramified-scalar-system-transpose supplies the actual morphism to which the functor is applied. For item step 3, lem-coef-ramified-scalar-system-transpose supplies the exact system transpose equation, lem-coef-ramified-scalar-exceptional-limit its actual endpoint/composite identifications, lem-coef-ramified-scalar-counit-limit the equality of the resulting adjunct word with the integral scalar counit word, and normalized-reconstruction-adjunction-calculus states verbatim that the adjunct of a descended map is the total limit of its system adjunct. I checked its restricted-full-subcategory clause, since these functors are defined on constructible normalized systems. The final inference is the inverse of the adjunction Hom equivalence, not a faithfulness claim about projections. citations.json quotes these statements verbatim.

I tested E=L (e=1 and canonical scalar identity), f=id (identity adjunction and scalar comparison), M=0 (all words zero), the first level n=1, a genuinely ramified case e>1 (B_n=S/v^(en) with full S tower recovered cofinally), and empty schemes (zero category and dimension bound 0 in the exceptional-adjoint statement). None requires a hidden extra hypothesis. Uniformizers differing by a unit yield the same ideal quotient; the finite basis is fixed before reduction. All new proof arrays are empty; no assertion is supported by a proof sketch in its statement. I preserved the original item statement and all maintainer-owned fields. No unit/chapter route was changed, and no repository/launcher or Lean file was written.

The original proof's longest step was 1374 characters. The replacement steps are 520, 475 and 715 characters, all below 2000; the item total is 1710. The reduction in the parent is accompanied by three new substantive unsplit statements, with all original arguments preserved verbatim next. This addresses the return's explicit warning against shortening without spreading the work.

## Retained returned proof — complete working arguments

### Returned step 1

Choose the fixed compactification $f=pj$ from the definition of the finite compact-support functors. For $A_n=R/\pi^n$ and $B_n=S/\pi^nS=S/v^{en}$, the finite-free extension statement gives that $B_n$ is finite free over $A_n$, and its projection comparison is a natural isomorphism. Applying it to $p$, and using $Rf_{!,A_n}=Rp_{*,A_n}j_!$, gives a finite natural isomorphism
\[
\alpha_n:T_{Y,n}F_{A_n}\xrightarrow{\sim}F_{B_n}T_{X,n}.
\]
On a basis of $S$ this is the finite-sum distributivity map, and its definition as the canonical projection comparison makes it independent of the basis. The coherent system realization is specified in Step 3.

Cited nodes: def-weil-integral-rational-qbar-compact-support, lem-coef-finite-free-extension.

### Returned step 2

By [lem-coef-integral-residue-tor], the reductions of $M$ have a uniform finite Tor interval, so each $M_n$ belongs to $D^b_{ctf}(Y,A_n)$. For $M_n\in D^b_{ctf}(Y,A_n)$, use the finite enriched adjunction to define $b_{n,M_n}$ as the transpose of
\[
F_{B_n}T_{X,n}G_{A_n}M_n\xrightarrow{\alpha_{n,G_{A_n}M_n}^{-1}}T_{Y,n}F_{A_n}G_{A_n}M_n\xrightarrow{T_{Y,n}\varepsilon_{A_n,M_n}}T_{Y,n}M_n.
\]
The realization theorem supplies the actual enriched evaluation and transpose maps on simultaneous resolutions, so this is an actual morphism with the displayed source and target. Its evaluation is the stated finite mate, including its unit and counit identities.

Cited nodes: lem-coef-finite-adjunction-diagram-realization, lem-coef-integral-residue-tor.

### Returned step 3

Use the simultaneous enhanced section models of [lem-coef-semilinear-derived-sections], with their strict realizations in the derived semilinear-system categories. Derived coefficient extension gives the cofinal system functor
\[
\mathsf T_W^{(e)}(N)_n=N_n\otimes_{A_n}^{L}B_n.
\]
Its transitions are tensor reassociation followed by the transition of $N$; normalization follows from derived tensor associativity. That lemma explicitly supplies simultaneous section models for the direct-image coefficient projection comparison and its composite with open extension. Use this specified construction, applied to the fixed compactification, for $\alpha^{\mathrm{sys}}$; its evaluations are the canonical $\alpha_n$ of Step 1. These evaluations are isomorphisms by [lem-coef-finite-free-extension], so the system comparison is an isomorphism by evaluation conservativity. Coefficient compatibility is therefore realized before total limit, rather than inferred by lifting a commuting diagram of homotopy classes. Restriction to the retained $S$-levels $en$ retains this construction and its quotient transitions.

Cited nodes: lem-coef-finite-free-extension, lem-coef-finite-adjunction-diagram-realization, lem-coef-derived-system-evaluation-calculus, lem-coef-semilinear-derived-sections.

### Returned step 4

Transpose $\alpha^{\mathrm{sys}}$ in the tensor-Hom adjunction of the simultaneous system realizations. Explicitly, apply the system-level tensor-Hom evaluation to
\[
\mathsf F_S\mathsf T_X^{(e)}\mathsf E_RN\xrightarrow{(\alpha^{\mathrm{sys}})^{-1}}\mathsf T_Y^{(e)}\mathsf F_R\mathsf E_RN\xrightarrow{\mathsf T_Y^{(e)}\varepsilon_R}\mathsf T_Y^{(e)}N.
\]
The evaluation calculus says that tensor-Hom evaluations and transpositions are maps and identities of derived coefficient systems induced by simultaneous resolutions. Hence this transpose is a natural system morphism $b^{\mathrm{sys}}:\mathsf T_X^{(e)}\mathsf E_R\Rightarrow\mathsf E_S\mathsf T_Y^{(e)}$, rather than a map reconstructed from its evaluations. Evaluating its $n$-component gives exactly $b_{n,M_n}$ from Step 2, while the quotient maps commute by Step 3 and the quotient cocycle for the finite exceptional maps.

Cited nodes: lem-coef-derived-system-evaluation-calculus, lem-coef-finite-adjunction-diagram-realization, lem-coef-finite-exceptional.

### Returned step 5

The $S$-system in Steps 3--4 is indexed by $B_n=S/v^{en}$, a cofinal subsystem of the full $S/v^m$-tower. By [lem-coef-integral-residue-tor], every integral constructible input has the required uniform finite-reduction Tor interval; this also applies to $G_RM$, which is integral constructible by [prop-coef-integral-exceptional-adjoint]. The integral compact-support comparison [lem-pur-compact-support-integral-coefficient-comparison] applies to the fixed compactification and the derived-complete constructible finite-Tor input: it constructs the integral comparison from compatible finite tensor comparisons on the cofinal strict reduction towers, with those maps fixed before derived limits and with the ordinary tensor presentations identified by the completed-scalar comparison. Thus the total limit of the retained $B_n$-system is canonically the total limit over all $m$, with the specified projections. The exceptional system uses the same coherent finite reductions fixed by [prop-coef-integral-exceptional-adjoint], so its target is identified with the corresponding integral exceptional object under these projections.

Cited nodes: lem-pur-compact-support-integral-coefficient-comparison, prop-coef-integral-exceptional-adjoint, lem-coef-integral-residue-tor.

### Returned step 6

Take the total derived inverse limit of the actual system morphism $b^{\mathrm{sys}}$. The completed finite-free scalar comparison identifies the limit of $N_n\otimes_{A_n}^{L}B_n$ with the prescribed strict-tower scalar extension $N\widehat\otimes_R^{L}S$, naturally and by an isomorphism for derived-complete $N$. The scalar-extension comparison [lem-coef-integral-finite-extension] is exact and preserves the integral bounded constructible categories; since $G_RM$ and $M$ are in the corresponding $R$-categories, this puts $T_XG_RM$ and $T_YM$ in the $S$-categories before $F_S$ and $G_S$ are applied. Together with Step 5 and the coherent realization of integral exceptional pullback, this identifies the limit source with $T_XG_RM$ and the limit target with $G_ST_YM$. The limit of $\alpha^{\mathrm{sys}}$ is the specified $\alpha:T_YF_R\xrightarrow{\sim}F_ST_X$. Therefore the limit of $b^{\mathrm{sys}}$ is a well-defined natural integral map $b:T_XG_RM\to G_ST_YM$ constructed before any projection is considered.

Cited nodes: lem-weil-finite-free-completed-scalar-comparison, def-weil-integral-scalar-extension, lem-coef-finite-adjunction-diagram-realization, prop-coef-integral-exceptional-adjoint, lem-coef-integral-finite-extension.

### Returned step 7

Before taking the limit, the system-level transpose identity says that the adjunct of $b^{\mathrm{sys}}$ is exactly
\[
\mathsf F_S\mathsf T_X^{(e)}\mathsf E_RM\xrightarrow{(\alpha^{\mathrm{sys}})^{-1}}\mathsf T_Y^{(e)}\mathsf F_R\mathsf E_RM\xrightarrow{\mathsf T_Y^{(e)}\varepsilon_R}\mathsf T_Y^{(e)}M.
\]
The coherent integral realization in [prop-coef-integral-exceptional-adjoint] fixes the exceptional system, its units and counits, before applying total inverse limit. Apply the normalized reconstruction adjunction calculus [lem-pur-normalized-reconstruction-adjunction-calculus] to these normalized systems: it states that the descended integral adjunction is $\mathcal L\mathcal F\mathcal R\dashv\mathcal L\mathcal E\mathcal R$ and that the adjunct of a descended map is the total limit of its system adjunct. Thus the integral adjunction is the total limit of the system adjunction, and two integral maps are equal after comparing their adjuncts as system maps via the unit/counit identities. Applying the limit functor to the displayed identity and using the completed-scalar comparison transports it to the adjunct of $b$, namely
\[
F_ST_XG_RM\xrightarrow{\alpha_{G_RM}^{-1}}T_YF_RG_RM\xrightarrow{T_Y\varepsilon_{R,M}}T_YM.
\]
This proves the required mate equality as an equality of integral maps; it is not inferred from equality of their finite projections.

Cited nodes: prop-coef-integral-exceptional-adjoint, lem-pur-normalized-reconstruction-adjunction-calculus, lem-coef-finite-adjunction-diagram-realization, lem-coef-derived-system-evaluation-calculus, lem-weil-finite-free-completed-scalar-comparison.

### Returned step 8

All constructions in Steps 1--4 are natural in $M$ and in morphisms of coefficient systems: the finite-sum comparison, quotient transitions, tensor-Hom transpose and their unit/counit equations are natural chain maps on the simultaneous models. Total inverse limit, the cofinal compact-support comparison and the completed-scalar comparison are natural as well. Hence the limit map $b$ is natural, and the equality in Step 7 is an equality of the specified natural integral maps. The constructions remain valid for $E=L$, $f=\mathrm{id}$, $M=0$, $n=1$, and empty schemes (the corresponding systems and limits are zero or identity systems).

Cited nodes: lem-coef-finite-free-extension, lem-coef-finite-exceptional, lem-coef-derived-system-evaluation-calculus, prop-coef-integral-exceptional-adjoint, lem-pur-compact-support-integral-coefficient-comparison.

