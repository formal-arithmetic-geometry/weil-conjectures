# Worker report — Q139 repair

## Files written

- dag/nodes/sec-six-functors/lem-sf-package-base-change-domain-realization.json: statement unchanged; split with seven short assembly steps (2121 characters).
- dag/nodes/sec-six-functors/lem-sf-bc-geometry-hypotheses.json: statement, unsplit; no Mathlib match for the complete assertion; carries former steps 1, 2.
- dag/nodes/sec-six-functors/lem-sf-bc-adic-ring-domain.json: statement, unsplit; no Mathlib match for the complete assertion; carries former steps 3.
- dag/nodes/sec-six-functors/lem-sf-bc-finite-mate-domain.json: statement, unsplit; no Mathlib match for the complete assertion; carries former steps 4, 5.
- dag/nodes/sec-six-functors/lem-sf-bc-completed-mate-domain.json: statement, unsplit; no Mathlib match for the complete assertion; carries former steps 6, 7.
- dag/nodes/sec-six-functors/lem-sf-bc-field-mate-domain.json: statement, unsplit; no Mathlib match for the complete assertion; carries former steps 8, 9.
- dag/nodes/sec-six-functors/lem-sf-bc-compact-support-domain.json: statement, unsplit; no Mathlib match for the complete assertion; carries former steps 10, 11.
- citations.json: verbatim statements for all seven step citations.

## Attachments

None. Searches for the blueprint tag and package/domain/exchange notions in lean/WeilConjectures found no completed project declaration stating this item or the new combined assertions. Existing completed-exchange construction files define transformations; they do not prove the full domain realizations.

## WANTED

None.

## What was wrong and repair of the return

The returned proof was 13133 characters in twelve steps. The human required at least four independent new statement-only nodes and an assembly of at most 3000 characters. Six new nodes now separate the geometric, coefficient-ring, finite-mate, completed-mate, field-mate and compact-support arguments. Each has proof=[], proof_deps=[], proof_origin=null and status=unsplit, so other workers can take them independently. No large replacement node states the full item. Old step 12 uses the existing fix-lem-exchanges and remains a direct application, not a seventh duplicate node.
The sandbox initially contained only dispatcher brief files: there was no delivered node, report, citations or searches.jsonl to resume. The initial required dry run exited with FAILED: no node files under the sandbox dag/nodes. I recovered the reviewed version from the current read-only repository. Its full twelve-step argument and source/citation lists are preserved below. This recovery retains the reviewer corrections: nonarchimedean verification, smooth arrow role matching, and identification of the completed mate by lem-sbc-completed-operations-linear-natural-exchange. No git command was run in the shared repository, and no Lean was written or compiled.
The statement is byte-for-byte unchanged from the recovered current item. There is no statement dispute.

## Sources and searches

I read GOAL.md, the stage-1 brief, stage-1 contract, worker role, SETUP levels and requirements, delivery-errors B--E, the package chapter and unit, and the current prop-functor-package.proof.md, clause (4). That proof names proper bounded-below, qbar, smooth bounded-below and compact-support finite/qbar base change. The six new sources are explicitly the separate realization arguments for that sentence. The mathematical source is the same package sentence and its existing theorem statements; the detailed arguments are agent-written assembly, not claimed to be an external theorem with the same package-specific wording. The retained geometric sources name Stacks 01T6 (lemma-finite-type-noetherian), 01OY (lemma-locally-Noetherian-quasi-separated) and 0A3V (lemma-morphism-finite-type-bounded-dimension); proper exchange uses 0DDE (lemma-proper-base-change) and 09C9 (theorem-proper-base-change). No prohibited source route is introduced.
For each new node msearch.py ran LeanFinder, Loogle, grep and a second natural-language phrasing with LeanSearch. The first three LeanSearch requests were unavailable due to HTTP rate limits, so those three second phrasings were also run successfully with LeanFinder. Each exact query and raw summary is in searches.jsonl and in the corresponding mathlib_searches; full hit outputs remain in search-*.txt. A field Loogle query had an unknown identifier; its corrected CategoryTheory.Functor.IsLocalization query ran successfully and is recorded separately.
I inspected all hit names and signatures. Geometry hits concern finite fibres, properness predicates and valuative criteria, not the combined finite-dimensional geometric-fibre bound plus compactifications. Ring hits include the local-field DVR instance (Mathlib/NumberTheory/LocalField/Basic.lean:108) and Valued.integer.finite_quotient_maximalIdeal_pow_of_finite_residueField (Mathlib/Topology/Algebra/Valued/LocallyCompact.lean:111); I read these candidates. They supply individual ingredients but do not state the finite-perfect quotient adic datum with the displayed finite-free resolution, annihilator and completed category conventions. The finite/completed exchange hits are geometric stability under base change, adjunction mates and derived-adjunction formulas, which do not assert cohomological base-change invertibility or its etale-origin/completion domains. Field hits concern module localization and Weierstrass base change, not these raw-localized completed exchanges. Compact-support hits concern supports of functions and linear-map base change, not compactified sheaf direct images. None is an exact match or a one-line specialization of the whole new statement.
Whole-DAG key-word searches, Stacks-tag searches and blueprint_refs search were run for base change, geometric hypotheses, fibre dimension, finite perfect quotients, adic coefficient, ordinary exchange, smooth base change, completed exchange, rational exchange and compact-support exchange. The existing nodes below supply ingredients and will be reused when the new nodes are split; they do not already contain these combined audited domain realizations.

## Not duplicates

lem-sf-bc-geometry-hypotheses vs lem-weil-pbc-finite-type-over-noetherian: only proves Noetherian permanence; the new statement additionally gives arrow qcqs, all corners, fibre bounds, invertible prime and compactifications.
lem-sf-bc-geometry-hypotheses vs lem-fin-finite-type-fibre-dimension-bound: only bounds scheme fibres; the new statement upgrades to geometric fibres and verifies all other package geometry.
lem-sf-bc-geometry-hypotheses vs thm-nagata-compactification: provides compactifiability but not the corner, arrow and fibre-dimension verifications.
lem-sf-bc-adic-ring-domain vs lem-weil-l-adic-extension-integers-dvr: does not assert all finite perfect quotient adic hypotheses or the completed coefficient/domain and indexing compatibility.
lem-sf-bc-adic-ring-domain vs lem-weil-valued-dvr-finite-quotients: assumes a valued DVR and only proves finite quotients/transitions; the new statement verifies the actual l-adic rings and perfect/torsion domain data.
lem-sf-bc-finite-mate-domain vs thm-weil-pbc-finite-level-proetale: proper witnessed exchange only; the new assertion includes etale module normalization, smooth exchange, exact comparison identity and role matching.
lem-sf-bc-finite-mate-domain vs sbc-thm-finite-proetale-smooth-base-change: smooth pro-etale assertion only; the new assertion also covers proper bounded-below input and etale forget-coefficients/transport identity.
lem-sf-bc-completed-mate-domain vs cor-weil-pbc-constructible-complete: only proper completed constructible exchange; the new assertion identifies the actual mate and separates the smooth ambient and four-family landing conclusions.
lem-sf-bc-completed-mate-domain vs sbc-thm-adic-smooth-base-change: only smooth exchange in its own labels; the new assertion includes proper exchange and its mate/derived-limit identification on the actual package domain.
lem-sf-bc-completed-mate-domain vs lem-sbc-completed-operations-linear-natural-exchange: identifies maps but asserts no invertibility; the new statement also verifies proper/smooth isomorphism domains and constructible landing.
lem-sf-bc-field-mate-domain vs lem-sf-field-stage-ordinary-realization: constructs realization functors into discrete constant coefficient derived categories; the new node concerns proper/smooth exchange in raw completed rational and common-stage categories.
lem-sf-bc-field-mate-domain vs thm-weil-pbc-qbar: only proper common-stage exchange; the new node also specifies rational and smooth lattice domains and the ambient/constructible distinction.
lem-sf-bc-field-mate-domain vs sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch: only smooth common-stage ambient exchange; the new node includes proper and rational domains and conditional constructible restriction.
lem-sf-bc-compact-support-domain vs thm-cbc-qbar: only common-stage compact support; the new statement includes the finite compactification-factor calculation and its finite witnessed/completed/rational identifications.
lem-sf-bc-compact-support-domain vs lem-sf-package-compactified-tower-comparisons: asserts compactification/coefficient/composition comparisons and proper coincidence; it does not give arbitrary-base-change compact-support invertibility throughout the specified stages.

## Review by Q139

I checked the repair against B--E with the six node statements and the package source open. Each statement introduces its fields, ring, schemes, maps and coefficient data. New nodes have no proof hidden in their statements: the resolution, map equality, role matching and endpoint identifications are conclusions to be proved by the future worker. Their intended arguments remain fully available below. I followed the unit route through proper and smooth base change, completion and field transport, and compactifications. I did not use the older eight-clause numbering as if it were the current proposition: current clause (4) is the base-change sentence.
Step 1 cites only lem-sf-bc-geometry-hypotheses, whose statement explicitly gives every corner and arrow property, the geometric bound, proper base change and quasi-compact open compactifications. The finite-type and separated hypotheses hold for every arrow in our square. Step 2 cites lem-sf-bc-adic-ring-domain, whose statement gives finite perfect quotients killed by ell^n, completed sheaves and the positive-index shift. The ring is a domain, so multiplication by a uniformizer power is injective, including n=1 and ramified E (ell=u varpi^r with r>=1).
Step 3 cites lem-sf-bc-finite-mate-domain: it says both the etale constant-module mate conclusion and the exact S_L,T_L conjugacy identity, not just that unrelated objects are isomorphic. I verified the smooth arrow is our g and the qcqs map our f, with output Y′. A bounded-below proper witness need not be bounded above; the smooth pro-etale witness is explicitly bounded constructible. Finite-Tor is only a restriction of that domain, not an unproved endpoint preservation claim.
Step 4 cites lem-sf-bc-completed-mate-domain. Its statement expressly identifies the completed adjunction mate with the derived-limit exchange, which is why the proper completed theorem applies to the actual map. It separately includes ambient smooth invertibility and the four-family constructible landing condition with one interval independent of n. The input and output finite-dimension hypotheses refer to X and Y′; Step 1 verifies both. The proper constructible corollary requires f and f′ proper, N=ell invertible killing R/I, and the nonnegative fibre bound: these are furnished by Steps 1--2.
Step 5 cites lem-sf-bc-field-mate-domain, whose statement covers the raw rational component, the proper common-stage component, smooth finite-level admissible lattice data, identity-idempotent inclusion and further scalar extensions. It asserts no unconditional smooth constructible landing, no reduction of rational objects, and no arbitrary unspecified lattice. I checked that further-stage representatives preserve the hypotheses, exactly as the original item requires.
Step 6 cites lem-sf-bc-compact-support-domain. The statement specifies proper exchange at j_!K followed by the open comparison and preserves the theorem-map identification at all stages, witness independence and uniform landing conditions. A finite bounded input has a bounded-below j_!K because j_! is exact; no smoothness of g occurs in either factor. Step 7 cites fix-lem-exchanges, which explicitly gives naturality/theorem-map agreement in clause (1), identity and both pastings in clause (2), smooth map identification in clause (3), and refinement/composition in clause (4). I checked these against its full statement and retained its condition that all intermediate operations lie in their domains. The entire cited statement is copied verbatim in citations.json, as are the six new cited statements.
Small cases checked: empty source and empty fibres (dimension -infinity and any e>=0); identity and proper identity maps; n=1 and ramified coefficient extensions; zero complexes; a proper f with nonsmooth g; smooth g with an unbounded-below reduction interval is excluded from the stronger landing conclusion; a finite overfield change does not identify raw localization with discrete constant rational etale sheaves. The six statements preserve the original domains and conclusions in these cases. No new statement claims all ordinary exchange maps are invertible for arbitrary g.
The long-step check now finds no parent proof step over 2000 characters (the whole assembly is 2121). The two statements over 2000 characters are statement-only work items, not inline proofs. Old steps 1--11 are partitioned into six separate arguments of comparable scope; no argument is silently discarded. Old step 12 remains the existing theorem application. Every new node is strictly smaller than the parent, and none depends on the parent; their blueprint via field is provenance only.

## Preserved arguments for the new work items

These are the recovered arguments verbatim, including their former numbering, cited-node lists and source places. References to old Steps refer to this preserved twelve-step sequence. They are report material only; no proof or proof dependency is installed in a new unsplit node.

### lem-sf-bc-geometry-hypotheses

Former step 1:

For each corner $T$, the structure map to $\operatorname{Spec}k$ is finite type. A field is Noetherian (its only ideals are $0$ and $k$), so [lem-weil-pbc-finite-type-over-noetherian] makes $T$ Noetherian, in particular quasi-compact. By [lem-weil-pbc-locally-noetherian-quasi-separated] it is quasi-separated, and [lem-kun-dimension-finite-type] gives finite dimension. Apply (1) of [lem-weil-pbc-qcqs-morphism-permanence] to each arrow: its source is quasi-compact and quasi-separated and its target is quasi-separated, so the arrow is qcqs. Finally $\ell$ is invertible on every corner: the nonzero element $\ell\in k$ has an inverse and the structure ring maps preserve this inverse. Thus the qcqs, Noetherian, finite-dimensional and invertible-prime hypotheses required below hold at the actual input and output corners, including $Y'$ as the output of exchange.

Cited nodes: lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-locally-noetherian-quasi-separated, lem-kun-dimension-finite-type, lem-weil-pbc-qcqs-morphism-permanence.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Clause (4): geometric hypotheses; Stacks 01T6 (lemma-finite-type-noetherian) and 01OY (lemma-locally-Noetherian-quasi-separated).
Former step 2:

Since $Y$ is quasi-compact and $f$ finite type, [lem-fin-finite-type-fibre-dimension-bound] supplies $e\geq0$ with $\dim X_y\leq e$ for all $y$. Each $X_y$ is finite type over $\kappa(y)$; the field-extension assertion of [lem-kun-dimension-extension] gives $\dim X_{\bar y}=\dim X_y\leq e$. Empty fibres have dimension $-\infty$, so the same nonnegative $e$ includes them. If $f$ is proper, [lem-weil-pbc-proper-base-change] makes $f'$ proper. Apply [thm-nagata-compactification] to $f$ over the qcqs target $Y$ to obtain a compactification. By [def-nagata-compactification] its open factor is quasi-compact. These verifications also apply to any other separated finite-type map to a corner for which a compactification is needed in a composition diagram.

Cited nodes: lem-fin-finite-type-fibre-dimension-bound, lem-kun-dimension-extension, lem-weil-pbc-proper-base-change, thm-nagata-compactification, def-nagata-compactification.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Clause (4): fibre bound and compactifications; Stacks 0A3V (lemma-morphism-finite-type-bounded-dimension).

### lem-sf-bc-adic-ring-domain

Former step 3:

Verify the coefficient input rather than identifying different ambient categories. By [lem-weil-l-adic-extension-integers-dvr], $R$ is a domain DVR with finite residue field and maximal ideal $(\varpi)$. Its absolute value is nonarchimedean, as the next lemma requires: if $|x|\le|y|$ with $y\ne0$, then $x/y\in R$, so $1+x/y\in R$ because $R$ is a subring, and $|x+y|=|y|\,|1+x/y|\le|y|$. It is Noetherian since every ideal in a PID is generated by one element. The restriction of the absolute value to $\mathbf Q_\ell$ gives $|\ell|<1$, so the residue field has characteristic $\ell$. By [lem-weil-valued-dvr-finite-quotients], $A_n$ is finite and the quotient transitions are surjective. The DVR expansion writes $\ell=u\varpi^r$ with $r>0$; hence $\ell^n$ kills $A_n$. Multiplication by $\varpi^n$ is injective, and the two-term finite free complex $[R\xrightarrow{\varpi^n}R]$ in degrees $-1,0$ has only cohomology $A_n$ in degree zero. Thus $A_n$ is perfect by [def-pc-perfect-ring-complex]. These are precisely the ring assumptions of [def-weil-pbc-adic-coefficient-datum] for $I=(\varpi)$: finite perfect quotients and torsion $R/I$. The integral coefficient sheaf is its inverse-limit sheaf $R_T$, not the discrete constant sheaf. The integral input category of [def-weil-pbc-bounded-constructible-complete] includes derived completeness, the uniform interval and compatible etale-origin reductions. Replacing the positive index $n$ by $n+1$ gives exactly the indexing used by the smooth coefficient theorems.

Cited nodes: lem-weil-l-adic-extension-integers-dvr, lem-weil-valued-dvr-finite-quotients, def-pc-perfect-ring-complex, def-weil-pbc-adic-coefficient-datum, def-weil-pbc-bounded-constructible-complete.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Clause (4): finite, completed and transported coefficient domains.

### lem-sf-bc-finite-mate-domain

Former step 4:

At finite etale level, apply [thm-weil-pbc-bounded-below] when $f$ is proper to the underlying abelian complex. Its input is bounded below with torsion cohomology. The final equivalence in [lem-weil-pbc-exchange-forget-coefficients] transfers invertibility to the specified constant-module mate, retaining the source and target comparisons of that lemma. When $g$ is smooth, apply [sbc-thm-bounded-below-derived-smooth-base-change]. To match its diagram (the square of the smooth base change theorem it refers to, with $h:Y\to X$, $e:Y\to T$), its smooth map $f:X\to S$ is our $g:Y'\to Y$, its quasi-compact quasi-separated map $g:T\to S$ is our $f:X\to Y$, its $h$ is our $f':X'\to Y'$, and its $e$ is our $g':X'\to X$; Steps 5, 7, 8 and 9 use this matching of roles, whatever the position of the arrows in the cited squares. Our $f$ is qcqs by Step 1. Every $A_n$-cohomology sheaf is killed by $\ell^n$, an invertible integer on $Y$, so it lies in the allowable-torsion category of that theorem. Its exchange is therefore invertible; the same forget-coefficients equivalence identifies this with the module exchange. This proves the finite etale ordinary assertion for the actual map, without requiring that $K$ be bounded above.

Cited nodes: thm-weil-pbc-bounded-below, lem-weil-pbc-exchange-forget-coefficients, sbc-thm-bounded-below-derived-smooth-base-change.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Clause (4): bounded-below proper and smooth base change; Stacks 0DDE (lemma-proper-base-change).
Former step 5:

For a finite pro-etale input with witness $\alpha:\nu_X^*L\simeq K$, use [lem-weil-pbc-transport-identifies-exchange]. Its hypothesis on $f,f'$ is qcqs, verified in Step 1. In its notation the equality is $T_L\nu_{Y'}^*(E_L)=\operatorname{Ex}^R_{\nu_X^*L}S_L$, with $S_L,T_L$ isomorphisms. Thus an invertible etale $E_L$ gives an invertible actual pro-etale mate, and naturality in the isomorphism $\alpha$ gives the same conclusion at $K$. In the proper case this is also the precise domain of [thm-weil-pbc-finite-level-proetale], allowing bounded-below witnessed inputs. In the smooth case retain the bounded constructible witness: [sbc-thm-finite-proetale-smooth-base-change], with the diagram labels of Step 4, identifies the same ambient mate with the conjugate etale exchange. It explicitly asserts an isomorphism in the ambient derived category and does not assert bounded constructible endpoints. A finite-Tor input is a restriction of this bounded constructible input domain.

Cited nodes: lem-weil-pbc-transport-identifies-exchange, thm-weil-pbc-finite-level-proetale, sbc-thm-finite-proetale-smooth-base-change.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Clause (4): etale-origin finite pro-etale transport, including named-map identification.

### lem-sf-bc-completed-mate-domain

Former step 6:

For proper $f$ at $R$, apply [thm-weil-pbc-complete-proetale] to the specified compatible reduction witnesses of $K$. Step 3 supplies its adic datum, and $f$ is proper by hypothesis. This yields invertibility of its completed exchange, the ordered Rlim composite built from the transported finite-level exchanges, using completed pullback. The item's integral map is the completed adjunction mate; [lem-sbc-completed-operations-linear-natural-exchange] states that, under the canonical finite-reduction and direct-image/derived-limit comparisons, this mate is the completed exchange obtained from the finite-level exchanges, and by Step 5 those are the actual finite pro-etale mates. So the mate is invertible, and its raw rationalization is the map used at $E$ in Step 8. For the constructible domain apply [cor-weil-pbc-constructible-complete]: every corner is Noetherian and finite-dimensional by Step 1, both $f$ and $f'$ are proper, $\ell$ annihilates $R/I$ and is invertible on all corners, and the geometric fibres have the nonnegative bound $e$ of Step 2. Its component is explicitly the same completed exchange, now with both endpoints in the uniform completed constructible categories. No assertion about discrete integral etale coefficients is used.

Cited nodes: thm-weil-pbc-complete-proetale, cor-weil-pbc-constructible-complete, lem-sbc-completed-operations-linear-natural-exchange.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Clause (4): completed proper exchange and its constructible restriction; Stacks 09C9 (theorem-proper-base-change).
Former step 7:

For smooth $g$ at $R$, apply [sbc-thm-adic-smooth-base-change], with the diagram relabeling of Step 4 and the index shift of Step 3. Its input corner $T$ is our $X$ and its output corner $X$ is our $Y'$, so both finite-dimension assumptions hold. The input reductions are bounded constructible etale-origin complexes as required in the item; Step 3 gives the finite perfect quotients of invertible torsion order. The theorem yields invertibility of the canonical completed adjunction-mate exchange in the ambient complete category. For its stronger conclusion require a single interval $[a,b]$, independent of $n$, for all four finite-level objects, in our labels
$$Rf_{n,*}K_n,\quad Lg_n^*Rf_{n,*}K_n,\quad Lg_n'^*K_n,\quad Rf'_{n,*}Lg_n'^*K_n,$$
with constructible cohomology. Exactly the final paragraph of the theorem then places both exchange endpoints in $D^b_c(Y',R)$. The first, ambient conclusion uses no such landing claim. The item retains these additional hypotheses wherever it asserts the constructible conclusion.

Cited nodes: sbc-thm-adic-smooth-base-change.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Clause (4): integral smooth exchange, with separate uniform constructible landing.

### lem-sf-bc-field-mate-domain

Former step 8:

For proper ordinary exchange at $E$, use [thm-weil-pbc-finite-extension]. Its geometric hypotheses were verified in Steps 1--2, and it defines the rational exchange to be the extension of the completed integral one, so it applies to the specified lattice presentation. For smooth ordinary exchange, the chosen lattice is finite-level etale admissible in the sense of [sbc-def-admissible-lattices]. Apply [sbc-thm-e-coefficient-smooth-base-change] with the labels of Step 4. Its functors and exchange are raw scalar localizations of the completed integral ones. The theorem yields the ambient exchange at $K_E$, independent of the chosen lattice isomorphism. Its $D^b_c$ conclusion requires square-constructible admissibility, namely the very four families and common interval of Step 7 applied to the lattice. Hence the item makes exactly that distinction between the ambient isomorphism and its constructible restriction, with no finite reduction of a rational object being taken.

Cited nodes: thm-weil-pbc-finite-extension, sbc-def-admissible-lattices, sbc-thm-e-coefficient-smooth-base-change.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Clause (4): rational ordinary exchange on specified admissible lattice domains.
Former step 9:

For proper ordinary exchange at $\overline{\mathbf Q}_\ell$, apply [thm-weil-pbc-qbar]: its component is the finite-stage exchange after passage to a common finite overfield and is independent of the representative. For smooth ordinary exchange use [sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch], with the labels of Step 4. The item assumes its finite-stage $E$ hypotheses for the representatives and their stability under common finite overfields, not just the existence of an arbitrary lattice. That theorem identifies the ambient component with the canonical raw $E$ exchange through the identity-idempotent inclusion and identifies its further-stage components with scalar extensions. It asserts no constructible landing. Restrict only when the additional landing hypotheses retained in the item put the relevant finite-stage values in $D^b_c$; Step 8 then supplies their isomorphism there. These finite-stage values and maps represent the common-stage constructible operations by [def-weil-pbc-qbar-category].

Cited nodes: thm-weil-pbc-qbar, sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch, def-weil-pbc-qbar-category.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Clause (4): ordinary common-stage exchange, with the ambient/constructible distinction retained.

### lem-sf-bc-compact-support-domain

Former step 10:

For finite compact-support exchange choose $c=(j,p)$ from Step 2. By [lem-weil-pbc-extension-by-zero-exact], $j_!K$ is still bounded below for bounded finite torsion etale $K$: its cohomology is $j_!\mathcal H^i(K)$, so it is still annihilated by the same finite coefficient ring. Step 4 applies proper base change to $p$. Follow that invertible proper exchange by $Rp'_*$ of the natural invertible open comparison of [cor-cbc-derived-extension-zero-base-change]. This is exactly the compactification formula, and [thm-cbc-finite-torsion] identifies it with its compactification-independent map, with the stated refinement comparisons. Neither factor requires smoothness of $g$. On a finite pro-etale input with a witness, [thm-cbc-finite-level-proetale] identifies the transported compactification composite with the etale one conjugated by the witness, and asserts its invertibility and independence of the witness. Thus the compact-support claim holds on both finite domains in the item.

Cited nodes: lem-weil-pbc-extension-by-zero-exact, cor-cbc-derived-extension-zero-base-change, thm-cbc-finite-torsion, thm-cbc-finite-level-proetale.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Clause (4): finite compact-support exchange from proper exchange followed by open base change.
Former step 11:

At $R$, apply [thm-cbc-complete-proetale] to the compactification of Step 2 and the complete input with its compatible etale-origin reductions. Its specified ordered composite is completed proper exchange on $j_!K$, followed by the completed open comparison, and its statement proves invertibility and compactification independence for precisely that composite. Use [thm-cbc-finite-extension] at $E$ on the raw rationalization of the integral category: Step 1 verifies all four Noetherian finite-dimensional schemes and the invertible prime. Its specified exchange is the extension of the completed one, and its statement gives landing in $D^b_c$, naturality for rational morphisms, and independence of the lattice. Finally [thm-cbc-qbar] applies at every admissible common coefficient stage and identifies its component with the finite-stage exchange after a common overfield; its stated independence of field and representative gives the required common-stage map. For these applications the complete integral inputs have compatible etale-origin reductions in a uniform interval; the rational inputs have their specified integral lattice presentations, and the algebraically closed inputs have admissible common-stage presentations with the finite-stage uniform landing bounds. None imposes smoothness on $g$.

Cited nodes: thm-cbc-complete-proetale, thm-cbc-finite-extension, thm-cbc-qbar.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Clause (4): completed, rational and common-stage compact-support exchanges.

### Existing coherence application (former step 12)

It remains to identify the package maps and their equations, rather than just prove existence of unrelated endpoint isomorphisms. Apply [fix-lem-exchanges] on the domains just verified. Its finite ordinary map is the constant-module mate, its witnessed pro-etale ordinary map is the ambient ringed mate, its finite compact-support map is the compactification composite, its integral maps are the completed mate and completed compactification composite, and its field maps are their rational and common-stage transports. Clause (1) identifies the compact-support maps with the cited base-change theorem maps; clause (3) identifies smooth ordinary exchange with smooth base change in the exchanged diagram labels. The proper identifications were supplied in Steps 4--6 and 8--9. Clauses (2) and (4) give identity, horizontal and vertical pasting, refinement independence, and compatibility with composition, with the canonical composition maps inserted. Apply these equations only where the intermediate inputs and composite functors satisfy the indicated domains. This proves exactly the coherence asserted in the item; invertibility does not silently enlarge any of those domains.

Cited node: fix-lem-exchanges.

## What remains

The six new nodes are intentionally unsplit for independent work. No authorized repair point is left unresolved. The first completed server dry run returned OK (not pushed) at 3d1ec797617. I then made the field-node input quantifiers explicit (no changed hypotheses or search question) and refreshed its verbatim citation before the final dry run. The delivery command reports the pushed commit.
