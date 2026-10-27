# Q154 stage-1 re-split repair

## Files written

- lem-sf-constructible-exceptional-coefficient-construction: original statement and statement dependencies retained; seven-step assembly.

- lem-sf-exceptional-finite-operations: statement, unsplit; no Mathlib match; returned steps 1–3.

- lem-sf-exceptional-finite-scalar-mates: statement, unsplit; no Mathlib match; returned steps 4–7.

- lem-sf-exceptional-system-transport: statement, unsplit; no Mathlib match; returned steps 8–9.

- lem-sf-exceptional-integral-reconstruction: statement, unsplit; no Mathlib match; returned steps 10–12.

- lem-sf-exceptional-integral-scalar-mates: statement, unsplit; no Mathlib match; returned steps 13–16.

- lem-sf-exceptional-field-descent: statement, unsplit; no Mathlib match; returned steps 17–19.

- lem-sf-exceptional-refinement-mates: statement, unsplit; no Mathlib match; returned steps 20–21.

## Attachments

None. The project theorem exists_coefficient_construction at Sheaf/Paper/ConstructibleExceptionalCoefficientConstruction.lean:460 ends in sorry; the upstream WeilConjectures search finds no finished declaration.

## Wanted literature

None.

## Repair and retained material

The fresh sandbox had no node, report or searches from the returned delivery, only dispatcher markers. The current live node holds the returned 22-step proof (20,476 characters); the repair note explicitly reopens stage 1. This repair starts from that current node and retains its statement, statement dependencies, source, existing searches and metadata. The complete old proof follows below, including its cited node ids and source places; nothing is discarded or represented as a proof of a new unsplit node.

The seven substantive children are separate obligations, not copies of record clauses: finite restriction and bounds; nonflat coefficient mate transport; actual system site transport; reduction/limit reconstruction and realization; ramified and composite scalar construction; raw/common-field descent; adjoint refinement transport. Each is statement-only, with proof=[], proof_deps=[], proof_origin=null. The final parent proof is 1925 characters.

The maintenance-created item has created.item equal to a Lean module name rather than a DAG id. tools/blueprint_refs.py ancestor therefore prints None. Children record that exact computed ancestor, with the actual blueprint place and via=[item]; the existing item blueprint reference to sk-thm-sf-tensor-hom is retained. This is reported rather than rewriting maintenance metadata.

## Not duplicates

lem-sf-exceptional-finite-operations vs lem-pur-finite-coefficient-adjoint-comparisons: the existing node assumes X and Y separated over k; the new construction permits nonseparated X and Y and specifies the actual adjoint shift and uniform bounds.

lem-sf-exceptional-finite-scalar-mates vs lem-pur-finite-coefficient-adjoint-comparisons: the existing node assumes absolute separatedness and only quotient/finite-free generators; the new one includes literal full-subcategory equality realizations and canonical site/shift transport without absolute separatedness.

lem-sf-exceptional-system-transport vs lem-pur-etale-coefficient-system-adjoint: that node constructs the ordinary etale system adjunction; the new statement transports actual system units, counits and proper/open maps to the pro-etale origin class.

lem-sf-exceptional-system-transport vs lem-per-finite-exceptional-system-adjunction: the latter assumes absolutely separated schemes and does not state the pro-etale system site-equivalence and canonical proper/open transport.

lem-sf-exceptional-integral-reconstruction vs lem-coef-finite-adjunction-diagram-realization: that statement assumes absolutely separated schemes and explicitly excludes integral output, adjunction and bounds; the new obligation is integral reconstruction with normalized ambient realization.

lem-sf-exceptional-integral-scalar-mates vs lem-coef-finite-scalar-mate-realization: the latter assumes absolutely separated schemes and an already constructed integral adjunction, and only treats a fixed finite-free extension; the new statement includes actual ramified reindexing, reductions, scalar realization equalities and all allowed composites.

lem-sf-exceptional-field-descent vs lem-sf-rational-direct-image-adjunctions: the latter concerns right adjoints of ordinary pullback, not exceptional right adjoints of compact support or the common-stage descent construction.

lem-sf-exceptional-field-descent vs lem-pur-transport-qbar-common-stage-counit: that statement concerns smooth purity and condensed coefficient categories, with separate compatibility hypotheses; the new argument concerns raw ordinary coefficient localizations for general separated finite-type f.

lem-sf-exceptional-refinement-mates vs prop-compactification-coherence-detailed: the latter gives finite left compact-support comparisons only; the new obligation includes integral actual-map realization, both conjugate adjunction equations and rational/common-stage transport.

Whole-DAG title/concept searches, Lean searches and whole-blueprint searches for exceptional scalar, system adjunction, rational adjunction, compactification refinement, normalized coefficient, completed scalar and finite Tor were read before the children were created. General tools already present in the DAG remain source material for the child workers; no existing statement covers these normalized obligations with their full hypotheses.

## Review by Q154

I read the current exceptional inverse-image blueprint paragraph and the tensor–Hom unit statement, the six-functor chapter and compatibility unit, and Zheng Propositions 2.23, 2.29, 3.16 and Section 5 (especially 5.22–5.26). Zheng supplies the ordinary etale and system route; the actual pro-etale normalized realizations are the agent-written synthesis of the retained DAG arguments, not attributed verbatim to Zheng. I read the relevant existing finite adjunction, constant tensor, system comparison/effectivity and compactification statement interfaces. The new nodes deliberately expose the substantial transports and normalizations instead of silently taking them from definition nodes.

Assembly step 1 uses the finite operation statement for exactly its uniform bounds, chosen transported adjunction and realizations. Step 2 uses the finite scalar statement for literal restriction, invertible nonflat mates, the counit equation and fixed site/shift normalization. Step 3 uses actual system transport, then integral reconstruction; both statements explicitly name the same etale adjunction, reduction/limit maps and normalized output class. The common bounds hypothesis is supplied by step 1. Step 4 uses the integral scalar statement for reduction, finite-free completed extension, ramified en indices, composite and identity realization maps, and the counit equations. Step 5 uses field descent on precisely those integral choices; its scalar-composition hypothesis is in the integral scalar statement. Step 6 applies the refinement statement to the same finite/system/localized/common-stage adjunctions; it explicitly supplies both equations and all the required realizations. Step 7 is only dependent-record packaging and the empty/identity edge checks. citations.json contains verbatim statement quotes for every citation.

I checked ell differs from p, n>=1, relative separatedness only, Noetherian finite-type inputs, finite rings at finite site comparison, completed rings only at integral stages, and common uniform intervals at reconstruction. Nonflat A_(n+1)->A_n is included using the constant-coefficient exceptional comparison, not an arbitrary sheaf projection formula. Ramification uses A_(L,en), never A_(L,n). A degree-zero free object on Spec k gives ordinary tensor and adjunction unitors; e=1 gives the full tower, while e>1 keeps the least-n subsequence extension. The empty case uses zero and bound zero; the identity case uses the same unitors. Integral equalities are equalities of actual system maps, never deduced from faithfulness of evaluation. Rational localization retains objects and divides morphisms, with no Karoubi completion. No unrestricted ambient exceptional pro-etale adjunction has been introduced.

I checked B–E: self-contained objects and definitions, accurate source places, actual logged Mathlib queries and service outcomes, whole-DAG/blueprint duplicates, no new proof sketches in child statements, no clauses moved to one replacement node, no new statement depending on the parent, and exact cited statement coverage. The old arguments are preserved below for subsequent workers. All substantive assembly steps are under 2000 characters. No new child was split, no Lean was written, no compiler was run.

## Retained returned arguments and allocation

### lem-sf-exceptional-finite-operations

Old step 1: Fix a compactification $c=(j,p_c)$. Proper finite type over the finite-type $k$-scheme $Y$ makes its middle scheme finite type over $k$; all three schemes are Noetherian by the finite-type-over-Noetherian lemma. Choose a nonnegative dimension bound $d_c$ for the middle scheme using the finite-dimension theorem, and use $d_c=0$ when it is empty. For an input of Tor interval $[a,b]$, open extension preserves that interval and bounded constructibility, and the direct-image theorem applied to $p_c$ gives $F^c_{A}K=Rp_{c,*}j_!K$ in the finite-Tor category with interval $[a,b+2d_c]$. These constants depend on $c$, not the coefficient level. The termwise exact-functor and derived-direct-image theorems give the left functor its exact and shift structures.

Cited nodes: lem-weil-pbc-finite-type-over-noetherian, lem-kun-dimension-finite-type, lem-trf-open-ctf, cor-sf-direct-image-ctf-proetale, lem-sf-exact-functor-derived-triangulated, lem-weil-pbc-derived-direct-image-triangulated.

Source: {"document": "literature/zheng-six-operations-lefschetz-verdier-DM-stacks_arXiv-1006.3810.pdf", "place": "Construction 2.17, Theorem 2.18, and Proposition 3.16(1); finite-stage compact support."}

Old step 2: On ordinary etale categories choose the compact-support right adjoint of thm-amb-etale-exceptional-adjoint. The bounded-class adjunction theorem identifies its pro-etale transport with the specified composite $G^c_A=\nu_X^*f^\times_{c,A}R\nu_{Y,*}$ and gives a natural Hom bijection for all bounded-below etale-origin left inputs. Every bounded constructible input has that origin. The preservation corollary applies to this same composite and supplies bounded constructibility and a Tor interval independent of the finite level. Thus the bijections restrict to the actual full finite-Tor categories and give an adjunction there, with unit, counit and both triangles by the natural-bijection theorem. The ambient realization of $F$ and the finite-right realization are the inclusion identifications of these restrictions.

Cited nodes: thm-amb-etale-exceptional-adjoint, thm-sf-ambient-adjoint-class, lem-sf-proetale-constructible-origin, cor-pur-general-admissibility-datum, def-weil-exceptional-inverse-image, lem-weil-pbc-adjunction-of-natural-bijection.

Source: {"document": "literature/zheng-six-operations-lefschetz-verdier-DM-stacks_arXiv-1006.3810.pdf", "place": "Proposition 2.23, Proposition 3.16(2), and the blueprint finite exceptional composite."}

Old step 3: The finite-Tor categories are triangulated by the finite-ctf theorem. Equip the right adjoint with the unique adjoint shift structure for the already chosen left shift structure. The shift-adjunction theorem gives compatibility of its unit and counit at every integer. Apply the triangulated-right-adjoint theorem, whose shift hypotheses are now satisfied, to obtain right exactness with these very shifts. Additivity of the right adjoint also follows directly from its Hom bijections: transposition respects sums because the left functor is additive. This constructs the finite-stage Operation fields, rather than assuming them.

Cited nodes: lem-weil-finite-ctf-triangulated, lem-weil-pbc-adjunction-shift-compatibility-unique, lem-sf-triangulated-right-adjoint.

Source: {"document": "literature/zheng-six-operations-lefschetz-verdier-DM-stacks_arXiv-1006.3810.pdf", "place": "Finite adjunction; exactness formalized by Stacks Tag 0A8D, lemma-adjoint-is-exact."}

### lem-sf-exceptional-finite-scalar-mates

Old step 4: For a finite coefficient map $A\to B$, choose a bounded flat constructible etale model $P$ of a finite-Tor object. The flat-model theorem supplies it on our Noetherian schemes. Each $P^i\otimes_A B$ is flat over $B$: testing an injection of $B$-modules is testing the same injection after restriction to $A$. Its terms are finite locally constant on finite refinements of the strata trivializing the terms of $P$, so its cohomology is constructible. The complex still occupies $[a,b]$. Derived change of rings gives its map action, exactness and independence of model. Transport to the pro-etale category through constructible origin and the Tor comparison; exact inverse image commutes with this constant-ring tensor on the flat model. Define the scalar functor as the literal restriction of the ambient derived extension. Its realization is consequently the equality isomorphism required in finiteScalar_normalized, including composites of the allowed maps.

Cited nodes: lem-sf-flat-model, lem-pur-derived-change-of-rings, lem-sf-proetale-constructible-origin, lem-sf-comparison-tor-amplitude.

Source: {"document": "literature/zheng-six-operations-lefschetz-verdier-DM-stacks_arXiv-1006.3810.pdf", "place": "Finite-coefficient change of rings and bounded flat models; Proposition 2.29."}

Old step 5: At a finite ring map work first on etale categories. Take $q$ to be the proper/open scalar comparison specified by lem-pur-etale-compact-scalar-coherence, not an arbitrary isomorphism. It is invertible even for nonflat quotients. To identify the scalar restriction square use ordinary ringed direct-image composition, which applies also to the same topos with a changed ring; open extension commutes with restriction on the underlying complexes. This gives $\operatorname{Res}_YF_B\cong F_A\operatorname{Res}_X$. Together with the normalized derived scalar/restriction adjunction it fixes the scalar-adjunction mate. Thus this $q$ has exactly the realization equation CounitQNormalized at the finite stages.

Cited nodes: lem-pur-etale-compact-scalar-coherence, lem-weil-pbc-ringed-topoi-derived-pushforward-composition, lem-pur-sheaf-ring-derived-coefficient-adjunction.

Source: {"document": "literature/zheng-six-operations-lefschetz-verdier-DM-stacks_arXiv-1006.3810.pdf", "place": "Proper/open scalar comparison; see also Stacks more-etale.tex Tag 0GL6, remark-Rf-lower-shriek-change-of-rings."}

Old step 6: Define $b_L$ as the $F_B\dashv G_B$ transpose of $T_Y\epsilon_{A,L}\circ q^{-1}_{G_AL}$. This immediately gives the required counit equation. Prove invertibility before restricting: the chain
$$\operatorname{Hom}_A(K,\operatorname{Res}_XG_BN)\cong\operatorname{Hom}_B(T_XK,G_BN)\cong\operatorname{Hom}_B(F_BT_XK,N)\cong\operatorname{Hom}_B(T_YF_AK,N)\cong\operatorname{Hom}_A(K,G_A\operatorname{Res}_YN)$$
identifies $\operatorname{Res}_XG_B$ with $G_A\operatorname{Res}_Y$ by Yoneda. With this identification, restriction of $b_L$ is the exceptional constant-$B$ tensor map: its transpose is inverse projection followed by $1\otimes\epsilon_A$. The constant-tensor lemma makes this specified map invertible for arbitrary $B\in D(A\text{-}\mathrm{Mod})$, including nonflat quotients. Restriction detects quasi-isomorphisms since the cohomology of its cone is the same underlying abelian sheaf. Hence $b_L$ is invertible as a $B$-linear map.

Cited nodes: lem-pur-sheaf-ring-derived-coefficient-adjunction, thm-amb-etale-exceptional-adjoint, lem-galois-yoneda-hom-bijection, lem-pur-etale-exceptional-constant-tensor.

Source: {"document": "literature/zheng-six-operations-lefschetz-verdier-DM-stacks_arXiv-1006.3810.pdf", "place": "Propositions 2.23 and 2.29(2); constant-coefficient exceptional tensor map (2.26.1)."}

Old step 7: Transport $q,b$ and the etale adjunction through the constructible-origin equivalence. The compact-support comparison and the Tor comparison identify the same $F,G$ on the finite full categories; the site-comparison unit is invertible on bounded-below complexes. Proper/open comparisons are the canonical adjunction mates, so the transported $q$ is the proper/open pro-etale scalar map in the realization equation. For its proper factor use the counit-normalized direct-image comparison; for its open factor use extension-zero comparison. The inverse-image/tensor identification is canonical on flat models by the derived pullback theorem. The counit-transpose description identifies the transported $b$ and counits, without choosing unrelated Hom bijections. Tensor comparisons, the proper projection mate and termwise open comparisons commute with shifts. Uniqueness of adjoint shifts then gives bShift for their transposes; composition and whiskering preserve these equations.

Cited nodes: lem-sf-proetale-constructible-origin, lem-sf-comparison-tor-amplitude, thm-weil-pbc-site-comparison, lem-sf-class-compact-support-comparison, lem-weil-pbc-comparison-direct-image-canonical-mate, lem-cbc-proetale-extension-zero-comparison, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-weil-pbc-ringed-projection-mate-exact, lem-weil-pbc-adjunction-shift-compatibility-unique, lem-weil-pbc-commshift-nattrans-comp-whisker.

Source: {"document": "literature/stacks-project/proetale.tex", "place": "Tags 09AK, lemma-compare-constructible; 09AL, lemma-compare-constructible-derived; 09B1, lemma-compare-derived; finite proper/open adjunction mates."}

### lem-sf-exceptional-system-transport

Old step 8: Form the actual strict systems with coefficients $A_n=R_E/\varpi_E^n$ on the etale site. The coefficient-system adjunction theorem gives an $R_E$-linear exact adjunction $\mathsf F^{et}=Rp_{c,A,*}j_{!,A}\dashv\mathsf G^{et}$ on their ordinary derived categories. Its conclusion supplies $e_n\mathsf G^{et}\cong f^\times_{c,A_n}e_n$, including evaluated units, counits and quotient transitions, a uniform lower bound and preservation of bounded-below normalization. These assertions are not inferred merely from evaluation of the left functor. Schemes have trivial inertia, and our geometric hypotheses are precisely those of that node; in particular $Y$ may be nonseparated. All further operations use this actual derived-system adjunction.

Cited nodes: lem-pur-etale-coefficient-system-adjoint, lem-pur-coefficient-system-derived-comparison.

Source: {"document": "literature/zheng-six-operations-lefschetz-verdier-DM-stacks_arXiv-1006.3810.pdf", "place": "Construction 5.15, Lemmas 5.13, 5.16 and 5.22, and Proposition 5.24 (pp. 34–36)."}

Old step 9: Write $C_T=\nu^*_{T,A}$ and $V_T=R\nu_{T,A,*}$. The system comparison theorem supplies an actual adjunction with the stated evaluation isomorphisms. On bounded-below systems of etale-origin levels its counit is invertible; its unit is invertible because it evaluates to the finite site-comparison unit and evaluations jointly detect isomorphisms. These are equivalences on this class and preserve normalization. Construct the system compact-support comparison by the derived direct-image mate for the proper factor and the termwise open comparison. Evaluation gives the canonical proper and open comparisons, so joint conservativity proves that this actual system map is invertible. The system Hom chain is therefore
$$\operatorname{Hom}(\mathsf F^{pro}M,N)\cong\operatorname{Hom}(\mathsf F^{et}V_XM,V_YN)\cong\operatorname{Hom}(V_XM,\mathsf G^{et}V_YN)\cong\operatorname{Hom}(M,C_X\mathsf G^{et}V_YN).$$
Use its unit and counit to transport the adjunction and its finite coefficient transposes. No faithfulness of finite evaluations on morphisms is used.

Cited nodes: lem-pur-coefficient-system-derived-comparison, thm-weil-pbc-site-comparison, lem-pur-system-level-left-extension, lem-weil-pbc-ringed-topoi-derived-pushforward-composition, lem-weil-pbc-comparison-direct-image-canonical-mate, lem-cbc-proetale-extension-zero-comparison, lem-weil-pbc-adjunction-of-natural-bijection.

Source: {"document": "literature/zheng-six-operations-lefschetz-verdier-DM-stacks_arXiv-1006.3810.pdf", "place": "Zheng Lemma 5.22 transported using system comparison; finite comparison is Stacks Tag 09B1."}

### lem-sf-exceptional-integral-reconstruction

Old step 10: Use the reduction/total-limit adjunction $\mathcal R_T\dashv\mathcal L_T$ of the derived-system evaluation calculus. Its unit is the actual compatible cone of quotient maps from one flat-term K-flat representative. The $L=E$ case of the finite-free completed-scalar comparison identifies that unit with the derived-completeness isomorphism for integral objects. On normalized systems its counit is invertible by normalized-DVR effectivity; the component is the scalar adjunct of the actual total-limit projection. Thus these functors restrict to mutually inverse equivalences between derived-complete objects and normalized systems, with the named unit and counit. Under the integral category definition, common constructible cohomological and Tor intervals on the levels are exactly the finiteness conditions needed for these equivalences to restrict to our integral finite-Tor subcategory.

Cited nodes: lem-coef-derived-system-evaluation-calculus, lem-weil-finite-free-completed-scalar-comparison, lem-coef-normalized-dvr-effectivity, def-weil-derived-complete-integral-detailed, def-weil-finite-tor-amplitude.

Source: {"document": "literature/zheng-six-operations-lefschetz-verdier-DM-stacks_arXiv-1006.3810.pdf", "place": "Reduction and total-limit reconstruction; Zheng Section 4 and the explicit pro-etale effectivity nodes."}

Old step 11: Restrict the transported system adjunction to normalized systems of bounded constructible finite-Tor levels. The left bounds of Step 1 are uniform in $n$; the finite exceptional preservation corollary gives common right bounds, and the system theorem gives normalized right outputs. Define $F_R=\mathcal L_Y\mathsf F^{pro}\mathcal R_X$ and $G_R=\mathcal L_X\mathsf G^{pro}\mathcal R_Y$. Transport the actual unit and counit through the equivalences of Step 10; their triangles follow from the system triangles and those equivalences. The integral compact-support theorem identifies $F_R$ with the published reduction-tower functor and its specified reductions. The integral finite-Tor subcategory is triangulated. Reduction and total limit are exact, and the system adjunction is exact, so these are exact operations; alternatively apply the right-adjoint exactness theorem with the adjoint shifts. The unique adjoint shift structures give unitShift and counitShift.

Cited nodes: lem-pur-etale-coefficient-system-adjoint, cor-pur-general-admissibility-datum, lem-coef-integral-compact-support, lem-weil-integral-ctf-triangulated, lem-weil-pbc-ringed-strict-tower-homotopy-limit, lem-weil-pbc-adjunction-shift-compatibility-unique, lem-sf-triangulated-right-adjoint.

Source: {"document": "literature/zheng-six-operations-lefschetz-verdier-DM-stacks_arXiv-1006.3810.pdf", "place": "Zheng Constructions 5.20 and 5.25, Proposition 5.24; normalized-system integral adjunction."}

Old step 12: Choose the integral left functor to be the prescribed reduction-tower compact-support functor, transporting the adjunction of Step 11 along its specified identification. The system-realization theorem applied to the single word $S_{p_c}J_j$ supplies its natural realization in the ambient completed-ring derived category, with the canonical proper/open maps. All intermediate objects satisfy its hypotheses by Step 1 and Step 11. Take $r_{c,R}$ to be the inverse of this ambient-to-tower realization after the integral-left identification. Then the included integralLeft map is, by this very choice, $r_{c,R}$ followed by the specified ambient-to-tower realization: this is integralLeft_normalized. This uses a realization of the actual system maps, rather than inferring equality of integral maps from finite evaluations. For the named integral realization and its maps, use the slotwise shift-realization theorem; it states compatibility with the canonical termwise and Roos-cone shifts for these same normalized expressions.

Cited nodes: lem-sf-integral-compactification-system-realization, def-weil-integral-rational-qbar-compact-support, lem-pur-integral-realization-shift-coherence.

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/def-weil-exceptional-inverse-image.md", "place": "Single-compactification word realization; the published reduction-tower compact support and its proper/open maps."}

### lem-sf-exceptional-integral-scalar-mates

Old step 13: For integral reduction choose the literal restriction of ambient derived extension to $A_{E,n}$; its output is the reduction in the definition of the integral finite-Tor category. Step 10 identifies the reduction of $F_R,G_R$ with their evaluated system operations. Its unit and counit identify those comparisons with the system evaluation comparisons, hence the resulting $b$ is the counit transpose of $q$. The proper/open system realization identifies the left map with the ambient scalar mate, so comparison_normalized holds. Its component equations hold as maps before evaluation, since they are transported system adjunction equations. These comparisons commute with shifts by their derived constructions and the unique adjoint shift structures. For the named integral realization and its maps, use the slotwise shift-realization theorem; it states compatibility with the canonical termwise and Roos-cone shifts for these same normalized expressions.

Cited nodes: lem-coef-derived-system-evaluation-calculus, lem-pur-etale-coefficient-system-adjoint, lem-sf-integral-compactification-system-realization, def-weil-finite-tor-amplitude, lem-weil-pbc-adjunction-shift-compatibility-unique, lem-pur-integral-realization-shift-coherence.

Source: {"document": "literature/zheng-six-operations-lefschetz-verdier-DM-stacks_arXiv-1006.3810.pdf", "place": "Zheng Lemmas 5.16 and 5.22, with the reduction/limit unit and counit normalization."}

Old step 14: For an embedding $E\to L$, identify $E$ with its image and write $e$ for the ramification index. At selected levels $B_n=R_L/\varpi_E^nR_L=A_{L,en}$, use the finite-free system scalar comparison in the system adjunction theorem. To recover the full $L$-tower use the subsequence left-extension adjunction: for each $m$, choose the least $n$ with $en\ge m$ and form $A_{L,m}\otimes^L_{A_{L,en}}(-)_n$. On normalized systems its evaluation counit is the normalization isomorphism, so joint conservativity makes restriction and extension inverse equivalences. This transports the finite-free system comparisons to every level, on actual system maps. The same theorem gives the prescribed transition maps. Thus the scalar mate is invertible without replacing $en$ by $n$ or assuming that arbitrary derived evaluations are faithful.

Cited nodes: lem-pur-etale-coefficient-system-adjoint, lem-pur-system-level-left-extension.

Source: {"document": "literature/zheng-six-operations-lefschetz-verdier-DM-stacks_arXiv-1006.3810.pdf", "place": "Zheng Lemma 5.22; finite-free extension and cofinal ramified subsequences, with derived subsequence left extensions."}

Old step 15: Ordinary derived extension from $\widehat R_E$ to $\widehat R_L$ agrees with the published strict-tower integral scalar extension via the specified comparison $\chi_{L/E}$. It is an isomorphism, natural and complete, by the finite-free completed-scalar theorem. The constructibility and adic Tor-bound theorems supply the actual scalar functor on our subcategories, with the same common interval. Choose this published functor for integralScalar_eq, and choose $\theta=\chi^{-1}$ for its ambient realization; integralScalar_normalized now holds literally. Transport Step 14 and its counit-transpose equation through $\chi$ and the proper/open realization of Step 12. The left map is the canonical ambient scalar mate: on the ringed diagram site it is the proper scalar mate followed by the open tensor map, and the realization theorem intertwines these generator maps. This gives the integral $q,b$ and their required normalizations; the complete-scalar comparison and derived adjunction structures supply their shifts. For the named integral realization and its maps, use the slotwise shift-realization theorem; it states compatibility with the canonical termwise and Roos-cone shifts for these same normalized expressions.

Cited nodes: lem-weil-finite-free-completed-scalar-comparison, lem-weil-integral-scalar-extension-constructible, lem-pur-adic-scalar-extension-tor-bound, lem-sf-integral-compactification-system-realization, lem-pur-ringed-coefficient-projection-cocycle, lem-sf-open-tensor-normalization, lem-pur-integral-realization-shift-coherence.

Source: {"document": "literature/zheng-six-operations-lefschetz-verdier-DM-stacks_arXiv-1006.3810.pdf", "place": "Finite-free integral coefficient extension, Zheng Section 5; explicit completed-scalar comparison and diagram-site realization."}

Old step 16: For every allowed composite choose the same scalar functor as for its actual coefficient-sheaf map: the literal derived restriction for a finite target, and the published integral extension for an integral target. Derived balanced associativity identifies successive scalar extensions with that choice. On flat-term representatives the map is $(x\otimes s)\otimes t\mapsto x\otimes b(s)t$, and the identity map is $x\otimes r\mapsto rx$. Lift these through the full inclusions using $\theta$; this defines scalarComposition and scalarIdentity with exactly their ambient normalization equations. The proper scalar-mate cocycle on ringed diagram sites and the open-unit tensor normalization identify the composite $q$ with the mate for the composite ring map. Compose the $b$ maps with these associators: the counit equation follows by substitution of the two counit equations and naturality of $q$. Invertibility and shift compatibility survive composition. Thus the construction is defined for every Allowed witness, including identity and composite witnesses, and all q maps have comparison_normalized.

Cited nodes: lem-sfb-successive-derived-quotient-normalization, lem-pur-sheaf-ring-derived-coefficient-adjunction, lem-pur-ringed-coefficient-projection-cocycle, lem-sf-open-tensor-normalization, lem-weil-pbc-mate-pasting, lem-weil-pbc-commshift-nattrans-comp-whisker.

Source: {"document": "literature/zheng-six-operations-lefschetz-verdier-DM-stacks_arXiv-1006.3810.pdf", "place": "Canonical balanced scalar associativity and proper/open mate pasting; diagram-site comparisons before total limit."}

### lem-sf-exceptional-field-descent

Old step 17: By the residue-Tor theorem every integral constructible representative belongs to the integral finite-Tor category. Localize the $R_E$-linear operations, natural transformations and adjunction Hom bijections at $\varpi_E$. The inverse localized Hom maps remain inverse because localization preserves the equations for their composites; the resulting unit, counit and triangles are their images. Raw scalar localization has the same objects and localized Hom modules, with exact localization functor. Hence the localized adjunction acts on exactly the published rational categories, and its operations and coefficient maps are exact with the induced shifts. Choose its left functor to be the published rational compact support and its rationalLeft realization to be the identity identification. This does not require a Karoubi completion.

Cited nodes: lem-coef-integral-residue-tor, def-weil-rationalization-karoubi, lem-weil-linear-scalar-localization-triangulated, lem-weil-pbc-adjunction-of-natural-bijection, def-weil-integral-rational-qbar-compact-support.

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/def-weil-exceptional-inverse-image.md", "place": "Raw rational localization of the integral adjunction; blueprint coefficient construction."}

Old step 18: For integral-to-rational comparison take $q$ to be the localization of integralLeft followed by the inverse of rationalLeft. Take $b$ to be the identity comparison on the localized integral-right object, transported along those choices. The counit equation is the image of the integral one, so it has the required transpose normalization. For a rational embedding $E\to L$, define $q,b$ by localizing their integral versions on the same object representatives. On a morphism $h/\varpi_E^r$ use its localized image; the integral maps are linear and natural, so this is independent of representatives and natural. This gives exactly rationalization_normalized and rational_normalized: the left maps are the raw images of the indicated integral maps. The scalar-extension theorem and localized derived structures give the required endpoint shifts, and the comparisons preserve them.

Cited nodes: def-weil-rationalization-karoubi, lem-weil-scalar-extension-exact-triangulated, lem-weil-pbc-commshift-nattrans-comp-whisker.

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/def-weil-exceptional-inverse-image.md", "place": "Rationalization and rational coefficient comparisons, on the prescribed integral representatives."}

Old step 19: Define the closed-stage operations on a pair $(E,K)$ by $(E,F_EK)$ and $(E,G_EK)$. For a map represented over $L$ use its image under $F_L$ or $G_L$, conjugated by the scalar comparisons. The left transition identities follow from canonical tensor associativity and proper/open mate pasting of Step 16. For the right transitions, take the inverse transposes of the two composites: substitution of the counit equations reduces equality to the left transition identity. Injectivity gives equality. Therefore passage to a larger common field preserves these represented maps, composition and identities. Likewise the Hom bijections commute with transition maps, so inverse natural bijections pass to the directed colimit defining the closed coefficient category. Use them for the adjunction. Distinguished triangles and shifts are represented over one finite field, which gives exactness. On the inclusion of a finite common field take $q$ to be the identity on $(E,F_EK)$; take $b$ to be its counit transpose. This is the identity on $(E,G_E L)$ by the finite-field adjunction. These choices give common_normalized and the required shifts.

Cited nodes: def-weil-algebraically-closed-coefficients, lem-weil-scalar-extension-composition, lem-weil-pbc-mate-pasting, lem-weil-pbc-adjunction-of-natural-bijection.

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/def-weil-exceptional-inverse-image.md", "place": "Common finite-field construction and third Hom bijection of sk-thm-sf-tensor-hom."}

### lem-sf-exceptional-refinement-mates

Old step 20: For a proper refinement $u:c\to d$ at finite coefficients use the canonical comparison $\alpha:F^c\cong F^d$ of compactification coherence. Its source map is the inverse of $j_{d!}\cong Ru_*j_{c!}$ followed by proper composition. The etale definition normalizes this open map by the open-unit transpose of the clopen-section restriction isomorphism. Transport along the canonical site comparisons of Step 7; they are adjunction mates, so the open unit and proper counit remain the named ones. This is exactly RingRefinementNormalized at finite coefficients. On strict systems use the same proper/open map in the system realization theorem and take its total-limit realization. The theorem intertwines open units, proper counits and direct-image composition before total limit; hence, under $r_{c,R},r_{d,R}$, it gives RingRefinementNormalized at the integral stage as well. Its intermediate bounds follow from Step 11. These maps commute with shifts because the generator maps do. For the named integral realization and its maps, use the slotwise shift-realization theorem; it states compatibility with the canonical termwise and Roos-cone shifts for these same normalized expressions.

Cited nodes: prop-compactification-coherence-detailed, def-weil-pbc-proper-open-comparison, lem-sf-integral-compactification-system-realization, lem-weil-pbc-comparison-direct-image-canonical-mate, lem-cbc-proetale-extension-zero-comparison, lem-weil-pbc-commshift-nattrans-comp-whisker, lem-pur-integral-realization-shift-coherence.

Source: {"document": "literature/zheng-six-operations-lefschetz-verdier-DM-stacks_arXiv-1006.3810.pdf", "place": "Proper/open compactification refinement, with open-unit and proper-counit normalization; Stacks Tag 0F7I, lemma-shriek-well-defined."}

Old step 21: Define $\rho:G^d\to G^c$ to be the $F^c\dashv G^c$ transpose of $\epsilon^d\circ\alpha_{G^d}$, and its inverse as the transpose using $\alpha^{-1}$. Substituting the counit equations, naturality of $\alpha$ and the triangle identities shows their composites transpose to the original counits, so they are inverse by injectivity. This proves the displayed refinement counit equation. For the unit equation, transpose its left side to $\epsilon^d_{F^dK}\circ\alpha_{G^dF^dK}\circ F^c\eta^d_K=\alpha_K$, using naturality and the $d$ triangle. Transpose its right side to $\alpha_K$ using the $c$ triangle. This proves the second equation. The unique-adjoint shift theorem makes $\rho$ shift-compatible with the shifts already chosen. At rational stages define $\alpha,\rho$ by localization of these maps; at the closed stage take their common-field representatives. Then refinementRational is the defining localization equality and refinementCommon is the defining common-stage equality conjugated by the common q maps.

Cited nodes: lem-weil-pbc-adjunction-of-natural-bijection, det-sp-unique-right-adjoint, lem-weil-pbc-adjunction-shift-compatibility-unique, def-weil-rationalization-karoubi, def-weil-algebraically-closed-coefficients.

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/def-weil-exceptional-inverse-image.md", "place": "Adjoint transposition of compactification refinements and raw/common-stage realizations."}

### Final assembly (old step 22)

Collect the operations and ring realizations of Steps 1–3 and 11–12, scalar functors and their realization equalities of Steps 4 and 13–16, the individual counit-normalized comparisons, field comparisons of Steps 17–19, and refinement maps of Steps 20–21. Each later field refers to these same earlier choices. This fills the four dependent records ring, fields, common and refinements, and hence CoefficientConstruction; wrapping it gives the required Nonempty. If $X$ is empty every output on $X$ is zero and choose all bounds there to be $[0,0]$; if $Y$ is empty then $X$ is empty. The positive index $n\ge1$ avoids the zero quotient. For $f=\mathrm{id}$ and identity scalar changes the maps used above are the tensor unitors and adjunction identities. These checks need neither a dimension for an empty scheme nor absolute separatedness.

## Unfinished work

The new nodes intentionally remain unsplit for independent parallel workers. The parent repair is complete subject to required server checks and delivery.
