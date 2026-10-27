# Worker report: re-split repair

1. Files written: the item under `dag/nodes/sec-six-functors-basics/`, with its mathematical statement unchanged and its proof replaced by a short assembly; three new statement nodes in the same chapter:
   - `lem-sfb-semilinear-translated-modification-product`: unsplit; no Mathlib match. Twisted factors, their embeddings, permutation action and invariant common isomorphism open.
   - `lem-sfb-projective-fibre-product-closed-model`: unsplit; no Mathlib match. Finite fibre-product embeddings, relative embeddings of closed models, properness, Noetherianity and the dense-open surjectivity criterion.
   - `lem-sfb-invariant-integral-open-schematic-closure`: unsplit; no Mathlib match. Integral schematic closure, descended action and canonical generic stalk isomorphism.
2. Attachments: none. The project was searched for the item id and for semilinear/equivariant Chow constructions. The current `Sheaf.AlgebraicGeometry.SemilinearEquivariantChowModification` declaration at line 105 contains `sorry`; no corresponding finished theorem in `WeilConjectures/` states all the clauses.
3. WANTED: de Jong, *Families of curves and alterations* (1997), §2.10, printed p.605, for the averaging-route attribution of the item and the translated-product node. The previous proof records an online reading; I did not replace that by a claim of local access. Its full detailed construction is retained below, and the checked local mathematical sources are Stacks, not this missing article.
4. What needed repair: the 7,622-character nine-step argument was too much work for one queue item. The repair introduces three independent construction lemmas rather than deleting its details or moving the whole result into one new theorem. No statement dispute or changed hypothesis is needed. The sandbox initially had only dispatcher marker files, with no node, report or search log; the current repository's full nine-step version was copied as the returned baseline. The initial required dry run exited with the diagnostic that report.md was missing. I preserved all existing node metadata, searches and ancestry, and added real new searches with their full output.
5. Unfinished work: the three new nodes deliberately have status `unsplit`, empty `proof` and `proof_deps`, and no proof sketch inside their statements, as the human requested for parallel work. There is no unaccounted-for argument in the parent assembly. No Lean was written and no compiler, Lake or build tool was run.

## Repair allocation

The parent assembly is 2,127 characters in five steps, below the 3,000-character limit. Its statement is byte-for-byte equal as a JSON string to the returned baseline. The new statements are self-contained and independent of the parent, and none asserts the existence of an equivariant Chow modification from the parent's hypotheses.

| Returned argument | Where it now belongs |
|---|---|
| 1: field spectrum Noetherian, ordinary Chow modification, finite projective embedding and Noetherian X | Parent step 1, unchanged |
| 2: semilinear twists, base-change embeddings, finite intersection of translates | Translated-product node |
| 3: separated-diagonal embedding of the fibre product, product of closed immersions, iterated Segre and the one-factor case | Projective-closed-model node |
| 4: projection formulas defining the action, common image, semilinearity, group law and inverse | Translated-product node |
| 5: common isomorphism open and equivariant inverse open immersion | Translated-product node |
| 6: reduced closure, nonempty irreducible support, integral T, restriction of schematic image | Invariant-closure node |
| 6: projective P is proper and finite type, hence Noetherian | Projective-closed-model node |
| 7: kernel ideal invariance, scheme-level descended automorphisms and equivariance | Invariant-closure node |
| 8: closed-model absolute embedding, closed graph and relative embedding, properness and finite type, closed dense image is all of X | Projective-closed-model node |
| 9: both generic points lie in the common open; actual stalk map and field property | Invariant-closure node |

The argument sizes assigned to the three workers are comparable: returned steps 2+4+5 total 2,260 characters, steps 3+8 total 2,334 characters, and steps 6+7+9 total 2,434 characters, with the short ambient-Noetherianity part of step 6 assigned to the second node. The statement lengths are also comparable. A worker can prove any of the three without proving either of the other two: the first takes a supplied ordinary modification, the second arbitrary projectively embedded factors, and the third a supplied Noetherian ambient model and invariant isomorphism open.

## Review by NK

I read the chapter and unit records, the current main-20261015 unit text, and the Noetherian Chow modification statement/proof in that snapshot. This repair stays below that route; it changes no chapter, unit, target statement or Lean declaration. `blueprint_refs.py ancestor` confirms that the inherited ancestry has from.node = null. The new nodes retain the inherited exact place and put the item in front of the via list. Whole-blueprint searches for equivariance, semilinearity, Segre, closure, projective permanence, finite fibre products, translated modifications and invariant integral opens found no existing blueprint theorem with any complete new statement. All source-overlap candidates were opened and compared, as recorded below.

For parent step 1 I read each of its six cited statements: `def-weil-field` gives inverses, so a nonzero ideal contains 1; `pqf-def-locnoeth` defines the local Noetherian condition, and Spec k is affine and quasi-compact; `def-pc-integral-scheme` gives reducedness; `lem-fin-noetherian-chow-modification` really supplies a proper modification, its dense isomorphism open and a projective source; `def-pc-projective-morphism` explicitly means an embedding into finite projective space; `lem-weil-pbc-finite-type-over-noetherian` applies to finite-type X over the Noetherian field spectrum. Stacks coherent.tex Tag 0200, lemma-chow-Noetherian, and the current blueprint proof were read. I did not read equivariance into this nonequivariant tool.

Parent step 2 takes precisely the twisted factors, embeddings, actual projection-defined action and common open from the new translated-product statement. I checked its three source arguments against morphisms.tex Tag 01WF, lemma-H-projective-base-change, and the old projection calculation. The base change is along b_g inverse, not b_g; its first projection identifies the twist with Y equipped with b_g f pi. For common images, q_g rho_(h inverse g) = a_h r, so the proposed components do define a scheme map. The order in A_h A_l is l inverse h inverse g = (hl) inverse g, valid also for a nonabelian group. Finite intersections of translates are dense opens without faithfulness; over their intersection every factor map is an isomorphism, and the inverse product map is an open immersion equivariant as a scheme map. The new node supplies the entire independent argument, not just a clause of the parent.

Parent step 3 uses the projective-closed-model statement for its projective-space embedding of P and its Noetherianity; `def-weil-proper-morphism` explicitly supplies separatedness of f. The index is nonempty because H has an identity. I read constructions.tex Tag 01WD, lemma-segre-embedding; schemes.tex Tag 01KR, lemma-fibre-product-after-map; morphisms.tex Tag 0C4Q, lemma-projective-permanence, and Tags 01WC and 01T6. These distinguish products over X from products over the field: the former embeds in the latter using the separated diagonal. The common finite n in the new statement gives exactly N = (n+1)^|H| - 1. Iterating the binary closed immersion and Segre construction is a real independent lemma, not a two-line definition unfolding. No integrality of the ambient product is claimed.

Parent step 4 uses every relevant conclusion of the new invariant-closure statement: integral T, actual descended action, isomorphism over U and the actual generic stalk map. I read morphisms.tex Tags 056B and 01R8, including the kernel, restriction and dense-image clauses, and Tags 01RV/01RW for the generic field. U is nonempty and integral because X is integral and U is dense open. In a Noetherian P, j is quasi-compact; it is quasi-separated as an open immersion. Thus restricting its schematic image to r inverse U gives U as a scheme, not merely as a set. Reducedness is from the reduced-image theorem; irreducibility is the closure of the irreducible nonempty U. The kernel ideal is preserved because each A_h preserves U scheme-theoretically; the inverse automorphism gives equality of ideals. Quotient sheaves yield genuine automorphisms of T satisfying the group law. The common open is dense in T by construction, so its generic point maps to the generic point of X and the resulting field identification is the actual map on germs. No arbitrary field isomorphism, normalization or geometric integrality is substituted.

Parent step 5 invokes the closed-model and final surjectivity clauses of the same projective-closed-model statement, now for c:T into P. I checked the relative graph: T = T times_X X embeds in T times_S X using the separated f, and base-changing the absolute embedding gives T times_S X into P^N_X. Composing produces the required embedding over X. The new statement asserts finite projective-space embeddings over both bases, not merely a projective-bundle convention. Properness gives finite type and a closed image, and that image contains the dense U supplied in step 4. Thus the surjectivity hypothesis is met. The old parent had already replaced an impermissible citation of `lem-per-h-projective-permanence` with this closed-graph argument; this repair preserves that argument inside the new node and in the complete allocation below, and does not add the dropped node as a dependency.

I checked B1--B10, C1--C8, D1--D5 and E1--E7 against these statements and sources. New nodes have statement-only payloads, inline definitions or actual defining-node citations, precise source tags/labels, complete hypotheses and no proof dependencies. The parent has a complete short assembly and every use has a verbatim statement quote in citations.json. Its non-elementary steps are all below 2,000 characters. No new node assumes an equivariant modification or depends on this item. Definitions such as the fibre-product universal property are not cited for properness or projectivity; those results sit in the actual extracted statement. No source was replaced with an SGA route.

Edge cases: for trivial H, U=U0 and P=Y, so the action/product statement reduces correctly; the N formula gives n. Nonfaithful field or scheme actions repeat factors and do not change the argument. For n=0, N=0, including products of closed subschemes of Spec k. Empty T is permitted in the generic projective-model lemma and is excluded by its dense-open isomorphism hypothesis when X is nonempty; an empty X causes no surjectivity problem. The closure lemma cannot be applied to an empty U when X is integral. Ambient P may be reducible or nonreduced: only its reduced integral closure of U is asserted integral. Zero-dimensional X=Spec K, positive characteristic dividing |H|, nontrivial base actions and nonabelian H require no averaging by division and no normality. No new statement was found false.

All recorded searches were actually run by msearch.py, with two semantic phrasings per node, Loogle, grep and LeanSearch. I read the returned types. The results concern properness and separatedness of Proj, finite-set or linear projectivization actions, integrality of nonempty opens or normalization, topological closure, integral closures of rings, and rational maps. They do not state the complete new lemmas. Broad Loogle searches found only supporting pullback/image notation. Their exact results are retained in mathlib_searches and the sandbox search outputs/log. The item itself was also searched again, while all old searches were retained.

## Not duplicates

lem-sfb-semilinear-translated-modification-product vs lem-pc-projective-base-change: existing statement gives only stability of a supplied projective morphism under one base change; no translated product action or invariant common open.

lem-sfb-semilinear-translated-modification-product vs lem-per-h-projective-permanence: existing statement gives only a relative embedding from an already supplied absolute embedding; no finite-product embedding, Noetherianity or common-open construction. It is not cited, because the returned proof records this node as route-dropped.

lem-sfb-projective-fibre-product-closed-model vs lem-sbc-composite-fibre-local-models: existing statement gives local rings and residue fields of composed fibres; no finite projective-space embedding of global fibre products.

lem-sfb-projective-fibre-product-closed-model vs pqf-def-locnoeth: existing statement gives definition of locally Noetherian schemes and its permanence remark; no projective fibre-product or closed-model construction.

lem-sfb-projective-fibre-product-closed-model vs lem-trf-proper-base-change-coherent-conservative: existing statement gives oriented-topos coherence/conservativity under a proper cover; no projective embeddings or relative closed graph.

lem-sfb-projective-fibre-product-closed-model vs lem-trf-projective-bundle-proper: existing statement gives properness of a given projective-bundle embedding; no construction of finite projective-space embeddings of products.

lem-sfb-projective-fibre-product-closed-model vs lem-trf-fibre-component-relative-associated: existing statement gives relative associated points of flat finite-type fibres; no fibre-product embeddings or closed-model projectivity.

lem-sfb-projective-fibre-product-closed-model vs lem-sfb-semilinear-equivariant-chow-modification: existing statement gives existence of an equivariant integral birational Chow modification from a proper integral input; the new product/closed-model lemma assumes the embedded factors, has no action, and constructs no modification.

lem-sfb-projective-fibre-product-closed-model vs pqf-lem-locnoeth-lft: existing statement gives only local Noetherianity under a locally finite-type map; no projective embeddings or properness of closed models.

lem-sfb-projective-fibre-product-closed-model vs lem-chow-segre: existing statement gives binary product of projective spaces and its embedding; no fibre product over an arbitrary separated X, relative closed-model embedding or dense-open surjectivity criterion.

lem-sfb-projective-fibre-product-closed-model vs lem-per-equivariant-projective-envelope: existing statement gives constructs a new compactification of a quasi-projective scheme with a linear action over a fixed affine base; no prescribed fibre product or prescribed invariant closure inside a Noetherian ambient scheme with semilinear base action.

lem-sfb-projective-fibre-product-closed-model vs lem-per-h-projective-permanence: existing statement gives only a relative embedding from an already supplied absolute embedding; no finite-product embedding, Noetherianity or common-open construction. It is not cited, because the returned proof records this node as route-dropped.

lem-sfb-projective-fibre-product-closed-model vs lem-chow-closed-model: existing statement gives closure of a supplied immersion into one projective space over an affine base; no invariant action, prescribed isomorphism open, or relative product/closed-graph construction.

lem-sfb-projective-fibre-product-closed-model vs lem-weil-pbc-finite-type-over-noetherian: existing statement gives only Noetherianity from finite type over a Noetherian base; no finite-space embedding or proper/relative projective model.

lem-sfb-projective-fibre-product-closed-model vs lem-weil-pbc-fibre-product-change-of-base-closed-immersion: existing statement gives only the binary closed immersion from changing the base from X to S; no finite Segre embedding, arbitrary closed model, relative projectivity or surjectivity.

lem-sfb-projective-fibre-product-closed-model vs lem-weil-pbc-finite-algebra-noetherian: existing statement gives Noetherianity of a module-finite algebra, not geometric finite-product embeddings.

lem-sfb-projective-fibre-product-closed-model vs lem-weil-pbc-finite-separable-base-refinement: existing statement gives changes a given smooth projective scheme from k to a finite separable extension; no finite-product or closed-model construction.

lem-sfb-projective-fibre-product-closed-model vs lem-weil-pbc-graded-finiteness-cohomology: existing statement gives finite generation of a graded cohomology module; no finite projective-space embeddings of fibre products.

lem-sfb-projective-fibre-product-closed-model vs lem-kun-projective-implies-proper: existing statement gives only properness from a supplied projective embedding; the new node constructs embeddings over S and X and handles finite products and closed models.

lem-sfb-projective-fibre-product-closed-model vs lem-pur-affine-line-support-geometry: existing statement gives Noetherianity/finite type for an affine line, its zero section and complement; no projective fibre product or closed model.

lem-sfb-invariant-integral-open-schematic-closure vs lem-sbc-geometrically-reduced-dominant-descent: existing statement gives geometric reducedness descends along a schematically dominant morphism; no invariant closure, action descent or generic stalk isomorphism.

lem-sfb-invariant-integral-open-schematic-closure vs lem-nagata-one-affine-subring-extension: existing statement gives extension of finite affine gluing models in a directed approximation system; no group-stable schematic closure with isomorphism over a dense integral open.

lem-sfb-invariant-integral-open-schematic-closure vs lem-trf-reduced-scheme-image: existing statement gives identifies a reduced source image with the reduced closure; does not give an induced group action, restriction to the common isomorphism open or its actual generic stalk isomorphism.

lem-sfb-invariant-integral-open-schematic-closure vs lem-trf-strict-transform-sheaf-kernel: existing statement gives kernel for a module strict transform under a blowup; no invariant integral open closure, descended scheme automorphisms or generic fields.

lem-sfb-invariant-integral-open-schematic-closure vs def-sfb-dominant-function-field-map: existing statement gives defines the canonical field map for a dominant morphism already supplied; neither constructs the integral closure model nor proves that its map is an isomorphism.

lem-sfb-invariant-integral-open-schematic-closure vs def-sc-rational-functions: existing statement gives defines rational functions on a scheme; no invariant schematic closure or descended action.

lem-sfb-invariant-integral-open-schematic-closure vs lem-sc-integral-function-field-affine-fraction: existing statement gives describes the field of fractions of one integral scheme; no comparison isomorphism from an invariant open closure or descended action.

lem-sfb-invariant-integral-open-schematic-closure vs lem-sc-rational-functions-generic-stalks: existing statement gives identifies rational functions of one scheme with its generic stalks; no invariant closure/action or isomorphism induced by q.

lem-sfb-invariant-integral-open-schematic-closure vs lem-sc-picard-locus-closed-valuation-criterion: existing statement gives closedness of an immersion satisfying a valuative extension property; no invariant closure or generic stalk comparison.

lem-sfb-invariant-integral-open-schematic-closure vs lem-per-equivariant-projective-envelope: existing statement gives constructs a new compactification of a quasi-projective scheme with a linear action over a fixed affine base; no prescribed fibre product or prescribed invariant closure inside a Noetherian ambient scheme with semilinear base action.

lem-sfb-invariant-integral-open-schematic-closure vs lem-weil-pbc-scheme-image-qc-kernel: existing statement gives kernel description and factorization of a quasi-compact image; does not prove integrality, action descent or generic stalk isomorphism of this closure.

lem-sfb-invariant-integral-open-schematic-closure vs lem-weil-pbc-spec-domain-stalks-function-field: existing statement gives stalks/localizations of a single affine spectrum; no invariant closure or action descent.

lem-sfb-invariant-integral-open-schematic-closure vs lem-weil-pbc-closed-image-limit-system: existing statement gives descending a closed subscheme through a cofiltered affine system; no invariant integral isomorphism open or group action.

lem-sfb-invariant-integral-open-schematic-closure vs lem-weil-pbc-scheme-theoretic-image-proper: existing statement gives properness of an image of a proper source; U here is generally not proper, and that node does not give invariant closure/action descent or a generic field isomorphism.

lem-sfb-invariant-integral-open-schematic-closure vs lem-sc-integral-scheme-stalks-in-function-field: existing statement gives embeds stalks of one integral scheme in its field of fractions; no closure construction, action or comparison between two schemes.

## Complete returned argument retained for the new workers

The paragraphs below retain the complete returned nine-step proof, including its original dependency names and source places. They are work guidance for the extracted nodes, not proofs attached to those statement-only nodes. The allocation table above states exactly where every part goes; no paragraph was discarded. The generic arguments in the newly generalized projective-model statement are the very same separated-diagonal, Segre and graph arguments with the factor index renamed I. They do not require an action or integrality.

### Returned step 1

Put $S=\operatorname{Spec}k$ and write $f:X\to S$. A field is Noetherian: an ideal containing a nonzero element contains $1$, so its only ideals are $(0)$ and $(1)$. Thus $S$ is affine Noetherian. Since $X$ is integral it is reduced. Apply [lem-fin-noetherian-chow-modification] to obtain $\pi:Y\to X$, proper and an isomorphism over a dense open $U_0\subset X$, with $Y$ projective over $S$. Here projective means a closed immersion $i:Y\hookrightarrow\mathbf P^n_S$ for some finite $n$, as in [def-pc-projective-morphism]. Also $X$ is Noetherian by [lem-weil-pbc-finite-type-over-noetherian].

Uses: `def-weil-field`, `pqf-def-locnoeth`, `def-pc-integral-scheme`, `lem-fin-noetherian-chow-modification`, `def-pc-projective-morphism`, `lem-weil-pbc-finite-type-over-noetherian`.

Source: literature/stacks-project/coherent.tex; Tag 0200, lemma-chow-Noetherian, specialized to a proper scheme over a field; the proper-source immersion is closed as in the existing modification node.

### Returned step 2

Let $a_g:X\to X$ and $b_g:S\to S$ denote the compatible left scheme actions, so $a_ga_h=a_{gh}$, $b_gb_h=b_{gh}$ and $fa_g=b_gf$ (the scheme action associated to a field action uses its inverse under $\operatorname{Spec}$). For each $g\in H$, take a copy $Y_g$ of the underlying scheme $Y$, with $q_g=a_g\pi:Y_g\to X$ and structure morphism $p_g=b_gf\pi=fq_g$. It is projective over $S$: $Y_g$ is the base change of $Y\to S$ along $b_g^{-1}$, with underlying first projection an isomorphism. Base change $i$ and use [lemma-nagata-projective-space-base-change-pullback] and [lem-weil-pbc-closed-immersion-base-change] to embed it into $\mathbf P^n_S$. This argument does not require $a_g$ or $b_g$ to be the identity. Set $U=\bigcap_{g\in H}a_g(U_0)$. Each translate is dense open; a finite intersection of dense opens is dense open, because intersecting any nonempty open successively with them stays nonempty. Left multiplication permutes the translates, so $a_h(U)=U$.

Uses: `def-pc-fibre-product`, `lemma-nagata-projective-space-base-change-pullback`, `lem-weil-pbc-closed-immersion-base-change`.

Source: literature/stacks-project/morphisms.tex; Tag 01WF, lemma-H-projective-base-change; agent-explicit semilinear twists and invariant open.

### Returned step 3

Form $P=\prod_{g\in H,X}Y_g$, with common morphism $r:P\to X$ and projections $\rho_g:P\to Y$. This is a finite nonempty fibre product, since a group contains its identity. It has a closed immersion into $\prod_{g\in H,S}Y_g$: for two factors this is [lem-weil-pbc-fibre-product-change-of-base-closed-immersion], applied to the separated map $f$; for further factors repeat that lemma and compose with the product of the preceding closed immersion and the identity. Products and composites of closed immersions are supplied by [lem-weil-pbc-closed-immersion-products]. The same node puts $\prod_SY_g$ as a closed subscheme of $\prod_{g\in H}\mathbf P^n_S$. Iterating [lem-chow-segre] gives a closed immersion of this product into $\mathbf P^{(n+1)^{|H|}-1}_S$. Composing gives a finite projective-space embedding of $P$ over $S$. For $|H|=1$, this is just the given embedding of $Y$.

Uses: `def-pc-fibre-product`, `def-weil-proper-morphism`, `lem-weil-pbc-fibre-product-change-of-base-closed-immersion`, `lem-weil-pbc-closed-immersion-products`, `lem-chow-segre`, `def-kun-projective`.

Source: literature/stacks-project/constructions.tex; Tag 01WD, lemma-segre-embedding; morphisms.tex Tags 01W8 and 01WF, with the separated-diagonal fibre-product construction.

### Returned step 4

For $h\in H$ define $A_h:P\to P$ by $\rho_g A_h=\rho_{h^{-1}g}$ as morphisms to the underlying copy of $Y$. These components have a common image in $X$, since $q_g\rho_{h^{-1}g}=a_g\pi\rho_{h^{-1}g}=a_ha_{h^{-1}g}\pi\rho_{h^{-1}g}=a_hr$. The fibre-product universal property therefore constructs $A_h$ and gives $rA_h=a_hr$. Its structure map to $S$ is consequently $b_hfr$, proving the required semilinearity. The $g$-component of $A_hA_l$ is $\rho_{l^{-1}h^{-1}g}=\rho_{(hl)^{-1}g}$, so uniqueness in the universal property gives $A_hA_l=A_{hl}$ and $A_1=1$. In particular each $A_h$ is an automorphism, with inverse $A_{h^{-1}}$. These are identities of scheme morphisms specified by their projections, not just formulas on geometric points.

Uses: `def-pc-fibre-product`.

Source: literature/stacks-project/coherent.tex; Agent expansion of finite-translate averaging after Tag 0200; de Jong (1997), §2.10, printed p.605, refers to this averaging.

### Returned step 5

Over $U$, every $q_g$ is an isomorphism: $a_g^{-1}(U)\subset U_0$, and its restriction is $\pi$ over that open followed by the isomorphism $a_g:a_g^{-1}(U)\to U$. Thus the fibre product $P\times_XU$ is canonically $U$, with its $g$-projection the inverse of $q_g$ over $U$. This is an isomorphism by the universal property, since each factor is $U\to U$. It identifies $U$ with an open subscheme $j:U\hookrightarrow P$. The equivariance of $r$ and the uniqueness of this inverse imply $A_hj=j(a_h|_U)$, using the already proved invariance of $U$.

Uses: `def-pc-fibre-product`, `def-weil-open-immersion`.

Source: literature/stacks-project/coherent.tex; Agent finite-product specialization of the common isomorphism open in Tag 0200.

### Returned step 6

Let $T=\operatorname{SIm}(j)\subset P$. The open $U\subset X$ is integral: it is nonempty and its nonempty affine opens are affine opens of the integral scheme $X$. By [lem-trf-reduced-scheme-image], $T$ is the reduced induced closed scheme on $\overline{j(U)}$. This support is nonempty and irreducible: any two nonempty relative opens meet $j(U)$ and hence meet each other, since $U$ is irreducible. Thus $T$ is integral by [def-pc-integral-scheme]. The scheme $P$ is Noetherian: its projective structure morphism is proper by [lem-kun-projective-implies-proper], hence finite type by [def-weil-proper-morphism], so [lem-weil-pbc-finite-type-over-noetherian] applies over $S$. Every open of a Noetherian scheme is quasi-compact by [lem-weil-pbc-noetherian-open-subscheme-noetherian], so $j$ is quasi-compact (apply this also to $U$ intersected with each affine open of $P$) and quasi-separated (it is an open immersion). Apply [lemma-nagata-scheme-image-restrict-open] to the open $P\times_XU$: the restricted morphism $j$ is its identity, so $T\times_XU=U$ as schemes.

Uses: `def-nagata-scheme-theoretic-image`, `lem-trf-reduced-scheme-image`, `def-pc-integral-scheme`, `lem-kun-projective-implies-proper`, `def-weil-proper-morphism`, `lem-weil-pbc-finite-type-over-noetherian`, `lem-weil-pbc-noetherian-open-subscheme-noetherian`, `lemma-nagata-scheme-image-restrict-open`.

Source: literature/stacks-project/morphisms.tex; Tags 056B (lemma-scheme-theoretic-image-reduced), 01R8 (lemma-quasi-compact-scheme-theoretic-image), 01WC (lemma-locally-projective-proper), 01T6 (lemma-finite-type-noetherian).

### Returned step 7

The action on $P$ restricts scheme-theoretically to $T$. Indeed [lem-weil-pbc-scheme-image-qc-kernel] identifies its defining ideal on every affine open with the functions restricting to zero on $U$. Since $A_h$ carries $U$ isomorphically to $U$, pullback by $A_h$ carries this ideal to itself; the reverse inclusion follows by $A_{h^{-1}}$. An automorphism preserving a defining ideal induces an automorphism on the quotient structure sheaf and on the closed subscheme. These induced automorphisms satisfy the group law because the ambient ones do. Restrict $rA_h=a_hr$ and $frA_h=b_hfr$ to $T$. Thus $q=r|_T$ and the structure map of $T$ are compatible with the same $H$-action.

Uses: `lem-weil-pbc-scheme-image-qc-kernel`, `def-weil-closed-immersion`.

Source: literature/stacks-project/morphisms.tex; Tag 01R8, lemma-quasi-compact-scheme-theoretic-image, kernel description; agent-explicit invariant quotient ideals.

### Returned step 8

Since $T\hookrightarrow P$ is closed, compose it with the projective-space embedding in step 3, using [lem-weil-pbc-closed-immersion-comp]. Thus $T\to S$ is projective in the finite-projective-space convention: there is a closed immersion $e:T\hookrightarrow\mathbf P^N_S$ over $S$, $N=(n+1)^{|H|}-1$. The map $f:X\to S$ is separated by [def-weil-proper-morphism]. Apply [lem-weil-pbc-fibre-product-change-of-base-closed-immersion] to $q:T\to X$, $\mathrm{id}:X\to X$ and $h=f$: the graph $\Gamma_q=(1,q):T=T\times_XX\to T\times_SX$ is a closed immersion. Base change of $e$ along $f$ gives a closed immersion $e\times_S1:T\times_SX\to\mathbf P^N_S\times_SX$ by [lem-weil-pbc-closed-immersion-base-change], and $\mathbf P^N_S\times_SX\cong\mathbf P^N_X$ over $X$ by [lemma-nagata-projective-space-base-change-pullback]. The composite $T\hookrightarrow\mathbf P^N_X$ is a closed immersion by [lem-weil-pbc-closed-immersion-comp], and followed by the projection to $X$ it is the second component of $\Gamma_q$, namely $q$. Hence $q$ is projective [def-kun-projective]. By [lem-kun-projective-implies-proper], both structure morphisms are proper and in particular of finite type. The image $q(T)$ is closed, since proper means universally closed, and contains $U$ by step 6. Since $U$ is dense, this closed image is all of $X$, so $q$ is surjective [def-weil-surjective-morphism]. Step 6 already proves that $q$ is an isomorphism over the dense open $U$.

Uses: `lem-weil-pbc-closed-immersion-comp`, `def-kun-projective`, `def-weil-proper-morphism`, `lem-weil-pbc-fibre-product-change-of-base-closed-immersion`, `lem-weil-pbc-closed-immersion-base-change`, `lemma-nagata-projective-space-base-change-pullback`, `lem-kun-projective-implies-proper`, `def-weil-surjective-morphism`.

Source: literature/stacks-project/morphisms.tex; Tags 0C4Q, lemma-projective-permanence (finite-space closed-graph version), and 01WC, lemma-locally-projective-proper.

### Returned step 9

For an integral scheme its function field is the stalk at its generic point, as in [def-sc-function-field]. A dense open of an integral scheme contains that generic point: otherwise its closed complement would contain the generic point and hence the whole scheme. The open $U$ is dense in both $T$ and $X$, by the closure construction and its original choice. Therefore the isomorphism $q^{-1}(U)\simeq U$ identifies their generic local rings, and the resulting isomorphism $k(X)\simeq k(T)$ is exactly the one induced by $q$. These are fields by [lem-sc-integral-function-field-affine-fraction]. This proves the last clause without any normality or geometric-integrality assumption.

Uses: `def-sc-function-field`, `lem-sc-integral-function-field-affine-fraction`.

Source: literature/stacks-project/morphisms.tex; Tag 01RW, definition-function-field, and the generic stalk of the isomorphism open.

## Validation

The first dry run was executed before any repair and exited because report.md was absent. After repairing the split, deliver.py --no-push will run the server preflight, check_dag and review_split; I will repair any reported failures and push only after a completed successful dry run. Only this item's sandbox has been written.
