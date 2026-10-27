# Worker report: det-prop-scalar-six-ctf

## Files written

- dag/nodes/sec-six-functors-basics/det-prop-scalar-six-ctf.json: split, unchanged statement and statement dependencies, six assembly steps (2666 text characters).
- dag/nodes/sec-six-functors-basics/lem-sfb-perfect-scalar-change-model.json: statement, unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-admissible-scalar-model-cohomology.json: statement, unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-stratum-perfect-uniform-bounds.json: statement, unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-ctf-retract-etale-images.json: statement, unsplit, no Mathlib match.
- citations.json: exact statement quotations for every step/use pair. Searches and raw hits are in searches.jsonl and the named search output files.

## Attachments

None. The project search for the exact blueprint tag found no declaration. Concept searches in WeilConjectures found the ModuleObject/ChangeOfCoefficients comparison constructions and finite-coefficient restriction/stability modules; reading ChangeOfCoefficients showed no theorem asserting the item's generation, all-coefficient local models, and preservation. No Mathlib declaration is being offered as a project attachment.

## Wanted sources

None. The current blueprint statement, proof, unit and chapter are available. Source citations below point to the latest blueprint, not an old snapshot. The supporting Stacks texts are available locally.

## Repair order and original defects

The released stage-1 repair note dated 2026-10-22 explicitly reopens the previously reviewed split, requires at least four statement-only nodes, unchanged statement, preservation of all old arguments, and an assembly of at most 3000 characters. This delivery supplies four. They are interfaces for scalar-model calculation, scalar-realization cohomology, global uniform bounds, and etale cohomology images of retracts. None repeats all three clauses or simply renames a clause of the item.

No statement dispute arose. The latest blueprint's assertions Dctf=Dbc and derived-completeness language are not needed here: the already reviewed route uses only Dctf contained in Dbc, and proves bounds for ordinary uncompleted coefficient complexes. I retained that route. The statement, Lean record, import flags, blueprint fields and prior review history were preserved. The unit's key node is sk-prop-scalar-six, not this detail node; its realized fields were not changed.

## Argument allocation

Old steps 1–3 remain assembly step 1, using the existing generation nodes, including both finite-discrete ring identifications. The finite-generated closure is finitary; a finite union of finite construction histories gives a finite history, so no transfinite generation assertion is used.

Old step 4 is the exact model isomorphism and flat/K-flat assertions of lem-sfb-perfect-scalar-change-model, applied by assembly step 2. Its future proof is the original retract-of-finite-free argument: choose generators, split the surjection by projectivity, tensor both splitting maps, obtain sheaf flatness from the direct summand of a finite-sum exact sequence, use bounded-flat K-flatness, commute restriction, then use tensor associativity. Scalar projectivity alone is already covered by Mathlib.Projective.tensorProduct, but that is not the coefficient-sheaf derived statement.

Old step 5 and the finite-ring convention in step 1 are lem-sfb-admissible-scalar-model-cohomology. Finite coefficients use exact constant sheafification, fields use split short exact sequences, and integral coefficients use the flat constant-to-completed map of det-prop-integral-criterion-constant-coefficients(1). DVR ideals are principal, hence the integral scalar ring is Noetherian; finite rings and fields are Noetherian directly. Cycles are finite submodules, their cohomology quotients finite, then finitely presented. The exact-functor cohomology formula is retained as an explicit isomorphism.

Old steps 6–9 and the geometric portion of step 10 are lem-sfb-stratum-perfect-uniform-bounds. Its future proof retains Noetherianity, retrocompactness, local finite type, quasi-separatedness and the finite affine cover; the finite affine pro-etale refinement; exact Cartesian coefficient restriction; a common degree interval over a finite cover; finitely presented scalar cohomology and cohomology descent; flat terms, bounded K-flatness and ringed-topos tensor pullback; and Tor-bound descent. It also retains the finite-type and separated-composition checks needed to apply standing-scheme theorems. It gives the specified finite-cover and tensor witnesses, not just membership in Dctf. Assembly step 3 applies direct-images(2) only after these geometric hypotheses hold, and uses precisely the item's module a_!=i_*u_! convention.

Old step 11 is lem-sfb-finite-ctf-retract-etale-images. It retains C_0 from the finite-Tor comparison, exact fully faithful inverse image lifting each cohomology idempotent, constructibility of its etale image, its pullback being H^q(J), pro-etale constructible comparison, unchanged cohomology bounds and unchanged Tor interval. The node does not assert a derived isomorphism merely on the basis of per-degree identifications. Assembly step 4 uses its retract conclusion and the existing finite Db_c triangulation.

Old step 12 remains assembly steps 4–5. The kernel of 1-ir is the image of i when ri=1: (1-ir)i=0 and every u killed by 1-ir satisfies u=i(ru), uniquely since ri=1. Thus the ambient kernel/cokernel assertions suffice for constructible cohomology of an arbitrary derived retract. Cohomology zero outside the old finite interval stays zero, and tensor preserves the retraction. Intersecting with the finite-Tor thick class and the cited Db_c triangulated classes gives thickness at every coefficient stage. This short algebraic argument was kept as a step instead of inventing a new elementary node; the general weak-Serre bounded-thick node also exists.

Old step 13 is assembly step 6, unchanged in substance: exact uncompleted scalar tensor, images of a_! generators via pullback(2), finitary induction, then transitivity via pullback(3) for composites. Every one of the original arguments is transcribed verbatim below as takeover material; no proof was placed in a new unsplit node's statement or proof fields.

## Not duplicates

lem-sfb-perfect-scalar-change-model vs det-prop-scalar-six-pullback: that node commutes geometric functors with scalar change, but does not identify the scalar projective complexes or assert their flat/K-flat models.
lem-sfb-perfect-scalar-change-model vs lem-zl-condensed-wcontractible-projective-calculus: that node concerns perfect/dualizable realization on a w-contractible affine and a single coefficient ring, not arbitrary coefficient change on a specified pro-etale covering.
lem-sfb-perfect-scalar-change-model vs lem-sfb-scalar-perfect-dual-realization: that node identifies scalar duals/internal Hom and exact Hom from finite-projective terms, not derived change-of-coefficient models.
lem-sfb-perfect-scalar-change-model vs lem-pe-restricted-kflat-tensor-identification: that node identifies restricted scalar-first and scalar-last resolution tensors, not finite-projective scalar model base change.
lem-sfb-perfect-scalar-change-model vs lem-weil-pbc-idempotent-endomorphism-image-base-change: that node is an ordinary ring-module idempotent theorem; it supplies one algebraic subfact, not the sheaf and derived assertions.
lem-sfb-admissible-scalar-model-cohomology vs lem-sfb-local-integral-perfect-model-cohomology: the latter is integral-only and includes a geometric pullback from an ambient X; the new node uniformly treats finite, integral and field coefficients and exact realization of every scalar module, with their canonical finite ring comparison.
lem-sfb-admissible-scalar-model-cohomology vs lem-zl-flat-condensed-scalar-realization: the latter assumes flatness on extremally disconnected sets for a general condensed ring and concludes exactness; it does not establish the coefficient-case hypotheses or finite presentation of scalar cohomology.
lem-sfb-admissible-scalar-model-cohomology vs det-prop-integral-criterion-constant-coefficients: that node supplies integral completion flatness and derived-complete comparisons only, not all-coefficient exact realization and perfect cohomology.
lem-sfb-admissible-scalar-model-cohomology vs lem-pe-finite-discrete-scalar-constant-models: that node compares a normalized fixed-module encoding for finite coefficients, not exactness on every scalar module and integral/field perfect cohomology.
lem-sfb-stratum-perfect-uniform-bounds vs lem-sfb-finite-scalar-perfect-refinement: that node supplies finite models and retraction packages only, expressly without scalar exactness; it does not give constructibility/cohomology and Tor descent or standing-stratum geometry.
lem-sfb-stratum-perfect-uniform-bounds vs lem-sfb-local-model-cohomology-descent: that node assumes a finite covering, a common interval, exact scalar realization and finitely presented cohomology; the new node supplies them from local perfectness and proves the Tor and geometric assertions as well.
lem-sfb-stratum-perfect-uniform-bounds vs lem-sfb-local-model-tor-bound-descent: that node assumes bounded flat models on a specified finite covering; the new node constructs uniform scalar models and gives constructible cohomology and standing-stratum geometry.
lem-sfb-stratum-perfect-uniform-bounds vs lem-dl-a1-locally-closed-stratum-separated-finite-type: that node constructs a reduced induced stratum inside a chosen open and proves geometric facts, not arbitrary given immersions with coefficient complexes, refinement and uniform bounds.
lem-sfb-finite-ctf-retract-etale-images vs det-brown-hypotheses-small: that node gives thickness and size for ell-primary admissible coefficients; the new node applies to any finite commutative ring and specifies the unique etale cohomology idempotents and their image/pullback identifications with unchanged intervals.
lem-sfb-finite-ctf-retract-etale-images vs lem-sfb-weak-serre-bounded-thick: that generic weak-Serre theorem assumes ambient kernel/cokernel/extension closure and identifies a complementary kernel. It does not construct an etale model or its unique lifted cohomology idempotents for arbitrary finite coefficients.
lem-sfb-finite-ctf-retract-etale-images vs det-pe-finite-tor-comparison-noetherian: that node supplies a comparison equivalence and Tor equivalence for an etale input, not the images of an arbitrary ambient retract.

Whole-DAG searches were made for locally perfect, scalar projective/change, scalar cohomology, retracts of constructible/finite-Tor complexes, uniform intervals, and corresponding source labels. Blueprint searches (all chapters) included locally perfect, local models, scalar model, scalar realization, projective scalar, cohomology idempotent, thick, finite Tor amplitude, uniform bounds and locally closed immersion. Relevant hits above were opened and compared. No source Stacks tag is newly assigned to a new node: these four extracted arguments have the blueprint proof as their source; the precise supporting tags checked are listed below.

## Review by N5

I read the latest det-prop-scalar-six-ctf statement and proof and sk-prop-scalar-six unit, the chapter record, and the current live thirteen-step proof. For the scalar-model node I read the displayed calculation in source (2), the projective definition, bounded-flat K-flat lemma and pullback(1). For admissible scalar cohomology I read source (2), Stacks sites-modules.tex Tag 093J, lemma-constant-exact, Tag 093M, lemma-completion-flat, and algebra.tex Tag 00IK, lemma-Noetherian-basic. I checked the existing integral flat-completion statement as well as its finite quotient coefficient convention. For the stratum node I read source (2), and the statements of finite-affine-proetale-refinement, local-model-cohomology-descent, local-model-tor-bound-descent and Cartesian coefficients: their finite-cover, exactness, finite-presentation and flat-term hypotheses are precisely what is retained in this node. The geometry follows the already reviewed immersion route, with the original source support 01T5 (morphisms lemma-immersion-locally-finite-type) and 01T6 (lemma-finite-type-noetherian). For the retract node I read source (3) and the statements of finite-tor-comparison-noetherian, classical-sheaves-modules, constructible-serre and pro-etale constructible comparison. Finite B is Noetherian and the assumed X is qcqs, so the comparison hypotheses are present; exact full faithfulness, not full faithfulness alone, gives both the idempotent lift and its image identification.

For assembly step 1 I opened each of its seven cited node statements. Finite-type-over-Noetherian applies to Spec k (a field has only two ideals), the ring-identification lemmas identify the actual coefficient ring, and all three generation statements give their claimed generators. Lisse means pro-etale locally free in the heart statement; finite free is finite projective. Step 2 cites the explicit model isomorphism, not an unsupported assertion about perfectness. Step 3 cites exact realization and the full finite-cover/Tor lemma; direct-images(2) requires a separated finite-type morphism between standing schemes, now supplied before application. Its a_! is exactly the module composite of the unchanged statement. Step 4 cites the new finite-retract lemma, finite-coefficient triangulation, and the Tor closure explicitly written in the Tor definition's well-definedness clause. Step 5 uses the actual ambient kernel/cokernel wording of integral-heart(2) and coefficient-heart(1); the complementary-idempotent calculation above supplies retract closure, and the other two cited statements give triangulation. Step 6 uses derived-change-of-rings(2) for exactness and the actual ordinary uncompleted locally closed comparison in pullback(2); the stratum geometry was already proved. Pullback(3) states precisely the transitivity needed for composites. No cited node's proof was used as its interface. citations.json contains exact statement witnesses for all 20 step/use pairs.

I tested the empty scheme/empty stratum, the identity immersion, a point, a zero coefficient ring, a zero model, and a shifted one-term free complex. Empty strata admit the empty covering and [0,0]. For nonflat scalar change I tested Z/ell^2 -> F_ell on the bounded projective two-term model [Z/ell^2 --ell--> Z/ell^2]; its changed model has zero differential and remains bounded. F_ell in degree zero over Z/ell^2 does not meet the projective-model/finite-Tor hypotheses, so it is not incorrectly admitted. Integral torsion cohomology (the cone of multiplication by a uniformizer) is allowed and finitely presented; no freeness of cohomology was asserted. A retract equal to zero or all of C gives idempotents 0 or 1 and the stated same-interval bounds. In the complementary-idempotent calculation ri=1 is the orientation used throughout. I repaired a nonexistent separated-definition reference by using def-weil-proper-morphism, which actually defines separatedness, and replaced a classicality definition used for the comparison map by the site-comparison definition. New statements contain no proof sketches, their proof fields/dependencies are empty, their blueprint places specify the original arguments, and no new non-elementary assembly step is longer than 2000 characters. All searches recorded were run through msearch.py; two natural-language formulations were read for each new node. Results were projective tensor/flatness, module finite presentation, scheme covers and etale algebra statements, not these sheaf-derived assertions. There are zero Mathlib leaves.

Generic external tools retained from the original route are finite-type-over-Noetherian, the finite condensed/constant-ring identifications, finite pro-etale Db_c triangulation, and exact derived change of rings. The coefficient-generation and direct-image/heart nodes are precisely the original blueprint route nodes; no substitute unit route is introduced. The four new nodes share this item's unit. No SGA source was used. No Lean was written and no compilation or build tool was run.

## What remains

The four new nodes intentionally await their own stage-1 splits, as the released repair order requires. No part of this item's assembly is unfinished. Dry run and delivery results are recorded after running the authorized tools.

## Preserved original proof and citations

The following is the live pre-repair proof verbatim, retained as takeover material for future workers. Its argument allocation is specified above, including those parts that reuse existing nodes rather than being duplicated.

### Original step 1

Finite-coefficient generators. The standing $X$ is Noetherian:
apply [lem-weil-pbc-finite-type-over-noetherian] to
$X\to\operatorname{Spec}k$; the spectrum of a field is Noetherian.
For every finite admissible ring $A$, apply
[det-sf-flat-model-generation](3). It states that $\Dctf(X,A)$ is the
subcategory generated by $a_!L$ under shifts, extensions and direct summands,
where $L$ is locally constant with finite projective $A$-module stalks.
Such $L$ is locally the constant sheaf of that finite projective module,
which is a bounded finite projective scalar complex concentrated in degree
zero. These are the locally perfect generators required in (1). The closure
is generated by finitary operations, so every object has a finite
construction with these operations. This argument covers arbitrary finite
commutative $A$, not only the $\ell$-primary case.
The current generation statement specifies ordinary constant-$A$ module sheaves, bounded constructible cohomology and finite Tor amplitude. For finite discrete $A$ the coefficient ring $A_X=p_X^*\underline A$ is the constant sheaf of rings $A$ on $X_{\mathrm{proét}}$: [lem-weil-pbc-finite-discrete-condensed-ring-constant] identifies $\underline A$ with the sheafified constant ring on profinite sets, and [lem-weil-pbc-finite-discrete-scheme-ring-constant] carries this monoidal isomorphism to the pulled-back ring on $X_{\mathrm{proét}}$ (and on every $W\in X_{\mathrm{proét}}$); module categories are transported along it. This identification is also the one used in steps 5, 8 and 9 for finite coefficients. These are the finite-coefficient categories used here, and its $a_!=g_*j_!$ convention agrees with the statement above.

Citations: lem-weil-pbc-finite-type-over-noetherian, det-sf-flat-model-generation, lem-weil-pbc-finite-discrete-condensed-ring-constant, lem-weil-pbc-finite-discrete-scheme-ring-constant

### Original step 2

Integral generators. If $K\in\Dctf(X,\mathcal O_E)$, then
$K\in\Dbc(X,\mathcal O_E)$ by
[det-def-sfb-constructible-tor-amplitude]. Apply
[det-lem-int-tensor-shriek](2): $K$ is a finite iterated extension of $a_!M$
whose restrictions are scalar extensions of bounded finite free
$\mathcal O_E$-complexes. These are among the generators of (1).
This uses only the inclusion $\Dctf\subseteq\Dbc$, not an identification
with a category defined using a tower or derived completeness.

Citations: det-def-sfb-constructible-tor-amplitude, det-lem-int-tensor-shriek

### Original step 3

Field generators. For $\Lambda=E$ or $\Qlb$, an input in $\Dctf$
is again bounded constructible. By
[det-cor-coefficient-heart-ii-generation] it is obtained by finitely many
cones and shifts from $a_!L$ with $L$ lisse. By
[sk-lem-coefficient-heart] lisse means pro-étale locally finite free, hence
locally perfect with its model in degree zero. A cone is an extension after
rotating its distinguished triangle. This proves (1) at the field stages
(including $\mathbf Q_\ell$), and step 2 includes $\mathbf Z_\ell$
by taking $E=\mathbf Q_\ell$.

Citations: det-def-sfb-constructible-tor-amplitude, det-cor-coefficient-heart-ii-generation, sk-lem-coefficient-heart

### Original step 4

Change the local projective models. Write $R=\Lambda(*)$ and
$R'=\Lambda'(*)$. Choose a cover $W\to S$ with
$P|_W\simeq\Lambda_W\otimes_R P_0^\bullet$, $P_0^\bullet$ bounded finite
projective. Each $P_0^q$ is a retract of a finite free $R$-module: take a
surjection $R^m\to P_0^q$ from finitely many generators and split it by
projectivity [def-weil-pbc-projective-module]. Tensoring the two splitting
maps preserves their composite identity. Thus $\Lambda_W\otimes_R P_0^q$
is a retract of $\Lambda_W^m$. Tensoring any short exact sequence with
this retract gives a direct summand of its finite direct-sum sequence, so
it is exact; this is flatness [def-pc-flat-sheaf-modules]. The same
splitting exhibits $R'\otimes_R P_0^q$ as a retract of $(R')^m$, hence
as a finite projective $R'$-module. The bounded flat complex is K-flat by
[lem-pc-bounded-above-flat-kflat-site]. By
[sk-def-sfb-derived-extension-of-scalars] its derived change of coefficients
is computed termwise. Restriction commutes with this change by
[det-prop-scalar-six-pullback](1), and ordinary tensor associativity gives
$$
P_{\Lambda'}|_W\simeq
\Lambda'_W\otimes_{\Lambda_W}(\Lambda_W\otimes_R P_0^\bullet)
\simeq\Lambda'_W\otimes_{R'}(R'\otimes_R P_0^\bullet).
$$
This proves local perfectness in (2), even when $A\to B$ is not flat.

Citations: def-weil-pbc-projective-module, def-pc-flat-sheaf-modules, lem-pc-bounded-above-flat-kflat-site, sk-def-sfb-derived-extension-of-scalars, det-prop-scalar-six-pullback

### Original step 5

Cohomology of a local model. For any coefficient stage $\Gamma$ in
the list, put $R=\Gamma(*)$. The functor $M\mapsto\Gamma_W\otimes_R M$
is exact. For finite $R$ it is the constant-sheaf functor; exactness follows
by sheafifying the sectionwise exact constant-presheaf sequence, using
[lem-weil-pbc-sheafification-exact]. If $R$ is a field, each short exact
sequence of $R$-modules splits and its image under this additive functor
still splits. For $R=\mathcal O_F$, exactness follows from the same
constant-sheaf exactness followed by the flat ring map of
[det-prop-integral-criterion-constant-coefficients](1), which applies on
every scheme $W$. Consequently, for a bounded finite projective scalar
complex $Q_0^\bullet$,
$$H^q(\Gamma_W\otimes_R Q_0^\bullet)
=\Gamma_W\otimes_R H^q(Q_0^\bullet).$$
The ring $R$ is Noetherian: for finite rings and fields this follows directly
from their ideals, and for $\mathcal O_F$ it follows from the principal-ideal
assertion in [lem-weil-l-adic-extension-integers-dvr](2). Its ideals are
finitely generated. Thus the cycles are finite by
[lem-weil-pbc-noetherian-submodule-finite], their quotients $H^q(Q_0^\bullet)$
are finite, and these modules are finitely presented by
[lem-sc-noetherian-finite-module-finite-presentation]. The displayed
cohomology therefore has finite constant local models.

Citations: lem-weil-pbc-sheafification-exact, det-prop-integral-criterion-constant-coefficients, lem-weil-l-adic-extension-integers-dvr, lem-weil-pbc-noetherian-submodule-finite, lem-sc-noetherian-finite-module-finite-presentation

### Original step 6

Noetherian geometry of the stratum. The standing $X$ is Noetherian by step 1. Its underlying space has every subset retrocompact by [def-weil-constructible-subset]. Since $X$ is quasi-compact, the locally closed stratum $S$ is quasi-compact. It is locally Noetherian by [lem-weil-pbc-immersion-base-change-lft](2) and [pqf-lem-locnoeth-lft]. Intersections of affine opens in the Noetherian space $S$ are quasi-compact, so $S$ is quasi-separated and admits a finite affine open cover. Let $Q$ be any locally perfect complex on $S$, with coefficient $\Gamma$ in the list; the next three steps show $Q\in\Dctf(S,\Gamma)$.

Citations: def-weil-constructible-subset, lem-weil-pbc-immersion-base-change-lft, pqf-lem-locnoeth-lft

### Original step 7

Finite pro-étale refinement. Choose a pro-étale covering family trivializing $Q$. Apply [lem-sfb-finite-affine-proetale-refinement] to the finite affine cover from the preceding step. It supplies finitely many affine $V_{\alpha j}$ lying in the chosen cover, with images covering $S$, and says that this finite family is itself a covering in the small pro-étale site. The weakly étale assertion uses [sk-lem-pe-weakly-etale-stability], while the finite affine-refinement condition is exactly the covering condition in [sk-def-pe-site].

Citations: lem-sfb-finite-affine-proetale-refinement, sk-lem-pe-weakly-etale-stability, sk-def-pe-site

### Original step 8

Uniform local models and cohomology. On each member $V_i$ of the finite cover, the exact pullback and ring isomorphism of [sk-prop-sfb-cartesian-coefficients](1) identify the restriction of $Q$ with $\Gamma_{V_i}\otimes_{\Gamma(*)}Q_i^\bullet$, retaining the scalar model from the trivializing cover. Take $r$ and $s$ to bound the degrees of the finitely many models; for empty $S$ use $r=s=0$. Step 5 proves exactness of scalar extension for every listed coefficient ring, and proves that every scalar cohomology module is finitely presented, not merely finitely generated. Thus [lem-sfb-local-model-cohomology-descent] applies: the global cohomology vanishes outside $[r,s]$ and has the finite constant local models of [det-def-sfb-constructible-local-model]. The whole $S$ is constructible in itself, so its one-piece stratification gives bounded constructible cohomology by [det-def-sfb-constructible-tor-amplitude](1),(2).

Citations: sk-prop-sfb-cartesian-coefficients, lem-sfb-local-model-cohomology-descent, det-def-sfb-constructible-local-model, det-def-sfb-constructible-tor-amplitude

### Original step 9

Tor amplitude on the stratum. Step 4's projective-retract argument makes each model term flat; the bounded model is K-flat by [lem-pc-bounded-above-flat-kflat-site]. The exact coefficient pullback of step 8 has coefficient ring identified with $\Gamma_{V_i}$, so the small ringed-topos tensor isomorphism of [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] applies. These are precisely the local model hypotheses of [lem-sfb-local-model-tor-bound-descent], which gives global Tor amplitude in $[r,s]$. Together with step 8 and [det-def-sfb-constructible-tor-amplitude], this proves $Q\in\Dctf(S,\Gamma)$.

Citations: lem-pc-bounded-above-flat-kflat-site, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-sfb-local-model-tor-bound-descent, det-def-sfb-constructible-tor-amplitude

### Original step 10

Extension by zero. Apply steps 6–9 to $Q=P_{\Lambda'}$ from step 4. The immersion $a:S\hookrightarrow X$ is quasi-compact: preimages of affine opens of $X$ are quasi-compact subsets of its Noetherian space. Its local finite type from step 6 therefore makes it finite type [def-weil-finite-type-morphism]. Its local affine algebras are finite type over finite-type $k$-algebras, hence finitely generated over $k$ by combining the two finite sets of generators. Since $S$ is quasi-compact, $S$ is finite type over $k$. By [lem-weil-pbc-separated-cancellation](a) $a$ is separated, and [lem-weil-pbc-proper-fp-permanence](e) applied to $a$ and $X\to\operatorname{Spec}k$ makes $S$ separated over $k$. Thus both schemes are standing schemes and $a$ is separated of finite type. For $a=i\circ u$, [sk-def-sfb-module-lower-shriek] defines the exact $u_!$ with underlying abelian sheaf $u^{\Ab}_!M$; [sk-def-sfb-module-pushforward-pullback] defines $i_*=\operatorname{Res}_{\eta_i}\circ\operatorname{mapMod}(i^{\Ab}_*)$, with coefficient action through $\eta_i$. Their composite is precisely the statement's module extension by zero. Now [det-thm-sf-ctf-stability-direct-images](2) gives $a_!Q\in\Dctf(X,\Lambda')$, completing (2).

Citations: def-weil-finite-type-morphism, lem-weil-pbc-separated-cancellation, lem-weil-pbc-proper-fp-permanence, sk-def-sfb-module-lower-shriek, sk-def-sfb-module-pushforward-pullback, det-thm-sf-ctf-stability-direct-images

### Original step 11

Retracts at finite coefficients. Let $C\in\Dctf(X,B)$ for a
finite admissible ring $B$, and suppose $J$ is a retract of $C$ in the
ambient derived category. The equivalence in
[det-pe-finite-tor-comparison-noetherian] gives an étale bounded
constructible finite-Tor complex $C_0$ with $\nu_X^*C_0\simeq C$.
Here $B$ is Noetherian and the standing $X$ is qcqs. The exact fully faithful
functor of [det-pe-classical-sheaves-modules] identifies
$H^q(C)$ with $\nu_X^*H^q(C_0)$ and lifts its idempotent whose image is
$H^q(J)$ to an endomorphism of $H^q(C_0)$. Its image is constructible by
[thm-constructible-serre] (image equals kernel of the cokernel).
Exactness of $\nu_X^*$ identifies its image with $H^q(J)$. Since $X$ is qcqs and $B$ is a discrete Noetherian ring, [sk-thm-pe-constructible-comparison] states that $\nu_X^*$ carries constructible étale sheaves of $B$-modules into $\Cons(X,B)$, so $H^q(J)\in\Cons(X,B)$; it vanishes outside the finite cohomological range of $C$. Thus $J$ has
bounded constructible cohomology. Tensoring the retraction with any module
still gives a retraction, so the Tor interval of $C$ bounds that of $J$.
It follows that $J\in\Dctf(X,B)$.

Citations: det-pe-finite-tor-comparison-noetherian, det-pe-classical-sheaves-modules, thm-constructible-serre, det-def-sfb-constructible-tor-amplitude, sk-thm-pe-constructible-comparison

### Original step 12

Thickness at the other coefficients and closure under triangles.
For $\mathcal O_F$, [det-lem-int-integral-heart-triangulated](2) explicitly
states that ambient kernels and cokernels of maps of constructible sheaves
are constructible. For fields the same is
[sk-lem-coefficient-heart](1). Hence an idempotent on a constructible sheaf
has constructible image (the kernel of its complementary idempotent).
Cohomology of a derived retract is such an image, so it is bounded
constructible. The Tor bound passes to a retract as in step 11.
For finite coefficients, [lem-weil-proetale-dbc-triangulated] states
triangulation of the bounded constructible category for every finite
commutative ring. For integral coefficients this is
[det-lem-int-integral-heart-triangulated](1), and for fields it is
[det-cor-coefficient-heart-ii-triangulated]. Finally
[det-def-sfb-constructible-tor-amplitude] states the shift, triangle and
retract closure of finite Tor amplitude. Intersecting these properties
with bounded constructibility, and using step 11 for finite coefficients,
shows that $\Dctf(X,\Lambda')$ is thick at every stage.

Citations: det-lem-int-integral-heart-triangulated, sk-lem-coefficient-heart, lem-weil-proetale-dbc-triangulated, det-cor-coefficient-heart-ii-triangulated, det-def-sfb-constructible-tor-amplitude

### Original step 13

Exact scalar extension and generation. The actual derived
extension of scalars along $\Lambda_X\to\Lambda'_X$ is an exact
triangulated functor by [lem-pur-derived-change-of-rings](2), applied to
the small ringed pro-étale site. It therefore preserves shifts and
extensions. It also preserves retracts: if $pi=1$, then $T(p)T(i)=1$.
Step 10 verifies that each generator immersion has both schemes in the standing separated finite-type setting, as required by the current [det-prop-scalar-six-pullback](2). Its exact locally closed extension by zero is applied termwise to the unbounded ambient complexes, and all scalar tensors here are ordinary derived tensors without completion. By that clause, the image of each generator $a_!P$
is $a_!(P_{\Lambda'})$, which belongs to $\Dctf(X,\Lambda')$ by steps 4–10.
Steps 11–12 show that the inverse image of this target subcategory is closed
under the finite operations in (1). Inducting on the finite construction
in steps 1–3 proves (3) for each elementary map. For a composite of listed
maps, apply this result successively and identify the composite functor
with extension along the composite by
[det-prop-scalar-six-pullback](3). The local calculation in step 4 applies
to that composite as well, so all three clauses hold as stated.

Citations: lem-pur-derived-change-of-rings, det-prop-scalar-six-pullback
