# Q160 stage-1 repair report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-smooth-curve-relative-frobenius-degree.json`: unchanged statement; three-step assembly.
- `dag/nodes/sec-six-functors-basics/lem-sfb-automorphism-twist-curve-lift.json`: statement, unsplit, no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-smooth-curve-function-field-p-basis.json`: statement, unsplit, no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-frobenius-image-field-tower-degree.json`: statement, unsplit, no Mathlib match.
- `citations.json`: verbatim statement quotes for every cited node in every assembly step.

## Attachments

None. The source-project search for the blueprint tag, relativeFrobenius and relative_frobenius found no declaration of the item under WeilConjectures. Sheaf.AlgebraicGeometry.Curve.RelativeFrobeniusDegree.smooth_proper_curve_relative_frobenius_degree is actually in namespace AlgebraicGeometry, at line 82, and its proof is `sorry`; it is not an attachment. The live declaration and docstring were read. No Lean was written or compiled.

## WANTED

None. All mathematical source passages used are present locally.

## What was wrong and what changed

The released repair note explicitly reopens the already-split item: the old 5052-character argument leaves too much work at one node. The sandbox had only dispatcher marker files, no previous node files/report/search log. No Q160 deliver process was running. I continued from the current live returned item, preserving its statement, statement dependencies, provenance and Lean records. The repair adds three genuine intermediate arguments rather than a new copy of the entire theorem; all are statement-only, unsplit and independently workable. The old proof route remains differential/p-basis, not the alternative etale-chart route of 0CCF.

## New nodes and preservation of the returned argument

1. `lem-sfb-automorphism-twist-curve-lift`: an arbitrary field automorphism and arbitrary compatible homeomorphic scheme endomorphism, with no Frobenius or degree hypothesis. This owns the relative-dimension reduction, explicit inverse to the first projection, invariance of integrality/dimension, base-change smoothness/properness, the projection equations, nonconstancy and functorial generic-stalk equality. The generic lemma is not the parent's twist clause restated: its semilinear lift and stalk comparison are reusable for any automorphism/endomorphism pair. Source: curves.tex 0CCY first paragraph and varieties.tex 0CCG diagram. The refinement is agent-written. The scalar structure is the SECOND projection; the first projection and its function-field map need not be k-linear.

2. `lem-sfb-smooth-curve-function-field-p-basis`: removes properness and asks only about an integral smooth dimension-one curve. This owns both the differential localization and the p-basis argument, without any twist or geometric Frobenius conclusion. Source: curves.tex 0CCY second paragraph, morphisms.tex 02G1, algebra.tex 00RT(2), more-algebra.tex 07P2. At the generic point take an affine neighborhood with free rank-one differentials, identify the function field with its fraction field, localize the module of differentials, then use an absolute p-basis. Algebraic closedness puts k inside K^p; thus the differential-basis theorem applies over kK^p=K^p. A basis of the one-dimensional differential space has one index, giving the displayed p-element monomial basis. No separability or properness is inserted.

3. `lem-sfb-frobenius-image-field-tower-degree`: works over any characteristic-p field K with a finite basis over K^p, of arbitrary degree d. This owns the Frobenius image isomorphisms, transport of spanning and independence, adjacent extension degrees, finite-tower multiplication and induction including n=0. Source: fields.tex 09G9 and the power iteration of varieties.tex 0CCG. The explicit basis transport is an agent-written refinement. No perfectness of K is used; a perfect K is allowed and gives d=1.

In the retained first attempt, existing `lem-sfb-relative-frobenius-function-field-image` was reused rather than duplicated for the exact image assertion. The returned-head repair below now derives that equality explicitly from the twist-lift node instead. Its statement and empty proof dependency list were read; it does not depend on this item. In the generic-stalk identity of the new twist-lift node, specialize u=F_C^n: on stalks u^*(x)=x^(p^n), and beta is surjective. Therefore the same explicit image argument as old step 3 is retained even independently of that reusable existing image statement.

The elementary prime-characteristic and algebraic-closedness root calculation of old step 1 stays in the parent's first step, where it is genuinely elementary. Its smooth-relative-dimension reduction is in the twist-lift node. Old step 2 and the geometric/stalk part of old step 3 go to the twist-lift node; old steps 4-5 go to the curve p-basis node; old step 6 goes to the general Frobenius tower node. The n=0 identity appears explicitly in the new twist-lift and tower statements and in parent step 3.

### Returned proof text retained verbatim

Old step 1:

Write $a:C\to S=\operatorname{Spec}k$. The integer $p$ is prime: a factorization $p=uv$ with $1<u,v<p$ would give $(u\cdot1_k)(v\cdot1_k)=0$ although both factors are nonzero, contrary to $k$ being a field and $p$ being the least positive characteristic. The only nonempty fibre of $a$ is $C$, which has a single irreducible component of dimension one because it is integral. Thus it is equidimensional of dimension one, and $a$ is smooth of relative dimension one by the equivalent fibre formulation in def-sbc-smooth-morphisms. For every $n\geq0$ the map $\varphi_n:k\to k$, $c\mapsto c^{p^n}$, is bijective: injectivity follows from $(x-y)^{p^n}=x^{p^n}-y^{p^n}$ and absence of nilpotents in a field, and surjectivity follows by taking a root of $T^{p^n}-c$ in the algebraically closed field $k$. For $n=0$ it is the identity.

Old step 2:

Put $s_n=\operatorname{Spec}(\varphi_n)$ and $C_n=C\times_{S,s_n}S$, with projections $\pi_n:C_n\to C$ and $a_n:C_n\to S$. Smooth relative dimension one and properness are preserved by this base change, by the two cited permanence statements. Moreover $\pi_n$ is an isomorphism of schemes: its inverse is the pair $(\operatorname{id}_C,s_n^{-1}\circ a)$, and the two inverse identities follow by composing with both projections in the fibre-product universal property. Hence $C_n$ is nonempty, reduced and irreducible, of dimension one, because these are invariant under an isomorphism of schemes. Properness supplies separatedness and finite type, so $C_n$ is a smooth proper integral $k$-curve of dimension one. The isomorphism $\pi_n$ is an isomorphism of schemes; no assertion that it respects the given $k$-structures is needed.

Old step 3:

The pair $(F_C^n,a)$ defines $F_n:C\to C_n$: the equality $a\circ F_C^n=s_n\circ a$ follows because every ring homomorphism preserves $p^n$-th powers. Its defining identities are $\pi_n\circ F_n=F_C^n$ and $a_n\circ F_n=a$. Absolute Frobenius is the identity on the underlying space, and $\pi_n$ is an isomorphism, so $F_n$ is a homeomorphism on underlying spaces. In particular it sends the generic point to the generic point. It is nonconstant: if it factored through a $k$-rational point, its surjective image would be a singleton, impossible for a space of dimension one. The cited curve/function-field statement therefore gives the induced field embedding $F_n^*:k(C_n)\hookrightarrow K:=k(C)$. Let $\beta_n=\pi_n^*:K\xrightarrow{\sim}k(C_n)$ be the isomorphism on generic stalks. On those stalks the identity $\pi_n\circ F_n=F_C^n$ says explicitly $F_n^*(\beta_n(x))=x^{p^n}$. Since $\beta_n$ is surjective, the image of $F_n^*$ is precisely $K^{p^n}:=\{x^{p^n}:x\in K\}$. This uses a field isomorphism $\beta_n$, not a $k$-linear identification of the twists.

Old step 4:

Let $\eta$ be the generic point of $C$. Apply the cited smooth-differentials statement at $\eta$ to find a nonempty affine open $W=\operatorname{Spec}A$ containing $\eta$ on which $\Omega_{A/k}$ is free of rank one: the fibre dimension in that statement is one by step 1. By the affine-fraction statement $K=k(C)$ is the field of fractions of the domain $A$. Apply localization of differentials with the multiplicative set $A\setminus\{0\}$ to obtain $\Omega_{K/k}\cong K\otimes_A\Omega_{A/k}\cong K$. Consequently $\dim_K\Omega_{K/k}=1$. Here $\Omega_{K/k}$ denotes the module of Kähler differentials, and every ring map in the localization is the given $k$-algebra map.

Old step 5:

Use the absolute $p$-basis existence statement for the field $K$ to choose a family $(t_i)_{i\in I}$ whose restricted monomials form a basis of $K$ over $K^p$. Step 1 gives $k\subseteq K^p$, since every element of $k$ has a $p$-th root in $k$. Thus the compositum $kK^p$ equals $K^p$, and this same family satisfies exactly the hypothesis of the cited differential-basis statement for $K/k$. It follows that $(\mathrm dt_i)_{i\in I}$ is a basis of $\Omega_{K/k}$. By step 4 this vector space has dimension one. Hence $I$ has exactly one element: it cannot be empty because it spans a nonzero vector space, and two distinct indices would give two independent vectors in a one-dimensional space. Writing its element as $t$, the original monomial basis is $1,t,\ldots,t^{p-1}$. It has $p$ elements, so $[K:K^p]=p$.

Old step 6:

For $i\geq0$ put $L_i=K^{p^i}$. The map $x\mapsto x^{p^i}$ is a field isomorphism $K\xrightarrow{\sim}L_i$ and maps $K^p$ onto $L_{i+1}$. In particular the image of the basis from step 5 is $1,t^{p^i},\ldots,(t^{p^i})^{p-1}$, a basis of $L_i$ over $L_{i+1}$: spanning and independence follow by applying this isomorphism and its inverse to the corresponding linear combinations. Thus every adjacent extension has degree $p$. Induct on $n$ to compute $[K:L_n]$. For $n=0$, $L_0=K$ and the degree is $1=p^0$. If $[K:L_n]=p^n$ is finite, field-degree multiplicativity for $L_{n+1}\subseteq L_n\subseteq K$ gives $[K:L_{n+1}]=[K:L_n][L_n:L_{n+1}]=p^np=p^{n+1}$. By step 3, $L_n=F_n^*k(C_n)$, proving the required formula. At $n=0$ the fibre-product identification and $\pi_0 F_0=\operatorname{id}_C$ identify $F_0$ with the identity, as required.

## Searches read

For each new node I ran LeanFinder, LeanSearch, Loogle and the required logged grep through msearch.py, and a second LeanFinder phrasing. searches.jsonl is the original command-generated log, not a reconstructed list. Every recorded query in the new node matches it exactly. No query was invented. The first p-basis grep was noisy (pBasis also matches groupBasis); the second restricted, case-sensitive-in-pattern grep and the semantic queries were read as well.

The geometry hits include Smooth base-change permanence and IsProper.isStableUnderBaseChange, read in Mathlib/AlgebraicGeometry/Morphisms/{Smooth,Proper}.lean (Smooth lines 117,166 and Proper line 72). They provide only parts of the twist/lift result. The function-field Mathlib file has generic stalks and fraction-field instances but no semilinear lift theorem. The p-basis hits include Algebra.SubmersivePresentation.basisKaehler and Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (StandardSmoothCotangent.lean lines 226 and 314), requiring the presentation/rank input that the curve argument must construct; they do not supply a singleton p-basis of the function field. The tower candidates IsPurelyInseparable.finrank_eq_pow (Basic.lean line 322) only supply an unspecified exponent. Module.Basis.mapPowExpCharPowOfIsSeparable (PerfectClosure.lean line 376) assumes separability and keeps its scalar field fixed, whereas K/K^p is generally inseparable and the tower scalars change. None is an exact match or a one-line specialization.

Whole-DAG and blueprint searches used Frobenius, relative Frobenius, Frobenius twist, field automorphism, p-basis, differentials, power subfield, p-th powers and the source tags. The blueprint hits concern Weil actions, finite-field models or relative-Frobenius conventions and do not state the new results. Existing function-field-image and p-basis lemmas were read and reused as existing material, not recreated.

## Not duplicates

lem-sfb-automorphism-twist-curve-lift vs lem-trf-scheme-frobenius-finite-radicial: the new node concerns any automorphism and compatible homeomorphic endomorphism, with explicit inverse and generic-stalk functoriality; Finiteness and radiciality of the scalar-extended scheme Frobenius does not give this full intermediate statement.

lem-sfb-automorphism-twist-curve-lift vs lem-trf-relative-frobenius-finite: the new node concerns any automorphism and compatible homeomorphic endomorphism, with explicit inverse and generic-stalk functoriality; Finiteness of the n-fold relative Frobenius does not give this full intermediate statement.

lem-sfb-automorphism-twist-curve-lift vs def-trf-scheme-frobenius: the new node concerns any automorphism and compatible homeomorphic endomorphism, with explicit inverse and generic-stalk functoriality; Scheme and Galois Frobenius of the geometric fiber does not give this full intermediate statement.

lem-sfb-automorphism-twist-curve-lift vs d-relative-frob: the new node concerns any automorphism and compatible homeomorphic endomorphism, with explicit inverse and generic-stalk functoriality; The relative Frobenius factorization does not give this full intermediate statement.

lem-sfb-automorphism-twist-curve-lift vs lem-sfb-frobenius-twist-geometric-integrality-affine: the new node concerns any automorphism and compatible homeomorphic endomorphism, with explicit inverse and generic-stalk functoriality; Frobenius twists: geometric integrality, scalar extension, and affine relative Frobenius does not give this full intermediate statement.

lem-sfb-automorphism-twist-curve-lift vs lem-sfb-relative-frobenius-function-field-image: the new node concerns any automorphism and compatible homeomorphic endomorphism, with explicit inverse and generic-stalk functoriality; Function-field image of iterated relative Frobenius over an algebraically closed field does not give this full intermediate statement.

lem-sfb-automorphism-twist-curve-lift vs lem-sfb-one-variable-purely-inseparable-subfield: the new node concerns any automorphism and compatible homeomorphic endomorphism, with explicit inverse and generic-stalk functoriality; Purely inseparable subfields of a one-variable function field are power subfields does not give this full intermediate statement.

lem-sfb-automorphism-twist-curve-lift vs lem-sfb-purely-inseparable-curve-frobenius: the new node concerns any automorphism and compatible homeomorphic endomorphism, with explicit inverse and generic-stalk functoriality; Purely inseparable smooth proper curve maps are relative Frobenius does not give this full intermediate statement.

lem-sfb-automorphism-twist-curve-lift vs lem-sfb-smooth-curve-relative-frobenius-degree: the new node concerns any automorphism and compatible homeomorphic endomorphism, with explicit inverse and generic-stalk functoriality; Relative Frobenius of a smooth proper curve has degree p to the n does not give this full intermediate statement.

lem-sfb-automorphism-twist-curve-lift vs lem-sfb-curve-frobenius-separable-factorization: the new node concerns any automorphism and compatible homeomorphic endomorphism, with explicit inverse and generic-stalk functoriality; Frobenius and separable factors of a nonconstant smooth proper curve map does not give this full intermediate statement.

lem-sfb-smooth-curve-function-field-p-basis vs lem-sfb-relative-frobenius-function-field-image: the new node deduces a singleton p-basis for an arbitrary smooth integral curve function field without properness; Function-field image of iterated relative Frobenius over an algebraically closed field supplies another field/p-basis input or a different geometric Frobenius conclusion.

lem-sfb-smooth-curve-function-field-p-basis vs lem-sfb-one-variable-purely-inseparable-subfield: the new node deduces a singleton p-basis for an arbitrary smooth integral curve function field without properness; Purely inseparable subfields of a one-variable function field are power subfields supplies another field/p-basis input or a different geometric Frobenius conclusion.

lem-sfb-smooth-curve-function-field-p-basis vs lem-sfb-purely-inseparable-curve-frobenius: the new node deduces a singleton p-basis for an arbitrary smooth integral curve function field without properness; Purely inseparable smooth proper curve maps are relative Frobenius supplies another field/p-basis input or a different geometric Frobenius conclusion.

lem-sfb-smooth-curve-function-field-p-basis vs lem-sfb-smooth-curve-relative-frobenius-degree: the new node deduces a singleton p-basis for an arbitrary smooth integral curve function field without properness; Relative Frobenius of a smooth proper curve has degree p to the n supplies another field/p-basis input or a different geometric Frobenius conclusion.

lem-sfb-smooth-curve-function-field-p-basis vs lem-per-cofinite-subfields-finite-extension-differential-rank: the new node deduces a singleton p-basis for an arbitrary smooth integral curve function field without properness; Eventual equality of differential ranks under a finite field extension supplies another field/p-basis input or a different geometric Frobenius conclusion.

lem-sfb-smooth-curve-function-field-p-basis vs lem-per-cofinite-pbasis-completed-generic-rank: the new node deduces a singleton p-basis for an arbitrary smooth integral curve function field without properness; Stabilized generic rank after deleting finitely many coefficient p-basis elements supplies another field/p-basis input or a different geometric Frobenius conclusion.

lem-sfb-smooth-curve-function-field-p-basis vs lem-weil-pbc-p-independent-extends-to-p-basis: the new node deduces a singleton p-basis for an arbitrary smooth integral curve function field without properness; A p-independent family extends to a p-basis supplies another field/p-basis input or a different geometric Frobenius conclusion.

lem-sfb-smooth-curve-function-field-p-basis vs lem-weil-pbc-differential-zero-iff-pth-power: the new node deduces a singleton p-basis for an arbitrary smooth integral curve function field without properness; Over a perfect field, da = 0 in the Kähler differentials exactly for p-th powers a supplies another field/p-basis input or a different geometric Frobenius conclusion.

lem-sfb-smooth-curve-function-field-p-basis vs lem-weil-pbc-derivation-nonzero-on-non-pth-power: the new node deduces a singleton p-basis for an arbitrary smooth integral curve function field without properness; A non-pth-power in a finite type characteristic-p domain is detected by a derivation supplies another field/p-basis input or a different geometric Frobenius conclusion.

lem-sfb-smooth-curve-function-field-p-basis vs lem-weil-pbc-intersection-subfields-differentials: the new node deduces a singleton p-basis for an arbitrary smooth integral curve function field without properness; A directed family of subfields between K^p and K with intersection K^p detects differentials and p-th powers in finite extensions supplies another field/p-basis input or a different geometric Frobenius conclusion.

lem-sfb-smooth-curve-function-field-p-basis vs lem-weil-pbc-p-independent-insert-outside-span: the new node deduces a singleton p-basis for an arbitrary smooth integral curve function field without properness; Insertion outside the p-monomial span preserves p-independence supplies another field/p-basis input or a different geometric Frobenius conclusion.

lem-sfb-smooth-curve-function-field-p-basis vs lem-weil-pbc-zorn-lemma: the new node deduces a singleton p-basis for an arbitrary smooth integral curve function field without properness; Zorn's lemma for families of subsets supplies another field/p-basis input or a different geometric Frobenius conclusion.

lem-sfb-smooth-curve-function-field-p-basis vs lem-weil-pbc-p-basis-exists: the new node deduces a singleton p-basis for an arbitrary smooth integral curve function field without properness; Every field of characteristic p has a p-basis supplies another field/p-basis input or a different geometric Frobenius conclusion.

lem-sfb-smooth-curve-function-field-p-basis vs lem-weil-pbc-p-basis-differentials-basis: the new node deduces a singleton p-basis for an arbitrary smooth integral curve function field without properness; The differentials of a p-basis form a basis of the Kähler differentials supplies another field/p-basis input or a different geometric Frobenius conclusion.

lem-sfb-smooth-curve-function-field-p-basis vs lem-weil-pbc-power-series-ring-subfields: the new node deduces a singleton p-basis for an arbitrary smooth integral curve function field without properness; The subfields K_J of the fraction field of k[[x]][y] cut out by a p-basis supplies another field/p-basis input or a different geometric Frobenius conclusion.

lem-sfb-smooth-curve-function-field-p-basis vs lem-weil-pbc-p-basis-zero-differential-coefficients: the new node deduces a singleton p-basis for an arbitrary smooth integral curve function field without properness; Euler operators detect all nonconstant p-basis coefficients of an element with zero differential supplies another field/p-basis input or a different geometric Frobenius conclusion.

lem-sfb-smooth-curve-function-field-p-basis vs lem-weil-pbc-p-independent-evaluation-kernel: the new node deduces a singleton p-basis for an arbitrary smooth integral curve function field without properness; Partial derivatives preserve the polynomial evaluation kernel of a p-independent family supplies another field/p-basis input or a different geometric Frobenius conclusion.

lem-sfb-smooth-curve-function-field-p-basis vs lem-weil-pbc-p-independent-maximal-superset: the new node deduces a singleton p-basis for an arbitrary smooth integral curve function field without properness; Maximal p-independent supersets supplies another field/p-basis input or a different geometric Frobenius conclusion.

lem-sfb-smooth-curve-function-field-p-basis vs lem-weil-pbc-p-independent-differentials-independent: the new node deduces a singleton p-basis for an arbitrary smooth integral curve function field without properness; The differentials of a p-independent family are linearly independent supplies another field/p-basis input or a different geometric Frobenius conclusion.

lem-sfb-frobenius-image-field-tower-degree vs det-def-sfb-qlbar-condensed-subextensions: the new node computes each Frobenius-image basis and all tower degrees from an arbitrary finite first degree d; Finite subextensions of $\overline{\mathbf Q}_\ell$ form a directed poset does not give this general basis-transport tower result.

lem-sfb-frobenius-image-field-tower-degree vs lem-trf-scheme-frobenius-finite-radicial: the new node computes each Frobenius-image basis and all tower degrees from an arbitrary finite first degree d; Finiteness and radiciality of the scalar-extended scheme Frobenius does not give this general basis-transport tower result.

lem-sfb-frobenius-image-field-tower-degree vs lem-trf-relative-frobenius-finite: the new node computes each Frobenius-image basis and all tower degrees from an arbitrary finite first degree d; Finiteness of the n-fold relative Frobenius does not give this general basis-transport tower result.

lem-sfb-frobenius-image-field-tower-degree vs def-trf-scheme-frobenius: the new node computes each Frobenius-image basis and all tower degrees from an arbitrary finite first degree d; Scheme and Galois Frobenius of the geometric fiber does not give this general basis-transport tower result.

lem-sfb-frobenius-image-field-tower-degree vs lem-wf-henselian-finite-galois-lift: the new node computes each Frobenius-image basis and all tower degrees from an arbitrary finite first degree d; Generic Galois group of a finite local etale henselian residue lift does not give this general basis-transport tower result.

lem-sfb-frobenius-image-field-tower-degree vs d-relative-frob: the new node computes each Frobenius-image basis and all tower degrees from an arbitrary finite first degree d; The relative Frobenius factorization does not give this general basis-transport tower result.

lem-sfb-frobenius-image-field-tower-degree vs lem-sfb-frobenius-twist-geometric-integrality-affine: the new node computes each Frobenius-image basis and all tower degrees from an arbitrary finite first degree d; Frobenius twists: geometric integrality, scalar extension, and affine relative Frobenius does not give this general basis-transport tower result.

lem-sfb-frobenius-image-field-tower-degree vs lem-sfb-relative-frobenius-function-field-image: the new node computes each Frobenius-image basis and all tower degrees from an arbitrary finite first degree d; Function-field image of iterated relative Frobenius over an algebraically closed field does not give this general basis-transport tower result.

lem-sfb-frobenius-image-field-tower-degree vs lem-sfb-purely-inseparable-curve-frobenius: the new node computes each Frobenius-image basis and all tower degrees from an arbitrary finite first degree d; Purely inseparable smooth proper curve maps are relative Frobenius does not give this general basis-transport tower result.

lem-sfb-frobenius-image-field-tower-degree vs lem-sfb-smooth-curve-relative-frobenius-degree: the new node computes each Frobenius-image basis and all tower degrees from an arbitrary finite first degree d; Relative Frobenius of a smooth proper curve has degree p to the n does not give this general basis-transport tower result.

lem-sfb-frobenius-image-field-tower-degree vs lem-sfb-curve-frobenius-separable-factorization: the new node computes each Frobenius-image basis and all tower degrees from an arbitrary finite first degree d; Frobenius and separable factors of a nonconstant smooth proper curve map does not give this general basis-transport tower result.

lem-sfb-frobenius-image-field-tower-degree vs lem-per-regular-gysin-calculus: the new node computes each Frobenius-image basis and all tower degrees from an arbitrary finite first degree d; Gysin purity calculus on regular affine schemes does not give this general basis-transport tower result.

lem-sfb-frobenius-image-field-tower-degree vs lem-per-cofinite-subfields-finite-extension-differential-rank: the new node computes each Frobenius-image basis and all tower degrees from an arbitrary finite first degree d; Eventual equality of differential ranks under a finite field extension does not give this general basis-transport tower result.

lem-sfb-frobenius-image-field-tower-degree vs lem-per-sylow-simultaneous-field-sections: the new node computes each Frobenius-image basis and all tower degrees from an arbitrary finite first degree d; Simultaneous prime-to-ell field sections over separable charts does not give this general basis-transport tower result.

lem-sfb-frobenius-image-field-tower-degree vs lem-weil-pbc-finitely-generated-field-complete-intersection-model: the new node computes each Frobenius-image basis and all tower degrees from an arbitrary finite first degree d; A finitely generated field is the fraction field of a quotient of a polynomial ring by a regular sequence, with n - c = trdeg does not give this general basis-transport tower result.

lem-sfb-frobenius-image-field-tower-degree vs lem-weil-pbc-field-degree-multiplicativity: the new node computes each Frobenius-image basis and all tower degrees from an arbitrary finite first degree d; Multiplicativity of degrees in a tower of finite field extensions does not give this general basis-transport tower result.

lem-sfb-frobenius-image-field-tower-degree vs lem-weil-pbc-finite-purely-inseparable-degree-p-intermediate: the new node computes each Frobenius-image basis and all tower degrees from an arbitrary finite first degree d; A nontrivial finite purely inseparable extension has a degree-p intermediate step does not give this general basis-transport tower result.

lem-sfb-frobenius-image-field-tower-degree vs lem-weil-pbc-tower-product-basis: the new node computes each Frobenius-image basis and all tower degrees from an arbitrary finite first degree d; Products of bases form a basis in a tower does not give this general basis-transport tower result.

lem-sfb-frobenius-image-field-tower-degree vs lem-weil-pbc-make-separably-generated: the new node computes each Frobenius-image basis and all tower degrees from an arbitrary finite first degree d; A finitely generated field extension becomes separably generated after finite purely inseparable extensions does not give this general basis-transport tower result.

lem-sfb-frobenius-image-field-tower-degree vs lem-weil-pbc-triangular-field-model-data: the new node computes each Frobenius-image basis and all tower degrees from an arbitrary finite first degree d; Triangular minimal-polynomial data and independent bounded products does not give this general basis-transport tower result.

lem-sfb-frobenius-image-field-tower-degree vs lem-weil-pbc-algebraic-tower-triangular-relations: the new node computes each Frobenius-image basis and all tower degrees from an arbitrary finite first degree d; Monic triangular relations and independent bounded products over an algebraic base field does not give this general basis-transport tower result.

lem-sfb-frobenius-image-field-tower-degree vs lem-weil-pbc-finite-purely-inseparable-transitive: the new node computes each Frobenius-image basis and all tower degrees from an arbitrary finite first degree d; Finite purely inseparable extensions compose does not give this general basis-transport tower result.

## Review by Q160

I read the returned six proof steps against curves.tex 0CCY in full, the relative-Frobenius definition and 0CCG diagram/iteration in varieties.tex, 07P2 in more-algebra.tex, 02G1 in morphisms.tex, 00RT(2) in algebra.tex and the multiplicativity proof 09G9 in fields.tex. I also read the chapter record, the inherited sk-thm-sf-ctf-stability unit, GOAL.md, the three-level contract and delivery-errors B-E. The inherited chapter/unit discrepancy and null blueprint ancestor are not changed: these auxiliary nodes keep their parent's route and ancestry, as the previous delivery did. I followed the released repair order, not the live split/review status.

Assembly step 1 cites the field, algebraic-closedness and characteristic definitions, which give respectively no zero divisors, roots of nonconstant polynomials, and the least positive characteristic. Those are exactly what the explicit prime and power-bijection argument needs; it does not invoke a separate perfect-field theorem.

Step 2 cites the NEW automorphism-twist lift statement, whose text explicitly provides the geometric curve properties, compatible unique lift, nonconstancy and injective generic-stalk map. I checked its au=sa hypothesis on ring maps, and its topological-homeomorphism hypothesis from the absolute-Frobenius definition, read in the cited node. The existing function-field-image node was checked for precisely the image equality under the same hypotheses in the first attempt. In the repaired assembly it is unnecessary: beta is surjective by the twist-lift statement, its composite with the lift pullback is u^*, and absolute Frobenius acts on generic stalks by p^n-th powers. Thus the image equality is proved explicitly in step 2.

Step 3 cites the NEW smooth-curve p-basis statement for its explicit p-element basis, not merely the definition of differentials. The curve in the item satisfies its smooth, integral and dimension-one hypotheses; properness is unneeded there. It then cites the NEW Frobenius-image field-tower statement with d=p, precisely the finite degree/basis just obtained. The tower's statement gives the formula for all n and includes the base case, so no field-tower theorem is silently assumed at the assembly level. The twist-lift statement's identity clause justifies the final n=0 identification, with both sigma and u the identity.

Every cited statement was opened and every citation quote is literally copied from that statement. New nodes have full hypotheses, define each power subfield and basis indexing inline, and cite definition nodes for the remaining notions. They have no proof sketches inside their statements, no proof steps, no proof dependencies and null proof_origin. Proof routes for their future workers are in this report, with the old texts preserved above. The parent proof is below 3000 characters and no step exceeds 2000 characters. This is three substantial separate arguments, not a one-node restatement of the parent.

Edge cases: n=0 gives T=C and degree 1; p=2 gives basis (1,t), adjacent tower degree 2 and total degree 2^n. On P^1 over an algebraically closed characteristic-p field, K=k(t) and L_i=k(t^(p^i)) have the displayed bases and degree. A perfect K in the general tower has d=1 and all images equal K. The zero-dimensional Spec(k) is deliberately excluded from the curve/p-basis and nonconstancy claims; its differentials have rank zero, showing why dimension one must remain. No integrality is inferred merely from arbitrary base change: the twist projection is an isomorphism because sigma is an automorphism. I corrected no statement and added no hypothesis to the parent.

## Unfinished work

The three new nodes are intentionally unsplit for parallel future workers, as ordered. No other unresolved mathematical issue was found.

## Returned-head repair and current-DAG comparison (2026-10-22)

The open return identifies head `9873422c5de` and a side-completion/live-DAG promotion failure, rather than a mathematical rejection. I retained the delivered sandbox, all three new statements, all source excerpts and all original search records. The initial resumed dry run completed successfully at `c2dc03622a5`; no earlier delivery invocation for this item was active. This repair is an updated split, not an unchanged re-push.

Against the current shared DAG, the retained parent statement, statement dependencies, source, blueprint provenance and maintainer metadata agree; the intended differences are its proof, proof dependencies and split report. None of the three new node ids is present in the current DAG. The released stage-1 repair order is still present and explicitly requires at least two new statement-only arguments and a parent assembly of at most 3000 characters. It applies despite the old pass record. The three independent intermediate statements remain intact and every original argument stays in the preserved proof texts and their assigned nodes.

I re-read every external statement used by the assembly: `def-pc-field-characteristic`, `def-weil-field`, `def-weil-algebraic-closure`, and `def-weil-absolute-frobenius-scheme`. Their retained citation quotes still agree with the current statements. I also re-read `lem-sfb-relative-frobenius-function-field-image`: its hypotheses and equality agree, but it is a redundant proof input. Step 2 now uses the actual generic-stalk identity stated by the new twist-lift lemma and the p-power action in the absolute-Frobenius definition. It writes both the composite map and the surjectivity argument, so it obtains the exact image without invoking the separate image node. I removed that citation from both proof_deps and citations.json. This directly preserves the old step 3 calculation and uses only statements that the assembly already needs.

Step 1 still supplies prime characteristic and the scalar automorphism by the explicit field/root calculation. Step 2 satisfies au=sa and the homeomorphism hypothesis and obtains all twist and nonconstancy clauses before calculating the image. Step 3 applies the p-basis lemma to the same smooth integral dimension-one curve and the general tower lemma to its displayed p-element basis; the identity-base-change clause handles n=0. The original P^1, p=2, perfect-field tower and excluded dimension-zero checks still apply. The parent statement and all new-node statements are unchanged, so the original logged Mathlib searches remain the same search questions and were read rather than repeated. No new Mathlib claim is made.

I also read every definition cited by the new statements against the current DAG, including curves, function fields, integrality, smooth relative dimension, fibre products, field degree and Kahler differentials. In particular def-sc-curves allows dimension at most one, so the explicit dimension-one hypotheses remain essential. The inverse to the twist projection is a scheme isomorphism, not a k-linear assertion. The general field-tower lemma assumes a finite first degree and defines all power subfields, so neither perfectness of K nor a hidden finiteness theorem is required.

The required delivery command will construct a fresh single commit on the current sheaf-dag and run server preflight; it owns rebasing and publication. No repository, launcher or Lean source was modified, and no compiler was run. The maintainer must perform any live promotion; the worker does not alter that state.

## Repair of the current return (2026-10-23, head 84f4e857e32)

The current entry in coord/returns/Q160.md names returned head `84f4e857e32`, dated 2026-10-22 16:43 UTC. The earlier head `9873422c5de` in the retained history above belongs to the previous repair attempt; it is not the head named by this return. I resumed the existing four node files, report, citations and command-generated search log. As required, I ran the dry run before editing; it exited successfully with `OK (not pushed)` at `f87e6bee055`.

For the return's rebase request, I compared each retained node file with its same relative path in the current shared DAG. All three auxiliary ids remain absent. The existing parent's only differing fields are proof, proof_deps and split_report; its statement, statement dependencies, source, blueprint ancestry, Lean records and maintainer metadata agree with current. The old six-step proof is still current, and the released stage-1 repair note still requires at least two new nodes and a short assembly. The delivery tool constructs the commit against freshly fetched current sheaf-dag and preserves maintainer-owned fields; no manual repository or git operation is needed.

For the changed-citation request, I reopened every external statement used by the assembly: def-pc-field-characteristic supplies least positive characteristic, def-weil-field supplies the nonzero-unit field axioms, def-weil-algebraic-closure supplies roots, and def-weil-absolute-frobenius-scheme supplies identity on points and the power action on sections. All retained quotes remain literal substrings. I also reopened all definition statements used by the three new nodes, particularly def-sc-curves (dimension at most one), def-sc-function-field (generic stalk), def-sbc-smooth-morphisms, fibre products and the differential universal property. No changed statement forces a new hypothesis or different route.

For the requested adjustment, assembly step 1 now explicitly verifies the unital ring homomorphism property of the scalar power map, by the characteristic-p binomial identity and iteration, before establishing bijectivity. Thus step 2 really supplies a field automorphism to the twist-lift lemma, not merely a bijection. Its source place no longer mentions the smooth-relative-dimension reduction that now belongs to the twist-lift node. The step-2 generic-stalk image calculation from the prior repair remains: surjectivity of beta and F* beta = (F_C^n)* give exactly K^(p^n). Step 3 still obtains the finite first degree from the p-basis statement and all iterated degrees from the tower statement, including n=0. I updated the split report and this review; this is not an unchanged re-push.

I reread curves.tex 0CCY, varieties.tex 0CCG, more-algebra.tex 07P2 and fields.tex 09G9 with the three new statements open. The twists keep the second projection as their scalar structure; the first projection is a scheme isomorphism with no claimed k-linearity. The p-basis assertion uses the explicit dimension-one hypothesis and does not assume properness. The tower assumes finite first degree and permits perfect K with d=1. Tests n=0, p=2 and K=k(t) still give identity degree 1, basis (1,t), and k(t^(p^n)) respectively. No new statement, new search question or Mathlib-leaf claim was introduced, so the original searches were read and retained. The project-only attachment search remains negative; the Sheaf theorem at line 82 still ends in sorry.

The promotion failure itself concerns maintainer-owned live state. This delivery supplies the refreshed checked overlay and leaves that promotion to L, as the return says.
