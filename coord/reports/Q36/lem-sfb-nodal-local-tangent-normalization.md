# Q36 stage-1 repair report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-nodal-local-tangent-normalization.json: existing statement unchanged; re-split assembly in five steps, 2601 characters.
- lem-sfb-nodal-completed-graded-model: statement, unsplit; no Mathlib match. This handles compatible completed normalization and the associated graded ring of the uncompleted local ring.
- lem-sfb-nodal-completed-residue-denominators: statement, unsplit; no Mathlib match. This handles faithful-flat descent, canonical residue identification and division coefficients.
- lem-sfb-graded-normalization-fraction-map: statement, unsplit; no Mathlib match. This constructs the intrinsic map, changes denominators and proves naturality without asserting invertibility.
- lem-sfb-quadratic-coefficient-proj-branches: statement, unsplit; no Mathlib match. This computes the single graded chart and its quadratic root/branch labels.
- report.md and citations.json; searches.jsonl is the unmodified output log of msearch.py. Search result files and returned-baseline.json retain the source material in the sandbox.

The sandbox initially held only dispatcher .brief files, no delivered node, report or search log. I copied the live returned node, retaining all of its fields and searches, to returned-baseline.json and the item path before editing. The live released repair note explicitly requires a new stage-1 re-split despite the earlier passing review. No repository or launcher file was changed. No git command, compiler, Lake command or sub-agent was run.

## Attachments

None. The project declaration AlgebraicGeometry.NodalLocal.tangent_normalization in lean/Sheaf/AlgebraicGeometry/NodalLocalTangentNormalization.lean:421 has `sorry` at line 442. Searches of lean/WeilConjectures by item tag, nodal notions, graded and normalization terminology found no completed declaration giving the whole item. Its sorry declaration is source material, not evidence of a finished proof. No new statement has a completed project declaration found by these searches.

## WANTED

None. All required Stacks source text is present.

## Problems repaired and work remaining

The returned proof contained 9497 characters and ten arguments in one node. It is now a short assembly of four comparable, genuinely intermediate statements. Each new node is self-contained, status unsplit, proof [], proof_deps [], proof_origin null; its proof belongs to a later worker. No new node restates the whole conclusion. The parent still proves that its intrinsic map is invertible by comparing the two independently constructed coefficient formulas, then derives its geometric and scheme-fibre clauses.

The parent statement is unchanged, and no STATEMENT-DISPUTED correction was needed. I retained the existing crucial restriction that a permitted denominator has unit leading coefficient in L, rather than merely a nonzero one. I also wrote out a reduction to a reduced finite-type affine neighbourhood before applying the existing normalization-stalk lemma: the original scheme need not be globally reduced or quasi-compact. No finite relative normalization/base-change theorem was substituted for the local argument. There are no unfinished repairs in the scope of this delivery; the four unsplit nodes are intentionally delivered as parallel work.

## Sources and research

Read the item and the actual ten-step Lean docstring, the live repair note, the chapter record and unit record, and latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/{_section.md,sk-thm-sf-ctf-stability-direct-images.proof.md}. The latter places this local calculation below direct-image preservation; it is not itself a claim about the six functors. The existing blueprint ancestry is retained: blueprint_refs.py ancestor prints None, so the new from.node is null with the complete inherited via chain plus the item and a precise local proof-step place. Searches of the whole blueprint by tangent, quadratic, normalization stalk, denominator, homogeneous localization, constant term and normalization fibre found no existing blueprint statement of these new intermediate facts.

Read Stacks curves.tex Tags 0CBT (remark-quadratic-extension), 0CBU (remark-trivial-quadratic-extension), 0CBW (lemma-split-node), 0C4A (lemma-2-branches-delta-1, both cases), and 0C4D (lemma-nodal). The equivalence with construction (3) in 0CBT is explicitly omitted: the intrinsic homogeneous-fraction argument is our agent-written completion of that omission, not a theorem falsely attributed to an explicit Stacks proof. Read varieties.tex Tag 0C3V (lemma-normalization-same-after-completion), morphisms.tex Tags 0C3B (lemma-stalk-normalization) and 0CDV (lemma-normalization-in-terms-of-components), and algebra.tex Tag 0307 (lemma-integral-closure-localize). No SGA source is used.

For every delivered new id the exact own-statement searches are in search-plan.json and its mathlib_searches: two LeanFinder phrasings, Loogle, source grep, and LeanSearch, all actually run through msearch.py. Results were read, including their signatures. The first general faithful-flat proposal was refined to the completed coefficient formula because the elementary descent fact alone should not become a new node. Likewise, I searched a possible new reduced-normalization-local-fibre node but did not create it after finding lem-trf-normalization-affine-stalk-closure. These exploratory searches remain in the log and are not fabricated entries for a delivered node.

Mathlib's FaithfullyFlat.tensorProduct_mk_injective and Ideal.comap_map_eq_self_of_faithfullyFlat, read in RingTheory/Flat/FaithfullyFlat/Algebra.lean, supply ingredients only; they do not state the completed denominator/residue formula. HomogeneousLocalization.map and awayMap, read in RingTheory/GradedAlgebra/HomogeneousLocalization.lean around 672 and 825, transport graded rings and homogeneous denominators; they do not send initial classes to quotients in a different ungraded algebra. AlgebraicGeometry.projIsoSpec at AlgebraicGeometry/ProjectiveSpectrum/Scheme.lean:847 identifies a standard chart with its homogeneous localization. It does not prove that this whole Proj is that chart or calculate its quadratic coefficient algebra and root labels. The general completion quotient results are reused through existing nodes rather than recreated as leaves. The grep hits for 'nodal' in Lagrange interpolation are unrelated to nodal local rings. The Weierstrass, Laurent-series, and projective-spectrum search hits do not state the new facts or specialize to them in one line. Thus this repair adds four unsplit nodes and zero Mathlib leaves.

## Review by Q36

I read the original proof against the actual source: 0CBT explicitly identifies the quadratic algebra through completion and normalization but leaves the Proj comparison to be proved. For the new completed-graded-model node I checked its reduced, dimension-one and essentially finite-type hypotheses against lem-trf-curve-normalization-completion, and its residue-preserving coefficient section against lem-sfb-separable-node-quadratic-completion. The original fraction compatibility is part of the cited normalization-completion statement, not an arbitrary abstract isomorphism. Its associated graded identification uses consecutive completion quotients; this new node includes that identification and the leading coefficient rule, rather than assuming them from a definition.

For completed-residue-denominators I checked the exact tensor quotient map, and tested the key descent on both B and B/fB using the universally injective map under completion. In L[[t]], ut+t^2h is t times a unit precisely when u is invertible, so regularity and ideal generation descend. No coefficient field in A is needed. The quotient comparison comes from R/mR=F; it is not descent of an abstract residue algebra. The degree-n residue is r/u^n, covering arbitrary admissible denominator lifts, not just the chosen Y.

For graded-normalization-fraction-map I checked that all its hypotheses are explicit and weaker than nodality: a local ring, an injective algebra, a regular f with mB=fB. A representative change by m^(n+1) changes d/f^n by mB, and a localization equality is killed by a further power of the regular f. Addition and multiplication use common denominators. For f,g both satisfying these hypotheses, g/f and f/g are mutually inverse; the displayed transition formula proves agreement of the two scheme maps on their overlap. I checked that transporting fractions and integral equations induces the required B-isomorphism in the normalization case. This node asserts only a homomorphism and its compatibilities; the parent must still prove it is an isomorphism.

For quadratic-coefficient-proj-branches I checked the standard-chart coverage, the coefficient identification for every unit u, and the branch description against 0CBT/0CBU and 0C4A. A homogeneous prime containing t contains the positive-degree part because every product of two positive-degree terms is divisible by t. The chart inverse takes r to rt/t. The discriminant excludes repeated roots including characteristic two. In changed coordinates, the coefficient of (X')^2 is nonzero exactly when the first coordinate vector is not on either zero line; hence Y' restricts nontrivially to both branches and its coefficient is a unit of L. Ordinary tensor products of power series rings are not confused with coefficientwise completed extension.

I opened the statement of EVERY parent proof citation. Step 1 uses separable-node-quadratic-completion for reducedness, local dimension, finite type and the quadratic presentation; completed-graded-model then supplies the compatible normalization and actual graded algebra. Step 2 uses completed-residue-denominators for ideal generation, regularity and the residue coefficient rule, then fraction-map for the well-defined algebra map. Step 3 uses quadratic-coefficient-proj-branches for the whole-chart assertion, completed-residue-denominators for the second coefficient formula, and fraction-map for independence and naturality. The fact that both coordinate maps agree on every homogeneous fraction proves invertibility; no unproved node is quoted for this last comparison. Step 4 uses the quadratic chart's root labels and lem-trf-separable-closed-point-formal-presentation's explicit base-change clause to connect them to the chosen geometric completed local ring. The finite separable residue-field hypothesis permits the embedding into the selected algebraic closure. Step 5 uses pqf-lem-locnoeth-lft to obtain a Noetherian chart, kills its finitely generated nilradical after localizing away from p, and applies lem-trf-normalization-affine-stalk-closure on that reduced finite-type chart. That node explicitly gives both normalization restriction to opens and the localized integral-closure algebra. The two affine pullbacks use precisely the projection-normalized isomorphism in lem-weil-pbc-fibre-product-affine-spectra. The final tensor quotient formula is immediate on pure tensors. Full verbatim relevant statements in citations.json cover each (step,node) pair; no quote was bent to make a citation pass.

I also read the statements of the older dependencies behind the extracted arguments: lem-sfb-quadratic-series-integral-closure supplies the image F+tL[[t]] and normalization, lem-weil-pbc-module-completion-complete gives the quotient kernels, and lem-weil-pbc-local-completion-faithfully-flat plus lem-weil-pbc-faithfully-flat-universally-injective give exactly the needed injections. In the retained step 10 the relative-normalization statement has an affine integral-closure clause, not just a definition of normality. The new assembly reuses the more direct existing affine/stalk statement for this same local argument.

Small-case checks: for R-real coefficients q=X^2+Y^2, L=C and the two branches appear only after algebraic closure. Over F_2, q=X^2+XY+Y^2 gives F_4 and q=X(X+Y) gives F_2 x F_2; both have nonzero discriminant. For the split coefficient algebra F x F, u=(1,0) is nonzero but not a unit, so the denominator hypotheses correctly exclude it. For f=t(1+th) and g=ut+t^2h' the residue transition is u and the coefficient formula gives r/u^n. A double line q=X^2 fails the discriminant hypothesis and is excluded. Nonrational finite separable residue fields enter via the supplied coefficient section, with no F-action assumed on A. Empty schemes have no selected x; every parent assertion is pointwise. No parent proof step exceeds 2000 characters (the longest is 780); there is no hidden long sub-argument in the assembly. The original calculations are retained below in full for their future workers.

## Preservation map for the returned proof

The complete returned proof is copied verbatim below, not shortened or replaced by a summary. Its work is assigned as follows:

- Old 1: apply the existing separable-node-quadratic-completion; coordinate choice is a conclusion of completed-graded-model, with its three-vector argument retained below.
- Old 2--3: completed-graded-model (normalization completion, F+tL[[t]], all powers, quotient kernels, graded multiplication and lift f).
- Old 4: quadratic-coefficient-proj-branches (whole standard chart and explicit coefficient localization).
- Old 5: completed-residue-denominators (both module injections, regularity, mB=fB, all powers).
- Old 6: graded-normalization-fraction-map (lift independence, the full localization equivalence relation, addition, multiplication and constants).
- Old 7: completed-residue-denominators (canonical tensor/quotient and coefficient identity); parent step 3 assembles that identity with the independent chart computation to prove invertibility.
- Old 8: completed-residue-denominators (units g/f and f/g), quadratic-coefficient-proj-branches (which changed coordinates are permitted), and graded-normalization-fraction-map (transition fractions, gluing and naturality).
- Old 9: quadratic-coefficient-proj-branches (quadratic alternatives, characteristic two, interpolation and root/branch labeling), with the existing formal-presentation base-change clause in parent step 4.
- Old 10: reuse existing lem-trf-normalization-affine-stalk-closure, which already states the affine product, local integral closure and open restriction, rather than duplicate its statement. Its full component/localization argument is retained below. Parent step 5 explicitly reduces to the lemma's hypotheses and computes the affine fibre.

The sizes of the four statement-only arguments are comparable (roughly 1.5--2.4 thousand characters). None contains the whole tangent-normalization theorem. They can be proved independently from their own hypotheses; their definitions do not depend on the parent.

## Not duplicates

- lem-sfb-graded-normalization-fraction-map vs def-sfb-nodal-branch-scheme: the new node states a general local algebra with mB=fB gives only the intrinsic homogeneous-fraction homomorphism, its full representative relations, overlap formula and naturality, not an isomorphism or nodal geometry; the existing node defines a relative branch scheme by blowing up a graph ideal and states no local quadratic comparison.

- lem-sfb-graded-normalization-fraction-map vs lem-sfb-graph-cone-gluing: the new node states a general local algebra with mB=fB gives only the intrinsic homogeneous-fraction homomorphism, its full representative relations, overlap formula and naturality, not an isomorphism or nodal geometry; the existing statement glues relative graph conormal algebras and their Proj, without quadratic coefficient or local fraction calculations.

- lem-sfb-graded-normalization-fraction-map vs lem-sfb-nodal-branch-double-cover: the new node states a general local algebra with mB=fB gives only the intrinsic homogeneous-fraction homomorphism, its full representative relations, overlap formula and naturality, not an isomorphism or nodal geometry; the existing statement constructs a relative finite etale branch cover of the singular locus for a flat family and uses the parent; citing it here would be circular.

- lem-sfb-graded-normalization-fraction-map vs lem-sfb-nodal-graph-cone-fibre: the new node states a general local algebra with mB=fB gives only the intrinsic homogeneous-fraction homomorphism, its full representative relations, overlap formula and naturality, not an isomorphism or nodal geometry; the existing statement compares a family graph-cone fibre and normalization and depends on the parent; it supplies no independent local proof here.

- lem-sfb-graded-normalization-fraction-map vs lem-sfb-nodal-local-tangent-normalization: the new node states a general local algebra with mB=fB gives only the intrinsic homogeneous-fraction homomorphism, its full representative relations, overlap formula and naturality, not an isomorphism or nodal geometry; the parent starts with a geometric node of a curve and concludes the intrinsic tangent-Proj/normalization-fibre isomorphism with all its scheme and branch clauses.

- lem-sfb-graded-normalization-fraction-map vs lem-trf-nodal-point-finite-separable-splitting: the new node states a general local algebra with mB=fB gives only the intrinsic homogeneous-fraction homomorphism, its full representative relations, overlap formula and naturality, not an isomorphism or nodal geometry; the existing statement produces a finite separable base extension splitting a geometric curve node.

- lem-sfb-graded-normalization-fraction-map vs lem-trf-quadratic-completion-separable-splitting: the new node states a general local algebra with mB=fB gives only the intrinsic homogeneous-fraction homomorphism, its full representative relations, overlap formula and naturality, not an isomorphism or nodal geometry; the existing statement splits the quadratic completed equation after an extension of degree at most two, with no graded chart or division-residue map.

- lem-sfb-nodal-completed-graded-model vs def-sfb-nodal-branch-scheme: the new node states a supplied local quadratic completion is compared with the original ring through every completion quotient, its associated graded multiplication, and the normalization-compatible fraction map; no Proj or geometric-node recognition is asserted; the existing node defines a relative branch scheme by blowing up a graph ideal and states no local quadratic comparison.

- lem-sfb-nodal-completed-graded-model vs lem-sfb-graph-cone-gluing: the new node states a supplied local quadratic completion is compared with the original ring through every completion quotient, its associated graded multiplication, and the normalization-compatible fraction map; no Proj or geometric-node recognition is asserted; the existing statement glues relative graph conormal algebras and their Proj, without quadratic coefficient or local fraction calculations.

- lem-sfb-nodal-completed-graded-model vs lem-sfb-nodal-branch-double-cover: the new node states a supplied local quadratic completion is compared with the original ring through every completion quotient, its associated graded multiplication, and the normalization-compatible fraction map; no Proj or geometric-node recognition is asserted; the existing statement constructs a relative finite etale branch cover of the singular locus for a flat family and uses the parent; citing it here would be circular.

- lem-sfb-nodal-completed-graded-model vs lem-sfb-nodal-graph-cone-fibre: the new node states a supplied local quadratic completion is compared with the original ring through every completion quotient, its associated graded multiplication, and the normalization-compatible fraction map; no Proj or geometric-node recognition is asserted; the existing statement compares a family graph-cone fibre and normalization and depends on the parent; it supplies no independent local proof here.

- lem-sfb-nodal-completed-graded-model vs lem-sfb-nodal-local-tangent-normalization: the new node states a supplied local quadratic completion is compared with the original ring through every completion quotient, its associated graded multiplication, and the normalization-compatible fraction map; no Proj or geometric-node recognition is asserted; the parent starts with a geometric node of a curve and concludes the intrinsic tangent-Proj/normalization-fibre isomorphism with all its scheme and branch clauses.

- lem-sfb-nodal-completed-graded-model vs lem-trf-nodal-point-finite-separable-splitting: the new node states a supplied local quadratic completion is compared with the original ring through every completion quotient, its associated graded multiplication, and the normalization-compatible fraction map; no Proj or geometric-node recognition is asserted; the existing statement produces a finite separable base extension splitting a geometric curve node.

- lem-sfb-nodal-completed-graded-model vs lem-trf-quadratic-completion-separable-splitting: the new node states a supplied local quadratic completion is compared with the original ring through every completion quotient, its associated graded multiplication, and the normalization-compatible fraction map; no Proj or geometric-node recognition is asserted; the existing statement splits the quadratic completed equation after an extension of degree at most two, with no graded chart or division-residue map.

- lem-sfb-nodal-completed-residue-denominators vs def-sfb-nodal-branch-scheme: the new node states an arbitrary injective algebra with supplied completed series model descends every regular unit-leading denominator and computes all division residues; it requires no curve or Proj; the existing node defines a relative branch scheme by blowing up a graph ideal and states no local quadratic comparison.

- lem-sfb-nodal-completed-residue-denominators vs lem-sfb-graph-cone-gluing: the new node states an arbitrary injective algebra with supplied completed series model descends every regular unit-leading denominator and computes all division residues; it requires no curve or Proj; the existing statement glues relative graph conormal algebras and their Proj, without quadratic coefficient or local fraction calculations.

- lem-sfb-nodal-completed-residue-denominators vs lem-sfb-nodal-branch-double-cover: the new node states an arbitrary injective algebra with supplied completed series model descends every regular unit-leading denominator and computes all division residues; it requires no curve or Proj; the existing statement constructs a relative finite etale branch cover of the singular locus for a flat family and uses the parent; citing it here would be circular.

- lem-sfb-nodal-completed-residue-denominators vs lem-sfb-nodal-graph-cone-fibre: the new node states an arbitrary injective algebra with supplied completed series model descends every regular unit-leading denominator and computes all division residues; it requires no curve or Proj; the existing statement compares a family graph-cone fibre and normalization and depends on the parent; it supplies no independent local proof here.

- lem-sfb-nodal-completed-residue-denominators vs lem-sfb-nodal-local-tangent-normalization: the new node states an arbitrary injective algebra with supplied completed series model descends every regular unit-leading denominator and computes all division residues; it requires no curve or Proj; the parent starts with a geometric node of a curve and concludes the intrinsic tangent-Proj/normalization-fibre isomorphism with all its scheme and branch clauses.

- lem-sfb-nodal-completed-residue-denominators vs lem-trf-nodal-point-finite-separable-splitting: the new node states an arbitrary injective algebra with supplied completed series model descends every regular unit-leading denominator and computes all division residues; it requires no curve or Proj; the existing statement produces a finite separable base extension splitting a geometric curve node.

- lem-sfb-nodal-completed-residue-denominators vs lem-trf-quadratic-completion-separable-splitting: the new node states an arbitrary injective algebra with supplied completed series model descends every regular unit-leading denominator and computes all division residues; it requires no curve or Proj; the existing statement splits the quadratic completed equation after an extension of degree at most two, with no graded chart or division-residue map.

- lem-sfb-quadratic-coefficient-proj-branches vs def-sfb-nodal-branch-scheme: the new node states a standalone quadratic coefficient graded ring has one explicit Proj chart and evaluation-labeled formal branches; no original local ring, uncompleted normalization comparison or family appears; the existing node defines a relative branch scheme by blowing up a graph ideal and states no local quadratic comparison.

- lem-sfb-quadratic-coefficient-proj-branches vs lem-sfb-graph-cone-gluing: the new node states a standalone quadratic coefficient graded ring has one explicit Proj chart and evaluation-labeled formal branches; no original local ring, uncompleted normalization comparison or family appears; the existing statement glues relative graph conormal algebras and their Proj, without quadratic coefficient or local fraction calculations.

- lem-sfb-quadratic-coefficient-proj-branches vs lem-sfb-nodal-branch-double-cover: the new node states a standalone quadratic coefficient graded ring has one explicit Proj chart and evaluation-labeled formal branches; no original local ring, uncompleted normalization comparison or family appears; the existing statement constructs a relative finite etale branch cover of the singular locus for a flat family and uses the parent; citing it here would be circular.

- lem-sfb-quadratic-coefficient-proj-branches vs lem-sfb-nodal-graph-cone-fibre: the new node states a standalone quadratic coefficient graded ring has one explicit Proj chart and evaluation-labeled formal branches; no original local ring, uncompleted normalization comparison or family appears; the existing statement compares a family graph-cone fibre and normalization and depends on the parent; it supplies no independent local proof here.

- lem-sfb-quadratic-coefficient-proj-branches vs lem-sfb-nodal-local-tangent-normalization: the new node states a standalone quadratic coefficient graded ring has one explicit Proj chart and evaluation-labeled formal branches; no original local ring, uncompleted normalization comparison or family appears; the parent starts with a geometric node of a curve and concludes the intrinsic tangent-Proj/normalization-fibre isomorphism with all its scheme and branch clauses.

- lem-sfb-quadratic-coefficient-proj-branches vs lem-trf-nodal-point-finite-separable-splitting: the new node states a standalone quadratic coefficient graded ring has one explicit Proj chart and evaluation-labeled formal branches; no original local ring, uncompleted normalization comparison or family appears; the existing statement produces a finite separable base extension splitting a geometric curve node.

- lem-sfb-quadratic-coefficient-proj-branches vs lem-trf-quadratic-completion-separable-splitting: the new node states a standalone quadratic coefficient graded ring has one explicit Proj chart and evaluation-labeled formal branches; no original local ring, uncompleted normalization comparison or family appears; the existing statement splits the quadratic completed equation after an extension of degree at most two, with no graded chart or division-residue map.

- lem-sfb-quadratic-coefficient-proj-branches vs lem-trf-stacks-nodal-closed-subcurve: the new node states a standalone quadratic coefficient graded ring has one explicit Proj chart and evaluation-labeled formal branches; no original local ring, uncompleted normalization comparison or family appears; the existing statement concerns preservation of split nodes and finite intersections under passage to closed subcurves.

- lem-sfb-nodal-completed-graded-model vs lem-sfb-quadratic-series-integral-closure: the existing node computes only the complete quotient's series normalization; the new node also identifies the uncompleted local ring's quotient tower and associated graded algebra through canonical completion maps.
- lem-sfb-quadratic-coefficient-proj-branches vs lem-sfb-quadratic-series-field-factors: the existing node decomposes the series coefficient algebra into fields and proves normality, integrality and module finiteness; the new node computes a graded Proj, root labels and admissible coordinate changes. Its split/field algebra calculation is shared background, not a new standalone duplicate of that existing statement.
- lem-sfb-nodal-completed-graded-model vs lem-sfb-quadratic-homogeneous-substitution: the latter is a formal substitution image/kernel statement even for degenerate quadrics, whereas the new node compares an uncompleted local ring and its normalization with the supplied completed model and computes its graded algebra.
- Proposed lem-sfb-reduced-normalization-local-fibre vs lem-trf-normalization-affine-stalk-closure: the existing affine and stalk integral-closure clause supplies the needed content on a reduced finite-type neighbourhood. No new node was created.

## Returned proof, preserved verbatim

### Returned step 1

Apply [lem-sfb-separable-node-quadratic-completion] at $x$. Thus $A$ is reduced, Noetherian, essentially of finite type over $k$, and of dimension one. Set $R=\widehat A$ and fix the resulting presentation $R=\kappa[[X,Y]]/(q)$, with $q=aX^2+bXY+cY^2$ and $b^2-4ac\ne0$. We may arrange $a\ne0$ by an invertible linear change of coordinates: one of $q(1,0),q(0,1),q(1,1)$ is nonzero, since their simultaneous vanishing forces $a=b=c=0$. Take that vector as the first basis vector. This argument also works over $\mathbf F_2$.

Uses: lem-sfb-separable-node-quadratic-completion

Source: literature/stacks-project/curves.tex — Tags 0C4D and 0C49: reduction to a quadratic completed equation

### Returned step 2

Put $B=A^\nu$ and $L=\kappa[Z]/(aZ^2+bZ+c)$. Since $A$ is reduced of dimension one and essentially of finite type, [lem-trf-curve-normalization-completion] applies: $B$ is finite over $A$ and canonically $\widetilde B:=B\otimes_A R$ is the integral closure of $R$ in its total fractions. Apply [lem-sfb-quadratic-series-integral-closure] to identify $\widetilde B=L[[t]]$, with $X\mapsto zt$, $Y\mapsto t$, and $R=\kappa+tL[[t]]$ inside it. In particular $\mathfrak m\widetilde B=tL[[t]]$. The normalization/completion map agrees with the original fractions of $A$; it is not an arbitrary isomorphism of abstract normalization rings.

Uses: lem-trf-curve-normalization-completion, lem-sfb-quadratic-series-integral-closure

Source: literature/stacks-project/curves.tex — Tag 0C4A, reduction to completion and Cases I--II; Varieties Tag 0C3V

### Returned step 3

For $n\ge1$, the maximal ideal of $R=\kappa+tL[[t]]$ has $n$th power $t^nL[[t]]$: the inclusion of a product is immediate, and $t^nh=t^{n-1}(th)$ gives the reverse inclusion. Thus its associated graded ring is
$$G=\kappa\oplus\bigoplus_{n\ge1}Lt^n\subset L[t],$$
with multiplication induced from $L[t]$. By [lem-weil-pbc-module-completion-complete] with $M=A$ and $I=\mathfrak m$, the canonical completion maps identify $A/\mathfrak m^n$ with $R/\mathfrak m^nR$ for every $n$. Taking kernels of consecutive quotient maps and using multiplication identifies $\operatorname{gr}_{\mathfrak m}A$ with this $G$. Choose $f\in\mathfrak m$ lifting the degree-one class of $Y$, and put $\ell=\operatorname{in}(f)$. Under this graded identification $\ell=t$, and the image of $f$ in $L[[t]]$ is $t(1+th)$ for some $h\in L[[t]]$.

Uses: lem-weil-pbc-module-completion-complete, def-weil-pbc-associated-graded-ring

Source: literature/stacks-project/curves.tex — Tag 0CBT construction (3), explicit graded calculation in the model from Tag 0C4A

### Returned step 4

The whole tangent Proj $T=\operatorname{Proj}G$ is $D_+(\ell)$. Indeed every product of two positive-degree homogeneous elements of $G$ belongs to $(t)$, since $Lt^{i+j}=t(Lt^{i+j-1})$ for $i,j\ge1$. A homogeneous prime containing $t$ therefore contains all positive-degree elements and is excluded from Proj. The standard-chart definition of [def-nagata-affine-proj] now gives
$$T=\operatorname{Spec}(G[\ell^{-1}]_0),\qquad G[\ell^{-1}]_0=L,$$
where $rt^n/t^n$ maps to $r$. This is an explicit localization calculation: every degree-zero fraction has that form, and equality is equality of its coefficient in $L$.

Uses: def-nagata-affine-proj

Source: literature/stacks-project/curves.tex — Tag 0CBT construction (3), omitted equivalence, single standard Proj chart

### Returned step 5

We next descend the denominator calculation. The completion map $A\to R$ is faithfully flat by [lem-weil-pbc-local-completion-faithfully-flat]. For every $A$-module $M$, [lem-weil-pbc-faithfully-flat-universally-injective] makes $M\to M\otimes_A R$ injective. In $\widetilde B=L[[t]]$, the element $f=t(1+th)$ is a non-zero-divisor and generates $\mathfrak m\widetilde B$. If $fb=0$ in $B$, injectivity for $M=B$ gives $b=0$. For $a\in\mathfrak m$, its class in $B/fB$ maps to zero in $(B/fB)\otimes_A R=\widetilde B/f\widetilde B$; injectivity for this module gives $a\in fB$. Here the tensor/quotient identity follows directly by sending $[b]\otimes r$ to $[b\otimes r]$, whose inverse is induced by the same formula. Hence $\mathfrak mB=fB$ and $\mathfrak m^nB=f^nB$. Since $A\subset B$, the element $f$ is also a non-zero-divisor of $A$.

Uses: lem-weil-pbc-local-completion-faithfully-flat, lem-weil-pbc-faithfully-flat-universally-injective, def-weil-pbc-module-tensor-product

Source: literature/stacks-project/curves.tex — Tag 0C4A completion reduction; Tag 0CBT omitted comparison, faithful-flat denominator descent

### Returned step 6

Put $E=B/\mathfrak mB$. Define a $\kappa$-algebra map
$$\theta_f:G[\ell^{-1}]_0\longrightarrow E,\qquad \frac{\operatorname{in}_n(a)}{\ell^n}\longmapsto \frac{a}{f^n}\bmod\mathfrak mB\quad(a\in\mathfrak m^n).$$
The quotient $a/f^n$ is a unique element of $B$ by step 5. Replacing $a$ by an element congruent modulo $\mathfrak m^{n+1}$ changes that quotient by an element of $\mathfrak mB$. Multiplying numerator and denominator by $\ell$ changes $a/f^n$ to $fa/f^{n+1}$ and hence changes nothing. More generally an equality after multiplying homogeneous numerators by a further power of $\ell$ gives the same residues by division by the corresponding power of $f$. These are exactly the localization equivalence relations. Common denominators verify addition, multiplication, and the unit; constants act through $A/\mathfrak m=\kappa$. Thus the formula defines the stated map without a coefficient-field choice in $A$.

Uses: def-weil-pbc-associated-graded-ring, def-nagata-affine-proj

Source: literature/stacks-project/curves.tex — Tag 0CBT omitted equivalence: explicit comparison on the standard chart

### Returned step 7

The canonical map $E\to\widetilde B/\mathfrak m\widetilde B$ is an isomorphism. Explicitly the tensor universal property identifies the latter quotient with $B\otimes_A(R/\mathfrak mR)=B\otimes_A\kappa=B/\mathfrak mB$: $b\otimes\bar a\mapsto ab\bmod\mathfrak mB$ is inverse to $[b]\mapsto b\otimes1$. Use the completion residue identification from step 3. The model of step 2 identifies this quotient with $L$ by constant term. Under the chart identification of step 4, $\theta_f$ is the identity of $L$: if $a$ has leading term $rt^n$ and $f=t(1+th)$, then $a/f^n$ has constant term $r$. Thus $\theta_f$ is an isomorphism. Taking its spectrum gives $\operatorname{Spec}E\xrightarrow{\sim}T$; its inverse is the isomorphism required in the statement.

Uses: def-weil-pbc-module-tensor-product

Source: literature/stacks-project/curves.tex — Tag 0CBT omitted equivalence, verification against the completed quadratic model

### Returned step 8

The isomorphism does not depend on $f$. Call $g\in\mathfrak m$ permitted when, under step 3, $\operatorname{in}(g)=ut$ with $u\in L^\times$; then $g$ maps to $ut(1+th')$ in $L[[t]]$ and step 5 applies verbatim, so $\mathfrak mB=gB$. The lift $f$ of the second coordinate of any presentation as in step 1 is permitted: if that coordinate has class $\alpha\bar X+\beta\bar Y$ in $\mathfrak m/\mathfrak m^2$, its initial form is $(\alpha z+\beta)t$, and $\alpha z+\beta$ is a unit of $L$ because, over an algebraic closure, $\alpha r_i+\beta=0$ would put the first basis vector of that presentation on a zero line of $q$, contradicting its leading coefficient being nonzero. For permitted $f,g$, $g/f$ is a unit of $B$ with inverse $f/g$. On the two Proj charts, the coordinate change rewrites
$$\frac{\operatorname{in}_n(a)}{\operatorname{in}(g)^n}=\frac{\operatorname{in}_n(a)}{\operatorname{in}(f)^n}\left(\frac{\operatorname{in}(g)}{\operatorname{in}(f)}\right)^{-n}.$$
Under $\theta_f$ the right side is $(a/f^n)(g/f)^{-n}=a/g^n$ modulo $\mathfrak mB$, exactly the formula for $\theta_g$. Thus the maps agree. A pointed local-ring isomorphism transports total fractions and monic integral equations, hence transports $B$, $E$, $f$, and every fraction in this formula. The formula therefore commutes with it. The completed presentation was used only to prove existence and invertibility of this intrinsic map.

Uses: def-weil-pbc-integral-closure, def-nagata-affine-proj

Source: literature/stacks-project/curves.tex — Tag 0CBT: canonical character of the associated quadratic algebra, coordinate-change verification

### Returned step 9

The algebra $E=L=\kappa[Z]/(aZ^2+bZ+c)$ has basis $1,z$ because $a\ne0$. The discriminant $b^2-4ac\ne0$ says the polynomial has no repeated root, including in characteristic two (where $b\ne0$). If it is irreducible, its quotient is a separable field of degree two. If it is reducible, write it as $a(Z-r_1)(Z-r_2)$ with $r_1\ne r_2$. Evaluation at $r_1,r_2$ is an isomorphism onto $\kappa^2$, with inverse $(s_1,s_2)\mapsto s_1(z-r_2)/(r_1-r_2)+s_2(z-r_1)/(r_2-r_1)$. Over an algebraic closure these two distinct roots always exist. Substitution $X=r_iY$ gives the two factors of the normalized completed node; the chart coordinate $X/Y=z$ evaluates to $r_i$ on the same factor. This proves the asserted branch correspondence. Scalar extension of the formal model means the power series model with extended coefficients; its equality with the geometric completed local ring follows from the base-change clause of [lem-trf-separable-closed-point-formal-presentation], applied to the presentation of step 1.

Uses: lem-trf-separable-closed-point-formal-presentation

Source: literature/stacks-project/curves.tex — Tags 0C4A, 0CBU, 0CBW: split/nonsplit alternatives and the two branches; Varieties 0C54 for geometric completion

### Returned step 10

As $k$ is Noetherian, [pqf-lem-locnoeth-lft] makes $C$ locally Noetherian; choose an affine open $U=\operatorname{Spec}S\ni x$ with $S$ Noetherian, with $x=\mathfrak p$, $A=S_{\mathfrak p}$. By [def-weil-pbc-reduced-normalization], $C^\nu$ is the disjoint union over the irreducible components $Z$ of $C$ of the normalizations $Z^\nu\to Z$ [def-sc-normalization] of their reduced structures, so $\nu^{-1}(U)=\coprod_Z\nu_Z^{-1}(Z\cap U)$. The components meeting $U$ are the closures of the finitely many minimal primes $\mathfrak p_1,\dots,\mathfrak p_t$ of $S$, with $Z_i\cap U=\operatorname{Spec}(S/\mathfrak p_i)$ and function field $K_i=\operatorname{Frac}(S/\mathfrak p_i)$. The constant sheaf $K_i$ on $Z_i$ is the direct image of $\mathcal O$ along $\operatorname{Spec}K_i\to Z_i$ (qcqs: its source is one point), so $Z_i^\nu$ is the relative normalization of [lem-weil-pbc-relative-normalization], whose clause (iii) gives $\nu_{Z_i}^{-1}(Z_i\cap U)=\operatorname{Spec}B_i$ with $B_i$ the integral closure of $S/\mathfrak p_i$ in $K_i$. Hence $\nu^{-1}(U)=\operatorname{Spec}(\prod_iB_i)$, and by [lem-weil-pbc-fibre-product-affine-spectra] its pullback to $\operatorname{Spec}A$ is $\operatorname{Spec}(\prod_i(B_i)_{\mathfrak p})$. By [lem-weil-pbc-integral-closure-commutes-localization], $(B_i)_{\mathfrak p}$ is $0$ if $\mathfrak p_i\not\subseteq\mathfrak p$ and otherwise the integral closure of $A/\mathfrak p_iA$ in $K_i$. The $\mathfrak p_iA$ with $\mathfrak p_i\subseteq\mathfrak p$ are the minimal primes of the reduced Noetherian $A$, and [lem-weil-pbc-reduced-noetherian-total-ring-fractions] gives $Q(A)=\prod K_i$; a monic equation is checked componentwise (conversely multiply component monic equations), so this product is $B$. Thus $C^\nu\times_C\operatorname{Spec}A=\operatorname{Spec}B$, and by [lem-weil-pbc-fibre-product-affine-spectra] again its fibre at $\kappa$ is $\operatorname{Spec}(B\otimes_A\kappa)=\operatorname{Spec}(B/\mathfrak mB)$ (step 7).

Uses: pqf-lem-locnoeth-lft, def-weil-pbc-reduced-normalization, def-sc-normalization, lem-weil-pbc-relative-normalization, lem-weil-pbc-fibre-product-affine-spectra, lem-weil-pbc-integral-closure-commutes-localization, lem-weil-pbc-reduced-noetherian-total-ring-fractions

Source: literature/stacks-project/curves.tex — Tag 0CBT final paragraph; normalization of an integral scheme on affine opens Morphisms Tag 035H (relative normalization) and integral closure localization Tag 0307
