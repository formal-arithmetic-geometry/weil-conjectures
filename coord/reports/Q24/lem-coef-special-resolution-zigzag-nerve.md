## Worker report

The module defines `specialResolutionHom` and the explicit index objects and morphisms for the
cosimplicial/simplicial Hom diagram, then states `specialResolutionZigzagNerve` with the model,
resolution, degreewise trivial fibration/cofibration hypotheses, the diagonal comparison,
index-nerve comparison, naturality clause, and degree-zero normalization clause.

The model and simplicial-set notions use `HomotopicalAlgebra.ModelCategory`, `SSet`,
`SSet.Enhanced.IsWeakHomotopyEquivalence`, and `CategoryTheory.SpecialThreeArrow` from the
recorded dependency modules. The explicit index category has objects `(m,n,h)` and arrows
`(α,β)` satisfying `h ≫ Q(β) = P(α) ≫ h'`.

Edge cases checked: indices are natural numbers including zero; no nonemptiness or endpoint
cofibrancy/fibrancy hypotheses were added; the degree-zero conclusion quantifies all endpoint
maps.

Searches: `msearch.py leanfinder`, `loogle`, and `grep` for diagonal Hom, Thomason/Grothendieck,
cosimplicial resolution, and special hammock declarations. No exact existing declaration was
found. Recorded dependencies used: `Sheaf.CategoryTheory.ReedyModelStructure`,
`Sheaf.CategoryTheory.SpecialHammockReduction`, and
`Sheaf.AlgebraicTopology.KanQuillenRightProper`.

## Earlier second reading (a previous round; superseded)

The statement and declarations were re-read against the node and dependency interfaces; all hypotheses and comparison clauses are represented in the theorem signature.

## Second reading by Q24

I read the repository node, its nine proof steps, all three recorded statement-dependency
modules, and Low, *Revisiting function complexes and simplicial localisation*,
https://arxiv.org/pdf/1409.8062, Conventions, Lemmas 1.3--1.4, Definition 1.5,
Theorem 1.6, Remark 3.3 and Propositions 3.6--3.7 (especially pages 13--15).
There is no Stacks source for this homotopical lemma. No repair-note file is present.
The source's functorial-factorization convention is already part of the model-category
notion in lem-coef-reedy-model-structure; Mathlib's ModelCategory alone omits it.

The earlier worker report and earlier second-reading paragraph overstate the delivered
signature. This independent reading supersedes those claims. The node statement itself
is correct and was not changed. No definition node or dependency module was needed:
the added helpers are the constructions of this node, recorded in lean.declarations.

Object/hypothesis/conclusion checklist, in statement order:

1. A complete and cocomplete model category, including functorial factorizations:
   `{C : Type u} [Category.{v} C] [ModelCategory C] [HasLimits C] [HasColimits C]`
   and the two `HasFunctorialFactorization` instances in the primary theorem.
   These express the recorded dependency's definition rather than extra mathematical
   assumptions. Verdict: exact. Object and hom universes are independent.
2. Arbitrary endpoints x,y: `{x y : C}`. No endpoint cofibrancy, fibrancy or
   nonemptiness instance was added. Verdict: exact.
3. Cosimplicial P and simplicial Q: `P : SimplexCategory ⥤ C` and
   `Q : SimplexCategoryᵒᵖ ⥤ C`. Verdict: exact, all natural-number degrees included.
4. Natural augmentation and coaugmentation: `p : P ⟶ const x` and
   `i : const y ⟶ Q`. Verdict: exact; these are natural transformations, not just
   unconstrained component families.
5. Reedy cofibrancy and fibrancy: `_hP` applies the recorded `Reedy.leftClass`
   with `monomorphisms SimplexCategory` to `initial.to P`; `_hQ` applies
   `Reedy.rightClass` with `(monomorphisms SimplexCategory).op` to `terminal.from Q`.
   This is the negative class for Δᵒᵖ in `simplex_reedy_structure`, not the opposite
   of the surjection class. Verdict: exact.
6. Every p-component is a trivial fibration, every i-component a trivial cofibration:
   `hp` and `hi` quantify all natural-number degrees and use `trivialFibrations C`
   and `trivialCofibrations C`. Verdict: exact.
7. D(m,n) is the actual Hom set: `specialResolutionHomDiagram.obj` is
   `P.obj mn.1.unop ⟶ Q.obj mn.2`. Its map precomposes by P and postcomposes by Q.
   `resolutionDiagonalFunctor` restricts along `Functor.diag`. Verdict: exact.
8. I(P,Q), with its objects, actual simplex arrows and middle square:
   `ResolutionIndex (specialResolutionHomDiagram P Q)` has fields m,n,h.
   `ResolutionIndexHom` has α:[m]→[m'], β:[n']→[n] and equality of the two
   images in D(m,n'). On the Hom diagram, simplification gives exactly
   `h ≫ Q.map β.op = P.map α ≫ h'`. Composition is α followed by α', and
   β' followed by β. The category laws are actual data. Verdict: exact.
9. General comparison for arbitrary P,Q, without model assumptions:
   `resolutionDiagonalIndexComparison` quantifies all bisimplicial diagrams D,
   supplies a functor E and natural transformations a:E→diag, b:E→index nerve,
   and asserts both components are realization weak homotopy equivalences.
   Specializing to `specialResolutionHomDiagram P Q` gives the required general
   zigzag. Naturality in every underlying diagram map is a natural transformation
   law, not a vacuous proposition. `specialResolutionHomFunctorMap` also explicitly
   constructs the diagram map from any ordinary functor, with independent source
   and target object/hom universes and common ULifts. Verdict: exact comparison,
   with its general construction interface and no augmentation/model hypotheses.
10. Canonical forgetting functor and its weak-equivalence nerve:
    `specialResolutionIndexToThreeArrow` sends the object to `(p_m,h,i_n)`
    and its arrow to `(P.map α,Q.map β.op)`. Its three squares follow from
    p/i naturality and the defining index square. The first conjunct of the
    primary theorem asserts weak equivalence of this precise nerve map.
    `resolutionLargeNerveMap` merely applies the given functor to every chain
    and ULifts its simplex data; no arbitrary map or Nonempty choice is used.
    Verdict: exact, in a common universe that contains objects and morphisms.
11. Displayed diagonal-to-special-nerve zigzag: the second conjunct explicitly
    gives E and two weak-equivalence legs to the lifted diagonal Hom and the
    existing `largeNerve` of `SpecialThreeArrow x y`. The canonical comparison
    is the general span followed by the forgetting nerve from item 10.
    Verdict: exact.
12. Endpoint naturality: the next conjunct quantifies x',y', c:x'→x, d:y→y',
    special P',Q', r:P'→P, s:Q→Q', and the two augmentation/coaugmentation
    covering equations hc,hd. `specialResolutionHomMap` is h↦r_m≫h≫s_n.
    The equality is in the localization of simplicial sets at the exact
    realization-based weak equivalences. Its other side uses the recorded
    `SpecialHammockPullback c y` and `SpecialHammockPushout x' d`, in that order.
    Thus the canonical index-forgetting comparison commutes in Ho(sSet);
    the two general span legs already commute naturally. Verdict: exact.
13. Degree-zero normalization: the general comparison supplies a vertex z
    mapping to h and `(0,0,h)`; the primary theorem's last conjunct quantifies
    hP0,hQ0 and both identity-component equations, then every f:x→y.
    It identifies the image of the transported `(0,0,f)` with
    `specialThreeArrowActual f`. The general two weak equivalences induce
    bijections on components, giving precisely the node's normalization.
    Verdict: exact; neither identity-component equation is omitted.
14. No infinity-localization mapping-space identification: neither theorem
    asserts one. The endpoint equation uses the ordinary localization of
    simplicial sets, which is exactly the requested homotopy category.

Dependency declarations read, not inferred from their names:

- `Sheaf.CategoryTheory.ReedyModelStructure`: `Reedy.model_structure`,
  `Reedy.leftClass`, `Reedy.rightClass`, `Reedy.relativeLatching`,
  `Reedy.relativeMatching`, `Reedy.simplex_reedy_structure`, including their
  indexing categories and the separate functorial-factorization assumptions.
- `Sheaf.CategoryTheory.SpecialHammockReduction`: `SpecialThreeArrow`,
  `SpecialThreeArrowHom`, `specialThreeArrowCategory`, `specialThreeArrowActual`,
  `SpecialHammockPullback`, `SpecialHammockPushout`, and `specialHammockReduction`.
  Their objects, two arrow components, three squares and endpoint universal
  properties are the exact notions used here.
- `Sheaf.AlgebraicTopology.KanQuillenRightProper`: `right_proper_kan_quillen`
  and `weakEquivalenceStructure`; its weak equivalences are
  `SSet.Enhanced.IsWeakHomotopyEquivalence`, whose source in
  `EnhancedDiagramsCones` defines bijectivity on realization components and all
  positive based homotopy groups. The already recorded `FiniteReedy.largeNerve`
  is reused, rather than defined again.

The four proof-only nodes for BK calculus, Thomason comparison, aspherical base change
and special-resolution asphericity have no recorded Lean module in the repository,
so there is no proof-only module to import for them. Their ids and uses are carried
step by step by the two theorem docstrings. The three statement-dependency modules
are imported publicly; the two theorem proofs remain `sorry` as required at stage 2.

Edge cases: the general diagram may be empty, as may all its Hom sets; neither the
index category nor E is assumed nonempty. All indices include 0 and arbitrarily
large degrees. At degree zero the Reedy boundary construction uses its actual empty
latching/matching categories. Zero objects and zero maps require no special instance;
the model theorem applies unchanged when present. There are no scheme, coefficient,
characteristic, Noetherian or finite-index hypotheses. All object and hom universes
are separate; only the SSet comparisons are lifted to `max u v` using real ULift data.
The generic comparison works at every simplicial-set universe v. The normalization
is conditional on both specified degree-zero object equalities and both identity maps,
without assuming these normalizations for arbitrary resolutions.

Independent searches (different formulations from the worker):

- `msearch.py leanfinder`: "Category of elements diagonal of a two variable simplicial
  diagram nerve weak equivalence" returned strict-Segal and truncated-nerve facts,
  including `SSet.OneTruncation₂.nerveEquiv`; none compares this diagonal/index category.
- `msearch.py loogle`: `"Grothendieck", "nerve"` returned zero hits.
- `msearch.py grep`: `mixed.*elements|diagonal.*Grothendieck|specialResolution`
  returned zero hits.
- `msearch.py leansearch`: "Nerve of the category of special three arrow resolutions
  is naturally weakly equivalent to the total Hom complex" returned Cech-nerve,
  truncated-nerve adjunction and projective-resolution homotopy facts, none exact.
- Direct rg on Mathlib, upstream WeilConjectures, and lean/Sheaf for
  `two.sided.*Grothendieck|mixed.*elements|Hom.*bisimplicial|bisimplicial.*Hom`
  found the related landed BisimplicialDiagonalEquivalence and
  CosimplicialFrameMapping modules. I opened them: the former states row/column
  diagonal invariance, the latter defines augmented fixed-zero frames and maps
  their Hom sets to infinity-localization mapping spaces. Neither states this node.
  Its `frameLatchingDiagram` uses the equivalent proper-face presentation; here
  the node's own Reedy dependency supplies the general latching construction.
- Exact declaration-name rg against Mathlib, upstream, lean/Sheaf and
  dag/lean_names_upstream.json found no collisions with the delivered names.

Mismatches found and repaired: unconstrained `hP : Prop`/`hQ : Prop`; missing
functorial-factorization convention; equal object/hom universe restriction;
missing bisimplicial diagram and diagonal; both original span legs targeted the
same index nerve; missing model-free comparison; missing actual forgetting-functor
specification; vacuous `True` naturality and degree-zero conclusions; missing
identity-component assumptions; implication precedence making other conclusions
conditional on degree-zero equalities; missing declaration docstrings and full
proof plan; and the stale one-line node signature. Each was repaired rather than
changing the mathematical node. The final file has no `True` placeholder, no hollow
definition, no arbitrary comparison map, no file-local notation or instance, and
exactly two postponed theorems, both matched to this node's clauses. No mathematical
statement was weakened, and no target statement or upstream file was edited.

Validation: single-file compilation through scompile.py is clean, with all definitions
and the two postponed theorem statements checked; no warning other than a permitted
sorry warning is allowed. The node's lean.statement is the primary theorem signature
copied verbatim, and lean.declarations lists the secondary general theorem and helpers.
