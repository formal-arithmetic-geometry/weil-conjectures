## Worker report

The module `Sheaf.RepresentationTheory.JointContinuousCoordinateDifferential` states
`ContinuousCohomology.exists_jointContinuousCoordinateDifferential` with one `sorry`.
It states every clause of the unchanged DAG node. The source read was
`literature/stacks-project/etale-cohomology.tex`, section-continuous-group-cohomology,
Tag 0DVG, especially the displayed general and degree-zero differentials. As the node
explicitly says, the homogeneous calculation is its agent-written verification, not a
verbatim theorem of Stacks. The theorem docstring includes all eight proof steps.
No definition or independent missing notion is introduced, and no dependency needs repair.

Hypotheses, one by one:

- The field is `(E : Type u) [Field E]`, using the exact `mathlib_match` of
  `def-weil-field`: `Field`, defined in `Mathlib.Algebra.Field.Defs` (read its full
  signature and docstring). It is imported transitively through
  `Mathlib.Topology.Algebra.Field`.
- `[TopologicalSpace E] [IsTopologicalDivisionRing E]` says addition and multiplication
  are jointly continuous and inversion is continuous away from zero. This class also
  records continuous negation, already forced by multiplication by the constant -1;
  it therefore adds no mathematical assumption to the node. It imposes no separation axiom.
- `(J : Type v) [Group J] [TopologicalSpace J] [IsTopologicalGroup J]` is precisely the
  group with continuous multiplication and inversion.
- `(V : Type w) [AddCommGroup V] [Module E V] [TopologicalSpace V]` is the topologized
  E-vector space. `[ContinuousAdd V] [ContinuousSMul E V]` are exactly its two stated
  joint continuity conditions. No continuity of negation is added as an assumption.
- `(ρ : J →* V ≃ₗ[E] V)` is an E-linear group action: the monoid homomorphism laws
  encode identity and composition, and a group action acts by invertible linear maps.
  `hρ : Continuous (fun p : J × V ↦ ρ p.1 p.2)` is exactly joint continuity of the action.
- All three universes are explicitly bound and independent. Pi types `Fin n → J`
  carry the product topology automatically; the whole theorem has no compactness,
  Hausdorffness, or discreteness hypotheses.

Conclusions, one by one (in their Lean order):

1. `B : ∀ n, Submodule E ((Fin (n + 1) → J) → V)` together with the first membership
   equivalence defines exactly the jointly continuous equivariant homogeneous functions.
   The equality is `F (fun i ↦ a * x i) = ρ a (F x)` for every a and x.
2. `C : ∀ n, Submodule E ((Fin n → J) → V)` and the second membership equivalence
   define exactly the continuous inhomogeneous functions. Being ambient submodules
   makes both spaces' operations pointwise. Existential submodules with exact carrier
   predicates are uniquely determined, not arbitrary replacement vector spaces.
   In degree zero there is exactly one empty tuple `Fin.elim0 : Fin 0 → J`; evaluation
   at it canonically identifies `C 0` with V, with inverse the constant function.
   Every function on this singleton domain is continuous for every topology on V.
3. The quantified `Φ : ∀ n, B n →ₗ[E] C n` is fixed on every argument by
   `(Φ n F).val g = F.val (Fin.partialProd g)`. Mathlib's existing `Fin.partialProd`
   is exactly P: its definition takes the ordered product of the first i entries.
4. `Ψ : ∀ n, C n →ₗ[E] B n` is fixed by
   `(Ψ n f).val x = ρ (x 0) (f.val (fun i ↦ (x i.castSucc)⁻¹ * x i.succ))`.
   This is precisely x0 acting on f composed with the successive-ratio tuple r.
5. `δ : ∀ n, B n →ₗ[E] B (n + 1)` states well-definedness and E-linearity of the
   omission differential. Its formula sums over `Fin (n + 2)` with scalar sign
   `(-1 : E) ^ i.val`; `x ∘ i.succAbove` deletes exactly coordinate i.
6. `d : ∀ n, C n →ₗ[E] C (n + 1)` states well-definedness and E-linearity of the
   coordinate differential. The first term is `ρ (g 0) (f.val (Fin.tail g))`.
   The sum over `i : Fin (n + 1)` with sign `(-1 : E) ^ (i.val + 1)` combines the
   paper's internal sum and final term: for i<n, `Fin.contractNth i (· * ·) g`
   merges the adjacent entries i and i+1; for i=n it is `Fin.init g`, since each
   k in Fin n is less than n. Thus the final sign is exactly (-1)^(n+1).
7. The separate degree-zero equation
   `(d 0 f).val (fun _ ↦ g) = ρ g (f.val Fin.elim0) - f.val Fin.elim0`
   is explicitly gv-v under the canonical identification in point 2.
8. `(δ (n + 1)).comp (δ n) = 0` is the asserted square-zero identity as linear maps.
9. `(Φ (n + 1)).comp (δ n) = (d n).comp (Φ n)` is the coordinate intertwining
   identity as linear maps, hence for every homogeneous F as required.
10. The first-face equation evaluates F at `Fin.tail (Fin.partialProd g)` and gives
    `ρ (g 0) ((Φ n F).val (Fin.tail g))`. This is the omitted p0 face, whose sign
    is +1 from point 5.
11. Internal faces are quantified over `i : Fin n`. The paper's face index is i.val+1,
    so `i.succ.castSucc.succAbove` omits p(i+1), while `i.castSucc` in
    `Fin.contractNth` merges the corresponding adjacent arguments. The displayed
    equation is exactly the paper's internal-face equation, and point 5 gives its
    sign (-1)^(i.val+1).
12. The last-face equation evaluates F at `Fin.init (Fin.partialProd g)` and Phi F
    at `Fin.init g`, exactly F(p0,...,pn) = Phi F(g1,...,gn). Its omission index is
    n+1, so its sign from point 5 is (-1)^(n+1).

All maps are completely specified on their exact function subspaces. No map is chosen
from an uncharacterized existence statement, and no definition uses sorry. The theorem
only postpones the proofs of these properties. The only statement dependency is the
Mathlib `Field` declaration. `proof_deps` is empty. No downstream coordinate-complex
module is imported, so this bottom-up lemma does not depend on its consumer.

Edge cases checked by reading the finite-tuple definitions:

- n=0: `Fin 0` is empty and its function type into J is a singleton. P is the tuple
  (1); r is empty. Phi evaluates at 1, and Psi sends v to x0 acting on v.
  The omission differential has two terms; d is gv-v; there are no internal faces.
- n=1: there is exactly one internal face, with omission index 1 and contracted tuple
  (g1*g2). The final term has sign +1. No off-by-one overlap occurs.
- Characteristic two: the scalar signs live in E, so paired equal signs cancel by
  1+1=0 there. The statement has no characteristic restriction.
- The trivial group and zero vector space are allowed. Arbitrary non-Hausdorff
  topologies satisfying the hypotheses are allowed, including indiscrete topologies.
- Noncommutative J is allowed: `Fin.partialProd` is an ordered list product and
  `Fin.contractNth` multiplies only adjacent entries in their given order.

Searches (all performed before finalizing the statement):

- `msearch.py ... leanfinder`: "Alternating omission differential on jointly continuous
  equivariant homogeneous cochains squares to zero and becomes the inhomogeneous
  differential under cumulative products". Eight hits, including algebraic
  `inhomogeneousCochains.d_hom_apply`, `inhomogeneousCochains.d`, and
  `ContinuousCohomology.MultiInd.d_comp_d`; no exact joint-function-space statement.
- `msearch.py ... leansearch`: "Jointly continuous homogeneous equivariant group cochain
  alternating omission differential cumulative products coordinate comparison".
  Eight hits for recursive continuous cohomology and algebraic differentials; no match.
- `msearch.py ... loogle`: "ContinuousMap.evalₗ, Fin.partialProd_contractNth,
  ContinuousCohomology.homogeneousCochains". Zero hits; unknown `ContinuousMap.evalₗ`.
  `Fin.partialProd_contractNth` was subsequently inspected directly in Mathlib and is
  only the internal/final tuple identity, not this lemma.
- `msearch.py ... grep`: "homogeneousCochains|partialProd_contractNth|d_comp_d" in
  RepresentationTheory. Twenty-five hits, including `TopRep.d_comp_d` and
  `TopRep.homogeneousCochains`, which use recursive iterated continuous-map spaces.
- Direct `rg` in Mathlib: read `Fin.partialProd`, `Fin.contractNth`,
  `Fin.partialProd_contractNth`, the algebraic `inhomogeneousCochains.d`, and
  the recursive `TopRep.homogeneousCochains` with their full signatures/docstrings.
  The search service's older `Mathlib.Algebra.Category.ContinuousCohomology.Basic`
  path is absent locally; its corresponding current recursive module is
  `Mathlib.RepresentationTheory.Homological.ContCohomology.Basic`, which was read.
- Direct `rg` in `lean/WeilConjectures` and `lean/Sheaf` for homogeneous cochains,
  continuous cochains, and coordinate differentials found
  `Rep.homogeneousCochainEvaluation_differential` and
  `ContinuousCohomology.JointContinuousCochainCoordinates`. The former assumes
  compact Hausdorff G and discrete coefficients and uses iterated maps; the latter
  specifies the downstream full complexes and an isomorphism and does not state the
  individual first/internal/final faces here. Neither is an exact existing declaration
  for this node. Both relevant source files were opened and read.
- `grep -rn` of the item id in `lean/WeilConjectures` found no attachment.
  `rg` in `dag/lean_names_upstream.json` found no exact joint-coordinate declaration.
  An exact-name search of Mathlib, `lean/WeilConjectures`, and `lean/Sheaf` found no
  preexisting `exists_jointContinuousCoordinateDifferential`.

No node fault or statement dispute was found. The node copy changes only `lean`.

## Second reading by NN

I reread the node and the completed signature as a separate pass; no other agent was
started, as the dispatcher's instructions prohibit it. The maintainer's independent
review remains the independent reading required by this delivery workflow.

The rereading checked the two exact membership predicates, all four pointwise map
formulas, square zero, intertwining, and each of the three face equations against the
node, including their signs. It checked the internal reindexing i_paper=i_Lean+1,
that the last contraction drops rather than multiplies, and that Fin 0 leaves no
internal face. It also checked the absence of separation, compactness, characteristic,
or common-universe restrictions. During compilation, function application to submodule
elements required explicit `.val`; those coercions were corrected throughout without
changing the mathematics. No remaining mismatch was found.

Validation: `scompile.py NN lem-sfb-joint-continuous-coordinate-differential` compiled
this module both as its sandbox probe and under its final library module name cleanly
(no errors or warnings), with reported Lean times 15.3 s and 2.1 s respectively.
