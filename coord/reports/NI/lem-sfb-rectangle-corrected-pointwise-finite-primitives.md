## Worker report

The module `Sheaf.RepresentationTheory.RectangleCorrectedPointwiseFinitePrimitives`
states `ContinuousCohomology.exists_rectangleCorrectedPointwiseFinitePrimitives`.
Its only proof is `sorry`. The helper `rectangleTrivialD` is a transparent abbreviation
specializing the published differential to the trivial self-representation; it constructs
no new differential and has no postponed data. The repair adds a definition node owning
the existing differential and complex; no mathematical statement correction is needed.

Hypothesis and clause correspondence:

- The prime is `l` with `[Fact l.Prime]`. `Ω` has `[IsAlgClosure ℚ_[l] Ω]` and the
  extended norm through `[NontriviallyNormedField Ω] [NormedAlgebra ℚ_[l] Ω]`; `hΩ`
  states the nonarchimedean inequality. The field norm restricts to the p-adic norm.
- `S : Profinite.{w}` includes the empty space. `G` has Group, IsTopologicalGroup,
  CompactSpace, T2Space and TotallyDisconnectedSpace. These give the profinite group
  topology, equivalently its open normal subgroup basis. The independent explicitly
  declared universes `u v w` implement the size convention.
- The source's positive degree is `n + 1`, where `n : ℕ` is arbitrary. Its primitive
  degree is `n`. `C(S × (Fin r → G), V)` is the actual jointly continuous function
  space. `rectangleTrivialD` is `continuousInhomogeneousD` on the trivial action.
  Its `Fin.contractNth` sum includes all internal product faces and the final
  omission, with coefficients `(-1)^(j.val+1)`. At zero the first and last terms
  cancel. No normalization, local constancy, or discrete coefficient topology is imposed.
- `F : ℕ → IntermediateField ℚ_[l] Ω`, `hF : Monotone F`, and the dependent
  FiniteDimensional instances give exactly the increasing finite intermediate fields.
  Their norms/topologies are the inherited ones, not completions.
- `p : ℕ → Ω →L[ℚ_[l]] Ω` with `hp_range`, `hp_fix`, `hp_norm` is the continuous
  linear projection onto `F i` viewed in Ω, fixing that subfield and contractive.
  This is equivalent to a projection with codomain `F i` by subtype restriction.
- `z` is the specified continuous family, and `hz` is the cocycle identity on every
  fibre. `e` is the named F_i-valued version of its projection differences: `he`
  pins every value to `p i z - p (i-1) z`, with the zero predecessor for i=0.
  These continuous cochains always exist by range inclusion and continuity, so
  naming them adds no hypothesis or choice to the mathematical statement. `he_norm`
  is convergence of their actual sup norms to zero; `he_zero` is eventual vanishing
  at each fixed evaluation, with no uniform threshold required.
- Positive rectangle indices are `ℕ+`. `H`, `hH`, `a`, `N` give open normal
  subgroups, the n+2 right-coset anchors, and nonnegative field thresholds. Here
  n+2 is source degree+1. `k : ℕ → LocallyConstant S ℕ+` has finite range because
  S is compact. `j : S → ℕ+` and `hk` express pointwise stabilization, without
  assuming that j itself is continuous. `hrectangle` quantifies all independent
  points of H in all coordinates and evaluates successive ratios of `x_q a_q`;
  thus it is precisely membership of f_z in F_(N_j) on the full ordered rectangle.
- `t,r,α,β,ψ,χ` give the fixed finite evaluation lists, p-adic coefficients, and
  continuous evaluation maps; `hα,hβ` bound the coefficients. `TΩ,RΩ,T,R` are the
  ambient and finite-field operators; `hTΩ,hRΩ,hT,hR` impose the SAME formulas
  in every coefficient field. This states coefficient independence explicitly.
  Empty evaluation lists are allowed. The formulas also imply preservation of all
  coefficient subspaces and continuous profinite parameter families, since they
  are finite sums of continuous evaluations and fixed scalar multiplications.
- `hopΩ` and `hop` give, for Ω and every F_i, both operator norm bounds, and on
  cocycles respectively `d T c + R c = c`, `d R c = 0`, and residual vanishing
  when the homogeneous function vanishes on the rectangle. Bounds on every input
  norm are equivalent to operator norm at most one; no completeness is needed.
- `h i` is F_i-linear, `hh_norm` gives its contractivity on every input, `hh_d`
  its right-inverse identity on cocycles, and `hh_family` preservation of continuous
  profinite families. This last binder quantifies every `P : Profinite.{w}`.
- The conclusion's `res,b` are bundled continuous F_i-valued cochains. Its first
  two conjunctions specify exactly r_i and b_i fibrewise, including h_i(r_i).
  The next conjunction is `db_i=e_i` on every fibre (equivalently on S × G^degree).
  The fourth and fifth clauses give the sup-norm estimate and convergence to zero.
  The sixth is eventual zero at each fixed (s,x).
- The final clause strengthens the precision of the same conclusion exactly as in
  the node: at every s, eventually `R i (j s) ((e i).curry s) = 0` as an ENTIRE
  cochain, all values of res_i at s vanish, and for every x simultaneously b_i is
  both `T_(j(s)) e_i(s)` and its fixed finite evaluation expansion. The threshold
  for b_i(s,x)=0 may depend on x, as the source requires.

Dependency declarations read and used:

- `Mathlib.NumberTheory.Padics.PadicNumbers`: `Padic` (completion definition, line
  531 and its normed field instances), for def-weil-l-adic-numbers.
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure` and its Basic import:
  `AlgebraicClosure`, `IsAlgClosure` (Basic line 264), for def-weil-algebraic-closure.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and its imported coefficient constructions;
  `Padic.coefficientExtensionDegree` records finite dimensionality
  as used here. Only the field-extension part of that dependency is relevant;
  neither an integer ring nor uniformizer enters this lemma.
- `Mathlib.Analysis.Normed.Algebra.Basic`: IntermediateField's inherited normed field;
  `Mathlib.Topology.ContinuousMap.Compact`: the actual sup-norm on compact domains.
- The size convention has no declaration: explicit universe polymorphism is used.
- Added the definition node def-sfb-continuous-inhomogeneous-cochains
  to stmt_deps to record use of `ContinuousCohomology.continuousInhomogeneousD`
  (`Sheaf.RepresentationTheory.ContinuousCochainFiniteIndexTransfer`). Its complete
  signature, evaluation construction and docstring were read. Its transfer theorem
  is not assumed or invoked. `rectangleTrivialD` only specializes this declaration.
  No proof dependencies are listed by this item's DAG; none were added.

Edge cases checked: empty S gives unique empty continuous maps and zero sup norms;
source degree one is n=0 and G^0 is the singleton with zero differential; i=0 uses
p_0 without an artificial negative-index field; N_j=0 is allowed; H_j=G is allowed;
the trivial group is allowed; zero cochains and empty finite evaluation lists give
zero; stabilization is pointwise rather than uniform in s; F_i may repeat or fail
to exhaust Ω; Ω and F_i are never assumed complete; no equality of universes is imposed.
The assumed contractions can of course rule out particular nonzero degree-one cocycles;
that is already an explicit hypothesis of the node, not a defect of its statement.

Searches made (all before writing):

- msearch.py leanfinder: "Rectangle correction of continuous group cocycles using
  finite evaluation operators produces bounded pointwise eventually zero primitives".
  Eight hits, including groupCohomology.IsCoboundary₂ and low-degree cocycle facts;
  none states the selector-dependent rectangle correction.
- msearch.py loogle: "inhomogeneousCochains.d, ContinuousMap.norm_le". Zero hits.
- msearch.py grep: "rectangle.*(cochain|primitive)|(cochain|primitive).*rectangle".
  Three hits, all complex analytic primitives, no matching group-cochain theorem.
- rg of lean/WeilConjectures for rectangle, finiteEvaluation, inhomogeneous,
  cochainDifferential, ContinuousCochain; rg for this exact node id gave no hit.
  Found only discrete or unrelated cohomological uses, no statement match.
- rg of lean/Sheaf/RepresentationTheory and Paper found the published
  BoundedFiniteEvaluationRectangleReplacement and ContinuousCochainFiniteIndexTransfer.
  Read their full relevant signatures and docstrings. The former constructs the
  operators (assumed here), and the latter supplies the differential (reused here).
  Neither gives the primitive-correction conclusion.
- rg of dag/lean_names_upstream.json for the relevant names found no exact match.
  DAG searches for cochain/evaluation definitions found no missing independent notion.
  The specified finite sums are explicit binders. The repair separately records the
  existing differential and complex under the new definition node described below.

The source proof paragraph (3) was opened: it motivates the auxiliary analytic lemma
but does not state this quantitative result. The inherited source's WANTED reference
is retained in both module and theorem docstrings; this is not attributed to Stacks.
No STATEMENT-DISPUTED or source correction is raised.

Validation: scompile.py compiled the sandbox module and the library-path module
successfully on the server, with no errors or non-sorry warnings. The module has
`set_option autoImplicit false`. Every auxiliary parameter and universe is explicit.


## New nodes

`def-sfb-continuous-inhomogeneous-cochains` records the existing definitions
`ContinuousCohomology.continuousInhomogeneousD` and
`ContinuousCohomology.continuousInhomogeneousComplex` in
`Sheaf.RepresentationTheory.ContinuousCochainFiniteIndexTransfer`, with
`existing: true` and no new module. Its only statement dependency is
`def-weil-field`. Its source is Stacks Tag 0DVG, read in
`literature/stacks-project/etale-cohomology.tex`, section
`section-continuous-group-cohomology`, including the degree-zero formula.
The jointly continuous linear representation is `A : TopRep E J` together with
`hA`; the cochains are `C(Fin n → J, A)`, and the differential is the specified
initial action term and signed `Fin.contractNth` faces. The complex lies in
`ModuleCat.{max v w} E`, indexed by ℕ. Its square-zero proof comes from the
existing named theorem; its cochain spaces and arrows are concrete constructions.
The complex imposes no closure, completeness or discrete topology condition.
Degree zero is continuous maps on a singleton; the last face at n=0 gives `gv-v`.
Independent coefficient and group universes and zero coefficient spaces are allowed.

Fresh searches on 2026-10-23: msearch LeanSearch, query "Continuous inhomogeneous
group cochains with coefficients in a topological linear representation,
differential and nonnegative cochain complex", returned eight hits, chiefly
`ContinuousCohomology.MultiInd.complex` and all-function `inhomogeneousCochains`.
These do not provide the requested finite-product jointly continuous interface.
msearch Loogle for `ContinuousCohomology.continuousInhomogeneousD` returned zero
hits with an unknown-identifier diagnostic. msearch Mathlib grep for
`continuousInhomogeneousD|continuousInhomogeneousComplex|inhomogeneous.*[Cc]ochain|[Cc]ochain.*inhomogeneous`
returned 25 ordinary inhomogeneous cochain hits. Local Mathlib ContCohomology is
iterated homogeneous cohomology. Direct rg over `lean/WeilConjectures` found
discrete or locally constant constructions. Direct rg over `lean/Sheaf` found
exactly the existing definitions reused here. DAG grep showed them only as helpers
in the transfer theorem record, not under a definition node; broader DAG searches
found discrete cohomology or coordinate comparison nodes. `blueprint_refs.py search
continuous-inhomogeneous` found zero blueprint nodes; `ancestor` returned None,
which is retained as the new node's `blueprint.from.node`.

## Repair of return H2 at 9a30cad26273

The transfer theorem was cited only to reach its plain definition helper, not
through a theorem choice. Added the requested definition node with all §5 fields,
recording both existing declarations in place. Replaced the delivery-added
`lem-sfb-continuous-cochain-finite-index-transfer` statement dependency with
`def-sfb-continuous-inhomogeneous-cochains`. The item's four original dependencies
and mathematical statement are unchanged. The Lean module is unchanged from the
returned packet. The initial saved-packet dry run passed at f3d3e159a9c; the repair
is nevertheless necessary to satisfy the independent reviewer. Delivery wrappers
rebase the packet onto current sheaf-dag; comparison with current main showed only
the intended statement-dependency and lean-record changes to the item.

## Second reading by NI

No additional worker was started: the dispatcher requires direct worker delivery
and reserves the independent reading to the maintainer. Self-check of this repair
read the new node against the complete existing definition signatures and Stacks
0DVG. It records actual definitions, with no theorem-choice substitution and no
new assumptions. The item uses the differential by the unchanged transparent
`rectangleTrivialD` specialization. The reviewer's mathematical acceptance of the
remaining statement is retained; this repair changes only definition ownership.

Repair validation: scompile.py recompiled the unchanged item successfully in both
sandbox and library module modes. The self-check verified both recorded signatures
verbatim and confirmed that the item preserves every original field except lean
and the addition of the new definition dependency.
