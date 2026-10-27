## Worker report

This delivery states `AlgebraicGeometry.ProjectiveSpace.exists_coherent_regular_hyperplane`
in `Sheaf.AlgebraicGeometry.CoherentRegularHyperplaneRestriction`. Its proof alone is
`sorry`. Five helper definitions give real, canonical constructions of the linear section,
multiplication, restriction, restricted multiplication, and transported connecting map.
The theorem docstring carries all nine steps of the DAG proof and their cited inputs.

The previous worker's stale-assignment conclusion was mistaken: Q13's reviewed merge was
stage 1 (nine natural-language proof steps), not a stage-2 Lean binding. The current node
is split, with no `lean` record. This delivery preserves that split and its statement,
source, proof and proof dependencies. There is no resplitting or statement correction.

I read the standing stage-2 brief, stage document, delivery-errors H, worker role, setup,
goal and state, the item, every statement dependency and its recorded declaration, and
the Stacks source at varieties.tex lines 6455--6593: hyperplane geometry 089Z, regular
section 08A0, finite-family remark, and twisted/cohomology remark 0EGK. The prescribed
CompactObject example is now withdrawn and contains only a module header; the delivered
file uses the current module/public-import/public-section conventions instead.

Clause-by-clause correspondence:

* An arbitrary infinite field is `(k : Type u) [Field k] [Infinite k]`. Dimension is
  `(n : ℕ) (hn : 1 ≤ n)`. Projective space is the existing
  `ProjectiveSpace (ULift.{u} (Fin (n+1))) (Spec (.of k))`; the coordinate index has the
  field's universe, and includes all `n+1` coordinates.
* The finite collection is `(v : ℕ)` and `E : Fin v → ...Modules`. This includes the
  empty collection and repetitions. `hE` uses `RingedSpace.IsCoherent` on each `E α`.
  This is the actual finite-type-with-finite-type-kernels definition. The item
  lean.note explains its use while retaining the landed shared dependency record.
* Coefficients are `a : Fin (n+1) → k`, with `a ≠ 0`. The helper
  `regularHyperplaneLinearSection` is literally the finite sum of `a_j T_j`: coefficients
  enter global functions by `Scheme.globalSectionsRingHom`, and `T_j` is the existing
  `ProjectiveSpace.twistOneSection`. The additional explicit inequality for the resulting
  section expresses the node's same nonzeroness under this coefficient encoding.
* `H`, `i`, `IsClosedImmersion i`, and `i.ker = Hom.zeroLocus (homOfGlobalSection ... s)`
  identify the closed subscheme with the zero scheme of this very section, not an
  arbitrary closed immersion with the same support. Zero schemes and ideal sheaves
  are existing constructions, and the kernel equality specifies their scheme structure.
* `e : H ≅ ProjectiveSpace (ULift (Fin ((n-1)+1))) (Spec (.of k))` is the required
  isomorphism; the following equality states it is over the field. For every `d : ℤ`,
  the next clause identifies `tensorPullback i` of the ambient twist with
  `tensorPullback e.hom` of the standard lower-dimensional twist. Thus `O_H(d)` is
  represented by `i^* O_X(d)`, exactly as in 0EGK.
* `G_α` is always the term `(tensorPullback i).obj (E α)`, never a freely chosen module.
  Its coherence is a separate conclusion. Its twist is the tensor product of this
  term with `(tensorPullback i).obj (twist ... d)`.
* The sequence uses the integer pair `d, 1+d`, which parametrizes exactly the source
  pair `D-1,D` by `D=1+d`; no degree is excluded or identified by a new hypothesis.
  `regularHyperplaneMultiplication` is whiskering of the canonical `twistMulHom rfl s`.
  `regularHyperplaneRestriction` is the unit of the recorded section-normalized tensor
  adjunction followed by pushforward of the canonical tensor comparison. Its target
  is literally `i_*(G_α ⊗ i^*O_X(1+d))`. `w` records the zero composite, and `hS` is
  `ShortComplex.ShortExact`, including monicity, exactness and epimorphic restriction.
* Pushforward is the existing `Scheme.Modules.pushforward i`, whose sections are
  sections on the inverse image open, with scalar action via the structure-sheaf map.
  No separate sheaf or action is postulated.
* `q : ℕ` includes degree zero. The cohomology identification is invertibility of
  the actual `Scheme.Modules.moduleCohomologyEdgeMap i N q`, from cohomology of
  `i_*N` to that of `N`. Its inverse gives precisely the node's natural identification.
  The final square asserts its naturality in every map among the chosen modules.
* All cohomology objects are `RingedSpace.moduleCohomology` (right derived global
  sections on modules), as in the recorded `pqf-def-cohomology`; `forget₂` only regards
  their module-linear maps as additive homomorphisms. The two `Function.Exact` clauses
  express exactness at the second and third terms of the four consecutive terms.
  The second arrow is the actual `moduleCohomologyFMap` of restriction. The third arrow
  is `regularHyperplaneConnecting`, defined as inverse edge map followed by the actual
  `moduleCohomologyBoundary` of the same short exact sequence. Standard derived categories
  are supplied explicitly inside this definition; no size assumption is added.
* Naturality of the short exact sequences is the pair of squares quantified over
  `α β`, `u : E α ⟶ E β`, and every `d`. Their vertical maps are `u` tensored with the
  identity twist, and pushforward of `i^*u` tensored with the restricted identity twist.
* Multiplication compatibility quantifies over every global section `t` of `O(1)`;
  on projective space these are exactly the linear forms in the node. The equation
  compares ambient multiplication then restriction with restriction then pushforward
  of the pullback multiplication, using the same tensor comparisons at both ends.

Dependency interfaces read and used:

* `Field`, Mathlib.Algebra.Field.Defs, for def-weil-field.
* `RingedSpace.IsCoherent`, WeilConjectures.AlgebraicGeometry.Coherent, for the full
  coherence notion of pqf-def-coherent; its landed binding is retained unchanged.
  The definition uses Mathlib finite type and tests every open and finite free map.
* `ProjectiveSpace.twist` and `twistOneSection`,
  WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist; the canonical `twistMulHom`
  in ProjectiveSpace.TwistMul uses `twistTensorIso` of ProjectiveSpace.TwistTensor.
* `sheafCohomologyAndHigherDirectImages`, WeilConjectures.AlgebraicGeometry.PQFCohomology,
  and its `RingedSpace.moduleCohomology` from Topology.RingedSpaceModuleCohomology.
* `Scheme.Modules.tensorPullbackSectionAdjunction` and `tensorPullbackSection`,
  Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction, publicly importing the existing
  tensor formula in WeilConjectures.AlgebraicGeometry.TensorPullback.
* `AlgebraicGeometry.IsClosedImmersion`, Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion.
* Additional already-landed nodes added to stmt_deps because their canonical constructions
  occur in the signature or helper bodies: def-pc-zero-scheme (`Hom.zeroLocus`,
  Modules.ZeroLocus); def-weil-pbc-module-cohomology-fmap (`moduleCohomologyFMap` and
  `moduleCohomologyEdgeMap`, ModuleCohomologyFMap); def-sc-module-cohomology-boundary
  (`moduleCohomologyBoundary`, ModuleCohomologyBoundary); and
  def-sc-tensor-pullback-power-comparison (`boundaryPullbackTensorIso`,
  WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons). This is the
  owner definition node of the existing general tensor comparison; the square-zero
  unit theorem in that same module is not needed to state this item.

All recorded proof-dependency modules are imported plainly, including the coherent
affine sections and affine pullback computations, relative Proj functoriality, the
natural module/abelian cohomology comparison, closed-embedding cohomology, left exact
global sections and the full derived-functor long exact sequence. Stated definitions
used by the signature are public imports. Mathlib finiteness/associated-prime and
finite-linear-avoidance modules are proof imports. No proof dependency is discarded.

Edge cases checked against the source: `v=0` still requires a nonzero section and the
hyperplane geometry, with vacuous module clauses. Zero modules yield zero sequences.
For `n=1`, the lower projective space is P^0, not an empty-coordinate projective space.
Negative twist degrees are quantified without restriction. Degree `q=0` and the first
connecting map are present. A skyscraper supported at one point forces the section to
avoid that point, consistently with the associated-prime construction. No characteristic
restriction is imposed beyond the infinite-field hypothesis. Universes do not equate
unrelated site universes or bound the field's universe by the finite coordinate type.

Searches: prescribed msearch.py calls, recorded in sandbox searches.jsonl, used LeanSearch
for a common regular hyperplane and twisted restriction sequences, LeanFinder for the
same full geometric/cohomological assertion, Loogle `"hyperplane"`, and Mathlib grep
`hyperplane|regularHyperplane|exactSequenceInduction` under AlgebraicGeometry. LeanSearch
returned finite-presentation algebra, Proj charts, quasicoherence and ordinary vector
projectivization; LeanFinder returned Proj charts, K-projective complexes, and unrelated
Mayer--Vietoris or Profinite sequences. Loogle's hits were convexity/measure hyperplanes.
The Mathlib grep had zero hits. Searches of both project source trees for the item id,
regularHyperplane, exactSequenceInduction and hyperplane/linear-form interfaces found
only the consumer's proof docstring and specialized coordinate geometry, not this lemma.
All six newly declared fully qualified names were searched in Mathlib, WeilConjectures,
Sheaf and dag/lean_names_upstream.json, with no existing declaration found.

No STATEMENT-DISPUTED flag or item statement fault remains. No new DAG node is created.
The coherence-record mismatch is documented in the item lean.note; the landed
record is retained. Initial complete server compile succeeded in both sandbox and
library module modes (10.6 and 10.9 seconds), without warnings. The repair validates
the unchanged Lean module again against the current published library.

## Return repairs

The return reviewed immutable head `fc530587e70d`. The saved packet's initial dry run
also passed (`bd9db426e22`), so its accepted Lean statement and canonical helpers are
retained. This repair makes the requested metadata changes:

1. H13: removed the sandbox copy of `pqf-def-coherent.json`. Its landed Q25
   `IsQuasiCoherentFiniteType` record has live users and is not rebound. The item keeps
   `RingedSpace.IsCoherent` and now explains in `lean.note` that it is the full
   finite-type-with-finite-type-kernels notion of Stacks 01BV. On the locally
   Noetherian projective spaces at issue, the recorded coherent/finite-type theorem
   relates these predicates. No dependency module is delivered.
2. H2: replaced the added statement dependency `lem-sc-square-zero-ideal-tensor-unit`
   with `def-sc-tensor-pullback-power-comparison`. I opened that owner node and the
   implementation: `boundaryPullbackTensorIso` is a real definition for arbitrary
   scheme morphisms and modules, obtained from left-adjoint uniqueness and the
   monoidal ordinary pullback. The square-zero theorem's conclusion is unused.
   The module import remains the same because this is where the definition lives.
3. H11: replaced the previous disclaimer with the actual second-pass reading below.

The packet was compared with the current read clone field by field. The item keeps
all current non-owned fields, including the current lean_audit. Only its `lean` and
the four additional owner dependencies differ from the current base. Its statement,
proof and proof dependencies are unchanged. The delivery wrapper performs the
current-base refresh and builds the reviewable commit; no direct Git command is used.

## Second reading by NR

Repair reading on 2026-10-22, performed by this worker in a fresh pass with the full
item node, all 272 lines of the Lean file, the comparison owner node, and Stacks
`varieties.tex` (hyperplane lemma, regular-section lemma, finite-family remark and
cohomology remark) open. This records a self-check; the dispatcher prohibits starting
another agent, and the maintainer supplies the independent delivery review.

| Node hypothesis or clause | Lean rendering checked | Finding |
| --- | --- | --- |
| Infinite field; n at least 1 | `(k : Type u) [Field k] [Infinite k]`, `(n : ℕ) (hn : 1 ≤ n)` | Exact hypotheses; no characteristic restriction. |
| Finite coherent family on P^n_k | `(v : ℕ)`, `E : Fin v → ...Modules`, `hE : ∀ α, RingedSpace.IsCoherent ... (E α)` | Full coherence, every finite size and repetitions included; the shared Q25 node is retained. |
| One nonzero linear form for the family | `∃ a : Fin (n + 1) → k`, `a ≠ 0`, `regularHyperplaneLinearSection k n a ≠ 0` | The helper is the sum of the coefficients times the existing coordinate sections; both nonzeroness clauses encode the same nonzero form. |
| Closed hyperplane H=V(s) | `∃ (H : Scheme.{u}) (i : H ⟶ ...)`, `IsClosedImmersion i`, `i.ker = Hom.zeroLocus (homOfGlobalSection _ s)` | Equality of ideal sheaves fixes the zero-scheme structure, not merely the support. The source and target of the section map are invertible, as zeroLocus requires. |
| H is P^(n-1) over k; all twists agree | `∃ e : H ≅ ...`, its equality over `Spec k`, and `∀ d : ℤ, Nonempty (tensorPullback i ... ≅ tensorPullback e.hom ...)` | The isomorphism is oriented inversely to Stacks 089Z, an equivalent existence assertion. Its twist clause covers all integer degrees as in 0EGK. |
| G is i^*E and coherent | `RingedSpace.IsCoherent H.toRingedSpace ((tensorPullback i).obj (E α))` | G is the actual tensor pullback throughout, with no extra choice. |
| Every twisted short exact restriction sequence | `∀ α d`, zero composite `w` and `(ShortComplex.mk ... w).ShortExact` | With source degree d and target degree 1+d this is precisely the node's pair D-1,D. Multiplication is `E ◁ twistMulHom rfl s`; restriction is the normalized adjunction unit followed by pushforward of `boundaryPullbackTensorIso.hom`. |
| Pushforward and induced scalar action | Existing `Scheme.Modules.pushforward i` | This is sheaf direct image with the prescribed structure-sheaf action; no new action is assumed. |
| Natural comparison in every q and four consecutive exact terms | `∀ q : ℕ, ∃ h : IsIso (moduleCohomologyEdgeMap i ... q)`, then the two `Function.Exact` clauses | The comparison is the canonical edge map. The first arrow is cohomology of multiplication, the second is `moduleCohomologyFMap` of restriction, and the third is inverse edge followed by the boundary of this same short exact sequence. Both interior exactness positions are present. |
| Naturality in maps of chosen modules | `∀ α β (u : E α ⟶ E β) d`, the two sequence squares, and the final edge-map square for all q | The maps are tensoring u with the identity twist, pulling it back, and pushing forward; all chosen modules and all degrees occur. |
| Restriction commutes with linear forms | `∀ α d (t : Γ(twist ... 1, ⊤))`, multiplication/restriction square | Restricted multiplication is the actual pullback of ambient multiplication through the fixed tensor comparisons. Every global degree-one section is quantified. |

Edge-case recheck: at `v=0` the module clauses are vacuous but the nonzero hyperplane
and its geometry are still required. At `n=1`, `Fin ((n-1)+1)` has one element and
therefore describes P^0. Zero modules impose no obstruction to regularity. Negative
degrees are allowed by ℤ and `d ↦ 1+d` covers every target degree. At `q=0`, the
canonical edge map and the first connecting map are still asserted. A skyscraper
module requires avoidance of its support, consistent with the associated-prime
choice in the source. ULift places finite coordinate types in the field's universe
without restricting the field or making a test-object quantifier vacuous.

Definition audit: each of the five helpers has explicit data. The comparison it
uses is a plain definition owned by `def-sc-tensor-pullback-power-comparison`;
its left-adjoint comparison uses the normalized adjunction, so no arbitrary scalar
normalization enters the restriction arrow. The only postponed proof in the item
module is `exists_coherent_regular_hyperplane`, with its nine-step source proof in
the docstring. All variables and the universe are explicitly bound. I found no
mathematical mismatch requiring a Lean change. The two metadata defects listed
above are repaired; no new node, dependency rebind or statement correction remains.

Repair validation: prescribed scompile.py succeeded on 2026-10-22 in sandbox mode
(7.2 seconds) and library mode (7.3 seconds), with no errors or warnings. The
recorded Lean signature was checked verbatim against the file. The item differs
from the read base only in lean and stmt_deps; pqf-def-coherent is absent from
the packet. Final deliver2.py preflight and compile are required before push.
