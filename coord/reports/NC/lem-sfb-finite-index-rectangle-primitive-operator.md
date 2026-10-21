## Worker report

The module `Sheaf.RepresentationTheory.FiniteIndexRectanglePrimitiveOperator` states
`ContinuousCohomology.exists_finiteIndexRectanglePrimitiveOperator` with its proof
entirely `sorry`. No definition or helper theorem is introduced. The theorem docstring
records all fourteen proof steps of the DAG. The blueprint paragraph (3) supplies the
application context only; the finite-index cochain lemma and its proof are explicitly
agent-written in the source node. No statement correction or disputed statement.

Hypothesis and clause correspondence:

- A prime ell is `(l : ℕ) [Fact l.Prime]`; its field is Mathlib `ℚ_[l]` (`Padic l`).
- A profinite group is `(G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]`.
  For compact Hausdorff topological groups, this is equivalent to the stated basis
  of open normal subgroups. The arbitrary open subgroup is `H : OpenSubgroup G`;
  its index `H.toSubgroup.index` is finite and positive by openness and compactness.
  There is no normality or coprimality assumption.
- The paper's positive degree is written `n + 1` with `n : ℕ`, so all positive degrees
  are represented and the primitive degree is `n`. The rectangle anchors are
  `a : Fin (n + 2) → G`.
- The coefficient space is universally quantified as `V : Type v` with
  `[NormedAddCommGroup V] [NormedSpace ℚ_[l] V]` and the explicit strong triangle
  inequality `∀ x y, ‖x + y‖ ≤ max ‖x‖ ‖y‖`. The normed-space instances supply
  the exact scalar norm equality and norm topology. No `CompleteSpace V` occurs.
- Cochains of degree r are Mathlib `C(Fin r → G, V)`. Degree zero is continuous
  maps from the singleton `Fin 0 → G`, canonically V by evaluation. The trivial
  action is expressed by the absence of any action factor in the first face.
- The natural number `t`, coefficients `α : Fin t → ℚ_[l]`, and continuous maps
  `ψ : Fin t → C(Fin n → G, Fin (n + 1) → G)` are existentially quantified before
  V. Thus all finite evaluation choices are independent of V, and also of S.
- Each scalar bound is `‖α j‖ ≤ ‖(H.toSubgroup.index : ℚ_[l])‖⁻¹`.
- The primitive is the linear operator `T : C(Fin (n + 1) → G, V) →ₗ[ℚ_[l]]
  C(Fin n → G, V)`, with the identity `T c x = ∑ j : Fin t, α j • c (ψ j x)`
  for every input, not merely cocycles.
- The cocycle hypothesis is its displayed inhomogeneous differential equal to zero:
  the first term drops coordinate zero; `Fin.contractNth j (· * ·)` multiplies the
  adjacent entries for `j.val < degree` and drops the last entry for the last j.
  Its coefficient is `(-1 : ℚ_[l]) ^ (j.val + 1)`. This gives exactly all middle
  terms and the final term, with their signs.
- The rectangle hypothesis quantifies `x : Fin (n + 2) → H`. Its i-th input to c
  is `((x i.castSucc : G) * a i.castSucc)⁻¹ * ((x i.succ : G) * a i.succ)`.
  These are the successive ratios of an arbitrary tuple in the right cosets H a_i,
  exactly the homogeneous function f_c in the node.
- Under those two hypotheses, the conclusion displays the same differential on T c
  and equates it with c at every tuple. When `n = 0` it is `T c () - T c () = c g`,
  giving the required d^0 = 0 case without excluding degree one.
- The supremum bound is `‖T c‖ ≤ ‖(H.toSubgroup.index : ℚ_[l])‖⁻¹ * ‖c‖`.
  Mathlib's norm on C(X,V) for compact X is exactly this supremum norm.
- Preservation of every coefficient subspace quantifies `W : Submodule ℚ_[l] V`
  and asserts that all T c values lie in W whenever all c values do; no closedness.
- For every `S : Profinite.{w}`, `TS` is a continuous linear map between the two
  continuous parameter-family spaces. Its displayed value is the identical finite
  sum `∑ j, α j • c (p.1, ψ j p.2)`, leaving the parameter fixed. The remaining
  clauses give the same supremum bound and preservation of all coefficient
  subspaces on these parameter-family spaces as well.
- Independent explicit universes u, v, w implement def-weil-size-convention for the
  group, coefficients, and parameter space. This convention has no module or
  declaration to import; there is no site or derived category in this statement.

Dependency declarations and sources read:

- def-weil-l-adic-numbers: `Padic` in
  `Mathlib.NumberTheory.Padics.PadicNumbers`, including its completion docstring,
  signature and canonical real-valued norm. Imported publicly for the statement.
- def-weil-size-convention: the recorded metatheoretic convention, implemented by
  explicit universe parameters; no mathematical declaration or module exists.
- Proof dependency lem-sfb-topological-homogeneous-cochain-coordinates:
  `ContinuousCohomology.exists_jointContinuousCochainCoordinates` in
  `Sheaf.RepresentationTheory.TopologicalHomogeneousCochainCoordinates` (plain import).
- Proof dependency def-weil-pbc-free-module: `Module.Free` in
  `Mathlib.LinearAlgebra.FreeModule.Basic` (plain import).
- Proof dependency lem-sfb-ordered-join-partial-contraction:
  `AlgebraicTopology.OrderedJoin.partialContraction` in
  `Sheaf.AlgebraicTopology.OrderedJoinPartialContraction` (plain import).
  All recorded proof dependencies with modules are imported; none was omitted.

Edge cases checked before writing: degree one (n = 0 in the file), H = G, nonnormal
H, ell dividing the index, repeated anchors, V = 0, noncomplete V, nonclosed linear
subspaces, and empty profinite S. For degree one, a cocycle is a homomorphism G → V;
rectangle vanishing forces it to vanish on H and hence on the finite quotient cosets,
so characteristic zero forces c = 0. This agrees with d^0 = 0. Empty S gives the
zero function space and is allowed by Profinite. A finite sum can be empty (t = 0).

Searches for existing declarations:

- msearch.py leanfinder: "continuous group cochain finite index coset rectangle
  primitive finite evaluation operator bound" returned 8 hits, including
  ContinuousCohomology.MultiInd.complex, homogeneousCochains and continuousCohomology;
  none gives this quantitative finite-evaluation primitive assertion.
- msearch.py leansearch: "finite evaluation primitive operator continuous group
  cocycle vanishing on finite index subgroup coset rectangle" returned 8 ordinary
  group-cohomology low-degree cocycle declarations; none matches the node.
- msearch.py loogle: "ContinuousMap, OpenSubgroup.index, Fin.contractNth" returned
  no hits (unknown identifier OpenSubgroup.index; the actual index is on toSubgroup).
- msearch.py grep: "finiteIndexRectangle|finite.index.rectangle|rectangle.*primitive|
  primitive.*rectangle" returned 3 unrelated complex-analysis rectangle/primitives
  hits in Mathlib/Analysis/Complex/HasPrimitives.lean.
- rg with the same pattern over lean/WeilConjectures and lean/Sheaf found only a
  docstring citation in ParameterCochainCompletionBoundaryDescent.lean. The explicit
  blueprint-id grep in lean/WeilConjectures found no declaration.
- Read the full nearby BoundedFiniteEvaluationRectangleReplacement module and node.
  It requires `Nat.Coprime H.toSubgroup.index l`; it cannot express this lemma for
  ell-divisible indices. HomogeneousCocycleRectangleDetection gives a primitive on H
  rather than the required universal finite-evaluation operator on G. Neither is an
  exact existing match, and no notion was redefined here.

The previous worker's stale-assignment conclusion confused the stage-1 `reviewed`
record (NL's proof-plan review) with a stage-2 `lean` record. The live item has no
Lean attachment, so this delivery supplies the missing statement. No source fields
other than `lean` are changed in the node copy.

Validation: scompile.py compiled this file separately in sandbox and library module
modes with no errors or unexpected warnings (3.0 s / 2.9 s).

## Second reading by NC

I reopened the full node and the delivered Lean file for a clause-by-clause self-review.
No second agent was started, as explicitly required by this worker brief; independent
review belongs to the maintainer. The finite evaluation data precede V, no
prime-to-l hypothesis survives, and every coefficient bound uses the index cast into
Q_l before taking its norm and inverse. I checked both Fin.contractNth face ranges,
especially n = 0, and verified that rectangle coordinates use H a_i in the stated
order. The family part uses a continuous linear operator, has the same formula and
bound, and includes preservation of nonclosed subspaces. There are no hidden
completeness, normality or universe equalities. No mismatch or correction was found.
