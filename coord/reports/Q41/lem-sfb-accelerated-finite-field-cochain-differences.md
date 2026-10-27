## Worker report

The module `Sheaf.RepresentationTheory.AcceleratedFiniteFieldCochainDifferences` states
`ContinuousCohomology.exists_acceleratedFiniteFieldCochainDifferences` with one `sorry`.
No theorem is proved. All five helper declarations have real bodies and belong to this
node: the trivial-action specialization, the two canonical coefficient inclusions, and
the explicitly recursive finite maximum and its tolerance. They introduce no independent
mathematical notion needing a new node.

Source read: `literature/blueprint/latest/blueprint/sec-six-functors-basics/`
`sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3).
It supplies the open-direct-image motivation; it does not assert this scalar analytic
lemma. The node explicitly labels its six-step analytic argument agent-formulated and
requests an exact literature reference. The module retains that attribution and the full
six-step proof plan, including the normed-vector-space hypotheses for dense extension.
No analytic theorem is attributed to the blueprint itself.

Hypotheses, in order:

- Prime ell: `(l : ℕ) [Fact l.Prime]`, with the actual Mathlib `ℚ_[l]`.
- Algebraic closure with the extending nonarchimedean norm:
  `(Ω : Type u) [NormedField Ω] [NormedAlgebra ℚ_[l] Ω]`
  `[IsAlgClosure ℚ_[l] Ω] [IsUltrametricDist Ω]`. These describe the norm topology;
  `NormedAlgebra` makes the structure inclusion isometric. No completeness of Ω is assumed.
- B is literally `UniformSpace.Completion Ω`, with Mathlib's normed-field structure and
  canonical isometric coercion, not an arbitrary ambient field or a chosen retraction.
- Increasing finite intermediate fields: `F : ℕ → IntermediateField ℚ_[l] Ω`,
  `hF : Monotone F`, `[∀ N, FiniteDimensional ℚ_[l] (F N)]`. Their union is Ω by
  `hcover : ∀ a : Ω, ∃ N, a ∈ F N`.
- Nonempty profinite S: independent universe `w`, topological space, compact, Hausdorff,
  totally disconnected and nonempty instances. Profinite group G has independent universe
  `v`, the same topological properties, a group and `IsTopologicalGroup G`.
- Degree at least two is represented exactly by `n + 2` with `n : ℕ`. The cocycle is
  `z : C(S × (Fin (n + 2) → G), Ω)`, and `hz` says its differential is zero for every s.
  The primitive is `b : C(S × (Fin (n + 1) → G), Completion Ω)`; `hb` equates its
  differential pointwise with the canonical inclusion of z.
- `N : ℕ+ → ℕ` and `C : ℕ+ → ℝ`, with `hC : ∀ j, 1 ≤ C j`, cover exactly the positive
  index sequences in the node, with no monotonicity or boundedness assumption.
- The universe convention is rendered by explicitly declared `u v w x`; no universe
  equalities, countability, metrizability or size restrictions are imposed on S or G.

The existing `continuousInhomogeneousD` specializes to trivial action via
`acceleratedTrivialD`. Its first term drops the first coordinate; `Fin.contractNth`
combines adjacent coordinates for interior indices and drops the last coordinate at the
last index, with sign `(-1)^(j.val+1)`. Thus it is exactly the displayed differential,
including cancellation in degree zero. The parameter s is held fixed by `.curry s`.

Conclusion clauses, in order:

- Existential `Q : ∀ k, Completion Ω →L[ℚ_[l]] F k` bundles continuity and Q_l-linearity;
  the first two conjuncts state fixing F_k and contractivity for every k and value.
- `StrictMono L`, `∀ i, i ≤ L i` and the positive-index domination conjunct express
  every required constraint, including L_0 >= N_1.
- `pz` and `pb` are continuous cochains valued in `F (L i)`. Their evaluation equations
  specify exactly Q_(L_i) applied to z and b. These binders introduce no extra assumption.
- `acceleratedLoss C` has value 1 at zero and is recursively the maximum of the preceding
  value with C_(t+1), hence exactly D_t. `acceleratedTolerance C i` is `(2⁻¹)^i / D_(i+1)`.
  The two norm inequalities are precisely the two sup error bounds, with pz included in
  Ω and pb included in B by actual inclusions. Mathlib's `ContinuousMap` norm on compact
  domains is the supremum norm.
- `e` and `c` are themselves continuous cochains in `F (L i)`. Their defining equations
  are the consecutive projected differences; `if i = 0 then 0 else ...` implements
  P_(-1) = 0. The c equation is in B, where b lives; injectivity of the field inclusions
  uniquely specifies the finite-field value just as an equation in Ω would.
- The next two clauses say de_i = 0 and dc_i = e_i in the finite field itself, at every s.
- The finite sum over `Finset.range (i + 1)` equals pz_i pointwise in Ω.
  `TendstoUniformly ... z atTop` says these sums converge uniformly in Ω itself.
- For every `1 ≤ i`, the two norms are at most the maximum of adjacent tolerances;
  the same maximum is at most `(2⁻¹)^(i-1) / D_i`. This includes both requested estimates.
- `∀ a, ∀ᶠ i in atTop, e i a = 0` is pointwise eventual vanishing on S times G^(n+2).
- The final clause quantifies every positive j <= i, every s and every arbitrary subset
  `R : Set (Fin (n + 3) → G)`. Its hypothesis is that all homogeneous z-values on R lie
  in F_(N_j); its conclusion is zero for all homogeneous e_i-values on R. The function
  `fun q ↦ (g q.castSucc)⁻¹ * g q.succ` is the exact successive-ratio coordinate map.
  No openness, rectangle structure or continuity restriction is imposed on R.
- There is no eventual-vanishing conclusion for c, and no map B to Ω is assumed.

Dependencies read and used:

- `def-weil-size-convention`: metatheoretic convention, explicit universes as above.
- `def-weil-l-adic-numbers`: Mathlib `Padic`, read in `NumberTheory/Padics/PadicNumbers.lean`;
  statement imports that module publicly.
- `def-weil-algebraic-closure`: Mathlib `IsAlgClosure`, full signature/docstring read in
  `FieldTheory/IsAlgClosed/Basic.lean`; imported through `AlgebraicClosure`.
- `lem-sfb-normed-field-completion`: the recorded completion normed-field instance,
  `Completion.coeRingHom`, `Completion.coe_isometry`, and completeness. Read their source
  and the normed-field completable-topological-field instance. `Completion Ω` and its
  canonical coercions are used directly, and the module imports the completion machinery.
- Added landed statement dependency `def-sfb-continuous-inhomogeneous-cochains`:
  `Sheaf.RepresentationTheory.ContinuousCochainFiniteIndexTransfer`, declaration
  `ContinuousCohomology.continuousInhomogeneousD`. Read its entire definition and docstring;
  used directly in `acceleratedTrivialD`. This avoids constructing a second differential.
- All five proof inputs are imported: `Padic.exists_normOne_finiteSubfield_projection`
  from `Sheaf.NumberTheory.Padics.NormOneFiniteSubfieldProjection`; recorded Mathlib
  `spectralNorm.completeSpace`; `Completion` machinery; `LinearMap.extendOfNorm`
  with its agreement/bound/uniqueness signatures; `Pi.compactSpace`. These imports remain
  plain proof imports when not needed by the public signature. Their declarations were read.

Searches:

- `msearch.py ... leanfinder "Contractive finite field projections approximate continuous
  p-adic cocycles and completed primitives with accelerated bounds and pointwise finite
  telescoping differences"`: eight p-adic approximation/Mahler hits; none is this statement.
- `msearch.py ... loogle "ContinuousMap, ContinuousLinearMap, TendstoUniformly"`: zero hits.
- `msearch.py ... grep "accelerated|finiteSubfield.*projection|pointwise.*cochain"`:
  zero Mathlib hits.
- `msearch.py ... leansearch "continuous inhomogeneous group cohomology trivial action
  finite subfield approximation"`: eight continuous/ordinary cohomology hits, none with
  the accelerated finite-field projection or simultaneous primitive conclusion.
- `rg` in `lean/WeilConjectures` for cochains, finite-subfield projections and all proposed
  names, plus the item id: no exact statement or proposed name. The fundamental-group
  finiteSubfieldDiagram is unrelated. The upstream names table has no proposed name.
- `rg` in `lean/Sheaf` for inhomogeneous/trivial cochains found the existing differential
  above and `rectangleTrivialD`, another abbreviation for the same specialization.
  Neither gives the accelerated theorem. The rectangle-corrected primitive theorem has
  no completed primitive hypothesis or prescribed accelerated approximation rates.
  The parent `ParameterCochainCompletionBoundaryDescent` was read: it gives existence of
  a primitive after a cover, not the projection-and-difference conclusion here.
- Read the DAG records for `def-sfb-continuous-inhomogeneous-cochains`,
  `lem-sfb-metrizable-cocycle-finite-field-components` and
  `lem-sfb-rectangle-corrected-pointwise-finite-primitives`; neither latter node duplicates
  this statement. No new definition node or dependency repair is necessary.

Edge cases checked: n=0 in the Lean binder gives the original n=2 and a degree-one
primitive. Singleton S and trivial G are allowed. Zero cochains are allowed. F may have
repetitions, while L must strictly increase. N_j may be zero, repeated or unordered; C_j
may be one, nonintegral or unbounded. At i=0 both differences subtract zero, and no
adjacent-error estimate is requested. At i=j=1 the domination at stage zero supplies
L_0 >= N_1. R may be empty or the full group power. Eventual vanishing depends on z in Ω,
not on b in B. No counterexample or statement defect found.

Compile: prescribed `scompile.py`, independently for the single delivered module in
sandbox mode and at its final module name; clean output. The initial completion-map
continuity expression needed its explicit Ω argument; this was repaired. All variables
and universes are explicitly bound, `autoImplicit` is false, all lines are at most 100
characters, and the only postponed proof is the named main theorem.

## Second reading by Q41

A separate author self-check was made with the node statement and complete final Lean
signature open; this is not an independent-agent review. The dispatcher prohibits
starting other agents; the maintainer supplies the independent review.

Checked all hypothesis and conclusion correspondences listed above. In particular,
positive sequence indices are ℕ+, degree n+2 includes exactly every allowed degree,
Q maps into F_k, all four named cochains have continuous finite-field-valued types,
subtraction takes place only after canonical inclusion, and uniform convergence is in Ω.
Verified that `Fin.contractNth` at its final index gives the last face, and that the
homogeneous coordinate indices have sizes n+3 to n+2. Checked both consecutive indices
in the j<=i vanishing argument, and checked that no stronger vanishing for c appears.
No mathematical mismatch found. Removed the initial overly broad coefficient-finiteness
public import in favor of the actual Padic, normed-algebra and finite-dimension modules.
The landed cochain definition node was added to stmt_deps as required for reuse.
