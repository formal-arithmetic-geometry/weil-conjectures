## Worker report

The module `Sheaf.Analysis.PrimeToEllCompleteScalarIntegral` states
`WeilConjectures.primeToEll_completeScalar_integral`. Its only theorem has proof `sorry`.
No definitions, new nodes, dependency repairs, or statement corrections are needed.
The current node is stage-1 split/reviewed by N5 but has no Lean binding. This delivery
preserves that split and supplies its stage-2 statement; it does not re-split the node.

The source read is the main-20261015 direct-image stability proof, paragraph (3), at
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`.
It gives the open-direct-image context, not this analytic assertion. The node explicitly
labels the analytic input agent-formulated, with an exact literature reference WANTED.
The module preserves that qualification and includes all nine proof steps in its docstring.

Hypothesis and conclusion correspondence:

- Prime ell: `(ell : ℕ) [Fact ell.Prime]`.
- Complete nonarchimedean normed field B: `(B : Type v) [NormedField B]
  [CompleteSpace B]` and `hultra : ∀ x y : B, ‖x + y‖ ≤ max ‖x‖ ‖y‖`.
  Completeness for the metric is equivalently convergence of every Cauchy sequence.
- Isometric containment of Q_ell: `iota : Padic ell →+* B` and
  `hiota : Isometry iota`. A unital field homomorphism is injective, so this is the
  specified field embedding, with exactly its norm/metric compatibility.
- Profinite group: `K : Type u`, `Group K`, `TopologicalSpace K`,
  `IsTopologicalGroup K`, `CompactSpace K`, `T2Space K`, and `hbasis`.
  The latter says every open identity neighbourhood contains an open normal subgroup.
  In a topological group this gives the required translated open-normal basis.
- All finite continuous quotient groups have prime-to-ell order: `hprime` quantifies
  over `U : OpenNormalSubgroup K` and requires
  `Nat.Coprime (Nat.card (K ⧸ U.toSubgroup)) ell`.
  These quotients are finite by compactness and openness. Conversely any continuous
  finite quotient group, with its finite discrete topology, has open normal kernel
  and is isomorphic to this kernel quotient. Thus the hypothesis covers exactly the
  node's finite continuous quotients, without limiting their presentation/universe.
- All continuous maps and the supremum norm: `C(K, B)` and Mathlib's compact-domain
  continuous-map norm. `ContinuousMap.norm_eq_iSup_norm` identifies it with
  `⨆ h, ‖f h‖`. K is nonempty because it is a group.
- Existence and B-linearity: `∃ I : C(K, B) →L[B] B`. The continuous-linear packaging
  adds no hypothesis or conclusion beyond the displayed contraction bound: that bound
  already implies continuity of a linear map in the node.
- Norm bound: `∀ f, ‖I f‖ ≤ ‖f‖`; normalization: `I 1 = 1`.
- Both translation identities: the next conjunct quantifies over `a` and `f`, and
  composes f with `h ↦ a * h` and `h ↦ h * a`, respectively. Each value equals `I f`.
- Every finite-quotient function: the next conjunct quantifies over every open normal
  U, every function `g : K ⧸ U.toSubgroup → B`, and every `f : C(K, B)` satisfying
  `∀ h, f h = g (QuotientGroup.mk h)`. Its conclusion is
  `I f = (Nat.card (K ⧸ U.toSubgroup) : B)⁻¹ * ∑' q, g q`.
  The tsum is exactly the finite sum because this quotient is finite; using tsum
  avoids choosing a Fintype enumeration. No continuity of g is additionally assumed.
- Every profinite parameter: `∃ J : (P : Profinite.{w}) →
  C(P × K, B) →ₗ[B] C(P, B)`. Mathlib's Profinite bundles precisely a compact
  Hausdorff totally disconnected space, including the empty space. Any such
  parameter can be bundled by `Profinite.of`. The output lies in C(P,B), so the
  claimed continuity is part of the type, not a discarded assertion.
- The parameter integral is the specified one: `∀ P f p, J P f p = I (f.curry p)`;
  the definition of `ContinuousMap.curry` gives `f.curry p h = f (p,h)`.
- C(P,B)-linearity: J P is B-linear, hence additive, and
  `J P ((c.comp ContinuousMap.fst) * f) = c * J P f` for every c and f
  supplies the full pointwise C(P,B)-scalar compatibility. Together these are
  exactly linearity over C(P,B) acting on the source by first-coordinate pullback;
  no second module-action definition is introduced.
- Naturality: for every P,P', `a : C(P',P)`, and f,
  `J P' (f.comp (a.prodMap (ContinuousMap.id K))) = (J P f).comp a`.
- Finite sums: the final conjunct asserts preservation of every sum indexed by
  `Fin n`, for arbitrary n, which represents every finite sum, including n=0.
- Size convention: `universe u v w` is explicit. K, B, and the profinite parameter
  universe are independent. P and P' range over the same arbitrary chosen parameter
  universe, as allowed by the fixed universes of the node. No site/derived object
  or universe equality is imposed here; the size dependency is metatheoretic.

Dependency declarations read and used:

- `def-weil-l-adic-numbers` is a Mathlib node, whose `mathlib_match` names
  `Padic`, in `Mathlib.NumberTheory.Padics.PadicNumbers`. Its full definition and
  docstring identify it as the p-adic Cauchy completion of Q. The theorem uses it
  directly, without creating a replacement coefficient field.
- `def-weil-size-convention` has its recorded convention-only binding and no Lean
  declaration. The theorem supplies explicit universes, as its record instructs.
- Proof dependency `lem-sfb-profinite-finite-map-approximation` is imported via
  `Mathlib.Topology.Separation.DisjointCover`; its recorded
  `ContinuousMap.exists_finite_approximation_of_mem_nhds_diagonal` was read with its
  signature and docstring. It applies to compact Hausdorff totally disconnected X
  and gives the finite discrete approximation, allowing empty X.
- Proof dependency `lem-sfb-dense-subspace-contractive-extension` is imported via
  `Mathlib.Analysis.Normed.Operator.Extend`; its recorded `LinearMap.extendOfNorm`,
  `extendOfNorm_eq`, `norm_extendOfNorm_apply_le`, `extendOfNorm_unique` and docstrings
  were read. Specializing the dense linear map to the subspace inclusion and C=1
  gives the node's contractive extension, without requiring completeness of E.
- Other Mathlib interfaces inspected: `OpenNormalSubgroup`, its normality instance,
  `Subgroup.quotient_finite_of_isOpen`, `ContinuousMap.curry`,
  `ContinuousMap.fst`, `ContinuousMap.prodMap`, `Profinite` and `Profinite.of`.

Edge cases checked before writing:

- Trivial K: the functional is evaluation at its unique point; all quotient orders
  are one and the normalization/formula agree.
- Finite K of order prime to ell: the normalized finite average satisfies the bound
  because the denominator has norm one. All stated identities are permutation or
  linearity identities, including quotient factorization.
- K cannot be empty because of its group identity. P and P' may be empty; J then
  has the unique continuous-function output and the naturality identity still makes
  sense. No Nonempty parameter hypothesis is imposed.
- The zero function, zero parameter scalar, U=K, n=0 finite sum, and ell=2 all fit.
  Nontrivial characteristic is excluded precisely by containing Q_ell. B itself
  need not be locally compact, discretely valued, or a finite extension of Q_ell.
- Removing prime-to-ell is invalid: in a finite quotient of order divisible by ell,
  the average of a single-coset indicator has norm greater than one. The actual
  statement retains that hypothesis. No counterexample to the node was found.

Searches made (no exact existing statement found):

- msearch leanfinder: "Bounded normalized nonarchimedean integral on continuous
  complete p adic valued functions on a pro prime to p profinite group". Eight
  hits about Mahler bases and PadicInt additive characters; no invariant integral
  on arbitrary pro-prime-to-ell groups or the parameter assertion.
- msearch loogle: `"integral", "Nonarchimedean"`; zero hits.
- msearch grep: `(haar|Haar|integral).*(Padic|Nonarchimedean)|
  (Padic|Nonarchimedean).*(haar|Haar|integral)`; four Bernoulli pIntegral hits,
  concerning rational p-integrality, not this integral.
- msearch leansearch: "Normalized translation invariant p adic integral on continuous
  functions on a profinite group with prime to p finite quotients". Eight hits;
  real Bochner/Haar integration identities and the PadicInt definition. The Haar
  results require NormedSpace ℝ and do not supply the specified coefficient field.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for
  `prime.to.*integral|completeScalarIntegral|scalarIntegral|` plus this node id:
  only unrelated scalar-model names and no copy of this statement. Further
  `profinite.*[Ii]ntegr|[Ii]ntegr.*[Pp]rofinite|[Pp]rimeTo.*[Ii]ntegr|`
  `[Nn]onarchimedean.*[Ii]ntegr` found coefficient/realization modules and no match.
- The prescribed grep of the node id in `lean/WeilConjectures` found no match.
  rg for the proposed full declaration name in Mathlib, both project roots, and
  `dag/lean_names_upstream.json` found no collision.
- DAG searches for scalar/normalized integrals gave the present item and its
  surrounding scalar comparison nodes; no existing Lean-bound equivalent.

Validation: scompile.py compiled the delivered module both as a sandbox and with its
library module name, cleanly, in 5.8 s and 2.9 s respectively. The preserved proof
is `sorry`; no proof was supplied at this stage. The node copy changes only `lean`.

## Second reading by NR

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
