## Worker report

The module `Sheaf.RingTheory.NormalConeDirectrixMinimalPrimes` states
`Ideal.normalCone_directrix_minimalPrimes`, with `sorry` as its only theorem proof.
Its six construction declarations supply the canonical residue scalar action,
the tensor fibre and its structures, homogeneous representative classes, and the
initial-form relations of the canonical component quotient. All their data are
explicit quotient, tensor, direct-sum and ideal-span constructions. No map is
chosen by an existence theorem, and no stronger hypothesis is substituted.

Hypothesis and clause correspondence:

- The Noetherian local commutative ring is `{R : Type u} [CommRing R]
  [IsLocalRing R] [IsNoetherianRing R]`. Its containing Q is `[Algebra ℚ R]`;
  a unital map from Q into this nonzero local ring is injective. Reducedness
  is `[IsReduced R]`.
- The ideal and containment are `(I : Ideal R)` and
  `(hI : I ≤ IsLocalRing.maximalIdeal R)`. The base A is literally `R ⧸ I`,
  the residue field k is literally `IsLocalRing.ResidueField R = R/m`,
  and G is the recorded `Ideal.associatedGraded I`.
- Flatness is `[Module.Flat (R ⧸ I) (associatedGraded I)]`. Mathlib's
  `Module.Flat.iff_rTensor_preserves_injective_linearMap` identifies this with
  the tensor-injectivity condition in the node; it adds no finiteness condition.
- B is `{B : Type v} [CommRing B] [Algebra k B]` with
  `(𝒜 : ℕ → Submodule k B) [GradedAlgebra 𝒜]
  [GradedAlgebra.IsStandard 𝒜]`, using the recorded standard-grading notion.
  The existing `grade_zero_eq_one` identifies B_0 with the scalar image.
  No separate nonzero assumption on B is added: the displayed fibre
  isomorphism already implies it (the fibre has degree-zero piece k).
- The nonnegative integer e is `(e : ℕ)` and the variables are `Fin e`.
  `θ` is a k-algebra equivalence from the canonical tensor fibre to
  `MvPolynomial (Fin e) B`. The tensor factors are written k tensor G,
  the canonical symmetry of the node's G tensor k.
- `hθ` is precisely preservation of the total grading. For each representative
  a in I^n, the coefficient at monomial b lies in B_(n-|b|), and it vanishes
  if |b|>n. These initial classes span every homogeneous fibre piece over k,
  so the condition on them is equivalent to preservation on the whole piece.
  Since θ is bijective, its inverse also preserves the direct-sum grading.
- `∀ p ∈ minimalPrimes R` is exactly every prime containing no smaller prime;
  no minimal prime is chosen and no irreducibility assumption is imposed.
- `normalConeFibreComponentRelations I hI p` presents the kernel of the
  canonical q_p. Its generators are the initial classes of all a in I^n
  intersect p, for all n including zero. The actual map used in the theorem
  is `Ideal.Quotient.mk` of this explicitly constructed ideal.
- The vertex quotient is
  `MvPolynomial.map (GradedRing.projZeroRingHom' 𝒜)` composed with θ.
  This uses B_0 as the concrete model of k: standardness gives B_0 equal to
  the scalar image, and k injects into B, so the canonical k-algebra
  identification B_0 = k identifies this exact map with epsilon. This is
  the degree-zero projection, not an arbitrary augmentation.
- The conclusion is the inclusion of the two `RingHom.ker` ideals. The
  quotient universal property gives exactly the equivalent surjective
  graded factorization asserted in the node. It is an equivalent
  formulation, rather than an additional independent conclusion.

Canonical component presentation, checked explicitly: in degree n,
G tensor_A k is I^n/(I^(n+1)+m I^n) = I^n/m I^n because I lies in m.
The fibre for R/p is (I^n+p)/(I^(n+1)+m I^n+p) =
(I^n+p)/(m I^n+p), including n=0. If x in I^n maps to zero, write
x=b+a with b in m I^n and a in p. Then a=x-b is in I^n intersect p,
and x and a have the same source class. Conversely these a all map to
zero. Thus the homogeneous kernels are exactly the displayed generators;
they form a graded ideal. Their ideal span is therefore the full kernel,
and the quotient by them is canonically the specified target
`gr_(I mod p)(R/p) tensor_A k`, with the canonical map on representatives.
This is a quotient presentation of the same component fibre, not an
arbitrary replacement map or an additional assumption about q_p.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`,
  `isNoetherianRing_iff_ideal_fg` (every ideal is finitely generated).
- `WeilConjectures.RingTheory.AssociatedGradedRing`:
  `Ideal.associatedGradedPiece`, `Ideal.associatedGraded`,
  `Ideal.associatedGradedCommRing`, `Ideal.associatedGradedRingHom`,
  `Ideal.associatedGradedAlgebra`. The existing ring and quotient algebra
  structures are used, without another definition of associated grading.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`, `Basic`, and `Map`, exposed
  by `Mathlib.RingTheory.TensorProduct.Basic`: `TensorProduct`,
  `TensorProduct.mk`, `TensorProduct.lift`, `TensorProduct.ext'`,
  `LinearMap.rTensor`. The scalar action comes from the actual
  `Ideal.Quotient.factor hI`.
- `WeilConjectures.RingTheory.GradedAlgebra.Standard`:
  `GradedAlgebra.IsStandard`, its finite-degree-one and generating fields,
  and `GradedAlgebra.IsStandard.grade_zero_eq_one`.
- `Mathlib.Algebra.MvPolynomial.Basic` and `Eval`: `MvPolynomial`,
  `MvPolynomial.aeval`, `MvPolynomial.algHom_ext`, `MvPolynomial.map`.
- The stated proof dependencies are imported privately:
  `Module.free_of_flat_of_isLocalRing` (`Mathlib.RingTheory.LocalRing.Module`),
  `MvPolynomial.funext_set` (`Mathlib.Algebra.MvPolynomial.Funext`),
  `Polynomial.Monic.mem_nonZeroDivisors`
  (`Mathlib.Algebra.Polynomial.RingDivision`),
  `Ideal.iInf_pow_smul_eq_bot_of_le_jacobson`
  (`Mathlib.RingTheory.Filtration`), and `Ideal.iUnion_minimalPrimes`
  (`Mathlib.RingTheory.Ideal.MinimalPrime.Localization`).

Sources read: the node's complete ten-step agent-written synthesis, and
`literature/stacks-project/algebra.tex`, labels
`lemma-reduced-ring-sub-product-fields` (00EW),
`lemma-intersect-powers-ideal-module-zero` (00IP),
`lemma-finite-flat-local` (00NZ), and `lemma-free-fibre-flat-free` (00MH).
The supporting tags do not claim to state the entire vertex assertion.
The theorem docstring preserves every step of the node's proof and its inputs.

Edge cases checked: n=0 makes the component quotient k and its kernel zero,
since every minimal prime lies in m. When e=0 there is one constant monomial,
and the vertex kills all positive B degrees. I=0 is allowed: G=R in degree
zero, its fibre is k, and the canonical component fibre is again k. The field
case R=Q is included. Vanishing graded pieces and rank-zero finite free
pieces impose no nonzero condition. The zero ring is excluded by the given
local-ring convention, matching the existence of its maximal ideal and residue
field in the node. The universes u and v are independent and explicitly bound;
no finite-type condition on R or extra residue-field equality is assumed.

Searches actually run with
`/home/ubuntu/weil-launcher-all/batch2/msearch.py O2
lem-trf-normal-cone-directrix-minimal-primes`:

- `leanfinder`: "For a reduced Noetherian local ring with flat associated
  graded algebra, a polynomial vertex of the residue fibre survives quotient
  by every minimal prime". Eight results, including
  `isStronglyTranscendental_mk_of_mem_minimalPrimes` and polynomial fibre
  quotients; none states this flat filtered-algebra vertex assertion.
- `loogle`: `"associatedGraded", "minimalPrimes"`: zero hits.
- `grep`: `directrix|associatedGraded.*minimalPrimes|normalCone.*minimal`:
  zero hits.
- `leansearch`: "A polynomial vertex of the special fibre of a flat
  associated graded ring is contained in the normal cone of every minimal
  prime quotient". Eight hits, including `Polynomial.fiberEquivQuotient`,
  Proj carrier results and homogeneous cores; none is the statement.
- Local `rg` of `lean/WeilConjectures` and `lean/Sheaf` for associated
  graded, normal cone, graded tensor, and directrix terms found the existing
  associated grading and `Ideal.associatedGradedMap` (additive only).
  Neither gives the residue-fibre component map needed here. The direct
  node-id grep in WeilConjectures gave no declaration. Searches of
  `dag/lean_names_upstream.json` and both source trees found no collision
  for any of the seven delivered declaration names.
- `tools/blueprint_refs.py search 'normal cone fibre'` gave zero blueprint
  nodes. DAG searches found this lemma and neighbouring Hilbert--Samuel and
  deformation-to-the-normal-cone nodes; none already defines these concrete
  fibre maps. These maps belong to this lemma's existing objects, so the
  authorized owning-module helper mechanism is used; no new independent
  definition node or dependency repair is needed.

Validation: `scompile.py` compiled the sandbox and final library module cleanly
(6.4 s and 7.1 s in the successful run). The first compile identified a private
`Finsupp.degree` import and the reducibility attribute for the class-valued
scalar construction; both were repaired by a public Weight import and
`@[instance_reducible]`. No diagnostic commands remain. No statement correction
or STATEMENT-DISPUTED flag is needed.

## Second reading by O2

Author's delivery check; independent review is performed by the maintainer,
as required by the dispatcher brief. Re-read the node and final signature:
all six ring hypotheses, ideal containment, flatness, the standard grading,
e, θ and its degree condition, and every minimal prime occur with the given
scope. The homogeneous quotient calculation above includes degree zero and
identifies the actual canonical map, while the degree-zero coefficient
projection identifies its vertex map. The two kernel ideals therefore have
exactly the intended meanings. No assumption of flatness of R/p, nontriviality
of a chosen graded piece, positivity of e, or finite type of R was introduced.
The only change made after compiler checking was to expose the imported
monomial degree and mark the explicit class-valued definition reducible.
