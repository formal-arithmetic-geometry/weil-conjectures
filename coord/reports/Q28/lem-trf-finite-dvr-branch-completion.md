## Worker report

`Sheaf.RingTheory.FiniteDVRBranchCompletion` states
`AdicCompletion.finite_dvr_branch_completion`, with one postponed theorem and
no definitions. The node's mathematical statement and dependency lists are unchanged.
No new node, dependency repair, statement correction or disputed statement is needed.

I read Stacks varieties.tex, lemma-normalization-same-after-completion (Tag 0C3V),
especially its final paragraph, and every statement dependency's recorded declaration.
The node abstracts the displayed product of completed local DVRs there, before the
subsequent birational comparison. The docstring contains all six node proof steps.

Hypothesis and clause correspondence (R, C and D below are explanatory names;
the Lean statement spells out the actual types, with no local abbreviations):

- The commutative rings are `(A : Type u) (B : Type v)` with `[CommRing A]`
  and `[CommRing B]`. The universes are independent.
- `[Algebra A B]` gives the ring homomorphism, and
  `hinj : Function.Injective (algebraMap A B)` says it is injective.
- `[IsNoetherianRing A] [IsLocalRing A]` give the Noetherian local hypothesis.
  The maximal ideal is `IsLocalRing.maximalIdeal A`, the unique maximal ideal.
- `hdim : ringKrullDim A = 1` is the dimension hypothesis.
- `[Module.Finite A B]` states that B is a finite A-module.
- `hbranch` quantifies over `(IsLocalRing.maximalIdeal A).primesOver B`.
  `Ideal.primesOver` is exactly the subtype of prime ideals whose contraction is
  the maximal ideal, not a selected collection of branches. The hypothesis asserts
  `IsDomain (Localization.AtPrime q.1)` and, with this witness available as an
  instance, `IsDiscreteValuationRing (Localization.AtPrime q.1)`. It includes the
  original requirement that a DVR is not a field.
- R is literally `AdicCompletion (IsLocalRing.maximalIdeal A) A`. C is literally
  `B ⊗[A] AdicCompletion (IsLocalRing.maximalIdeal A) A`, in the node's tensor order.
- Finiteness of the set of branches is the conclusion
  `Finite ((IsLocalRing.maximalIdeal A).primesOver B)`, not a hypothesis.
- The product isomorphism is `e : C ≃ₐ[B] (∀ q, D q)`, where D q is literally
  `AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q.1))
  (Localization.AtPrime q.1)`. Its B-algebra structures are the tensor left inclusion
  and localization followed by completion. Thus B-compatibility is part of e's type.
- Canonicity and R-compatibility are specified by ring maps `g q : R →+* D q`:
  for every n, a in R, and r in A representing the n-th coordinate of a, the n-th
  coordinate of `g q a` is the class of `algebraMap A (Localization.AtPrime q.1) r`.
  Thus g is the completed local map, characterized on all quotient coordinates.
  The equation `e (1 ⊗ₜ[A] a) q = g q a` expresses R-compatibility. Combined with
  B-linearity, this fixes e on all pure tensors. No arbitrary equivalence is substituted
  for the canonical comparison. These conditions express, rather than strengthen,
  the node's canonical isomorphism requirement.
- Each factor's DVR and normal-domain properties are
  `∀ q, ∃ _ : IsDomain (D q), IsDiscreteValuationRing (D q) ∧ IsIntegrallyClosed (D q)`.
  For a domain, this uses its fraction field exactly as in the node.
- Flatness of A to R is `RingHom.Flat (algebraMap A R)`.
- The structural map i is exactly `Algebra.TensorProduct.includeRight`, sending r
  to `1 ⊗ₜ[A] r`; its conclusion is `Function.Injective` of this map.
- Reducedness is `IsReduced R ∧ IsReduced C`, with no domain condition on R or C.
- R's remaining properties are `IsNoetherianRing R`, `IsLocalRing R`, and
  `ringKrullDim R = 1`.
- Finiteness of C over R is `RingHom.Finite includeRight.toRingHom`. This is
  definitionally `Module.Finite R C` for the R-algebra structure induced by i;
  this encoding avoids needing a file-local tensor right-algebra instance.
- Integrality over R is `RingHom.IsIntegral includeRight.toRingHom`, namely a
  monic equation for each c with coefficients mapped by i.
- Noetherianity of C is `IsNoetherianRing C`.
- The last conclusion is `IsIntegrallyClosed C`. Its definition is
  `IsIntegrallyClosedIn C (FractionRing C)`; `FractionRing C` is the localization
  at `nonZeroDivisors C` even for rings with zero divisors. Thus this is precisely
  integral closedness in the total fraction ring, without assuming C is a domain.

Statement dependency declarations read and reused:

| Node | Module | Declaration |
| --- | --- | --- |
| def-weil-pbc-noetherian-ring | Mathlib.RingTheory.Noetherian.Defs | IsNoetherianRing |
| def-weil-pbc-krull-dimension-ring | Mathlib.RingTheory.KrullDimension.Basic | ringKrullDim |
| def-weil-finitely-generated-module | Mathlib.RingTheory.Finiteness.Defs | Module.Finite; RingHom.Finite |
| def-sc-discrete-valuation-ring | Mathlib.RingTheory.DiscreteValuationRing.Basic | IsDiscreteValuationRing |
| def-weil-pbc-localization-at-prime | Mathlib.RingTheory.Localization.AtPrime.Basic | Localization.AtPrime |
| def-weil-pbc-adic-completion | Mathlib.RingTheory.AdicCompletion.Basic; Mathlib.RingTheory.AdicCompletion.Algebra | AdicCompletion; AdicCompletion.evalₐ; canonical algebra structures |
| def-weil-module-base-change | Mathlib.LinearAlgebra.TensorProduct.Tower; Mathlib.RingTheory.TensorProduct.Basic | TensorProduct; Algebra.TensorProduct.includeRight |
| def-weil-pbc-integral-closure | Mathlib.RingTheory.IntegralClosure.Algebra.Basic; Mathlib.RingTheory.IntegralClosure.IntegrallyClosed | IsIntegral; RingHom.IsIntegral; IsIntegrallyClosedIn; IsIntegrallyClosed |
| def-weil-pbc-flat-ring-map | Mathlib.RingTheory.RingHom.Flat | RingHom.Flat |

All recorded statement-dependency modules are public imports; completion Basic
is publicly imported by completion Algebra. The currently stated proof inputs
are non-public imports: `WeilConjectures.RingTheory.CompletionFiniteExtension`
(`AdicCompletion.completion_finite_extension`), `CompletionOfDVR`
(`AdicCompletion.isDiscreteValuationRing`), `AdicCompletionNoetherian`
(`AdicCompletion.isNoetherianRing`), and `CompletionDimension`
(`RingTheory.completion_dimension`). Mathlib proof inputs are completion flatness
(`AdicCompletion.flat_of_isNoetherian`, AdicCompletion.AsTensorProduct), localness
(AdicCompletion.LocalRing), PID normality (PrincipalIdealDomain, already imported by
DVR.Basic, and Polynomial.RationalRoot), finite-algebra Noetherianity
(`IsNoetherianRing.of_finite`, Noetherian.Basic), finite-algebra integrality
(`Algebra.IsIntegral.of_finite`, IntegralClosure.Algebra.Basic), and the fraction
relation (LocalizedModule.Basic). Their declarations and source signatures were read.

Edge cases checked before writing:

- The zero ring cannot have dimension one; no extra Nontrivial hypothesis is added.
  B cannot be zero under the stated injection from A.
- A field branch is excluded by the original DVR hypothesis and by Mathlib's DVR class.
- An empty branch subtype is allowed syntactically, and its product is the zero ring.
  Integral lying over makes it impossible under these hypotheses; no extra
  nonemptiness assumption is inserted.
- One branch, a ramified finite DVR extension, and several branches are all covered.
  For A a DVR and B = A × A with the diagonal inclusion, C has zero divisors and
  is reduced and integrally closed in its total fraction ring. It is not assumed a domain.
- The nodal example A = k[[x,y]]/(xy), B = k[[x]] × k[[y]] has two complete DVR
  factors. A is reduced and is not assumed normal or a domain.
- n = 0 in the quotient characterization gives the zero quotient and adds no
  restriction. Residue characteristic is unrestricted.

Searches made using the prescribed msearch.py wrapper:

- LeanFinder query: "A finite algebra over a Noetherian local ring with DVR branches
  has completed tensor product a finite product of completed DVRs, reduced and
  integrally closed in its total quotient ring". Eight hits: mainly valuation
  completions of Dedekind fraction fields, DVR equivalences and completeIntegralClosure.
  None states this product and conjunction for ideal-adic completion.
- Loogle query: `AdicCompletion, Module.Finite`. Ten hits, including
  `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian`, exactness and tensor
  injection results. These give components, not the required full statement.
- Grep of Mathlib/RingTheory:
  `completion.*[Dd][Vv][Rr]|[Dd][Vv][Rr].*completion|AdicCompletion.*IsDiscreteValuationRing`.
  No hits.
- LeanSearch query: "A finite algebra with discrete valuation local branches has
  completed tensor product a product of complete discrete valuation rings". Eight
  hits, including the finite-module completion tensor equivalence, tensor ring instance,
  finite base-change results and a different valued-field compactness theorem. No match.
- rg in both project Lean roots for `completion.*branch`, `branch.*completion`,
  `finite_dvr_branch` and the exact node id. Hits concern geometric branch calculations
  that use the algebra input, not a declaration of this statement. The exact id has
  no source hit. No preexisting definition or theorem was duplicated.

Validation: scompile.py returned exit 0 against current server sources. The server
confirmation compiled the statement in 1.7 seconds without errors or non-sorry warnings.
Its preliminary overlay attempt ran out of disk space; the prescribed wrapper recovered
by confirming on the server. No live source or shared-repository Git mutation was made
directly. Delivery uses only the prescribed wrapper.

## Second reading by Q28

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
