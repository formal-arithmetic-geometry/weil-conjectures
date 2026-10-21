## Worker report

The single module `Sheaf.Paper.SemilinearFieldOperationLifts` states this compound node
in five named theorem clauses, with explicit specification definitions. Its principal
geometry/transport theorem is `WeilConjectures.semilinearFieldOperationLifts`.
Every theorem proof is `sorry`; every definition has real data. No node correction,
new independent notion, or dependency-module replacement is made.

Hypothesis and clause correspondence:

- The primes, positive exponent, q = p^a, finite field and fixed algebraic closure
  are the fields of the recorded `FiniteFieldDatum D`. The coefficient prime is
  `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)`. No coefficient invertibility assumption
  is added: `sfWeilPrimeInvertible` supplies it from the finite-field datum.
- A finite-type k₀-scheme is `T₀ : Over (Spec (.of D.k₀))` with
  `[LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom]`. Both X₀ and Y₀ have these
  binders. The morphism f₀ is an Over arrow with separatedness, local finite type
  and quasi-compactness on its underlying map. No separatedness of either model
  is required. The actual f is `((Over.pullback (Spec.map ...)).map f₀).left`.
- E is any `Type u` with `Field`, `Algebra (Padic l)` and `FiniteDimensional`;
  Ω has an independent universe v and `IsAlgClosure (Padic l) Ω`. The operations
  at E are independent of a choice of embedding in Ω; the common-stage category
  uses its actual finite subfields and equivalent small coefficient models.
  Thus the unused embedding of an abstract E is not an extra hypothesis.
- T and g_T are exactly `D.geometricFiber T₀` and `D.geometricFrobenius T₀`.
  The principal theorem asserts `IsPullback gX f f gY`. Its next equality
  `f ≫ gY ≫ aY = gX ≫ aX` says that f is over k between the restructured upper
  corners. This uses ordinary scheme maps and does not assert that g is k-linear.
- `PodRationalFrobeniusTransportSpec` retains the specified integral comparison
  to `isomorphismIntegralTermwiseInverseImage`, the inverse-composite identity
  normalized by `pullbackIdentityEpsilon`, and the reverse identity. It asserts
  additivity, finite-limit and finite-colimit preservation and equivalence for
  the actual `podCompletedModuleInverseImage` on completed modules.
- The rational Frobenius functor is the dependency's `sfWeilFrobeniusPullback`.
  Its inverse is the recorded `rationalDerivedPullback` along the literal inverse
  scheme map. Both natural inverse-composition isomorphisms are asserted. The
  forward identity is normalized to localization of the integral epsilon.
- `PodFieldOperationTransportSpec` gives the analogous common-stage equivalence,
  both inverse compositions and a finite-stage representative formula for the
  forward counit. Naturality is that of an actual natural isomorphism on the
  common-stage category, so it includes every common-field arrow, identity stages
  and successive extensions. Underlying exactness at both field stages is
  `∃ s : P.CommShift ℤ, P.IsTriangulated`, with the instance explicitly supplied
  by a lambda; no shift or triangulation on fixed pairs is introduced.
- `pod_actual_pullback_field_lifts` states the rational and common-stage canonical
  comparisons for the actual base-changed f. Its f/hf binders are an explicit
  name with equality to that map, so they do not restrict the models. The component
  equalities identify alpha and beta with `podRationalSquarePullbackComponent`
  and `podCommonSquarePullbackComponent`. These definitions are inverse first
  compositor, the scheme-square equality, and second compositor, exactly step 4
  of the node. HEq avoids expensive elaboration of the equality presentations;
  it still fixes the very same entire isomorphism and its arrow map.
- `pod_supplied_field_operation_lifts` states the three covariant lifts on the
  supplied closed operation domains of `def-exchange-projection`. Its S is that
  dependency's `ExchangeProjectionStage`, including actual operations, adjunctions,
  proper/open comparisons and compactification identifications. The equalities
  hpull/hpush/hsupport identify the operation on the two copies of the square.
  The horizontal functors are the equivalences on these domains. The theorem
  fixes alpha to inverse `S.pullbackComparison`, beta to `S.exchange`, and gamma
  to `S.compactExchange`, followed only by endpoint transports. In particular
  it uses the recorded Ex_* mate and Ex_! proper/open paste, not arbitrary maps.
  This is the parametric supplied-domain clause at either coefficient stage;
  `pod_actual_pullback_field_lifts` additionally fixes the geometric pullback
  comparison without supplying operation data.
- `PodCovariantWeilLiftSpec` and `pod_covariant_field_operation_lift` use exactly
  the existing `IsoAlgebra.mapOfNatIso`. They specify the object FK, structure
  `alpha.app K ≪≫ F.mapIso K.str`, and arrow F(u). The last equation is the
  node's displayed intertwining equation in Lean's left-to-right composition
  convention. The functor is an actual Functor, so identity/composition laws
  are included. Forgetting is equality of whole functors, including all arrows.
- `PodTensorWeilLiftSpec` uses the existing product of pairs followed by that
  transport. The structure is `mu.app (K,L) ≪≫ T.mapIso (K.str.prod L.str)`;
  the arrow is T(u,v). Both coefficient-stage tensor comparisons are explicitly
  identified with `canonicalRationalPullbackTensor` and
  `canonicalCommonStagePullbackTensor` in the transport specification.
- `podWeilHomPairs` is precisely the inverse image of the already recorded
  permitted-pair property J under forgetting. It defines no alternate perfection
  or constructibility predicate. `podWeilHomPairForget` retains the actual
  witness. `PodHomWeilLiftSpec` asserts a functor from that full subcategory of
  `(IsoAlgebra P)ᵒᵖ × IsoAlgebra P`, with structure kappa followed by
  `H.map (theta_M.inv.op, theta_N.hom)`. Its forgetful equality and explicit arrow
  equality fix the original H(u,v). The contravariant variance and inverse first
  structure are both essential and present. Each coefficient-stage kappa is
  fixed to `podRationalHomComparison` or `podCommonHomComparison`.
- `pod_tensor_hom_field_operation_lifts` is the formal two-variable functoriality
  clause; it does not assume Hom on every pair. The actual rational and common
  specializations retain `constructibleRationalHomPairs` and `commonStageHomPairs`.
  Any previously imposed site-perfect subdomain is a full-subcategory restriction
  of this same functor; it is never enlarged. At these field stages finite Tor
  is exactly the entire category by `finiteTorFieldCoefficientCategory`. Thus the
  M in D_ctf, N in D_c case retains its exact domain and does not add an integral
  finite-Tor or site-perfect hypothesis. The recorded site-perfect notions remain
  `IsSfRationalCoefficientSitePerfect` and
  `IsGeneralAlgebraicallyClosedCoefficientSitePerfect`, imported from their owner.
- All five forgetful claims are in the specifications, and no theorem claims
  new bounded-constructibility preservation or any triangulation of Weil pairs.
  For covariant operations the underlying functor is unchanged, so every existing
  exactness structure is unchanged; the theorem does not supply a new one on pairs.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, `.geometricFiber`.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`: `.geometricFrobenius` and its actual inverse.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `constructibleIntegralPullback`,
  `rationalDerivedPullback`, `commonStageDerivedPullback`, `rationalDerivedTensor`,
  `commonStageDerivedTensor`, the two permitted-Hom properties and Hom functors.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfWeilFrobeniusPullback`,
  `sfCommonStageWeilFrobeniusPullback`, `sfWeilComplex`, `sfCommonStageWeilComplex`,
  and `sfWeilPrimeInvertible`. They are the actual rational/common-stage IsoAlgebra
  constructions. The upstream IsoAlgebra transports, product and contravariant
  transport were read in full; they are reused rather than copied.
- `def-weil-scheme-morphism-properties` is a convention node, with no declaration;
  use its named Mathlib properties `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`.
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`: `Scheme.sfIntrinsicCompactSupport`,
  the finite `Rg_* j_!` construction. Its higher passage is the supplied-domain
  compactSupport/identification in `ExchangeProjectionStage`; it is not replaced
  by an arbitrary unconstrained compact-support arrow.
- `Sheaf.Paper.SfDerivedDirectImage`: `SfIntegralDirectImage` and its Roos projection
  description. Higher operation data and its adjunction are retained in the supplied
  domain stage, as required by the coefficient paragraph of the exchange definition.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage`, `.exchange`,
  `.compactExchange` and the actual defining composites.
- `Sheaf.Paper.FiniteTorAmplitudeSites`: the publicly reexported
  `finiteTorFieldCoefficientCategory`; `Sheaf.Paper.SitePerfectComplex`: the two
  field-stage site-perfect predicates listed above. No duplicate definitions.
- Proof inputs with statements are imported: FrobeniusSquareCartesian,
  IsoSectionwiseInverseImage, IsomorphismDerivedPullback, IntegralOperationsScalarComparisons,
  PullbackIdentitiesScalarExtension, IntegralPullbackComposition,
  IntegralFinitePullbackComposition, the upstream Etale Derived.Adjunctions,
  MateIsoAlongEquivalences, FrobeniusCompactSupportExchange,
  DerivedPullbackTensorIso, DerivedAutomorphismHomEvaluation. Proof inputs whose
  declarations also occur in the delivered signatures are public imports.

Edge cases checked before and after writing: empty X or Y; zero objects and arrows;
identity f and identity coefficient enlargement; arbitrary towers of coefficient
extensions; inverse first Hom structure; pairs outside the Hom constructibility
property are excluded, while no perfection or finite-Tor restriction is added at
field coefficients; nonseparated finite-type models remain allowed; Ω may live in
an independent larger universe; prime invertibility is derived and never an extra
hypothesis. Inverses are actual pullbacks along g inverse, not arbitrary chosen
quasi-inverse functors. Equality presentations are compared by HEq where necessary.

Searches (through the prescribed msearch.py, plus local reads):

- LeanFinder: “Frobenius pullback exact equivalence on rational and common-stage
  constructible categories and five operation lifts to Weil fixed pairs”: 8 hits,
  field Frobenius and generic monoidal/fiber functors, no match.
- Loogle: `IsoAlgebra.mapOfNatIso, IsoAlgebra, Functor.IsEquivalence`: 0 hits,
  unknown IsoAlgebra.mapOfNatIso in Mathlib search; its exact upstream definition
  was subsequently located and read directly.
- Mathlib grep: `mapOfNatIso|IsoAlgebra`, CategoryTheory: 0 hits.
- LeanSearch: “Frobenius transport of fixed pairs exact equivalence and tensor
  internal Hom lifts”: 8 generic tensor/closed-category hits, no match.
- rg on `lean/WeilConjectures` and `lean/Sheaf` for the item id, sfWeil lifts and
  semilinearFieldOperation: only a downstream explanatory docstring in
  FixedPairTruncationCohomology.lean, no statement. Broader semilinear/Frobenius
  module searches found the dependency APIs recorded above, and upstream
  IsoAlgebra.mapOfNatIso, mapOfNatIso₂, prod and opFunctor. The compound geometric,
  coefficient and operation statement is absent, so an existing:true record
  would omit clauses. The helper specifications only name clauses of this item.
- The dependency `lean` records, full statements and declared source signatures
  were inspected, including the finite-Tor and site-perfect distinctions.

No STATEMENT-DISPUTED or node fault was found. The node is unchanged outside lean.
All compilation uses scompile.py. The final file compiled cleanly in sandbox and
library module modes (18.2 s and 15.4 s); only expected sorry proofs are present.
The earlier expensive equality presentation was repaired using explicit canonical
component definitions and HEq; no time limit or tool was changed.

## Second reading by Q33

The dispatcher forbids starting another agent, so this is a separate self-reading,
not a claim of an independent reviewer. I reopened the node and the final module
and checked the clause correspondence above. The maintainer performs the independent
review of this direct delivery.

This reading caught and repaired an initially absent actual pullback compositor
normalization: `pod_actual_pullback_field_lifts` now fixes both component formulas,
using real definitions for their inverse-compositor/equality/compositor composites.
It also added explicit exact completed-module transport, normalization of the
rational inverse identity to the integral epsilon, and common-stage representative
normalization. It checked that the three supplied-stage comparisons retain the
actual Ex_* and Ex_! composites, the Hom first structure is inverted, and the Hom
source is exactly its original permitted-pair subcategory. No source statement,
constructibility domain, scheme separation assumption, or site universe was changed.
