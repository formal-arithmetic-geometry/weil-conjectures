## Worker report

The delivery states `lem-weil-point-automorphism-transport-scalar-extension` in
`Sheaf.Paper.PointAutomorphismTransportScalarExtension`. There are four postponed
theorems, all for this node: `WeilConjectures.pointTransportPrimeUnits`, `WeilConjectures.point_automorphism_transport_scalar_extension`,
`WeilConjectures.point_automorphism_transport_scalar_unit`, and
`WeilConjectures.point_automorphism_transport_scalar_tower`. Their proofs are exactly `sorry`.
All helper definitions have actual data from the existing constructions. The named
prime-invertibility consequence is a theorem with a postponed proof, rather than a proof
hidden inside a definition. The natural-language
statement, dependencies, proof and proof dependencies of the item are unchanged.

Hypothesis and clause correspondence:

- The fixed `p,a,q,k₀,k` are `D : FiniteFieldDatum.{u}`; its structure contains primality,
  positive exponent, `q = p^a`, the specified finite base field and algebraic closure.
- The coefficient prime is `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)`.
- Finite coefficient fields are `E,L : Type u`, each with `Field`, `Algebra ℚ_[l]` and
  `FiniteDimensional ℚ_[l]`. The inclusion is `ι : E →ₐ[ℚ_[l]] L`. This is the
  usual model-of-an-inclusion interface of the recorded scalar comparisons; algebra
  homomorphisms between these fields are injective. It includes actual subfield inclusions
  in any fixed algebraic closure, arbitrary ramification, and the identity inclusion.
  Neither an additional E-algebra structure on L nor an unrelated coefficient map is chosen.
  The valuation rings and uniformizers are the existing `Padic.coefficientExtension*`
  constructions, with their actual completed sheaves, not discrete replacement coefficients.
- The point is literally `Spec (.of D.k)`. The morphism `g` has those source and target,
  with `[IsIso g]`. There is no condition that it be a morphism over k₀.
- The site is Mathlib `Scheme.ProEt`, with its recorded topology. Its scheme universe
  is `u`, its object universe `u+1`, and its morphism universe `u`. Section modules
  use universe `u+1`. These site universes are not identified. Finite coefficient
  models use `Type u`, as in the existing point-sections and scalar-comparison interfaces.
- `K : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))` with
  `hK : sfIntegralConstructible l E (Spec (.of D.k)) K` is exactly bounded
  constructibility and derived completeness with a common finite cohomological interval.
  `pointIntegralConstructible_iff` converts to the legacy predicate only when calling
  the already recorded sections interface. It adds no assumption.
- `G_F` is `inverseImageIntegralDerived l F g`, whose scalar action is transported
  through the inverse of the completed coefficient map. `P_F` is the existing
  `integralDerivedPullback l F g`. `T` is the existing `integralScalarExtension`.
  The independent-universe interface and the original interface unfold to the same
  normalized localization witness in this specialization.
- Sigma is `pointAutomorphismRestrictionDerived D l hl F g`. Its module map is
  the section-normalized transformation of the recorded restriction theorem, followed
  by restriction along the inverse ULift ring equivalence. Its derived map uses
  `Localization.liftNatTrans` and `Functor.mapDerivedCategoryCompIso`. Thus it is the
  same restriction/coprojection map on complexes, with the required actual Gamma/G endpoints.
- Ordinary scalar extension C and its tensor comparison b are the existing
  `integralOrdinaryDerivedScalar` and `isomorphismScalarTensorDerived`. The universal
  derived scalar model is identified with this exact finite-free model by the recorded
  `isomorphismScalarModel_existsUnique`, including its chi normalization. No new C is defined.
- `pointTransportBetaIso` is chi at G K inverse, then b, then G(chi at K).
  Its hom unfolds to the recorded `isomorphismComparisonScalarBeta`. This merely
  packages that existing comparison as an isomorphism so its inverse can be used.
- `pointTransportPhi` is exactly `pointSectionsScalarExtensionIso`, hence precisely
  `(Gamma(chi) theta)⁻¹`, with no alternative sections comparison. `pointTransportPsi`
  is Gamma(beta⁻¹) followed by phi at G K.
- The main theorem's first conjunct is sigma_L at T K followed by psi, equal to
  phi at K followed by the module scalar extension of sigma_E. This is the first
  displayed equation, written in Lean's left-to-right `≫` convention.
- `pointTransportKappa` is exactly `inverseImagePullbackComparisonDerived`.
  `pointTransportPrimeUnits` states the consequence that the nonzero coefficient prime
  is a unit in each stalk, so the comparison API needs no additional invertibility hypothesis.
  Its postponed proof plan maps the existing finite-field unit through the actual germ map.
  `pointTransport` is sigma followed by Gamma(kappa), exactly t of the node.
- `pointTransportAlphaIso` is exactly `scalarPullbackCompleted`, whose hom is the
  recorded `isomorphismComparisonScalarAlpha`. `pointTransportPullbackPsi` is
  Gamma(alpha⁻¹) followed by phi at P K. The main theorem's second conjunct is
  t_L at T K followed by this map, equal to phi at K followed by tensor of t_E.
- Admissibility of G K and P K is supplied by
  `isomorphismComparisonInputs_constructible`, the specialized existing assertion of
  the isomorphism-derived-pullback dependency. The two helper definitions merely
  project its two proofs, including derived completeness.
- The main theorem's third conjunct is the second equation after applying
  `pointModuleDerivedRationalization l L`. The right endpoint is identified using
  `pointDerivedTensorRationalization`; the named rational phi is exactly
  `pointRationalSectionsScalarExtensionIso`. The right map is coefficient-field tensor
  of `pointModuleDerivedRationalization l E` applied to t_E. This is t^(E,rat).
  It operates on integral representatives and tensors morphisms with the field, as
  in `sfRationalConstructibleCategory`; it never takes idempotent completion.
- The unit theorem has four conjuncts: the psi and psi-prime equations, each integral
  and rational. Each is followed by the existing module/field multiplication unit,
  and equals Gamma applied to G or P of the existing `pointIntegralScalarUnit`.
  This expresses identity compatibility under the canonical identifications, rather
  than assuming an identity scalar functor is definitionally the identity.
- The tower theorem adds finite `M` and `j : L →ₐ[ℚ_[l]] M`, with the direct extension
  `j.comp ι`. Its four conjuncts are the psi and psi-prime equations, each integral
  and rational. The left sides are Gamma(G_M A) or Gamma(P_M A) followed by the
  direct comparison. The right sides are the L-to-M comparison at T K, the scalar
  extension of the E-to-L comparison, then the actual module/field associator.
  `pointTransportScalarAssoc` is precisely `pointIntegralScalarAssoc`, whose definition
  conjugates the ordinary associator by chi. Constructibility of T K comes from
  the existing `sfIntegralScalarExtension_constructible`.
- No naturality of t in H is asserted. Sigma's existing ambient derived naturality
  and phi's naturality are the inputs described in the proof docstrings.

Dependency declarations read and used (module names under `Sheaf.Paper` unless qualified):

- `FiniteFieldFiber`: `FiniteFieldDatum` and its field/algebraic-closure structures.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: the existing coefficient-ring
  conventions and `Padic.finite_coefficientExtensionRing`.
- The scheme-property collection defines no declaration; `[IsIso g]` is Mathlib's
  scheme-automorphism condition.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.mk`, `ProEt.topology`.
- `InverseImagePullbackComparisonDerived`: `inverseImagePullbackComparisonDerived`, with
  the publicly imported `inverseImageIntegralModules` and `inverseImageIntegralDerived`.
- `SfIntegralConstructible`: `sfIntegralConstructible`, read through `scompile.py --source`
  because its recorded source was absent in the local snapshot.
- `IntegralScalarExtensionUniverses`: `integralScalarExtensionOfUniverses`, retaining
  `IntegralScalarExtension.integralScalarExtension` with the same normalized data.
- `PointAutomorphismRestrictionNatural`: `point_automorphism_restriction_natural`,
  `pointRestrictionRaw`, `pointRestrictionCoefficientMap`, `pointRestrictionSections`.
  The two helpers in the item module name the existing normalized maps.
- `CompletedIntegralConstantMapOfUniverses`: `integralConstantToCompletionOfUniverses`.
- `FiniteFreeCompletedScalarComparison`: `completedScalarComparison`,
  `completedDerivedScalarExtension`, `finiteFreeCompletedScalarComparison`.
- `IsomorphismComparisonScalarExtension`: `isomorphismScalarTensorDerived`,
  `isomorphismComparisonScalarBeta`, `isomorphismComparisonScalarAlpha`,
  `isomorphismComparisonInputs_constructible`, `isomorphismComparison_scalarExtension`.
- `PointSectionsScalarExtension`: `pointCompletedDerivedSections`,
  `pointIntegralConstructible_iff`, `pointSectionsScalarExtensionIso`,
  `pointRationalSectionsScalarExtensionIso`, `pointIntegralScalarUnit`,
  `pointIntegralScalarAssoc`, `pointIntegralModuleDerivedTensor`,
  `pointIntegralModuleDerivedUnit`, `pointIntegralModuleDerivedAssoc`,
  `pointModuleDerivedRationalization`, `pointDerivedTensorRationalization`, and the
  corresponding coefficient-field derived tensor/unit/associator.
- `IsomorphismDerivedPullback`: `isomorphismIntegralDerivedPullback_termwise`,
  retained through the scalar-comparison interface that supplies its admissibility specialization.
- `IntegralOperationsScalarComparisons`: `scalarCompletionIso`, `scalarPullbackCompleted`,
  and the specified ordinary comparison/unit/tower data.
- `SfRationalizationKaroubi`: `sfRationalConstructibleCategory`, raw localization with
  unchanged objects and tensor-Hom fraction-field coordinates.

Proof-only imports retain the stated K-flat tensor model, independent-coefficient K-flat
resolution, sheaf tensor, and coefficient-complex rationalization dependencies. The three
proof prerequisites `lem-weil-point-derived-sections-tensor-descent`,
`lem-weil-point-finite-free-sections-tensor`, and
`lem-weil-point-derived-tensor-tower-coherence` have no recorded Lean modules in the
read DAG, so no nonexistent import was added. None is needed to type the statement.

Searches before writing:

- `msearch.py ... leanfinder "inverse image at a geometric point commutes with completed
  scalar extension and global sections"`: eight results about ordinary scheme sections
  and restriction; none states completed point-transport coefficient compatibility.
- `msearch.py ... loogle "CategoryTheory.Functor.mapDerivedCategoryNatTrans,
  CategoryTheory.Functor.mapDerivedCategoryCompIso"`: zero hits, unknown first identifier.
  Reading the source located the exact `Localization.liftNatTrans` and the upstream
  exact-functor composition isomorphism actually used.
- `msearch.py ... grep "scalar.*[Tt]ransport|[Tt]ransport.*scalar|mapDerivedCategoryNatTrans"
  CategoryTheory`: zero hits.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for point transport/restriction and
  automorphism scalar comparisons found the recorded restriction and comparison modules,
  finite Frobenius-power transport, and unrelated point/fibre transport; no exact statement.
  `grep -rn` for this node id in `lean/WeilConjectures` found no match.
- Final collision search for the new public names in both roots, Mathlib, and
  `dag/lean_names_upstream.json` found no existing declarations.

Edge cases checked before writing: g=id, any g not over k₀, K=0, torsion K (whose rationalization
can vanish), the identity coefficient inclusion, a tower with either inclusion the identity,
nontrivial ramification, and unbounded representatives of bounded-constructible derived objects.
The equations have identical typed endpoints in all these cases. No flatness condition on K,
no bounded flat representative, no invertibility of t, and no completeness condition on the
ambient domain of sigma were added. The completed ring is not replaced by a discrete constant ring.
No statement dispute or mathematical correction was needed.

## Returned-delivery repair

The return at immutable head `a5562f0bab6d` identified H13/H2: the dependency
record replaced Q57's usable theorem and its 12 declarations by a def-only record.
The sandbox dependency JSON is now byte-identical to live, including its theorem,
all 12 declarations and all non-Lean fields. No dependency-record change is delivered.
The obsolete `PointAutomorphismRestrictionDerived.lean` is removed from this packet.
Its two definitions, `pointAutomorphismRestrictionModules` and
`pointAutomorphismRestrictionDerived`, now live in the item's
`PointAutomorphismTransportScalarExtension.lean`, and both are listed in the item's
`lean.declarations`. Their blueprint docstrings name this item. The item directly
imports `PointAutomorphismRestrictionNatural` and `PointSectionsScalarExtension`.
The definitions' signatures and bodies are retained; only their location and ownership
changed. The original dependency theorem remains the source of the normalized map.
The item JSON was refreshed from live and changed only in `lean`.

The prime-unit duplication was advisory: the cited proved `frobeniusPointPrimeUnit`
lives downstream. This repair retains the reviewed prime-unit input and does not
add a downstream import or change the mathematical statements.

## Second reading by Q29

No separate worker was started: this dispatcher brief prohibits other agents and specifies that
the maintainer independently reviews the delivery. The worker's own second pass re-read the node
and the item module against the correspondence above. It checked the order of `≫` in the two integral
equations, the fact that beta's inverse is between the actual completed endpoints, the use of
phi=(Gamma(chi) theta)⁻¹, the specified alpha and kappa, all four unit and all four tower equations,
and the rationalization associators. The derived sigma is named by helpers owned by this item,
using the unchanged dependency theorem and its section normalization; the unit equations
explicitly include multiplication and Gamma(G/P(unit)), rather than an ill-typed literal identity. Compilation then verified these
endpoints. This is a self-check, not a claimed independent review.

Repair self-check: I compared the saved packet with the returned description and the
current live nodes. Both moved helpers have unchanged signatures and bodies; their
only docstring change is the blueprint owner. The main, unit and tower theorem
signatures are unchanged from the returned packet. The dependency record is
byte-identical to live and still owns Q57's theorem and all 12 declarations.
Every helper in the module is listed in the item's declaration record.

Validation: the saved packet's preliminary dry run passed (`a7bb25fc479`), before
this required ownership repair. The repaired single module compiled cleanly through
`scompile.py` both at its sandbox and actual library module names (15.3 s and
14.8 s), without errors or warnings. The repaired `deliver2.py --no-push` passed
server preflight and compilation (`55241fc2e3e`). Its staged set contains only the
report, item node, and item module: the dependency record is not staged. Only the
prescribed wrappers were used; no global build or direct live-repository write occurred.
