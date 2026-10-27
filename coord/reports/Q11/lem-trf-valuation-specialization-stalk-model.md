## Worker report

The module `Sheaf.AlgebraicGeometry.ValuationSpecializationStalkModel` states
`AlgebraicGeometry.ValuationSpecialization.valuation_specialization_stalk_model` with one
`sorry`. The concrete helper declarations only expose canonical stalks, scalar maps,
quotients, scalar extensions, localizations and pulled-back germs. No theorem is proved,
no data is postponed, no statement is corrected and no dependency record is changed.

Source checked: `literature/stacks-project/more-morphisms.tex`, Tag 0GSI,
`lemma-associated-point-specializes`, third proof paragraph, lines 5207–5252. The local
calculation does not require the flatness or association assumptions of the encompassing
specialization theorem. Its proof docstring expands all eight steps of the DAG proof.

Clause-by-clause correspondence:

- A valuation domain is `{A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]`.
  The fraction field is the canonical `FractionRing A`; the closed point is
  `IsLocalRing.closedPoint A`, with residue field A/m_A. There is no restriction on
  the rank of the valuation. The base is exactly `Spec (.of A)`.
- The named morphism is `f : X ⟶ Spec (.of A)` with `[LocallyOfFiniteType f]`.
  `F : X.Modules` and `hF : F.IsQuasiCoherentFiniteType` supply exactly quasi-coherence
  and finite type, using the recorded conjunction, without coherence or flatness.
- The point y of the generic fibre is encoded by its image in X and
  `hy : (f y).asIdeal = ⊥`. The fibre projection is a homeomorphism onto the inverse
  image of its base point, so this encoding includes precisely all points of X_t.
- The reduced induced closure Y is the existing
  `(Scheme.IdealSheafData.vanishingIdeal ⟨closure {y}, isClosed_closure⟩).subscheme`,
  not a freely chosen closed subscheme. Its map to S is its closed immersion composed
  with f. The component and its generic point are the existential C,z in hcomponent,
  with `C ∈ irreducibleComponents ...`, `IsGenericPoint z C` and image equal to x.
  `hx : f x = IsLocalRing.closedPoint A` records x's membership in the closed fibre.
  This follows already from hcomponent and excludes no case.
- B is literally `X.presheaf.stalk x`; N is the recorded
  `(RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F`, abbreviated `stalk F x`.
  The map A→B is `baseMap f x`, the composite of `StructureSheaf.toStalk A (f x)`
  and `f.stalkMap x`.
- The first three conclusions are `IsLocalHom (baseMap f x)`,
  `(baseMap f x).EssFiniteType` and `Module.Finite B N`.
- The prime q is quantified in `PrimeSpectrum B`, and `(X.fromSpecStalk x) q = y`
  specifies precisely the generalization prime. Its contraction is explicitly
  `q.asIdeal.comap (baseMap f x) = ⊥`.
- `closedIdeal f x` is the extension of `IsLocalRing.maximalIdeal A` to B.
  `(q.asIdeal ⊔ closedIdeal f x).radical = IsLocalRing.maximalIdeal B` is exactly
  the radical of q+m_A B; ideal supremum is ideal sum.
- `closedRing f x` is B/m_A B. `closedModule f F x` has exactly the carrier
  N/(m_A B • ⊤), with its quotient-ring module action transported through Mathlib's
  `TensorProduct.quotTensorEquivQuotSMul`; this is the canonical quotient action.
  `IsNoetherianRing (closedRing f x)` and `Module.Finite ...` are both explicit.
- `eR` and `eL` identify R and L with the stalks at `f.asFiber x` on the actual
  scheme fibre over `f x` (equal to s by hx). The module uses `tensorPullback`,
  as the module-pullback node requires. The formula for eR identifies the quotient
  map with `f.fiberStalkMap x`. The formula `eL (r • m) = eR r • eL m` specifies
  compatibility of scalars. The formula on every section germ specifies that the
  class of an original germ maps to its pulled-back germ.
- `genericRing f x` is literally B⊗_A FractionRing A, with the algebra action given
  by baseMap, and `genericInclusion` is b↦b⊗1. The prime qK has the required equality
  `qK.asIdeal = q.asIdeal.map (genericInclusion f x)`; hence its primality is included.
- The generic module is encoded as B_K⊗_B N using Mathlib's `extendScalars`. This is
  canonically N⊗_A K by tensor cancellation and symmetry (the existing tensor-product
  and localization-over-base APIs), with n⊗1 represented by 1⊗n. Its localization
  is literally `LocalizedModule qK.asIdeal.primeCompl ...`, with Mathlib's actual
  localized-ring module structure. T is `Localization.AtPrime qK.asIdeal`.
- `eT` and `eP` identify T and P with the generic-fibre stalks at `f.asFiber y`.
  Their scalar-compatibility equation and normalization on every germ specify the
  canonical comparisons, including denominators: ring homomorphisms preserve
  inverses of the inverted elements; semilinearity does the same for module fractions.
  Germs at x generate B,N, and their scalar fractions generate T,P. Thus these are
  compatible canonical comparisons, not merely unrelated additive equivalences.
- The final two iff clauses use the recorded `Scheme.Modules.relativeAssassin`
  and `RingTheory.annihilatorAssociatedPrimes`. In the R clause, m_R is written as
  the image of m_B under the quotient map; locality of A→B implies m_A B⊆m_B,
  so this is exactly the maximal ideal of R. This spelling avoids requiring a
  separately chosen local-ring instance on the quotient. The T clause uses the
  canonical `IsLocalRing.maximalIdeal T` directly.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`:
  `Scheme.Modules.IsQuasiCoherentFiniteType` and its underlying Mathlib predicates.
- `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral`. The reduced closure is the
  integral closed subscheme from the node, not a new integrality assumption.
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`:
  `Scheme.IdealSheafData.reduced_induced_closed_subscheme`, `vanishingIdeal` and
  its existing `.subscheme` and `.subschemeι` construction.
- `Mathlib.Topology.Sober`: `IsGenericPoint`; `Mathlib.Topology.Irreducible`:
  `irreducibleComponents`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`, `asFiber`.
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`:
  `PresheafOfModules.moduleStalkFunctor`, `stalkObj`. On scheme module sheaves,
  as the dependency record expressly directs, use the same carrier through
  `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`:
  `RingedSpace.moduleStalkFunctor`.
- `Mathlib.RingTheory.EssentialFiniteness`: `RingHom.EssFiniteType`.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`, together with
  the ordinary extension-of-scalars construction and quotient tensor equivalence.
- `Mathlib.Algebra.Module.LocalizedModule.Basic`: `LocalizedModule`, `mk`,
  `moduleOfIsLocalization`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction` publicly exposes the
  unchanged upstream `Scheme.Modules.tensorPullback`. The normalized section unit
  used here is `Classical.choose (exists_tensorPullbackAdjunction g)` from
  `WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction`, as the standing brief
  prescribes. No duplicate pullback or adjunction is introduced.
- `Sheaf.AlgebraicGeometry.RelativeAssassin`: `Scheme.Modules.relativeAssassin`.
- `WeilConjectures.RingTheory.AnnihilatorAssociatedPrimes`:
  `RingTheory.annihilatorAssociatedPrimes`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.

The module imports the available proof dependencies for the eight-step plan, including
FibreStalkQuotient, ValuationClosedFibreNoetherian, AffineModuleGermLocalization,
FiniteTypeModuleStalkFinite, TensorPullbackStalk, SpecLocalRingCanonicalMorphism,
localization over base, minimal-prime radical localization and affine fibre products.

Edge cases checked before and after writing: A a field (generic and closed points
coincide, generic base extension and closed quotient specialize to identities), arbitrary
higher-rank valuation rings, F=0 (both assassins empty, zero stalk modules allowed), and
empty X or empty Y_s (the point/component hypotheses have no witness). A=Z_(p), X=A[T],
y=(T) and x=(p,T) give q=(T) in the local ring and √(q+pB)=m_B. With y=(pT−1), Y_s
is empty, and hcomponent correctly has no witness. No Noetherian hypothesis on A or X,
no flatness hypothesis on F, and no finite-presentation hypothesis is added.

Searches for an existing whole statement (all through the prescribed msearch.py):

- LeanFinder: "valuation scheme specialization local stalk model quotient closed fibre
  generic fibre localization associated points" returned eight structure-sheaf stalk
  specialization identities, none giving the combined model or module comparisons.
- Loogle: "AlgebraicGeometry.Scheme.fromSpecStalk, AlgebraicGeometry.Scheme.Hom.fiber,
  IsLocalHom" returned zero hits.
- Mathlib grep: `valuation.*stalk|stalk.*valuation|fiberStalkMap` in AlgebraicGeometry
  returned ValuativeCriterion's valuation factorization and OrderOfVanishing, no match.
- LeanSearch: "local stalks scheme fibre quotient maximal ideal localization generic
  fibre module valuation ring" returned eight individual affine germ/localization and
  fibre stalk declarations, no combined statement.
- Local rg in lean/WeilConjectures and lean/Sheaf for valuation/stalk, scalar-stalk and
  generic-fibre-stalk patterns found only individual helpers and neighbouring flat
  specialization/dimension results. The required grep by the exact blueprint id in
  lean/WeilConjectures returned no declaration. Namespace/name search for
  `ValuationSpecialization|valuation_specialization_stalk_model` in both project
  libraries and Mathlib found no existing declaration.

Validation: scompile.py was used for every compiler invocation. Initial errors in the
quotient scalar-action inference, localization instance arguments and dependent point
transport were repaired. A later compile passed both sandbox and final module checks
without errors or warnings. The final import/closure-expression adjustment is compiled
again before delivery. Every universe is explicit, with autoImplicit=false.

## Second reading by Q11

This is the dispatch worker's separate clause audit, not a claim to have started an
independent agent: the dispatch instructions forbid subagents and the maintainer supplies
independent review. I reopened the node and the final signature. Each hypothesis and each
conclusion is matched above. I removed a proposed alias for the closure-to-base map,
using the existing vanishing-ideal construction inline. I checked that the generic module
encoding is canonically the node's N⊗_A K, and that m_R is the actual quotient maximal
ideal. The equations on section germs determine the ring/module comparisons and do not
replace canonical maps by arbitrary isomorphisms. No remaining mismatch was found.
