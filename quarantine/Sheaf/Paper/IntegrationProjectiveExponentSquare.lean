/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G7
-/
module

public import Sheaf.Paper.IntegrationExponentTransposeData

/-! # Exponent transport: a step of the normalized integration argument -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ)

/-- Root transitions preserve the actual unit--Chern decomposition on both sites.
Source: Stacks 03PK, section-kummer; accepted exponent-transport proof Steps 6--7.
(blueprint: lem-pur-projective-exponent-square).
Proof: the root-power transition carries the Kummer boundary of the infinity divisor
to the boundary at the smaller exponent, since the Kummer exact sequences commute
with the root-power maps. Its composite with the divisor constant map has the same
property. Naturality of the adjunction unit proves the other component square.
The biproduct universal property combines the two pro-etale component squares.
Use p1KummerTraceSiteTransport at each exponent and naturality of the proper mate
to identify the compared ordinary square with this pro-etale square. Comparison
is fully faithful on the bounded shifted lines and their projective decompositions,
so it reflects that square. No trace or inverse equation is assumed here.
-/
theorem integrationProjectiveExponentSquare (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) :
  IntegrationDecompositionSquare
    (integrationLineTransition l E n S hS r s hrs hr hs).hom
    ((Etale.ordinaryFinitePushforward _ (ProjectiveLine S ↘ S)).map
      (integrationLineTransition l E n (ProjectiveLine S)
        (by simpa using hS.map (ProjectiveLine S ↘ S).appTop.hom) r s hrs hr hs).hom)
    (kummerTraceOrdinaryDatum l E n S hS r hr).decomposition
    (kummerTraceOrdinaryDatum l E n S hS s hs).decomposition ∧
  ∃ (br : (line l E n r hr S ⊞ unit (Scheme.finiteTateCoefficient l E n) S) ≅
      (lowerStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
        (ProjectiveLine S ↘ S)).rightDerivedFunctor.obj (line l E n r hr (ProjectiveLine S)))
    (bs : (line l E n s hs S ⊞ unit (Scheme.finiteTateCoefficient l E n) S) ≅
      (lowerStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
        (ProjectiveLine S ↘ S)).rightDerivedFunctor.obj (line l E n s hs (ProjectiveLine S))),
    br.hom = projectiveB l E n S hS (infinityCartier S) r hr ∧
    bs.hom = projectiveB l E n S hS (infinityCartier S) s hs ∧
    IntegrationDecompositionSquare
      ((comparison (Scheme.finiteTateCoefficient l E n) S).map
        (integrationLineTransition l E n S hS r s hrs hr hs).hom)
      ((lowerStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
        (ProjectiveLine S ↘ S)).rightDerivedFunctor.map
          ((comparison (Scheme.finiteTateCoefficient l E n) (ProjectiveLine S)).map
            (integrationLineTransition l E n (ProjectiveLine S)
              (by simpa using hS.map (ProjectiveLine S ↘ S).appTop.hom)
              r s hrs hr hs).hom)) br bs := by sorry

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
