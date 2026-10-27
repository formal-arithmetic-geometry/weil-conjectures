/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T5
-/
module

public import Sheaf.Paper.CompleteReductionSectionsModel
public import WeilConjectures.CategoryTheory.Triangulated.MilnorSequence
import Sheaf.Paper.ReductionSectionsRoosTriangle
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-! # Milnor exact sequence on a resolved tensor-reduction tower

Source: Stacks Project, Cohomology on Sites, Tag 0D6K; More on Algebra,
Tags 07KY and 08U5 (blueprint: lem-sfb-reduction-sections-milnor).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CompleteReductionSections

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (U : Scheme.{u})

attribute [local instance] roosTowerEnoughInjectives roosLimitAdditive

/-- The Milnor sequence after identifying the limit with any specified object L.
No completeness or cohomological upper-bound hypothesis is imposed.

Source: Stacks Project, Tag 0D6K, and More on Algebra, Tags 07KY and 08U5
(blueprint: lem-sfb-reduction-sections-milnor).

Proof: evaluation of a K-injective strict tower is K-injective. Hence termwise
sections of I compute the derived sections of its levels. The quasi-isomorphisms
j_n, and the K-flat scalar-extension computation for P, identify these levels
with RΓ of integralLevel K n. Naturality of the scalar comparison retains the
actual quotient transitions. The strict abelian-group Roos fibre is a derived
inverse limit: countable products of abelian groups are exact, so localization
identifies its cone triangle with the triangle on derived products. Transport
its first object along z. Apply milnor_shortExact to this specified triangle.
Its end terms are the actual right-derived inverse limit in degree one of
H^(q-1) and the inverse limit of H^q. Transport along the natural level
identifications to obtain the displayed short exact sequence. Neither the
choice of z nor this argument requires a surjectivity hypothesis on transitions.
For a zero complex both end terms and the middle term are zero; all degrees q
are integers and positive quotient exponents are indexed by n+1. -/
theorem reduction_sections_milnor
    (K : DerivedCategory (AdicCompletion.Modules l E U))
    (P : CochainComplex (AdicCompletion.Modules l E U) ℤ)
    (hP : (HomologicalComplex.quasiIso (AdicCompletion.Modules l E U) (.up ℤ)).kFlat P)
    (e : DerivedCategory.Q.obj P ≅ K)
    (I : CochainComplex (ℕᵒᵖ ⥤ AdicCompletion.Modules l E U) ℤ)
    (hI : I.IsKInjective)
    (j : Functor.ofOpSequence
      (X := fun n : ℕ ↦ (AdicCompletion.level l E U n).obj P)
      (AdicCompletion.levelStep l E U P) ⟶ I.asFunctor)
    (hj : ∀ n : ℕ, QuasiIso (j.app (op n)))
    (L : DerivedCategory Ab.{u + 1})
    (z : L ≅ DerivedCategory.Q.obj (roosF.obj (sectionTower l E U I))) (q : ℤ) :
    ∃ (a : ((lim : (ℕᵒᵖ ⥤ Ab.{u + 1}) ⥤ Ab.{u + 1}).rightDerived 1).obj
          (AdicCompletion.derivedTower l E U K ⋙ rgamma l E U ⋙
            DerivedCategory.homologyFunctor Ab.{u + 1} (q - 1)) ⟶
          (DerivedCategory.homologyFunctor Ab.{u + 1} q).obj L)
      (b : (DerivedCategory.homologyFunctor Ab.{u + 1} q).obj L ⟶
        limit (AdicCompletion.derivedTower l E U K ⋙ rgamma l E U ⋙
          DerivedCategory.homologyFunctor Ab.{u + 1} q))
      (hz : a ≫ b = 0),
      (ShortComplex.mk a b hz).ShortExact := by
  let T := AdicCompletion.derivedTower l E U K ⋙ rgamma l E U
  obtain ⟨p, δ, hT⟩ := reduction_sections_roos_triangle l E U K P hP e I hI j hj
  have hL : IsDerivedLimitTriangle
      (fun n : ℕ ↦ T.map (homOfLE (Nat.le_succ n)).op) L
      (z.hom ≫ p) (δ ≫ (shiftFunctor _ (1 : ℤ)).map z.inv) := by
    apply CategoryTheory.Pretriangulated.isomorphic_distinguished _ hT _
    refine CategoryTheory.Pretriangulated.Triangle.isoMk _ _ z
      (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
    · simp
    · simp [T, AdicCompletion.derivedTower]
    · simp [Category.assoc, ← Functor.map_comp]
  obtain ⟨a, b, hab, _⟩ := milnor_shortExact.{u + 1} q
  obtain ⟨⟨hz, hseq⟩, _⟩ := hab T L (z.hom ≫ p)
    (δ ≫ (shiftFunctor _ (1 : ℤ)).map z.inv) hL
  exact ⟨_, _, hz, hseq⟩

end AlgebraicGeometry.ProEtale.CompleteReductionSections
