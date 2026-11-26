/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.SelfTorConormalComparisonPredicate
import WeilConjectures.RingTheory.KoszulAugmentationLiftExists
import WeilConjectures.RingTheory.KoszulConormalCycleRelations
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Self-Tor and the conormal module via the Tate construction

The Tate construction gives a comparison map from the exterior powers of the conormal module
`I/I²` to `Tor_n^A(A/I, A/I)`, computed by a wedge formula on an augmentation lift of each
Koszul complex to a projective resolution.

## Implementation details

`TateComparisonCertificate` records the wedge formula for one chosen augmentation lift; it
does not claim the formula for arbitrary lifts.

## References

* [Stacks, Tag 09PQ]
* [Stacks, Tag 00LS]
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry

/-- A comparison computed by one augmentation lift for each Koszul complex and
projective resolution, together with the wedge formula it satisfies for that chosen lift. -/
def TateComparisonCertificate (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ)
    (c : conormalExteriorModule A I n ⟶
      ((Tor' (ModuleCat.{u} A) n).obj (ModuleCat.of A (A ⧸ I))).obj
        (ModuleCat.of A (A ⧸ I))) : Prop :=
  ∀ (r : ℕ) (g : Fin r → I) (P : ProjectiveResolution (ModuleCat.of A (A ⧸ I))),
    ∃ a : ExteriorAlgebra.koszulComplex A r (fun j ↦ (g j : A)) ⟶ P.complex,
      a.f 0 ≫ P.π.f 0 =
        ModuleCat.ofHom (I.mkQ.comp
          (exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap) ∧
      let K := ExteriorAlgebra.koszulComplex A r (fun j ↦ (g j : A))
      let T := (tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)
      ∀ (v : Fin n → (Fin r →₀ A)) (z : (T.obj K).cycles n),
        (T.obj K).iCycles n z =
          (exteriorPower.ιMulti A n v) ⊗ₜ[A] (1 : A ⧸ I) →
        (P.isoLeftDerivedObj (tensorRight (ModuleCat.of A (A ⧸ I))) n).hom
            (c (exteriorPower.ιMulti (A ⧸ I) n
              (fun j ↦ I.toCotangent (Finsupp.linearCombination A g (v j))))) =
          ((HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.down ℕ) n).map
            (T.map a)) ((T.obj K).homologyπ n z)

/-- The Tate construction supplies a comparison with a wedge formula for a
chosen augmentation lift, for each tuple and projective resolution. -/
theorem tate_selfTor_conormal_map (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) :
    ∃ c : conormalExteriorModule A I n ⟶
      ((Tor' (ModuleCat.{u} A) n).obj (ModuleCat.of A (A ⧸ I))).obj
        (ModuleCat.of A (A ⧸ I)), TateComparisonCertificate A I n c := by
  classical
  let Q := projectiveResolution (ModuleCat.of A (A ⧸ I))
  choose a ha using fun r g ↦ koszul_augmentation_lift_exists A I r g Q
  let φ := koszulConormalCyclePresentation A I n
  let ψ := koszulConormalCycleEvaluation A I n Q a
  have hφ : Function.Surjective φ := koszulConormalCyclePresentation_surjective A I n
  have hker : LinearMap.ker φ ≤ LinearMap.ker ψ :=
    koszulConormalCycleEvaluation_ker A I n Q a ha
  let e := φ.quotKerEquivOfSurjective hφ
  let d : conormalExteriorModule A I n ⟶
      (((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)).obj
        Q.complex).homology n :=
    ModuleCat.ofHom (((LinearMap.ker φ).liftQ ψ hker).comp e.symm.toLinearMap)
  have hd (x : KoszulConormalWedgeCycle A I n →₀ A) : d (φ x) = ψ x := by
    change (LinearMap.ker φ).liftQ ψ hker (e.symm (φ x)) = ψ x
    have he : e.symm (φ x) = (LinearMap.ker φ).mkQ x := by
      apply e.injective
      simp [e]
    rw [he]
    rfl
  let F := tensorRight (ModuleCat.of A (A ⧸ I))
  let T := F.mapHomologicalComplex (.down ℕ)
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.down ℕ) n
  refine ⟨d ≫ (Q.isoLeftDerivedObj F n).inv, ?_⟩
  intro r g P
  let b := ProjectiveResolution.lift (𝟙 (ModuleCat.of A (A ⧸ I))) Q P
  have hb : b.f 0 ≫ P.π.f 0 = Q.π.f 0 := by
    simp [b]
  refine ⟨a r g ≫ b, ?_, ?_⟩
  · change (a r g).f 0 ≫ b.f 0 ≫ P.π.f 0 = _
    rw [hb]
    exact ha r g
  · dsimp only
    intro v z hz
    let s : KoszulConormalWedgeCycle A I n := ⟨r, g, v, z, hz⟩
    have hs := hd (Finsupp.single s 1)
    simp only [φ, ψ, koszulConormalCyclePresentation, koszulConormalCycleEvaluation,
      Finsupp.linearCombination_single, one_smul] at hs
    have hn : (P.isoLeftDerivedObj F n).hom =
        (Q.isoLeftDerivedObj F n).hom ≫ H.map (T.map b) := by
      simpa [H, T] using ProjectiveResolution.isoLeftDerivedObj_hom_naturality
        (𝟙 (ModuleCat.of A (A ⧸ I))) Q P b (by simpa using hb) F n
    have he : (d ≫ (Q.isoLeftDerivedObj F n).inv) ≫ (P.isoLeftDerivedObj F n).hom =
        d ≫ H.map (T.map b) := by
      rw [hn]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    change ((d ≫ (Q.isoLeftDerivedObj F n).inv) ≫ (P.isoLeftDerivedObj F n).hom)
      (exteriorPower.ιMulti (A ⧸ I) n
        (fun j ↦ I.toCotangent (Finsupp.linearCombination A g (v j)))) = _
    rw [he]
    change H.map (T.map b) (d (exteriorPower.ιMulti (A ⧸ I) n
      (fun j ↦ I.toCotangent (Finsupp.linearCombination A g (v j))))) = _
    rw [hs]
    simp only [Functor.map_comp, ModuleCat.comp_apply]
    rfl


end AlgebraicGeometry
