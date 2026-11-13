/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.SingleComplexInheritedTensorCondition
import WeilConjectures.AlgebraicGeometry.SingleComplexQcqsInduction
import WeilConjectures.AlgebraicGeometry.DerivedTensorQCohClosure
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorQCoh
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel

/-! # Single-complex criterion for derived direct-image base change

## References

* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
* [Stacks Project, Tag 0DJA](https://stacks.math.columbia.edu/tag/0DJA)
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
set_option autoImplicit false
namespace AlgebraicGeometry

private theorem complex_qcoh (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hG : ∀ i : ℤ, (G.X i).IsQuasicoherent) :
    schemeDerivedQCohProperty X (DerivedCategory.Q.obj G) := by
  intro n
  let S := G.sc n
  have : S.X₁.IsQuasicoherent := hG _
  have : S.X₂.IsQuasicoherent := hG _
  have : S.X₃.IsQuasicoherent := hG _
  have : (kernel S.g).IsQuasicoherent := Scheme.Modules.isQuasicoherent_kernel S.g
  have : (cokernel (kernel.lift S.g S.f S.zero)).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_cokernel _
  let e : S.homology ≅ cokernel (kernel.lift S.g S.f S.zero) :=
    S.leftHomologyIso.symm ≪≫ S.leftHomologyIsoCokernelLift
  exact (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
    (((DerivedCategory.homologyFunctorFactors _ n).app G) ≪≫ e).symm inferInstance

/-- The single-complex base-change criterion, with G an actual complex of
quasi-coherent modules (no boundedness is needed) and its ordinary termwise tensor pullback:
under the stalk condition, the canonical base-change map for `E ⊗ Q(G)`, followed by the
canonical tensor comparison and the left-derived counit at `G`, is an isomorphism. -/
theorem singleComplexBaseChangeCriterion
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) [QuasiCompact f] [QuasiSeparated f]
    (E : schemeDerivedCategory X) (hE : schemeDerivedQCohProperty X E)
    (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hG_qcoh : ∀ i : ℤ, (G.X i).IsQuasicoherent)
    (h_stalk : SingleComplexBaseChange.StalkCondition f f' g g' sq
      (DerivedCategory.Q.obj G)
      (DerivedCategory.Q.obj
        (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj G))
      (cast (by rfl) ((SingleComplexBaseChange.counit g').app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj G))))
    (τ : ∀ A B : schemeDerivedCategory X,
      (derivedPullback g').obj (A ⊗ B) ⟶
        (derivedPullback g').obj A ⊗ (derivedPullback g').obj B)
    (hτ : IsCanonicalPullbackTensorComparison g' τ) :
    IsIso (schemeDerivedBaseChangeMap f f' g g' sq.w (E ⊗ DerivedCategory.Q.obj G) ≫
      (schemeDerivedDirectImage f').map
        (τ E (DerivedCategory.Q.obj G) ≫
          (derivedPullback g').obj E ◁
            (cast (by rfl) ((SingleComplexBaseChange.counit g').app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj G)) :
              (derivedPullback g').obj (DerivedCategory.Q.obj G) ⟶
                DerivedCategory.Q.obj
                  (((Scheme.Modules.tensorPullback g').mapHomologicalComplex
                    (.up ℤ)).obj G)))) := by
  classical
  have hG : schemeDerivedQCohProperty X (DerivedCategory.Q.obj G) :=
    complex_qcoh X G hG_qcoh
  let G' := ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj G
  have hG' : schemeDerivedQCohProperty X' (DerivedCategory.Q.obj G') := by
    apply complex_qcoh X' G'
    intro i
    have : (G.X i).IsQuasicoherent := hG_qcoh i
    let e : Scheme.Modules.tensorPullback g' ≅ Scheme.Modules.pullback g' :=
      Adjunction.leftAdjointUniq (Scheme.Modules.nonempty_tensorPullbackAdjunction g').some
        (Scheme.Modules.pullbackPushforwardAdjunction g')
    exact (SheafOfModules.isQuasicoherent (moduleRings X'.toRingedSpace)).prop_of_iso
      (e.app (G.X i)).symm (Scheme.Modules.isQuasicoherent_pullback g' (G.X i))
  obtain ⟨m, hm, hinherit⟩ := singleComplexInheritedTensorCondition f f' g g' sq
    ⟨DerivedCategory.Q.obj G, hG⟩ ⟨DerivedCategory.Q.obj G', hG'⟩
    ((SingleComplexBaseChange.counit g').app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj G)) h_stalk
  have inherited := hinherit ⟨E, hE⟩
  have hcomparison : (m.μIso E (DerivedCategory.Q.obj G)).inv =
      τ E (DerivedCategory.Q.obj G) :=
    congrFun (congrFun (hm.unique hτ) E) (DerivedCategory.Q.obj G)
  rw [hcomparison] at inherited
  exact singleComplexBaseChangeQcqsInduction f f' g g' sq _
    (canonical_derivedTensor_preserve_QCoh X E _ hE hG) _
    (canonical_derivedTensor_preserve_QCoh X' _ _
      ((derivedPullback_tensor_preserve_QCoh g').1 E hE) hG') _ inherited

end AlgebraicGeometry
