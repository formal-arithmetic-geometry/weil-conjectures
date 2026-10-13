/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Sheaf.AlgebraicGeometry.FlatBaseChangeMapSectionsDefs
public import Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.AlgebraicGeometry.FlatBaseChangeOpenChoices
import Sheaf.AlgebraicGeometry.LerayDegenerateSections
import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap
import Sheaf.AlgebraicGeometry.ModuleCohomologySourceComparison
import Sheaf.AlgebraicGeometry.OrdinaryHigherImageQuasiCoherent
import Sheaf.AlgebraicGeometry.TensorPullback
import Sheaf.Paper.HigherDirectImagePresheaf
import Sheaf.Paper.ZariskiModuleAbelianCohomologyNatural
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech

/-! # Target Leray comparison normalized against a natural source comparison

Source: Stacks Project, Tags 01XK, 01E4, 03FD and the affine dictionary in 02KH.
(blueprint: new-flat-base-change-target-leray-comparison)
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] enoughInjectives

/-- Choose the natural source module/Ext comparison together with the target affine
Leray equivalence, compatibly with the cohomological pullback. This does not construct
or assume a source tensor comparison, nor assert invertibility of base change.

Source: Stacks Project, Tags 03FD, 01XK, 01E4 and 02KH, first paragraph of the proof.
(blueprint: new-flat-base-change-target-leray-comparison)

Proof: For every module on U = f inverse V, compare module derived sections and abelian
Ext cohomology using the section complex of a module injective resolution. Forgotten
injectives are section-acyclic by 03FD. The free abelian Yoneda object at the top open
and the constant integer sheaf are identified by evaluation at 1. Choose these same
comparisons for all modules. An augmented resolution lift of any module morphism
computes both induced maps, so the resulting family E is natural in the module.
Compose its component at F restricted to U with restrictFunctorIsoPullback to obtain e0.

The affine chart square identifies U times Spec B over Spec A with f prime inverse W.
The pullback composition isomorphisms identify its coefficient module with g prime
pullback F restricted there, and intertwine the adjunction units. The base change f prime
is qcqs and its coefficient module is quasi-coherent. Its higher images are therefore
quasi-coherent by 01XJ. Positive cohomology of these on affine W vanishes, so the
cocycle-normalized Leray edge of 01XK is an isomorphism. Compose the chart identification,
the same module/Ext comparison on this chart, and this Leray edge to obtain b.
Naturality for multiplication by sections makes b B-linear.

For compatibility, lift D.psi to an augmented map of module resolutions. The exact
inverse-image Ext pullback and this lift induce the same map on the common section
complex: D.unit_square and the composite-adjunction unit equations identify their
coefficient maps. Any two augmented lifts are homotopic, so their maps on cohomology
agree. D.source.augmentation and D.target.augmentation fix the identifications with I
and J; their components equations fix the section restrictions term by term. By 01E4
the target Leray edge sends a cocycle to its class in the higher-image sheaf. Restricting
this class from g inverse V to W gives the displayed equality for every source class x.
This is a comparison of maps, with no flatness or bijectivity of the pullback map used.
The same section complexes and augmentations handle p = 0, zero coefficients and empty
opens; no nonempty choice or division by a scalar occurs. -/
theorem exists_flatBaseChange_target_leray_comparison
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent]
    (I : InjectiveResolution F)
    (J : InjectiveResolution
      ((Scheme.Modules.tensorPullback (pullback.snd g f)).obj F))
    (p : ℕ) (V : S.Opens) (W : S'.Opens) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (eVW : W ≤ g ⁻¹ᵁ V)
    (D : Scheme.Modules.FlatBaseChangeOpenChoices f g F I J V) :
    letI : Algebra Γ(S, V) Γ(S', W) := (g.appLE V W eVW).hom.toAlgebra
    let h := f.resLE V (f ⁻¹ᵁ V) le_rfl ≫ V.toSpecΓ
    let N := (Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj F
    let Q := ((Scheme.Modules.pushforward (pullback.fst g f)).rightDerived p).obj
      ((Scheme.Modules.tensorPullback (pullback.snd g f)).obj F)
    ∃ E : ∀ M : (f ⁻¹ᵁ V).toScheme.Modules,
        ((RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p).obj M) ≃+
          H M p,
      (∀ (M M' : (f ⁻¹ᵁ V).toScheme.Modules) (φ : M ⟶ M')
        (x : (RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p).obj M),
        E M' (((RingedSpace.moduleCohomology
          (f ⁻¹ᵁ V).toScheme.toRingedSpace p).map φ).hom x) = H.map φ p (E M x)) ∧
      (∃ e0 : ((RingedSpace.moduleCohomology
            (f ⁻¹ᵁ V).toScheme.toRingedSpace p).obj
            ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F)) ≃+ HOver h N p,
         e0 = (E ((restrictFunctor (f ⁻¹ᵁ V).ι).obj F)).trans
            (H.mapLinearEquiv ((restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app F) p).toAddEquiv ∧
       ∃ b : HOver (baseChangeSnd (S := Γ(S', W)) h)
           (baseChangedModule (S := Γ(S', W)) h N) p ≃ₗ[Γ(S', W)] Γ(Q, W),
         ∀ xi : HOver h N p,
           b (H.baseChangeLinear (S := Γ(S', W)) h N p xi) =
             Q.presheaf.map (homOfLE eVW).op
               (D.targetClass p
                 (moduleCohomologyFMap ((pullback.snd g f).resLE (f ⁻¹ᵁ V)
                   ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)) le_rfl) D.psi p (e0.symm xi)))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
