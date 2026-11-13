/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeMapSectionsDefs
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.FlatBaseChangeMapSectionsLift
import WeilConjectures.AlgebraicGeometry.FlatBaseChangeResolutionIndependence
import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoicesExist
import WeilConjectures.AlgebraicGeometry.FlatBaseChangeResolutionSections

/-! # FlatBaseChangeMapSections

## References

* [Stacks Project, Tag 02N7](https://stacks.math.columbia.edu/tag/02N7)
* [Stacks Project, Tag 01FB](https://stacks.math.columbia.edu/tag/01FB)
* [Stacks Project, Tag 01E4](https://stacks.math.columbia.edu/tag/01E4)
-/

@[expose] public section
universe uBC
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] AlgebraicGeometry.Scheme.Modules.enoughInjectives

set_option maxHeartbeats 600000 in
-- Comparing section maps elaborates the nested resolution and homology transports.
/-- The base-change map constructed from resolutions is independent of the resolutions
and augmented lifts. Its adjoint sends the canonical image of a class on `f⁻¹V` to the
canonical image of its pullback along `g'` restricted to `g'⁻¹(f⁻¹V)`. The local pullback
is written as the recorded cohomology h-map of the restricted unit.
(Stacks, Tags 02N7, 01E4 and 01FB.) -/
theorem flatBaseChangeMap_sections {X S S' : Scheme.{uBC}} (f : X ⟶ S) (g : S' ⟶ S)
    [Flat g] [Flat (pullback.snd g f)] (F : X.Modules) (p : ℕ) :
    ∃ beta : (tensorPullback g).obj (((pushforward f).rightDerived p).obj F) ⟶
        ((pushforward (pullback.fst g f)).rightDerived p).obj
          ((tensorPullback (pullback.snd g f)).obj F),
      (∀ (I : InjectiveResolution F)
        (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
        (t : I.cocomplex ⟶ ((pushforward (pullback.snd g f)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj J.cocomplex),
        I.ι.f 0 ≫ t.f 0 =
          (Classical.choose (exists_tensorPullbackAdjunction (pullback.snd g f))).unit.app F ≫
            (pushforward (pullback.snd g f)).map (J.ι.f 0) →
        flatBaseChangeResolutionBeta f g I J t p = beta) ∧
      (∀ (I : InjectiveResolution F)
        (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F)) (V : S.Opens),
        Nonempty (FlatBaseChangeOpenChoices f g F I J V)) ∧
      (∀ (I : InjectiveResolution F)
        (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F)) (V : S.Opens)
        (D : FlatBaseChangeOpenChoices f g F I J V)
        (xi : (forget₂ _ AddCommGrpCat.{uBC}).obj
          ((RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p).obj
            ((restrictFunctor (f ⁻¹ᵁ V).ι).obj F))),
        Hom.app ((Classical.choose (exists_tensorPullbackAdjunction g)).homEquiv _ _ beta) V
          (D.sourceClass p xi) =
        D.targetClass p
          (moduleCohomologyFMap ((pullback.snd g f).resLE (f ⁻¹ᵁ V)
            ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)) le_rfl) D.psi p xi)) := by
  let I := injectiveResolution F
  let J := injectiveResolution ((tensorPullback (pullback.snd g f)).obj F)
  obtain ⟨t, ht⟩ := flatBaseChangeResolutionLift f g I J
  refine ⟨flatBaseChangeResolutionBeta f g I J t p, ?_, ?_, ?_⟩
  · intro I₁ J₁ t₁ ht₁
    exact flatBaseChangeResolutionBeta_independent f g I₁ J₁ t₁ ht₁ I J t ht p
  · exact flatBaseChangeMap_sections_choices f g F
  · intro I₁ J₁ V D xi
    obtain ⟨t₁, ht₁⟩ := flatBaseChangeResolutionLift f g I₁ J₁
    have h := flatBaseChangeResolutionBeta_sections f g I₁ J₁ t₁ ht₁ p V D xi
    simpa only [flatBaseChangeResolutionBeta_independent f g I₁ J₁ t₁ ht₁ I J t ht p]
      using h

end AlgebraicGeometry.Scheme.Modules
