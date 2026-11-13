/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomologyEvaluation
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.AlgebraicGeometry.SelfExtPushforwardHomology
import WeilConjectures.AlgebraicGeometry.SelfTorPushforwardHomology
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardFullyFaithful
import WeilConjectures.AlgebraicGeometry.SelfExtTorResolutionLocal

/-! # A common complex model for self Ext and self Tor

## References

* [Stacks Project, Tag 08DH](https://stacks.math.columbia.edu/tag/08DH)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
* [Stacks Project, Tag 068G](https://stacks.math.columbia.edu/tag/068G)
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry

/-- Self Ext and self Tor are computed on the closed subscheme by one complex T and
an injective resolution J of its structure sheaf. On regular affine charts T has
a finite free zero-differential model. This statement supplies no comparison map
from Ext to dual Tor and asserts no invertibility of such a map. -/
theorem exists_selfExt_tor_resolution_model
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (n : ℕ) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
    let G := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (n : ℤ)).obj
        (H.obj (op (S.obj B), S.obj B))
    let Q := (Scheme.Modules.tensorPullback i).obj
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (-(n : ℤ))).obj
          (S.obj B ⊗ S.obj B))
    ∃ (T J : CochainComplex Z.Modules ℤ)
      (_ : ∀ k : ℤ, k ≠ 0 → IsZero (J.homology k))
      (_ : J.homology 0 ≅ SheafOfModules.unit Z.ringCatSheaf)
      (_ : (Scheme.Modules.tensorPullback i).obj G ≅
        (homComplex (R := Z.sheaf) T J).homology (n : ℤ))
      (_ : Q ≅ T.homology (-(n : ℤ))),
      ∀ (V : Z.Opens) (U : Y.affineOpens)
        (_hU : ∃ (m : ℕ) (f : Fin m → Γ(Y, U.1)),
          Ideal.span (Set.range f) = i.ker.ideal U ∧
            RingTheory.Sequence.IsKoszulRegular f),
        let W := V.ι ⁻¹ᵁ (i ⁻¹ᵁ U.1)
        let Fc := moduleOpenOverComplexFunctor Z V W
        CochainComplex.IsKInjective (Fc.obj J) ∧
          HasFiniteFreeZeroModel (V.toScheme.ringCatSheaf.over W) (Fc.obj T) := by
  classical
  dsimp
  let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction i
  have hAdd : (Scheme.Modules.tensorPullback i).Additive := adj.left_adjoint_additive
  obtain ⟨P, a, hP, hflat, ha, _⟩ := CochainComplex.exists_isKFlatResolution
    (R := Y.sheaf) ((HomologicalComplex.single Y.Modules (.up ℤ) 0).obj B)
  obtain ⟨_, _, I, η, hI⟩ :=
    SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutions
      (Opens.grothendieckTopology Z) Z.sheaf
  let O := (HomologicalComplex.single Z.Modules (.up ℤ) 0).obj
    (SheafOfModules.unit Z.ringCatSheaf)
  let J := I.obj O
  let b := η.app O
  obtain ⟨hb, hKI, _⟩ := hI O
  have : QuasiIso b := hb
  have hJ : ∀ k : ℤ, k ≠ 0 → IsZero (J.homology k) := by
    intro k hk
    exact (HomologicalComplex.isZero_single_obj_homology (.up ℤ) 0
      (SheafOfModules.unit Z.ringCatSheaf) k hk).of_iso
        (isoOfQuasiIsoAt b k).symm
  let e0 : J.homology 0 ≅ SheafOfModules.unit Z.ringCatSheaf :=
    (isoOfQuasiIsoAt b 0).symm ≪≫
      HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 _
  let T := ((Scheme.Modules.tensorPullback i).mapHomologicalComplex (.up ℤ)).obj P
  obtain ⟨g⟩ := nonempty_selfExt_pushforward_homology i P J a b ⟨ha, hP⟩ hb hKI (n : ℤ)
  obtain ⟨q⟩ := nonempty_selfTor_pushforward_homology i P a ⟨ha, hP⟩ (-(n : ℤ))
  let e : Scheme.Modules.tensorPullback i ⊣ Scheme.Modules.pushforward i :=
    Classical.choice (Scheme.Modules.nonempty_tensorPullbackAdjunction i)
  have hc : ∀ N : Z.Modules, IsIso (e.counit.app N) :=
    (closedImmersion_pushforward_fullyFaithful i).1
  let eG := (Scheme.Modules.tensorPullback i).mapIso g ≪≫
    asIso (e.counit.app ((homComplex (R := Z.sheaf) T J).homology (n : ℤ)))
  let eQ := (Scheme.Modules.tensorPullback i).mapIso q ≪≫
    asIso (e.counit.app (T.homology (-(n : ℤ))))
  exact ⟨T, J, hJ, e0, eG, eQ,
    selfExt_tor_resolution_local i P J a b ⟨ha, hP⟩ hflat hb hKI⟩

end AlgebraicGeometry
