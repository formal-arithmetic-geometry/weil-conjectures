/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.AlgebraDiagramPullbackData
import Sheaf.CategoryTheory.Sites.GeometricInverseImageExact
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso
import Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction

/-! # Exactness for algebra diagram pullback

Source: Stacks 03D2 and 03CY (blueprint: lem-pur-algebra-diagram-exactness).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance 100000] CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize

universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.CochainPullback
namespace CategoryTheory.AlgebraDiagramPullback
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {K : GrothendieckTopology C} {L : GrothendieckTopology D}
  {R : Sheaf K CommRingCat.{u}} {S : Sheaf L CommRingCat.{u}}

private def unliftSetSheafIso
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} :
    sheafCompose J uliftFunctor.{u, u} ≅ 𝟭 (Sheaf J (Type u)) :=
  NatIso.ofComponents (fun T ↦
    { hom := ⟨{ app := fun _ ↦ ↾ULift.down }⟩
      inv := ⟨{ app := fun _ ↦ ↾ULift.up }⟩ })
    (by intro T T' f; rfl)

-- The same conjugation by `ULift.down` is used in `LocalizationInverseImageCoherence`.
private noncomputable def inverseImageUniverses
    {C : Type u} {D : Type u} [Category.{u} C] [Category.{u} D]
    [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (a : SheafOfModules.AlgebraicInverseImage L R S) :
    SheafOfModules.AlgebraicInverseImageOfUniverses.{u, u, u, u, u, u} L R S := by
  let eJ := unliftSetSheafIso (J := J)
  let eK := unliftSetSheafIso (J := K)
  let rR := (sheafCompose J (forget CommRingCat.{u})).obj R
  let rS := (sheafCompose K (forget CommRingCat.{u})).obj S
  let mR := SheafOfModules.toSheaf.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
      sheafCompose J (forget AddCommGrpCat.{u})
  let mS := SheafOfModules.toSheaf.{u}
    ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙
      sheafCompose K (forget AddCommGrpCat.{u})
  refine
    { ringUnderlying := L.mapIso (eJ.app rR) ≪≫ a.ringUnderlying ≪≫ (eK.app rS).symm
      modules := a.modules
      moduleUnderlying :=
        Functor.isoWhiskerLeft a.modules (Functor.isoWhiskerLeft mS eK) ≪≫
          a.moduleUnderlying ≪≫
            Functor.isoWhiskerRight (Functor.isoWhiskerLeft mR eJ.symm) L
      ringAdd := ?_
      ringMul := ?_
      ringZero := ?_
      ringOne := ?_
      moduleAdd := ?_
      moduleZero := ?_
      moduleSMul := ?_ }
  · intro T x y z h W q
    simpa [eJ, eK, unliftSetSheafIso, Functor.map_comp] using
      a.ringAdd T (x ≫ eJ.hom.app rR) (y ≫ eJ.hom.app rR)
        (z ≫ eJ.hom.app rR) h W q
  · intro T x y z h W q
    simpa [eJ, eK, unliftSetSheafIso, Functor.map_comp] using
      a.ringMul T (x ≫ eJ.hom.app rR) (y ≫ eJ.hom.app rR)
        (z ≫ eJ.hom.app rR) h W q
  · intro T x h W q
    simpa [eJ, eK, unliftSetSheafIso, Functor.map_comp] using
      a.ringZero T (x ≫ eJ.hom.app rR) h W q
  · intro T x h W q
    simpa [eJ, eK, unliftSetSheafIso, Functor.map_comp] using
      a.ringOne T (x ≫ eJ.hom.app rR) h W q
  · intro M T x y z h W q
    have h' := a.moduleAdd M T (x ≫ eJ.hom.app (mR.obj M))
      (y ≫ eJ.hom.app (mR.obj M)) (z ≫ eJ.hom.app (mR.obj M)) h W q
    simp only [Functor.map_comp] at h'
    convert h' using 1
    all_goals rfl
  · intro M T x h W q
    have h' := a.moduleZero M T (x ≫ eJ.hom.app (mR.obj M)) h W q
    simp only [Functor.map_comp] at h'
    convert h' using 1
    all_goals rfl
  · intro M T r x z h W q
    have h' := a.moduleSMul M T (r ≫ eJ.hom.app rR) (x ≫ eJ.hom.app (mR.obj M))
      (z ≫ eJ.hom.app (mR.obj M)) h W q
    simp only [Functor.map_comp] at h'
    convert h' using 1
    all_goals rfl


/-- Restriction of scalars is exact, by its two adjoints. Source: Stacks 03CY
(blueprint: lem-pur-algebra-diagram-exactness). -/
theorem restriction_exact {B : Sheaf K CommRingCat.{u}} (a : R ⟶ B) :
    ExactRestriction a := by
  obtain ⟨hl, hc, _⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction a
  exact { limits := hl, colimits := hc }

/-- An inverse image with invertible structural coefficients is exact.
Source: Stacks 03D2 (blueprint: lem-pur-algebra-diagram-exactness). -/
theorem pullback_exact (f : RingedPullback.{u, u, u, u, u} R S)
    [IsIso f.coefficient] : ExactPullback f := by
  let geo : GeometricMorphism (Sheaf L (Type u)) (Sheaf K (Type u)) :=
    ⟨f.uInv, f.uPush, f.adj, f.finiteLimits⟩
  let lifted := inverseImageUniverses.{u} f.I
  have hi := ((GeometricMorphism.geometric_inverse_image_exact K L geo).2.2 R).2 f.RI lifted
  have : PreservesFiniteLimits f.I.modules := (exactFunctor_iff _).mp hi.1 |>.1
  have : PreservesFiniteColimits f.I.modules := (exactFunctor_iff _).mp hi.1 |>.2
  obtain ⟨t, _, _, ht⟩ := SheafOfModules.exists_scalarExtensionRingIso.{u, u, u, u}
    (asIso f.coefficient)
  let res := restrictionFunctor.{u, u, u, u} (inv f.coefficient)
  let e : f.L ≅ f.I.modules ⋙ res := NatIso.ofComponents
    (fun M ↦ eqToIso (f.hobj M) ≪≫ t (f.I.modules.obj M)) (by
      intro M N a
      change f.L.map a ≫ (eqToHom (f.hobj N) ≫ (t (f.I.modules.obj N)).hom) =
        (eqToHom (f.hobj M) ≫ (t (f.I.modules.obj M)).hom) ≫ res.map (f.I.modules.map a)
      rw [f.hmap]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      exact congrArg (fun z ↦ eqToHom (f.hobj M) ≫ z)
        (ht (f.I.modules.obj M) (f.I.modules.obj N) (f.I.modules.map a)))
  let : ExactRestriction (inv f.coefficient) := restriction_exact _
  have : PreservesFiniteLimits (f.I.modules ⋙ res) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (f.I.modules ⋙ res) := comp_preservesFiniteColimits _ _
  exact { limits := preservesFiniteLimits_of_natIso e.symm
          colimits := preservesFiniteColimits_of_natIso e.symm }

end CategoryTheory.AlgebraDiagramPullback
