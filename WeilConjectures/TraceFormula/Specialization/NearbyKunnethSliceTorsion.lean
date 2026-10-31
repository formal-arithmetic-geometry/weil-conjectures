/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethSliceTorsionSquares
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethSliceTorsionSpecial
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethSliceTorsionExchange
public import WeilConjectures.SixFunctors.NearbyCycles.GaloisInvariantsCoinvariantTensor

/-!

# The generic-slicing step of Gabber's Künneth formula modulo `ϖ`

Let `P` be the product over `S = Spec k'⟦t⟧` of models `M`, `N` of finite type, `b` a coordinate
of `M` and `D` a generic slice trait `S'` of `𝔸¹_S`. The generic-slicing step modulo `ϖ` (blueprint
`sk-prop-tf-nearby-external-kunneth`, identification (2) and projection formula (3)) goes in three
steps:

1. from the geometric slice over `Spec K⟦t⟧` to the configuration `M_{S'} ⟵ P_{S'} ⟶ N` of the
   slices over `S'`: the changes of trait have invertible exchanges (Th. finitude 3.7 with
   `𝔽_E`-coefficients) and the pullback along the special fibre of the change of trait reflects
   isomorphisms (proved below);
2. descent along the Galois layer of `S' ⟶ S`
   (`NearbyCyclesModel.isIso_map_kunnethMap_of_galoisSlice`, applied to the models of
   `WeilConjectures.TraceFormula.Specialization.NearbyKunnethSliceTorsionGalois` and
   `WeilConjectures.TraceFormula.Specialization.NearbyKunnethSliceTorsionProduct`);
3. transport to the special fibre map `τ_s ≫ σ_s` of the slice of `P`.

## Unfinished

Steps 2 and 3 are not yet assembled: the instantiation of
`NearbyCyclesModel.isIso_map_kunnethMap_of_galoisSlice` at the concrete models elaborates, but its
hypotheses, produced by lemmas stated for a general coefficient ring, differ from its statement by
instance paths (`Precoherent Profinite` proofs, `Field.toCommRing` against `Field.toDivisionRing`),
and the kernel check of the closing `exact_by_kernel` does not finish in reasonable time. The main
theorem is therefore `sorry`ed.

-/

@[expose] public section


universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) {k' : Type u}
  [Field k'] [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  {X Y Z : Scheme.{u}} {X' Y' Z' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {N : NearbyCyclesModel Y Y'.left} {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X}
  {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y} {f₂' : Z'.left ⟶ Y'.left} {φ₁ : P.Hom M f₁ f₁'}
  {φ₂ : P.Hom N f₂ f₂'} {qM : M.total ⟶ trait k'}
  {gM : M.generic ⟶ Spec (.of (traitGenericField k'))} {qN : N.total ⟶ trait k'}
  {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}

set_option hygiene false in
/-- The condensed field `𝔽̲_E`. -/
local notation "𝔽" => Profinite.continuousMapRingObj (PadicAlgCl.integersResidueField ℓ E.1)

set_option maxHeartbeats 4000000 in
-- the Künneth maps of the two product configurations are large terms
omit [Fact (ringChar k').Prime] in
/-- **From the geometric slice to the slice over a generic slice trait** (SGA 4½,
[Th. finitude], 3.7; `𝔽_E`-coefficients): if the Künneth map of the geometric slice of the product
along `b` is invertible, so is the Künneth map of `M_{S'} ⟵ P_{S'} ⟶ N`, at the restrictions of
`A`, `B` to the geometric generic fibres. -/
private theorem isIso_kunnethMap_coordinateSliceTrait_of_isIso_sliceFst
    (hM : M.IsTraitModelOver qM gM)
    (hN : N.IsTraitModelOver qN gN) (hpb : IsPullback φ₁.total φ₂.total qM qN)
    (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM))
    (hgen : φ₂.generic ≫ gN = φ₁.generic ≫ gM) {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
    (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = qM) (D : GenericSliceTrait k')
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj 𝔽 X))}
    (hA : DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl.integersResidueField ℓ E.1))) M.generic
      ((finiteCoefficientDerivedEquivalence M.generic
        (PadicAlgCl.integersResidueField ℓ E.1)).functor.obj (L((M.ε)^*⟦𝔽⟧).obj A)))
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj 𝔽 Y))}
    (hB : DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl.integersResidueField ℓ E.1))) N.generic
      ((finiteCoefficientDerivedEquivalence N.generic
        (PadicAlgCl.integersResidueField ℓ E.1)).functor.obj (L((N.ε)^*⟦𝔽⟧).obj B)))
    (h : IsIso (kunnethMap 𝔽 (sliceFst hM hP hb) (sliceSnd hN hpb hP hgen hb) A B)) :
    IsIso (kunnethMap 𝔽 (coordinateSliceTraitMap φ₁ b D)
      (coordinateSliceTraitSnd hP hb D (φ₂ := φ₂))
      ((L((coordinateSliceTraitGeneric hM b hb D)^*⟦𝔽⟧)).obj ((L((M.ε)^*⟦𝔽⟧)).obj A))
      ((L((N.ε)^*⟦𝔽⟧)).obj B)) := by
  have hAS : DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl.integersResidueField ℓ E.1)))
      (pullback (pullback.snd b D.toAffineLine) (Spec.map (CommRingCat.ofHom D.a)))
      ((finiteCoefficientDerivedEquivalence
        (pullback (pullback.snd b D.toAffineLine) (Spec.map (CommRingCat.ofHom D.a)))
        (PadicAlgCl.integersResidueField ℓ E.1)).functor.obj
          ((L((coordinateSliceTraitGeneric hM b hb D)^*⟦𝔽⟧)).obj ((L((M.ε)^*⟦𝔽⟧)).obj A))) :=
    ProEtale.plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj
      _ (coordinateSliceTraitGeneric hM b hb D) hA
  have hτM : IsIso (((coordinateSliceTraitChangeHom hM b hb D).pullbackExchange 𝔽).app
      ((L((coordinateSliceTraitGeneric hM b hb D)^*⟦𝔽⟧)).obj ((L((M.ε)^*⟦𝔽⟧)).obj A))) :=
    isIso_pullbackExchange_coordinateSliceTraitChangeHom_residueField hM b hb D E hAS
  have hBP : DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl.integersResidueField ℓ E.1)))
      (pullback (pullback.snd (φ₁.total ≫ b) D.toAffineLine) (Spec.map (CommRingCat.ofHom D.a)))
      ((finiteCoefficientDerivedEquivalence
        (pullback (pullback.snd (φ₁.total ≫ b) D.toAffineLine) (Spec.map (CommRingCat.ofHom D.a)))
        (PadicAlgCl.integersResidueField ℓ E.1)).functor.obj
          ((L((coordinateSliceTraitMapGeneric φ₁ b D)^*⟦𝔽⟧)).obj
            ((L((coordinateSliceTraitGeneric hM b hb D)^*⟦𝔽⟧)).obj ((L((M.ε)^*⟦𝔽⟧)).obj A)) ⊗
          (L((coordinateSliceTraitGeneric hP (φ₁.total ≫ b) (comp_coordinate_fst hb) D ≫
            φ₂.generic)^*⟦𝔽⟧)).obj ((L((N.ε)^*⟦𝔽⟧)).obj B))) :=
    ProEtale.plusEtaleOrigin_finiteCoefficientDerivedEquivalence_tensorObj_leftDerivedUpperStar
      _ (Field.toIsField _) _ _ hAS hB
  have hτP : IsIso (((coordinateSliceTraitChangeHom hP (φ₁.total ≫ b) (comp_coordinate_fst hb)
      D).pullbackExchange 𝔽).app
        ((L((coordinateSliceTraitMapGeneric φ₁ b D)^*⟦𝔽⟧)).obj
            ((L((coordinateSliceTraitGeneric hM b hb D)^*⟦𝔽⟧)).obj ((L((M.ε)^*⟦𝔽⟧)).obj A)) ⊗
          (L((coordinateSliceTraitGeneric hP (φ₁.total ≫ b) (comp_coordinate_fst hb) D ≫
            φ₂.generic)^*⟦𝔽⟧)).obj ((L((N.ε)^*⟦𝔽⟧)).obj B))) :=
    isIso_pullbackExchange_coordinateSliceTraitChangeHom_residueField hP (φ₁.total ≫ b)
      (comp_coordinate_fst hb) D E hBP
  have hτN : IsIso ((((baseChangeHom hN qN (Category.comp_id qN) (traitMap k' (traitSliceField k'))
      (Category.comp_id _)).toGeneric).pullbackExchange 𝔽).app ((L((N.ε)^*⟦𝔽⟧)).obj B)) :=
    isIso_pullbackExchange_toGeneric_baseChangeHom_traitMap_residueField hN E hB
  -- the square of Künneth maps along the changes of trait
  have sq := isIso_map_map_kunnethMap_iff_of_isIso_pullbackExchange 𝔽
    (coordinateSliceTraitMap φ₁ b D) (coordinateSliceTraitSnd hP hb D (φ₂ := φ₂))
    (sliceFst hM hP hb).toGeneric (sliceSnd hN hpb hP hgen hb).toGeneric
    (coordinateSliceTraitChangeHom hM b hb D)
    ((baseChangeHom hN qN (Category.comp_id qN) (traitMap k' (traitSliceField k'))
      (Category.comp_id _)).toGeneric)
    (coordinateSliceTraitChangeHom hP (φ₁.total ≫ b) (comp_coordinate_fst hb) D)
    (sliceFst_total_comp_coordinateSliceTraitChangeTotal hM hP hb D)
    (sliceFst_toGeneric_generic_comp_coordinateSliceTraitChangeHom_generic hM hP hb D)
    (sliceSnd_total_comp_baseChangeHom_total hN hpb hP hgen hb D)
    (sliceSnd_toGeneric_generic_comp_baseChangeHom_generic hN hpb hP hgen hb D)
    (sliceFst_generic_comp_coordinateSliceTraitChangeGeneric hM hP hb D)
    (sliceFst_special_comp_coordinateSliceTraitChangeSpecial D)
    (sliceSnd_generic_comp_baseChangeHom_generic hN hpb hP hgen hb D)
    (sliceSnd_special_comp_baseChangeSpecialMap hN hpb hP hb D)
    ((L((coordinateSliceTraitGeneric hM b hb D)^*⟦𝔽⟧)).obj ((L((M.ε)^*⟦𝔽⟧)).obj A))
    ((L((N.ε)^*⟦𝔽⟧)).obj B) hτM hτN hτP (𝟭 _)
  refine isIso_of_isIso_map_coordinateSliceTraitChangeSpecial (φ₁.total ≫ b) D 𝔽 _ ?_
  refine sq.2 ?_
  have h₀ := (isIso_kunnethMap_iff_toGeneric 𝔽 _ _ A B).1 h
  exact isIso_kunnethMap_of_iso 𝔽 _ _
    (((leftDerivedUpperStarCompOfEq 𝔽 (coordinateSliceTraitChangeGeneric_comp hM b hb D)).app
      ((L((M.ε)^*⟦𝔽⟧)).obj A)).symm ≪≫
      ((leftDerivedUpperStarCompOfEq 𝔽
        (p := (baseChangeHom hM b hb (traitSlice (traitSliceCoord k'))
          (traitSlice_over (traitSliceCoord k'))).generic) (q := M.ε) rfl).app A).symm)
    ((leftDerivedUpperStarCompOfEq 𝔽 (p := (baseChangeHom hN qN (Category.comp_id qN)
      (traitMap k' (traitSliceField k')) (Category.comp_id _)).generic) (q := N.ε) rfl).app B).symm
    h₀
/-- **The generic-slicing step modulo `ϖ`** (blueprint `sk-prop-tf-nearby-external-kunneth`,
identification (2) and projection formula (3), coefficients `𝔽_E`): if the Künneth map of the
geometric slice of the product along a coordinate `b` of `M` is invertible, so is the pullback of
`Π_{A,B}` to the special fibre of the slice of `P`. -/
theorem isIso_map_kunnethMap_of_isIso_sliceFst_residueField (hM : M.IsTraitModelOver qM gM)
    (hN : N.IsTraitModelOver qN gN) (hpb : IsPullback φ₁.total φ₂.total qM qN)
    (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM))
    (hgen : φ₂.generic ≫ gN = φ₁.generic ≫ gM) {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
    (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = qM)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj 𝔽 X))}
    (hA : boundedConstructible (condensedRingObj 𝔽 M.generic) (L((M.ε)^*⟦𝔽⟧).obj A))
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj 𝔽 Y))}
    (hB : boundedConstructible (condensedRingObj 𝔽 N.generic) (L((N.ε)^*⟦𝔽⟧).obj B))
    (h : IsIso (kunnethMap 𝔽 (sliceFst hM hP hb) (sliceSnd hN hpb hP hgen hb) A B)) :
    IsIso (L((baseChangeSpecialMap hP (φ₁.total ≫ b) (comp_coordinate_fst hb)
        (traitSlice (traitSliceCoord k')) (traitSlice_over (traitSliceCoord k')))^*⟦𝔽⟧).map
      (kunnethMap 𝔽 φ₁ φ₂ A B)) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
