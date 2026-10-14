/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.PicardSingleMapIso
public import Sheaf.AlgebraicGeometry.RelativeMVMaps
public import Sheaf.AlgebraicGeometry.SingleComplexOpenRestrictionData

/-! # Coefficient comparison for top restriction -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The coefficient part of top restriction commutes with the pinned single maps.
Source: Stacks Project, Tags 08HY, 0D5S and 08DW.
(blueprint: lem-pc-top-restriction-coefficient-coherence-y3)

Proof: Write q_f for the pinned single map. The tensor composition comparison
δ(h,f) identifies tensor pullback of h ≫ f with successive tensor pullbacks.
The map b below is δ(k,r) inverse, equality transport, δ(r',j), and pullback
of the adjoint-uniqueness comparison ρ from tensor pullback along j to
restriction. Thus d.hom is q_k followed by the single embedding of b. Apply
picardTermwiseSingleMap_composition to k,r and to r',j. Their underived
composition factors are exactly those of b; cancel their inverse factors.
Naturality of the single comparison moves ρ to the final position. The
comparison a from open derived pullback to the restricted single is q_j
followed by the single embedding of ρ: expand singleComplexOpenPullbackIso
and use the defining factorization of leftDerivedUnique, then the
mapDerivedCategorySingleFunctor equation. Substituting this expression
for a gives the claimed identity. Equality transports agree by proof
irrelevance. No map along r or r' is inverted, so arbitrary modules,
zero modules and empty schemes are allowed. -/
theorem topRestriction_coefficient_coherence
    {Y P P' : Scheme.{u}} (M : Y.Modules)
    (k : P' ≅ P) (r : P ⟶ Y) (r' : P' ⟶ (⊤ : Y.Opens).toScheme)
    (h : k.hom ≫ r = r' ≫ (⊤ : Y.Opens).ι) :
    letI := fun Z : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))
    let j := (⊤ : Y.Opens).ι
    let N := M.restrict j
    let K := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M
    let ρ : Scheme.Modules.tensorPullback j ≅ Scheme.Modules.restrictFunctor j :=
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction j)).leftAdjointUniq
        (Scheme.Modules.pullbackPushforwardAdjunction j) ≪≫
          (Scheme.Modules.restrictFunctorIsoPullback j).symm
    let b : @Iso (SheafOfModules.{u} (moduleRings P'.toRingedSpace))
        inferInstance ((Scheme.Modules.tensorPullback k.hom).obj
          (Scheme.Modules.tensorPullbackObj r M)) (Scheme.Modules.tensorPullbackObj r' N) :=
        (Scheme.Modules.tensorPullbackCompositionIso k.hom r
        (k.hom ≫ r) rfl).symm.app M ≪≫
      (eqToIso (congrArg Scheme.Modules.tensorPullback h)).app M ≪≫
      (Scheme.Modules.tensorPullbackCompositionIso r' j (r' ≫ j) rfl).app M ≪≫
      (Scheme.Modules.tensorPullback r').mapIso (ρ.app M)
    letI : IsIso (Scheme.picardTermwiseSingleMap k.hom
        (Scheme.Modules.tensorPullbackObj r M)) :=
      picardTermwiseSingleMap_isIso_of_iso k _
    let d := asIso (Scheme.picardTermwiseSingleMap k.hom
        (Scheme.Modules.tensorPullbackObj r M)) ≪≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings P'.toRingedSpace)) 0).mapIso b
    let a := (singleComplexOpenPullbackIso Y ⊤).app K ≪≫
      ((schemeOpenRestriction Y ⊤).mapDerivedCategorySingleFunctor 0).app M ≪≫
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings
        (⊤ : Y.Opens).toScheme.toRingedSpace)) 0).mapIso
        ((Scheme.Modules.overFunctorEquiv ⊤).app M)
    ((relativeMVComp r' j).hom.app K ≫
        eqToHom (congrArg (fun s ↦ (derivedPullback s).obj K) h.symm) ≫
        (relativeMVComp k.hom r).inv.app K ≫
        (derivedPullback k.hom).map (Scheme.picardTermwiseSingleMap r M)) ≫ d.hom =
      (derivedPullback r').map a.hom ≫ Scheme.picardTermwiseSingleMap r' N := by sorry

end AlgebraicGeometry
