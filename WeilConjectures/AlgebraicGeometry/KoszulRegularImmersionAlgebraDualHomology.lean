/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.AlgebraicGeometry.LocallyRankedExteriorComplex
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.LinearAlgebra.Dimension.Finrank
import WeilConjectures.AlgebraicGeometry.AffineDerivedHomEvaluationCounit
import WeilConjectures.AlgebraicGeometry.KoszulRegularImmersionDerivedHom
import Mathlib.Algebra.Homology.ShortComplex.Homology
import WeilConjectures.AlgebraicGeometry.DerivedRHomAlgebraModule
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import Mathlib.Topology.Sheaves.LocallySurjective
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Cohomology of the algebra-valued Koszul dual

## References

* Stacks Project, Tags 0BQZ, 0AX3 and 0AVW.
-/

@[expose] public section

universe u wY wA

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem closedImmersion_scalar_locallySurjective
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i] :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y)
      (Functor.whiskerRight i.c (forget₂ CommRingCat RingCat)) := by
  apply (TopCat.Presheaf.isLocallySurjective_iff _).mpr
  intro U t y hy
  obtain ⟨V, hV, hyV, hVU⟩ := exists_isAffineOpen_mem_and_subset hy
  obtain ⟨s, hs⟩ := i.app_surjective V hV
    (((directImageAlgebraSpace i).presheaf.map (homOfLE hVU).op) t)
  exact ⟨V, hVU, ⟨s, hs⟩, hyV⟩

private noncomputable def scalarRestriction_fullyFaithful
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R R' : Sheaf J RingCat.{u}} (α : R ⟶ R')
    [Presheaf.IsLocallySurjective J α.hom] :
    (SheafOfModules.restrictScalars.{u} α).FullyFaithful := by
  refine ⟨(fun {M N} f ↦
    ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective α.hom N.isSheaf).symm
      f.val⟩), ?_, ?_⟩
  · intro M N f
    apply SheafOfModules.hom_ext
    exact (PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      α.hom N.isSheaf).apply_symm_apply f.val
  · intro M N f
    apply SheafOfModules.hom_ext
    exact (PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      α.hom N.isSheaf).symm_apply_apply f.val

/-- The scalar cohomology calculation, without an algebra action or a choice of right
adjoint (Stacks, Tag 0BQZ). -/
private theorem koszulRegularImmersion_scalar_homology
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (hregular : ∀ z : Z, ∃ U : Y.affineOpens, i z ∈ U.1 ∧
      ∃ (n : ℕ) (f : Fin n → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f)
    (r : LocallyConstant Z ℕ)
    (hr : ∀ z : Z, r z = Module.finrank (Z.presheaf.stalk z)
      ((RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj
        ((Scheme.Modules.tensorPullback i).obj i.ker.toModules))) (n : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj
        ((derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).obj
          (Opposite.op ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))),
            (DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
                (SheafOfModules.unit Y.ringCatSheaf))) ≅
      (Scheme.Modules.pushforward i).obj
        (Scheme.Modules.locallyRankedExteriorTerm
          (SheafOfModules.homObj (R := Z.sheaf)
            ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)
            (SheafOfModules.unit Z.ringCatSheaf)) r n)) := by
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let Lc := (HomologicalComplex.single A (.up ℤ) 0).obj
    ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))
  let Gc := (HomologicalComplex.single A (.up ℤ) 0).obj
    (SheafOfModules.unit Y.ringCatSheaf)
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let I := CochainComplex.kInjectiveResolutionFunctor.{u} A
  let η := CochainComplex.toKInjectiveResolution.{u} A
  let Ic := I.obj Gc
  have : Ic.IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A Gc
  have : QuasiIso (η.app Gc) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A Gc).2
  let C := CategoryTheory.homComplex (R := Y.sheaf) Lc Ic
  have hc : Nonempty (C.homology n ≅
      (Scheme.Modules.pushforward i).obj
        (Scheme.Modules.locallyRankedExteriorTerm
          (SheafOfModules.homObj (R := Z.sheaf)
            ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)
            (SheafOfModules.unit Z.ringCatSheaf)) r n)) := by
    let := HasDerivedCategory.standard A
    let := HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))
    obtain ⟨e⟩ := koszulRegularImmersion_derivedInternalHom i hregular r hr
    obtain ⟨eR⟩ := derivedInternalHom_obj_iso
      (Opens.grothendieckTopology Y) Y.sheaf
      (DerivedCategory.Q.obj Lc) (DerivedCategory.Q.obj Gc)
      Lc Ic (Iso.refl _) (asIso (DerivedCategory.Q.map (η.app Gc))).symm
    let K := ((Scheme.Modules.pushforward i).mapHomologicalComplex (.up ℤ)).obj
      (Scheme.Modules.locallyRankedExteriorComplex
        (SheafOfModules.homObj (R := Z.sheaf)
          ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)
          (SheafOfModules.unit Z.ringCatSheaf)) r)
    have hf : (K.sc n).f = 0 := by
      dsimp [K, Scheme.Modules.locallyRankedExteriorComplex]
      simp [CochainComplex.of.d]
    have hg : (K.sc n).g = 0 := by
      dsimp [K, Scheme.Modules.locallyRankedExteriorComplex]
      simp [CochainComplex.of.d]
    let z : K.homology n ≅ K.X n :=
      (ShortComplex.HomologyData.ofZeros (K.sc n) hf hg).left.homologyIso
    exact ⟨((DerivedCategory.homologyFunctorFactors A n).app C).symm ≪≫
      (DerivedCategory.homologyFunctor A n).mapIso (eR.symm ≪≫ e) ≪≫
      (DerivedCategory.homologyFunctorFactors A n).app K ≪≫ z⟩
  obtain ⟨eR⟩ := derivedInternalHom_obj_iso
    (Opens.grothendieckTopology Y) Y.sheaf
    (DerivedCategory.Q.obj Lc) (DerivedCategory.Q.obj Gc)
    Lc Ic (Iso.refl _) (asIso (DerivedCategory.Q.map (η.app Gc))).symm
  obtain ⟨ec⟩ := hc
  exact ⟨(DerivedCategory.homologyFunctor A n).mapIso eR ≪≫
    (DerivedCategory.homologyFunctorFactors A n).app C ≪≫ ec⟩

/-- The intrinsic Koszul Ext identifications glue as direct-image-algebra module maps.
This computes cohomology only; it does not identify the derived objects or split
extensions between different cohomological degrees. -/
theorem koszulRegularImmersion_algebraDual_homology {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsNoetherian Y] [IsClosedImmersion i]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wA} (SheafOfModules.{u}
      (moduleRings (directImageAlgebraSpace i)))]
    (hregular : ∀ z : Z, ∃ U : Y.affineOpens, i z ∈ U.1 ∧
      ∃ (n : ℕ) (f : Fin n → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f)
    (r : LocallyConstant Z ℕ)
    (hr : ∀ z : Z, r z = Module.finrank (Z.presheaf.stalk z)
      ((RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj
        ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)))
    (H : schemeDerivedCategory Y ⥤ DerivedCategory (SheafOfModules.{u}
      (moduleRings (directImageAlgebraSpace i))))
    (adjH : (SheafOfModules.restrictScalars
      (R := moduleRings Y.toRingedSpace)
      (R' := moduleRings (directImageAlgebraSpace i))
      ⟨Functor.whiskerRight i.c (forget₂ CommRingCat RingCat)⟩).rightDerivedFunctor ⊣ H) (n : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) n).obj
        (H.obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
            (SheafOfModules.unit Y.ringCatSheaf))) ≅
      (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace i)).obj
        (Scheme.Modules.locallyRankedExteriorTerm
          (SheafOfModules.homObj (R := Z.sheaf)
            ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)
            (SheafOfModules.unit Z.ringCatSheaf)) r n)) := by
  let B : Y.CommAlgebraSheaf := Under.mk (⟨i.c⟩ : Y.sheaf ⟶
    (TopCat.Sheaf.pushforward CommRingCat i.base).obj Z.sheaf)
  let T := SheafOfModules.restrictScalars
    (R := moduleRings Y.toRingedSpace)
    (R' := moduleRings (directImageAlgebraSpace i))
    ⟨Functor.whiskerRight i.c (forget₂ CommRingCat RingCat)⟩
  have : HasDerivedCategory.{wA} (SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).obj B.right)) := by
    dsimp [B]
    exact inferInstanceAs (HasDerivedCategory.{wA}
      (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))))
  have : PreservesFiniteLimits T := sheafAlgebraRestrictScalars_preservesFiniteLimits Y B
  have : PreservesFiniteColimits T := sheafAlgebraRestrictScalars_preservesFiniteColimits Y B
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y)
      (Functor.whiskerRight i.c (forget₂ CommRingCat RingCat)) :=
    closedImmersion_scalar_locallySurjective i
  let full := scalarRestriction_fullyFaithful
    (show moduleRings Y.toRingedSpace ⟶ moduleRings (directImageAlgebraSpace i) from
      ⟨Functor.whiskerRight i.c (forget₂ CommRingCat RingCat)⟩)
  obtain ⟨H₀, adj₀, _, hd⟩ := exists_affine_derivedHom_evaluation_counit i
  let OY := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
      (SheafOfModules.unit Y.ringCatSheaf)
  obtain ⟨d, _⟩ := hd OY
  let eH := Adjunction.rightAdjointUniq adjH adj₀
  let hY := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n
  obtain ⟨eK⟩ := koszulRegularImmersion_scalar_homology i hregular r hr n
  let e := (T.rightDerivedFunctorHomologyFunctorIso n).app (H.obj OY) ≪≫
    hY.mapIso (T.rightDerivedFunctor.mapIso (eH.app OY)) ≪≫ hY.mapIso d ≪≫ eK
  exact ⟨full.preimageIso e⟩

end AlgebraicGeometry
