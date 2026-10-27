/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.Blowup.AdmissibleBlowup
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.TraceFormula.SchematicallyDenseOpen
import Sheaf.AlgebraicGeometry.FlatteningModuleByAdmissibleBlowup
import WeilConjectures.Blowup.BlowupUniversal
import Sheaf.AlgebraicGeometry.FlatIdealStrictTransformComparison
import Sheaf.AlgebraicGeometry.EtaleFlatSupportedIdealInvertible
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine
import WeilConjectures.AlgebraicGeometry.Modules.LocalPresentation
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent

/-! # Principalizing a supported ideal on an etale scheme by modifying its base

Source: Stacks Project, More on Flatness, Tag 0815 (`theorem-flatten-module`),
Divisors, Tags 080D, 0809 and 080F, and More on Morphisms, Tag 080Q;
ILO XX 4.4, printed p.373 (blueprint: lem-per-etale-supported-ideal-principalization).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.IdealSheafData

open TopologicalSpace Opposite in
private theorem structure_module_stalk_iso (X : AlgebraicGeometry.RingedSpace.{u}) (x : X) :
    let S := AlgebraicGeometry.RingedSpace.moduleStalkFunctor X x
    ∃ e : S.obj (SheafOfModules.unit (moduleRings X)) ≅
        ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x),
      ∀ (U : TopologicalSpace.Opens X) (hx : x ∈ U) (r : X.presheaf.obj (op U)),
        e.hom (TopCat.Presheaf.germ (SheafOfModules.unit (moduleRings X)).val.presheaf
          U x hx r) = X.presheaf.germ U x hx r := by
  let D := (OpenNhds.inclusion x).op ⋙ X.presheaf
  let A := forget₂ CommRingCat.{u} RingCat.{u} ⋙
    forget₂ RingCat.{u} AddCommGrpCat.{u}
  let e : ↑(TopCat.Presheaf.stalk (C := Ab.{u})
      (SheafOfModules.unit (moduleRings X)).val.presheaf x) ≃+ X.presheaf.stalk x :=
    (preservesColimitIso A D).symm.addCommGroupIsoToAddEquiv
  have hg (U : TopologicalSpace.Opens X) (hx : x ∈ U) (r : X.presheaf.obj (op U)) :
      e (TopCat.Presheaf.germ (SheafOfModules.unit (moduleRings X)).val.presheaf
        U x hx r) = X.presheaf.germ U x hx r := by
    change (colimit.ι (D ⋙ A) (Opposite.op (⟨U, hx⟩ : OpenNhds x)) ≫
      (preservesColimitIso A D).inv) r = _
    rw [ι_preservesColimitIso_inv]
    rfl
  let f : (RingedSpace.moduleStalkFunctor X x).obj
      (SheafOfModules.unit (moduleRings X)) →ₗ[X.presheaf.stalk x] X.presheaf.stalk x :=
    { e.toAddMonoidHom with
      map_smul' := by
        intro r m
        obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq r
        obtain ⟨V, hxV, m, rfl⟩ :=
          TopCat.Presheaf.exists_germ_eq
            (SheafOfModules.unit (moduleRings X)).val.presheaf m
        have hx : x ∈ U ⊓ V := ⟨hxU, hxV⟩
        rw [← X.presheaf.germ_res_apply (homOfLE inf_le_left) x hx r,
          ← TopCat.Presheaf.germ_res_apply
            (SheafOfModules.unit (moduleRings X)).val.presheaf
            (homOfLE inf_le_right) x hx m,
          ← PresheafOfModules.germ_smul (R := X.presheaf)]
        let r' := X.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op r
        let m' : X.presheaf.obj (op (U ⊓ V)) :=
          (SheafOfModules.unit (moduleRings X)).val.presheaf.map
            (homOfLE inf_le_right : U ⊓ V ⟶ V).op m
        change e (TopCat.Presheaf.germ
          (SheafOfModules.unit (moduleRings X)).val.presheaf (U ⊓ V) x hx (r' * m')) =
          X.presheaf.germ (U ⊓ V) x hx r' * (e (TopCat.Presheaf.germ
            (SheafOfModules.unit (moduleRings X)).val.presheaf (U ⊓ V) x hx m') :
              X.presheaf.stalk x)
        rw [hg, hg]
        exact map_mul (X.presheaf.germ (U ⊓ V) x hx).hom _ _ }
  refine ⟨(LinearEquiv.ofBijective f e.bijective).toModuleIso, ?_⟩
  exact hg


private theorem isIso_restrict_ideal_inclusion {X : Scheme.{u}}
    (K : X.IdealSheafData) (U : X.Opens) (hunit : K.comap U.ι = ⊤) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map K.toModulesι) := by
  apply Scheme.Modules.isIso_of_bijective_app_of_isAffineOpen
  intro W hW
  change Function.Bijective (K.toModulesι.app (U.ι ''ᵁ W))
  refine ⟨K.injective_toModulesι_app _, fun a ↦ ?_⟩
  apply (K.range_toModulesι_app ⟨_, hW.image_of_isOpenImmersion U.ι⟩).superset
  obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso (U.ι.appIso W).inv).2 a
  have hb : b ∈ (K.comap U.ι).ideal ⟨W, hW⟩ := by rw [hunit]; trivial
  rw [ideal_comap_of_isOpenImmersion, Ideal.mem_comap] at hb
  change (U.ι.appIso W).inv.hom b ∈
    K.ideal ⟨U.ι ''ᵁ W, hW.image_of_isOpenImmersion U.ι⟩
  exact hb

private theorem supported_ideal_flattening_input {S X : Scheme.{u}}
    (f : X ⟶ S) [Flat f] (K : X.IdealSheafData) (U : S.Opens)
    (hunit : K.comap (f ⁻¹ᵁ U).ι = ⊤) :
    ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj K.toModules).IsFinitePresentation ∧
      (∀ x : X, f x ∈ U → Module.Flat (S.presheaf.stalk (f x))
        ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj K.toModules))) := by
  have hi := isIso_restrict_ideal_inclusion K (f ⁻¹ᵁ U) hunit
  let e := asIso ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map K.toModulesι) ≪≫
    Scheme.Modules.restrictUnitIso (f ⁻¹ᵁ U).ι
  have hu : (SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf).IsFinitePresentation :=
    have : (SheafOfModules.free (R := (f ⁻¹ᵁ U).toScheme.ringCatSheaf)
        (ULift.{u} PUnit)).IsFinitePresentation :=
      Scheme.Modules.isFinitePresentation_free (X := (f ⁻¹ᵁ U).toScheme) _
    Scheme.Modules.isFinitePresentation_of_iso
      (SheafOfModules.freeUniqueIso (R := (f ⁻¹ᵁ U).toScheme.ringCatSheaf)
        (ULift.{u} PUnit))
  have := hu
  refine ⟨Scheme.Modules.isFinitePresentation_of_iso e.symm, ?_⟩
  intro x hx
  let T := RingedSpace.moduleStalkFunctor X.toRingedSpace x
  have hj : IsIso (T.map K.toModulesι) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact Scheme.Modules.bijective_stalk_of_isIso_restrict K.toModulesι (U := f ⁻¹ᵁ U) x hx
  obtain ⟨eu, _⟩ := structure_module_stalk_iso X.toRingedSpace x
  let ex := asIso (T.map K.toModulesι) ≪≫ eu
  let r := (f.stalkMap x).hom
  let : Algebra (S.presheaf.stalk (f x)) (X.presheaf.stalk x) := r.toAlgebra
  have hflat : Module.Flat (S.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (Flat.iff_flat_stalkMap (f := f)).mp inferInstance x
  let er := (ModuleCat.restrictScalars r).mapIso ex
  exact (Module.Flat.equiv_iff er.toLinearEquiv).mpr hflat

/-- An ideal on an etale scheme, supported outside a quasi-compact schematically dense
Cartier complement, becomes invertible after an admissible blowup of the base.
The centre `B.I` specifies the blowup `B.I.blowupMap`; the extended ideal is its actual
ideal-sheaf pullback along the first projection, including its inclusion into the structure
sheaf. `IsInvertible` means affine-locally generated by a nonzerodivisor, equivalently locally
free of rank one as an ideal. No Noetherian or excellence assumption is made.

Source: Stacks Project, Tag 0815 (`theorem-flatten-module`), applied to the ideal;
Divisors, Tags 080D, 0809 and 080F; More on Morphisms, Tag 080Q; ILO XX 4.4, p.373
(blueprint: lem-per-etale-supported-ideal-principalization).

Proof:
1. Apply lem-trf-flattening-module-by-admissible-blowup to `e` and `K.toModules`.
   Over the preserved open this is the structure sheaf, finitely presented and flat over
   the base because `e` is etale. Obtain a finite-type admissible centre and a module strict
   transform on `Y = V ×_S B.I.blowup` that is finitely presented and flat over the new base.
2. The projection from `Y` is etale by lem-weil-pbc-etale-scheme-base-change and of finite
   presentation by lem-weil-pbc-qcqs-morphism-permanence. By
   lemma-nagata-cartier-total-transform-blowup the boundary remains Cartier. Apply
   lem-trf-relative-flat-cartier-support to the structure sheaf: restriction to the open
   complement of the pulled-back boundary is injective on sections of every open of `Y`.
3. By lem-pur-ideal-tensor-pullback-comparison the image of the tensor pullback of the ideal
   in the structure sheaf is the extended ideal. Its kernel is supported on the exceptional
   divisor since the blowup is an isomorphism off its centre
   (thm-nagata-global-blowup-complement). Conversely any section supported there maps to
   zero on the preserved open, hence to zero by step 2. The supported-section quotient of
   def-trf-module-strict-transform is therefore precisely the extended ideal.
4. It is now finitely presented and flat over the new base. By
   lem-weil-pbc-etale-fibre-discrete-separable-points the fibre local rings are fields, so
   its fibre stalks are flat. Apply lem-trf-flat-fibre-free-neighbourhood to obtain finite
   free neighbourhoods everywhere on `Y`.
5. On a nonempty affine neighbourhood with boundary equation `d`, step 2 makes `d` regular.
   Thus the localization at `d` is nonzero. The ideal is the unit ideal there, forcing the
   local free rank to be one by passage to a residue field. A free generator of an ideal
   is regular because its inclusion into the structure sheaf is injective. Conversely,
   multiplication by a regular generator identifies the ideal with the ring. This proves
   the asserted equivalence; the empty fibre product needs no local verification. -/
theorem exists_admissibleBlowup_isInvertible_comap_etale
    {S V : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    [CompactSpace V] [QuasiSeparatedSpace V]
    (D : S.IdealSheafData) (hD : D.IsInvertible)
    (hU : IsCompact (D.support.compl : Set S))
    (hdense : SchematicallyDenseOpen D.support.compl)
    (e : V ⟶ S) [Etale e] [QuasiCompact e] [IsSeparated e]
    (K : V.IdealSheafData) (hK : K.toModules.IsQuasiCoherentFiniteType)
    (hunit : K.comap (e ⁻¹ᵁ D.support.compl).ι = ⊤) :
    ∃ B : IsAdmissible S D.support.compl,
      (K.comap (pullback.fst e B.I.blowupMap)).IsInvertible := by
  have _hdense := hdense
  have : K.toModules.IsQuasicoherent := hK.1
  have : K.toModules.IsFiniteType := hK.2
  obtain ⟨hfpU, hflatU⟩ := supported_ideal_flattening_input e K D.support.compl hunit
  obtain ⟨B, hflat, hfp⟩ :=
    exists_flat_finitePresentation_moduleStrictTransform_admissibleBlowup
      e K.toModules D.support.compl hU hfpU hflatU
  have : B.I.toModules.IsFiniteType := B.I.isFiniteType_toModules_sheaf B.finiteType
  let p := pullback.fst e B.I.blowupMap
  let g := pullback.snd e B.I.blowupMap
  let L := K.comap p
  obtain ⟨a⟩ := Scheme.Modules.nonempty_moduleStrictTransform_ideal_iso_comap e B.I K
  have : (@Scheme.Modules.moduleStrictTransform V S e B.I
      (B.I.isFiniteType_toModules_sheaf B.finiteType) K.toModules hK.1).IsFinitePresentation :=
    hfp
  have : L.toModules.IsFinitePresentation := Scheme.Modules.isFinitePresentation_of_iso a
  have hflatL (x : (pullback e B.I.blowupMap : Scheme.{u})) :
      Module.Flat (B.I.blowup.presheaf.stalk (g x))
        ((ModuleCat.restrictScalars (g.stalkMap x).hom).obj
          ((RingedSpace.moduleStalkFunctor _ x).obj L.toModules)) := by
    let ax := (ModuleCat.restrictScalars (g.stalkMap x).hom).mapIso
      ((RingedSpace.moduleStalkFunctor _ x).mapIso a)
    exact (Module.Flat.equiv_iff ax.toLinearEquiv).mp (hflat x)
  have hboundary : (D.comap B.I.blowupMap).IsInvertible := hD.comap_blowupMap B.I
  let W := g ⁻¹ᵁ (D.comap B.I.blowupMap).support.compl
  have hW : W ≤ p ⁻¹ᵁ (e ⁻¹ᵁ D.support.compl) := by
    intro x hx
    change e (p x) ∈ D.support.compl
    have hsq : e (p x) = B.I.blowupMap (g x) :=
      congrArg (fun t : pullback e B.I.blowupMap ⟶ S ↦ t x) pullback.condition
    rw [hsq]
    change g x ∉ (D.comap B.I.blowupMap).support at hx
    rw [support_comap] at hx
    exact hx
  have hunitL : L.comap W.ι = ⊤ := by
    change (K.comap p).comap W.ι = ⊤
    rw [← comap_comp, ← Scheme.Hom.resLE_comp_ι p hW,
      comap_comp, hunit, comap_top]
  exact ⟨B, isInvertible_of_etale_flat_finitePresentation g
    (D.comap B.I.blowupMap) hboundary L hflatL hunitL⟩

end AlgebraicGeometry.Scheme.IdealSheafData
