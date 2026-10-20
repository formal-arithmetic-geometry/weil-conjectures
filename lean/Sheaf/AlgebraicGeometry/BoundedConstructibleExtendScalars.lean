/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Sheaf.UpstreamExtra.WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
/-! # Exact scalar extension preserves bounded constructible module objects

Source: upstream master, SixFunctors/ProEtale/ModuleObject/Colimit/TwoColimit.lean,
module docstring, preservation of finite presentations and boundedness
(blueprint: lem-weil-pbc-bounded-constructible-exact-scalar-extension).
-/

@[expose] public section
universe u
open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
variable {X Y : Scheme.{u}} (g : Y ⟶ X)
  (R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
  [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ]
omit [IsCommMonObj S] in
private noncomputable def pullbackExtendScalarsIso :
    Mod.extendScalars φ ⋙ (upperStar Ab.{u + 1} g).mapMod S ≅
      (upperStar Ab.{u + 1} g).mapMod R ⋙
        Mod.extendScalars ((upperStar Ab.{u + 1} g).map φ) := by
  let F := upperStar Ab.{u + 1} g
  let G := lowerStar Ab.{u + 1} g
  let adj := upperStarLowerStarAdjunction Ab.{u + 1} g
  let a := (Mod.extendRestrictAdjunction φ).comp (adj.mapModAdjunction S)
  let b := (adj.mapModAdjunction R).comp
    (Mod.extendRestrictAdjunction (F.map φ))
  have e : Mod.comap (F.map φ) ⋙
      (G.mapMod (F.obj R) ⋙ Mod.comap (adj.unitAlgHom R)) ≅
      (G.mapMod (F.obj S) ⋙ Mod.comap (adj.unitAlgHom S)) ⋙ Mod.comap φ :=
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (G.mapModComapIso (F.map φ)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Mod.comapComp _ _).symm ≪≫
    Functor.isoWhiskerLeft _ (Mod.comapCongr (adj.unit.naturality φ).symm) ≪≫
    Functor.isoWhiskerLeft _ (Mod.comapComp _ _) ≪≫
    (Functor.associator _ _ _).symm
  exact a.leftAdjointUniq (b.ofNatIsoRight e)

lemma fp_iff_of_iso {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (e : M ≅ N) : Mod.IsFinitelyPresented R M ↔ Mod.IsFinitelyPresented R N := by
  constructor
  · intro h
    rcases h with ⟨n, m, f, ⟨i⟩⟩
    exact ⟨n, m, f, ⟨e.symm ≪≫ i⟩⟩
  · intro h
    rcases h with ⟨n, m, f, ⟨i⟩⟩
    exact ⟨n, m, f, ⟨e ≪≫ i⟩⟩

lemma fp_map {X Y : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) [MonObj R] [MonObj S]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) S)
    [F.Additive] [PreservesFiniteColimits F]
    (e : F.obj (Mod.regular R) ≅ Mod.regular S)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : Mod.IsFinitelyPresented R M) : Mod.IsFinitelyPresented S (F.obj M) := by
  rcases h with ⟨n, m, f, ⟨i⟩⟩
  let en (n : ℕ) : F.obj (Mod.finiteFree R n) ≅ Mod.finiteFree S n :=
    F.mapBiproduct (fun _ : Fin n ↦ Mod.regular R) ≪≫ biproduct.mapIso (fun _ ↦ e)
  let f' : Mod.finiteFree S m ⟶ Mod.finiteFree S n := (en m).inv ≫ F.map f ≫ (en n).hom
  exact ⟨n, m, f', ⟨F.mapIso i ≪≫ PreservesCokernel.iso F f ≪≫
    cokernel.mapIso (F.map f) f' (en m) (en n) (by simp [f'])⟩⟩


private noncomputable def extendScalarsRegularIso :
    (Mod.extendScalars φ).obj (Mod.regular R) ≅ Mod.regular S := by
  let e₀ := Mod.toBimodRegularIso (R := R)
  let B := Bimod.ofMonHom φ
  let e₁ : B.tensorBimod ((Mod.toBimod R).obj (Mod.regular R)) ≅
      B.tensorBimod (Bimod.regular (Mon.mk R)) :=
    { hom := Bimod.whiskerLeft B e₀.hom
      inv := Bimod.whiskerLeft B e₀.inv
      hom_inv_id := by rw [← Bimod.whiskerLeft_comp_bimod, Iso.hom_inv_id];
                       exact Bimod.whiskerLeft_id_bimod
      inv_hom_id := by rw [← Bimod.whiskerLeft_comp_bimod, Iso.inv_hom_id];
                       exact Bimod.whiskerLeft_id_bimod }
  let e := e₁ ≪≫ Bimod.rightUnitorBimod B
  exact Mod.isoMk
    { hom := e.hom.hom
      inv := e.inv.hom
      hom_inv_id := congrArg Bimod.Hom.hom e.hom_inv_id
      inv_hom_id := congrArg Bimod.Hom.hom e.inv_hom_id }
    e.hom.left_act_hom


omit [IsCommMonObj S] in
lemma fp_extend
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : Mod.IsFinitelyPresented R M) :
    Mod.IsFinitelyPresented S ((Mod.extendScalars φ).obj M) :=
  fp_map R S (Mod.extendScalars φ) (extendScalarsRegularIso R S φ) h

omit [IsCommMonObj R] in
private lemma lfp_of_iso
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : IsLocallyFinitelyPresented R M) (e : M ≅ N) :
    IsLocallyFinitelyPresented R N := by
  rcases h with ⟨U, hU⟩
  exact ⟨U, fun i ↦ (fp_iff_of_iso ((upperStar Ab.{u + 1} (U.f i)).mapMod R |>.mapIso e)).mp
    (hU i)⟩

omit [IsCommMonObj S] in
private lemma lfp_extend
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : IsLocallyFinitelyPresented R M) :
    IsLocallyFinitelyPresented S ((Mod.extendScalars φ).obj M) := by
  rcases h with ⟨U, hU⟩
  refine ⟨U, fun i ↦ ?_⟩
  let F := upperStar Ab.{u + 1} (U.f i)
  exact (fp_iff_of_iso ((pullbackExtendScalarsIso (U.f i) R S φ).app M).symm).mp
    (fp_extend (F.obj R) (F.obj S) (F.map φ) (hU i))

omit [IsCommMonObj S] in
private lemma constructible_extend
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : IsConstructibleModuleObject R M) :
    IsConstructibleModuleObject S ((Mod.extendScalars φ).obj M) := by
  rcases h with ⟨U, hU⟩
  refine ⟨U, fun i ↦ ?_⟩
  let F := upperStar Ab.{u + 1} (U.immersion i)
  exact lfp_of_iso (F.obj S) (lfp_extend (F.obj R) (F.obj S) (F.map φ) (hU i))
    ((pullbackExtendScalarsIso (U.immersion i) R S φ).app M).symm


omit [IsCommMonObj S] [IsCommMonObj R] in
private lemma constructible_of_iso
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : IsConstructibleModuleObject R M) (e : M ≅ N) :
    IsConstructibleModuleObject R N := by
  rcases h with ⟨U, hU⟩
  exact ⟨U, fun i ↦ lfp_of_iso _ (hU i)
    (((upperStar Ab.{u + 1} (U.immersion i)).mapMod R).mapIso e)⟩

/-- Exact extension of scalars preserves bounded constructible complexes of module objects.
Source: upstream master, ModuleObject/Colimit/TwoColimit.lean, Sorried input, preservation
paragraph (blueprint: lem-weil-pbc-bounded-constructible-exact-scalar-extension).

Proof: scalar extension preserves colimits and sends the regular module to the regular
module, hence preserves finite free presentations. Monoidal pullback commutes with scalar
extension: the two left adjoints have canonically isomorphic right adjoints, by naturality
of the pullback adjunction unit. Thus the same presentation covers and stratification
witness constructibility after scalar extension. Exact scalar extension commutes with
derived cohomology. It preserves zero objects, so the old cohomological bounds remain
valid; its preservation of constructible sheaves applies to each cohomology object.
This also includes zero rings, rank-zero presentations, and the empty scheme. -/
theorem boundedConstructible_leftDerivedExtendScalars_obj
    [PreservesFiniteLimits (Mod.extendScalars φ)]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R))
    (hK : boundedConstructible R K) :
    boundedConstructible S ((Mod.extendScalars φ).leftDerivedFunctor.obj K) := by
  rw [mem_boundedConstructible_iff] at hK ⊢
  obtain ⟨⟨a, b, hab⟩, hK⟩ := hK
  let F := Mod.extendScalars φ
  refine ⟨⟨a, b, fun i hi ↦ ?_⟩, fun n ↦ ?_⟩
  · exact (F.map_isZero (hab i hi)).of_iso
      ((F.leftDerivedFunctorHomologyFunctorIso i).app K).symm
  · exact constructible_of_iso S (constructible_extend R S φ (hK n))
      ((F.leftDerivedFunctorHomologyFunctorIso n).app K)

end AlgebraicGeometry.ProEtale
