/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.Coproducts
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjectiveResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective

/-!
# Right derived functors of finite cohomological dimension

Let `F : C ⥤ D` be a left exact additive functor between abelian categories which has *finite
cohomological dimension*: there is `d` with `R^q F X = 0` for every object `X` and every
`q > d`. Then:

* `F` sends exact complexes of `F`-acyclic objects to exact complexes, with no boundedness
  assumption (`HomologicalComplex.Acyclic.map_of_rightAcyclic_of_isZero_rightDerived`). The
  proof is the dimension shifting argument of the bounded below case
  (`HomologicalComplex.Acyclic.map_of_rightAcyclic`): for an exact complex `K` the cycles
  satisfy `R^q F(Zⁿ) ⊆ R^{q+1} F(Zⁿ⁻¹) ⊆ ⋯ ⊆ R^{q+d} F(Zⁿ⁻ᵈ) = 0` for `q ≥ 1`.
* Consequently `F` preserves quasi-isomorphisms between unbounded complexes of `F`-acyclic
  objects, and the unbounded right derived functor `RF` is computed by applying `F` termwise to
  any complex of `F`-acyclic objects
  (`CategoryTheory.Functor.isIso_rightDerivedFunctorUnit_app_of_rightAcyclic`), when `C` is a
  Grothendieck abelian category (whose K-injective resolutions have injective components).
* If moreover `F` commutes with coproducts of shape `J` and `F`-acyclic objects are stable under
  such coproducts, then `RF` commutes with coproducts of shape `J`
  (`CategoryTheory.Functor.preservesColimitsOfShape_rightDerivedFunctor`): a family in `D(C)` is
  represented by K-injective complexes with injective components, whose coproduct is a complex of
  `F`-acyclic objects computing the coproduct in `D(C)`.

This is the abstract part of Stacks, Tag 0F11 (blueprint `lem-kun-0f11`).

The finite cohomological dimension is expressed through the unbounded right derived functor:
`H^q(RF(X[0])) = 0` for `q > d`; it is equivalent to the vanishing of the classical right
derived functors (`CategoryTheory.Functor.isZero_rightDerived_of_isZero_homology`).
-/

@[expose] public section

open CategoryTheory Limits

namespace HomologicalComplex

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [HasInjectiveResolutions C]
  [Abelian D]

/-- A left exact additive functor `F : C ⥤ D` of finite cohomological dimension (`R^q F = 0` for
`q > d`) sends an exact cochain complex `K` whose terms are all `F`-acyclic to an exact complex
`F(K)`, with no boundedness assumption on `K`.

The short exact sequences `0 ⟶ Zⁿ⁻¹ ⟶ Kⁿ⁻¹ ⟶ Zⁿ ⟶ 0` of cycles give injections
`R^q F(Zⁿ) ⟶ R^{q+1} F(Zⁿ⁻¹)` for `q ≥ 1`, so `R^q F(Zⁿ)` embeds into
`R^{q+d} F(Zⁿ⁻ᵈ) = 0`: all the cycles are `F`-acyclic, and `F` keeps the short exact sequences
of cycles exact. -/
theorem Acyclic.map_of_rightAcyclic_of_isZero_rightDerived {K : CochainComplex C ℤ}
    (hK : K.Acyclic) (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] (d : ℕ)
    (hF : ∀ (X : C) (q : ℕ), d < q → IsZero ((F.rightDerived q).obj X))
    (hK' : ∀ n, F.rightAcyclic (K.X n)) :
    ((F.mapHomologicalComplex _).obj K).Acyclic := by
  have hS (n : ℤ) := (hK (n + 1)).shortExact_cyclesShortComplex (i := n) (by simp)
  -- dimension shifting: `R^{q+1} F(Zⁿ) = 0` as soon as `d ≤ q + k`, by induction on `k`
  have hZ' (k : ℕ) : ∀ (n : ℤ) (q : ℕ), d ≤ q + k →
      IsZero ((F.rightDerived (q + 1)).obj (K.cycles n)) := by
    induction k with
    | zero => exact fun n q hq ↦ hF _ _ (by lia)
    | succ k ih =>
      intro n q hq
      obtain ⟨δ, w₁, w₂, h, -⟩ := (hS (n - 1)).exists_rightDerived_δ_exact F (q + 1)
      have h' := (h.isZero_X₂_iff).2
        ⟨(hK' (n - 1) q).eq_of_src _ _, (ih (n - 1) (q + 1) (by lia)).eq_of_tgt _ _⟩
      have h'' : IsZero ((F.rightDerived (q + 1)).obj (K.cycles (n - 1 + 1))) := h'
      rwa [sub_add_cancel] at h''
  have hZ (n : ℤ) : F.rightAcyclic (K.cycles n) := fun q ↦ hZ' d n q (by lia)
  intro m
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by lia⟩
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp; lia)]
  let T := ShortComplex.mk (F.map (K.iCycles (n + 1))) (F.map (K.d (n + 1) (n + 2)))
    (by rw [← F.map_comp, iCycles_d, F.map_zero])
  have hT : IsLimit (KernelFork.ofι T.f T.zero) :=
    isLimitForkMapOfIsLimit' F _ (K.cyclesIsKernel (n + 1) (n + 2) (by simp; lia))
  have : Epi (F.map (K.toCycles n (n + 1))) :=
    ((hS n).map_of_rightAcyclic (hZ n)).epi_g
  let φ : ((F.mapHomologicalComplex _).obj K).sc' n (n + 1) (n + 2) ⟶ T :=
    { τ₁ := F.map (K.toCycles n (n + 1))
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [T, ← F.map_comp] }
  rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ]
  exact ShortComplex.exact_of_f_is_kernel _ hT

end HomologicalComplex

namespace CategoryTheory

namespace Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

section Classical

variable [HasInjectiveResolutions C] (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

/-- A left exact additive functor of finite cohomological dimension preserves
quasi-isomorphisms between (unbounded) cochain complexes of `F`-acyclic objects: the mapping
cone is an exact complex of `F`-acyclic objects. -/
theorem quasiIso_map_of_rightAcyclic_of_isZero_rightDerived {K L : CochainComplex C ℤ}
    (φ : K ⟶ L) [QuasiIso φ] (d : ℕ)
    (hF : ∀ (X : C) (q : ℕ), d < q → IsZero ((F.rightDerived q).obj X))
    (hK : ∀ n, F.rightAcyclic (K.X n)) (hL : ∀ n, F.rightAcyclic (L.X n)) :
    QuasiIso ((F.mapHomologicalComplex _).map φ) := by
  have hφ := (CochainComplex.mappingCone.quasiIso_iff_acyclic φ).1 ‹_›
  rw [CochainComplex.mappingCone.quasiIso_iff_acyclic]
  refine HomologicalComplex.Acyclic.of_iso ?_
    (CochainComplex.mappingCone.mapHomologicalComplexIso φ F)
  refine hφ.map_of_rightAcyclic_of_isZero_rightDerived F d hF fun n ↦ ?_
  exact F.rightAcyclic.prop_of_iso
    (HomologicalComplex.homotopyCofiber.XIsoBiprod φ n (n + 1) rfl).symm
    (rightAcyclic_biprod (hK (n + 1)) (hL n))

end Classical

section Derived

variable [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
  (F : C ⥤ D) [F.Additive]

/-- The vanishing of `H^q(RF(X[0]))` for the unbounded right derived functor `RF` is the
vanishing of the classical right derived functor `R^q F X`. -/
lemma isZero_rightDerived_of_isZero_homology [HasInjectiveResolutions C] (X : C) (q : ℕ)
    (h : IsZero ((DerivedCategory.homologyFunctor D q).obj
      (F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj X)))) :
    IsZero ((F.rightDerived q).obj X) :=
  h.of_iso ((CochainComplex.KInjectiveResolution.rightDerivedHomologyIsoRightDerived F
      (injectiveResolution X).kInjectiveResolution q).symm ≪≫
    (CochainComplex.KInjectiveResolution.homologyRightDerivedFunctorObjIso F
      (injectiveResolution X).kInjectiveResolution q).symm ≪≫
    (DerivedCategory.homologyFunctor D q).mapIso (F.rightDerivedFunctor.mapIso
      ((DerivedCategory.singleFunctorIsoCompQ C 0).app X).symm))

variable [PreservesFiniteLimits F]

/-- **Acyclic complexes compute the unbounded right derived functor.** Let `C` be a Grothendieck
abelian category and `F : C ⥤ D` a left exact additive functor of finite cohomological dimension.
For every (unbounded) cochain complex `K` of `F`-acyclic objects, the unit
`F(K) ⟶ RF(K)` of the right derived functor is an isomorphism.

Indeed `K` has a quasi-isomorphism `K ⟶ I` to a K-injective complex with injective components
(`CochainComplex.toKInjectiveResolution`), at which the unit is an isomorphism, and `F` maps it to
a quasi-isomorphism (`Functor.quasiIso_map_of_rightAcyclic_of_isZero_rightDerived`). -/
theorem isIso_rightDerivedFunctorUnit_app_of_rightAcyclic [IsGrothendieckAbelian.{w} C]
    [HasInjectiveResolutions C] (d : ℕ)
    (hF : ∀ (X : C) (q : ℕ), d < q → IsZero ((F.rightDerived q).obj X))
    (K : CochainComplex C ℤ) (hK : ∀ n, F.rightAcyclic (K.X n)) :
    IsIso (F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C (.up ℤ)).obj K)) := by
  let ι := (CochainComplex.toKInjectiveResolution.{w} C).app K
  have : QuasiIso ι := (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{w} C K).2
  have := F.quasiIso_map_of_rightAcyclic_of_isZero_rightDerived ι d hF hK
    (fun n ↦ rightAcyclic_of_injective _)
  have h₁ : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map ι)) :=
    Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso C _) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2
        ((HomologicalComplex.mem_quasiIso_iff _).2 inferInstance))
  have h₂ : IsIso ((F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).map
      ((HomotopyCategory.quotient C (.up ℤ)).map ι)) := by
    dsimp only [Functor.comp_map]
    rw [Functor.mapHomotopyCategory_map]
    exact Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso D _) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2
        ((HomologicalComplex.mem_quasiIso_iff _).2 inferInstance))
  have h₃ : IsIso ((DerivedCategory.Qh ⋙ F.rightDerivedFunctor).map
      ((HomotopyCategory.quotient C (.up ℤ)).map ι)) := by
    dsimp only [Functor.comp_map]
    infer_instance
  have h₄ : IsIso (F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C (.up ℤ)).obj
      ((CochainComplex.kInjectiveResolutionFunctor.{w} C).obj K))) := inferInstance
  exact IsIso.of_isIso_fac_right (h := (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).map
    ((HomotopyCategory.quotient C (.up ℤ)).map ι) ≫ F.rightDerivedFunctorUnit.app _)
    (F.rightDerivedFunctorUnit.naturality _).symm

/-- **Right derived functors of finite cohomological dimension commute with coproducts.** Let
`C` be a Grothendieck abelian category and `F : C ⥤ D` a left exact additive functor of finite
cohomological dimension which commutes with coproducts of shape `J`, and such that coproducts of
shape `J` of `F`-acyclic objects are `F`-acyclic. Then the unbounded right derived functor
`RF : D(C) ⥤ D(D)` commutes with coproducts of shape `J`.

A family in `D(C)` is represented by K-injective complexes `I j` with injective components. The
coproduct `∐ I j` of complexes is a coproduct in `D(C)` (`DerivedCategory.isColimitCofanMkQObj`)
and a complex of `F`-acyclic objects, so `RF(∐ I j) ≅ F(∐ I j) ≅ ∐ F(I j) ≅ ∐ RF(I j)`
(`Functor.isIso_rightDerivedFunctorUnit_app_of_rightAcyclic`). -/
theorem preservesColimitsOfShape_rightDerivedFunctor [IsGrothendieckAbelian.{w} C]
    [HasInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D] (J : Type*)
    [HasColimitsOfShape (Discrete J) C] [HasColimitsOfShape (Discrete J) D]
    [PreservesColimitsOfShape (Discrete J) F] (d : ℕ)
    (hF : ∀ (X : C) (q : ℕ), d < q → IsZero ((F.rightDerived q).obj X))
    (hJ : ∀ X : J → C, (∀ j, F.rightAcyclic (X j)) → F.rightAcyclic (∐ X)) :
    PreservesColimitsOfShape (Discrete J) F.rightDerivedFunctor where
  preservesColimit {G} := by
    let I (j : J) := (CochainComplex.kInjectiveResolutionFunctor.{w} C).obj
      (DerivedCategory.Q.objPreimage (G.obj ⟨j⟩))
    have hι (j : J) : IsIso (DerivedCategory.Q.map ((CochainComplex.toKInjectiveResolution.{w}
        C).app (DerivedCategory.Q.objPreimage (G.obj ⟨j⟩)))) :=
      Localization.inverts DerivedCategory.Q (HomologicalComplex.quasiIso C _) _
        ((CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{w} C _).2)
    let e : Discrete.functor (fun j ↦ DerivedCategory.Q.obj (I j)) ≅ G :=
      Discrete.natIso fun j ↦ (asIso (DerivedCategory.Q.map
        ((CochainComplex.toKInjectiveResolution.{w} C).app
          (DerivedCategory.Q.objPreimage (G.obj ⟨j.as⟩))))).symm ≪≫
        DerivedCategory.Q.objObjPreimageIso _
    suffices PreservesColimit (Discrete.functor fun j ↦ DerivedCategory.Q.obj (I j))
        F.rightDerivedFunctor from preservesColimit_of_iso_diagram _ e
    -- the coproduct of the complexes `I j` is a complex of `F`-acyclic objects
    have hinj (j : J) (n : ℤ) : Injective ((I j).X n) :=
      CochainComplex.injective_kInjectiveResolutionFunctor_obj_X.{w} _ n
    -- the coproduct of the complexes `I j` is a complex of `F`-acyclic objects
    have hP (n : ℤ) : F.rightAcyclic ((∐ I).X n) :=
      F.rightAcyclic.prop_of_iso
        (PreservesCoproduct.iso (HomologicalComplex.eval C (.up ℤ) n) I).symm
        (hJ _ fun j ↦ have := hinj j n; rightAcyclic_of_injective ((I j).X n))
    -- the comparison maps `F(K) ⟶ RF(K)`, natural in `K`
    let v (K : CochainComplex C ℤ) : DerivedCategory.Q.obj ((F.mapHomologicalComplex _).obj K) ⟶
        F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K) :=
      (DerivedCategory.quotientCompQhIso D).inv.app _ ≫
        F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C (.up ℤ)).obj K) ≫
          F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso C).hom.app K)
    have nat {K L : CochainComplex C ℤ} (f : K ⟶ L) :
        DerivedCategory.Q.map ((F.mapHomologicalComplex _).map f) ≫ v L =
          v K ≫ F.rightDerivedFunctor.map (DerivedCategory.Q.map f) := by
      have h := F.rightDerivedFunctorUnit.naturality ((HomotopyCategory.quotient C (.up ℤ)).map f)
      simp only [Functor.comp_map, Functor.mapHomotopyCategory_map] at h
      simp only [v, DerivedCategory.quotientCompQhIso_inv_naturality_assoc, Category.assoc]
      rw [reassoc_of% h, ← Functor.map_comp, ← Functor.map_comp,
        DerivedCategory.quotientCompQhIso_hom_naturality]
    have hv (K : CochainComplex C ℤ) (hK : ∀ n, F.rightAcyclic (K.X n)) : IsIso (v K) := by
      have := F.isIso_rightDerivedFunctorUnit_app_of_rightAcyclic d hF K hK
      dsimp only [v]
      infer_instance
    have hu (j : J) : IsIso (v (I j)) :=
      hv _ fun n ↦ have := hinj j n; rightAcyclic_of_injective _
    have huP : IsIso (v (∐ I)) := hv _ hP
    -- the image under `F` of the coproduct cofan is a coproduct in `D(D)`
    have hFc : IsColimit (Cofan.mk (DerivedCategory.Q.obj ((F.mapHomologicalComplex _).obj (∐ I)))
        fun j ↦ DerivedCategory.Q.map ((F.mapHomologicalComplex _).map (Sigma.ι I j))) :=
      DerivedCategory.isColimitCofanMkQObj
        ((isColimitMapCoconeCofanMkEquiv (F.mapHomologicalComplex (.up ℤ)) I (Sigma.ι I)).1
          (isColimitOfPreserves (F.mapHomologicalComplex (.up ℤ)) (coproductIsCoproduct I)))
    refine preservesColimit_of_preserves_colimit_cocone
      (DerivedCategory.isColimitCofanMkQObj (coproductIsCoproduct I))
      ((isColimitMapCoconeCofanMkEquiv _ _ _).2 ?_)
    refine (IsColimit.equivOfNatIsoOfIso (Discrete.natIso fun j ↦ asIso (v (I j.as))) _ _
      (Cocone.ext (asIso (v (∐ I))) fun j ↦ ?_)) hFc
    dsimp
    rw [Category.assoc, nat]
    simp

/-- **Right derived functors of finite cohomological dimension commute with coproducts**, when
all the classical right derived functors `R^n F` (`n ≥ 0`) commute with coproducts of shape `J`:
`R^0 F ≅ F` commutes with them, and a coproduct of `F`-acyclic objects is `F`-acyclic
(`Functor.preservesColimitsOfShape_rightDerivedFunctor`). -/
theorem preservesColimitsOfShape_rightDerivedFunctor_of_rightDerived [IsGrothendieckAbelian.{w} C]
    [HasInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D] (J : Type*)
    [HasColimitsOfShape (Discrete J) C] [HasColimitsOfShape (Discrete J) D] (d : ℕ)
    (hF : ∀ (X : C) (q : ℕ), d < q → IsZero ((F.rightDerived q).obj X))
    (hJ : ∀ n, PreservesColimitsOfShape (Discrete J) (F.rightDerived n)) :
    PreservesColimitsOfShape (Discrete J) F.rightDerivedFunctor :=
  have : PreservesColimitsOfShape (Discrete J) F :=
    have := hJ 0
    preservesColimitsOfShape_of_natIso F.rightDerivedZeroIsoSelf
  F.preservesColimitsOfShape_rightDerivedFunctor J d hF fun X hX q ↦
    have := hJ (q + 1)
    IsZero.of_iso ((IsZero.iff_id_eq_zero _).2
        (Sigma.hom_ext _ _ fun j ↦ (hX j q).eq_of_src _ _))
      (PreservesCoproduct.iso (F.rightDerived (q + 1)) X)

end Derived

end Functor

end CategoryTheory
