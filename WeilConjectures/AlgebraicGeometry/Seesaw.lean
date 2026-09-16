module

public import WeilConjectures.AlgebraicGeometry.Cohomology.BaseChange
public import WeilConjectures.AlgebraicGeometry.Modules.FibrewiseCriteria
public import WeilConjectures.AlgebraicGeometry.Modules.TrivialLineBundle
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Integral

@[expose] public section
universe u
open CategoryTheory Limits MonoidalCategory SheafOfModules
namespace AlgebraicGeometry.Scheme.Modules

variable {W T : Scheme.{u}}

theorem isCoherent_of_invertible {Z : Scheme.{u}} {L : Z.Modules} (hL : L.Invertible) :
    L.IsCoherent :=
  have := hL.isLocallyFree
  (SheafOfModules.isCoherent_iff L).2 ⟨inferInstance, hL.isFiniteType⟩

@[reassoc]
lemma fiberPullbackIso_hom_naturality (u : W ⟶ T) (x : W) [IsIso (u.residueFieldMap x)]
    {M N : T.Modules} (φ : M ⟶ N) :
    fiberMap ((Modules.pullback u).map φ) x ≫ (fiberPullbackIso u N x).hom =
      (fiberPullbackIso u M x).hom ≫
        (ModuleCat.restrictScalars (inv (u.residueFieldMap x)).hom).map (fiberMap φ (u x)) :=
  (fiberFunctorPullbackIso u x).hom.naturality φ

lemma fiberMap_pullback_map_eq_zero_iff (u : W ⟶ T) (x : W) [IsIso (u.residueFieldMap x)]
    {M N : T.Modules} (φ : M ⟶ N) :
    fiberMap ((Modules.pullback u).map φ) x = 0 ↔ fiberMap φ (u x) = 0 := by
  rw [← Preadditive.IsIso.comp_right_eq_zero (fiberMap ((Modules.pullback u).map φ) x)
      (fiberPullbackIso u N x).hom, fiberPullbackIso_hom_naturality,
    Preadditive.IsIso.comp_left_eq_zero, Functor.map_eq_zero_iff]

lemma fiberMap_ne_zero_of_fiberMk_ne_zero {Z : Scheme.{u}} {A G : Z.Modules} (ψ : A ⟶ G) (w : Z)
    (τ : Γ(A, ⊤)) (h : fiberMk G w (Hom.app ψ ⊤ τ) ≠ 0) : fiberMap ψ w ≠ 0 := by
  intro h0
  refine h ?_
  rw [← fiberMap_fiberMk ψ w τ, h0]
  simp

lemma fiberMap_fiberFreeAdjunction_counit_ne_zero (f : W ⟶ T) (t : T) {G : (f.fiber t).Modules}
    (w : f.fiber t) (σ : Γ(G, ⊤)) (hσ : fiberMk G w σ ≠ 0) :
    fiberMap ((fiberFreeAdjunction f t).counit.app G) w ≠ 0 := by
  refine fiberMap_ne_zero_of_fiberMk_ne_zero _ w
    ((fiberFreeAdjunction f t).unit.app ((fiberSectionsFunctor f t).obj G) σ) ?_
  have h := ConcreteCategory.congr_hom ((fiberFreeAdjunction f t).right_triangle_components G) σ
  rw [ConcreteCategory.comp_apply] at h
  rw [show Hom.app ((fiberFreeAdjunction f t).counit.app G) ⊤
      ((fiberFreeAdjunction f t).unit.app ((fiberSectionsFunctor f t).obj G) σ) = σ from h]
  exact hσ

lemma exists_fiberMk_ne_zero {Z : Scheme.{u}} {G : Z.Modules} (e : G ≅ Z.structureModules) :
    ∃ σ : Γ(G, ⊤), ∀ w : Z, fiberMk G w σ ≠ 0 :=
  ⟨(sectionsEquivOfIsoUnit e).symm 1, fun w ↦ fiberMk_ne_zero_of_isUnit e (by simp) w⟩

theorem finrankFiberSections_eq_one_of_iso (f : W ⟶ T) [IsProper f] (F : W.Modules) (t : T)
    [GeometricallyIntegral (f.fiberToSpecResidueField t)]
    (e : (restrictToFiber f t).obj F ≅ (f.fiber t).structureModules) :
    finrankFiberSections f F t = 1 := by
  let _ : (f.fiber t).Over (Spec (.of ↥(T.residueField t))) := ⟨f.fiberToSpecResidueField t⟩
  have hp : IsProper ((f.fiber t) ↘ Spec (.of ↥(T.residueField t))) :=
    inferInstanceAs (IsProper (f.fiberToSpecResidueField t))
  have hg : GeometricallyIntegral ((f.fiber t) ↘ Spec (.of ↥(T.residueField t))) :=
    inferInstanceAs (GeometricallyIntegral (f.fiberToSpecResidueField t))
  exact finrank_sections_eq_one_of_iso_unit_of_geometricallyIntegral
    (K := ↥(T.residueField t)) (X := f.fiber t) (L := (restrictToFiber f t).obj F) e

theorem finrankFiberSections_eq_one [JacobsonSpace T] [IsNoetherian T] (f : W ⟶ T) [IsProper f]
    (F : W.Modules) [F.IsCoherent] [F.FlatOver f]
    (h : ∀ t : T, IsClosed {t} → finrankFiberSections f F t = 1) (t : T) :
    finrankFiberSections f F t = 1 := by
  have hc2 : IsClosed {s : T | 2 ≤ finrankFiberSections f F s} :=
    isClosed_setOf_le_finrankFiberSections f F 2
  have hc1 : IsClosed {s : T | 1 ≤ finrankFiberSections f F s} :=
    isClosed_setOf_le_finrankFiberSections f F 1
  have hlt : finrankFiberSections f F t < 2 := by
    by_contra hcon
    obtain ⟨s, hs, hsc⟩ :=
      nonempty_inter_closedPoints (Z := {s : T | 2 ≤ finrankFiberSections f F s})
        ⟨t, not_lt.1 hcon⟩ hc2.isLocallyClosed
    rw [Set.mem_ofPred_eq, h s hsc] at hs
    omega
  have hge : (1 : ℕ) ≤ finrankFiberSections f F t := by
    have hsub : closedPoints T ⊆ {s : T | 1 ≤ finrankFiberSections f F s} :=
      fun x hx ↦ by simp [h x hx]
    have hcl := closure_mono hsub
    rw [closure_closedPoints, hc1.closure_eq] at hcl
    exact hcl (Set.mem_univ t)
  omega

section Seesaw

variable (f : W ⟶ T) {L : W.Modules}

lemma fiberMap_counit_ne_zero_of_iso [IsReduced T] [IsNoetherian T] [IsProper f]
    (hL : L.Invertible) [L.FlatOver f] (h1 : ∀ s : T, finrankFiberSections f L s = 1) (t : T)
    (e : (restrictToFiber f t).obj L ≅ (f.fiber t).structureModules) (w : W) (hw : f w = t) :
    fiberMap ((pullbackPushforwardAdjunction f).counit.app L) w ≠ 0 := by
  have hcoh : L.IsCoherent := isCoherent_of_invertible hL
  have hM : ((pushforward f).obj L).Invertible :=
    invertible_pushforward_of_finrankFiberSections_eq_one f L h1
  have hqc : ((Modules.pullback (T.fromSpecResidueField t)).obj
      ((pushforward f).obj L)).IsQuasicoherent :=
    have := (SheafOfModules.Invertible.pullback (T.fromSpecResidueField t) hM).isLocallyFree
    inferInstance
  have hβ : IsIso (fiberBaseChangeMap f L t) :=
    isIso_fiberBaseChangeMap_of_finrankFiberSections_eq f L t h1
  obtain ⟨σ, hσ⟩ := exists_fiberMk_ne_zero e
  obtain ⟨w', hw'⟩ : w ∈ Set.range (f.fiberι t) := by
    rw [f.range_fiberι t]; exact hw
  intro hzero
  rw [← hw', ← fiberMap_pullback_map_eq_zero_iff (f.fiberι t) w'
    ((pullbackPushforwardAdjunction f).counit.app L)] at hzero
  have key := congrArg (fun ψ ↦ fiberMap ψ w') (fiberFreeComparison_comp_map_counit f L t)
  simp only [fiberMap_comp] at key
  rw [hzero, comp_zero] at key
  refine fiberMap_fiberFreeAdjunction_counit_ne_zero f t w' σ (hσ w') ?_
  rw [← Preadditive.IsIso.comp_left_eq_zero
    (fiberMap ((fiberFreeFunctor f t).map (fiberBaseChangeMap f L t)) w')]
  exact key.symm

theorem isIso_counit_of_forall_closedPoint [IsReduced T] [IsNoetherian T] [JacobsonSpace T]
    [IsProper f] (hL : L.Invertible) [L.FlatOver f]
    (h1 : ∀ s : T, finrankFiberSections f L s = 1)
    (htriv : ∀ t : T, IsClosed {t} →
      Nonempty ((restrictToFiber f t).obj L ≅ (f.fiber t).structureModules)) :
    IsIso ((pullbackPushforwardAdjunction f).counit.app L) := by
  have hM : ((pushforward f).obj L).Invertible :=
    have := isCoherent_of_invertible hL
    invertible_pushforward_of_finrankFiberSections_eq_one f L h1
  refine isIso_of_forall_fiberMap_ne_zero (SheafOfModules.Invertible.pullback f hM) hL _
    fun w ↦ ?_
  by_contra hw
  have hNclosed : IsClosed {v : W | fiberMap ((pullbackPushforwardAdjunction f).counit.app L) v = 0}
      := isClosed_setOf_fiberMap_eq_zero (SheafOfModules.Invertible.pullback f hM) hL _
  have himg := f.isClosedMap _ hNclosed
  obtain ⟨t, ⟨v, hv, hvt⟩, htc⟩ :=
    nonempty_inter_closedPoints (Z := f.base '' _) ⟨f w, w, hw, rfl⟩ himg.isLocallyClosed
  obtain ⟨e⟩ := htriv t htc
  exact fiberMap_counit_ne_zero_of_iso f hL h1 t e v hvt hv

/-- The pullback of a sheaf of modules along a section of `f`, pulled back along `f`, is the
sheaf itself. -/
noncomputable def pullbackSectionIso (s : T ⟶ W) (hs : s ≫ f = 𝟙 T) (M : T.Modules) :
    (Modules.pullback s).obj ((Modules.pullback f).obj M) ≅ M :=
  (Modules.pullbackComp s f).app M ≪≫ (Modules.pullbackCongr hs).app M ≪≫
    (Modules.pullbackId T).app M

theorem nonempty_iso_structureModules_of_section [IsReduced T] [IsNoetherian T] [JacobsonSpace T]
    [IsProper f] (hL : L.Invertible) [L.FlatOver f]
    (h1 : ∀ s : T, finrankFiberSections f L s = 1)
    (htriv : ∀ t : T, IsClosed {t} →
      Nonempty ((restrictToFiber f t).obj L ≅ (f.fiber t).structureModules))
    (s : T ⟶ W) (hs : s ≫ f = 𝟙 T)
    (hsec : Nonempty ((Modules.pullback s).obj L ≅ T.structureModules)) :
    Nonempty (L ≅ W.structureModules) := by
  obtain ⟨e⟩ := hsec
  have hiso := isIso_counit_of_forall_closedPoint f hL h1 htriv
  let ε := asIso ((pullbackPushforwardAdjunction f).counit.app L)
  have hMtriv : (pushforward f).obj L ≅ T.structureModules :=
    (pullbackSectionIso f s hs ((pushforward f).obj L)).symm ≪≫
      (Modules.pullback s).mapIso ε ≪≫ e
  exact ⟨ε.symm ≪≫ (Modules.pullback f).mapIso hMtriv ≪≫ Modules.pullbackUnitIso f⟩

end Seesaw

section Projection

variable {K : Type u} [Field K] {X : Scheme.{u}} (πX : X ⟶ Spec (.of K)) (πT : T ⟶ Spec (.of K))

theorem isNoetherian_of_finiteType [LocallyOfFiniteType πT] [QuasiCompact πT] :
    IsNoetherian T :=
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian πT
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace πT
  ⟨⟩

variable [IsProper πX] [GeometricallyIntegral πX] [LocallyOfFiniteType πT] [QuasiCompact πT]

variable {L : (Limits.pullback πX πT).Modules} (hL : L.Invertible)
  [L.FlatOver (Limits.pullback.snd πX πT)]

include hL in
theorem finrankFiberSections_pullbackSnd_eq_one
    (htriv : ∀ t : T, IsClosed {t} →
      Nonempty ((restrictToFiber (Limits.pullback.snd πX πT) t).obj L ≅
        ((Limits.pullback.snd πX πT).fiber t).structureModules))
    (t : T) : finrankFiberSections (Limits.pullback.snd πX πT) L t = 1 :=
  have := isNoetherian_of_finiteType πT
  have : JacobsonSpace T := LocallyOfFiniteType.jacobsonSpace πT
  have := isCoherent_of_invertible hL
  finrankFiberSections_eq_one _ L
    (fun s hs ↦ finrankFiberSections_eq_one_of_iso _ L s (htriv s hs).some) t

include hL in
theorem invertible_pushforward_pullbackSnd [IsReduced T]
    (htriv : ∀ t : T, IsClosed {t} →
      Nonempty ((restrictToFiber (Limits.pullback.snd πX πT) t).obj L ≅
        ((Limits.pullback.snd πX πT).fiber t).structureModules)) :
    ((pushforward (Limits.pullback.snd πX πT)).obj L).Invertible :=
  have := isNoetherian_of_finiteType πT
  have := isCoherent_of_invertible hL
  invertible_pushforward_of_finrankFiberSections_eq_one _ L
    (finrankFiberSections_pullbackSnd_eq_one πX πT hL htriv)

include hL in
theorem isIso_counit_pullbackSnd [IsReduced T]
    (htriv : ∀ t : T, IsClosed {t} →
      Nonempty ((restrictToFiber (Limits.pullback.snd πX πT) t).obj L ≅
        ((Limits.pullback.snd πX πT).fiber t).structureModules)) :
    IsIso ((pullbackPushforwardAdjunction (Limits.pullback.snd πX πT)).counit.app L) :=
  have := isNoetherian_of_finiteType πT
  have : JacobsonSpace T := LocallyOfFiniteType.jacobsonSpace πT
  isIso_counit_of_forall_closedPoint _ hL
    (finrankFiberSections_pullbackSnd_eq_one πX πT hL htriv) htriv

include hL in
theorem nonempty_iso_structureModules_of_sliceInclusionSnd [IsReduced T]
    (htriv : ∀ t : T, IsClosed {t} →
      Nonempty ((restrictToFiber (Limits.pullback.snd πX πT) t).obj L ≅
        ((Limits.pullback.snd πX πT).fiber t).structureModules))
    (x₀ : Spec (.of K) ⟶ X) (hx₀ : x₀ ≫ πX = 𝟙 _)
    (hsec : Nonempty ((Modules.pullback (sliceInclusionSnd πX πT x₀ hx₀)).obj L ≅
      T.structureModules)) :
    Nonempty (L ≅ (Limits.pullback πX πT).structureModules) :=
  have := isNoetherian_of_finiteType πT
  have : JacobsonSpace T := LocallyOfFiniteType.jacobsonSpace πT
  nonempty_iso_structureModules_of_section _ hL
    (finrankFiberSections_pullbackSnd_eq_one πX πT hL htriv) htriv
    (sliceInclusionSnd πX πT x₀ hx₀) (sliceInclusionSnd_snd πX πT x₀ hx₀) hsec

end Projection

end AlgebraicGeometry.Scheme.Modules
