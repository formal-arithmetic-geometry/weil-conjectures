/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.CategoryTheory.Functor.OfSequence
import Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardFullyFaithful
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! # Lifting the comparison map of the second adic system

Source: Stacks Project, Tag 088A, construction of the maps G_e → H/K^e H.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Full faithfulness of supported completion, transported through closed pushforward. -/
private theorem supported_completion_bijective
    {X Z : Scheme.{u}} [IsNoetherian X] (j : Z ⟶ X) [IsClosedImmersion j]
    (I : X.IdealSheafData)
    (he : (@completion Z (isNoetherian_of_locallyOfFiniteType j) (I.comap j)).IsEquivalence)
    (F G : CoherentModules X)
    (hF : CoherentModuleSupportedOn F j) (hG : CoherentModuleSupportedOn G j) :
    Function.Bijective (formalCompletionMap I : (F.obj ⟶ G.obj) → _) := by
  classical
  let : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType j
  obtain ⟨E, ⟨β⟩⟩ := closedImmersion_coherent_equivalence j
  let Fs := (⟨F, hF⟩ : ObjectProperty.FullSubcategory
    (fun L : CoherentModules X ↦ CoherentModuleSupportedOn L j))
  let Gs := (⟨G, hG⟩ : ObjectProperty.FullSubcategory
    (fun L : CoherentModules X ↦ CoherentModuleSupportedOn L j))
  let FZ := E.inverse.obj Fs
  let GZ := E.inverse.obj Gs
  let A := ObjectProperty.ι (fun L : CoherentModules X ↦ CoherentModuleSupportedOn L j) ⋙
    ObjectProperty.ι (RingedSpace.IsCoherent X.toRingedSpace)
  let a : F.obj ≅ (Scheme.Modules.pushforward j).obj FZ.obj :=
    (A.mapIso (E.counitIso.app Fs)).symm ≪≫ β.app FZ
  let b : G.obj ≅ (Scheme.Modules.pushforward j).obj GZ.obj :=
    (A.mapIso (E.counitIso.app Gs)).symm ≪≫ β.app GZ
  let P := Scheme.Modules.pushforward j
  obtain ⟨hP⟩ := (Functor.FullyFaithful.nonempty_iff_map_bijective P).mpr
    ((closedImmersion_pushforward_fullyFaithful j).2)
  let C := completion Z (I.comap j)
  let := he
  let U := ObjectProperty.ι (RingedSpace.IsCoherent Z.toRingedSpace)
  have hC : C.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful C
  have hCV := hC.comp (ObjectProperty.fullyFaithfulι (IsCoherentFormalModule (I.comap j)))
  obtain ⟨θ, _⟩ := (closedImmersion_coherentFormal_equivalence j I).2
  have hH : (U ⋙ P ⋙ formalCompletionFunctor I).FullyFaithful :=
    (hCV.comp (hP.whiskeringRight ℕᵒᵖ)).ofIso θ.symm
  have hcomposite := hH.map_bijective FZ GZ
  have hPcoh := ((ObjectProperty.fullyFaithfulι
    (RingedSpace.IsCoherent Z.toRingedSpace)).comp hP).map_bijective FZ GZ
  have hquot : Function.Bijective
      ((formalCompletionFunctor I).map : (P.obj FZ.obj ⟶ P.obj GZ.obj) → _) := by
    constructor
    · intro v w h
      obtain ⟨v', rfl⟩ := hPcoh.surjective v
      obtain ⟨w', rfl⟩ := hPcoh.surjective w
      exact congrArg (U ⋙ P).map (hcomposite.injective h)
    · intro v
      obtain ⟨w, hw⟩ := hcomposite.surjective v
      exact ⟨(U ⋙ P).map w, hw⟩
  let T := formalCompletionFunctor I
  change Function.Bijective (T.map : (F.obj ⟶ G.obj) → _)
  change Function.Bijective (T.map : (P.obj FZ.obj ⟶ P.obj GZ.obj) → _) at hquot
  have square (w : F.obj ⟶ G.obj) :
      T.map (Iso.homCongr a b w) =
        Iso.homCongr (T.mapIso a) (T.mapIso b) (T.map w) := by
    exact T.map_homCongr a b w
  constructor
  · intro w w' hw
    apply (Iso.homCongr a b).injective
    apply hquot.injective
    rw [square, square, hw]
  · intro v
    obtain ⟨w, hw⟩ := hquot.surjective (Iso.homCongr (T.mapIso a) (T.mapIso b) v)
    refine ⟨(Iso.homCongr a b).symm w, ?_⟩
    apply (Iso.homCongr (T.mapIso a) (T.mapIso b)).injective
    rw [← square, Equiv.apply_symm_apply, hw]

/-- Raising an annihilating power preserves annihilation. -/
private theorem annihilated_higher_power
    {X : Scheme.{u}} (K : X.IdealSheafData) (F : X.Modules)
    {a b : ℕ} (h : a ≤ b)
    (hz : IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι a).2 F)) :
    IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι b).2 F) := by
  obtain ⟨k, hk⟩ := formalModuleQuotient_factor K (𝟙 F) h
  have hi := hz.eq_zero_of_src
    (Scheme.idealModuleProductι (Scheme.idealSheafPower K.toModulesι a).2 F)
  have : Mono (Scheme.idealModuleProductι (Scheme.idealSheafPower K.toModulesι b).2 F) := by
    dsimp [Scheme.idealModuleProductι]
    infer_instance
  apply IsZero.of_mono_eq_zero
    (Scheme.idealModuleProductι (Scheme.idealSheafPower K.toModulesι b).2 F)
  simpa [hi] using hk

/-- Supported completion gives a Hom bijection for any two bounded K-torsion modules. -/
private theorem torsion_completion_bijective
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (hthick : ∀ (e : ℕ), 1 ≤ e →
      ∀ (hZ : IsNoetherian (K ^ e).subscheme),
        Functor.IsEquivalence
          (@completion ((K ^ e).subscheme) hZ (I.comap (K ^ e).subschemeι)))
    (F G : CoherentModules X) (a b : ℕ)
    (hF : IsZero (Scheme.idealModuleProduct
      (Scheme.idealSheafPower K.toModulesι (a + 1)).2 F.obj))
    (hG : IsZero (Scheme.idealModuleProduct
      (Scheme.idealSheafPower K.toModulesι (b + 1)).2 G.obj)) :
    Function.Bijective (formalCompletionMap I : (F.obj ⟶ G.obj) → _) := by
  let q := max (a + 1) (b + 1)
  have hq : 1 ≤ q := (Nat.succ_le_succ (Nat.zero_le a)).trans (le_max_left _ _)
  have hs (L : CoherentModules X)
      (hz : IsZero (Scheme.idealModuleProduct
        (Scheme.idealSheafPower K.toModulesι q).2 L.obj)) :
      CoherentModuleSupportedOn L (K ^ q).subschemeι := by
    have : L.obj.IsQuasicoherent :=
      ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X L.obj).mp
        L.property).1
    let J := K ^ q
    let i := (Scheme.idealSheafPower K.toModulesι q).2
    let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
    open MonoidalCategory Scheme.Modules in
    have hμ : i ▷ L.obj ≫ (λ_ L.obj).hom = 0 :=
      eq_zero_of_image_eq_zero (hz.eq_of_src _ _)
    open MonoidalCategory Scheme.Modules in
    have hkill (U : X.affineOpens) (a : Γ(J.toModules, U.1)) (t : Γ(L.obj, U.1)) :
        (show Γ(X, U.1) from J.toModulesι.app U.1 a) • t = 0 := by
      have ha : (show Γ(X, U.1) from J.toModulesι.app U.1 a) ∈ K.ideal U ^ q := by
        have hr := (J.range_toModulesι_app U)
        have hm := hr.subset ⟨a, rfl⟩
        change _ ∈ J.ideal U at hm
        simpa only [J, Scheme.IdealSheafData.ideal_pow, Pi.pow_apply] using hm
      have hr := ((ideal_times_quasiCoherent_affine_sections K L.obj).2.2.2.1 U).2.2.2
        q (Nat.lt_of_lt_of_le Nat.zero_lt_one hq)
      obtain ⟨b, hb⟩ := hr.symm.subset ha
      have ht := congrArg (fun f ↦ f.app U.1 (tmulSection b t)) hμ
      rw [Hom.comp_app, ConcreteCategory.comp_apply, whiskerRight_app_tmulSection] at ht
      erw [leftUnitor_hom_app_tmulSection'] at ht
      exact hb ▸ ht
    open MonoidalCategory Scheme.Modules in
    have hμ : J.toModulesι ▷ L.obj ≫ (λ_ L.obj).hom = 0 := by
      have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
      have : J.toModules.IsQuasicoherent :=
        ((ideal_times_quasiCoherent_affine_sections J
          (SheafOfModules.unit X.ringCatSheaf)).2.2.1 1 (by omega))
      have hzero (U : X.affineOpens)
          (s : Γ(J.toModules ⊗ L.obj, U.1)) :
          (J.toModulesι ▷ L.obj ≫ (λ_ L.obj).hom).app U.1 s = 0 := by
        obtain ⟨z, rfl⟩ :=
          (quasiCoherent_tensor_product_affine_sections J.toModules L.obj).2 U.1 U.2 |>.2 s
        induction z using TensorProduct.induction_on with
        | zero => simp only [map_zero]
        | add z z' hz hz' => simp only [map_add, hz, hz', add_zero]
        | tmul a t =>
          rw [tensorSectionsMap_tmul, Hom.comp_app, ConcreteCategory.comp_apply,
            whiskerRight_app_tmulSection]
          erw [leftUnitor_hom_app_tmulSection']
          exact hkill U a t
      apply hom_ext
      intro W
      ext s
      change (J.toModulesι ▷ L.obj ≫ (λ_ L.obj).hom).app W s = 0
      refine TopCat.Sheaf.eq_of_locally_eq' ⟨L.obj.presheaf, L.obj.isSheaf⟩
        (fun i : {V : X.affineOpens // V.1 ≤ W} ↦ i.1.1) W
        (fun i ↦ homOfLE i.2) ?_ _ _ ?_
      · intro x hx
        obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
          X.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
        exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVW⟩, hxV⟩
      · intro i
        rw [← Hom.app_presheaf_map, map_zero]
        exact hzero i.1 _
    change IsZero (Scheme.idealModuleProduct (K ^ q).subschemeι.ker.toModulesι L.obj)
    rw [Scheme.IdealSheafData.ker_subschemeι]
    have : Mono (Scheme.idealModuleProductι J.toModulesι L.obj) := by
      dsimp [Scheme.idealModuleProductι]
      infer_instance
    apply IsZero.of_mono_eq_zero (Scheme.idealModuleProductι J.toModulesι L.obj)
    apply (cancel_epi (factorThruImage _)).mp
    exact (image.fac _).trans hμ
  exact supported_completion_bijective (K ^ q).subschemeι I
    (hthick q hq _) F G
    (hs F (annihilated_higher_power K F.obj (le_max_left _ _) hF))
    (hs G (annihilated_higher_power K G.obj (le_max_right _ _) hG))

/-- Construct a comparison map for an already algebraized second-ideal system.
Source: Stacks Project, Tag 088A (lemma-existence-tricky), construction of
G_e → H/K^e H, using the closed-immersion equivalence of Tag 087T.
https://stacks.math.columbia.edu/tag/088A
(blueprint: lem-weil-pbc-devissage-second-adic-system-lift-compatibility).

Proof: Coherent modules killed by powers of K descend to a common closed thickening.
Closed pushforward is fully faithful and commutes naturally with I-completion.
The assumed completion equivalence on that thickening therefore gives a bijection
on Hom sets for the ambient I-completion. Form the doubly natural morphism τ by
composing σ, the K-reduction of α, and θ inverse. The terms N_e and H/K^(e+1)H
are coherent and annihilated by K^(e+1), so surjectivity lifts τ_e uniquely to d_e.
For adjacent indices, the two composites of d with the transitions have equal
I-completions by naturality of τ. Both endpoints are killed by a common higher
power of K, so injectivity makes the composites equal. Assemble these adjacent
compatible maps as a natural transformation δ. Its component lifting equations,
composed with θ, give precisely the displayed squares. The maps are uniquely
specified by their completions; no arbitrary witness or square hypothesis is used. -/
theorem grothendieckDevissage_secondAdicSystem_lift_compatibility
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (M : CoherentFormalModule X I)
    (hthick : ∀ (e : ℕ), 1 ≤ e →
      ∀ (hZ : IsNoetherian (K ^ e).subscheme),
        Functor.IsEquivalence
          (@completion ((K ^ e).subscheme) hZ (I.comap (K ^ e).subschemeι)))
    (H : CoherentModules X) (α : M ⟶ (completion X I).obj H)
    (θ : formalCompletionSystem K H.obj ⋙ formalCompletionFunctor I ≅
      (formalCompletionSystem I H.obj ⋙ formalCompletionFunctor K).flip)
    {N : CoherentFormalModule X K}
    (σ : N.obj ⋙ formalCompletionFunctor I ≅
      (M.obj ⋙ formalCompletionFunctor K).flip) :
    ∃ (δ : N ⟶ (completion X K).obj H), ∀ e n : ℕ,
      (σ.hom.app (op e)).app (op n) ≫
          formalModuleQuotientMap K (α.hom.app (op n)) (Nat.le_refl (e + 1)) =
        formalModuleQuotientMap I (δ.hom.app (op e)) (Nat.le_refl (n + 1)) ≫
          (θ.hom.app (op e)).app (op n) := by
  classical
  let Q := (completion X K).obj H
  let τ : N.obj ⋙ formalCompletionFunctor I ⟶ Q.obj ⋙ formalCompletionFunctor I :=
    σ.hom ≫ (flipFunctor _ _ _).map
      (Functor.whiskerRight α.hom (formalCompletionFunctor K)) ≫ θ.inv
  let F (e : ℕ) : CoherentModules X := ⟨N.obj.obj (op e), N.property.1 e⟩
  let G (e : ℕ) : CoherentModules X := ⟨Q.obj.obj (op e), Q.property.1 e⟩
  have hbij (e f : ℕ) := torsion_completion_bijective I K hthick (F e) (G f) e f
    (N.property.2.1 e) (Q.property.2.1 f)
  have hlift (e : ℕ) : ∃ d : N.obj.obj (op e) ⟶ Q.obj.obj (op e),
      formalCompletionMap I d = τ.app (op e) :=
    (hbij e e).surjective (τ.app (op e))
  choose d hd using hlift
  have hnat (e : ℕ) : N.obj.map (homOfLE (Nat.le_succ e)).op ≫ d e =
      d (e + 1) ≫ Q.obj.map (homOfLE (Nat.le_succ e)).op := by
    apply (hbij (e + 1) e).injective
    rw [(formalCompletionMap_laws I).2, (formalCompletionMap_laws I).2, hd, hd]
    exact τ.naturality (homOfLE (Nat.le_succ e)).op
  let δ : N ⟶ Q := ⟨NatTrans.ofOpSequence d hnat⟩
  refine ⟨δ, ?_⟩
  intro e n
  have he := congrArg (fun t ↦ t.app (op n)) (hd e)
  change formalModuleQuotientMap I (d e) (Nat.le_refl (n + 1)) =
    (σ.hom.app (op e)).app (op n) ≫
      formalModuleQuotientMap K (α.hom.app (op n)) (Nat.le_refl (e + 1)) ≫
      (θ.inv.app (op e)).app (op n) at he
  change _ = formalModuleQuotientMap I (d e) (Nat.le_refl (n + 1)) ≫ _
  rw [he]
  simp only [Category.assoc, ← NatTrans.comp_app, θ.inv_hom_id,
    NatTrans.id_app]
  exact (Category.comp_id _).symm

end AlgebraicGeometry
