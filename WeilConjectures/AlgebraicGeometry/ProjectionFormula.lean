/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.IntersectionNumber
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyTrivial
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal

/-!
# The generic rank and the projection formula for intersection numbers
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

section Pushforward

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (P : X.Modules)

/-- The sections of a direct image over an open whose preimage is empty vanish. -/
lemma subsingleton_sections_pushforward_of_preimage_eq_bot {W : Y.Opens} (hW : f ⁻¹ᵁ W = ⊥) :
    Subsingleton Γ((pushforward f).obj P, W) := by
  have h : Γ((pushforward f).obj P, W) = Γ(P, ⊥) := by
    rw [pushforward_obj_obj f P W, hW]
  rw [h]
  infer_instance

/-- **The stalks of a direct image vanish away from the image**, in the form in which the
dévissage argument uses it: at a point with a neighbourhood whose preimage is empty. -/
lemma subsingleton_stalk_pushforward {y : Y} {W : Y.Opens} (hy : y ∈ W) (hW : f ⁻¹ᵁ W = ⊥) :
    Subsingleton (((pushforward f).obj P).presheaf.stalk y) := by
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨U, hyU, s, rfl⟩ := ((pushforward f).obj P).presheaf.exists_germ_eq a
  obtain ⟨V, hyV, t, rfl⟩ := ((pushforward f).obj P).presheaf.exists_germ_eq b
  have hyW : y ∈ U ⊓ V ⊓ W := ⟨⟨hyU, hyV⟩, hy⟩
  have hbot : f ⁻¹ᵁ (U ⊓ V ⊓ W) = ⊥ := by
    rw [← le_bot_iff, ← hW]
    exact fun x hx ↦ hx.2
  have : Subsingleton Γ((pushforward f).obj P, U ⊓ V ⊓ W) :=
    subsingleton_sections_pushforward_of_preimage_eq_bot f P hbot
  rw [← TopCat.Presheaf.germ_res_apply ((pushforward f).obj P).presheaf
      (homOfLE (inf_le_left.trans inf_le_left) : U ⊓ V ⊓ W ⟶ U) y hyW s,
    ← TopCat.Presheaf.germ_res_apply ((pushforward f).obj P).presheaf
      (homOfLE (inf_le_left.trans inf_le_right) : U ⊓ V ⊓ W ⟶ V) y hyW t]
  exact congrArg _ (Subsingleton.elim _ _)

/-- **The stalk of a direct image along a closed immersion vanishes off the image.** -/
lemma subsingleton_stalk_pushforward_of_notMem_range (hf : IsClosed (Set.range f.base)) {y : Y}
    (hy : y ∉ Set.range f.base) :
    Subsingleton (((pushforward f).obj P).presheaf.stalk y) :=
  subsingleton_stalk_pushforward f P (W := ⟨(Set.range f.base)ᶜ, hf.isOpen_compl⟩) hy
    (by ext x; simp)

end Pushforward

section GenericRank

variable {X : Scheme.{u}}

/-- **The stalk of a coherent sheaf at the generic point of an integral scheme is a
finite-dimensional vector space over the function field**, so that the generic rank is the
dimension of a finite-dimensional space. -/
instance finiteDimensional_stalk_genericPoint [IsIntegral X] (F : X.Modules) [F.IsCoherent] :
    FiniteDimensional X.functionField (F.presheaf.stalk (genericPoint X)) :=
  finite_stalk F (genericPoint X)

/-- **The generic rank of a coherent sheaf vanishes exactly when the generic point is not in its
support.** -/
lemma genericRank_eq_zero_iff [IsIntegral X] (F : X.Modules) [F.IsCoherent] :
    genericRank F = 0 ↔ genericPoint X ∉ F.support := by
  rw [genericRank, Module.finrank_zero_iff, support, Set.mem_ofPred_eq,
    not_nontrivial_iff_subsingleton]

/-- **The generic rank is monotone along a monomorphism** of sheaves of modules on an integral
scheme. -/
lemma genericRank_le_of_mono [IsIntegral X] {G H : X.Modules} (u : G ⟶ H) [Mono u]
    [H.IsCoherent] : genericRank G ≤ genericRank H := by
  have hmono : Mono (C := SheafOfModules.{u} X.ringCatSheaf) u := inferInstance
  have hm : Mono ((SheafOfModules.stalkFunctor X.ringCatSheaf (genericPoint X)).map u) :=
    (SheafOfModules.stalkFunctor X.ringCatSheaf (genericPoint X)).map_mono _
  have hinj : Function.Injective (PresheafOfModules.stalkMapₗ u.val (genericPoint X)) :=
    (AddCommGrpCat.mono_iff_injective _).1 hm
  exact LinearMap.finrank_le_finrank_of_injective hinj

end GenericRank

section Rank

variable (k : Type u) [Field k] {Y : Scheme.{u}} [Y.Over (Spec (.of k))]

/-- A zero sheaf of modules is coherent. -/
lemma isCoherent_of_isZero {G : Y.Modules} (h : IsZero G) : G.IsCoherent :=
  haveI : Y.structureModules.IsCoherent := (SheafOfModules.invertible_unit Y.sheaf).isCoherent
  (SheafOfModules.isCoherent Y.ringCatSheaf).prop_of_iso
    ((isZero_cokernel_of_epi (𝟙 Y.structureModules)).iso h)
    (isCoherent_cokernel (𝟙 Y.structureModules) inferInstance inferInstance)

/-- **The intersection number depends on the coefficient sheaf only through its isomorphism
class.** -/
lemma intersectionNumber_congr_left {F F' : Y.Modules} (e : F ≅ F') {d : ℕ}
    (L : Fin d → Y.Modules) (hL : ∀ j, (L j).Invertible) :
    intersectionNumber k F L hL = intersectionNumber k F' L hL := by
  rw [intersectionNumber, intersectionNumber]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  congr 1
  exact eulerChar_congr k (tensorIso e (Iso.refl _))

/-- **The intersection number of a zero sheaf vanishes.** -/
lemma intersectionNumber_eq_zero_of_isZero {F : Y.Modules} (hF : IsZero F) {d : ℕ}
    (L : Fin d → Y.Modules) (hL : ∀ j, (L j).Invertible) :
    intersectionNumber k F L hL = 0 := by
  rw [intersectionNumber]
  refine Finset.sum_eq_zero fun S _ ↦ ?_
  exact mul_eq_zero_of_right _
    (eulerChar_eq_zero_of_isZero k ((invertible_zpowProd L hL _).isZero_tensorObj hF))

end Rank

section GenericRankAux

variable {X : Scheme.{u}}

/-- **The generic rank depends on a sheaf only through its isomorphism class.** -/
lemma genericRank_congr [IrreducibleSpace X] {F F' : X.Modules} (e : F ≅ F') :
    genericRank F = genericRank F' :=
  (((stalkFunctor X (genericPoint X)).mapIso e).toLinearEquiv).finrank_eq

/-- **The generic rank of a zero sheaf vanishes.** -/
lemma genericRank_eq_zero_of_isZero [IrreducibleSpace X] {F : X.Modules} (h : IsZero F) :
    genericRank F = 0 := by
  have : Subsingleton (F.presheaf.stalk (genericPoint X)) := by
    rw [← not_nontrivial_iff_subsingleton]
    intro hnt
    have : genericPoint X ∈ F.support := hnt
    simp [(support_eq_empty_iff_isZero F).2 h] at this
  exact (Module.finrank_eq_zero_iff_of_free _ _).mpr this

/-- **The generic rank of the tensor unit is `1`**, the tensor unit being the structure sheaf. -/
lemma genericRank_tensorUnit [IsIntegral X] : genericRank (𝟙_ X.Modules) = 1 :=
  (genericRank_congr (Modules.tensorUnitIsoUnit (X := X))).trans genericRank_unit

end GenericRankAux

section PushforwardIso

variable {Z Y : Scheme.{u}} (ι : Z ⟶ Y) [IsIso ι]

/-- **Pulling back along an isomorphism is an equivalence** of the categories of sheaves of
modules, with inverse the pullback along the inverse isomorphism. -/
noncomputable def pullbackEquivOfIsIso : Y.Modules ≌ Z.Modules :=
  .mk (pullback ι) (pullback (inv ι))
    ((pullbackComp (inv ι) ι ≪≫ eqToIso (congrArg Modules.pullback (IsIso.inv_hom_id ι)) ≪≫
      pullbackId Y).symm)
    (pullbackComp ι (inv ι) ≪≫ eqToIso (congrArg Modules.pullback (IsIso.hom_inv_id ι)) ≪≫
      pullbackId Z)

/-- **The direct image along an isomorphism is the inverse image along its inverse**, both being
right adjoint to the inverse image along the isomorphism. -/
noncomputable def pushforwardIsoPullbackInv : pushforward ι ≅ pullback (inv ι) :=
  (pullbackPushforwardAdjunction ι).rightAdjointUniq (pullbackEquivOfIsIso ι).toAdjunction

/-- **The direct image of the structure sheaf along an isomorphism is the structure sheaf.** -/
noncomputable def pushforwardStructureModulesIso :
    (pushforward ι).obj Z.structureModules ≅ Y.structureModules :=
  (pushforwardIsoPullbackInv ι).app _ ≪≫ pullbackUnitIso (inv ι)

end PushforwardIso

section IntersectionRank

variable (k : Type u) [Field k] {Y : Scheme.{u}} [Y.Over (Spec (.of k))] [Infinite k]
  [IsProper (Y ↘ Spec (.of k))] [IsIntegral Y] {A : Y.Modules} (hA : A.Invertible)
  (hAa : A.IsAmple) {d : ℕ} (hd : topologicalKrullDim Y = (d : WithBot ℕ∞))

include hA hAa hd

/-- **A coherent sheaf whose generic rank vanishes has vanishing top intersection number**: its
support is then a proper closed subset of `Y`, hence of dimension `< d`. -/
theorem intersectionNumber_eq_zero_of_genericRank_eq_zero (F : Y.Modules) [F.IsCoherent]
    (L : Fin d → Y.Modules) (hL : ∀ j, (L j).Invertible) (hr : genericRank F = 0) :
    intersectionNumber k F L hL = 0 := by
  have hcpt : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  refine intersectionNumber_eq_zero_of_supportDim_lt k hA hAa F L hL ?_
  have hns : genericPoint Y ∉ F.support := (genericRank_eq_zero_iff F).1 hr
  rw [supportDim_def, ← hd]
  exact topologicalKrullDim_lt_of_ne_univ (Y ↘ Spec (.of k)) (isClosed_support F)
    fun h ↦ hns (h ▸ Set.mem_univ _)

/-- **A subsheaf of the same generic rank has the same top intersection number**: the quotient
has generic rank zero, so its own intersection number vanishes. -/
theorem intersectionNumber_eq_of_mono {G H : Y.Modules} [G.IsCoherent] [H.IsCoherent]
    (u : G ⟶ H) [Mono u] (hrk : genericRank G = genericRank H) (L : Fin d → Y.Modules)
    (hL : ∀ j, (L j).Invertible) :
    intersectionNumber k G L hL = intersectionNumber k H L hL := by
  have hcohc : (cokernel u).IsCoherent := isCoherent_cokernel u inferInstance inferInstance
  have hSE : (ShortComplex.mk u (cokernel.π u) (by simp)).ShortExact :=
    { exact := ShortComplex.exact_cokernel u }
  have hrk' : genericRank H = genericRank G + genericRank (cokernel u) := hSE.genericRank_add
  have hz : genericRank (cokernel u) = 0 := by omega
  have h0 := intersectionNumber_eq_zero_of_genericRank_eq_zero k hA hAa hd (cokernel u) L hL hz
  have hadd : intersectionNumber k G L hL + intersectionNumber k (cokernel u) L hL
      = intersectionNumber k H L hL := intersectionNumber_add_intersectionNumber k hSE L hL
  omega

/-- **The top intersection number of a graded piece of the dévissage.** A pushforward of a
non-zero ideal sheaf on an integral closed subscheme `Z ⊆ Y` either misses the generic point of
`Y`, and then both sides vanish, or `Z = Y`, and then it is a non-zero ideal sheaf on `Y`, of
generic rank one and with the same intersection number as `𝒪_Y`. -/
theorem intersectionNumber_eq_genericRank_mul_of_isPushforwardIdealSheaf (P : Y.Modules)
    [P.IsCoherent] (hP : IsPushforwardIdealSheaf P) (L : Fin d → Y.Modules)
    (hL : ∀ j, (L j).Invertible) :
    intersectionNumber k P L hL
      = (genericRank P : ℤ) * intersectionNumber k (𝟙_ Y.Modules) L hL := by
  have hunit : (𝟙_ Y.Modules).IsCoherent :=
    (SheafOfModules.invertible_tensorUnit Y.sheaf).isCoherent
  obtain ⟨Z, ι, hι, hZ, I, hI, ⟨e⟩⟩ := hP
  have hι' : IsClosedImmersion ι := hι
  have hZ' : IsIntegral Z := hZ
  by_cases hr : genericRank P = 0
  · rw [hr, intersectionNumber_eq_zero_of_genericRank_eq_zero k hA hAa hd P L hL hr]
    simp
  have hmem : genericPoint Y ∈ Set.range ι.base := by
    by_contra hn
    have hss : Subsingleton (((pushforward ι).obj I.toModules).presheaf.stalk (genericPoint Y)) :=
      subsingleton_stalk_pushforward_of_notMem_range ι I.toModules
        ι.isClosedEmbedding.isClosed_range hn
    exact hr ((genericRank_congr e).trans ((Module.finrank_eq_zero_iff_of_free _ _).mpr hss))
  have hrange : Set.range ι.base = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← genericPoint_closure Y]
    exact ι.isClosedEmbedding.isClosed_range.closure_subset_iff.2 (by simpa using hmem)
  have hsurj : Surjective ι := ⟨Set.range_eq_univ.1 hrange⟩
  have hiso : IsIso ι := isIso_of_isClosedImmersion_of_surjective ι
  set u : P ⟶ 𝟙_ Y.Modules := e.hom ≫ (pushforward ι).map I.toModulesι ≫
    (pushforwardStructureModulesIso ι).hom ≫ (Modules.tensorUnitIsoUnit (X := Y)).inv with hu
  have hmono : Mono u := by rw [hu]; infer_instance
  have hle : genericRank P ≤ 1 := by
    have := genericRank_le_of_mono u
    rwa [genericRank_tensorUnit] at this
  have hP1 : genericRank P = 1 := le_antisymm hle (Nat.one_le_iff_ne_zero.2 hr)
  rw [hP1, Nat.cast_one, one_mul]
  exact intersectionNumber_eq_of_mono k hA hAa hd u (by rw [hP1, genericRank_tensorUnit]) L hL

/-- **The top intersection number sees only the generic rank** (`prop:deg-intersection-rank`).

For `Y` an integral scheme of dimension `d`, proper over the field `k` and carrying an ample
invertible sheaf, for `L₁, …, L_d` invertible and `F` coherent of generic rank `r`,

`(L₁ ⋯ L_d · F) = r · (L₁ ⋯ L_d)`. -/
theorem intersectionNumber_eq_genericRank_mul [IsNoetherian Y] (F : Y.Modules) [F.IsCoherent]
    (L : Fin d → Y.Modules) (hL : ∀ j, (L j).Invertible) :
    intersectionNumber k F L hL
      = (genericRank F : ℤ) * intersectionNumber k (𝟙_ Y.Modules) L hL := by
  obtain ⟨t, G, φ, hG0, ⟨eF⟩, hstep⟩ := exists_devissage F
  have key : ∀ j : Fin (t + 1), (G j).IsCoherent ∧
      intersectionNumber k (G j) L hL
        = (genericRank (G j) : ℤ) * intersectionNumber k (𝟙_ Y.Modules) L hL := by
    refine Fin.induction ⟨isCoherent_of_isZero hG0, ?_⟩ ?_
    · rw [intersectionNumber_eq_zero_of_isZero k hG0, genericRank_eq_zero_of_isZero hG0]
      simp
    · rintro j ⟨hcoh, ih⟩
      obtain ⟨hcohs, hmono, hpush⟩ := hstep j
      have hcoh1 : (G j.castSucc).IsCoherent := hcoh
      have hcoh2 : (G j.succ).IsCoherent := hcohs
      have hmono' : Mono (φ j) := hmono
      have hcohc : (cokernel (φ j)).IsCoherent :=
        isCoherent_cokernel (φ j) inferInstance hcohs
      have hSE : (ShortComplex.mk (φ j) (cokernel.π (φ j)) (by simp)).ShortExact :=
        { exact := ShortComplex.exact_cokernel (φ j) }
      have hrk : genericRank (G j.succ)
          = genericRank (G j.castSucc) + genericRank (cokernel (φ j)) := hSE.genericRank_add
      have hadd : intersectionNumber k (G j.castSucc) L hL
            + intersectionNumber k (cokernel (φ j)) L hL
          = intersectionNumber k (G j.succ) L hL :=
        intersectionNumber_add_intersectionNumber k hSE L hL
      have hcok := intersectionNumber_eq_genericRank_mul_of_isPushforwardIdealSheaf k hA hAa hd
        (cokernel (φ j)) hpush L hL
      refine ⟨hcohs, ?_⟩
      rw [← hadd, ih, hcok, hrk]
      push_cast
      ring
  obtain ⟨-, hlast⟩ := key (Fin.last t)
  rw [← intersectionNumber_congr_left k eF L hL, hlast, genericRank_congr eF]

end IntersectionRank

section ProjectionFormula

variable (k : Type u) [Field k] {X Y : Scheme.{u}} [X.Over (Spec (.of k))]
  [Y.Over (Spec (.of k))] (f : X ⟶ Y) [IsFinite f] [f.IsOver (Spec (.of k))]

/-- **The degree of a finite morphism** onto an irreducible scheme: the generic rank of the
direct image `f_* 𝒪_X` of the structure sheaf. -/
noncomputable def _root_.AlgebraicGeometry.Scheme.Hom.degree {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IrreducibleSpace Y] : ℕ :=
  genericRank ((pushforward f).obj X.structureModules)

/-- **The Euler characteristic of a twist of `𝒪_X` by an inverse image** is the Euler
characteristic of the corresponding twist of `f_* 𝒪_X`: this is the invariance of the Euler
characteristic along a finite morphism together with the projection formula. -/
lemma eulerChar_tensorObj_pullback (N : Y.Modules) (hN : N.Invertible) :
    eulerChar k (X.structureModules ⊗ (pullback f).obj N)
      = eulerChar k ((pushforward f).obj X.structureModules ⊗ N) := by
  have hXc : X.structureModules.IsCoherent := (SheafOfModules.invertible_unit X.sheaf).isCoherent
  have hNl : N.IsLocallyFree := hN.isLocallyFree
  have hNf : N.IsFiniteType := hN.isFiniteType
  have hc : (X.structureModules ⊗ (pullback f).obj N).IsCoherent :=
    isCoherent_tensorObj_of_invertible X.structureModules (hN.pullback f)
  rw [← eulerChar_pushforward k f (X.structureModules ⊗ (pullback f).obj N)]
  exact eulerChar_congr k (pushforwardTensorPullbackIso f X.structureModules N)

/-- **The intersection number of the inverse images is the intersection number on the target
with coefficients in `f_* 𝒪_X`.** This is the sheaf-theoretic half of the projection formula. -/
theorem intersectionNumber_pullback_structureModules {d : ℕ} (L : Fin d → Y.Modules)
    (hL : ∀ j, (L j).Invertible) :
    intersectionNumber k X.structureModules (fun j ↦ (pullback f).obj (L j))
        (fun j ↦ (hL j).pullback f)
      = intersectionNumber k ((pushforward f).obj X.structureModules) L hL := by
  rw [intersectionNumber, intersectionNumber]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  congr 1
  have hpic : Pic.mk (zpowProd (fun j ↦ (pullback f).obj (L j)) (fun j ↦ (hL j).pullback f)
        (fun j ↦ if j ∈ S then 1 else 0)) (invertible_zpowProd _ _ _)
      = Pic.mk ((pullback f).obj (zpowProd L hL fun j ↦ if j ∈ S then 1 else 0))
        ((invertible_zpowProd L hL _).pullback f) := by
    rw [Pic.mk_zpowProd, ← Pic.map_mk (hM := invertible_zpowProd L hL _), Pic.mk_zpowProd,
      map_prod]
    exact Finset.prod_congr rfl fun j _ ↦ by rw [map_zpow, Pic.map_mk]
  obtain ⟨eZ⟩ := Pic.mk_eq_mk_iff.1 hpic
  calc eulerChar k (tensorZPow X.structureModules (fun j ↦ (pullback f).obj (L j))
          (fun j ↦ (hL j).pullback f) fun j ↦ if j ∈ S then 1 else 0)
      = eulerChar k (X.structureModules ⊗
          (pullback f).obj (zpowProd L hL fun j ↦ if j ∈ S then 1 else 0)) :=
        eulerChar_congr k (tensorIso (Iso.refl _) eZ)
    _ = eulerChar k ((pushforward f).obj X.structureModules ⊗
          zpowProd L hL fun j ↦ if j ∈ S then 1 else 0) :=
        eulerChar_tensorObj_pullback k f _ (invertible_zpowProd L hL _)
    _ = eulerChar k (tensorZPow ((pushforward f).obj X.structureModules) L hL
          fun j ↦ if j ∈ S then 1 else 0) := rfl

/-- **The projection formula for intersection numbers** (`prop:deg-projection-formula`).

For a finite morphism `f : X ⟶ Y` of schemes over `k` with `Y` integral of dimension `d`, proper
over `k` and carrying an ample invertible sheaf, and for `L₁, …, L_d` invertible on `Y`,

`(f^* L₁ ⋯ f^* L_d)_X = deg f · (L₁ ⋯ L_d)_Y`,

where `deg f` is the generic rank of `f_* 𝒪_X`. -/
theorem intersectionNumber_pullback_eq_degree_mul [Infinite k] [IsProper (Y ↘ Spec (.of k))]
    [IsIntegral Y] [IsNoetherian Y] {A : Y.Modules} (hA : A.Invertible) (hAa : A.IsAmple)
    {d : ℕ} (hd : topologicalKrullDim Y = (d : WithBot ℕ∞)) (L : Fin d → Y.Modules)
    (hL : ∀ j, (L j).Invertible) :
    intersectionNumber k X.structureModules (fun j ↦ (pullback f).obj (L j))
        (fun j ↦ (hL j).pullback f)
      = (f.degree : ℤ) * intersectionNumber k (𝟙_ Y.Modules) L hL := by
  have hXc : X.structureModules.IsCoherent := (SheafOfModules.invertible_unit X.sheaf).isCoherent
  have hc : ((pushforward f).obj X.structureModules).IsCoherent :=
    isCoherent_pushforward_of_isFinite f X.structureModules
  rw [intersectionNumber_pullback_structureModules k f L hL]
  exact intersectionNumber_eq_genericRank_mul k hA hAa hd _ L hL

end ProjectionFormula

end AlgebraicGeometry.Scheme.Modules
