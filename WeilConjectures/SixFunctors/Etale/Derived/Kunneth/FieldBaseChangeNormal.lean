/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.LimitBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OpenImmersionBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.SepClosedPushforward
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Coefficients

/-!
# Base change along a limit of schemes of finite type over a field

Let `K` be a field, `n` an integer invertible in `K` and killing the coefficient ring `Λ`, and
`X` a scheme of finite type over `K`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace CategoryTheory

variable {J : Type*} [Category J] {C : Type*} [Category C]

/-- Converse of `CategoryTheory.IsPullback.isPullback_map_of_isLimit`: given a system of
cartesian squares `Pⱼ → Xⱼ, Pⱼ → Yⱼ, Xⱼ → Sⱼ, Yⱼ → Sⱼ`, limit cones of the diagrams `X`, `Y`,
`S`, and a cone `cP` over `P` whose induced square of cone points is cartesian, the cone `cP`
is a limit cone. -/
noncomputable def IsPullback.isLimitOfIsPullbackMap {P X Y S : J ⥤ C} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (h : ∀ j, IsPullback (fst.app j) (snd.app j) (f.app j) (g.app j))
    {cP : Cone P} {cX : Cone X} {cY : Cone Y} {cS : Cone S} (hX : IsLimit cX)
    (hY : IsLimit cY) (hS : IsLimit cS)
    (hP : IsPullback (hX.map cP fst) (hY.map cP snd) (hS.map cX f) (hS.map cY g)) :
    IsLimit cP where
  lift s := hP.lift (hX.map s fst) (hY.map s snd) (hS.hom_ext fun j ↦ by simp [(h j).w])
  fac s j := (h j).hom_ext
    (by rw [Category.assoc, ← IsLimit.map_π, ← Category.assoc, hP.lift_fst, IsLimit.map_π])
    (by rw [Category.assoc, ← IsLimit.map_π, ← Category.assoc, hP.lift_snd, IsLimit.map_π])
  uniq s m hm := hP.hom_ext (hX.hom_ext fun j ↦ by simp [← hm])
    (hY.hom_ext fun j ↦ by simp [← hm])

namespace Limits

variable [HasPullbacks C]

/-- Pullbacks in a functor category are computed pointwise. -/
lemma isPullback_pullback_app {F G H : J ⥤ C} (f : F ⟶ H) (g : G ⟶ H) (j : J) :
    IsPullback ((pullback.fst f g).app j) ((pullback.snd f g).app j) (f.app j) (g.app j) :=
  (IsPullback.of_hasPullback f g).map ((evaluation J C).obj j)

/-- The transition squares of the diagram `j ↦ X ×_W Dⱼ` over the diagram `D` are cartesian. -/
lemma isPullback_pullback_const_map {D : J ⥤ C} {W X : C} (a : X ⟶ W)
    (w : D ⟶ (Functor.const J).obj W) {j k : J} (u : j ⟶ k) :
    IsPullback ((pullback ((Functor.const J).map a) w).map u)
      ((pullback.snd ((Functor.const J).map a) w).app j)
      ((pullback.snd ((Functor.const J).map a) w).app k) (D.map u) := by
  refine IsPullback.of_right ?_ ((pullback.snd ((Functor.const J).map a) w).naturality u).symm
    (isPullback_pullback_app _ w k)
  have h₁ : (pullback ((Functor.const J).map a) w).map u ≫
      (pullback.fst ((Functor.const J).map a) w).app k =
        (pullback.fst ((Functor.const J).map a) w).app j := by
    simpa using (pullback.fst ((Functor.const J).map a) w).naturality u
  have h₂ : D.map u ≫ w.app k = w.app j := by simpa using w.naturality u
  rw [h₁, h₂]
  exact isPullback_pullback_app _ w j

/-- The cone with vertex `X'` over the diagram `j ↦ X ×_W Dⱼ`, for a commutative square
`X' → X, X' → lim D` over `W`. -/
@[simps pt]
noncomputable def pullbackConstCone {D : J ⥤ C} {W X : C} (a : X ⟶ W)
    (w : D ⟶ (Functor.const J).obj W) (cD : Cone D) {X' : C} (b : X' ⟶ X) (p' : X' ⟶ cD.pt)
    {w₀ : cD.pt ⟶ W} (hw₀ : ∀ j, cD.π.app j ≫ w.app j = w₀) (hb : b ≫ a = p' ≫ w₀) :
    Cone (pullback ((Functor.const J).map a) w) where
  pt := X'
  π :=
    { app j := (isPullback_pullback_app _ w j).lift b (p' ≫ cD.π.app j) (by simp [hw₀, hb])
      naturality j k u := (isPullback_pullback_app _ w k).hom_ext (by simp) (by simp) }

@[reassoc (attr := simp)]
lemma pullbackConstCone_π_app_fst {D : J ⥤ C} {W X : C} (a : X ⟶ W)
    (w : D ⟶ (Functor.const J).obj W) (cD : Cone D) {X' : C} (b : X' ⟶ X) (p' : X' ⟶ cD.pt)
    {w₀ : cD.pt ⟶ W} (hw₀ : ∀ j, cD.π.app j ≫ w.app j = w₀) (hb : b ≫ a = p' ≫ w₀) (j : J) :
    (pullbackConstCone a w cD b p' hw₀ hb).π.app j ≫
      (pullback.fst ((Functor.const J).map a) w).app j = b :=
  IsPullback.lift_fst _ _ _ _

@[reassoc (attr := simp)]
lemma pullbackConstCone_π_app_snd {D : J ⥤ C} {W X : C} (a : X ⟶ W)
    (w : D ⟶ (Functor.const J).obj W) (cD : Cone D) {X' : C} (b : X' ⟶ X) (p' : X' ⟶ cD.pt)
    {w₀ : cD.pt ⟶ W} (hw₀ : ∀ j, cD.π.app j ≫ w.app j = w₀) (hb : b ≫ a = p' ≫ w₀) (j : J) :
    (pullbackConstCone a w cD b p' hw₀ hb).π.app j ≫
      (pullback.snd ((Functor.const J).map a) w).app j = p' ≫ cD.π.app j :=
  IsPullback.lift_snd _ _ _ _

/-- Over a connected index category, the base change `X ×_W (lim D)` of a limit along a map
`a : X ⟶ W` is the limit of the base changes `X ×_W Dⱼ`. -/
noncomputable def isLimitPullbackConstCone [IsConnected J] {D : J ⥤ C} {W X : C} (a : X ⟶ W)
    (w : D ⟶ (Functor.const J).obj W) {cD : Cone D} (hD : IsLimit cD) {X' : C} (b : X' ⟶ X)
    (p' : X' ⟶ cD.pt) {w₀ : cD.pt ⟶ W} (hw₀ : ∀ j, cD.π.app j ≫ w.app j = w₀)
    (hpb : IsPullback b p' a w₀) :
    IsLimit (pullbackConstCone a w cD b p' hw₀ hpb.w) := by
  refine IsPullback.isLimitOfIsPullbackMap (isPullback_pullback_app _ w)
    (isLimitConstCone J X) hD (isLimitConstCone J W) ?_
  have e₁ : (isLimitConstCone J X).map (pullbackConstCone a w cD b p' hw₀ hpb.w)
      (pullback.fst ((Functor.const J).map a) w) = b :=
    (isLimitConstCone J X).hom_ext fun j ↦ by simp
  have e₂ : hD.map (pullbackConstCone a w cD b p' hw₀ hpb.w)
      (pullback.snd ((Functor.const J).map a) w) = p' :=
    hD.hom_ext fun j ↦ by simp
  have e₃ : (isLimitConstCone J W).map (constCone J X) ((Functor.const J).map a) = a :=
    (isLimitConstCone J W).hom_ext fun j ↦ by
      rw [IsLimit.map_π]
      simp
  have e₄ : (isLimitConstCone J W).map cD w = w₀ :=
    (isLimitConstCone J W).hom_ext fun j ↦ by
      rw [IsLimit.map_π]
      simp [hw₀]
  rw [e₁, e₂, e₃, e₄]
  exact hpb

end Limits

end CategoryTheory

namespace Subalgebra

variable {R : Type*} {A : Type u} [CommRing R] [CommRing A] [Algebra R A] {ι : Type u}
  [Preorder ι]

/-- The diagram in `CommRingCat` given by a monotone family of subalgebras. -/
@[simps]
def diagramOfMonotone (F : ι →o Subalgebra R A) : ι ⥤ CommRingCat.{u} where
  obj i := CommRingCat.of (F i)
  map f := CommRingCat.ofHom (Subalgebra.inclusion (F.monotone (leOfHom f))).toRingHom

/-- The cocone with vertex `A` over the diagram of a monotone family of subalgebras. -/
@[simps]
def coconeOfMonotone (F : ι →o Subalgebra R A) : Cocone (diagramOfMonotone F) where
  pt := CommRingCat.of A
  ι := { app i := CommRingCat.ofHom (F i).val.toRingHom }

/-- A monotone family of subalgebras of `A` indexed by a nonempty directed order, whose union is
`A`, exhibits `A` as the filtered colimit of its members in `CommRingCat`. -/
noncomputable def isColimitCoconeOfMonotone [IsDirectedOrder ι] [Nonempty ι]
    (F : ι →o Subalgebra R A) (hcov : ∀ x : A, ∃ i, x ∈ F i) :
    IsColimit (coconeOfMonotone F) := by
  have := reflectsColimit_of_reflectsIsomorphisms (diagramOfMonotone F) (forget CommRingCat.{u})
  refine isColimitOfReflects (forget CommRingCat.{u}) (Types.FilteredColimit.isColimitOf' _ _
    (fun x ↦ ?_) (fun i x y h ↦ ⟨i, 𝟙 i, ?_⟩))
  · obtain ⟨i, hx⟩ := hcov x
    exact ⟨i, ⟨x, hx⟩, rfl⟩
  · exact Subtype.ext h

end Subalgebra

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Base change along a cofiltered limit of morphisms `gᵢ : Tᵢ ⟶ Sᵢ` of schemes of finite type
over a field `K`, for the base changes `Xᵢ = X ×_K Sᵢ` of a scheme `X` of finite type over `K`.

Let `t : T ⟶ S'` be the limit of the `gᵢ` (with affine transition maps), `X' = X ×_K S'` and
`Y = X' ×_{S'} T`. Then the exchange morphism `p'⁻¹ R^q t_* F ⟶ R^q h_* e⁻¹ F` is an
isomorphism for every sheaf `F` pulled back from `Spec K`: by the limit theorem (blueprint
`lem-kun-0ezt`, `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isLimit`) this reduces
to the stages, where it is `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_field`. -/
theorem Etale.isIso_baseChangeHomologyMap_of_isLimit_of_field {K : Type u} [Field K]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a]
    (n : ℕ) (hn : IsUnit (n : K)) (hΛ : (n : Λ) = 0)
    {I : Type u} [Category.{u} I] [IsCofiltered I] {S T : I ⥤ Scheme.{u}} (g : T ⟶ S)
    (w : S ⟶ (Functor.const I).obj (Spec (.of K)))
    [∀ i, LocallyOfFiniteType (w.app i)] [∀ i, QuasiCompact (w.app i)]
    [∀ i, IsSeparated (g.app i)] [∀ i, LocallyOfFiniteType (g.app i)]
    [∀ i, QuasiCompact (g.app i)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (S.map f)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (T.map f)]
    {cS : Cone S} (hS : IsLimit cS) {cT : Cone T} (hT : IsLimit cT)
    (s : cS.pt ⟶ Spec (.of K)) (hs : ∀ i, cS.π.app i ≫ w.app i = s)
    (t : cT.pt ⟶ cS.pt) (ht : ∀ i, t ≫ cS.π.app i = cT.π.app i ≫ g.app i)
    [QuasiCompact t] [QuasiSeparated t]
    {X' : Scheme.{u}} (b : X' ⟶ X) (p' : X' ⟶ cS.pt) (hpb : IsPullback b p' a s)
    {Y : Scheme.{u}} {e : Y ⟶ cT.pt} {h : Y ⟶ X'} (sq : IsPullback e h t p') (q : ℤ)
    (G : Sheaf (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (Etale.baseChangeHomologyMap Λ sq q (((t ≫ s)^*[ModuleCat.{u + 1} Λ]).obj G)) := by
  have : IsConnected I := IsCofiltered.isConnected I
  let a' := (Functor.const I).map a
  let XD := pullback a' w
  let YD := pullback a' (g ≫ w)
  let pD : XD ⟶ S := pullback.snd _ _
  let eD : YD ⟶ T := pullback.snd _ _
  let hD : YD ⟶ XD := pullback.map _ _ _ _ (𝟙 _) g (𝟙 _) (by simp) (by simp)
  have hX := isPullback_pullback_app a' w
  have hY := isPullback_pullback_app a' (g ≫ w)
  have h₁ : hD ≫ pullback.fst a' w = pullback.fst a' (g ≫ w) := by simp [hD]
  have h₂ : hD ≫ pD = eD ≫ g := by simp [hD, pD, eD]
  have h₁' (i : I) :
      hD.app i ≫ (pullback.fst a' w).app i = (pullback.fst a' (g ≫ w)).app i := by
    rw [← NatTrans.comp_app, h₁]
  have h₂' (i : I) : hD.app i ≫ pD.app i = eD.app i ≫ g.app i := by
    rw [← NatTrans.comp_app, h₂, NatTrans.comp_app]
  have hsq (i : I) : IsPullback (eD.app i) (hD.app i) (g.app i) (pD.app i) := by
    refine (IsPullback.of_right ?_ (h₂' i) (hX i)).flip
    rw [h₁' i]
    exact hY i
  have hsT (i : I) : cT.π.app i ≫ (g ≫ w).app i = t ≫ s := by
    rw [NatTrans.comp_app, ← Category.assoc, ← ht, Category.assoc, hs]
  have hpbY : IsPullback (h ≫ b) e a (t ≫ s) := sq.flip.paste_horiz hpb
  let cX := pullbackConstCone a w cS b p' hs hpb.w
  let cY := pullbackConstCone a (g ≫ w) cT (h ≫ b) e hsT hpbY.w
  have hXl : IsLimit cX := isLimitPullbackConstCone a w hS b p' hs hpb
  have hYl : IsLimit cY := isLimitPullbackConstCone a (g ≫ w) hT (h ≫ b) e hsT hpbY
  have hh₀ (i : I) : h ≫ cX.π.app i = cY.π.app i ≫ hD.app i := by
    refine (hX i).hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, h₁' i]
      simp [cX, cY]
    · rw [Category.assoc, Category.assoc, h₂' i]
      simp [cX, cY, sq.w_assoc]
  have hpD (i : I) : QuasiCompact (pD.app i) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) (hX i) ‹_›
  have hpD' (i : I) : LocallyOfFiniteType (pD.app i) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) (hX i) ‹_›
  have (i : I) : IsLocallyNoetherian (S.obj i) := LocallyOfFiniteType.isLocallyNoetherian (w.app i)
  have (i : I) : CompactSpace (S.obj i) := QuasiCompact.compactSpace_of_compactSpace (w.app i)
  have (i : I) : IsLocallyNoetherian (XD.obj i) :=
    LocallyOfFiniteType.isLocallyNoetherian (pD.app i ≫ w.app i)
  have (i : I) : CompactSpace (XD.obj i) :=
    QuasiCompact.compactSpace_of_compactSpace (pD.app i ≫ w.app i)
  have {i j : I} (f : i ⟶ j) : IsAffineHom (XD.map f) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) (isPullback_pullback_const_map a w f).flip
      inferInstance
  have {i j : I} (f : i ⟶ j) : IsAffineHom (YD.map f) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (isPullback_pullback_const_map a (g ≫ w) f).flip inferInstance
  exact Etale.isIso_baseChangeHomologyMap_of_isLimit Λ pD g eD hD hsq hS hXl hT hYl
    (fun i ↦ (pullbackConstCone_π_app_snd _ _ _ _ _ _ _ i).symm) ht
    (fun i ↦ (pullbackConstCone_π_app_snd _ _ _ _ _ _ _ i).symm) hh₀ sq (g ≫ w) (t ≫ s) hsT G q
    fun i ↦ Etale.isIso_baseChangeHomologyMap_of_field Λ (w.app i) a (g.app i) (pD.app i)
      ((pullback.fst a' w).app i) (hX i).flip (eD.app i) (hD.app i) (hsq i) n hn hΛ q _

/-- Blueprint `lem-kun-0f1i-normal` (general form): base change for `X ×_K S' ⟶ S'` along a
morphism of affine schemes.

Let `K` be a field, `n` an integer invertible in `K` and killing `Λ`, `X` a scheme of finite type
over `K`, `S'` an affine `K`-scheme, `X' = X ×_K S'`, `t : T ⟶ S'` a morphism from an affine
scheme and `Y = X' ×_{S'} T`. Then the exchange morphism `p'⁻¹ R^q t_* F ⟶ R^q h_* e⁻¹ F` is an
isomorphism for every sheaf `F` on `T_ét` pulled back from `Spec K`, in every degree `q`.

Write `Γ(S')` and `Γ(T)` as the directed unions of their finite type `K`-subalgebras `B₀ ⊆ C`
(with `t^♯(B₀) ⊆ C`), so that `t` is the limit of the morphisms `Spec C ⟶ Spec B₀` of schemes of
finite type over `K` (`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isLimit_of_field`).
-/
theorem Etale.isIso_baseChangeHomologyMap_of_field_of_isAffine {K : Type u} [Field K]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a]
    (n : ℕ) (hn : IsUnit (n : K)) (hΛ : (n : Λ) = 0)
    {S' X' : Scheme.{u}} (s : S' ⟶ Spec (.of K)) (b : X' ⟶ X) (p' : X' ⟶ S')
    (hpb : IsPullback b p' a s) [IsAffine S'] {T Y : Scheme.{u}} [IsAffine T] (t : T ⟶ S')
    {e : Y ⟶ T} {h : Y ⟶ X'} (sq : IsPullback e h t p') (q : ℤ)
    (G : Sheaf (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (Etale.baseChangeHomologyMap Λ sq q (((t ≫ s)^*[ModuleCat.{u + 1} Λ]).obj G)) := by
  classical
  letI : Algebra K Γ(S', ⊤) := (s.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  letI : Algebra K Γ(T, ⊤) := (t.appTop.hom.comp (algebraMap K Γ(S', ⊤))).toAlgebra
  let φ : Γ(S', ⊤) →ₐ[K] Γ(T, ⊤) := { t.appTop.hom with commutes' := fun _ ↦ rfl }
  let FB : (Finset Γ(S', ⊤) × Finset Γ(T, ⊤)) →o Subalgebra K Γ(S', ⊤) :=
    ⟨fun i ↦ Algebra.adjoin K ↑i.1, fun i j hij ↦ Algebra.adjoin_mono (Finset.coe_subset.2 hij.1)⟩
  let FC : (Finset Γ(S', ⊤) × Finset Γ(T, ⊤)) →o Subalgebra K Γ(T, ⊤) :=
    ⟨fun i ↦ Algebra.adjoin K (↑i.2 ∪ φ '' ↑i.1), fun i j hij ↦ Algebra.adjoin_mono
      (Set.union_subset_union (Finset.coe_subset.2 hij.2)
        (Set.image_mono (Finset.coe_subset.2 hij.1)))⟩
  have hφ (i : Finset Γ(S', ⊤) × Finset Γ(T, ⊤)) (x : FB i) : φ x ∈ FC i := by
    have hx : φ x ∈ (FB i).map φ := Subalgebra.mem_map.2 ⟨x, x.2, rfl⟩
    rw [AlgHom.map_adjoin] at hx
    exact Algebra.adjoin_mono Set.subset_union_right hx
  let ψ : Subalgebra.diagramOfMonotone FB ⟶ Subalgebra.diagramOfMonotone FC :=
    { app i := CommRingCat.ofHom ((φ.comp (FB i).val).codRestrict (FC i) (hφ i)).toRingHom }
  let S := (Subalgebra.diagramOfMonotone FB).op ⋙ Scheme.Spec
  let TD := (Subalgebra.diagramOfMonotone FC).op ⋙ Scheme.Spec
  let g : TD ⟶ S := Functor.whiskerRight (NatTrans.op ψ) Scheme.Spec
  let w : S ⟶ (Functor.const _).obj (Spec (.of K)) :=
    { app i := Spec.map (CommRingCat.ofHom (algebraMap K (FB i.unop)))
      naturality i j f := by
        dsimp [S]
        rw [Category.comp_id, ← Spec.map_comp]
        rfl }
  let cS : Cone S :=
    { pt := S'
      π := { app i := S'.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (FB i.unop).val.toRingHom)
             naturality i j f := by
               dsimp [S]
               rw [Category.id_comp, Category.assoc, ← Spec.map_comp]
               rfl } }
  let cT : Cone TD :=
    { pt := T
      π := { app i := T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (FC i.unop).val.toRingHom)
             naturality i j f := by
               dsimp [TD]
               rw [Category.id_comp, Category.assoc, ← Spec.map_comp]
               rfl } }
  have hS : IsLimit cS :=
    (isLimitOfPreserves Scheme.Spec (Subalgebra.isColimitCoconeOfMonotone FB
      fun x ↦ ⟨({x}, ∅), Algebra.subset_adjoin (by simp)⟩).op).ofIsoLimit
      (Cones.ext S'.isoSpec.symm fun i ↦ by simp [cS])
  have hT : IsLimit cT :=
    (isLimitOfPreserves Scheme.Spec (Subalgebra.isColimitCoconeOfMonotone FC
      fun x ↦ ⟨(∅, {x}), Algebra.subset_adjoin (by simp)⟩).op).ofIsoLimit
      (Cones.ext T.isoSpec.symm fun i ↦ by simp [cT])
  have hsK : S'.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(S', ⊤))) = s := by
    have : CommRingCat.ofHom (algebraMap K Γ(S', ⊤)) =
        (Scheme.ΓSpecIso (.of K)).inv ≫ s.appTop := rfl
    rw [this, Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
      Category.comp_id]
  have hs (i) : cS.π.app i ≫ w.app i = s := by
    rw [← hsK]
    dsimp [cS, w]
    rw [Category.assoc, ← Spec.map_comp]
    rfl
  have ht (i) : t ≫ cS.π.app i = cT.π.app i ≫ g.app i := by
    dsimp [cS, cT, g]
    rw [Scheme.toSpecΓ_naturality_assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  have hfinB (i : Finset Γ(S', ⊤) × Finset Γ(T, ⊤)) : Algebra.FiniteType K (FB i) :=
    (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_adjoin_finset _)
  have hfinC (i : Finset Γ(S', ⊤) × Finset Γ(T, ⊤)) : Algebra.FiniteType K (FC i) :=
    (Subalgebra.fg_iff_finiteType _).1 ⟨i.2 ∪ i.1.image φ, by simp [FC]⟩
  have (i) : LocallyOfFiniteType (w.app i) :=
    HasRingHomProperty.Spec_iff.2 (RingHom.finiteType_algebraMap.2 (hfinB i.unop))
  have (i) : QuasiCompact (w.app i) := inferInstanceAs (QuasiCompact (Spec.map _))
  have (i) : IsSeparated (g.app i) := inferInstanceAs (IsSeparated (Spec.map _))
  have (i) : QuasiCompact (g.app i) := inferInstanceAs (QuasiCompact (Spec.map _))
  have (i) : LocallyOfFiniteType (g.app i) :=
    HasRingHomProperty.Spec_iff.2 (RingHom.FiniteType.of_comp_finiteType
      (f := algebraMap K (FB i.unop)) (RingHom.finiteType_algebraMap.2 (hfinC i.unop)))
  have {i j} (f : i ⟶ j) : IsAffineHom (S.map f) := inferInstanceAs (IsAffineHom (Spec.map _))
  have {i j} (f : i ⟶ j) : IsAffineHom (TD.map f) := inferInstanceAs (IsAffineHom (Spec.map _))
  exact Etale.isIso_baseChangeHomologyMap_of_isLimit_of_field Λ a n hn hΛ g w hS hT s hs t ht
    b p' hpb sq q G


/-- Blueprint `lem-kun-0f1i-normal`: the normal integral case.

Let `K` be a field, `n` an integer invertible in `K` and killing `Λ`, and `X` a scheme of finite
type over `K`. Let `X' = X ×_K S'` be the base change of `X` to an affine integral scheme `S'`
with algebraically closed function field, let `L` be an algebraically closed extension of that
function field, and let `h : Y ⟶ X'` be the fibre of `X' ⟶ S'` over the resulting geometric
generic point `Spec L ⟶ S'`. Then `R^q h_* (Λ/dΛ) = 0` for all `q ≥ 1` and `d ∣ n`.

The blueprint takes `L` to be the function field itself; the general algebraically closed
extension is what `AlgebraicGeometry.Etale.exists_isPullback_not_isZero_higherDirectImage`
produces. -/
theorem Etale.isZero_higherDirectImage_constantModSheaf_of_isAlgClosed {K : Type u} [Field K]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a]
    (n : ℕ) (hn : IsUnit (n : K)) (hΛ : (n : Λ) = 0)
    {S' X' : Scheme.{u}} (s : S' ⟶ Spec (.of K)) (b : X' ⟶ X) (p' : X' ⟶ S')
    (hpb : IsPullback b p' a s) [IsAffine S'] [IsIntegral S']
    (hnorm : ∀ x : S', IsIntegrallyClosed (S'.presheaf.stalk x))
    [IsAlgClosed S'.functionField] {L : Type u} [Field L] [IsAlgClosed L]
    (i : S'.functionField ⟶ CommRingCat.of L) {Y : Scheme.{u}} (e : Y ⟶ Spec (.of L))
    (h : Y ⟶ X') (sq : IsPullback e h (Spec.map i ≫ S'.fromSpecStalk (genericPoint S')) p')
    (d : ℕ) (hd : d ∣ n) (q : ℤ) (hq : 1 ≤ q) :
    IsZero (Etale.higherDirectImage Λ h q (Etale.constantModSheaf Λ Y d)) := by
  let t := Spec.map i ≫ S'.fromSpecStalk (genericPoint S')
  let M := ModuleCat.of Λ (Λ ⧸ (Ideal.span {(d : Λ)} : Ideal Λ))
  let F := ((t ≫ s)^*[ModuleCat.{u + 1} Λ]).obj (Etale.constantModSheaf Λ (Spec (.of K)) d)
  have := Etale.isIso_baseChangeHomologyMap_of_field_of_isAffine Λ a n hn hΛ s b p' hpb t sq q
    (Etale.constantModSheaf Λ (Spec (.of K)) d)
  have hsrc : IsZero ((Etale.baseChangeSourceFunctor Λ p' t q).obj F) :=
    IsZero.of_iso (((p')^*[ModuleCat.{u + 1} Λ]).map_isZero
      (Etale.isZero_higherDirectImage_of_isSepClosed Λ t F (by omega)))
      ((Etale.baseChangeSourceFunctorIso Λ p' t q).app F)
  have htgt : IsZero ((Etale.baseChangeTargetFunctor Λ e h q).obj F) :=
    hsrc.of_iso (asIso (Etale.baseChangeHomologyMap Λ sq q F)).symm
  let E : Etale.constantModSheaf Λ Y d ≅ ((e)^*[ModuleCat.{u + 1} Λ]).obj F :=
    ((Etale.constantSheafCompUpperStarIso Λ e).app M).symm ≪≫
      ((e)^*[ModuleCat.{u + 1} Λ]).mapIso ((Etale.constantSheafCompUpperStarIso Λ (t ≫ s)).app M).symm
  exact htgt.of_iso ((DerivedCategory.Plus.singleFunctor _ 0 ⋙ R+((h)_*[ModuleCat.{u + 1} Λ]) ⋙
    DerivedCategory.Plus.homologyFunctor _ q).mapIso E ≪≫
      ((Etale.baseChangeTargetFunctorIso Λ e h q).app F).symm)

end AlgebraicGeometry
