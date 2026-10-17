/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import WeilConjectures.AlgebraicGeometry.HypercoverResolutionLocal
public import WeilConjectures.AlgebraicGeometry.HypercoverHomotopyInvariance
public import WeilConjectures.AlgebraicGeometry.SplitEtaleHypercoverFreeComplex

/-!
# Verdier's hypercovering theorem for finite split étale hypercovers

For a sheaf `F` with injective resolution `F ⟶ L^•`, the cohomology `H^q(C(U, F))` of a finite
split étale hypercover `U` maps to `H^q(Γ(X, L)) = R^qΓ(F)` through the total complex
`Tot(U, L)` (`AlgebraicGeometry.FiniteSplitEtaleHypercover.cohomologyMap`). These maps are
natural in `F` and compatible with refinements; every class of `R^qΓ(F)` comes from some `U`,
and a class of `H^q(C(U, F))` mapping to zero dies on a refinement of `U`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

open SplitEtaleHypercover

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
  {A : Type (u + 2)} [Category.{u + 1} A] [Abelian A]
  {FA : A → A → Type*} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [∀ X, AddCommGroup (CA X)] [∀ X Y, AddMonoidHomClass (FA X Y) (CA X) (CA Y)]
  (hA : ElementwiseAbelian A)
  [HasSheafify X.smallEtaleTopology A] [X.smallEtaleTopology.WEqualsLocallyBijective A]
  [X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  [ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization A]

section Resolution

variable {F : Sheaf X.smallEtaleTopology A} (I : InjectiveResolution F)

/-- The coaugmentation `F ⟶ L^0` of an injective resolution. -/
noncomputable abbrev resι : F ⟶ I.cocomplex.X 0 := I.ι.f 0

lemma resι_d : resι I ≫ I.cocomplex.d 0 1 = 0 := I.ι_f_zero_comp_complex_d

include hA in
lemma resι_glob (T : X.Etale) (s : ToType ((I.cocomplex.X 0).obj.obj (op T)))
    (hs : (I.cocomplex.d 0 1).hom.app (op T) s = 0) :
    ∃ w, (resι I).hom.app (op T) w = s :=
  exists_kernel_elem hA (w := I.ι_f_zero_comp_complex_d) I.isLimitKernelFork T s hs

include hA in
lemma resι_inj (T : X.Etale) : Function.Injective ((resι I).hom.app (op T)) := by
  have : Mono (resι I) := Fork.IsLimit.mono I.isLimitKernelFork
  have : Mono (resι I).hom := (sheafToPresheaf X.smallEtaleTopology A).map_mono (resι I)
  have : Mono ((resι I).hom.app (op T)) := (NatTrans.mono_iff_mono_app _).1 this _
  exact hA.injective_of_mono _

end Resolution

/-- Global sections over the final object. -/
noncomputable abbrev Γ' : Sheaf X.smallEtaleTopology A ⥤ A :=
  (sheafSections X.smallEtaleTopology A).obj (op (⊤_ X.Etale))

instance : (Γ' (X := X) (A := A)).Additive where
  map_add := rfl

section Main

variable (Free : Type (u + 1) ⥤ A) (adj : Free ⊣ CategoryTheory.forget A)
  (hfin : ∀ (S : Type (u + 1)) (x : ToType (Free.obj S)), ∃ F : Set S, F.Finite ∧
    x ∈ Set.range (Free.map (↾(Subtype.val : F → S))))
  [(presheafToSheaf X.smallEtaleTopology A).PreservesHomology]
  [(CategoryTheory.forget A).PreservesMonomorphisms]

include hA adj hfin

lemma rows_of_injective (U : SplitEtaleHypercover X)
    (L : CochainComplex (Sheaf X.smallEtaleTopology A) ℕ)
    [∀ r, Injective (L.X r)] :
    (∀ r, Function.Injective (U.resTop (L.X r) 0)) ∧
      (∀ r (s : ToType (U.dObj L 0 r)), U.dHor L 0 r s = 0 →
        ∃ t, U.resTop (L.X r) 0 t = s) ∧
      (∀ p r (s : ToType (U.dObj L (p + 1) r)), U.dHor L (p + 1) r s = 0 →
        ∃ t, U.dHor L p r t = s) := by
  have H := fun r ↦ U.injective_section_cohomology Free hA.sub_apply hfin adj hA.exact_of_elem
    (L.X r)
  refine ⟨fun r ↦ (H r).1, fun r s hs ↦ ((H r).2.1 s).1 hs, fun p r s hs ↦ ?_⟩
  have hz := (H r).2.2 (p + 1) (Nat.succ_pos p)
  have hex := (HomologicalComplex.exactAt_iff_isZero_homology _ _).2 hz
  rw [HomologicalComplex.exactAt_iff' _ p (p + 1) (p + 2) (by simp) (by simp)] at hex
  exact hA.elem_of_exact _ hex s hs

/-- For a complex of injective sheaves `L`, the augmentation `Γ(X, L) ⟶ Tot(U, L)` is an
isomorphism on cohomology. -/
noncomputable def augIso (U : SplitEtaleHypercover X)
    (L : CochainComplex (Sheaf X.smallEtaleTopology A) ℕ) [∀ r, Injective (L.X r)] (n : ℕ) :
    (gammaComplex L).homology n ≅ (U.totComplex L).homology n :=
  have h := rows_of_injective hA Free adj hfin U L
  have := U.isIso_homologyMap_totAug L hA h.1 h.2.1 h.2.2 n
  asIso (HomologicalComplex.homologyMap (U.totAug L) n)

lemma augIso_hom (U : SplitEtaleHypercover X)
    (L : CochainComplex (Sheaf X.smallEtaleTopology A) ℕ) [∀ r, Injective (L.X r)] (n : ℕ) :
    (augIso hA Free adj hfin U L n).hom = HomologicalComplex.homologyMap (U.totAug L) n := rfl

lemma augIso_inv_naturality (U : SplitEtaleHypercover X)
    {L L' : CochainComplex (Sheaf X.smallEtaleTopology A) ℕ} [∀ r, Injective (L.X r)]
    [∀ r, Injective (L'.X r)] (φ : L ⟶ L') (n : ℕ) :
    (augIso hA Free adj hfin U L n).inv ≫
        HomologicalComplex.homologyMap ((Γ' (X := X) (A := A)).mapHomologicalComplex _ |>.map φ) n =
      HomologicalComplex.homologyMap (U.totMapL φ) n ≫ (augIso hA Free adj hfin U L' n).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, augIso_hom, augIso_hom,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    totAug_totMapL]

lemma augIso_inv_totMap {U V : SplitEtaleHypercover X} (f : U.simplicial ⟶ V.simplicial)
    (L : CochainComplex (Sheaf X.smallEtaleTopology A) ℕ) [∀ r, Injective (L.X r)] (n : ℕ) :
    HomologicalComplex.homologyMap (totMap L f) n ≫ (augIso hA Free adj hfin U L n).inv =
      (augIso hA Free adj hfin V L n).inv := by
  rw [Iso.comp_inv_eq, Iso.eq_inv_comp, augIso_hom, augIso_hom,
    ← HomologicalComplex.homologyMap_comp, totAug_totMap]

variable [HasInjectiveResolutions (Sheaf X.smallEtaleTopology A)] (q : ℕ)

/-- The comparison map `H^q(C(U, F)) ⟶ R^qΓ(F)`. -/
noncomputable def cmap (U : FiniteSplitEtaleHypercover X) (F : Sheaf X.smallEtaleTopology A) :
    (cohomologyFunctor A U q).obj F ⟶ ((Γ' (X := X) (A := A)).rightDerived q).obj F :=
  HomologicalComplex.homologyMap
      (U.toSplitEtaleHypercover.totRow (resι (injectiveResolution F))
        (resι_d (injectiveResolution F))) q ≫
    (augIso hA Free adj hfin U.toSplitEtaleHypercover (injectiveResolution F).cocomplex q).inv ≫
      ((injectiveResolution F).isoRightDerivedObj Γ' q).inv

lemma cmap_naturality_aux (U : SplitEtaleHypercover X) {F G : Sheaf X.smallEtaleTopology A}
    (g : F ⟶ G) (I : InjectiveResolution F) (J : InjectiveResolution G)
    (φ : I.cocomplex ⟶ J.cocomplex) (hφ : I.ι.f 0 ≫ φ.f 0 = g ≫ J.ι.f 0) :
    HomologicalComplex.homologyMap ((AlgebraicTopology.alternatingCofaceMapComplex A).map
        (Functor.whiskerLeft U.simplicial.rightOp g.hom)) q ≫
      HomologicalComplex.homologyMap (U.totRow (resι J) (resι_d J)) q ≫
        (augIso hA Free adj hfin U J.cocomplex q).inv =
      HomologicalComplex.homologyMap (U.totRow (resι I) (resι_d I)) q ≫
        (augIso hA Free adj hfin U I.cocomplex q).inv ≫
          HomologicalComplex.homologyMap
            ((Γ' (X := X) (A := A)).mapHomologicalComplex _ |>.map φ) q := by
  rw [augIso_inv_naturality, ← Category.assoc, ← Category.assoc,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    totRow_totMapL _ φ (resι I) (resι_d I) (resι J) (resι_d J) g hφ]

/-- The comparison maps as a natural transformation. -/
noncomputable def cnat (U : FiniteSplitEtaleHypercover X) :
    cohomologyFunctor A U q ⟶ (Γ' (X := X) (A := A)).rightDerived q where
  app F := cmap hA Free adj hfin q U F
  naturality F G g := by
    let I := injectiveResolution F
    let J := injectiveResolution G
    let φ := InjectiveResolution.desc g J I
    have hφ : I.ι.f 0 ≫ φ.f 0 = g ≫ J.ι.f 0 := by
      have := congrArg (fun ψ ↦ ψ.f 0) (InjectiveResolution.desc_commutes g J I)
      simp only [HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero] at this
      exact this
    have key : (cohomologyFunctor A U q).map g ≫
        HomologicalComplex.homologyMap (U.toSplitEtaleHypercover.totRow (resι J) (resι_d J)) q ≫
          (augIso hA Free adj hfin U.toSplitEtaleHypercover J.cocomplex q).inv =
        HomologicalComplex.homologyMap (U.toSplitEtaleHypercover.totRow (resι I) (resι_d I)) q ≫
          (augIso hA Free adj hfin U.toSplitEtaleHypercover I.cocomplex q).inv ≫
            ((Γ' (X := X) (A := A)).mapHomologicalComplex _ ⋙
              HomologicalComplex.homologyFunctor _ _ q).map φ :=
      cmap_naturality_aux hA Free adj hfin q U.toSplitEtaleHypercover g I J φ hφ
    dsimp only [cmap]
    rw [Category.assoc, Category.assoc,
      InjectiveResolution.isoRightDerivedObj_inv_naturality g I J φ hφ]
    simp only [← Category.assoc] at key ⊢
    rw [key]

lemma cmap_refinement_aux {U V : SplitEtaleHypercover X} (f : U.simplicial ⟶ V.simplicial)
    {F : Sheaf X.smallEtaleTopology A} (I : InjectiveResolution F) :
    HomologicalComplex.homologyMap (secMap f F) q ≫
      HomologicalComplex.homologyMap (U.totRow (resι I) (resι_d I)) q ≫
        (augIso hA Free adj hfin U I.cocomplex q).inv =
      HomologicalComplex.homologyMap (V.totRow (resι I) (resι_d I)) q ≫
        (augIso hA Free adj hfin V I.cocomplex q).inv := by
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp, ← totRow_totMap,
    HomologicalComplex.homologyMap_comp, Category.assoc, augIso_inv_totMap]

lemma cnat_refinement {U V : FiniteSplitEtaleHypercover X} (f : U.Refinement V) :
    cohomologyRefinement A f q ≫ cnat hA Free adj hfin q U = cnat hA Free adj hfin q V := by
  refine NatTrans.ext (funext fun F ↦ ?_)
  have key := cmap_refinement_aux hA Free adj hfin q (U := U.toSplitEtaleHypercover)
    (V := V.toSplitEtaleHypercover) f (injectiveResolution F)
  change HomologicalComplex.homologyMap (secMap f F) q ≫ cmap hA Free adj hfin q U F =
    cmap hA Free adj hfin q V F
  dsimp only [cmap]
  simp only [← Category.assoc] at key ⊢
  rw [key]

omit [HasSheafify X.smallEtaleTopology A] [X.smallEtaleTopology.WEqualsLocallyBijective A]
  [X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  [ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization A]
  [(presheafToSheaf X.smallEtaleTopology A).PreservesHomology]
  [(CategoryTheory.forget A).PreservesMonomorphisms]
  [HasInjectiveResolutions (Sheaf X.smallEtaleTopology A)] adj hfin in
lemma iso_inv_hom_apply {Y Z : A} (e : Y ≅ Z) (y : ToType Y) : e.inv (e.hom y) = y := by
  rw [← ConcreteCategory.comp_apply, e.hom_inv_id, ConcreteCategory.id_apply]

/-- Every class of `R^qΓ(F)` comes from the cohomology of some finite split hypercover. -/
lemma cmap_surjective (F : Sheaf X.smallEtaleTopology A)
    (y : ToType (((Γ' (X := X) (A := A)).rightDerived q).obj F)) :
    ∃ (U : FiniteSplitEtaleHypercover X) (x : ToType ((cohomologyFunctor A U q).obj F)),
      cmap hA Free adj hfin q U F x = y := by
  let I := injectiveResolution F
  obtain ⟨U₀⟩ := FiniteSplitEtaleHypercover.nonempty X
  let y₀ := (I.isoRightDerivedObj Γ' q).hom y
  let y₁ := (augIso hA Free adj hfin U₀.toSplitEtaleHypercover I.cocomplex q).hom y₀
  obtain ⟨t, ht⟩ := HomologicalComplex.exists_isCls hA (U₀.totComplex I.cocomplex) q y₁
  have hdt : U₀.totD I.cocomplex q t = 0 := by
    have := HomologicalComplex.IsCls.d_eq_zero hA _ (q + 1) ht
    rwa [totComplex_d] at this
  suffices H : ∃ (V : FiniteSplitEtaleHypercover X) (x : ToType ((cohomologyFunctor A V q).obj F)),
      (augIso hA Free adj hfin V.toSplitEtaleHypercover I.cocomplex q).inv
        (HomologicalComplex.homologyMap
          (V.toSplitEtaleHypercover.totRow (resι I) (resι_d I)) q x) = y₀ by
    obtain ⟨V, x, hx⟩ := H
    refine ⟨V, x, ?_⟩
    simp only [cmap, ConcreteCategory.comp_apply]
    erw [hx]
    exact iso_inv_hom_apply hA _ y
  cases q with
  | zero =>
    obtain ⟨w, hw0, hwt⟩ := exists_totRow_eq_zero I.cocomplex hA (resι I) (resι_d I)
      (resι_glob hA I) (resι_inj hA I) U₀.toSplitEtaleHypercover t hdt
    obtain ⟨x, hx⟩ := HomologicalComplex.exists_isCls_of_d_eq_zero hA
      (U₀.toSplitEtaleHypercover.secComplex F) 0 1 (by simp) w hw0
    refine ⟨U₀, x, ?_⟩
    have hm := HomologicalComplex.IsCls.map _
      (U₀.toSplitEtaleHypercover.totRow (resι I) (resι_d I)) hx
    rw [hwt] at hm
    rw [(HomologicalComplex.IsCls.eq_iff hA _ 0 0 (by simp) hm ht).2
      ⟨0, by rw [map_zero, sub_self]⟩]
    exact iso_inv_hom_apply hA _ y₀
  | succ m =>
    obtain ⟨V, f, w, y', hw0, hwt⟩ := exists_refinement_totRow_eq I.cocomplex hA (resι I)
      (resι_d I) (resι_glob hA I) (resι_inj hA I)
      (locallyExactPos_of_injectiveResolution hA I) U₀ m t hdt
    obtain ⟨x, hx⟩ := HomologicalComplex.exists_isCls_of_d_eq_zero hA
      (V.toSplitEtaleHypercover.secComplex F) (m + 1) (m + 2) (by simp) w hw0
    refine ⟨V, x, ?_⟩
    have hm := HomologicalComplex.IsCls.map _
      (V.toSplitEtaleHypercover.totRow (resι I) (resι_d I)) hx
    have ht' := HomologicalComplex.IsCls.map _ (totMap I.cocomplex f) ht
    rw [(HomologicalComplex.IsCls.eq_iff hA _ m (m + 1) (by simp) hm ht').2
      ⟨-y', by
        rw [map_neg, hwt, totComplex_d, totMap_f]
        exact (sub_sub_cancel_left _ _).symm⟩]
    rw [← ConcreteCategory.comp_apply, augIso_inv_totMap]
    exact iso_inv_hom_apply hA _ y₀

/-- A class of `H^q(C(U, F))` mapping to zero in `R^qΓ(F)` dies on a refinement of `U`. -/
lemma cmap_injective (U : FiniteSplitEtaleHypercover X) (F : Sheaf X.smallEtaleTopology A)
    (x : ToType ((cohomologyFunctor A U q).obj F)) (hx : cmap hA Free adj hfin q U F x = 0) :
    ∃ (V : FiniteSplitEtaleHypercover X) (f : V.Refinement U),
      (cohomologyRefinement A f q).app F x = 0 := by
  let I := injectiveResolution F
  have hβ : HomologicalComplex.homologyMap
      (U.toSplitEtaleHypercover.totRow (resι I) (resι_d I)) q x = 0 := by
    have h1 := congrArg (I.isoRightDerivedObj Γ' q).hom hx
    simp only [cmap, ConcreteCategory.comp_apply, map_zero] at h1
    erw [← ConcreteCategory.comp_apply ((I.isoRightDerivedObj Γ' q).inv),
      Iso.inv_hom_id, ConcreteCategory.id_apply] at h1
    have h2 := congrArg (augIso hA Free adj hfin U.toSplitEtaleHypercover I.cocomplex q).hom h1
    rwa [map_zero, ← ConcreteCategory.comp_apply, Iso.inv_hom_id,
      ConcreteCategory.id_apply] at h2
  obtain ⟨w, hw⟩ := HomologicalComplex.exists_isCls hA (U.toSplitEtaleHypercover.secComplex F) q x
  have hm := HomologicalComplex.IsCls.map _
    (U.toSplitEtaleHypercover.totRow (resι I) (resι_d I)) hw
  rw [hβ] at hm
  cases q with
  | zero =>
    obtain ⟨y, hy⟩ := (HomologicalComplex.IsCls.eq_zero_iff hA _ 0 0 (by simp) hm).1 rfl
    rw [HomologicalComplex.shape _ _ _ (by simp), hA.zero_apply] at hy
    have hw0 := eq_zero_of_totRow_eq_zero I.cocomplex hA (resι I) (resι_d I) (resι_glob hA I)
      (resι_inj hA I) U.toSplitEtaleHypercover w hy.symm
    subst hw0
    have hx0 : x = 0 := (HomologicalComplex.IsCls.eq_zero_iff hA _ 0 0 (by simp) hw).2
      ⟨0, by rw [map_zero]⟩
    exact ⟨U, 𝟙 _, by rw [hx0, map_zero]⟩
  | succ m =>
    obtain ⟨y, hy⟩ := (HomologicalComplex.IsCls.eq_zero_iff hA _ m (m + 1) (by simp) hm).1 rfl
    rw [totComplex_d] at hy
    obtain ⟨V, f, v, hv⟩ := exists_refinement_secComplex_d_eq I.cocomplex hA (resι I) (resι_d I)
      (resι_glob hA I) (resι_inj hA I) (locallyExactPos_of_injectiveResolution hA I) U m w y hy
    refine ⟨V, f, ?_⟩
    have hm' := HomologicalComplex.IsCls.map _ (secMap f F) hw
    exact (HomologicalComplex.IsCls.eq_zero_iff hA _ m (m + 1) (by simp) hm').2 ⟨v, hv⟩

end Main

end AlgebraicGeometry.FiniteSplitEtaleHypercover
