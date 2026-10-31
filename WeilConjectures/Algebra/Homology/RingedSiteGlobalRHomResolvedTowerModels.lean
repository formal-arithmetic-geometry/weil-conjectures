/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RingedSiteGlobalRHomModel
import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorHomEquiv
import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Limits.Yoneda


/-! Models used in the global derived Hom and inverse-limit comparison. -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe c v r a w z u b

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.RingedSiteGlobalRHom

private theorem injective_tower_transition_split
    {A : Type*} [Category A] [Abelian A]
    (T : ℕᵒᵖ ⥤ A) [Injective T]
    (n : ℕ) : IsSplitEpi (T.map (homOfLE (Nat.le_succ n)).op) := by
  classical
  let k := (homOfLE (Nat.le_succ n)).op
  let M := T.obj (op n)
  let L := (evaluationLeftAdjoint A (op n)).obj M
  let L' := (evaluationLeftAdjoint A (op (n + 1))).obj M
  let i : L ⟶ L' :=
    { app := fun m ↦ Sigma.desc fun g ↦ Sigma.ι (fun _ ↦ M) (k ≫ g)
      naturality := by
        intro x y f
        apply Sigma.hom_ext
        intro g
        simp [L, L', evaluationLeftAdjoint, Category.assoc] }
  have (m : ℕᵒᵖ) : Mono (i.app m) := by
    let r : L'.obj m ⟶ L.obj m := Sigma.desc fun _ ↦
      if h : Nonempty (op n ⟶ m) then Sigma.ι (fun _ ↦ M) h.some else 0
    have hr : i.app m ≫ r = 𝟙 _ := by
      apply Sigma.hom_ext
      intro g
      simp only [i, r, colimit.ι_desc_assoc, Cofan.mk_ι_app,
        dif_pos (show Nonempty (op n ⟶ m) from ⟨g⟩), colimit.ι_desc]
      exact (congrArg (Sigma.ι (fun _ : op n ⟶ m ↦ M))
        (Subsingleton.elim _ g)).trans (Category.comp_id _).symm
    exact (IsSplitMono.mk' ⟨r, hr⟩).mono
  have : Mono i := NatTrans.mono_of_mono_app i
  let a : L ⟶ T :=
    { app := fun m ↦ Sigma.desc fun g ↦ T.map g
      naturality := by
        intro x y f
        apply Sigma.hom_ext
        intro g
        simp [L, evaluationLeftAdjoint, Functor.map_comp] }
  let b := Injective.factorThru a i
  have hb : i ≫ b = a := Injective.comp_factorThru a i
  refine IsSplitEpi.mk' ⟨Sigma.ι (fun _ ↦ M) (𝟙 (op (n + 1))) ≫
    b.app (op (n + 1)), ?_⟩
  rw [Category.assoc, ← b.naturality k, ← Category.assoc]
  have hn := congrArg (fun f : L ⟶ T ↦
    Sigma.ι (fun _ ↦ M) (𝟙 (op n)) ≫ f.app (op n)) hb
  simpa [L', evaluationLeftAdjoint, i, a] using hn


private theorem fan_shift_splitEpi
    {A : Type u} [Category.{v} A] [Preadditive A]
    (K : ℕ → A) (P : Fan K) (hP : IsLimit P) (q : ∀ n, K (n + 1) ⟶ K n)
    [∀ n, IsSplitEpi (q n)] (t : P.pt ⟶ P.pt)
    (ht : ∀ n, t ≫ P.proj n = P.proj n - P.proj (n + 1) ≫ q n) : IsSplitEpi t := by
  let a : ∀ n : ℕ, P.pt ⟶ K n := fun n ↦ Nat.rec 0
    (fun n a ↦ (a - P.proj n) ≫ section_ (q n)) n
  have ha (n : ℕ) : a (n + 1) ≫ q n = a n - P.proj n := by
    change ((a n - P.proj n) ≫ section_ (q n)) ≫ q n = _
    rw [Category.assoc, IsSplitEpi.id, Category.comp_id]
  let r := hP.lift (Fan.mk P.pt a)
  have hr (n) : r ≫ P.proj n = a n := hP.fac _ ⟨n⟩
  refine IsSplitEpi.mk' ⟨r, ?_⟩
  apply Fan.IsLimit.hom_ext hP
  intro n
  rw [Category.assoc, ht, Preadditive.comp_sub, ← Category.assoc, hr, hr, ha]
  simp

private theorem split_tower_triangle
    {D : Type u} [Category.{b} D] [Abelian D] [HasDerivedCategory.{w} D]
    [HasCountableProducts D] [HasLimitsOfShape ℕᵒᵖ D]
    (T : ℕᵒᵖ ⥤ CochainComplex D ℤ)
    (hSplit : ∀ (i : ℤ) (n : ℕ), IsSplitEpi ((T.map (homOfLE n.le_succ).op).f i))
    (hQ : Nonempty (IsLimit (DerivedCategory.Q.{w}.mapCone
      (limit.cone (Discrete.functor (fun n : ℕ ↦ T.obj (op n))))))) :
    ∃ _hp : HasProduct (fun n : ℕ ↦ DerivedCategory.Q.{w}.obj (T.obj (op n))),
      ∃ (p : DerivedCategory.Q.{w}.obj (limit T) ⟶
          ∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.{w}.obj (T.obj (op n))))
        (δ : (∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.{w}.obj (T.obj (op n)))) ⟶
          (DerivedCategory.Q.{w}.obj (limit T))⟦(1 : ℤ)⟧),
        IsDerivedLimitTriangle
          (fun n : ℕ ↦ DerivedCategory.Q.{w}.map (T.map (homOfLE n.le_succ).op))
          (DerivedCategory.Q.{w}.obj (limit T)) p δ ∧
        ∀ n : ℕ, p ≫ Pi.π _ n = DerivedCategory.Q.{w}.map (limit.π T (op n)) := by
  classical
  let K := fun n : ℕ ↦ T.obj (op n)
  let B : Fan K := limit.cone (Discrete.functor K)
  let hB : IsLimit B := limit.isLimit _
  let s : B.pt ⟶ B.pt := towerProductShift (fun n ↦ T.map (homOfLE n.le_succ).op)
  have hs (n : ℕ) : s ≫ B.proj n =
      B.proj (n + 1) ≫ T.map (homOfLE n.le_succ).op := Pi.lift_π _ _
  let S := ShortComplex.mk _ _
    (Fan.IsLimit.lift_π_comp_one_sub_eq_zero hB s hs (limit.cone T))
  have hk := Fan.IsLimit.isLimitKernelForkOneSub hB s hs (limit.isLimit T)
  have hS : S.ShortExact := by
    have : Mono S.f := mono_of_isLimit_fork hk
    have : Epi S.g := HomologicalComplex.epi_of_epi_f _ fun i ↦ by
      rw [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f]
      have (n : ℕ) := hSplit i n
      exact (fan_shift_splitEpi (fun n ↦ (K n).X i) _
        (isLimitFanMkObjOfIsLimit (HomologicalComplex.eval _ _ i) K B.proj
          ((IsLimit.equivIsoLimit (Cone.ext (Iso.refl _))).1 hB))
        (fun n ↦ (T.map (homOfLE n.le_succ).op).f i) (𝟙 _ - s.f i)
        (fun n ↦ by
          change (𝟙 (B.pt.X i) - s.f i) ≫ (B.proj n).f i =
            (B.proj n).f i - (B.proj (n + 1)).f i ≫ _
          rw [Preadditive.sub_comp, Category.id_comp]
          exact congrArg (fun f ↦ (B.proj n).f i - f)
            ((HomologicalComplex.comp_f _ _ i).symm.trans
              ((congrArg (fun f ↦ f.f i) (hs n)).trans
                (HomologicalComplex.comp_f _ _ i))))).epi
    exact { exact := ShortComplex.exact_of_f_is_kernel _ hk }
  let hQFan := (Fan.isLimitMapConeEquiv DerivedCategory.Q K B) hQ.some
  let hp : HasProduct (fun n ↦ DerivedCategory.Q.{w}.obj (K n)) := ⟨⟨_, hQFan⟩⟩
  let := hp
  let K₀ := fun n ↦ DerivedCategory.Q.{w}.obj (K n)
  let f₀ := fun n : ℕ ↦ DerivedCategory.Q.{w}.map (T.map (homOfLE n.le_succ).op)
  let p : DerivedCategory.Q.{w}.obj (limit T) ⟶ ∏ᶜ K₀ :=
    Pi.lift (fun n ↦ DerivedCategory.Q.{w}.map (limit.π T (op n)))
  let E : DerivedCategory.Q.{w}.obj B.pt ≅ ∏ᶜ K₀ :=
    hQFan.conePointUniqueUpToIso (productIsProduct K₀)
  have hE (n : ℕ) : E.hom ≫ Pi.π K₀ n = DerivedCategory.Q.map (B.proj n) :=
    hQFan.conePointUniqueUpToIso_hom_comp (productIsProduct K₀) ⟨n⟩
  have hπ (n : ℕ) : p ≫ Pi.π K₀ n =
      DerivedCategory.Q.map (limit.π T (op n)) := Pi.lift_π _ _
  have hi : DerivedCategory.Q.map S.f ≫ E.hom = p := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, hE, ← Functor.map_comp, hπ]
    exact congrArg DerivedCategory.Q.map (hB.fac _ ⟨n⟩)
  have hu (n : ℕ) : S.g ≫ B.proj n = B.proj n -
      B.proj (n + 1) ≫ T.map (homOfLE n.le_succ).op := by
    change (𝟙 B.pt - s) ≫ B.proj n = _
    rw [Preadditive.sub_comp, Category.id_comp, hs]
  have htrans : DerivedCategory.Q.map S.g ≫ E.hom =
      E.hom ≫ towerTransitionEndomorphism f₀ := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, hE, ← Functor.map_comp, hu, Functor.map_sub]
    simp only [towerTransitionEndomorphism, towerProductShift, Preadditive.sub_comp,
      Category.id_comp, Preadditive.comp_sub, Pi.lift_π, hE, f₀]
    rw [Functor.map_comp, ← Category.assoc, hE]
  let δ := DerivedCategory.triangleOfSESδ hS
  refine ⟨hp, p, E.inv ≫ δ, ?_, hπ⟩
  exact (Pretriangulated.distinguished_iff_of_iso
    (Pretriangulated.Triangle.isoMk
      (Pretriangulated.Triangle.mk (DerivedCategory.Q.map S.f) (DerivedCategory.Q.map S.g) δ)
      (Pretriangulated.Triangle.mk p (towerTransitionEndomorphism f₀) (E.inv ≫ δ))
      (Iso.refl _) E E (by simpa using hi) htrans (by simp))).mp
    (DerivedCategory.triangleOfSES_distinguished hS)

private theorem preservesLimit_of_product_cones
    {D : Type*} [Category D] {E : Type*} [Category E]
    {S : Type*} [Category S] {ι : Type*}
    (G : D ⥤ E) (F : ι → D ⥤ E) (π : ∀ i, G ⟶ F i)
    (hG : ∀ X, IsLimit (Fan.mk (G.obj X) (fun i ↦ (π i).app X)))
    (T : S ⥤ D) [∀ i, PreservesLimit T (F i)] : PreservesLimit T G := by
  constructor
  intro c hc
  let hcF (i : ι) := isLimitOfPreserves (F i) hc
  let sc (s : Cone (T ⋙ G)) (i : ι) : Cone (T ⋙ F i) :=
    (Cone.postcompose (Functor.whiskerLeft T (π i))).obj s
  let l (s : Cone (T ⋙ G)) : s.pt ⟶ G.obj c.pt :=
    (hG c.pt).lift (Fan.mk s.pt (fun i ↦ (hcF i).lift (sc s i)))
  have hl (s : Cone (T ⋙ G)) (i : ι) :
      l s ≫ (π i).app c.pt = (hcF i).lift (sc s i) := (hG c.pt).fac _ ⟨i⟩
  refine ⟨{ lift := l, fac := ?_, uniq := ?_ }⟩
  · intro s j
    apply Fan.IsLimit.hom_ext (hG (T.obj j))
    intro i
    change (l s ≫ G.map (c.π.app j)) ≫ (π i).app (T.obj j) = _
    rw [Category.assoc, (π i).naturality, ← Category.assoc, hl]
    exact (hcF i).fac (sc s i) j
  · intro s m hm
    apply Fan.IsLimit.hom_ext (hG c.pt)
    intro i
    change m ≫ (π i).app c.pt = l s ≫ (π i).app c.pt
    rw [hl]
    apply (hcF i).uniq (sc s i)
    intro j
    change (m ≫ (π i).app c.pt) ≫ (F i).map (c.π.app j) = _
    have hmj : m ≫ G.map (c.π.app j) = s.π.app j := hm j
    rw [Category.assoc, ← (π i).naturality, ← Category.assoc, hmj]
    rfl

private theorem product_map_isSplitEpi
    {D : Type*} [Category D] {E : Type*} [Category E] {ι : Type*}
    (G : D ⥤ E) (F : ι → D ⥤ E) (π : ∀ i, G ⟶ F i)
    (hG : ∀ X, IsLimit (Fan.mk (G.obj X) (fun i ↦ (π i).app X)))
    {X Y : D} (f : X ⟶ Y) [∀ i, IsSplitEpi ((F i).map f)] :
    IsSplitEpi (G.map f) := by
  let r := (hG X).lift (Fan.mk (G.obj Y)
    (fun i ↦ (π i).app Y ≫ section_ ((F i).map f)))
  refine IsSplitEpi.mk' ⟨r, ?_⟩
  apply Fan.IsLimit.hom_ext (hG Y)
  intro i
  change (r ≫ G.map f) ≫ (π i).app Y = 𝟙 _ ≫ (π i).app Y
  have hr : r ≫ (π i).app X = (π i).app Y ≫ section_ ((F i).map f) :=
    (hG X).fac _ ⟨i⟩
  rw [Category.assoc, (π i).naturality, ← Category.assoc, hr]
  simp

private theorem linearCoyoneda_preserves_limits
    {D : Type u} [Category.{b} D] [Preadditive D]
    (S : Type r) [Ring S] [Linear S D] (M : D) :
    PreservesLimitsOfShape ℕᵒᵖ ((linearCoyoneda S D).obj (op M)) := by
  have : PreservesLimitsOfShape ℕᵒᵖ
      ((linearCoyoneda S D).obj (op M) ⋙ forget (ModuleCat.{b} S)) :=
    inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ (coyoneda.obj (op M)))
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (forget (ModuleCat.{b} S))

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max c v r})
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasDerivedCategory.{w} (Modules.{c, v, max c v r} R)]
  (A : Type a) [CommRing A] (φ : A →+* Scalars.{c, v, max c v r} R)
  [HasDerivedCategory.{z} (ModuleCat.{max c v r} A)]

private def hom_degree_projection
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    (R : Sheaf J CommRingCat.{r})
    (L : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (q p : ℤ) :
    (homComplexFunctor (R := R)).obj (op L) ⋙ HomologicalComplex.eval _ _ q ⟶
      HomologicalComplex.eval _ _ (p + q) ⋙
        (SheafOfModules.homFunctor R).obj (op (L.X p)) where
  app M := homComplexπ L M q p (p + q) rfl
  naturality {_X _Y} f := homComplexFunctor_obj_map_f_π f q p (p + q) rfl

omit [HasDerivedCategory.{w} (Modules.{c, v, max c v r} R)] in
private theorem hom_preserves_limits
    (M : Modules.{c, v, max c v r} R) :
    PreservesLimitsOfShape ℕᵒᵖ ((SheafOfModules.homFunctor R).obj (op M)) := by
  let adj : SheafOfModules.siteSheafTensorRight.{v, c, max c v r, max c v r} M ⊣
      (SheafOfModules.homFunctor R).obj (op M) := Adjunction.mkOfHomEquiv
    { homEquiv := fun P N ↦ SheafOfModules.SiteTensorHom.equiv.{c, v, max c v r, r} P M N
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        apply (SheafOfModules.SiteTensorHom.equiv.{c, v, max c v r, r} X' M Y).injective
        erw [Equiv.apply_symm_apply,
          SheafOfModules.SiteTensorHom.equiv_naturality.{c, v, max c v r, r},
          Equiv.apply_symm_apply]
      homEquiv_naturality_right := by
        intro X Y Y' f g
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.hom_ext
        intro U
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        apply PresheafOfModules.hom_ext
        intro W
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro y
        change (((SheafOfModules.SiteTensorHom.equiv.{c, v, max c v r, r}
            X M Y' (f ≫ g)).val.app U x).app W) y =
          g.val.app (op W.unop.left)
            ((((SheafOfModules.SiteTensorHom.equiv.{c, v, max c v r, r}
              X M Y f).val.app U x).app W) y)
        erw [SheafOfModules.SiteTensorHom.equiv_apply.{c, v, max c v r, r}
            X M Y' (f ≫ g) U x W.unop y] }
  exact adj.rightAdjoint_preservesLimits.preservesLimitsOfShape

omit [HasDerivedCategory.{w} (Modules.{c, v, max c v r} R)]
  [HasDerivedCategory.{z} (ModuleCat.{max c v r} A)] in
private theorem representative_preserves_limits
    (L : CochainComplex (Modules.{c, v, max c v r} R) ℤ) :
    PreservesLimitsOfShape ℕᵒᵖ (representative.{c, v, r, a} R A φ L) := by
  have (M : Modules.{c, v, max c v r} R) := hom_preserves_limits.{c, v, r} R M
  have : PreservesLimitsOfShape ℕᵒᵖ ((homComplexFunctor (R := R)).obj (op L)) := by
    apply HomologicalComplex.preservesLimitsOfShape_of_eval
    intro q
    exact ⟨fun {T} ↦ preservesLimit_of_product_cones _ _
      (hom_degree_projection R L q) (fun M ↦ homComplexIsLimit L M q) T⟩
  have : PreservesLimitsOfShape ℕᵒᵖ (sections.{c, v, max c v r} R A φ) := by
    let S := Scalars.{c, v, max c v r} R
    let M : Modules.{c, v, max c v r} R := SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)
    have := linearCoyoneda_preserves_limits S M
    have : PreservesLimitsOfShape ℕᵒᵖ
        (ModuleCat.restrictScalars.{max c v r} φ) :=
      ⟨fun {T} ↦ ModuleCat.preservesLimit_restrictScalars φ T⟩
    dsimp only [sections]
    infer_instance
  dsimp [representative]
  infer_instance

omit [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasDerivedCategory.{w} (Modules.{c, v, max c v r} R)]
  [HasDerivedCategory.{z} (ModuleCat.{max c v r} A)] in
private theorem representative_split
    (L : CochainComplex (Modules.{c, v, max c v r} R) ℤ)
    {X Y : CochainComplex (Modules.{c, v, max c v r} R) ℤ} (f : X ⟶ Y)
    (hf : ∀ i, IsSplitEpi (f.f i)) (q : ℤ) :
    IsSplitEpi (((representative.{c, v, r, a} R A φ L).map f).f q) := by
  have (p : ℤ) : IsSplitEpi
      ((HomologicalComplex.eval _ _ (p + q) ⋙
        (SheafOfModules.homFunctor R).obj (op (L.X p))).map f) := by
    change IsSplitEpi (((SheafOfModules.homFunctor R).obj (op (L.X p))).map
      (f.f (p + q)))
    have := hf (p + q)
    infer_instance
  have : IsSplitEpi (((homComplexFunctor (R := R)).obj (op L)).map f |>.f q) :=
    product_map_isSplitEpi _ _ (hom_degree_projection R L q)
      (fun M ↦ homComplexIsLimit L M q) f
  change IsSplitEpi ((sections.{c, v, max c v r} R A φ).map
    ((((homComplexFunctor (R := R)).obj (op L)).map f).f q))
  infer_instance

/-- Ordinary limit and normalized Roos models on resolved strict towers.

Source: Stacks Project, sites-cohomology.tex, Tag 0941, proof of
lemma-derived-limit-is-ok; derived.tex, Tag 08BJ.
(blueprint: lem-sfb-global-rhom-resolved-tower-models).

Proof: For a resolved tower, injectivity of each term makes every transition split epic.
The injective-tower Roos theorem identifies Q of its termwise product with the
product of the Q values, and the kernel of 1-shift with the ordinary limit.
Transport its distinguished triangle to the chosen derived product. Its first map
has exactly the ordinary limit projections; this gives the source triangle.
In each degree, representative(L,I) is the product over p of Hom(L^p,I^(p+q)),
with the section-ring action restricted along φ. Maps into limits are compatible
families, and interchanging the products identifies representative(L,lim I)
with lim representative(L,I), with identical differentials. This is precisely
limit.post, proving its invertibility. The split transitions of I induce split
surjections on each product of Hom groups. Recursively solve x_n-t_n x_(n+1)=b_n,
starting with x_0=0, to see that 1-shift is surjective in every degree. Its kernel
is the ordinary limit. The kernel-to-shifted-cone lemma and exact products of
A-modules give the target Roos triangle. Its kernel inclusion is (0,z), so its
first arrow has the stated projections, with no sign change. These constructions
also cover zero or identity transitions and zero objects; no exact-products
hypothesis is imposed on module sheaves. -/
theorem resolved_tower_models
    (L : CochainComplex (Modules.{c, v, max c v r} R) ℤ) :
    (∀ I : (resolvedProperty.{c, v, r} R).FullSubcategory,
      IsIso (limit.post I.obj.asFunctor (representative.{c, v, r, a} R A φ L))) ∧
      (∀ I : (resolvedProperty.{c, v, r} R).FullSubcategory,
        ∃ _hp : HasProduct (fun n : ℕ ↦
            DerivedCategory.Q.{w}.obj (I.obj.asFunctor.obj (op n))),
        ∃ (p : DerivedCategory.Q.{w}.obj (limit I.obj.asFunctor) ⟶
            ∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.{w}.obj (I.obj.asFunctor.obj (op n))))
          (δ : (∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.{w}.obj
              (I.obj.asFunctor.obj (op n)))) ⟶
            (DerivedCategory.Q.{w}.obj (limit I.obj.asFunctor))⟦(1 : ℤ)⟧),
          IsDerivedLimitTriangle
            (fun n : ℕ ↦ DerivedCategory.Q.{w}.map
              (I.obj.asFunctor.map (homOfLE (Nat.le_succ n)).op))
            (DerivedCategory.Q.{w}.obj (limit I.obj.asFunctor)) p δ ∧
          ∀ n : ℕ, p ≫ Pi.π _ n = DerivedCategory.Q.{w}.map
            (limit.π I.obj.asFunctor (op n))) ∧
      (∀ I : (resolvedProperty.{c, v, r} R).FullSubcategory,
        ∃ _hp : HasProduct (fun n : ℕ ↦ DerivedCategory.Q.obj
            (((representativeTowers.{c, v, r, a} R A φ L).obj I).obj (op n))),
        ∃ (p : (globalHomLimit.{c, v, r, a} R A φ L).obj I ⟶
            ∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.obj
              (((representativeTowers.{c, v, r, a} R A φ L).obj I).obj (op n))))
          (δ : (∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.obj
              (((representativeTowers.{c, v, r, a} R A φ L).obj I).obj (op n)))) ⟶
            ((globalHomLimit.{c, v, r, a} R A φ L).obj I)⟦(1 : ℤ)⟧),
          IsDerivedLimitTriangle
            (fun n : ℕ ↦ DerivedCategory.Q.map
              (((representativeTowers.{c, v, r, a} R A φ L).obj I).map
                (homOfLE (Nat.le_succ n)).op))
            ((globalHomLimit.{c, v, r, a} R A φ L).obj I) p δ ∧
          ∀ n : ℕ, p ≫ Pi.π _ n = DerivedCategory.Q.map
            (limit.π ((representativeTowers.{c, v, r, a} R A φ L).obj I) (op n))) := by
  classical
  have hPres := representative_preserves_limits.{c, v, r, a} R A φ L
  refine ⟨fun I ↦ inferInstance, ?_, ?_⟩
  · intro I
    have : I.obj.IsKInjective := I.property.1
    have (q : ℤ) : Injective (I.obj.X q) := I.property.2 q
    have (n : ℕ) : CochainComplex.IsKInjective (I.obj.asFunctor.obj (op n)) :=
      tower_evaluation_isKInjective _ I.obj (op n)
    obtain ⟨_, ⟨hd⟩⟩ := CochainComplex.termwise_product_isKInjective_and_isLimit
      (fun n : ℕ ↦ I.obj.asFunctor.obj (op n))
    let T := Discrete.functor (fun n : ℕ ↦ I.obj.asFunctor.obj (op n))
    let hc := HomologicalComplex.isLimitConeOfHasLimitEval T
    have hQ : Nonempty (IsLimit (DerivedCategory.Q.{w}.mapCone (limit.cone T))) :=
      ⟨hd.ofIsoLimit ((Cone.functoriality T DerivedCategory.Q).mapIso
        (hc.uniqueUpToIso (limit.isLimit T)))⟩
    exact split_tower_triangle I.obj.asFunctor
      (fun q n ↦ injective_tower_transition_split (I.obj.X q) n) hQ
  · intro I
    have (q : ℤ) : Injective (I.obj.X q) := I.property.2 q
    let U := forget₂ (ModuleCat.{max c v r} A) AddCommGrpCat.{max c v r}
    have : PreservesFiniteColimits U := ⟨fun S _ _ ↦
      ModuleCat.forget₂PreservesColimitsOfShape.{max c v r, a, 0, 0} A S⟩
    have : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{max c v r} A) :=
      HasExactLimitsOfShape.domain_of_functor (Discrete ℕ) U
    have : HasFiniteBiproducts (ModuleCat.{max c v r} A) := Abelian.hasFiniteBiproducts
    have : CountableAB4Star (ModuleCat.{max c v r} A) :=
      CountableAB4Star.of_hasExactLimitsOfShape_nat _
    obtain ⟨_, hQ, _⟩ := derivedCategory_countableProducts_core (ModuleCat.{max c v r} A)
    exact split_tower_triangle ((representativeTowers.{c, v, r, a} R A φ L).obj I)
      (fun q n ↦ representative_split.{c, v, r, a} R A φ L
        (I.obj.asFunctor.map (homOfLE n.le_succ).op)
        (fun i ↦ injective_tower_transition_split (I.obj.X i) n) q)
      (hQ ℕ _)

end CategoryTheory.RingedSiteGlobalRHom
