/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeWeilInduction.NativeWeilInductionComparisonData
import WeilConjectures.AlgebraicGeometry.NativeWeilInduction.NativeWeilComparisonStructure
import WeilConjectures.AlgebraicGeometry.NativeWeilInduction.NativeWeilHeartProperties
import WeilConjectures.CategoryTheory.Exact.ExactFunctorCoproducts

/-! # Integer exchanges and the transpose of native free induction -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor

attribute [instance] AlgebraicGeometry.Compactification.over

namespace IntegerExchange

variable {C D : Type*} [Category C] [Category D]
  (P : C ⥤ C) (Q : D ⥤ D) [P.IsEquivalence] [Q.IsEquivalence]
  (F : C ⥤ D) (e : F ⋙ Q ≅ P ⋙ F)

private def positive (A : C) : ∀ n : ℕ,
    IsoAlgebra.Free.posObj Q (F.obj A) n ≅ F.obj (IsoAlgebra.Free.posObj P A n)
  | 0 => Iso.refl _
  | n + 1 => Q.mapIso (positive A n) ≪≫ e.app _

private def negative (A : C) : ∀ n : ℕ,
    IsoAlgebra.Free.negObj Q (F.obj A) n ≅ F.obj (IsoAlgebra.Free.negObj P A n)
  | 0 => Q.preimageIso
      (Q.asEquivalence.counitIso.app (F.obj A) ≪≫
        F.mapIso (P.asEquivalence.counitIso.app A).symm ≪≫ (e.app (P.inv.obj A)).symm)
  | n + 1 => Q.preimageIso
      (IsoAlgebra.Free.objSucc Q (F.obj A) (.negSucc (n + 1)) ≪≫ negative A n ≪≫
        F.mapIso (IsoAlgebra.Free.objSucc P A (.negSucc (n + 1))).symm ≪≫
        (e.app _).symm)

private def iterate (n : ℤ) (A : C) :
    IsoAlgebra.Free.obj Q (F.obj A) n ≅ F.obj (IsoAlgebra.Free.obj P A n) :=
  match n with
  | .ofNat n => positive P Q F e A n
  | .negSucc n => negative P Q F e A n

private theorem iterate_zero (A : C) : (iterate P Q F e 0 A).hom = 𝟙 _ := rfl

private theorem iterate_succ (n : ℤ) (A : C) :
    Q.map (iterate P Q F e n A).hom ≫ e.hom.app (IsoAlgebra.Free.obj P A n) ≫
      F.map (IsoAlgebra.Free.objSucc P A n).hom =
    (IsoAlgebra.Free.objSucc Q (F.obj A) n).hom ≫
      (iterate P Q F e (n + 1) A).hom := by
  rcases n with n | _ | n
  · change Q.map (positive P Q F e A n).hom ≫ e.hom.app _ ≫ F.map (𝟙 _) =
      𝟙 _ ≫ (positive P Q F e A (n + 1)).hom
    simp [positive]
  · change Q.map (negative P Q F e A 0).hom ≫ e.hom.app _ ≫ F.map _ =
      _ ≫ (positive P Q F e A 0).hom
    simp [negative, Functor.preimageIso, positive, IsoAlgebra.Free.obj,
      IsoAlgebra.Free.objSucc, IsoAlgebra.Free.negObj, Category.assoc, ← F.map_comp]
  · change Q.map (negative P Q F e A (n + 1)).hom ≫ e.hom.app _ ≫ F.map _ =
      _ ≫ (negative P Q F e A n).hom
    simp [negative, Functor.preimageIso, IsoAlgebra.Free.obj,
      Category.assoc, ← F.map_comp]

private theorem iterate_natural (n : ℤ) {A B : C} (g : A ⟶ B) :
    IsoAlgebra.Free.objMap Q (F.map g) n ≫ (iterate P Q F e n B).hom =
      (iterate P Q F e n A).hom ≫ F.map (IsoAlgebra.Free.objMap P g n) := by
  have step (m n : ℤ) (hmn : m + 1 = n) :
      (IsoAlgebra.Free.objMap Q (F.map g) m ≫ (iterate P Q F e m B).hom =
        (iterate P Q F e m A).hom ≫ F.map (IsoAlgebra.Free.objMap P g m)) ↔
      (IsoAlgebra.Free.objMap Q (F.map g) n ≫
          (iterate P Q F e n B).hom =
        (iterate P Q F e n A).hom ≫
          F.map (IsoAlgebra.Free.objMap P g n)) := by
    subst n
    have hA := iterate_succ P Q F e m A
    have hB := iterate_succ P Q F e m B
    have hQ := IsoAlgebra.Free.map_objMap_comp_objSucc (F := Q) (F.map g) m
    have hP := IsoAlgebra.Free.map_objMap_comp_objSucc (F := P) g m
    have hE := e.hom.naturality (IsoAlgebra.Free.objMap P g m)
    change Q.map (F.map _) ≫ _ = _ ≫ F.map (P.map _) at hE
    have hleft : Q.map (IsoAlgebra.Free.objMap Q (F.map g) m ≫
          (iterate P Q F e m B).hom) ≫ e.hom.app _ ≫
          F.map (IsoAlgebra.Free.objSucc P B m).hom =
        (IsoAlgebra.Free.objSucc Q (F.obj A) m).hom ≫
          IsoAlgebra.Free.objMap Q (F.map g) (m + 1) ≫
          (iterate P Q F e (m + 1) B).hom := by
      simp only [Functor.map_comp, Category.assoc]
      rw [hB, ← Category.assoc, hQ, Category.assoc]
    have hright : Q.map ((iterate P Q F e m A).hom ≫
          F.map (IsoAlgebra.Free.objMap P g m)) ≫ e.hom.app _ ≫
          F.map (IsoAlgebra.Free.objSucc P B m).hom =
        (IsoAlgebra.Free.objSucc Q (F.obj A) m).hom ≫
          (iterate P Q F e (m + 1) A).hom ≫
          F.map (IsoAlgebra.Free.objMap P g (m + 1)) := by
      simp only [Functor.map_comp, Category.assoc]
      rw [reassoc_of% hE, ← F.map_comp, hP, F.map_comp]
      simpa only [Category.assoc] using congrArg
        (fun t ↦ t ≫ F.map (IsoAlgebra.Free.objMap P g (m + 1))) hA
    constructor
    · intro h
      apply (cancel_epi (IsoAlgebra.Free.objSucc Q (F.obj A) m).hom).1
      simpa only [Category.assoc] using (hleft.symm.trans (by rw [h])).trans hright
    · intro h
      apply Q.map_injective
      apply (cancel_mono (e.hom.app (IsoAlgebra.Free.obj P B m) ≫
        F.map (IsoAlgebra.Free.objSucc P B m).hom)).1
      simpa only [Category.assoc] using (hleft.trans (by rw [h])).trans hright.symm
  exact Int.induction_on n (by simp [iterate_zero, IsoAlgebra.Free.objMap_zero])
    (fun m hm ↦ (step _ _ rfl).1 hm)
    (fun m hm ↦ (step _ _ (by omega)).2 hm)

private theorem family_ext (A : D) (K : IsoAlgebra Q)
    (a b : ∀ n : ℤ, IsoAlgebra.Free.obj Q A n ⟶ K.carrier)
    (h0 : a 0 = b 0)
    (ha : ∀ n, Q.map (a n) ≫ K.str.hom =
      (IsoAlgebra.Free.objSucc Q A n).hom ≫ a (n + 1))
    (hb : ∀ n, Q.map (b n) ≫ K.str.hom =
      (IsoAlgebra.Free.objSucc Q A n).hom ≫ b (n + 1)) : ∀ n, a n = b n := by
  have step (m n : ℤ) (hmn : m + 1 = n) : a m = b m ↔ a n = b n := by
    subst n
    constructor
    · intro h
      apply (cancel_epi (IsoAlgebra.Free.objSucc Q A m).hom).1
      rw [← ha, ← hb, h]
    · intro h
      apply Q.map_injective
      apply (cancel_mono K.str.hom).1
      rw [ha, hb, h]
  intro n
  exact Int.induction_on n h0 (fun m hm ↦ (step _ _ rfl).1 hm)
    (fun m hm ↦ (step _ _ (by omega)).2 hm)

private theorem summand_formula (A : C) (K : IsoAlgebra P) (B L : IsoAlgebra Q)
    (a0 : A ⟶ K.carrier) (u0 : F.obj A ⟶ B.carrier)
    (h : B.carrier ⟶ L.carrier) (b : L.carrier ≅ F.obj K.carrier)
    (hh : Q.map h ≫ L.str.hom = B.str.hom ≫ h)
    (hb : Q.map b.hom ≫ e.hom.app K.carrier ≫ F.map K.str.hom =
      L.str.hom ≫ b.hom)
    (h0 : u0 ≫ h ≫ b.hom = F.map a0) (n : ℤ) :
    IsoAlgebra.Free.hom B u0 n ≫ h ≫ b.hom =
      (iterate P Q F e n A).hom ≫ F.map (IsoAlgebra.Free.hom K a0 n) := by
  apply family_ext Q (F.obj A)
    (IsoAlgebra.mk _ (e.app K.carrier ≪≫ F.mapIso K.str))
    (fun n ↦ IsoAlgebra.Free.hom B u0 n ≫ h ≫ b.hom)
    (fun n ↦ (iterate P Q F e n A).hom ≫ F.map (IsoAlgebra.Free.hom K a0 n))
    (by simpa only [IsoAlgebra.Free.hom_zero, iterate_zero, Category.id_comp] using h0)
    ?_ ?_ n
  · intro m
    change Q.map (_ ≫ h ≫ b.hom) ≫
        (e.hom.app K.carrier ≫ F.map K.str.hom) = _
    simp only [Functor.map_comp, Category.assoc]
    rw [hb, ← Category.assoc (Q.map h), hh]
    simp only [Category.assoc]
    rw [← Category.assoc, ← Category.assoc,
      IsoAlgebra.Free.map_hom_comp_str B u0 m]
    simp only [Category.assoc]
  · intro m
    change Q.map (_ ≫ F.map _) ≫ (e.hom.app K.carrier ≫ F.map K.str.hom) = _
    have hn := e.hom.naturality (IsoAlgebra.Free.hom K a0 m)
    change Q.map (F.map _) ≫ _ = _ ≫ F.map (P.map _) at hn
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% hn, ← F.map_comp, IsoAlgebra.Free.map_hom_comp_str,
      F.map_comp]
    simpa only [Category.assoc] using congrArg
      (fun t ↦ t ≫ F.map (IsoAlgebra.Free.hom K a0 (m + 1)))
      (iterate_succ P Q F e m A)

private def transpose {E : Type*} [Category E] (I : D ⥤ E) (U : E ⥤ D)
    (adj : I ⊣ U) (F : C ⥤ D) (H : C ⥤ E) (a : F ⟶ H ⋙ U) : F ⋙ I ⟶ H :=
  { app := fun A ↦ (adj.homEquiv (F.obj A) (H.obj A)).symm (a.app A)
    naturality := by
      intro A B g
      apply (adj.homEquiv _ _).injective
      change adj.homEquiv _ _ (I.map (F.map g) ≫ _) =
        adj.homEquiv _ _ (_ ≫ H.map g)
      rw [adj.homEquiv_naturality_left, Equiv.apply_symm_apply,
        adj.homEquiv_naturality_right, Equiv.apply_symm_apply]
      exact a.naturality g }

private theorem cofan_isIso {J : Type*} {Xs Ys : J → D}
    (cx : Cofan Xs) (cy : Cofan Ys) (hx : IsColimit cx) (hy : IsColimit cy)
    (c : ∀ j, Ys j ≅ Xs j) (t : cy.pt ⟶ cx.pt)
    (ht : ∀ j, cy.inj j ≫ t = (c j).hom ≫ cx.inj j) : IsIso t := by
  let s := hx.desc (Cofan.mk _ (fun j ↦ (c j).inv ≫ cy.inj j))
  have hs (j : J) : cx.inj j ≫ s = (c j).inv ≫ cy.inj j := hx.fac _ ⟨j⟩
  have hts : t ≫ s = 𝟙 _ := by
    apply hy.hom_ext
    intro ⟨j⟩
    change cy.inj j ≫ (t ≫ s) = _ ≫ 𝟙 _
    rw [← Category.assoc, ht, Category.assoc, hs]
    simp only [Iso.hom_inv_id_assoc, Category.comp_id]
    rfl
  have hst : s ≫ t = 𝟙 _ := by
    apply hx.hom_ext
    intro ⟨j⟩
    change cx.inj j ≫ (s ≫ t) = _ ≫ 𝟙 _
    rw [← Category.assoc, hs, Category.assoc, ht]
    simp only [Iso.inv_hom_id_assoc, Category.comp_id]
    rfl
  exact ⟨⟨s, hts, hst⟩⟩

end IntegerExchange

namespace AlgebraicGeometry.NativeWeilInduction

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

omit [Fact (ringChar k₀ ≠ l)] in
private theorem inverse_frobenius_hull
    (T : Scheme.{u}) [T.Over (Spec (.of k₀))]
    (A : _root_.DerivedCategory
      (ProEtale.AdicSheaf l (T ↘ Spec (.of k₀)).geometricFiber))
    (hA : ProEtale.nativeAdicConstructibleLocalizingHull l
      (T ↘ Spec (.of k₀)).geometricFiber A) :
    ProEtale.nativeAdicConstructibleLocalizingHull l (T ↘ Spec (.of k₀)).geometricFiber
      ((frobenius k₀ l T).inv.obj A) := by
  let C := ProEtale.AdicSheaf l (T ↘ Spec (.of k₀)).geometricFiber
  let Fr := (T ↘ Spec (.of k₀)).geometricGaloisFrobenius
  let E := ProEtale.adicLowerStarEquivalence l Fr.symm
  have : E.inverse.Additive :=
    inferInstanceAs (ProEtale.adicLowerStar l Fr.hom).Additive
  have : E.functor.Additive :=
    inferInstanceAs (WeilSheaf.frobeniusPullback k₀ l T).Additive
  let R := E.inverse.mapDerivedCategory
  let L := ProEtale.nativeAdicConstructibleLocalizingHull l
    (T ↘ Spec (.of k₀)).geometricFiber
  have (J : Type (u + 1)) : HasColimitsOfShape (Discrete J) C :=
    IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1} C J
  have (J : Type (u + 1)) : PreservesColimitsOfShape (Discrete J) R :=
    E.inverse.mapDerivedCategory_preservesCoproducts J
  have : (L.inverseImage R).IsLocalizing :=
    { isClosedUnderColimitsOfShape_discrete J :=
        { colimitsOfShape_le := by
            rintro B ⟨h⟩
            exact L.prop_of_isColimit (isColimitOfPreserves R h.isColimit)
              h.prop_diag_obj } }
  have hR : L ≤ L.inverseImage R := by
    apply ObjectProperty.localizingClosure_le (Q := L.inverseImage R)
    intro B hB
    apply ObjectProperty.le_localizingClosure
    let e := Functor.mapDerivedCategoryNatIso
      (ProEtale.adicUpperStarIsoLowerStarInv l Fr.symm)
    have he := e.app B
    have hp := ProEtale.DerivedCategory.boundedAdicConstructible_mapDerivedCategory_upperStar
      Fr.inv hB
    exact ⟨_root_.DerivedCategory.TStructure.t.bounded.prop_of_iso he hp.1,
      fun i ↦ (ProEtale.adicConstructibleSheaf l _).prop_of_iso
        ((_root_.DerivedCategory.homologyFunctor _ i).mapIso he) (hp.2 i)⟩
  let ε : R ⋙ frobenius k₀ l T ≅ 𝟭 _ :=
    (Functor.mapDerivedCategoryCompIso E.inverse E.functor).symm ≪≫
      Functor.mapDerivedCategoryNatIso E.counitIso ≪≫ Functor.mapDerivedCategoryIdIso C
  let b : (frobenius k₀ l T).inv.obj A ≅ R.obj A :=
    (frobenius k₀ l T).preimageIso
      ((frobenius k₀ l T).asEquivalence.counitIso.app A ≪≫ (ε.app A).symm)
  exact L.prop_of_iso b.symm (hR A hA)

variable {X Y : Scheme.{u}} [X.Over (Spec (.of k₀))] [Y.Over (Spec (.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of k₀))] (c : Compactification f)

private theorem ordinary_preserves_free_cofan
    [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f]
    [LocallyOfFiniteType (Y ↘ Spec (.of k₀))]
    [QuasiCompact (Y ↘ Spec (.of k₀))] [QuasiSeparated (Y ↘ Spec (.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of k₀))] [QuasiCompact (X ↘ Spec (.of k₀))]
    (A : _root_.DerivedCategory
      (ProEtale.AdicSheaf l (X ↘ Spec (.of k₀)).geometricFiber))
    (hA : ProEtale.nativeAdicConstructibleLocalizingHull l
      (X ↘ Spec (.of k₀)).geometricFiber A) :
    Nonempty (IsColimit (Cofan.mk
      ((ordinaryImage k₀ l f c).obj ((forget k₀ l X).obj ((induction k₀ l X).obj A)))
      (fun n : ℤ ↦ (ordinaryImage k₀ l f c).map (inclusion k₀ l X A n)))) := by
  let aX := X ↘ Spec (.of k₀)
  let aY := Y ↘ Spec (.of k₀)
  let aZ := c.Z ↘ Spec (.of k₀)
  let fbar := Scheme.Hom.geometricFiberMap f (comp_over f (Spec (.of k₀)))
  let ibar := Scheme.Hom.geometricFiberMap c.i (comp_over c.i (Spec (.of k₀)))
  let gbar := Scheme.Hom.geometricFiberMap c.g (comp_over c.g (Spec (.of k₀)))
  let : aX.geometricFiber.Over (Spec (.of (AlgebraicClosure k₀))) :=
    ⟨aX.geometricFiberToAlgebraicClosure⟩
  let : aY.geometricFiber.Over (Spec (.of (AlgebraicClosure k₀))) :=
    ⟨aY.geometricFiberToAlgebraicClosure⟩
  have : fbar.IsOver (Spec (.of (AlgebraicClosure k₀))) :=
    ⟨Scheme.Hom.geometricFiberMap_comp_geometricFiberToAlgebraicClosure f _⟩
  have : IsProper gbar :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsProper) c.g _
      inferInstance
  let cbar : Compactification fbar :=
    { Z := aZ.geometricFiber
      g := gbar
      i := ibar
      comm := by
        dsimp only [fbar, ibar, gbar]
        rw [← Scheme.Hom.geometricFiberMap_comp]
        congr 1
        exact c.comm
      isProper := inferInstance
      isOpenImmersion := inferInstance }
  have : LocallyOfFiniteType (aX.geometricFiber ↘ Spec (.of (AlgebraicClosure k₀))) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : QuasiCompact (aX.geometricFiber ↘ Spec (.of (AlgebraicClosure k₀))) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : LocallyOfFiniteType (aY.geometricFiber ↘ Spec (.of (AlgebraicClosure k₀))) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : QuasiCompact (aY.geometricFiber ↘ Spec (.of (AlgebraicClosure k₀))) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  obtain ⟨h, -, hpres⟩ := ProEtale.nativeAdicCompactSupport_localizing_preservesCoproducts
    k₀ (AlgebraicClosure k₀) l (Fact.out : ringChar k₀ ≠ l) fbar cbar
  let LX := ProEtale.nativeAdicConstructibleLocalizingHull l aX.geometricFiber
  let LY := ProEtale.nativeAdicConstructibleLocalizingHull l aY.geometricFiber
  let F := ordinaryImage k₀ l f c
  let G := LX.liftFullSubcategory LY F h
  have : PreservesColimitsOfShape (Discrete (ULift.{u + 1} ℤ)) G := hpres _
  have : PreservesColimitsOfShape (Discrete ℤ) G :=
    preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) G
  have : LX.IsClosedUnderColimitsOfShape (Discrete ℤ) :=
    ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence (P := LX)
      (Discrete.equivalence (Equiv.ulift : ULift.{u + 1} ℤ ≃ ℤ))
  have : LY.IsClosedUnderColimitsOfShape (Discrete ℤ) :=
    ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence (P := LY)
      (Discrete.equivalence (Equiv.ulift : ULift.{u + 1} ℤ ≃ ℤ))
  have hPn (n : ℤ) : LX (IsoAlgebra.Free.obj (frobenius k₀ l X) A n) := by
    have hpos (m : ℕ) : LX (IsoAlgebra.Free.posObj (frobenius k₀ l X) A m) := by
      induction m with
      | zero => exact hA
      | succ m hm => exact (nativeWeil_heart_properties k₀ l X).2.2.2.2.2.2.2.2.2.1 _ hm
    have hneg (m : ℕ) : LX (IsoAlgebra.Free.negObj (frobenius k₀ l X) A m) := by
      induction m with
      | zero => exact inverse_frobenius_hull k₀ l X A hA
      | succ m hm => exact inverse_frobenius_hull k₀ l X _ hm
    cases n with
    | ofNat n => exact hpos n
    | negSucc n => exact hneg n
  let sc := Cofan.mk ((forget k₀ l X).obj ((induction k₀ l X).obj A)) (inclusion k₀ l X A)
  have hc := ((nativeWeil_heart_properties k₀ l X).2.2.2.2.2.2.2.2.2.2 A).some
  have hsum : LX sc.pt := LX.prop_of_isColimit hc (fun n ↦ hPn n.as)
  let scL : Cofan (fun n : ℤ ↦ (⟨_, hPn n⟩ : LX.FullSubcategory)) :=
    Cofan.mk ⟨_, hsum⟩ (fun n ↦ ObjectProperty.homMk (inclusion k₀ l X A n))
  have hcL : IsColimit scL := isColimitOfReflects LX.ι
    ((Cofan.isColimitMapCoconeEquiv LX.ι _ scL).symm hc)
  have (J : Type) : HasColimitsOfShape (Discrete J)
      (ProEtale.AdicSheaf l aY.geometricFiber) :=
    IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1} _ J
  have : HasCoproducts.{0} (_root_.DerivedCategory
      (ProEtale.AdicSheaf l aY.geometricFiber)) := derived_hasCoproducts
  have : PreservesColimitsOfShape (Discrete ℤ) LY.ι := inferInstance
  exact ⟨Cofan.isColimitMapCoconeEquiv (G ⋙ LY.ι) _ scL
    (isColimitOfPreserves (G ⋙ LY.ι) hcL)⟩

set_option maxHeartbeats 400000 in
-- The native derived functor expressions require extra elaboration for the existential
-- witnesses; the integer recursion and cofan calculations are proved generically above.
/-- The coherent integer exchanges and the actual free-adjunction transpose satisfy
the summand formula, and the transpose is invertible on the constructible localizing hull.
Source: comparison proof steps 5--8, blueprint `lem-fix-weil-operations`, paragraphs 1--2,
and the final sentence of `cor-coef-verdier-weil-equivariance`.
(blueprint: lem-sf-native-weil-induction-summands)

Proof: iterate the specified native exchange and its inverse, starting with the identity
at zero. Naturality follows by induction; cancellation gives the successor recurrence
also at negative indices. Define the natural map by transposing `F(eta)` followed by
beta inverse under the specified derived free adjunction. On a common K-injective
resolution, beta intertwines the localized structure with F of the source structure
after the native exchange: this is the defining equation of the lifted sheaf functor.
It is compatible with derived maps by the K-injective map computation. Iterate that
equation over the integers. The free unit is the zeroth coprojection, and its iterated
structure maps give the coprojections numbered by all integers. The adjunction triangle
identity and exchange naturality give the stated formula on every summand. Frobenius
and its inverse preserve the constructible localizing hull, so the native compact-support
coproduct theorem applies to this family. The formula identifies the forgotten transpose
with the canonical coproduct comparison composed with the sum of the integer exchange
isomorphisms. It is invertible; conservativity of derived forgetting reflects this. -/
theorem nativeWeil_induction_summands
    [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f]
    [LocallyOfFiniteType (Y ↘ Spec (.of k₀))]
    [QuasiCompact (Y ↘ Spec (.of k₀))] [QuasiSeparated (Y ↘ Spec (.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of k₀))] [QuasiCompact (X ↘ Spec (.of k₀))] :
    ∃ cN : ∀ (n : ℤ) (A : _root_.DerivedCategory
        (ProEtale.AdicSheaf l (X ↘ Spec (.of k₀)).geometricFiber)),
      IsoAlgebra.Free.obj (frobenius k₀ l Y) ((ordinaryImage k₀ l f c).obj A) n ≅
        (ordinaryImage k₀ l f c).obj (IsoAlgebra.Free.obj (frobenius k₀ l X) A n),
      (∀ (n : ℤ) (A B : _root_.DerivedCategory
          (ProEtale.AdicSheaf l (X ↘ Spec (.of k₀)).geometricFiber)) (g : A ⟶ B),
        IsoAlgebra.Free.objMap (frobenius k₀ l Y) ((ordinaryImage k₀ l f c).map g) n ≫
          (cN n B).hom = (cN n A).hom ≫ (ordinaryImage k₀ l f c).map
            (IsoAlgebra.Free.objMap (frobenius k₀ l X) g n)) ∧
      (∀ A, (cN 0 A).hom = 𝟙 _) ∧
      (∀ (n : ℤ) A,
        (frobenius k₀ l Y).map (cN n A).hom ≫
          (exchange k₀ l f c).hom.app (IsoAlgebra.Free.obj (frobenius k₀ l X) A n) ≫
          (ordinaryImage k₀ l f c).map (IsoAlgebra.Free.objSucc
            (frobenius k₀ l X) A n).hom =
        (IsoAlgebra.Free.objSucc (frobenius k₀ l Y)
          ((ordinaryImage k₀ l f c).obj A) n).hom ≫ (cN (n + 1) A).hom) ∧
      ∃ κ : ordinaryImage k₀ l f c ⋙ induction k₀ l Y ⟶
          induction k₀ l X ⋙ ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f c,
        (∀ A, κ.app A = (induction k₀ l Y).map
          ((ordinaryImage k₀ l f c).map
              ((IsoAlgebra.freeWeilDerivedAdjunction
                (WeilSheaf.frobeniusPullback k₀ l X)).unit.app A) ≫
            (comparison k₀ l f c).inv.app ((induction k₀ l X).obj A)) ≫
          (IsoAlgebra.freeWeilDerivedAdjunction
            (WeilSheaf.frobeniusPullback k₀ l Y)).counit.app
              ((ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f c).obj
                ((induction k₀ l X).obj A))) ∧
        ∀ A, ProEtale.nativeAdicConstructibleLocalizingHull l
            (X ↘ Spec (.of k₀)).geometricFiber A →
          IsIso (κ.app A) ∧ ∀ n : ℤ,
            inclusion k₀ l Y ((ordinaryImage k₀ l f c).obj A) n ≫
              (forget k₀ l Y).map (κ.app A) ≫
              (comparison k₀ l f c).hom.app ((induction k₀ l X).obj A) =
            (cN n A).hom ≫ (ordinaryImage k₀ l f c).map (inclusion k₀ l X A n) := by
  let P := frobenius k₀ l X
  let Q := frobenius k₀ l Y
  let F := ordinaryImage k₀ l f c
  let e := exchange k₀ l f c
  let IX := induction k₀ l X
  let IY := induction k₀ l Y
  let UX := forget k₀ l X
  let UY := forget k₀ l Y
  let FW := ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f c
  let β := comparison k₀ l f c
  let adjX := IsoAlgebra.freeWeilDerivedAdjunction (WeilSheaf.frobeniusPullback k₀ l X)
  let adjY := IsoAlgebra.freeWeilDerivedAdjunction (WeilSheaf.frobeniusPullback k₀ l Y)
  let a : F ⟶ IX ⋙ FW ⋙ UY :=
    { app := fun A ↦ F.map (adjX.unit.app A) ≫ β.inv.app (IX.obj A)
      naturality := by
        intro A B g
        change F.map g ≫ (F.map (adjX.unit.app B) ≫ β.inv.app (IX.obj B)) =
          (F.map (adjX.unit.app A) ≫ β.inv.app (IX.obj A)) ≫ UY.map (FW.map (IX.map g))
        have hu := adjX.unit.naturality g
        change g ≫ adjX.unit.app B = adjX.unit.app A ≫ UX.map (IX.map g) at hu
        have hb := β.inv.naturality (IX.map g)
        change F.map (UX.map (IX.map g)) ≫ β.inv.app (IX.obj B) =
          β.inv.app (IX.obj A) ≫ UY.map (FW.map (IX.map g)) at hb
        rw [← F.map_comp_assoc, hu, F.map_comp, Category.assoc, hb]
        simp only [Category.assoc] }
  let κ : F ⋙ IY ⟶ IX ⋙ FW := IntegerExchange.transpose IY UY adjY F (IX ⋙ FW) a
  let cN := IntegerExchange.iterate P Q F e
  refine ⟨cN, ?_, ?_, ?_, κ, ?_, ?_⟩
  · exact fun n A B g ↦ IntegerExchange.iterate_natural P Q F e n g
  · exact IntegerExchange.iterate_zero P Q F e
  · exact IntegerExchange.iterate_succ P Q F e
  · intro A
    rfl
  · intro A hA
    have hformula (n : ℤ) :
        inclusion k₀ l Y (F.obj A) n ≫ UY.map (κ.app A) ≫ β.hom.app (IX.obj A) =
          (cN n A).hom ≫ F.map (inclusion k₀ l X A n) := by
      apply IntegerExchange.summand_formula P Q F e A
        (IsoAlgebra.mk _ ((structureIso k₀ l X).app (IX.obj A)))
        (IsoAlgebra.mk _ ((structureIso k₀ l Y).app (IY.obj (F.obj A))))
        (IsoAlgebra.mk _ ((structureIso k₀ l Y).app (FW.obj (IX.obj A))))
        (adjX.unit.app A) (adjY.unit.app (F.obj A)) (UY.map (κ.app A))
        (β.app (IX.obj A)) ?_ ?_ ?_ n
      · exact (structureIso k₀ l Y).hom.naturality (κ.app A)
      · exact nativeWeil_comparison_structure k₀ l f c (IX.obj A)
      · have h := (adjY.homEquiv (F.obj A) (FW.obj (IX.obj A))).apply_symm_apply
          (a.app A)
        change adjY.unit.app (F.obj A) ≫ UY.map (κ.app A) = a.app A at h
        rw [← Category.assoc, h]
        dsimp only [a, NatTrans.app]
        change (F.map (adjX.unit.app A) ≫ (β.app (IX.obj A)).inv) ≫
          (β.app (IX.obj A)).hom = _
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    refine ⟨?_, hformula⟩
    have hX := (ordinary_preserves_free_cofan k₀ l f c A hA).some
    have hY := ((nativeWeil_heart_properties k₀ l Y).2.2.2.2.2.2.2.2.2.2
      (F.obj A)).some
    have : IsIso (UY.map (κ.app A) ≫ β.hom.app (IX.obj A)) :=
      IntegerExchange.cofan_isIso _ _ hX hY (fun n ↦ cN n A) _ hformula
    have : IsIso (UY.map (κ.app A)) :=
      IsIso.of_isIso_comp_right _ (β.hom.app (IX.obj A))
    have : UY.ReflectsIsomorphisms :=
      (nativeWeil_heart_properties k₀ l Y).2.2.2.2.2.1
    exact isIso_of_reflects_iso (κ.app A) UY

end AlgebraicGeometry.NativeWeilInduction
