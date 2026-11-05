/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.DerivedHom
public import WeilConjectures.WeilSheaf.LowerShriekFunctoriality
public import WeilConjectures.WeilSheaf.Localization
public import WeilConjectures.WeilSheaf.VerdierExchange

/-!
# The Verdier exchange of Weil complexes, natural form

For a separated morphism of finite type `f : X ⟶ Y` of separated `k₀`-schemes of finite type,
the Verdier exchange `𝔻_Y Rf₀! ≅ Rf_* 𝔻_X` (blueprint `fix-cor-verdier-exchange`) as a natural
isomorphism of functors `(WeilComplex X)ᵒᵖ ⥤ WeilComplex Y`. With Verdier biduality it identifies
`Rf^!` with `𝔻_X f^* 𝔻_Y` (`AlgebraicGeometry.WeilComplex.nonempty_upperShriek_obj_iso`).

The Verdier dual `AlgebraicGeometry.WeilComplex.verdierDual` and the dualizing complex are defined
in `WeilConjectures.WeilSheaf.VerdierDual`, which imports this file; they are spelled out here:
the dualizing complex of `X` is `(Ra_X!)^{ra}(ℚ̄_ℓ)`, the right adjoint of `Ra_X!` applied to the
constant Weil sheaf on `Spec k₀`, and the Verdier dual is the derived internal hom into it, lifted
to Weil complexes along a proof that it lands there (in `VerdierDual`,
`AlgebraicGeometry.WeilComplex.objectProperty_derivedHom_dualizingComplex`).
-/

@[expose] public section

universe u

open CategoryTheory Opposite MonoidalCategory

/-- A natural isomorphism `F ≅ G` from bijections `(T ⟶ F c) ≃ (T ⟶ G c)` natural in both `T`
and `c` (the Yoneda lemma, in both variables). -/
noncomputable def CategoryTheory.NatIso.ofHomEquiv {C : Type*} [Category C] {D : Type*}
    [Category D] {F G : C ⥤ D} (e : ∀ c T, (T ⟶ F.obj c) ≃ (T ⟶ G.obj c))
    (hT : ∀ c {T T' : D} (t : T' ⟶ T) (φ : T ⟶ F.obj c), e c T' (t ≫ φ) = t ≫ e c T φ)
    (hc : ∀ {c c' : C} (g : c ⟶ c') (T : D) (φ : T ⟶ F.obj c),
      e c' T (φ ≫ F.map g) = e c T φ ≫ G.map g) : F ≅ G :=
  have hT' : ∀ c {T T' : D} (t : T' ⟶ T) (ψ : T ⟶ G.obj c),
      (e c T').symm (t ≫ ψ) = t ≫ (e c T).symm ψ := fun c T T' t ψ ↦ by
    apply (e c T').injective
    rw [Equiv.apply_symm_apply, hT, Equiv.apply_symm_apply]
  NatIso.ofComponents
    (fun c ↦
      { hom := e c _ (𝟙 _)
        inv := (e c _).symm (𝟙 _)
        hom_inv_id := by
          rw [← hT', Category.comp_id, Equiv.symm_apply_apply]
        inv_hom_id := by
          rw [← hT, Category.comp_id, Equiv.apply_symm_apply] })
    fun {c c'} g ↦ by
      dsimp
      rw [← hT, Category.comp_id, ← hc, Category.id_comp]

/-- The tensor–hom transpose is natural in the tensored variable. -/
lemma WeilConjectures.CoefficientClosedStructure.homEquiv_whiskerLeft {D : Type*} [Category D]
    {H : Dᵒᵖ × D ⥤ D} (S : WeilConjectures.CoefficientClosedStructure H) {P P' : D}
    (g : P' ⟶ P) (T Q : D)
    (φ : (@MonoidalCategory.tensorRight D _ S.monoidal P).obj T ⟶ Q) :
    (S.adjunction P').homEquiv T Q
        ((@MonoidalCategory.tensorLeft D _ S.monoidal T).map g ≫ φ) =
      (S.adjunction P).homEquiv T Q φ ≫ H.map (Prod.mkHom g.op (𝟙 Q)) := by
  let := S.monoidal
  apply ((S.adjunction P').homEquiv T Q).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  erw [S.evaluation_naturality P P' Q g]
  change (T ◁ g) ≫ φ = (((S.adjunction P).homEquiv T Q φ) ▷ P') ≫ (H.obj (op P, Q) ◁ g) ≫
    (S.adjunction P).counit.app Q
  have hx := whisker_exchange (C := D) ((S.adjunction P).homEquiv T Q φ : T ⟶ H.obj (op P, Q)) g
  rw [← Category.assoc (((S.adjunction P).homEquiv T Q φ) ▷ P')]
  erw [← hx]
  rw [Category.assoc]
  congr 1
  conv_lhs => rw [← Equiv.symm_apply_apply ((S.adjunction P).homEquiv T Q) φ,
    Adjunction.homEquiv_counit]
  rfl

/-- The tensor–hom transpose, precomposed with the symmetry, is natural in the tensored
variable. -/
lemma WeilConjectures.CoefficientClosedStructure.homEquiv_braiding_inv_naturality {D : Type*}
    [Category D] {H : Dᵒᵖ × D ⥤ D} (S : WeilConjectures.CoefficientClosedStructure H)
    (β : @SymmetricCategory D _ S.monoidal) {P P' : D} (g : P' ⟶ P) (T Q : D)
    (ψ : S.tensor.obj (P, T) ⟶ Q) :
    letI := S.monoidal
    letI := β
    (S.adjunction P').homEquiv T Q ((β_ P' T).inv ≫ S.tensor.map (Prod.mkHom g (𝟙 T)) ≫ ψ) =
      (S.adjunction P).homEquiv T Q ((β_ P T).inv ≫ ψ) ≫ H.map (Prod.mkHom g.op (𝟙 Q)) := by
  let := S.monoidal
  let := β
  rw [← S.homEquiv_whiskerLeft]
  congr 1
  change (β_ P' T).inv ≫ (g ⊗ₘ 𝟙 T) ≫ ψ = (T ◁ g) ≫ (β_ P T).inv ≫ ψ
  rw [tensorHom_id, ← Category.assoc, ← BraidedCategory.braiding_inv_naturality_right,
    Category.assoc]

/-- The tensor–hom transpose, precomposed with the symmetry, is natural in the test variable. -/
lemma WeilConjectures.CoefficientClosedStructure.homEquiv_braiding_inv_naturality_right
    {D : Type*} [Category D] {H : Dᵒᵖ × D ⥤ D} (S : WeilConjectures.CoefficientClosedStructure H)
    (β : @SymmetricCategory D _ S.monoidal) {T T' : D} (t : T' ⟶ T) (P Q : D)
    (ψ : S.tensor.obj (P, T) ⟶ Q) :
    letI := S.monoidal
    letI := β
    (S.adjunction P).homEquiv T' Q ((β_ P T').inv ≫ S.tensor.map (Prod.mkHom (𝟙 P) t) ≫ ψ) =
      t ≫ (S.adjunction P).homEquiv T Q ((β_ P T).inv ≫ ψ) := by
  let := S.monoidal
  let := β
  rw [← Adjunction.homEquiv_naturality_left]
  congr 1
  change (β_ P T').inv ≫ (𝟙 P ⊗ₘ t) ≫ ψ = (t ▷ P) ≫ (β_ P T).inv ≫ ψ
  rw [id_tensorHom, ← Category.assoc, ← BraidedCategory.braiding_inv_naturality_left,
    Category.assoc]

namespace AlgebraicGeometry

attribute [local irreducible] ProEtaleWeilSheaf.nativeDerivedClosedComparison

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace ProEtaleWeilSheaf

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

set_option linter.flexible false in
lemma nativeDerivedTensorOpCompYonedaIso_hom_app_apply
    (P Q T : DerivedCategory (ProEtaleWeilSheaf k₀ l X))
    (ψ : (nativeDerivedTensor k₀ l X).obj (P, T) ⟶ Q) :
    (nativeDerivedTensorOpCompYonedaIso P Q).hom.app (op T) ψ =
      letI := (nativeDerivedClosedComparison k₀ l X).weilClosed.monoidal
      letI := (nativeDerivedClosedComparison k₀ l X).weilSymmetry
      ((nativeDerivedClosedComparison k₀ l X).weilClosed.adjunction P).homEquiv T Q
          ((β_ P T).inv ≫ ψ) ≫
        ((nativeDerivedClosedComparison k₀ l X).homModels.nativeModel Q).hom.app (op P) := by
  simp [nativeDerivedTensorOpCompYonedaIso, Adjunction.compYonedaIso]
  erw [Category.id_comp]

/-- The tensor–hom isomorphism `Hom(P ⊗ T, Q) ≅ Hom(T, RHom(P, Q))` is natural in `P`. -/
lemma nativeDerivedTensorOpCompYonedaIso_hom_app_map_left
    {P P' : DerivedCategory (ProEtaleWeilSheaf k₀ l X)} (g : P' ⟶ P)
    (Q T : DerivedCategory (ProEtaleWeilSheaf k₀ l X))
    (ψ : (nativeDerivedTensor k₀ l X).obj (P, T) ⟶ Q) :
    (nativeDerivedTensorOpCompYonedaIso P' Q).hom.app (op T)
        ((nativeDerivedTensor k₀ l X).map (Prod.mkHom g (𝟙 T)) ≫ ψ) =
      (nativeDerivedTensorOpCompYonedaIso P Q).hom.app (op T) ψ ≫
        (derivedHom k₀ l X Q).map g.op := by
  rw [nativeDerivedTensorOpCompYonedaIso_hom_app_apply,
    nativeDerivedTensorOpCompYonedaIso_hom_app_apply]
  have nat : (nativeDerivedClosedComparison k₀ l X).homModels.weilHom.map (Prod.mkHom g.op (𝟙 Q)) ≫
      ((nativeDerivedClosedComparison k₀ l X).homModels.nativeModel Q).hom.app (op P') =
      ((nativeDerivedClosedComparison k₀ l X).homModels.nativeModel Q).hom.app (op P) ≫
        (derivedHom k₀ l X Q).map g.op :=
    ((nativeDerivedClosedComparison k₀ l X).homModels.nativeModel Q).hom.naturality g.op
  have h := WeilConjectures.CoefficientClosedStructure.homEquiv_braiding_inv_naturality
    (nativeDerivedClosedComparison k₀ l X).weilClosed
    (nativeDerivedClosedComparison k₀ l X).weilSymmetry g T Q ψ
  refine (congrArg (· ≫ ((nativeDerivedClosedComparison k₀ l X).homModels.nativeModel Q).hom.app
    (op P')) h).trans ?_
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) nat).trans (Category.assoc _ _ _).symm)

/-- The tensor–hom isomorphism `Hom(P ⊗ T, Q) ≅ Hom(T, RHom(P, Q))` is natural in `T`. -/
lemma nativeDerivedTensorOpCompYonedaIso_hom_app_map_right
    (P Q : DerivedCategory (ProEtaleWeilSheaf k₀ l X))
    {T T' : DerivedCategory (ProEtaleWeilSheaf k₀ l X)}
    (t : T' ⟶ T) (ψ : (nativeDerivedTensor k₀ l X).obj (P, T) ⟶ Q) :
    (nativeDerivedTensorOpCompYonedaIso P Q).hom.app (op T')
        ((nativeDerivedTensor k₀ l X).map (Prod.mkHom (𝟙 P) t) ≫ ψ) =
      t ≫ (nativeDerivedTensorOpCompYonedaIso P Q).hom.app (op T) ψ := by
  rw [nativeDerivedTensorOpCompYonedaIso_hom_app_apply,
    nativeDerivedTensorOpCompYonedaIso_hom_app_apply]
  exact (congrArg (· ≫ ((nativeDerivedClosedComparison k₀ l X).homModels.nativeModel Q).hom.app
    (op P)) (WeilConjectures.CoefficientClosedStructure.homEquiv_braiding_inv_naturality_right
      (nativeDerivedClosedComparison k₀ l X).weilClosed
      (nativeDerivedClosedComparison k₀ l X).weilSymmetry t P Q ψ)).trans (Category.assoc _ _ _)


end ProEtaleWeilSheaf

namespace WeilComplex

section NatExchange

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]

/-- The tensor–hom bijection `Hom(P ⊗ T, Q) ≃ Hom(T, RHom(P, Q))` for Weil complexes. -/
noncomputable def nativeConstructibleTensorHomEquiv (P Q T : WeilComplex k₀ l X) :
    ((nativeConstructibleTensor k₀ l X).obj (P, T) ⟶ Q) ≃
      (T.obj ⟶ (ProEtaleWeilSheaf.derivedHom k₀ l X Q.obj).obj (op P.obj)) :=
  (InducedCategory.homEquiv).trans
    ((ProEtaleWeilSheaf.nativeDerivedTensorOpCompYonedaIso P.obj Q.obj).app (op T.obj)).toEquiv

lemma nativeConstructibleTensorHomEquiv_apply (P Q T : WeilComplex k₀ l X)
    (ψ : (nativeConstructibleTensor k₀ l X).obj (P, T) ⟶ Q) :
    nativeConstructibleTensorHomEquiv P Q T ψ =
      (ProEtaleWeilSheaf.nativeDerivedTensorOpCompYonedaIso P.obj Q.obj).hom.app (op T.obj)
        ψ.hom :=
  rfl

lemma nativeConstructibleTensorHomEquiv_map_right (P Q : WeilComplex k₀ l X)
    {T T' : WeilComplex k₀ l X} (t : T' ⟶ T)
    (ψ : (nativeConstructibleTensor k₀ l X).obj (P, T) ⟶ Q) :
    nativeConstructibleTensorHomEquiv P Q T'
        ((nativeConstructibleTensor k₀ l X).map (Prod.mkHom (𝟙 P) t) ≫ ψ) =
      t.hom ≫ nativeConstructibleTensorHomEquiv P Q T ψ := by
  rw [nativeConstructibleTensorHomEquiv_apply, nativeConstructibleTensorHomEquiv_apply]
  exact ProEtaleWeilSheaf.nativeDerivedTensorOpCompYonedaIso_hom_app_map_right P.obj Q.obj t.hom
    ψ.hom

lemma nativeConstructibleTensorHomEquiv_map_left {P P' : WeilComplex k₀ l X} (g : P' ⟶ P)
    (Q T : WeilComplex k₀ l X) (ψ : (nativeConstructibleTensor k₀ l X).obj (P, T) ⟶ Q) :
    nativeConstructibleTensorHomEquiv P' Q T
        ((nativeConstructibleTensor k₀ l X).map (Prod.mkHom g (𝟙 T)) ≫ ψ) =
      nativeConstructibleTensorHomEquiv P Q T ψ ≫
        (ProEtaleWeilSheaf.derivedHom k₀ l X Q.obj).map g.hom.op := by
  rw [nativeConstructibleTensorHomEquiv_apply, nativeConstructibleTensorHomEquiv_apply]
  exact ProEtaleWeilSheaf.nativeDerivedTensorOpCompYonedaIso_hom_app_map_left g.hom Q.obj T.obj
    ψ.hom

omit [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] in
lemma nativeConstructibleTensorHomEquiv_symm_map_right (P Q : WeilComplex k₀ l X)
    {T T' : WeilComplex k₀ l X} (t : T' ⟶ T)
    (x : T.obj ⟶ (ProEtaleWeilSheaf.derivedHom k₀ l X Q.obj).obj (op P.obj)) :
    (nativeConstructibleTensorHomEquiv P Q T').symm (t.hom ≫ x) =
      (nativeConstructibleTensor k₀ l X).map (Prod.mkHom (𝟙 P) t) ≫
        (nativeConstructibleTensorHomEquiv P Q T).symm x := by
  rw [Equiv.symm_apply_eq, nativeConstructibleTensorHomEquiv_map_right, Equiv.apply_symm_apply]

omit [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] in
lemma nativeConstructibleTensorHomEquiv_symm_map_left {P P' : WeilComplex k₀ l X} (g : P' ⟶ P)
    (Q T : WeilComplex k₀ l X)
    (x : T.obj ⟶ (ProEtaleWeilSheaf.derivedHom k₀ l X Q.obj).obj (op P.obj)) :
    (nativeConstructibleTensorHomEquiv P' Q T).symm
        (x ≫ (ProEtaleWeilSheaf.derivedHom k₀ l X Q.obj).map g.hom.op) =
      (nativeConstructibleTensor k₀ l X).map (Prod.mkHom g (𝟙 T)) ≫
        (nativeConstructibleTensorHomEquiv P Q T).symm x := by
  rw [Equiv.symm_apply_eq, nativeConstructibleTensorHomEquiv_map_left, Equiv.apply_symm_apply]

variable (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]


variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  {S : Scheme.{u}} [S.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (S ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (S ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (S ↘ Spec (CommRingCat.of k₀))]
  (aX : X ⟶ S) (aY : Y ⟶ S) [aX.IsOver (Spec (CommRingCat.of k₀))]
  [aY.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated aX] [LocallyOfFiniteType aX]
  [QuasiCompact aX] [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
  {GX : WeilComplex k₀ l S ⥤ WeilComplex k₀ l X} {GY : WeilComplex k₀ l S ⥤ WeilComplex k₀ l Y}
  (adjX : derivedLowerShriek k₀ l aX ⊣ GX) (adjY : derivedLowerShriek k₀ l aY ⊣ GY)
  (c : derivedLowerShriek k₀ l aX ≅ derivedLowerShriek k₀ l f ⋙ derivedLowerShriek k₀ l aY)
  (π : nativeCompactProjectionLeft k₀ l f ≅ nativeCompactProjectionRight k₀ l f)
  (Q : WeilComplex k₀ l S)
  (hX : ∀ K : WeilComplex k₀ l X, WeilComplex.objectProperty k₀ l X
    ((ProEtaleWeilSheaf.derivedHom k₀ l X (GX.obj Q).obj).obj (op K.obj)))
  (hY : ∀ K : WeilComplex k₀ l Y, WeilComplex.objectProperty k₀ l Y
    ((ProEtaleWeilSheaf.derivedHom k₀ l Y (GY.obj Q).obj).obj (op K.obj)))

/-- `Hom(f^* T, D) ≃ Hom(T, Rf_* D)` with the source written in the ambient derived category. -/
noncomputable def upperStarObjHomEquiv (T : WeilComplex k₀ l Y) (D : WeilComplex k₀ l X) :
    (((upperStar f).obj T).obj ⟶ D.obj) ≃ (T ⟶ (derivedLowerStar f).obj D) :=
  ((objectProperty k₀ l X).fullyFaithfulι.homEquiv).symm.trans
    ((upperStarDerivedLowerStarAdjunction f).homEquiv _ _)

omit [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))] in
lemma upperStarObjHomEquiv_map_left {T T' : WeilComplex k₀ l Y} (t : T' ⟶ T)
    (D : WeilComplex k₀ l X) (v : ((upperStar f).obj T).obj ⟶ D.obj) :
    upperStarObjHomEquiv f T' D (((upperStar f).map t).hom ≫ v) =
      t ≫ upperStarObjHomEquiv f T D v := by
  simp only [upperStarObjHomEquiv, Equiv.trans_apply]
  rw [← Adjunction.homEquiv_naturality_left]
  congr 1

omit [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))] in
lemma upperStarObjHomEquiv_map_right (T : WeilComplex k₀ l Y) {D D' : WeilComplex k₀ l X}
    (k : D ⟶ D') (v : ((upperStar f).obj T).obj ⟶ D.obj) :
    upperStarObjHomEquiv f T D' (v ≫ k.hom) =
      upperStarObjHomEquiv f T D v ≫ (derivedLowerStar f).map k := by
  simp only [upperStarObjHomEquiv, Equiv.trans_apply]
  rw [← Adjunction.homEquiv_naturality_right]
  congr 1


/-- `Hom(Rf₀! N, G_Y Q) ≃ Hom(N, G_X Q)`, from `Ra_{X,0}! ≅ Ra_{Y,0}! Rf₀!`. -/
noncomputable def derivedLowerShriekHomEquivOfComp (N : WeilComplex k₀ l X) :
    ((derivedLowerShriek k₀ l f).obj N ⟶ GY.obj Q) ≃ (N ⟶ GX.obj Q) where
  toFun φ := adjX.homEquiv _ _ (c.hom.app N ≫ (adjY.homEquiv _ _).symm φ)
  invFun ψ := adjY.homEquiv _ _ (c.inv.app N ≫ (adjX.homEquiv _ _).symm ψ)
  left_inv φ := by simp
  right_inv ψ := by simp

omit [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] in
lemma derivedLowerShriekHomEquivOfComp_naturality {N N' : WeilComplex k₀ l X} (t : N' ⟶ N)
    (φ : (derivedLowerShriek k₀ l f).obj N ⟶ GY.obj Q) :
    derivedLowerShriekHomEquivOfComp f aX aY adjX adjY c Q N'
        ((derivedLowerShriek k₀ l f).map t ≫ φ) =
      t ≫ derivedLowerShriekHomEquivOfComp f aX aY adjX adjY c Q N φ := by
  simp only [derivedLowerShriekHomEquivOfComp, Equiv.coe_fn_mk]
  rw [Adjunction.homEquiv_naturality_left_symm, ← adjX.homEquiv_naturality_left,
    ← Category.assoc, ← Category.assoc, c.hom.naturality t]
  rfl

lemma projectionIso_inv_naturality_right (M : WeilComplex k₀ l X) {T T' : WeilComplex k₀ l Y}
    (t : T' ⟶ T) :
    π.inv.app (M, T') ≫ (nativeConstructibleTensor k₀ l Y).map (Prod.mkHom (𝟙 _) t) =
      (derivedLowerShriek k₀ l f).map ((nativeConstructibleTensor k₀ l X).map
        (Prod.mkHom (𝟙 M) ((upperStar f).map t))) ≫ π.inv.app (M, T) := by
  have := π.inv.naturality (Prod.mkHom (𝟙 M) t)
  simp only [nativeCompactProjectionLeft, nativeCompactProjectionRight, Functor.comp_map,
    Functor.prod_map, Functor.id_map, CategoryTheory.Functor.map_id] at this
  exact this.symm

lemma projectionIso_inv_naturality_left {M M' : WeilComplex k₀ l X} (g : M' ⟶ M)
    (T : WeilComplex k₀ l Y) :
    π.inv.app (M', T) ≫
        (nativeConstructibleTensor k₀ l Y).map
          (Prod.mkHom ((derivedLowerShriek k₀ l f).map g) (𝟙 T)) =
      (derivedLowerShriek k₀ l f).map ((nativeConstructibleTensor k₀ l X).map
        (Prod.mkHom g (𝟙 _))) ≫ π.inv.app (M, T) := by
  have := π.inv.naturality (Prod.mkHom g (𝟙 T))
  simp only [nativeCompactProjectionLeft, nativeCompactProjectionRight, Functor.comp_map,
    Functor.prod_map, Functor.id_map, CategoryTheory.Functor.map_id] at this
  exact this.symm


/-- The bijection `Hom(T, 𝔻_Y Rf₀! M) ≃ Hom(T, Rf_* 𝔻_X M)` of the Verdier exchange. -/
noncomputable def verdierExchangeHomEquiv (M : WeilComplex k₀ l X) (T : WeilComplex k₀ l Y) :
    (T ⟶ ((derivedLowerShriek k₀ l f).op ⋙
        ObjectProperty.lift _ ((ObjectProperty.ι _).op ⋙
          ProEtaleWeilSheaf.derivedHom k₀ l Y (GY.obj Q).obj) (fun K ↦ hY K.unop)).obj (op M)) ≃
      (T ⟶ (ObjectProperty.lift _ ((ObjectProperty.ι _).op ⋙
          ProEtaleWeilSheaf.derivedHom k₀ l X (GX.obj Q).obj) (fun K ↦ hX K.unop) ⋙
            derivedLowerStar f).obj (op M)) :=
  (objectProperty k₀ l Y).fullyFaithfulι.homEquiv.trans <|
    (nativeConstructibleTensorHomEquiv ((derivedLowerShriek k₀ l f).obj M) (GY.obj Q)
      T).symm.trans <|
      (Equiv.mk (fun φ ↦ π.inv.app (M, T) ≫ φ) (fun ψ ↦ π.hom.app (M, T) ≫ ψ)
        (fun _ ↦ by simp) (fun _ ↦ by simp)).trans <|
        (derivedLowerShriekHomEquivOfComp f aX aY adjX adjY c Q _).trans <|
          (nativeConstructibleTensorHomEquiv M (GX.obj Q) ((upperStar f).obj T)).trans <|
            upperStarObjHomEquiv f T ((ObjectProperty.lift _
              ((ObjectProperty.ι _).op ⋙ ProEtaleWeilSheaf.derivedHom k₀ l X (GX.obj Q).obj)
                (fun K ↦ hX K.unop)).obj (op M))

lemma verdierExchangeHomEquiv_apply (M : WeilComplex k₀ l X) (T : WeilComplex k₀ l Y)
    (φ : T ⟶ ((derivedLowerShriek k₀ l f).op ⋙
        ObjectProperty.lift _ ((ObjectProperty.ι _).op ⋙
          ProEtaleWeilSheaf.derivedHom k₀ l Y (GY.obj Q).obj) (fun K ↦ hY K.unop)).obj (op M)) :
    verdierExchangeHomEquiv f aX aY adjX adjY c π Q hX hY M T φ =
      upperStarObjHomEquiv f T ((ObjectProperty.lift _
          ((ObjectProperty.ι _).op ⋙ ProEtaleWeilSheaf.derivedHom k₀ l X (GX.obj Q).obj)
            (fun K ↦ hX K.unop)).obj (op M))
        (nativeConstructibleTensorHomEquiv M (GX.obj Q) ((upperStar f).obj T)
          (derivedLowerShriekHomEquivOfComp f aX aY adjX adjY c Q
            ((nativeConstructibleTensor k₀ l X).obj (M, (upperStar f).obj T))
            (π.inv.app (M, T) ≫
              (nativeConstructibleTensorHomEquiv ((derivedLowerShriek k₀ l f).obj M) (GY.obj Q)
                T).symm φ.hom))) :=
  rfl

attribute [local irreducible] verdierExchangeHomEquiv upperStarObjHomEquiv
  nativeConstructibleTensorHomEquiv derivedLowerShriekHomEquivOfComp

lemma verdierExchangeHomEquiv_naturality_right (M : WeilComplex k₀ l X)
    {T T' : WeilComplex k₀ l Y} (t : T' ⟶ T)
    (φ : T ⟶ ((derivedLowerShriek k₀ l f).op ⋙
        ObjectProperty.lift _ ((ObjectProperty.ι _).op ⋙
          ProEtaleWeilSheaf.derivedHom k₀ l Y (GY.obj Q).obj) (fun K ↦ hY K.unop)).obj (op M)) :
    verdierExchangeHomEquiv f aX aY adjX adjY c π Q hX hY M T' (t ≫ φ) =
      t ≫ verdierExchangeHomEquiv f aX aY adjX adjY c π Q hX hY M T φ := by
  conv_lhs => rw [verdierExchangeHomEquiv_apply]
  conv_rhs => rw [verdierExchangeHomEquiv_apply]
  have h1 : (nativeConstructibleTensorHomEquiv ((derivedLowerShriek k₀ l f).obj M) (GY.obj Q)
      T').symm (t ≫ φ).hom =
      (nativeConstructibleTensor k₀ l Y).map (Prod.mkHom (𝟙 _) t) ≫
        (nativeConstructibleTensorHomEquiv ((derivedLowerShriek k₀ l f).obj M) (GY.obj Q)
          T).symm φ.hom :=
    nativeConstructibleTensorHomEquiv_symm_map_right _ _ t φ.hom
  have e1 : π.inv.app (M, T') ≫ (nativeConstructibleTensorHomEquiv
      ((derivedLowerShriek k₀ l f).obj M) (GY.obj Q) T').symm (t ≫ φ).hom =
      (derivedLowerShriek k₀ l f).map ((nativeConstructibleTensor k₀ l X).map
        (Prod.mkHom (𝟙 M) ((upperStar f).map t))) ≫ π.inv.app (M, T) ≫
          (nativeConstructibleTensorHomEquiv ((derivedLowerShriek k₀ l f).obj M) (GY.obj Q)
            T).symm φ.hom := by
    rw [h1, ← Category.assoc, projectionIso_inv_naturality_right, Category.assoc]
  refine (congrArg (fun z ↦ upperStarObjHomEquiv f T' ((ObjectProperty.lift _
      ((ObjectProperty.ι _).op ⋙ ProEtaleWeilSheaf.derivedHom k₀ l X (GX.obj Q).obj)
        (fun K ↦ hX K.unop)).obj (op M))
      (nativeConstructibleTensorHomEquiv M (GX.obj Q) ((upperStar f).obj T')
        (derivedLowerShriekHomEquivOfComp f aX aY adjX adjY c Q
          ((nativeConstructibleTensor k₀ l X).obj (M, (upperStar f).obj T')) z))) e1).trans ?_
  refine (congrArg (fun z ↦ upperStarObjHomEquiv f T' ((ObjectProperty.lift _
      ((ObjectProperty.ι _).op ⋙ ProEtaleWeilSheaf.derivedHom k₀ l X (GX.obj Q).obj)
        (fun K ↦ hX K.unop)).obj (op M))
      (nativeConstructibleTensorHomEquiv M (GX.obj Q) ((upperStar f).obj T') z))
    (derivedLowerShriekHomEquivOfComp_naturality f aX aY adjX adjY c Q _ _)).trans ?_
  refine (congrArg (fun z ↦ upperStarObjHomEquiv f T' ((ObjectProperty.lift _
      ((ObjectProperty.ι _).op ⋙ ProEtaleWeilSheaf.derivedHom k₀ l X (GX.obj Q).obj)
        (fun K ↦ hX K.unop)).obj (op M)) z)
    (nativeConstructibleTensorHomEquiv_map_right _ _ _ _)).trans ?_
  exact upperStarObjHomEquiv_map_left f t _ _

lemma verdierExchangeHomEquiv_naturality_left {M M' : (WeilComplex k₀ l X)ᵒᵖ} (g : M ⟶ M')
    (T : WeilComplex k₀ l Y)
    (φ : T ⟶ ((derivedLowerShriek k₀ l f).op ⋙
        ObjectProperty.lift _ ((ObjectProperty.ι _).op ⋙
          ProEtaleWeilSheaf.derivedHom k₀ l Y (GY.obj Q).obj) (fun K ↦ hY K.unop)).obj M) :
    verdierExchangeHomEquiv f aX aY adjX adjY c π Q hX hY M'.unop T
        (φ ≫ ((derivedLowerShriek k₀ l f).op ⋙
          ObjectProperty.lift _ ((ObjectProperty.ι _).op ⋙
            ProEtaleWeilSheaf.derivedHom k₀ l Y (GY.obj Q).obj) (fun K ↦ hY K.unop)).map g) =
      verdierExchangeHomEquiv f aX aY adjX adjY c π Q hX hY M.unop T φ ≫
        (ObjectProperty.lift _ ((ObjectProperty.ι _).op ⋙
          ProEtaleWeilSheaf.derivedHom k₀ l X (GX.obj Q).obj) (fun K ↦ hX K.unop) ⋙
            derivedLowerStar f).map g := by
  conv_lhs => rw [verdierExchangeHomEquiv_apply]
  conv_rhs => rw [verdierExchangeHomEquiv_apply]
  have h1 : (nativeConstructibleTensorHomEquiv ((derivedLowerShriek k₀ l f).obj M'.unop)
      (GY.obj Q) T).symm (φ ≫ ((derivedLowerShriek k₀ l f).op ⋙
          ObjectProperty.lift _ ((ObjectProperty.ι _).op ⋙
            ProEtaleWeilSheaf.derivedHom k₀ l Y (GY.obj Q).obj) (fun K ↦ hY K.unop)).map g).hom =
      (nativeConstructibleTensor k₀ l Y).map
          (Prod.mkHom ((derivedLowerShriek k₀ l f).map g.unop) (𝟙 T)) ≫
        (nativeConstructibleTensorHomEquiv ((derivedLowerShriek k₀ l f).obj M.unop) (GY.obj Q)
          T).symm φ.hom :=
    nativeConstructibleTensorHomEquiv_symm_map_left ((derivedLowerShriek k₀ l f).map g.unop) _ _
      φ.hom
  have e1 : π.inv.app (M'.unop, T) ≫ (nativeConstructibleTensorHomEquiv
      ((derivedLowerShriek k₀ l f).obj M'.unop) (GY.obj Q) T).symm
        (φ ≫ ((derivedLowerShriek k₀ l f).op ⋙ ObjectProperty.lift _ ((ObjectProperty.ι _).op ⋙
          ProEtaleWeilSheaf.derivedHom k₀ l Y (GY.obj Q).obj) (fun K ↦ hY K.unop)).map g).hom =
      (derivedLowerShriek k₀ l f).map ((nativeConstructibleTensor k₀ l X).map
        (Prod.mkHom g.unop (𝟙 _))) ≫ π.inv.app (M.unop, T) ≫
          (nativeConstructibleTensorHomEquiv ((derivedLowerShriek k₀ l f).obj M.unop) (GY.obj Q)
            T).symm φ.hom := by
    rw [h1, ← Category.assoc, projectionIso_inv_naturality_left, Category.assoc]
  refine (congrArg (fun z ↦ upperStarObjHomEquiv f T ((ObjectProperty.lift _
      ((ObjectProperty.ι _).op ⋙ ProEtaleWeilSheaf.derivedHom k₀ l X (GX.obj Q).obj)
        (fun K ↦ hX K.unop)).obj (op M'.unop))
      (nativeConstructibleTensorHomEquiv M'.unop (GX.obj Q) ((upperStar f).obj T)
        (derivedLowerShriekHomEquivOfComp f aX aY adjX adjY c Q
          ((nativeConstructibleTensor k₀ l X).obj (M'.unop, (upperStar f).obj T)) z))) e1).trans ?_
  refine (congrArg (fun z ↦ upperStarObjHomEquiv f T ((ObjectProperty.lift _
      ((ObjectProperty.ι _).op ⋙ ProEtaleWeilSheaf.derivedHom k₀ l X (GX.obj Q).obj)
        (fun K ↦ hX K.unop)).obj (op M'.unop))
      (nativeConstructibleTensorHomEquiv M'.unop (GX.obj Q) ((upperStar f).obj T) z))
    (derivedLowerShriekHomEquivOfComp_naturality f aX aY adjX adjY c Q _ _)).trans ?_
  refine (congrArg (fun z ↦ upperStarObjHomEquiv f T ((ObjectProperty.lift _
      ((ObjectProperty.ι _).op ⋙ ProEtaleWeilSheaf.derivedHom k₀ l X (GX.obj Q).obj)
        (fun K ↦ hX K.unop)).obj (op M'.unop)) z)
    (nativeConstructibleTensorHomEquiv_map_left g.unop _ _ _)).trans ?_
  exact upperStarObjHomEquiv_map_right f T ((ObjectProperty.lift _ ((ObjectProperty.ι _).op ⋙
    ProEtaleWeilSheaf.derivedHom k₀ l X (GX.obj Q).obj) (fun K ↦ hX K.unop)).map g) _

include adjX adjY in
/-- **Verdier exchange, natural form, over a base** (blueprint `fix-cor-verdier-exchange`): for
`a_X = f ≫ a_Y` and right adjoints `G_X`, `G_Y` of `Ra_{X,0}!`, `Ra_{Y,0}!`, the functors
`M ↦ RHom(Rf₀! M, G_Y Q)` and `M ↦ Rf_* RHom(M, G_X Q)` are isomorphic. The proof is the Yoneda
argument of `AlgebraicGeometry.WeilComplex.nonempty_iso_derivedLowerStar_of_adjunction`, whose
steps are natural in `M` (`AlgebraicGeometry.WeilComplex.verdierExchangeHomEquiv`). -/
theorem nonempty_verdierExchange_natIso_of_adjunction (h : f ≫ aY = aX) :
    Nonempty ((derivedLowerShriek k₀ l f).op ⋙
        ObjectProperty.lift _ ((ObjectProperty.ι _).op ⋙
          ProEtaleWeilSheaf.derivedHom k₀ l Y (GY.obj Q).obj) (fun K ↦ hY K.unop) ≅
      ObjectProperty.lift _ ((ObjectProperty.ι _).op ⋙
          ProEtaleWeilSheaf.derivedHom k₀ l X (GX.obj Q).obj) (fun K ↦ hX K.unop) ⋙
        derivedLowerStar f) := by
  subst h
  obtain ⟨π⟩ := nonempty_nativeCompactProjectionLeft_iso (k₀ := k₀) (l := l) f
  obtain ⟨c⟩ := nonempty_derivedLowerShriek_comp_iso (k₀ := k₀) (l := l) f aY
  exact ⟨NatIso.ofHomEquiv
    (fun M T ↦ verdierExchangeHomEquiv f _ aY adjX adjY c π Q hX hY M.unop T)
    (fun M _ _ t φ ↦ verdierExchangeHomEquiv_naturality_right f _ aY adjX adjY c π Q hX hY
      M.unop t φ)
    (fun g T φ ↦ verdierExchangeHomEquiv_naturality_left f _ aY adjX adjY c π Q hX hY g T φ)⟩

end NatExchange

variable (k₀ l) in
/-- The dualizing complex `ω_X = (Ra_X!)^{ra}(ℚ̄_ℓ)` of a `k₀`-scheme of finite type `X`, given a
right adjoint of `Ra_X!` (`AlgebraicGeometry.WeilComplex.dualizingComplex`, spelled out). -/
noncomputable abbrev dualizingComplexOfIsLeftAdjoint (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))] [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [(derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).IsLeftAdjoint] :
    WeilComplex k₀ l X :=
  (derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).rightAdjoint.obj
    (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀))))

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [(derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).IsLeftAdjoint]
  [(derivedLowerShriek k₀ l (Y ↘ Spec (CommRingCat.of k₀))).IsLeftAdjoint]

/-- **Verdier exchange, natural in `M`** (blueprint `fix-cor-verdier-exchange`): for a separated
morphism of finite type `f : X ⟶ Y`, `𝔻_Y (Rf₀! M) ≅ Rf_* (𝔻_X M)` naturally in the Weil
complex `M`. Here `𝔻 = RHom(-, ω)` is the derived internal hom into the dualizing complex
`ω = (Ra!)^{ra}(ℚ̄_ℓ)`, lifted to Weil complexes along any proofs `hX`, `hY` that it lands there.

This is an input from the Verdier duality section, stated here because the Verdier dual is only
defined in `WeilConjectures.WeilSheaf.VerdierDual`, which imports this file. The blueprint proves
it by Yoneda from the projection formula for `Rf₀!`, the tensor–hom adjunction of `RHom`, the
adjunction `f^* ⊣ Rf_*` and `Rf^! ω_Y ≅ ω_X`; the objectwise form is
`AlgebraicGeometry.WeilComplex.nonempty_verdierDual_derivedLowerShriek_iso`. -/
theorem nonempty_verdierDual_derivedLowerShriek_natIso
    (hX : ∀ K : WeilComplex k₀ l X, WeilComplex.objectProperty k₀ l X
      ((ProEtaleWeilSheaf.derivedHom k₀ l X (dualizingComplexOfIsLeftAdjoint k₀ l X).obj).obj
        (op K.obj)))
    (hY : ∀ K : WeilComplex k₀ l Y, WeilComplex.objectProperty k₀ l Y
      ((ProEtaleWeilSheaf.derivedHom k₀ l Y (dualizingComplexOfIsLeftAdjoint k₀ l Y).obj).obj
        (op K.obj))) :
    Nonempty ((derivedLowerShriek k₀ l f).op ⋙
        ObjectProperty.lift _ ((ObjectProperty.ι _).op ⋙
          ProEtaleWeilSheaf.derivedHom k₀ l Y (dualizingComplexOfIsLeftAdjoint k₀ l Y).obj)
          (fun K ↦ hY K.unop) ≅
      ObjectProperty.lift _ ((ObjectProperty.ι _).op ⋙
          ProEtaleWeilSheaf.derivedHom k₀ l X (dualizingComplexOfIsLeftAdjoint k₀ l X).obj)
          (fun K ↦ hX K.unop) ⋙ derivedLowerStar f) :=
  nonempty_verdierExchange_natIso_of_adjunction f (X ↘ Spec (CommRingCat.of k₀))
    (Y ↘ Spec (CommRingCat.of k₀)) (Adjunction.ofIsLeftAdjoint _) (Adjunction.ofIsLeftAdjoint _)
    (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀)))) hX hY
    (comp_over f _)

end WeilComplex

end AlgebraicGeometry
