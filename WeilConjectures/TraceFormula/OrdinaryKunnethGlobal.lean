/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.Kunneth
public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeCoherence
public import WeilConjectures.TraceFormula.ProperKunneth
public import WeilConjectures.TraceFormula.GenericBaseChangePullback
public import WeilConjectures.TraceFormula.OrdinaryKunnethProjection
public import WeilConjectures.TraceFormula.FieldDualizable
public import WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMorphismDualizable
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SquareComparisonCoherence
public import WeilConjectures.Tactic.NormalizeProofConstant
public import WeilConjectures.Tactic.ExactModProofs

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]




/-- The transposes along the restricted adjunction `Lf^* ⊣ Rf_*` on `Dᵇc` are those of the ambient
adjunction. -/
lemma homEquiv_hom_boundedConstructibleUpperStarLowerStarAdjunction {Y : Over (Spec (.of k))}
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] (f : X ⟶ Y)
    (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (φ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).obj K ⟶ L) :
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ f).homEquiv K L φ).hom =
      (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) f.left).homEquiv
        K.obj L.obj φ.hom := by
  rw [boundedConstructibleUpperStarLowerStarAdjunction, Adjunction.restrictFullyFaithful_homEquiv_apply]
  simp [boundedConstructibleUpperStarCompatibility, boundedConstructibleLowerStarCompatibility,
    ObjectProperty.liftCompιIso, Adjunction.homEquiv_unit]

/-- The counits of the restricted adjunction `Lf^* ⊣ Rf_*` on `Dᵇc` are those of the ambient
adjunction. -/
lemma counit_app_hom_boundedConstructibleUpperStarLowerStarAdjunction {Y : Over (Spec (.of k))}
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] (f : X ⟶ Y)
    (L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ f).counit.app L).hom =
      (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) f.left).counit.app
        L.obj := by
  have h := Adjunction.map_restrictFullyFaithful_counit_app
    (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) f.left)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleUpperStarCompatibility (Profinite.padicAlgClRingObj ℓ) ℓ f).symm
    (boundedConstructibleLowerStarCompatibility ℓ f).symm L
  refine h.trans ?_
  simp [boundedConstructibleUpperStarCompatibility, boundedConstructibleLowerStarCompatibility,
    ObjectProperty.liftCompιIso]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
end AlgebraicGeometry.ProEtale.CondensedRing

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) [F.OplaxMonoidal]

/-- A tensor product of morphisms `bᵢ : Uᵢ ⟶ G Mᵢ` followed by a lax tensor map `μ` of `G` whose
transpose is the tensor product of the counits is the transpose of the oplax structure of `F`
followed by the tensor product of the transposes `cᵢ` of the `bᵢ`. -/
lemma tensorHom_comp_eq_homEquiv_δ (μ : ∀ M N, G.obj M ⊗ G.obj N ⟶ G.obj (M ⊗ N))
    (hμ : ∀ M N, F.map (μ M N) ≫ adj.counit.app (M ⊗ N) =
      Functor.OplaxMonoidal.δ F _ _ ≫ (adj.counit.app M ⊗ₘ adj.counit.app N))
    {U₁ U₂ : D} {M N : C} (b₁ : U₁ ⟶ G.obj M) (b₂ : U₂ ⟶ G.obj N) (c₁ : F.obj U₁ ⟶ M)
    (c₂ : F.obj U₂ ⟶ N) (hb₁ : F.map b₁ ≫ adj.counit.app M = c₁)
    (hb₂ : F.map b₂ ≫ adj.counit.app N = c₂) :
    (b₁ ⊗ₘ b₂) ≫ μ M N = adj.homEquiv _ _ (Functor.OplaxMonoidal.δ F U₁ U₂ ≫ (c₁ ⊗ₘ c₂)) := by
  apply (adj.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, homEquiv_counit, Functor.map_comp, Category.assoc, hμ,
    ← Functor.OplaxMonoidal.δ_natural_assoc, tensorHom_comp_tensorHom, hb₁, hb₂]

section Restrict

variable {P : ObjectProperty C} [P.IsMonoidal] {Q : ObjectProperty D} [Q.IsMonoidal]
  {F' : D ⥤ C} [F'.Monoidal] {G' : C ⥤ D} (adj' : F' ⊣ G')
  (hF : ∀ X : Q.FullSubcategory, P (F'.obj X.obj)) (hG : ∀ X : P.FullSubcategory, Q (G'.obj X.obj))

/-- The Künneth transpose of the restriction of an adjunction `F ⊣ G` to full monoidal
subcategories is the Künneth transpose of `F ⊣ G`. -/
lemma ι_map_homEquiv_δ_tensorHom_restrictFullyFaithful {U₁ U₂ : Q.FullSubcategory}
    {A₁ A₂ : P.FullSubcategory} (c₁ : (P.lift (Q.ι ⋙ F') hF).obj U₁ ⟶ A₁)
    (c₂ : (P.lift (Q.ι ⋙ F') hF).obj U₂ ⟶ A₂) :
    Q.ι.map ((adj'.restrictFullyFaithful Q.fullyFaithfulι P.fullyFaithfulι
      (P.liftCompιIso (Q.ι ⋙ F') hF).symm (Q.liftCompιIso (P.ι ⋙ G') hG).symm).homEquiv _ _
        (Functor.OplaxMonoidal.δ (P.lift (Q.ι ⋙ F') hF) U₁ U₂ ≫ (c₁ ⊗ₘ c₂))) =
      adj'.homEquiv _ _ (Functor.OplaxMonoidal.δ F' U₁.obj U₂.obj ≫ (P.ι.map c₁ ⊗ₘ P.ι.map c₂)) := by
  rw [restrictFullyFaithful_homEquiv_apply, Functor.FullyFaithful.map_preimage, homEquiv_unit]
  simp only [ObjectProperty.liftCompιIso, Iso.symm_hom, Iso.refl_inv, Functor.map_comp]
  erw [Functor.map_id, Category.id_comp, Category.comp_id]
  rfl

end Restrict

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {P P' X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The underlying morphism of an `eqToHom` in a full subcategory. -/
lemma _root_.CategoryTheory.ObjectProperty.FullSubcategory.eqToHom_hom' {C : Type*} [Category C]
    {Q : ObjectProperty C} {K K' : Q.FullSubcategory} (h : K = K') :
    (eqToHom h).hom = eqToHom (congrArg ObjectProperty.FullSubcategory.obj h) := by
  subst h
  rfl

/-- The inverse composition isomorphisms of the pullbacks on `Dᵇc` are the ambient ones. -/
lemma boundedConstructibleUpperStarComp_inv_app_hom' {Z : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] (f : P ⟶ X) (g : X ⟶ Z)
    (K : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f g).inv.app K).hom =
      (leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ℓ) f.left g.left).inv.app K.obj := by
  simp [boundedConstructibleUpperStarComp, boundedConstructibleUpperStarCompatibility,
    ObjectProperty.liftCompιIso]

/-- The transported counit of a commutative square is, on the ambient derived categories, the
transpose of the base change morphism of the square. -/
lemma map_baseChangeMap_app_comp_counit {q : P ⟶ P'} {p : P ⟶ X} {p' : P' ⟶ Y} {f : X ⟶ Y}
    (w : q ≫ p' = p ≫ f) (sq : CommSq p.left q.left f.left p'.left)
    (B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    L((q.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map
        ((baseChangeMap (Profinite.padicAlgClRingObj ℓ) sq).app B.obj) ≫
      (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) q.left).counit.app
        (L((p.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj B.obj) =
      (prodUpperStarCounit ℓ w B).hom := by
  have H := Adjunction.exchangeRight_app_comp_counit' _
    (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) q.left)
    (pullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) sq)
    (baseChangeMap (Profinite.padicAlgClRingObj ℓ) sq) rfl B.obj
  have H2 : (prodUpperStarCounit ℓ w B).hom = (pullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) sq).hom.app _ ≫
      L((p.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map
        ((derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) f.left).counit.app B.obj) := by
    rw [pullbackSquareComparison_hom_app]
    simp only [prodUpperStarCounit, ObjectProperty.FullSubcategory.comp_hom,
      boundedConstructibleUpperStarComp_hom_app_hom, boundedConstructibleUpperStarComp_inv_app_hom',
      boundedConstructibleUpperStar_map_hom, ObjectProperty.FullSubcategory.eqToHom_hom',
      counit_app_hom_boundedConstructibleUpperStarLowerStarAdjunction, Category.assoc]
    rfl
  exact H.trans H2.symm

section Bridge

variable {Q X₁ X₂ Y₁ Y₂ : Over (Spec (.of k))}
  [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom] [IsSeparated Q.hom]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X₂.hom] [QuasiCompact X₂.hom] [IsSeparated X₂.hom]
  [LocallyOfFiniteType Y₁.hom] [QuasiCompact Y₁.hom] [IsSeparated Y₁.hom]
  [LocallyOfFiniteType Y₂.hom] [QuasiCompact Y₂.hom] [IsSeparated Y₂.hom]

/-- The oplax structure of the pullback on `Dᵇc` is that of the ambient pullback. -/
lemma δ_hom_boundedConstructibleUpperStar (q : P ⟶ Q)
    (A B : Dᵇc(Q.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ q)
      A B).hom = Functor.OplaxMonoidal.δ L((q.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) A.obj B.obj := by
  normalize_proof_constant AlgebraicGeometry.ProEtale.pointLowerStar._proof_1
  rfl

/-- The tensor product of objects of `Dᵇc` is the ambient one. -/
lemma tensorObj_obj_boundedConstructible (A B : Dᵇc(P.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (A ⊗ B).obj = A.obj ⊗ B.obj :=
  rfl

/-- The direct image on `Dᵇc` is the ambient one on objects. -/
lemma boundedConstructibleLowerStar_obj_obj' (q : P ⟶ Q)
    (A : Dᵇc(P.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleLowerStar ℓ q).obj A).obj =
      R((q.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A.obj :=
  rfl

/-- The tensor product of morphisms of `Dᵇc` is the ambient one. -/
lemma tensorHom_hom_boundedConstructible {A A' B B' : Dᵇc(P.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (f : A ⟶ A') (g : B ⟶ B') : (f ⊗ₘ g).hom = f.hom ⊗ₘ g.hom :=
  rfl

end Bridge

/-! ### The Künneth formula on `Dᵇc` -/

section Kunneth

variable {Q R X₁ X₂ Y₁ Y₂ : Over (Spec (.of k))}
  [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom] [IsSeparated Q.hom]
  [LocallyOfFiniteType R.hom] [QuasiCompact R.hom] [IsSeparated R.hom]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X₂.hom] [QuasiCompact X₂.hom] [IsSeparated X₂.hom]
  [LocallyOfFiniteType Y₁.hom] [QuasiCompact Y₁.hom] [IsSeparated Y₁.hom]
  [LocallyOfFiniteType Y₂.hom] [QuasiCompact Y₂.hom] [IsSeparated Y₂.hom]

/-- **The Künneth map of a factorization `q = r ≫ s`** (the criterion behind
`isIso_homEquiv_δ_tensorHom_prodUpperStarCounit`, without properness): let `q ≫ πᵢ = pᵢ ≫ fᵢ` be
commutative squares with `q = r ≫ s` and `p₂ = r ≫ ρ₂`. If the base change morphisms of the
squares `p₁ ≫ f₁ = r ≫ s ≫ π₁` and `ρ₂ ≫ f₂ = s ≫ π₂`, the projection morphism of `r` and the left
projection morphism of `s` are isomorphisms at the relevant objects, then the Künneth map, the
transpose of `Lq^* (Lπ₁^* Rf₁* B₁ ⊗ Lπ₂^* Rf₂* B₂) ⟶ Lp₁^* B₁ ⊗ Lp₂^* B₂`, is an isomorphism. -/
theorem isIso_homEquiv_δ_tensorHom_prodUpperStarCounit_of_isIso {q : P ⟶ Q} {p₁ : P ⟶ X₁}
    {p₂ : P ⟶ X₂} {π₁ : Q ⟶ Y₁} {π₂ : Q ⟶ Y₂} {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂} (r : P ⟶ R)
    (s : R ⟶ Q) (ρ₂ : R ⟶ X₂) (hq : r ≫ s = q) (hp₂ : r ≫ ρ₂ = p₂) (w₁ : q ≫ π₁ = p₁ ≫ f₁)
    (w₂ : q ≫ π₂ = p₂ ≫ f₂) (sq₁ : CommSq p₁ r f₁ (s ≫ π₁)) (sq₂ : CommSq ρ₂ s f₂ π₂)
    (B₁ : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (B₂ : Dᵇc(X₂.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (h₁ : IsIso ((boundedConstructibleBaseChange ℓ sq₁).app B₁))
    (h₂ : IsIso ((boundedConstructibleBaseChange ℓ sq₂).app B₂))
    (hr : IsIso ((boundedConstructibleUpperStarLowerStarAdjunction ℓ r).projectionMorphism
      ((boundedConstructibleUpperStar _ ℓ p₁).obj B₁) ((boundedConstructibleUpperStar _ ℓ ρ₂).obj B₂)))
    (hs : IsIso ((boundedConstructibleUpperStarLowerStarAdjunction ℓ s).leftProjectionMorphism
      ((boundedConstructibleUpperStar _ ℓ π₁).obj ((boundedConstructibleLowerStar ℓ f₁).obj B₁))
      ((boundedConstructibleUpperStar _ ℓ ρ₂).obj B₂))) :
    IsIso ((boundedConstructibleUpperStarLowerStarAdjunction ℓ q).homEquiv _ _
      (Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar _ ℓ q) _ _ ≫
        (prodUpperStarCounit ℓ w₁ B₁ ⊗ₘ prodUpperStarCounit ℓ w₂ B₂))) := by
  subst hq hp₂
  have hc₁ := upperStarComp_inv_app_comp_prodUpperStarCounit_right ℓ w₁ sq₁.w.symm B₁
  have : IsIso ((boundedConstructibleUpperStarLowerStarAdjunction ℓ r).homEquiv _ _
      ((boundedConstructibleUpperStarComp _ ℓ r s).inv.app _ ≫ prodUpperStarCounit ℓ w₁ B₁)) := by
    rw [hc₁, Adjunction.homEquiv_naturality_left]
    have : IsIso ((boundedConstructibleUpperStarLowerStarAdjunction ℓ r).homEquiv _ _
        (prodUpperStarCounit ℓ sq₁.w.symm B₁)) := by
      rw [homEquiv_prodUpperStarCounit]
      exact h₁
    infer_instance
  have : IsIso ((boundedConstructibleUpperStarLowerStarAdjunction ℓ s).homEquiv _ _
      (prodUpperStarCounit ℓ sq₂.w.symm B₂)) := by
    rw [homEquiv_prodUpperStarCounit]
    exact h₂
  exact Adjunction.isIso_homEquiv_δ_tensorHom
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ r)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ s)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (r ≫ s))
    (boundedConstructibleUpperStarComp _ ℓ r s)
    (boundedConstructibleUpperStarComp_hom_app_tensor_δ ℓ r s) _ _
    (prodUpperStarCounit ℓ sq₂.w.symm B₂) ((boundedConstructibleUpperStarComp _ ℓ r ρ₂).inv.app B₂)
    (upperStarComp_inv_app_comp_prodUpperStarCounit_left ℓ w₂ sq₂.w.symm B₂)

/-- **The Künneth formula for global sections on `Dᵇc`**: for a cartesian square
`P = X ×_k Y` of separated `k`-schemes of finite type and `A ∈ Dᵇc(X)`, `B ∈ Dᵇc(Y)`, the Künneth
map `RΓ(X, A) ⊗ RΓ(Y, B) ⟶ RΓ(P, Lp₁^* A ⊗ Lp₂^* B)` is an isomorphism. It is the Künneth map of
the factorization `P ⟶ Y ⟶ Spec k`: generic base change along `Y ⟶ Spec k`
(`isIso_boundedConstructibleBaseChange_of_isPullback_toPoint`), the relative Künneth formula
for `p₂` (`isIso_projectionMorphism_upperStar_of_isPullback`) and the projection formula over the
point, where every object is dualizable (`isDualizable_point`). -/
theorem isIso_homEquiv_δ_tensorHom_prodUpperStarCounit_of_isPullback {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    {p₁ : P ⟶ X} {p₂ : P ⟶ Y}
    (h : IsPullback p₁.left p₂.left X.hom Y.hom) {q : P ⟶ point k} {a : X ⟶ point k}
    {b : Y ⟶ point k} (w₁ : q ≫ 𝟙 (point k) = p₁ ≫ a) (w₂ : q ≫ 𝟙 (point k) = p₂ ≫ b)
    (A : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (B : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((boundedConstructibleUpperStarLowerStarAdjunction ℓ q).homEquiv _ _
      (Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar _ ℓ q) _ _ ≫
        (prodUpperStarCounit ℓ w₁ A ⊗ₘ prodUpperStarCounit ℓ w₂ B))) := by
  obtain rfl : a = toPoint X := (isTerminalPoint k).hom_ext _ _
  obtain rfl : b = toPoint Y := (isTerminalPoint k).hom_ext _ _
  obtain rfl : q = p₂ ≫ toPoint Y := (isTerminalPoint k).hom_ext _ _
  have key : ∀ (g : Y ⟶ point k) (sq : CommSq p₁ p₂ (toPoint X) g), g = toPoint Y →
      IsIso (boundedConstructibleBaseChange ℓ sq) := by
    rintro g sq rfl
    exact isIso_boundedConstructibleBaseChange_of_isPullback_toPoint ℓ sq h
  have sq₂ : CommSq (𝟙 Y) (toPoint Y) (toPoint Y) (𝟙 (point k)) := ⟨by simp⟩
  have h₂ := isIso_boundedConstructibleBaseChange_of_isIso ℓ sq₂
  have h₁ := key _ ⟨(isTerminalPoint k).hom_ext _ _⟩ (Category.comp_id _)
  exact isIso_homEquiv_δ_tensorHom_prodUpperStarCounit_of_isIso ℓ p₂ (toPoint Y) (𝟙 Y) rfl
    (Category.comp_id _) w₁ w₂ _ sq₂ A B inferInstance inferInstance
    (isIso_projectionMorphism_upperStar_of_isPullback ℓ h A _)
    (Adjunction.isIso_leftProjectionMorphism_of_isDualizable _ (isDualizable_point ℓ _) _)

end Kunneth

/-! ### The ordinary Künneth formula on the ambient derived categories -/

section Ambient

/-- The ordinary Künneth map is the transpose of the oplax structure of `Lk^*` followed by the
tensor product of the transposes of the base change morphisms. -/
lemma lowerStarKunnethMap'_eq_homEquiv (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X X₁ Y Y₁ Z Z₁ : Scheme.{u}} {f₁ : Z ⟶ X} {f₂ : Z ⟶ Y}
    {g : X ⟶ X₁} {h : Y ⟶ Y₁} {k : Z ⟶ Z₁} {e₁ : Z₁ ⟶ X₁} {e₂ : Z₁ ⟶ Y₁}
    (sq₁ : CommSq f₁ k g e₁) (sq₂ : CommSq f₂ k h e₂)
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    lowerStarKunnethMap' Λ sq₁ sq₂ A B =
      (derivedUpperStarLowerStarAdjunction Λ k).homEquiv _ _
        (Functor.OplaxMonoidal.δ L((k)^*⟦Λ⟧) _ _ ≫
          ((L((k)^*⟦Λ⟧).map ((baseChangeMap Λ sq₁).app A) ≫
              (derivedUpperStarLowerStarAdjunction Λ k).counit.app _) ⊗ₘ
            (L((k)^*⟦Λ⟧).map ((baseChangeMap Λ sq₂).app B) ≫
              (derivedUpperStarLowerStarAdjunction Λ k).counit.app _))) :=
  Adjunction.tensorHom_comp_eq_homEquiv_δ (derivedUpperStarLowerStarAdjunction Λ k)
    (lowerStarTensorMap' Λ k) (lowerStarTensorMap'_comp_counit Λ k) _ _ _ _ rfl rfl

variable {K : Type u} [Field K] [Fact (ringChar K).Prime] [Fact (ringChar K ≠ ℓ)]
  {X Y P : Over (Spec (.of K))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]

end Ambient

section BridgeKunneth

variable {Q X₁ X₂ Y₁ Y₂ : Over (Spec (.of k))}
  [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom] [IsSeparated Q.hom]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X₂.hom] [QuasiCompact X₂.hom] [IsSeparated X₂.hom]
  [LocallyOfFiniteType Y₁.hom] [QuasiCompact Y₁.hom] [IsSeparated Y₁.hom]
  [LocallyOfFiniteType Y₂.hom] [QuasiCompact Y₂.hom] [IsSeparated Y₂.hom]

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- `lowerStarKunnethMap'_eq_homEquiv` for the coefficients `ℚ̄_ℓ`, so that its statement
carries the same instance proofs as the other statements on `Dᵇc`. -/
lemma lowerStarKunnethMap'_eq_homEquiv_padicAlgCl {X X₁ Y Y₁ Z Z₁ : Scheme.{u}} {f₁ : Z ⟶ X}
    {f₂ : Z ⟶ Y} {g : X ⟶ X₁} {h : Y ⟶ Y₁} {k : Z ⟶ Z₁} {e₁ : Z₁ ⟶ X₁} {e₂ : Z₁ ⟶ Y₁}
    (sq₁ : CommSq f₁ k g e₁) (sq₂ : CommSq f₂ k h e₂)
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))) :
    lowerStarKunnethMap' (Profinite.padicAlgClRingObj ℓ) sq₁ sq₂ A B =
      (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) k).homEquiv _ _
        (Functor.OplaxMonoidal.δ L((k)^*⟦Profinite.padicAlgClRingObj ℓ⟧) _ _ ≫
          ((L((k)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map
              ((baseChangeMap (Profinite.padicAlgClRingObj ℓ) sq₁).app A) ≫
              (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) k).counit.app _) ⊗ₘ
            (L((k)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map
              ((baseChangeMap (Profinite.padicAlgClRingObj ℓ) sq₂).app B) ≫
              (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) k).counit.app _))) := by
  exact_mod_proofs lowerStarKunnethMap'_eq_homEquiv (Profinite.padicAlgClRingObj ℓ) sq₁ sq₂ A B

/-- **The ordinary Künneth map on `Dᵇc`**: the ordinary Künneth map of bounded constructible
complexes (`lowerStarKunnethMap'`) is the underlying morphism of the transpose along
`Lq^* ⊣ Rq_*` on `Dᵇc` of the oplax structure of `Lq^*` followed by the transported counits
(`prodUpperStarCounit`). -/
lemma lowerStarKunnethMap'_eq_hom {q : P ⟶ Q} {p₁ : P ⟶ X₁} {p₂ : P ⟶ X₂} {π₁ : Q ⟶ Y₁}
    {π₂ : Q ⟶ Y₂} {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂} (w₁ : q ≫ π₁ = p₁ ≫ f₁)
    (w₂ : q ≫ π₂ = p₂ ≫ f₂) (sq₁ : CommSq p₁.left q.left f₁.left π₁.left)
    (sq₂ : CommSq p₂.left q.left f₂.left π₂.left)
    (B₁ : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (B₂ : Dᵇc(X₂.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    lowerStarKunnethMap' (Profinite.padicAlgClRingObj ℓ) sq₁ sq₂ B₁.obj B₂.obj =
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ q).homEquiv _ _
        (Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ q)
          _ _ ≫ (prodUpperStarCounit ℓ w₁ B₁ ⊗ₘ prodUpperStarCounit ℓ w₂ B₂))).hom := by
  sorry

/-- **The ordinary Künneth formula for global sections**, for squares of morphisms over the base
point, on bounded constructible complexes. -/
theorem isIso_lowerStarKunnethMap'_of_isPullback_point {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    {p₁ : P ⟶ X} {p₂ : P ⟶ Y}
    (h : IsPullback p₁.left p₂.left X.hom Y.hom) {q : P ⟶ point k} {a : X ⟶ point k}
    {b : Y ⟶ point k} (w₁ : q ≫ 𝟙 (point k) = p₁ ≫ a) (w₂ : q ≫ 𝟙 (point k) = p₂ ≫ b)
    (sq₁ : CommSq p₁.left q.left a.left (Over.Hom.left (𝟙 (point k))))
    (sq₂ : CommSq p₂.left q.left b.left (Over.Hom.left (𝟙 (point k))))
    (A : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (B : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (lowerStarKunnethMap' (Profinite.padicAlgClRingObj ℓ) sq₁ sq₂ A.obj B.obj) := by
  rw [lowerStarKunnethMap'_eq_hom ℓ w₁ w₂ sq₁ sq₂ A B]
  have := isIso_homEquiv_δ_tensorHom_prodUpperStarCounit_of_isPullback ℓ h w₁ w₂ A B
  exact (ObjectProperty.isIso_hom_iff _).mpr this

end BridgeKunneth


section Final

set_option allowUnsafeReducibility true in
attribute [local reducible] Over.mk Over.homMk CostructuredArrow.mk CostructuredArrow.homMk

variable {K : Type u} [Field K] [Fact (ringChar K).Prime] [Fact (ringChar K ≠ ℓ)]
  {X Y P : Over (Spec (.of K))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- **The ordinary Künneth formula over a field**, for global sections. -/
theorem isIso_lowerStarKunnethMap'_of_isPullback (p₁ : P.left ⟶ X.left)
    (p₂ : P.left ⟶ Y.left)
    (w₁ : p₁ ≫ X.hom = P.hom ≫ 𝟙 _) (w₂ : p₂ ≫ Y.hom = P.hom ≫ 𝟙 _)
    (h : IsPullback p₁ p₂ X.hom Y.hom)
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)))
    (hA : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left) A)
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left)))
    (hB : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left) B) :
    IsIso (lowerStarKunnethMap' (Profinite.padicAlgClRingObj ℓ)
      (⟨w₁⟩ : CommSq p₁ P.hom X.hom (𝟙 _)) (⟨w₂⟩ : CommSq p₂ P.hom Y.hom (𝟙 _)) A B) := by
  exact_mod_proofs isIso_lowerStarKunnethMap'_of_isPullback_point ℓ
    (p₁ := (Over.homMk p₁ (w₁.trans (Category.comp_id _)) : P ⟶ X))
    (p₂ := (Over.homMk p₂ (w₂.trans (Category.comp_id _)) : P ⟶ Y)) h
    (q := (Over.homMk P.hom (Category.comp_id _) : P ⟶ point K))
    (a := (Over.homMk X.hom (Category.comp_id _) : X ⟶ point K))
    (b := (Over.homMk Y.hom (Category.comp_id _) : Y ⟶ point K))
    (Over.OverMorphism.ext w₁.symm) (Over.OverMorphism.ext w₂.symm) ⟨w₁⟩ ⟨w₂⟩ ⟨A, hA⟩ ⟨B, hB⟩
end Final

end AlgebraicGeometry.ProEtale.CondensedRing
