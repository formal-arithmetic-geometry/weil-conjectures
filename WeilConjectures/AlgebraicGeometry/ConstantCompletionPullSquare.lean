/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImage
import WeilConjectures.CategoryTheory.Sites.ConstantRingSheafEndomorphism
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImage
import all WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackAdjunctionSupplement

/-!
# Commutation of constant-coefficient module pullbacks

Given four inverse images of sheaves of sets with algebraic lifts (`InverseImageData`) and an
isomorphism `sq : Lg ⋙ Lk ≅ Lf ⋙ Lh`, the composite constant-coefficient module pullbacks
are isomorphic by a unique isomorphism compatible with the inverse-image insertions
(`CategoryTheory.ConstantCompletion.pullSquare_existsUnique`).

## Implementation details

The isomorphism is built on underlying sheaves of sets as the composite of the inverse of
the first insertion, `sq` and the second insertion. It is linear because both insertions
transport the graphs of addition and scalar multiplication (`BinaryCompat`); comparing the
two transports through the product test sheaf shows that the comparison preserves the
operations, once the two induced identifications of the constant ring sheaves agree. The
latter holds because their difference is a natural, additive and unital endomorphism of the
constant ring sheaves (`CategoryTheory.constantSheaf_forget_natTrans_eq_id`).
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.ConstantCompletion

variable {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
  {J : GrothendieckTopology C} {J' : GrothendieckTopology D} {J'' : GrothendieckTopology E}

/-- A family of maps out of inverse images transports a sectionwise binary operation:
the inverse image of the graph of the operation lands in the graph of the target operation. -/
private def BinaryCompat (L : Sheaf J (Type u) ⥤ Sheaf J' (Type u))
    {P₁ P₂ P₃ : Sheaf J (Type u)} {Q₁ Q₂ Q₃ : Sheaf J' (Type u)}
    (op : ∀ U, P₁.obj.obj U → P₂.obj.obj U → P₃.obj.obj U)
    (op' : ∀ V, Q₁.obj.obj V → Q₂.obj.obj V → Q₃.obj.obj V)
    (ψ₁ : L.obj P₁ ⟶ Q₁) (ψ₂ : L.obj P₂ ⟶ Q₂) (ψ₃ : L.obj P₃ ⟶ Q₃) : Prop :=
  ∀ (T : Sheaf J (Type u)) (a : T ⟶ P₁) (b : T ⟶ P₂) (t : T ⟶ P₃),
    (∀ U x, t.hom.app U x = op U (a.hom.app U x) (b.hom.app U x)) →
      ∀ V (z : (L.obj T).obj.obj V), ψ₃.hom.app V ((L.map t).hom.app V z) =
        op' V (ψ₁.hom.app V ((L.map a).hom.app V z)) (ψ₂.hom.app V ((L.map b).hom.app V z))

/-- The nullary version: a sectionwise constant is transported to a sectionwise constant. -/
private def NullaryCompat (L : Sheaf J (Type u) ⥤ Sheaf J' (Type u))
    {P : Sheaf J (Type u)} {Q : Sheaf J' (Type u)}
    (c : ∀ U, P.obj.obj U) (c' : ∀ V, Q.obj.obj V) (ψ : L.obj P ⟶ Q) : Prop :=
  ∀ (T : Sheaf J (Type u)) (a : T ⟶ P), (∀ U x, a.hom.app U x = c U) →
    ∀ V (z : (L.obj T).obj.obj V), ψ.hom.app V ((L.map a).hom.app V z) = c' V

private theorem BinaryCompat.comp {L : Sheaf J (Type u) ⥤ Sheaf J' (Type u)}
    {L' : Sheaf J' (Type u) ⥤ Sheaf J'' (Type u)}
    {P₁ P₂ P₃ : Sheaf J (Type u)} {Q₁ Q₂ Q₃ : Sheaf J' (Type u)}
    {S₁ S₂ S₃ : Sheaf J'' (Type u)}
    {op : ∀ U, P₁.obj.obj U → P₂.obj.obj U → P₃.obj.obj U}
    {op' : ∀ V, Q₁.obj.obj V → Q₂.obj.obj V → Q₃.obj.obj V}
    {op'' : ∀ W, S₁.obj.obj W → S₂.obj.obj W → S₃.obj.obj W}
    {ψ₁ : L.obj P₁ ⟶ Q₁} {ψ₂ : L.obj P₂ ⟶ Q₂} {ψ₃ : L.obj P₃ ⟶ Q₃}
    {χ₁ : L'.obj Q₁ ⟶ S₁} {χ₂ : L'.obj Q₂ ⟶ S₂} {χ₃ : L'.obj Q₃ ⟶ S₃}
    (hψ : BinaryCompat L op op' ψ₁ ψ₂ ψ₃) (hχ : BinaryCompat L' op' op'' χ₁ χ₂ χ₃) :
    BinaryCompat (L ⋙ L') op op'' (L'.map ψ₁ ≫ χ₁) (L'.map ψ₂ ≫ χ₂) (L'.map ψ₃ ≫ χ₃) := by
  intro T a b t h W z
  have := hχ (L.obj T) (L.map a ≫ ψ₁) (L.map b ≫ ψ₂) (L.map t ≫ ψ₃) (hψ T a b t h) W z
  simp only [Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply] at this
  exact this


private theorem NullaryCompat.comp {L : Sheaf J (Type u) ⥤ Sheaf J' (Type u)}
    {L' : Sheaf J' (Type u) ⥤ Sheaf J'' (Type u)}
    {P : Sheaf J (Type u)} {Q : Sheaf J' (Type u)} {S : Sheaf J'' (Type u)}
    {c : ∀ U, P.obj.obj U} {c' : ∀ V, Q.obj.obj V} {c'' : ∀ W, S.obj.obj W}
    {ψ : L.obj P ⟶ Q} {χ : L'.obj Q ⟶ S}
    (hψ : NullaryCompat L c c' ψ) (hχ : NullaryCompat L' c' c'' χ) :
    NullaryCompat (L ⋙ L') c c'' (L'.map ψ ≫ χ) := by
  intro T a h W z
  have := hχ (L.obj T) (L.map a ≫ ψ) (hψ T a h) W z
  simp only [Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply] at this
  exact this

private theorem BinaryCompat.post {L : Sheaf J (Type u) ⥤ Sheaf J' (Type u)}
    {P₁ P₂ P₃ : Sheaf J (Type u)} {Q₁ Q₂ Q₃ S₁ S₂ S₃ : Sheaf J' (Type u)}
    {op : ∀ U, P₁.obj.obj U → P₂.obj.obj U → P₃.obj.obj U}
    {op' : ∀ V, Q₁.obj.obj V → Q₂.obj.obj V → Q₃.obj.obj V}
    {op'' : ∀ V, S₁.obj.obj V → S₂.obj.obj V → S₃.obj.obj V}
    {ψ₁ : L.obj P₁ ⟶ Q₁} {ψ₂ : L.obj P₂ ⟶ Q₂} {ψ₃ : L.obj P₃ ⟶ Q₃}
    (hψ : BinaryCompat L op op' ψ₁ ψ₂ ψ₃)
    (β₁ : Q₁ ⟶ S₁) (β₂ : Q₂ ⟶ S₂) (β₃ : Q₃ ⟶ S₃)
    (hβ : ∀ V x y, β₃.hom.app V (op' V x y) = op'' V (β₁.hom.app V x) (β₂.hom.app V y)) :
    BinaryCompat L op op'' (ψ₁ ≫ β₁) (ψ₂ ≫ β₂) (ψ₃ ≫ β₃) := by
  intro T a b t h V z
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply]
  rw [hψ T a b t h V z, hβ]

private theorem NullaryCompat.post {L : Sheaf J (Type u) ⥤ Sheaf J' (Type u)}
    {P : Sheaf J (Type u)} {Q S : Sheaf J' (Type u)}
    {c : ∀ U, P.obj.obj U} {c' : ∀ V, Q.obj.obj V} {c'' : ∀ V, S.obj.obj V}
    {ψ : L.obj P ⟶ Q} (hψ : NullaryCompat L c c' ψ) (β : Q ⟶ S)
    (hβ : ∀ V, β.hom.app V (c' V) = c'' V) :
    NullaryCompat L c c'' (ψ ≫ β) := by
  intro T a h V z
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply]
  rw [hψ T a h V z, hβ]

private theorem BinaryCompat.pre {L L' : Sheaf J (Type u) ⥤ Sheaf J' (Type u)}
    {P₁ P₂ P₃ : Sheaf J (Type u)} {Q₁ Q₂ Q₃ : Sheaf J' (Type u)}
    {op : ∀ U, P₁.obj.obj U → P₂.obj.obj U → P₃.obj.obj U}
    {op' : ∀ V, Q₁.obj.obj V → Q₂.obj.obj V → Q₃.obj.obj V}
    {ψ₁ : L.obj P₁ ⟶ Q₁} {ψ₂ : L.obj P₂ ⟶ Q₂} {ψ₃ : L.obj P₃ ⟶ Q₃}
    (hψ : BinaryCompat L op op' ψ₁ ψ₂ ψ₃) (σ : L' ⟶ L) :
    BinaryCompat L' op op' (σ.app P₁ ≫ ψ₁) (σ.app P₂ ≫ ψ₂) (σ.app P₃ ≫ ψ₃) := by
  intro T a b t h V z
  have hn {P : Sheaf J (Type u)} (k : T ⟶ P) :
      (σ.app P).hom.app V ((L'.map k).hom.app V z) =
        (L.map k).hom.app V ((σ.app T).hom.app V z) :=
    congrArg (fun m ↦ m.hom.app V z) (σ.naturality k)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply]
  rw [hn, hn, hn]
  exact hψ T a b t h V _

private theorem NullaryCompat.pre {L L' : Sheaf J (Type u) ⥤ Sheaf J' (Type u)}
    {P : Sheaf J (Type u)} {Q : Sheaf J' (Type u)}
    {c : ∀ U, P.obj.obj U} {c' : ∀ V, Q.obj.obj V}
    {ψ : L.obj P ⟶ Q} (hψ : NullaryCompat L c c' ψ) (σ : L' ⟶ L) :
    NullaryCompat L' c c' (σ.app P ≫ ψ) := by
  intro T a h V z
  have hn : (σ.app P).hom.app V ((L'.map a).hom.app V z) =
      (L.map a).hom.app V ((σ.app T).hom.app V z) :=
    congrArg (fun m ↦ m.hom.app V z) (σ.naturality a)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply]
  rw [hn]
  exact hψ T a h V _


/-- An inverse image preserving a binary product has jointly surjective projections on
sections. -/
private theorem exists_section_prod (L : Sheaf J (Type u) ⥤ Sheaf J' (Type u))
    (P₁ P₂ : Sheaf J (Type u)) [PreservesLimit (pair P₁ P₂) L] (V : Dᵒᵖ)
    (x : (L.obj P₁).obj.obj V) (y : (L.obj P₂).obj.obj V) :
    ∃ z : (L.obj (P₁ ⨯ P₂)).obj.obj V,
      (L.map prod.fst).hom.app V z = x ∧ (L.map prod.snd).hom.app V z = y := by
  let G := L ⋙ sheafToPresheaf J' (Type u) ⋙ (evaluation _ _).obj V
  have h := (isLimitMapConeBinaryFanEquiv G prod.fst prod.snd)
    (isLimitOfPreserves G (prodIsProd P₁ P₂))
  obtain ⟨l, hl₁, hl₂⟩ := BinaryFan.IsLimit.lift' h
    (TypeCat.ofHom (fun _ : PUnit.{u + 1} ↦ x)) (TypeCat.ofHom (fun _ : PUnit.{u + 1} ↦ y))
  exact ⟨l PUnit.unit, congrArg (fun k ↦ k PUnit.unit) hl₁,
    congrArg (fun k ↦ k PUnit.unit) hl₂⟩


private theorem inv_hom_apply' {X Y : Sheaf J' (Type u)} (ψ : X ⟶ Y) [IsIso ψ] (V : Dᵒᵖ)
    (w : Y.obj.obj V) : ψ.hom.app V ((inv ψ).hom.app V w) = w := by
  have := congrArg (fun k ↦ k.hom.app V w) (IsIso.inv_hom_id ψ)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply] at this
  exact this

private theorem hom_inv_apply' {X Y : Sheaf J' (Type u)} (ψ : X ⟶ Y) [IsIso ψ] (V : Dᵒᵖ)
    (w : X.obj.obj V) : (inv ψ).hom.app V (ψ.hom.app V w) = w := by
  have := congrArg (fun k ↦ k.hom.app V w) (IsIso.hom_inv_id ψ)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply] at this
  exact this

/-- The sheaf map given sectionwise by a natural binary operation on a product. -/
private def prodOperation {P₁ P₂ P₃ : Sheaf J (Type u)}
    (op : ∀ U, P₁.obj.obj U → P₂.obj.obj U → P₃.obj.obj U)
    (hop : ∀ {U U' : Cᵒᵖ} (f : U ⟶ U') x y,
      P₃.obj.map f (op U x y) = op U' (P₁.obj.map f x) (P₂.obj.map f y)) :
    P₁ ⨯ P₂ ⟶ P₃ :=
  Sheaf.homEquiv.symm
    { app U := TypeCat.ofHom (fun z ↦ op U ((prod.fst : P₁ ⨯ P₂ ⟶ P₁).hom.app U z)
        ((prod.snd : P₁ ⨯ P₂ ⟶ P₂).hom.app U z))
      naturality U U' f := by
        ext z
        change op U' _ _ = P₃.obj.map f (op U _ _)
        rw [hop]
        congr 1
        · exact congrArg (fun k ↦ k z) ((prod.fst : P₁ ⨯ P₂ ⟶ P₁).hom.naturality f)
        · exact congrArg (fun k ↦ k z) ((prod.snd : P₁ ⨯ P₂ ⟶ P₂).hom.naturality f) }

/-- Two transports of the same operation along isomorphic identifications differ by an
operation-preserving map. -/
private theorem BinaryCompat.extract {L : Sheaf J (Type u) ⥤ Sheaf J' (Type u)}
    {P₁ P₂ P₃ : Sheaf J (Type u)} {Q₁ Q₂ Q₃ S₁ S₂ S₃ : Sheaf J' (Type u)}
    {op : ∀ U, P₁.obj.obj U → P₂.obj.obj U → P₃.obj.obj U}
    (hop : ∀ {U U' : Cᵒᵖ} (f : U ⟶ U') x y,
      P₃.obj.map f (op U x y) = op U' (P₁.obj.map f x) (P₂.obj.map f y))
    {op' : ∀ V, Q₁.obj.obj V → Q₂.obj.obj V → Q₃.obj.obj V}
    {op'' : ∀ V, S₁.obj.obj V → S₂.obj.obj V → S₃.obj.obj V}
    {ψ₁ : L.obj P₁ ⟶ Q₁} {ψ₂ : L.obj P₂ ⟶ Q₂} {ψ₃ : L.obj P₃ ⟶ Q₃}
    {χ₁ : L.obj P₁ ⟶ S₁} {χ₂ : L.obj P₂ ⟶ S₂} {χ₃ : L.obj P₃ ⟶ S₃}
    (hψ : BinaryCompat L op op' ψ₁ ψ₂ ψ₃) (hχ : BinaryCompat L op op'' χ₁ χ₂ χ₃)
    [IsIso ψ₁] [IsIso ψ₂] [IsIso ψ₃] [PreservesLimit (pair P₁ P₂) L]
    (V : Dᵒᵖ) (x : Q₁.obj.obj V) (y : Q₂.obj.obj V) :
    χ₃.hom.app V ((inv ψ₃).hom.app V (op' V x y)) =
      op'' V (χ₁.hom.app V ((inv ψ₁).hom.app V x)) (χ₂.hom.app V ((inv ψ₂).hom.app V y)) := by
  obtain ⟨z, hz₁, hz₂⟩ := exists_section_prod L P₁ P₂ V ((inv ψ₁).hom.app V x)
    ((inv ψ₂).hom.app V y)
  have h₁ := hψ _ prod.fst prod.snd (prodOperation op hop) (fun _ _ ↦ rfl) V z
  have h₂ := hχ _ prod.fst prod.snd (prodOperation op hop) (fun _ _ ↦ rfl) V z
  rw [hz₁, hz₂, inv_hom_apply', inv_hom_apply'] at h₁
  rw [hz₁, hz₂] at h₂
  rw [← h₁, hom_inv_apply', h₂]

/-- The nullary version of `BinaryCompat.extract`. -/
private theorem NullaryCompat.extract {L : Sheaf J (Type u) ⥤ Sheaf J' (Type u)}
    {P : Sheaf J (Type u)} {Q S : Sheaf J' (Type u)}
    {c : ∀ U, P.obj.obj U} (hc : ∀ {U U' : Cᵒᵖ} (f : U ⟶ U'), P.obj.map f (c U) = c U')
    {c' : ∀ V, Q.obj.obj V} {c'' : ∀ V, S.obj.obj V}
    {ψ : L.obj P ⟶ Q} {χ : L.obj P ⟶ S}
    (hψ : NullaryCompat L c c' ψ) (hχ : NullaryCompat L c c'' χ) [IsIso ψ] (V : Dᵒᵖ) :
    χ.hom.app V ((inv ψ).hom.app V (c' V)) = c'' V := by
  let a : P ⟶ P := Sheaf.homEquiv.symm
    { app U := TypeCat.ofHom (fun _ ↦ c U)
      naturality U U' f := by
        ext z
        exact (hc f).symm }
  let z := (inv ψ).hom.app V (c' V)
  have h₁ := hψ P a (fun _ _ ↦ rfl) V z
  have h₂ := hχ P a (fun _ _ ↦ rfl) V z
  rw [← h₁, hom_inv_apply', h₂]


section Operations

variable {C₀ : Type u} [SmallCategory C₀] {J₀ : GrothendieckTopology C₀}

/-- Addition of sections of a module sheaf. -/
private def addOp {O : Sheaf J₀ CommRingCat.{u}} (M : Mod O) (U : C₀ᵒᵖ)
    (x y : ((underlying O).obj M).obj.obj U) : ((underlying O).obj M).obj.obj U :=
  @id (((underlying O).obj M).obj.obj U) (@id (M.val.obj U) x + @id (M.val.obj U) y)

/-- Scalar multiplication on sections of a module sheaf. -/
private def smulOp {O : Sheaf J₀ CommRingCat.{u}} (M : Mod O) (U : C₀ᵒᵖ)
    (r : ((sheafCompose J₀ (forget CommRingCat.{u})).obj O).obj.obj U)
    (x : ((underlying O).obj M).obj.obj U) : ((underlying O).obj M).obj.obj U :=
  @id (((underlying O).obj M).obj.obj U) (@id (O.obj.obj U) r • @id (M.val.obj U) x)

/-- Addition of sections of a ring sheaf. -/
private def ringAddOp (O : Sheaf J₀ CommRingCat.{u}) (U : C₀ᵒᵖ)
    (r s : ((sheafCompose J₀ (forget CommRingCat.{u})).obj O).obj.obj U) :
    ((sheafCompose J₀ (forget CommRingCat.{u})).obj O).obj.obj U :=
  @id (((sheafCompose J₀ (forget CommRingCat.{u})).obj O).obj.obj U)
    (@id (O.obj.obj U) r + @id (O.obj.obj U) s)

/-- The unit section of a ring sheaf. -/
private def ringOne (O : Sheaf J₀ CommRingCat.{u}) (U : C₀ᵒᵖ) :
    ((sheafCompose J₀ (forget CommRingCat.{u})).obj O).obj.obj U :=
  @id (((sheafCompose J₀ (forget CommRingCat.{u})).obj O).obj.obj U) (1 : O.obj.obj U)

private theorem addOp_natural {O : Sheaf J₀ CommRingCat.{u}} (M : Mod O) {U U' : C₀ᵒᵖ}
    (f : U ⟶ U') (x y) :
    ((underlying O).obj M).obj.map f (addOp M U x y) =
      addOp M U' (((underlying O).obj M).obj.map f x) (((underlying O).obj M).obj.map f y) :=
  (M.val.map f).hom.map_add _ _

private theorem smulOp_natural {O : Sheaf J₀ CommRingCat.{u}} (M : Mod O) {U U' : C₀ᵒᵖ}
    (f : U ⟶ U') (r x) :
    ((underlying O).obj M).obj.map f (smulOp M U r x) =
      smulOp M U' (((sheafCompose J₀ (forget CommRingCat.{u})).obj O).obj.map f r)
        (((underlying O).obj M).obj.map f x) :=
  M.val.map_smul f _ _

private theorem ringAddOp_natural (O : Sheaf J₀ CommRingCat.{u}) {U U' : C₀ᵒᵖ}
    (f : U ⟶ U') (r s) :
    ((sheafCompose J₀ (forget CommRingCat.{u})).obj O).obj.map f (ringAddOp O U r s) =
      ringAddOp O U' (((sheafCompose J₀ (forget CommRingCat.{u})).obj O).obj.map f r)
        (((sheafCompose J₀ (forget CommRingCat.{u})).obj O).obj.map f s) :=
  (O.obj.map f).hom.map_add _ _

private theorem ringOne_natural (O : Sheaf J₀ CommRingCat.{u}) {U U' : C₀ᵒᵖ}
    (f : U ⟶ U') :
    ((sheafCompose J₀ (forget CommRingCat.{u})).obj O).obj.map f (ringOne O U) =
      ringOne O U' :=
  (O.obj.map f).hom.map_one

/-- The scalar-extension insertion is additive. -/
private theorem insertion_add {R S : Sheaf J₀ CommRingCat.{u}} (c : R ⟶ S) (M : Mod R)
    (U : C₀ᵒᵖ) (x y) :
    (insertion c M).hom.app U (addOp M U x y) =
      addOp ((change c).obj M) U ((insertion c M).hom.app U x)
        ((insertion c M).hom.app U y) := by
  have h := (insertion_existsUnique c M).exists.choose_spec U
  dsimp only [addOp, id]
  rw [show insertion c M = (insertion_existsUnique c M).exists.choose from rfl, h, h, h]
  unfold tensorSection
  rw [TensorProduct.tmul_add, map_add]

/-- The scalar-extension insertion is semilinear along the ring map. -/
private theorem insertion_smul {R S : Sheaf J₀ CommRingCat.{u}} (c : R ⟶ S) (M : Mod R)
    (U : C₀ᵒᵖ) (r x) :
    (insertion c M).hom.app U (smulOp M U r x) =
      smulOp ((change c).obj M) U
        (((sheafCompose J₀ (forget CommRingCat.{u})).map c).hom.app U r)
        ((insertion c M).hom.app U x) := by
  have h := (insertion_existsUnique c M).exists.choose_spec U
  dsimp only [smulOp, id]
  rw [show insertion c M = (insertion_existsUnique c M).exists.choose from rfl, h, h]
  erw [← tensorSection_smul]
  unfold tensorSection
  congr 1
  refine (TensorProduct.smul_tmul _ _ _).symm.trans ?_
  congr 1
  exact mul_one (c.hom.app U r : S.obj.obj U)

end Operations


section Transport

variable {L : Sheaf J (Type u) ⥤ Sheaf J' (Type u)} (F : InverseImageData L)

/-- The ring part of the pullback, on underlying sheaves of sets. -/
private def ringPull {R : Sheaf J CommRingCat.{u}} {S : Sheaf J' CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) :
    L.obj ((sheafCompose J (forget CommRingCat.{u})).obj R) ⟶
      (sheafCompose J' (forget CommRingCat.{u})).obj S :=
  (F.algebra R).ringUnderlying.hom ≫ (sheafCompose J' (forget CommRingCat.{u})).map c

private theorem pullInsertion_add {R : Sheaf J CommRingCat.{u}} {S : Sheaf J' CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) (M : Mod R) :
    BinaryCompat L (addOp M) (addOp ((pull F c).obj M))
      (pullInsertion F c M) (pullInsertion F c M) (pullInsertion F c M) := by
  have h : BinaryCompat L (addOp M) (addOp ((F.algebra R).modules.obj M))
      ((F.algebra R).moduleUnderlying.inv.app M) ((F.algebra R).moduleUnderlying.inv.app M)
      ((F.algebra R).moduleUnderlying.inv.app M) :=
    fun T a b t ht V z ↦ (F.algebra R).moduleAdd M T a b t ht V z
  exact h.post _ _ _ (insertion_add c _)

private theorem pullInsertion_smul {R : Sheaf J CommRingCat.{u}}
    {S : Sheaf J' CommRingCat.{u}} (c : F.rings.obj R ⟶ S) (M : Mod R) :
    BinaryCompat L (smulOp M) (smulOp ((pull F c).obj M))
      (ringPull F c) (pullInsertion F c M) (pullInsertion F c M) := by
  have h : BinaryCompat L (smulOp M) (smulOp ((F.algebra R).modules.obj M))
      (F.algebra R).ringUnderlying.hom ((F.algebra R).moduleUnderlying.inv.app M)
      ((F.algebra R).moduleUnderlying.inv.app M) :=
    fun T a b t ht V z ↦ (F.algebra R).moduleSMul M T a b t ht V z
  exact h.post _ _ _ (insertion_smul c _)

private theorem ringPull_add {R : Sheaf J CommRingCat.{u}} {S : Sheaf J' CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) :
    BinaryCompat L (ringAddOp R) (ringAddOp S) (ringPull F c) (ringPull F c) (ringPull F c) := by
  have h : BinaryCompat L (ringAddOp R) (ringAddOp (F.rings.obj R))
      (F.algebra R).ringUnderlying.hom (F.algebra R).ringUnderlying.hom
      (F.algebra R).ringUnderlying.hom :=
    fun T a b t ht V z ↦ (F.algebra R).ringAdd T a b t ht V z
  exact h.post _ _ _ (fun V x y ↦ (c.hom.app V).hom.map_add _ _)

private theorem ringPull_one {R : Sheaf J CommRingCat.{u}} {S : Sheaf J' CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) :
    NullaryCompat L (ringOne R) (ringOne S) (ringPull F c) := by
  have h : NullaryCompat L (ringOne R) (ringOne (F.rings.obj R))
      (F.algebra R).ringUnderlying.hom :=
    fun T a ht V z ↦ (F.algebra R).ringOne T a ht V z
  exact h.post _ (fun V ↦ (c.hom.app V).hom.map_one)

end Transport


section Naturality

variable {C₀ : Type u} [SmallCategory C₀] {J₀ : GrothendieckTopology C₀}

private theorem insertion_naturality {R S : Sheaf J₀ CommRingCat.{u}} (c : R ⟶ S)
    {M N : Mod R} (a : M ⟶ N) :
    insertion c M ≫ (underlying S).map ((change c).map a) =
      (underlying R).map a ≫ insertion c N := by
  have hM := (insertion_existsUnique c M).exists.choose_spec
  have hN := (insertion_existsUnique c N).exists.choose_spec
  apply Sheaf.hom_ext
  ext U m
  change ((change c).map a).val.app U ((insertion c M).hom.app U m) =
    (insertion c N).hom.app U (a.val.app U m)
  rw [show insertion c M = (insertion_existsUnique c M).exists.choose from rfl,
    show insertion c N = (insertion_existsUnique c N).exists.choose from rfl, hM, hN,
    tensorSection_map]

/-- A map of underlying sheaves preserving addition and scalars is a module map. -/
private def linearOfUnderlying {O : Sheaf J₀ CommRingCat.{u}} {M N : Mod O}
    (α : (underlying O).obj M ⟶ (underlying O).obj N)
    (ha : ∀ U x y, α.hom.app U (addOp M U x y) = addOp N U (α.hom.app U x) (α.hom.app U y))
    (hs : ∀ U r x, α.hom.app U (smulOp M U r x) = smulOp N U r (α.hom.app U x)) :
    M ⟶ N where
  val :=
    { app U := ModuleCat.ofHom
        { toFun := α.hom.app U
          map_add' := ha U
          map_smul' := hs U }
      naturality := by
        intro X Y f
        ext x
        exact congrArg (fun k ↦ k x) (α.hom.naturality f) }

end Naturality

private theorem pullInsertion_naturality {L : Sheaf J (Type u) ⥤ Sheaf J' (Type u)}
    (F : InverseImageData L) {R : Sheaf J CommRingCat.{u}} {S : Sheaf J' CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) {M N : Mod R} (a : M ⟶ N) :
    L.map ((underlying R).map a) ≫ pullInsertion F c N =
      pullInsertion F c M ≫ (underlying S).map ((pull F c).map a) := by
  have h : L.map ((underlying R).map a) ≫ (F.algebra R).moduleUnderlying.inv.app N =
      (F.algebra R).moduleUnderlying.inv.app M ≫
        (underlying (F.rings.obj R)).map ((F.algebra R).modules.map a) :=
    (F.algebra R).moduleUnderlying.inv.naturality a
  dsimp only [pullInsertion]
  rw [← Category.assoc, h, Category.assoc, Category.assoc]
  congr 1
  exact (insertion_naturality c ((F.algebra R).modules.map a)).symm

private theorem pullInsertion_isIso {L : Sheaf J (Type u) ⥤ Sheaf J' (Type u)}
    (F : InverseImageData L) {R : Sheaf J CommRingCat.{u}} {S : Sheaf J' CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) [IsIso c] (M : Mod R) : IsIso (pullInsertion F c M) := by
  have : (res c).IsEquivalence := restrictScalars_equivalence
    ((sheafCompose J' (forget₂ CommRingCat RingCat)).mapIso (asIso c))
  let adj := SheafOfModules.RingedTensor.tensorAdjunction c
  have := adj.isEquivalence_left_of_isEquivalence_right
  have := adj.unit_isIso_of_L_fully_faithful
  have : IsIso (insertion c ((F.algebra R).modules.obj M)) := by
    rw [show insertion c ((F.algebra R).modules.obj M) =
        (underlying _).map (adj.unit.app ((F.algebra R).modules.obj M)) from
      (insertion_existsUnique c _).unique (insertion_existsUnique c _).exists.choose_spec
        (fun _ _ ↦ rfl)]
    infer_instance
  dsimp only [pullInsertion]
  infer_instance


/-- The ring part of the pullback on constant coefficient sheaves, natural in the ring. -/
private def constRingPull {L : Sheaf J (Type u) ⥤ Sheaf J' (Type u)} (F : InverseImageData L) :
    (constantSheaf J CommRingCat.{u} ⋙ sheafCompose J (forget CommRingCat.{u})) ⋙ L ⟶
      constantSheaf J' CommRingCat.{u} ⋙ sheafCompose J' (forget CommRingCat.{u}) where
  app A := ringPull F (F.constants.hom.app A)
  naturality A B α := by
    have h₁ := F.ring_naturality ((constantSheaf J CommRingCat.{u}).map α)
    have h₂ := F.constants.hom.naturality α
    dsimp only [ringPull, Functor.comp_map]
    rw [← Category.assoc, h₁, Category.assoc, Category.assoc, ← Functor.map_comp,
      ← Functor.map_comp]
    congr 2

private theorem ringPull_isIso {L : Sheaf J (Type u) ⥤ Sheaf J' (Type u)}
    (F : InverseImageData L) {R : Sheaf J CommRingCat.{u}} {S : Sheaf J' CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) [IsIso c] : IsIso (ringPull F c) := by
  dsimp only [ringPull]
  infer_instance


section Square

variable {C₁ C₂ C₃ C₄ : Type u} [SmallCategory C₁] [SmallCategory C₂] [SmallCategory C₃]
  [SmallCategory C₄] {J₁ : GrothendieckTopology C₁} {J₂ : GrothendieckTopology C₂}
  {J₃ : GrothendieckTopology C₃} {J₄ : GrothendieckTopology C₄}
  {Lg : Sheaf J₁ (Type u) ⥤ Sheaf J₂ (Type u)} {Lk : Sheaf J₂ (Type u) ⥤ Sheaf J₄ (Type u)}
  {Lf : Sheaf J₁ (Type u) ⥤ Sheaf J₃ (Type u)} {Lh : Sheaf J₃ (Type u) ⥤ Sheaf J₄ (Type u)}

/-- The ring identification along the first composite. -/
private def squareRing₁ (Fg : InverseImageData Lg) (Fk : InverseImageData Lk) :
    (constantSheaf J₁ CommRingCat.{u} ⋙ sheafCompose J₁ (forget CommRingCat.{u})) ⋙ Lg ⋙ Lk ⟶
      constantSheaf J₄ CommRingCat.{u} ⋙ sheafCompose J₄ (forget CommRingCat.{u}) :=
  Functor.whiskerRight (constRingPull Fg) Lk ≫ constRingPull Fk

/-- The ring identification along the second composite, through the square. -/
private def squareRing₂ (Ff : InverseImageData Lf) (Fh : InverseImageData Lh)
    (sq : Lg ⋙ Lk ≅ Lf ⋙ Lh) :
    (constantSheaf J₁ CommRingCat.{u} ⋙ sheafCompose J₁ (forget CommRingCat.{u})) ⋙ Lg ⋙ Lk ⟶
      constantSheaf J₄ CommRingCat.{u} ⋙ sheafCompose J₄ (forget CommRingCat.{u}) :=
  Functor.whiskerLeft (constantSheaf J₁ CommRingCat.{u} ⋙
      sheafCompose J₁ (forget CommRingCat.{u})) sq.hom ≫
    Functor.whiskerRight (constRingPull Ff) Lh ≫ constRingPull Fh

private theorem squareRing₁_add (Fg : InverseImageData Lg) (Fk : InverseImageData Lk)
    (B : CommRingCat.{u}) :
    BinaryCompat (Lg ⋙ Lk) (ringAddOp ((constantSheaf J₁ CommRingCat.{u}).obj B))
      (ringAddOp ((constantSheaf J₄ CommRingCat.{u}).obj B)) ((squareRing₁ Fg Fk).app B)
      ((squareRing₁ Fg Fk).app B) ((squareRing₁ Fg Fk).app B) :=
  (ringPull_add Fg _).comp (ringPull_add Fk _)


private theorem squareRing₂_add (Ff : InverseImageData Lf) (Fh : InverseImageData Lh)
    (sq : Lg ⋙ Lk ≅ Lf ⋙ Lh) (B : CommRingCat.{u}) :
    BinaryCompat (Lg ⋙ Lk) (ringAddOp ((constantSheaf J₁ CommRingCat.{u}).obj B))
      (ringAddOp ((constantSheaf J₄ CommRingCat.{u}).obj B)) ((squareRing₂ Ff Fh sq).app B)
      ((squareRing₂ Ff Fh sq).app B) ((squareRing₂ Ff Fh sq).app B) :=
  ((ringPull_add Ff _).comp (ringPull_add Fh _)).pre sq.hom

private theorem squareRing₁_one (Fg : InverseImageData Lg) (Fk : InverseImageData Lk)
    (B : CommRingCat.{u}) :
    NullaryCompat (Lg ⋙ Lk) (ringOne ((constantSheaf J₁ CommRingCat.{u}).obj B))
      (ringOne ((constantSheaf J₄ CommRingCat.{u}).obj B)) ((squareRing₁ Fg Fk).app B) :=
  (ringPull_one Fg _).comp (ringPull_one Fk _)

private theorem squareRing₂_one (Ff : InverseImageData Lf) (Fh : InverseImageData Lh)
    (sq : Lg ⋙ Lk ≅ Lf ⋙ Lh) (B : CommRingCat.{u}) :
    NullaryCompat (Lg ⋙ Lk) (ringOne ((constantSheaf J₁ CommRingCat.{u}).obj B))
      (ringOne ((constantSheaf J₄ CommRingCat.{u}).obj B)) ((squareRing₂ Ff Fh sq).app B) :=
  ((ringPull_one Ff _).comp (ringPull_one Fh _)).pre sq.hom

private theorem squareRing₁_isIso (Fg : InverseImageData Lg) (Fk : InverseImageData Lk) :
    IsIso (squareRing₁ Fg Fk) := by
  have (B : CommRingCat.{u}) : IsIso ((squareRing₁ Fg Fk).app B) := by
    have := ringPull_isIso Fg (Fg.constants.hom.app B)
    have := ringPull_isIso Fk (Fk.constants.hom.app B)
    change IsIso (Lk.map (ringPull Fg _) ≫ ringPull Fk _)
    infer_instance
  exact NatIso.isIso_of_isIso_app _

private theorem squareRing_eq [PreservesFiniteLimits Lg] [PreservesFiniteLimits Lk]
    (Fg : InverseImageData Lg) (Fk : InverseImageData Lk)
    (Ff : InverseImageData Lf) (Fh : InverseImageData Lh) (sq : Lg ⋙ Lk ≅ Lf ⋙ Lh) :
    squareRing₁ Fg Fk = squareRing₂ Ff Fh sq := by
  have := squareRing₁_isIso Fg Fk
  have hψ := constantSheaf_forget_natTrans_eq_id J₄
    (inv (squareRing₁ Fg Fk) ≫ squareRing₂ Ff Fh sq) ?_ ?_
  · rw [IsIso.inv_comp_eq, Category.comp_id] at hψ
    exact hψ.symm
  · intro B V x y
    have := BinaryCompat.extract (ringAddOp_natural _) (squareRing₁_add Fg Fk B)
      (squareRing₂_add Ff Fh sq B) V x y
    simp only [NatTrans.comp_app, NatIso.isIso_inv_app]
    exact this
  · intro B V
    have := NullaryCompat.extract (ringOne_natural _) (squareRing₁_one Fg Fk B)
      (squareRing₂_one Ff Fh sq B) V
    simp only [NatTrans.comp_app, NatIso.isIso_inv_app]
    exact this

/-- The inverse-image insertion along the first composite. -/
private def squareModule₁ (Fg : InverseImageData Lg) (Fk : InverseImageData Lk)
    (A : Type u) [CommRing A] (M : Mod (constant J₁ A)) :
    (Lg ⋙ Lk).obj ((underlying (constant J₁ A)).obj M) ⟶ (underlying (constant J₄ A)).obj
      ((pull Fg (constantMap Fg A) ⋙ pull Fk (constantMap Fk A)).obj M) :=
  Lk.map (pullInsertion Fg (constantMap Fg A) M) ≫
    pullInsertion Fk (constantMap Fk A) ((pull Fg (constantMap Fg A)).obj M)

/-- The inverse-image insertion along the second composite, through the square. -/
private def squareModule₂ (Ff : InverseImageData Lf) (Fh : InverseImageData Lh)
    (sq : Lg ⋙ Lk ≅ Lf ⋙ Lh) (A : Type u) [CommRing A] (M : Mod (constant J₁ A)) :
    (Lg ⋙ Lk).obj ((underlying (constant J₁ A)).obj M) ⟶ (underlying (constant J₄ A)).obj
      ((pull Ff (constantMap Ff A) ⋙ pull Fh (constantMap Fh A)).obj M) :=
  sq.hom.app ((underlying (constant J₁ A)).obj M) ≫
    Lh.map (pullInsertion Ff (constantMap Ff A) M) ≫
    pullInsertion Fh (constantMap Fh A) ((pull Ff (constantMap Ff A)).obj M)

private theorem squareModule₁_add (Fg : InverseImageData Lg) (Fk : InverseImageData Lk)
    (A : Type u) [CommRing A] (M : Mod (constant J₁ A)) :
    BinaryCompat (Lg ⋙ Lk) (addOp M)
      (addOp ((pull Fg (constantMap Fg A) ⋙ pull Fk (constantMap Fk A)).obj M))
      (squareModule₁ Fg Fk A M) (squareModule₁ Fg Fk A M) (squareModule₁ Fg Fk A M) :=
  (pullInsertion_add Fg _ M).comp (pullInsertion_add Fk _ _)

private theorem squareModule₂_add (Ff : InverseImageData Lf) (Fh : InverseImageData Lh)
    (sq : Lg ⋙ Lk ≅ Lf ⋙ Lh) (A : Type u) [CommRing A] (M : Mod (constant J₁ A)) :
    BinaryCompat (Lg ⋙ Lk) (addOp M)
      (addOp ((pull Ff (constantMap Ff A) ⋙ pull Fh (constantMap Fh A)).obj M))
      (squareModule₂ Ff Fh sq A M) (squareModule₂ Ff Fh sq A M) (squareModule₂ Ff Fh sq A M) :=
  ((pullInsertion_add Ff _ M).comp (pullInsertion_add Fh _ _)).pre sq.hom

private theorem squareModule₁_smul (Fg : InverseImageData Lg) (Fk : InverseImageData Lk)
    (A : Type u) [CommRing A] (M : Mod (constant J₁ A)) :
    BinaryCompat (Lg ⋙ Lk) (smulOp M)
      (smulOp ((pull Fg (constantMap Fg A) ⋙ pull Fk (constantMap Fk A)).obj M))
      ((squareRing₁ Fg Fk).app (CommRingCat.of A))
      (squareModule₁ Fg Fk A M) (squareModule₁ Fg Fk A M) :=
  (pullInsertion_smul Fg _ M).comp (pullInsertion_smul Fk _ _)

private theorem squareModule₂_smul (Ff : InverseImageData Lf) (Fh : InverseImageData Lh)
    (sq : Lg ⋙ Lk ≅ Lf ⋙ Lh) (A : Type u) [CommRing A] (M : Mod (constant J₁ A)) :
    BinaryCompat (Lg ⋙ Lk) (smulOp M)
      (smulOp ((pull Ff (constantMap Ff A) ⋙ pull Fh (constantMap Fh A)).obj M))
      ((squareRing₂ Ff Fh sq).app (CommRingCat.of A))
      (squareModule₂ Ff Fh sq A M) (squareModule₂ Ff Fh sq A M) :=
  ((pullInsertion_smul Ff _ M).comp (pullInsertion_smul Fh _ _)).pre sq.hom

private theorem squareModule₁_isIso (Fg : InverseImageData Lg) (Fk : InverseImageData Lk)
    (A : Type u) [CommRing A] (M : Mod (constant J₁ A)) : IsIso (squareModule₁ Fg Fk A M) := by
  have : IsIso (constantMap Fg A) := by dsimp only [constantMap]; infer_instance
  have : IsIso (constantMap Fk A) := by dsimp only [constantMap]; infer_instance
  have := pullInsertion_isIso Fg (constantMap Fg A) M
  have := pullInsertion_isIso Fk (constantMap Fk A) ((pull Fg (constantMap Fg A)).obj M)
  dsimp only [squareModule₁]
  infer_instance

private theorem squareModule₂_isIso (Ff : InverseImageData Lf) (Fh : InverseImageData Lh)
    (sq : Lg ⋙ Lk ≅ Lf ⋙ Lh) (A : Type u) [CommRing A] (M : Mod (constant J₁ A)) :
    IsIso (squareModule₂ Ff Fh sq A M) := by
  have : IsIso (constantMap Ff A) := by dsimp only [constantMap]; infer_instance
  have : IsIso (constantMap Fh A) := by dsimp only [constantMap]; infer_instance
  have := pullInsertion_isIso Ff (constantMap Ff A) M
  have := pullInsertion_isIso Fh (constantMap Fh A) ((pull Ff (constantMap Ff A)).obj M)
  dsimp only [squareModule₂]
  infer_instance

private theorem squareModule₁_naturality (Fg : InverseImageData Lg) (Fk : InverseImageData Lk)
    (A : Type u) [CommRing A] {M N : Mod (constant J₁ A)} (a : M ⟶ N) :
    (Lg ⋙ Lk).map ((underlying (constant J₁ A)).map a) ≫ squareModule₁ Fg Fk A N =
      squareModule₁ Fg Fk A M ≫ (underlying (constant J₄ A)).map
        ((pull Fg (constantMap Fg A) ⋙ pull Fk (constantMap Fk A)).map a) := by
  have h₁ := pullInsertion_naturality Fg (constantMap Fg A) a
  have h₂ := pullInsertion_naturality Fk (constantMap Fk A) ((pull Fg (constantMap Fg A)).map a)
  change Lk.map (Lg.map _) ≫ Lk.map _ ≫ _ = (Lk.map _ ≫ _) ≫ _
  rw [← Category.assoc, ← Functor.map_comp, h₁, Functor.map_comp, Category.assoc, h₂,
    Category.assoc]
  rfl

private theorem squareModule₂_naturality (Ff : InverseImageData Lf) (Fh : InverseImageData Lh)
    (sq : Lg ⋙ Lk ≅ Lf ⋙ Lh) (A : Type u) [CommRing A] {M N : Mod (constant J₁ A)}
    (a : M ⟶ N) :
    (Lg ⋙ Lk).map ((underlying (constant J₁ A)).map a) ≫ squareModule₂ Ff Fh sq A N =
      squareModule₂ Ff Fh sq A M ≫ (underlying (constant J₄ A)).map
        ((pull Ff (constantMap Ff A) ⋙ pull Fh (constantMap Fh A)).map a) := by
  have h₁ := pullInsertion_naturality Ff (constantMap Ff A) a
  have h₂ := pullInsertion_naturality Fh (constantMap Fh A) ((pull Ff (constantMap Ff A)).map a)
  have h₀ := sq.hom.naturality ((underlying (constant J₁ A)).map a)
  change _ ≫ sq.hom.app _ ≫ Lh.map _ ≫ _ = (sq.hom.app _ ≫ Lh.map _ ≫ _) ≫ _
  rw [← Category.assoc, h₀, Category.assoc, Category.assoc]
  refine congrArg (sq.hom.app _ ≫ ·) ?_
  change Lh.map (Lf.map _) ≫ Lh.map _ ≫ _ = (Lh.map _ ≫ _) ≫ _
  rw [← Category.assoc, ← Functor.map_comp, h₁, Functor.map_comp, Category.assoc, h₂,
    Category.assoc]
  rfl

/-- The comparison of underlying sheaves between the two composite pullbacks. -/
private def squareUnderlying (Fg : InverseImageData Lg) (Fk : InverseImageData Lk)
    (Ff : InverseImageData Lf) (Fh : InverseImageData Lh) (sq : Lg ⋙ Lk ≅ Lf ⋙ Lh)
    (A : Type u) [CommRing A] (M : Mod (constant J₁ A)) :
    (underlying (constant J₄ A)).obj
        ((pull Fg (constantMap Fg A) ⋙ pull Fk (constantMap Fk A)).obj M) ⟶
      (underlying (constant J₄ A)).obj
        ((pull Ff (constantMap Ff A) ⋙ pull Fh (constantMap Fh A)).obj M) :=
  have := squareModule₁_isIso Fg Fk A M
  inv (squareModule₁ Fg Fk A M) ≫ squareModule₂ Ff Fh sq A M

private theorem squareUnderlying_add [PreservesFiniteLimits Lg] [PreservesFiniteLimits Lk]
    (Fg : InverseImageData Lg) (Fk : InverseImageData Lk)
    (Ff : InverseImageData Lf) (Fh : InverseImageData Lh) (sq : Lg ⋙ Lk ≅ Lf ⋙ Lh)
    (A : Type u) [CommRing A] (M : Mod (constant J₁ A)) (V : C₄ᵒᵖ) (x y) :
    (squareUnderlying Fg Fk Ff Fh sq A M).hom.app V (addOp _ V x y) =
      addOp _ V ((squareUnderlying Fg Fk Ff Fh sq A M).hom.app V x)
        ((squareUnderlying Fg Fk Ff Fh sq A M).hom.app V y) := by
  have := squareModule₁_isIso Fg Fk A M
  exact BinaryCompat.extract (addOp_natural M) (squareModule₁_add Fg Fk A M)
    (squareModule₂_add Ff Fh sq A M) V x y

private theorem squareUnderlying_smul [PreservesFiniteLimits Lg] [PreservesFiniteLimits Lk]
    (Fg : InverseImageData Lg) (Fk : InverseImageData Lk)
    (Ff : InverseImageData Lf) (Fh : InverseImageData Lh) (sq : Lg ⋙ Lk ≅ Lf ⋙ Lh)
    (A : Type u) [CommRing A] (M : Mod (constant J₁ A)) (V : C₄ᵒᵖ) (r x) :
    (squareUnderlying Fg Fk Ff Fh sq A M).hom.app V (smulOp _ V r x) =
      smulOp _ V r ((squareUnderlying Fg Fk Ff Fh sq A M).hom.app V x) := by
  have := squareModule₁_isIso Fg Fk A M
  have := squareRing₁_isIso Fg Fk
  have h := BinaryCompat.extract (smulOp_natural M) (squareModule₁_smul Fg Fk A M)
    (squareModule₂_smul Ff Fh sq A M) V r x
  rw [← squareRing_eq Fg Fk Ff Fh sq, inv_hom_apply'] at h
  exact h

private theorem squareUnderlying_naturality (Fg : InverseImageData Lg)
    (Fk : InverseImageData Lk) (Ff : InverseImageData Lf) (Fh : InverseImageData Lh)
    (sq : Lg ⋙ Lk ≅ Lf ⋙ Lh) (A : Type u) [CommRing A] {M N : Mod (constant J₁ A)}
    (a : M ⟶ N) :
    squareUnderlying Fg Fk Ff Fh sq A M ≫ (underlying (constant J₄ A)).map
        ((pull Ff (constantMap Ff A) ⋙ pull Fh (constantMap Fh A)).map a) =
      (underlying (constant J₄ A)).map
          ((pull Fg (constantMap Fg A) ⋙ pull Fk (constantMap Fk A)).map a) ≫
        squareUnderlying Fg Fk Ff Fh sq A N := by
  have := squareModule₁_isIso Fg Fk A M
  have := squareModule₁_isIso Fg Fk A N
  dsimp only [squareUnderlying]
  rw [Category.assoc, IsIso.inv_comp_eq, ← squareModule₂_naturality,
    ← Category.assoc (squareModule₁ Fg Fk A M), ← squareModule₁_naturality, Category.assoc,
    IsIso.hom_inv_id_assoc]

/-- A commutation isomorphism of inverse images of sheaves of sets induces a unique
isomorphism of the constant-coefficient module pullbacks which is compatible with the
inverse-image insertions. -/
theorem pullSquare_existsUnique [PreservesFiniteLimits Lg] [PreservesFiniteLimits Lk]
    (Fg : InverseImageData Lg) (Fk : InverseImageData Lk)
    (Ff : InverseImageData Lf) (Fh : InverseImageData Lh) (sq : Lg ⋙ Lk ≅ Lf ⋙ Lh)
    (A : Type u) [CommRing A] :
    ∃! e : pull Fg (constantMap Fg A) ⋙ pull Fk (constantMap Fk A) ≅
        pull Ff (constantMap Ff A) ⋙ pull Fh (constantMap Fh A),
      ∀ M : Mod (constant J₁ A),
        Lk.map (pullInsertion Fg (constantMap Fg A) M) ≫
            pullInsertion Fk (constantMap Fk A) ((pull Fg (constantMap Fg A)).obj M) ≫
            (underlying (constant J₄ A)).map (e.hom.app M) =
          sq.hom.app ((underlying (constant J₁ A)).obj M) ≫
            Lh.map (pullInsertion Ff (constantMap Ff A) M) ≫
            pullInsertion Fh (constantMap Fh A) ((pull Ff (constantMap Ff A)).obj M) := by
  let l (M : Mod (constant J₁ A)) :=
    linearOfUnderlying (squareUnderlying Fg Fk Ff Fh sq A M)
      (squareUnderlying_add Fg Fk Ff Fh sq A M) (squareUnderlying_smul Fg Fk Ff Fh sq A M)
  have hl (M : Mod (constant J₁ A)) :
      (underlying (constant J₄ A)).map (l M) = squareUnderlying Fg Fk Ff Fh sq A M := rfl
  have hiso (M : Mod (constant J₁ A)) : IsIso (l M) := by
    have := squareModule₁_isIso Fg Fk A M
    have : IsIso ((underlying (constant J₄ A)).map (l M)) := by
      have := squareModule₂_isIso Ff Fh sq A M
      rw [hl]
      dsimp only [squareUnderlying]
      infer_instance
    exact isIso_of_reflects_iso _ (underlying (constant J₄ A))
  have hnorm (M : Mod (constant J₁ A)) :
      squareModule₁ Fg Fk A M ≫ (underlying (constant J₄ A)).map (l M) =
        squareModule₂ Ff Fh sq A M := by
    have := squareModule₁_isIso Fg Fk A M
    rw [hl]
    dsimp only [squareUnderlying]
    rw [IsIso.hom_inv_id_assoc]
  refine ⟨NatIso.ofComponents (fun M ↦ asIso (l M)) (fun {M N} a ↦ ?_), ?_, ?_⟩
  · apply (underlying (constant J₄ A)).map_injective
    simp only [Functor.map_comp, asIso_hom, hl]
    exact (squareUnderlying_naturality Fg Fk Ff Fh sq A a).symm
  · intro M
    rw [← Category.assoc]
    exact hnorm M
  · intro e he
    apply Iso.ext
    apply NatTrans.ext
    funext M
    have := squareModule₁_isIso Fg Fk A M
    apply (underlying (constant J₄ A)).map_injective
    apply (cancel_epi (squareModule₁ Fg Fk A M)).mp
    exact ((Category.assoc _ _ _).trans (he M)).trans (hnorm M).symm

end Square

end CategoryTheory.ConstantCompletion
