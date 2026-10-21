/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Sheaf.CategoryTheory.ExtUniverseChange

/-! # Degree zero of the cohomology map induced by an adjunction

Source: Stacks Project, Tags 01F7 and 03AX.
-/

@[expose] public section
universe u v u' v' w t t'
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.Sheaf
noncomputable section
attribute [local irreducible] constantSheaf constantSheafAdj Adjunction.leftAdjointUniq

private theorem homEquiv_uniq_inv {A B : Type*} [Category* A] [Category* B]
    {L L' : A ⥤ B} {R : B ⥤ A} (a : L ⊣ R) (b : L' ⊣ R)
    {X : A} {Y : B} (f : L.obj X ⟶ Y) :
    b.homEquiv X Y ((a.leftAdjointUniq b).inv.app X ≫ f) = a.homEquiv X Y f := by
  rw [Adjunction.homEquiv_unit, R.map_comp, ← Category.assoc,
    Adjunction.leftAdjointUniq_inv_app, Adjunction.unit_leftAdjointUniq_hom_app]
  rfl

private theorem composite_homEquiv
    {A B E : Type*} [Category* A] [Category* B] [Category* E]
    {CX : A ⥤ B} {SX : B ⥤ A} {CY : A ⥤ E} {SY : E ⥤ A}
    (aX : CX ⊣ SX) (aY : CY ⊣ SY)
    {L : B ⥤ E} {R : E ⥤ B} (adj : L ⊣ R) (σ : R ⋙ SX ≅ SY)
    {Z : A} {F : B} {G : E} (a : CX.obj Z ⟶ F) (ψ : L.obj F ⟶ G) :
    aY.homEquiv Z G
        ((((aX.comp adj).ofNatIsoRight σ).leftAdjointUniq aY).inv.app Z ≫
          L.map a ≫ ψ) =
      aX.homEquiv Z F a ≫ SX.map (adj.homEquiv F G ψ) ≫ σ.hom.app G := by
  rw [homEquiv_uniq_inv, Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.comp_homEquiv]
  change aX.homEquiv _ _ (adj.homEquiv _ _ (L.map a ≫ ψ)) ≫ σ.hom.app G = _
  rw [adj.homEquiv_naturality_left,
    aX.homEquiv_naturality_right, Category.assoc]

section PullbackMap
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [esJ : HasExt.{t} (Sheaf J AddCommGrpCat.{w})]
  [esK : HasExt.{t} (Sheaf K AddCommGrpCat.{w})]
  (L : Sheaf J AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w})
  [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  (e : (constantSheaf K AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift.{w} ℤ)) ≅
    L.obj ((constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift.{w} ℤ))))

/-- Exact inverse image followed by a coefficient morphism, with its Ext data explicit. -/
@[irreducible]
def cohomologyPullbackMap (F : Sheaf J AddCommGrpCat.{w})
    (G : Sheaf K AddCommGrpCat.{w}) (ψ : L.obj F ⟶ G) (q : ℕ) : H F q → H G q :=
  Abelian.Ext.mapExactFunctorWithCoefficients L e.hom ψ q

/-- The concrete Ext construction agrees with the standard cohomology maps.
Source: Mathlib's Sheaf.H.map_apply and H.mapFunctor_apply.
(blueprint: lem-weil-pbc-adjunction-cohomology-pullback-zero)

Proof: Both standard maps are Yoneda composition with their coefficient
morphisms, and exact inverse image acts by Ext.mapExactFunctor. -/
theorem cohomologyPullbackMap_apply
    (F : Sheaf J AddCommGrpCat.{w}) (G : Sheaf K AddCommGrpCat.{w})
    (ψ : L.obj F ⟶ G) (q : ℕ) (x : H F q) :
    cohomologyPullbackMap L e F G ψ q x = H.map.{t} ψ q (H.mapFunctor.{t} L e F q x) := by
  unfold cohomologyPullbackMap Abelian.Ext.mapExactFunctorWithCoefficients
  rfl

/-- Exact inverse image and a morphism of short exact sequences preserve boundaries.
Source: Stacks Project, Tags 010T and 03AX.
(blueprint: lem-weil-pbc-adjunction-cohomology-pullback-zero)

Proof: Exact functors preserve the extension class of a short exact sequence.
Associativity of Ext composition therefore commutes inverse image and the boundary.
Naturality of the extension class for the coefficient morphism finishes the square. -/
theorem cohomologyPullbackMap_boundary
    (A : ShortComplex (Sheaf J AddCommGrpCat.{w}))
    (B : ShortComplex (Sheaf K AddCommGrpCat.{w}))
    (hA : A.ShortExact) (hB : B.ShortExact) (φ : A.map L ⟶ B)
    (q : ℕ) (x : H A.X₃ q) :
    cohomologyPullbackMap L e A.X₁ B.X₁ φ.τ₁ (q + 1) (H.δSucc.{t} hA q x) =
      H.δSucc.{t} hB q (cohomologyPullbackMap L e A.X₃ B.X₃ φ.τ₃ q x) := by
  unfold cohomologyPullbackMap Abelian.Ext.mapExactFunctorWithCoefficients
  change H.map.{t} φ.τ₁ (q + 1) (H.mapFunctor.{t} L e A.X₁ (q + 1) (H.δSucc.{t} hA q x)) = _
  have hb : H.mapFunctor.{t} L e A.X₁ (q + 1) (H.δSucc.{t} hA q x) =
      H.δSucc.{t} (hA.map_of_exact L) q (H.mapFunctor.{t} L e A.X₃ q x) := by
    simp only [H.mapFunctor_apply, H.δSucc_apply,
      Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_extClass]
    exact (Abelian.Ext.comp_assoc _ _ _ (zero_add q) rfl (by omega)).symm
  rw [hb]
  exact H.map_δSucc _ _ φ q _

/-- Pullback with a coefficient morphism specified on the right adjoint. -/
@[irreducible]
def adjointCohomologyPullbackMap
    (R : Sheaf K AddCommGrpCat.{w} ⥤ Sheaf J AddCommGrpCat.{w}) (adj : L ⊣ R)
    (F : Sheaf J AddCommGrpCat.{w}) (G : Sheaf K AddCommGrpCat.{w})
    (θ : F ⟶ R.obj G) (q : ℕ) : H F q → H G q :=
  cohomologyPullbackMap L e F G ((adj.homEquiv F G).symm θ) q

/-- Adjoint coefficient squares give commuting boundary squares.
Source: Stacks Project, Tags 010T and 03AX.
(blueprint: lem-weil-pbc-adjunction-cohomology-pullback-zero)

Proof: Adjunction turns each coefficient square into a morphism from the
exact pulled-back source sequence to the target sequence. Apply boundary
naturality for exact pullback and that morphism. -/
theorem adjointCohomologyPullbackMap_boundary
    (R : Sheaf K AddCommGrpCat.{w} ⥤ Sheaf J AddCommGrpCat.{w}) (adj : L ⊣ R)
    (A : ShortComplex (Sheaf J AddCommGrpCat.{w}))
    (B : ShortComplex (Sheaf K AddCommGrpCat.{w}))
    (hA : A.ShortExact) (hB : B.ShortExact)
    (θ₁ : A.X₁ ⟶ R.obj B.X₁) (θ₂ : A.X₂ ⟶ R.obj B.X₂)
    (θ₃ : A.X₃ ⟶ R.obj B.X₃)
    (h₁ : A.f ≫ θ₂ = θ₁ ≫ R.map B.f) (h₂ : A.g ≫ θ₃ = θ₂ ≫ R.map B.g)
    (q : ℕ) (x : H A.X₃ q) :
    adjointCohomologyPullbackMap L e R adj A.X₁ B.X₁ θ₁ (q + 1) (H.δSucc.{t} hA q x) =
      H.δSucc.{t} hB q (adjointCohomologyPullbackMap L e R adj A.X₃ B.X₃ θ₃ q x) := by
  let φ : A.map L ⟶ B := ShortComplex.homMk
    ((adj.homEquiv _ _).symm θ₁) ((adj.homEquiv _ _).symm θ₂)
    ((adj.homEquiv _ _).symm θ₃)
    (adj.homEquiv_naturality_right_square _ _ _ _ h₁).symm
    (adj.homEquiv_naturality_right_square _ _ _ _ h₂).symm
  unfold adjointCohomologyPullbackMap
  exact cohomologyPullbackMap_boundary L e A B hA hB φ q x

omit e in
/-- The adjoint form of the degree-zero pullback formula.
Source: Stacks Project, Tags 01F7 and 03AX.
(blueprint: lem-weil-pbc-adjunction-cohomology-pullback-zero)

Proof: Represent a degree-zero Ext class by its sheaf morphism. Exact inverse
image applies the left adjoint and the constant-sheaf comparison. Uniqueness
of left adjoints and the composite adjunction formula identify its section
with the right-adjoint coefficient map followed by the section comparison. -/
theorem adjointCohomologyPullbackMap_zero
    (R : Sheaf K AddCommGrpCat.{w} ⥤ Sheaf J AddCommGrpCat.{w}) (adj : L ⊣ R)
    {TX : C} {TY : D} (hX : IsTerminal TX) (hY : IsTerminal TY)
    (σ : R ⋙ (sheafSections J AddCommGrpCat.{w}).obj (op TX) ≅
      (sheafSections K AddCommGrpCat.{w}).obj (op TY))
    (F : Sheaf J AddCommGrpCat.{w}) (G : Sheaf K AddCommGrpCat.{w})
    (θ : F ⟶ R.obj G) (x : H F 0) :
    let c := Adjunction.leftAdjointUniq
      (((constantSheafAdj J AddCommGrpCat.{w} hX).comp adj).ofNatIsoRight σ)
      (constantSheafAdj K AddCommGrpCat.{w} hY)
    H.equiv₀.{t} G hY (adjointCohomologyPullbackMap L
        (c.symm.app (AddCommGrpCat.of (ULift.{w} ℤ))) R adj F G θ 0 x) =
      σ.hom.app G (θ.hom.app (op TX) (H.equiv₀.{t} F hX x)) := by
  dsimp only
  unfold adjointCohomologyPullbackMap cohomologyPullbackMap
    Abelian.Ext.mapExactFunctorWithCoefficients
  obtain ⟨a, rfl⟩ := (Abelian.Ext.mk₀_bijective _ _).2 x
  simp only [Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mk₀_comp_mk₀]
  simp only [Category.assoc, H.equiv₀, AddEquiv.trans_apply,
    ← Abelian.Ext.addEquiv₀_symm_apply, AddEquiv.apply_symm_apply]
  let aX := constantSheafAdj J AddCommGrpCat.{w} hX
  let aY := constantSheafAdj K AddCommGrpCat.{w} hY
  have he := composite_homEquiv aX aY adj σ a ((adj.homEquiv F G).symm θ)
  change AddCommGrpCat.uliftZMultiplesAddEquiv _
      (aY.homEquiv _ _ (_ ≫ L.map a ≫ (adj.homEquiv F G).symm θ)) = _
  change AddCommGrpCat.uliftZMultiplesAddEquiv _
    (aY.homEquiv _ _
      ((((aX.comp adj).ofNatIsoRight σ).leftAdjointUniq aY).inv.app _ ≫
        L.map a ≫ (adj.homEquiv F G).symm θ)) = _
  rw [he, (adj.homEquiv F G).apply_symm_apply]
  rfl

/-- The degree-zero formula with an explicitly specified constant-sheaf comparison.
Source: Stacks Project, Tags 01F7 and 03AX.
(blueprint: lem-weil-pbc-adjunction-cohomology-pullback-zero)

Proof: Replace the specified comparison by the uniqueness isomorphism, and
apply the adjoint degree-zero formula. The explicit equality lets concrete
sites reuse the formula without repeatedly unfolding their comparison data. -/
theorem adjointCohomologyPullbackMap_zero_of_eq
    (R : Sheaf K AddCommGrpCat.{w} ⥤ Sheaf J AddCommGrpCat.{w}) (adj : L ⊣ R)
    {TX : C} {TY : D} (hX : IsTerminal TX) (hY : IsTerminal TY)
    (σ : R ⋙ (sheafSections J AddCommGrpCat.{w}).obj (op TX) ≅
      (sheafSections K AddCommGrpCat.{w}).obj (op TY))
    (he : e = (Adjunction.leftAdjointUniq
      (((constantSheafAdj J AddCommGrpCat.{w} hX).comp adj).ofNatIsoRight σ)
      (constantSheafAdj K AddCommGrpCat.{w} hY)).symm.app
        (AddCommGrpCat.of (ULift.{w} ℤ)))
    (F : Sheaf J AddCommGrpCat.{w}) (G : Sheaf K AddCommGrpCat.{w})
    (θ : F ⟶ R.obj G) (x : H F 0) :
    H.equiv₀.{t} G hY (adjointCohomologyPullbackMap L e R adj F G θ 0 x) =
      σ.hom.app G (θ.hom.app (op TX) (H.equiv₀.{t} F hX x)) := by
  rw [he]
  exact adjointCohomologyPullbackMap_zero L R adj hX hY σ F G θ x


end PullbackMap
end
end CategoryTheory.Sheaf
