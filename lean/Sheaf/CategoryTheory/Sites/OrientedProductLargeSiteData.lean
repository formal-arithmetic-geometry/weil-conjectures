/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q65
-/
module

public import Sheaf.CategoryTheory.Sites.OrientedProductUniversal

/-! # Definitions of oriented triple sites with independent universes

Source: ILO Exposé XI §§1.1–1.7
(blueprint: def-trf-large-oriented-site-data).

This generalizes the recorded triple-site construction and its universal statement to sites
with objects in `Type w` and morphisms in `Type v`, such as the small etale sites. Sheaves take
values in `Type (max v w)`, the containing universe of `def-weil-size-convention`. The comma
category and the three generators are unchanged; no homomorphism universe is enlarged. For
`v = w` this is exactly the recorded statement `CategoryTheory.OrientedProduct.universal`.
-/

@[expose] public section
set_option autoImplicit false
universe v w e ve
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.OrientedProduct

/-- Associated sheaves of representables on a site with independent universes, valued in the
containing universe `Type (max v w)`; no subcanonicity is assumed.
Source: ILO XI §§1.2–1.3 (blueprint: def-trf-large-oriented-site-data). -/
noncomputable def largeAssociated {C : Type w} [Category.{v} C] (J : GrothendieckTopology C) :
    C ⥤ Sheaf J (Type (max v w)) :=
  uliftYoneda.{w} ⋙ presheafToSheaf J (Type (max v w))

variable {C₁ C₂ D : Type w} [Category.{v} C₁] [Category.{v} C₂] [Category.{v} D]
  [HasFiniteLimits C₁] [HasFiniteLimits C₂] [HasFiniteLimits D]

/-- The category of triples, using Mathlib's comma and product categories.
Source: ILO XI §1.1(i) (blueprint: def-trf-large-oriented-site-data). -/
abbrev largeTriples (F : D ⥤ C₁) (G : D ⥤ C₂) := Comma (𝟭 (C₁ × C₂)) (F.prod' G)

/-- The three generating covering types. Unchanged components are allowed to be isomorphisms;
this is the isomorphism closure of the literal generators in XI §1.1(ii)(a)–(c).
Source: ILO XI §1.1(ii) (blueprint: def-trf-large-oriented-site-data). -/
def largeGenerators (J₁ : Pretopology C₁) (J₂ : Pretopology C₂)
    (F : D ⥤ C₁) (G : D ⥤ C₂) : Precoverage (largeTriples F G) where
  coverings Z := {R |
    (∃ (I : Type (max v w)) (Zᵢ : I → largeTriples F G) (r : ∀ i, Zᵢ i ⟶ Z),
      R = Presieve.ofArrows Zᵢ r ∧
      ((Presieve.ofArrows (fun i ↦ (Zᵢ i).left.1) (fun i ↦ (r i).left.1) ∈ J₁ Z.left.1 ∧
        ∀ i, IsIso (r i).right ∧ IsIso (r i).left.2) ∨
       (Presieve.ofArrows (fun i ↦ (Zᵢ i).left.2) (fun i ↦ (r i).left.2) ∈ J₂ Z.left.2 ∧
        ∀ i, IsIso (r i).right ∧ IsIso (r i).left.1))) ∨
    (∃ (Z' : largeTriples F G) (r : Z' ⟶ Z), R = Presieve.singleton r ∧
      IsIso r.left.1 ∧ IsPullback r.left.2 Z'.hom.2 Z.hom.2 (G.map r.right))}

/-- The generated Grothendieck topology, with no unproved data.
Source: ILO XI §1.1(ii) (blueprint: def-trf-large-oriented-site-data). -/
def largeTopology (J₁ : Pretopology C₁) (J₂ : Pretopology C₂)
    (F : D ⥤ C₁) (G : D ⥤ C₂) : GrothendieckTopology (largeTriples F G) :=
  (largeGenerators J₁ J₂ F G).toGrothendieck

/-- The first site projection on objects, using final objects.
Source: ILO XI §1.3 (blueprint: def-trf-large-oriented-site-data). -/
noncomputable def largeFirstTriple (F : D ⥤ C₁) (G : D ⥤ C₂)
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (U : C₁) : largeTriples F G where
  left := (U, ⊤_ C₂)
  right := ⊤_ D
  hom := (terminal.from U ≫ inv (terminalComparison F), inv (terminalComparison G))

/-- The second site projection on objects.
Source: ILO XI §1.3 (blueprint: def-trf-large-oriented-site-data). -/
noncomputable def largeSecondTriple (F : D ⥤ C₁) (G : D ⥤ C₂)
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (W : C₂) : largeTriples F G where
  left := (⊤_ C₁, W)
  right := ⊤_ D
  hom := (inv (terminalComparison F), terminal.from W ≫ inv (terminalComparison G))

variable (F : D ⥤ C₁) (G : D ⥤ C₂)
  [PreservesFiniteLimits F] [PreservesFiniteLimits G]

/-- The first projection site functor. Source: ILO XI §1.3
(blueprint: def-trf-large-oriented-site-data). -/
noncomputable def largeFirst : C₁ ⥤ largeTriples F G where
  obj := largeFirstTriple F G
  map r := ⟨(r, 𝟙 _), 𝟙 _, by
    apply Prod.ext <;> simp [largeFirstTriple]⟩
  map_comp _ _ := by ext <;> simp [largeFirstTriple]

/-- The second projection site functor. Source: ILO XI §1.3
(blueprint: def-trf-large-oriented-site-data). -/
noncomputable def largeSecond : C₂ ⥤ largeTriples F G where
  obj := largeSecondTriple F G
  map r := ⟨(𝟙 _, r), 𝟙 _, by
    apply Prod.ext <;> simp [largeSecondTriple]⟩
  map_comp _ _ := by ext <;> simp [largeSecondTriple]

/-- Structural arrow to the first projection triple. Source: ILO XI Lemma 1.5
(blueprint: def-trf-large-oriented-site-data). -/
noncomputable def largeToFirst (Z : largeTriples F G) : Z ⟶ (largeFirst F G).obj Z.left.1 where
  left := (𝟙 _, terminal.from _)
  right := terminal.from _
  w := Prod.ext
    ((terminalIsTerminal.isTerminalObj F _).hom_ext _ _)
    ((terminalIsTerminal.isTerminalObj G _).hom_ext _ _)

/-- Structural arrow to the second projection triple. Source: ILO XI Lemma 1.5
(blueprint: def-trf-large-oriented-site-data). -/
noncomputable def largeToSecond (Z : largeTriples F G) : Z ⟶ (largeSecond F G).obj Z.left.2 where
  left := (terminal.from _, 𝟙 _)
  right := terminal.from _
  w := Prod.ext
    ((terminalIsTerminal.isTerminalObj F _).hom_ext _ _)
    ((terminalIsTerminal.isTerminalObj G _).hom_ext _ _)

/-- The middle triple defining the orientation. Source: ILO XI §1.3
(blueprint: def-trf-large-oriented-site-data). -/
def largeMiddle (V : D) : largeTriples F G := ⟨(F.obj V, G.obj V), V, (𝟙 _, 𝟙 _)⟩

/-- The defining pullback formula, with its actual structural maps; it is required for
all compatible lifts, hence in particular for the universal lift.
Source: ILO XI §1.6, formula (1.a) (blueprint: def-trf-large-oriented-site-data). -/
def LargeHasLiftFormula (J₁ : Pretopology C₁) (J₂ : Pretopology C₂) (K : Pretopology D)
    (f : GeometricMorphism (Sheaf J₁.toGrothendieck (Type (max v w)))
      (Sheaf K.toGrothendieck (Type (max v w))))
    (g : GeometricMorphism (Sheaf J₂.toGrothendieck (Type (max v w)))
      (Sheaf K.toGrothendieck (Type (max v w))))
    (ηF : largeAssociated K.toGrothendieck ⋙ f.inverse ≅
      F ⋙ largeAssociated J₁.toGrothendieck)
    (ηG : largeAssociated K.toGrothendieck ⋙ g.inverse ≅
      G ⋙ largeAssociated J₂.toGrothendieck)
    (p₁ : GeometricMorphism (Sheaf (largeTopology J₁ J₂ F G) (Type (max v w)))
      (Sheaf J₁.toGrothendieck (Type (max v w))))
    (p₂ : GeometricMorphism (Sheaf (largeTopology J₁ J₂ F G) (Type (max v w)))
      (Sheaf J₂.toGrothendieck (Type (max v w))))
    (π₁ : largeAssociated J₁.toGrothendieck ⋙ p₁.inverse ≅
      largeFirst F G ⋙ largeAssociated (largeTopology J₁ J₂ F G))
    (π₂ : largeAssociated J₂.toGrothendieck ⋙ p₂.inverse ≅
      largeSecond F G ⋙ largeAssociated (largeTopology J₁ J₂ F G))
    (τ : (p₂.comp g).direct ⟶ (p₁.comp f).direct) : Prop :=
  ∀ (E : Type e) [Category.{ve} E], IsGrothendieckTopos.{max v w} E →
    ∀ (a : GeometricMorphism E (Sheaf J₁.toGrothendieck (Type (max v w))))
      (b : GeometricMorphism E (Sheaf J₂.toGrothendieck (Type (max v w))))
      (t : (b.comp g).direct ⟶ (a.comp f).direct)
      (h : GeometricMorphism E (Sheaf (largeTopology J₁ J₂ F G) (Type (max v w))))
      (α : (h.comp p₁).direct ≅ a.direct) (β : (h.comp p₂).direct ≅ b.direct),
      paste f g p₁ p₂ τ h a b α β = t → ∀ Z : largeTriples F G,
      IsPullback
        (h.inverse.map ((largeAssociated (largeTopology J₁ J₂ F G)).map (largeToFirst F G Z) ≫
            π₁.inv.app Z.left.1) ≫ (GeometricMorphism.inverseIso α).inv.app
              ((largeAssociated J₁.toGrothendieck).obj Z.left.1))
        (h.inverse.map ((largeAssociated (largeTopology J₁ J₂ F G)).map (largeToSecond F G Z) ≫
            π₂.inv.app Z.left.2) ≫ (GeometricMorphism.inverseIso β).inv.app
              ((largeAssociated J₂.toGrothendieck).obj Z.left.2))
        (a.inverse.map ((largeAssociated J₁.toGrothendieck).map Z.hom.1 ≫ ηF.inv.app Z.right) ≫
          (GeometricMorphism.inverseMate t).app ((largeAssociated K.toGrothendieck).obj Z.right))
        (b.inverse.map ((largeAssociated J₂.toGrothendieck).map Z.hom.2 ≫ ηG.inv.app Z.right))

/-- The orientation on associated representables, including invertibility of the type-(c)
structural arrow. Source: ILO XI §1.3
(blueprint: def-trf-large-oriented-site-data). -/
def LargeOrientationFormula (J₁ : Pretopology C₁) (J₂ : Pretopology C₂) (K : Pretopology D)
    (f : GeometricMorphism (Sheaf J₁.toGrothendieck (Type (max v w)))
      (Sheaf K.toGrothendieck (Type (max v w))))
    (g : GeometricMorphism (Sheaf J₂.toGrothendieck (Type (max v w)))
      (Sheaf K.toGrothendieck (Type (max v w))))
    (ηF : largeAssociated K.toGrothendieck ⋙ f.inverse ≅
      F ⋙ largeAssociated J₁.toGrothendieck)
    (ηG : largeAssociated K.toGrothendieck ⋙ g.inverse ≅
      G ⋙ largeAssociated J₂.toGrothendieck)
    (p₁ : GeometricMorphism (Sheaf (largeTopology J₁ J₂ F G) (Type (max v w)))
      (Sheaf J₁.toGrothendieck (Type (max v w))))
    (p₂ : GeometricMorphism (Sheaf (largeTopology J₁ J₂ F G) (Type (max v w)))
      (Sheaf J₂.toGrothendieck (Type (max v w))))
    (π₁ : largeAssociated J₁.toGrothendieck ⋙ p₁.inverse ≅
      largeFirst F G ⋙ largeAssociated (largeTopology J₁ J₂ F G))
    (π₂ : largeAssociated J₂.toGrothendieck ⋙ p₂.inverse ≅
      largeSecond F G ⋙ largeAssociated (largeTopology J₁ J₂ F G))
    (τ : (p₂.comp g).direct ⟶ (p₁.comp f).direct) : Prop :=
  ∀ V : D,
    ∃ (_ : IsIso ((largeAssociated (largeTopology J₁ J₂ F G)).map
            (largeToFirst F G (largeMiddle F G V)))),
    (GeometricMorphism.inverseMate τ).app ((largeAssociated K.toGrothendieck).obj V) =
            p₁.inverse.map (ηF.hom.app V) ≫ π₁.hom.app (F.obj V) ≫
            inv ((largeAssociated (largeTopology J₁ J₂ F G)).map
              (largeToFirst F G (largeMiddle F G V))) ≫
            (largeAssociated (largeTopology J₁ J₂ F G)).map
              (largeToSecond F G (largeMiddle F G V)) ≫
            π₂.inv.app (G.obj V) ≫ p₂.inverse.map (ηG.inv.app V)

end CategoryTheory.OrientedProduct
