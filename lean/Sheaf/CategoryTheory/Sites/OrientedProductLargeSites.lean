/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q65
-/
module

public import Sheaf.CategoryTheory.Sites.OrientedProductUniversal
import Sheaf.CategoryTheory.RingedToposMorphism
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.CategoryTheory.SiteInverseImageTensor
import Sheaf.CategoryTheory.SiteOfSheafGenerators
import Sheaf.CategoryTheory.Sites.GrothendieckTopos

/-! # Oriented triple sites with independent object and morphism universes

Source: ILO Exposé XI §§1.1–1.7
(blueprint: lem-trf-oriented-product-universal).

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
Source: ILO XI §§1.2–1.3 (blueprint: lem-trf-oriented-product-universal). -/
noncomputable def largeAssociated {C : Type w} [Category.{v} C] (J : GrothendieckTopology C) :
    C ⥤ Sheaf J (Type (max v w)) :=
  uliftYoneda.{w} ⋙ presheafToSheaf J (Type (max v w))

variable {C₁ C₂ D : Type w} [Category.{v} C₁] [Category.{v} C₂] [Category.{v} D]
  [HasFiniteLimits C₁] [HasFiniteLimits C₂] [HasFiniteLimits D]

/-- The category of triples, using Mathlib's comma and product categories.
Source: ILO XI §1.1(i) (blueprint: lem-trf-oriented-product-universal). -/
abbrev largeTriples (F : D ⥤ C₁) (G : D ⥤ C₂) := Comma (𝟭 (C₁ × C₂)) (F.prod' G)

/-- The three generating covering types. Unchanged components are allowed to be isomorphisms;
this is the isomorphism closure of the literal generators in XI §1.1(ii)(a)–(c).
Source: ILO XI §1.1(ii) (blueprint: lem-trf-oriented-product-universal). -/
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
Source: ILO XI §1.1(ii) (blueprint: lem-trf-oriented-product-universal). -/
def largeTopology (J₁ : Pretopology C₁) (J₂ : Pretopology C₂)
    (F : D ⥤ C₁) (G : D ⥤ C₂) : GrothendieckTopology (largeTriples F G) :=
  (largeGenerators J₁ J₂ F G).toGrothendieck

/-- The first site projection on objects, using final objects.
Source: ILO XI §1.3 (blueprint: lem-trf-oriented-product-universal). -/
noncomputable def largeFirstTriple (F : D ⥤ C₁) (G : D ⥤ C₂)
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (U : C₁) : largeTriples F G where
  left := (U, ⊤_ C₂)
  right := ⊤_ D
  hom := (terminal.from U ≫ inv (terminalComparison F), inv (terminalComparison G))

/-- The second site projection on objects.
Source: ILO XI §1.3 (blueprint: lem-trf-oriented-product-universal). -/
noncomputable def largeSecondTriple (F : D ⥤ C₁) (G : D ⥤ C₂)
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (W : C₂) : largeTriples F G where
  left := (⊤_ C₁, W)
  right := ⊤_ D
  hom := (inv (terminalComparison F), terminal.from W ≫ inv (terminalComparison G))

variable (F : D ⥤ C₁) (G : D ⥤ C₂)
  [PreservesFiniteLimits F] [PreservesFiniteLimits G]

/-- The first projection site functor. Source: ILO XI §1.3
(blueprint: lem-trf-oriented-product-universal). -/
noncomputable def largeFirst : C₁ ⥤ largeTriples F G where
  obj := largeFirstTriple F G
  map r := ⟨(r, 𝟙 _), 𝟙 _, by
    apply Prod.ext <;> simp [largeFirstTriple]⟩
  map_comp _ _ := by ext <;> simp [largeFirstTriple]

/-- The second projection site functor. Source: ILO XI §1.3
(blueprint: lem-trf-oriented-product-universal). -/
noncomputable def largeSecond : C₂ ⥤ largeTriples F G where
  obj := largeSecondTriple F G
  map r := ⟨(𝟙 _, r), 𝟙 _, by
    apply Prod.ext <;> simp [largeSecondTriple]⟩
  map_comp _ _ := by ext <;> simp [largeSecondTriple]

/-- Structural arrow to the first projection triple. Source: ILO XI Lemma 1.5
(blueprint: lem-trf-oriented-product-universal). -/
noncomputable def largeToFirst (Z : largeTriples F G) : Z ⟶ (largeFirst F G).obj Z.left.1 where
  left := (𝟙 _, terminal.from _)
  right := terminal.from _
  w := Prod.ext
    ((terminalIsTerminal.isTerminalObj F _).hom_ext _ _)
    ((terminalIsTerminal.isTerminalObj G _).hom_ext _ _)

/-- Structural arrow to the second projection triple. Source: ILO XI Lemma 1.5
(blueprint: lem-trf-oriented-product-universal). -/
noncomputable def largeToSecond (Z : largeTriples F G) : Z ⟶ (largeSecond F G).obj Z.left.2 where
  left := (terminal.from _, 𝟙 _)
  right := terminal.from _
  w := Prod.ext
    ((terminalIsTerminal.isTerminalObj F _).hom_ext _ _)
    ((terminalIsTerminal.isTerminalObj G _).hom_ext _ _)

/-- The middle triple defining the orientation. Source: ILO XI §1.3
(blueprint: lem-trf-oriented-product-universal). -/
def largeMiddle (V : D) : largeTriples F G := ⟨(F.obj V, G.obj V), V, (𝟙 _, 𝟙 _)⟩

/-- The defining pullback formula, with its actual structural maps; it is required for
all compatible lifts, hence in particular for the universal lift.
Source: ILO XI §1.6, formula (1.a) (blueprint: lem-trf-oriented-product-universal). -/
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

/-- The triple-site construction on sites with independent object and morphism universes has its
stated projections, canonical orientation, universal compatible lift, and inverse-image pullback
formula; topoi are tested in the containing universe `max v w`. For `v = w` this is exactly
`CategoryTheory.OrientedProduct.universal`.

Source: ILO Exposé XI §§1.1, 1.3, Theorem 1.4, §1.6 formula (1.a), and Definition 1.7
(blueprint: lem-trf-oriented-product-universal).

Proof plan (the ten steps of the DAG node; universes as in `def-weil-size-convention`):
1. Form the comma category of triples. Finite limits are componentwise. The generators
are stable under base change; their saturation defines the topology, using
lem-weil-pbc-pretopology-sheaf-condition.
2. Descent for the first two types is ordinary descent. A type-(c) map has covering
diagonal, so restriction is bijective. Yoneda and the sheafification adjunction
(def-weil-pbc-sheafification, lem-galois-yoneda-hom-bijection) make its associated map invertible.
3. The functors largeFirst and largeSecond preserve finite limits and covers. Apply
lem-weil-pbc-left-exact-site-inverse-image-tensor; adjunction and Yoneda identify their
inverse images on associated representables with the two projection formulas.
4. At V use the inverse of the type-(c) map from largeMiddle V to largeFirst (F V), followed by
its map to largeSecond (G V). Taking mates defines the displayed orientation.
5. Compute the componentwise pullbacks in XI Lemma 1.5. Yoneda and
lem-weil-pbc-sheafification-sets-exact preserve them. Cancel the type-(c) isomorphisms.
6. For a cone (a,b,t) form H(Z) by the displayed pullback. Naturality gives its action
on arrows. Finite limits commute with pullbacks by
lem-weil-pbc-site-sheaf-sets-limits-sectionwise, so H preserves finite limits.
7. The first two covering types map to pullbacks of epimorphic families; inverse images
preserve them using lem-weil-pbc-site-sheaf-sets-epi-kernel-pair-coequalizer, and their
pullbacks remain epimorphic by lem-weil-pbc-site-sheaf-sets-epi-locally-surjective.
The third type maps to an isomorphism by naturality of the inverse-image mate of t.
8. Enlarge generators of a presentation of E by the H(Z) and finite limits. Apply
lem-weil-pbc-site-of-sheaf-generators, then the left exact site inverse image theorem.
9. Evaluation on largeFirst and largeSecond gives alpha and beta. On largeMiddle V the inverse
of the first pullback projection followed by the second is exactly the mate of t.
Colimits of associated representables extend this equality to all sheaves.
10. Any other compatible lift preserves the pullback of step 5, forcing its inverse
image and its maps. Adjunction and Yoneda determine its direct image and the unique
projection-compatible isomorphism. Applying this to two site presentations gives
inverse equivalences, unique with projection and orientation compatibilities, which
is the site independence asserted in Definition 1.7.
-/
theorem universalWithLargeSites (J₁ : Pretopology C₁) (J₂ : Pretopology C₂) (K : Pretopology D)
    [F.IsContinuous K.toGrothendieck J₁.toGrothendieck]
    [G.IsContinuous K.toGrothendieck J₂.toGrothendieck]
    (f : GeometricMorphism (Sheaf J₁.toGrothendieck (Type (max v w)))
      (Sheaf K.toGrothendieck (Type (max v w))))
    (g : GeometricMorphism (Sheaf J₂.toGrothendieck (Type (max v w)))
      (Sheaf K.toGrothendieck (Type (max v w))))
    (ηF : largeAssociated K.toGrothendieck ⋙ f.inverse ≅
      F ⋙ largeAssociated J₁.toGrothendieck)
    (ηG : largeAssociated K.toGrothendieck ⋙ g.inverse ≅
      G ⋙ largeAssociated J₂.toGrothendieck) :
    ∃ (p₁ : GeometricMorphism (Sheaf (largeTopology J₁ J₂ F G) (Type (max v w)))
        (Sheaf J₁.toGrothendieck (Type (max v w))))
      (p₂ : GeometricMorphism (Sheaf (largeTopology J₁ J₂ F G) (Type (max v w)))
        (Sheaf J₂.toGrothendieck (Type (max v w))))
      (π₁ : largeAssociated J₁.toGrothendieck ⋙ p₁.inverse ≅
        largeFirst F G ⋙ largeAssociated (largeTopology J₁ J₂ F G))
      (π₂ : largeAssociated J₂.toGrothendieck ⋙ p₂.inverse ≅
        largeSecond F G ⋙ largeAssociated (largeTopology J₁ J₂ F G))
      (τ : (p₂.comp g).direct ⟶ (p₁.comp f).direct),
      IsUniversal.{max v w, e, ve} f g p₁ p₂ τ ∧
      LargeHasLiftFormula.{v, w, e, ve} F G J₁ J₂ K f g ηF ηG p₁ p₂ π₁ π₂ τ ∧
      (∀ (Q : Type (max v w + 1)) [Category.{max v w} Q], IsGrothendieckTopos.{max v w} Q →
        ∀ (q₁ : GeometricMorphism Q (Sheaf J₁.toGrothendieck (Type (max v w))))
          (q₂ : GeometricMorphism Q (Sheaf J₂.toGrothendieck (Type (max v w))))
          (σ : (q₂.comp g).direct ⟶ (q₁.comp f).direct),
          IsUniversal.{max v w, max v w + 1, max v w} f g q₁ q₂ σ →
          ∃ (h : GeometricMorphism Q (Sheaf (largeTopology J₁ J₂ F G) (Type (max v w))))
            (α : (h.comp p₁).direct ≅ q₁.direct) (β : (h.comp p₂).direct ≅ q₂.direct),
            paste f g p₁ p₂ τ h q₁ q₂ α β = σ ∧ h.direct.IsEquivalence ∧
            ∀ (h' : GeometricMorphism Q (Sheaf (largeTopology J₁ J₂ F G) (Type (max v w))))
              (α' : (h'.comp p₁).direct ≅ q₁.direct)
              (β' : (h'.comp p₂).direct ≅ q₂.direct),
              paste f g p₁ p₂ τ h' q₁ q₂ α' β' = σ →
              ∃! γ : h.direct ≅ h'.direct,
                Functor.isoWhiskerRight γ p₁.direct ≪≫ α' = α ∧
                Functor.isoWhiskerRight γ p₂.direct ≪≫ β' = β) ∧
      ∀ V : D,
        ∃ (_ : IsIso ((largeAssociated (largeTopology J₁ J₂ F G)).map
          (largeToFirst F G (largeMiddle F G V)))),
        (GeometricMorphism.inverseMate τ).app ((largeAssociated K.toGrothendieck).obj V) =
          p₁.inverse.map (ηF.hom.app V) ≫ π₁.hom.app (F.obj V) ≫
          inv ((largeAssociated (largeTopology J₁ J₂ F G)).map
            (largeToFirst F G (largeMiddle F G V))) ≫
          (largeAssociated (largeTopology J₁ J₂ F G)).map
            (largeToSecond F G (largeMiddle F G V)) ≫
          π₂.inv.app (G.obj V) ≫ p₂.inverse.map (ηG.inv.app V) := by
  sorry

end CategoryTheory.OrientedProduct
