module

public import Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Strict structures and intertwiners under a natural comparison

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/
sk-thm-sf-package/prop-pur-weil-equivariance-scheme-frobenius.proof.md,
entire proof, preservation of the squares by precomposing the vertical maps.
(blueprint: lem-pur-natural-comparison-strict-intertwiners)
-/

@[expose] public section

universe u v

namespace CategoryTheory.Endofunctor.Algebra

/-- A natural comparison preserves and reflects the intertwiner equation for the same arrow.
Invertible structure maps remain invertible with the specified inverse, on both objects.
The algebra transport restricts to the full subcategories of strict fixed pairs; the equality
after inclusion specifies every transported object, structure map, and underlying arrow.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/
sk-thm-sf-package/prop-pur-weil-equivariance-scheme-frobenius.proof.md,
entire proof, preservation of the squares by precomposing the vertical maps.
(blueprint: lem-pur-natural-comparison-strict-intertwiners)

Proof plan: (1) Substitute the precomposed structure maps. Associativity and naturality of
kappa turn a G-intertwiner into an F-intertwiner without changing h.
(2) Conversely rewrite by naturality and cancel kappa.hom.app M using its inverse.
(3) At either object the candidate inverse is the inverse structure map followed by
kappa.inv. Associativity and the two inverse identities for each factor verify both
inverse equations, and uniqueness identifies this candidate with inv of the composite.
(4) Use these invertibility statements to restrict functorOfNatTrans kappa.hom to the
full subcategories with invertible structure map. Its object formula precomposes the
structure map by kappa, and its arrow formula is h itself. Identities and composition
are inherited from C, so the restriction is a functor with the displayed inclusion
equality. These steps use def-nagata-category and def-weil-endofunctor-fixed-pair-category. -/
theorem naturalComparisonStrictIntertwiners
    {C : Type u} [Category.{v} C] (F G : C ⥤ C) (kappa : F ≅ G)
    (M N : C) (phiM : G.obj M ⟶ M) (phiN : G.obj N ⟶ N) (h : M ⟶ N) :
    ((phiM ≫ h = G.map h ≫ phiN) ↔
      ((kappa.hom.app M ≫ phiM) ≫ h = F.map h ≫ (kappa.hom.app N ≫ phiN))) ∧
    (∀ (_hM : IsIso phiM),
      IsIso (kappa.hom.app M ≫ phiM) ∧
      inv (kappa.hom.app M ≫ phiM) = inv phiM ≫ kappa.inv.app M ∧
      (kappa.hom.app M ≫ phiM) ≫ (inv phiM ≫ kappa.inv.app M) = 𝟙 (F.obj M) ∧
      (inv phiM ≫ kappa.inv.app M) ≫ (kappa.hom.app M ≫ phiM) = 𝟙 M) ∧
    (∀ (_hN : IsIso phiN),
      IsIso (kappa.hom.app N ≫ phiN) ∧
      inv (kappa.hom.app N ≫ phiN) = inv phiN ≫ kappa.inv.app N ∧
      (kappa.hom.app N ≫ phiN) ≫ (inv phiN ≫ kappa.inv.app N) = 𝟙 (F.obj N) ∧
      (inv phiN ≫ kappa.inv.app N) ≫ (kappa.hom.app N ≫ phiN) = 𝟙 N) ∧
    (∃ T :
      ObjectProperty.FullSubcategory (fun A : Algebra G ↦ IsIso A.str) ⥤
        ObjectProperty.FullSubcategory (fun A : Algebra F ↦ IsIso A.str),
      T ⋙ ObjectProperty.ι (fun A : Algebra F ↦ IsIso A.str) =
        ObjectProperty.ι (fun A : Algebra G ↦ IsIso A.str) ⋙
          functorOfNatTrans kappa.hom) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · intro e
      rw [Category.assoc, e, ← Category.assoc, ← kappa.hom.naturality h,
        Category.assoc]
    · intro e
      apply (cancel_epi (kappa.hom.app M)).1
      simpa only [← Category.assoc, kappa.hom.naturality h] using e
  · intro hM
    refine ⟨inferInstance, ?_, ?_, ?_⟩
    · simp
    · simp [Category.assoc]
    · simp [Category.assoc]
  · intro hN
    refine ⟨inferInstance, ?_, ?_, ?_⟩
    · simp
    · simp [Category.assoc]
    · simp [Category.assoc]
  · refine ⟨ObjectProperty.lift (fun A : Algebra F ↦ IsIso A.str)
      (ObjectProperty.ι (fun A : Algebra G ↦ IsIso A.str) ⋙
        functorOfNatTrans kappa.hom) ?_, rfl⟩
    intro A
    change IsIso (kappa.hom.app A.obj.a ≫ A.obj.str)
    have := A.property
    infer_instance

end CategoryTheory.Endofunctor.Algebra
