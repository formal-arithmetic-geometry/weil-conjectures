module
public import Sheaf.AlgebraicGeometry.AffineStructureAlgebraFullyFaithful
@[expose] public section
universe u
open CategoryTheory Opposite TopologicalSpace
namespace AlgebraicGeometry
/-- The local chart compatibility for the relative-spectrum anti-equivalence.
Source: Stacks Project, Morphisms, Lemma 01SA and Constructions, Lemma 01LX
(blueprint: lem-weil-pbc-relative-spec-morphism-chart).

Proof: Apply naturality of the counit of the equivalence to an algebra morphism,
then use the affine `toSpecΓ` naturality lemma and functoriality of `Spec.map`. -/
theorem relative_spec_morphism_chart (S : Scheme.{u})
    (E : (ObjectProperty.FullSubcategory (fun Y : Over S ↦ IsAffineHom Y.hom))ᵒᵖ ≌
      ObjectProperty.FullSubcategory (fun A : S.CommAlgebraSheaf ↦ A.toModule.IsQuasicoherent))
    (hobj : ∀ Y, (E.functor.obj (op Y)).obj = Under.mk (⟨Y.obj.hom.c⟩ : Scheme.sheaf _ ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} Y.obj.hom.base).obj (Scheme.sheaf _)))
    : ∀ (A B) (φ : A ⟶ B) (U : S.Opens), IsAffineOpen U →
      (E.inverse.map φ).unop.hom.left.resLE ((E.inverse.obj A).unop.obj.hom ⁻¹ᵁ U)
          ((E.inverse.obj B).unop.obj.hom ⁻¹ᵁ U)
          (by rw [← Scheme.Hom.comp_preimage, Over.w (E.inverse.map φ).unop.hom]) ≫
        ((E.inverse.obj A).unop.obj.hom ⁻¹ᵁ U).toSpecΓ ≫
        Spec.map (((E.counitIso.app A).inv.hom ≫
          eqToHom (hobj (E.inverse.obj A).unop)).right.hom.app (op U)) =
      ((E.inverse.obj B).unop.obj.hom ⁻¹ᵁ U).toSpecΓ ≫
        Spec.map (((E.counitIso.app B).inv.hom ≫
          eqToHom (hobj (E.inverse.obj B).unop)).right.hom.app (op U)) ≫
        Spec.map (φ.hom.right.hom.app (op U)) := by
  sorry
end AlgebraicGeometry
