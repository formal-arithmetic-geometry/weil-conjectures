module

public import Mathlib.CategoryTheory.Endofunctor.Algebra

/-! # Comparison of fixed pairs and transport along a functor

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/
sk-thm-sf-package/prop-pur-weil-equivariance-scheme-frobenius.proof.md,
entire proof, compatibility with pullback composition and with f.
(blueprint: lem-pur-natural-comparison-functor-transport)
-/

@[expose] public section

universe uC vC uD vD

namespace CategoryTheory.Endofunctor.Algebra

/-- Changing the endofunctor before or after transport gives the same structure map,
with the specified two-sided inverse, and transports intertwiners to intertwiners.
The fixed pairs are precisely endofunctor algebras with invertible structure map,
as in def-weil-endofunctor-fixed-pair-category; no extra algebra laws are imposed.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/
sk-thm-sf-package/prop-pur-weil-equivariance-scheme-frobenius.proof.md,
entire proof, compatibility with pullback composition and with f.
(blueprint: lem-pur-natural-comparison-functor-transport)

Proof plan: (1) Cancel cG and cF in the assumed comparison square to obtain
kD followed by cG inverse = cF inverse followed by L(kC).
(2) Postcompose with L of the structure map and apply functoriality of L.
This identifies the two structure maps on the same object L(M).
(3) The inverse of kC followed by the structure map is the inverse structure
map followed by kC inverse. Apply L and postcompose with cF. Associativity,
the two inverse identities, and preservation of composition and identities by L
verify both inverse equations displayed below.
(4) Naturality of kC turns an intertwiner for GC into one for FC. Naturality
of cF, after cancelling its invertible components, then shows that L(h)
intertwines the common transported maps. These are the same underlying arrows
in both constructions. (5) Objects and their structure maps specify fixed pairs;
identities and composition are inherited from the base categories. Hence these
object and arrow formulas identify both orders of construction. These steps use
only def-nagata-category and def-weil-endofunctor-fixed-pair-category. -/
theorem naturalComparisonFunctorTransport
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (L : C ⥤ D) (FC GC : C ⥤ C) (FD GD : D ⥤ D)
    (kC : FC ≅ GC) (kD : FD ≅ GD)
    (cF : FC ⋙ L ≅ L ⋙ FD) (cG : GC ⋙ L ≅ L ⋙ GD)
    (compat : ∀ M : C,
      L.map (kC.hom.app M) ≫ cG.hom.app M = cF.hom.app M ≫ kD.hom.app (L.obj M))
    (A : Algebra GC) [IsIso A.str] :
    (kD.hom.app (L.obj A.a) ≫ cG.inv.app A.a ≫ L.map A.str =
      cF.inv.app A.a ≫ L.map (kC.hom.app A.a ≫ A.str)) ∧
    ((cF.inv.app A.a ≫ L.map (kC.hom.app A.a ≫ A.str)) ≫
      (L.map (inv A.str ≫ kC.inv.app A.a) ≫ cF.hom.app A.a) =
        𝟙 (FD.obj (L.obj A.a))) ∧
    ((L.map (inv A.str ≫ kC.inv.app A.a) ≫ cF.hom.app A.a) ≫
      (cF.inv.app A.a ≫ L.map (kC.hom.app A.a ≫ A.str)) = 𝟙 (L.obj A.a)) ∧
    (∀ (B : Algebra GC) (_hB : IsIso B.str) (h : A ⟶ B),
      (cF.inv.app A.a ≫ L.map (kC.hom.app A.a ≫ A.str)) ≫ L.map h.f =
        FD.map (L.map h.f) ≫ cF.inv.app B.a ≫ L.map (kC.hom.app B.a ≫ B.str)) := by
  have square : kD.hom.app (L.obj A.a) ≫ cG.inv.app A.a =
      cF.inv.app A.a ≫ L.map (kC.hom.app A.a) := by
    have eq := congrArg (fun f ↦ cF.inv.app A.a ≫ f ≫ cG.inv.app A.a) (compat A.a)
    simpa [Category.assoc] using eq.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Category.assoc, square, Category.assoc, ← L.map_comp]
  · rw [Category.assoc, ← L.map_comp_assoc]
    simp [Category.assoc]
  · simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [← L.map_comp]
    simp [Category.assoc]
  · intro B _hB h
    have intertwine : (kC.hom.app A.a ≫ A.str) ≫ h.f =
        FC.map h.f ≫ (kC.hom.app B.a ≫ B.str) := by
      rw [Category.assoc, ← h.h, ← Category.assoc, ← kC.hom.naturality,
        Category.assoc]
    calc
      _ = cF.inv.app A.a ≫ L.map ((kC.hom.app A.a ≫ A.str) ≫ h.f) := by
        simp only [L.map_comp, Category.assoc]
      _ = cF.inv.app A.a ≫ L.map (FC.map h.f ≫ (kC.hom.app B.a ≫ B.str)) := by
        rw [intertwine]
      _ = FD.map (L.map h.f) ≫ cF.inv.app B.a ≫
          L.map (kC.hom.app B.a ≫ B.str) := by
        rw [L.map_comp, ← Category.assoc]
        simpa only [Functor.comp_map, Category.assoc] using
          congrArg (fun f ↦ f ≫ L.map (kC.hom.app B.a ≫ B.str))
            (cF.inv.naturality h.f).symm

end CategoryTheory.Endofunctor.Algebra
