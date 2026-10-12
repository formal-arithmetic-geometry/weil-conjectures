module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Sheaf.Paper.DerivedHomMayerVietoris

/-! Auxiliary descent theorem assuming diagonal transition maps are identities.
Source: Stacks Project, Sheaves, Lemmas 00AL and 00AM.
(blueprint: lem-weil-pbc-module-object-open-descent-aux-diagonal)
-/

@[expose] public section

universe u v w

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

/-- Descent of module objects when the diagonal transition maps are identities.
The proof constructs compatible families on each open and glues them componentwise;
the diagonal assumption is used to show the projection and reconstruction maps are
mutual inverses.
(blueprint: lem-weil-pbc-module-object-open-descent-aux-diagonal)
Proof: construct the compatible-family sheaf componentwise, glue sections using local
sheaf axioms, and use diagonal and cocycle identities to prove projection and
reconstruction are inverse. -/
theorem module_object_open_descent_aux
    (X : RingedSpace.{u}) (I : Type w) (U : I → Opens X)
    (hcover : ⨆ i, U i = ⊤)
    (Fi : ∀ i : I, SheafOfModules.{max u v} ((moduleRings X).over (U i)))
    (φij : ∀ i j : I,
      (SheafOfModules.overMap (moduleRings X) (homOfLE inf_le_left : U i ⊓ U j ⟶ U i)).obj
          (Fi i) ≅
        (SheafOfModules.overMap (moduleRings X)
          (homOfLE inf_le_right : U i ⊓ U j ⟶ U j)).obj (Fi j))
    (hdiag : ∀ (i : I) (W : Opens X) (hi : W ≤ U i),
      (φij i i).hom.val.app (op (Over.mk (homOfLE (le_inf hi hi)))) =
        𝟙 _) :
    (∀ (i j k : I) (W : Opens X)
      (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k),
      (φij i k).hom.val.app (op (Over.mk (homOfLE (le_inf hi hk)))) =
        (φij i j).hom.val.app (op (Over.mk (homOfLE (le_inf hi hj)))) ≫
          (φij j k).hom.val.app (op (Over.mk (homOfLE (le_inf hj hk))))) →
    ∃ (H : SheafOfModules.{max u v} (moduleRings X))
      (φi : ∀ i : I, H.over (U i) ≅ Fi i),
      ∀ (i j : I) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j),
        (φi i).hom.val.app (op (Over.mk (homOfLE hi))) ≫
            (φij i j).hom.val.app (op (Over.mk (homOfLE (le_inf hi hj)))) =
          (φi j).hom.val.app (op (Over.mk (homOfLE hj))) := by
  sorry

end AlgebraicGeometry
