module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Abelian

/-! # Extension by zero for abelian Zariski sheaves

Source: literature/stacks-project/sites-modules.tex, Lemma 03DI and Definition 04IX;
blueprint: lem-weil-pbc-zariski-extension-by-zero-adjunction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry

/-- The presheaf extension by zero and its sheafification give an additive left adjoint
from abelian sheaves on an open Zariski subspace to abelian sheaves on the ambient scheme.
Source: Stacks Project, Modules on Sites, Lemma 03DI
(blueprint: lem-weil-pbc-zariski-extension-by-zero-adjunction).

The presheaf `P F` is sectionwise `F W` on opens `W ≤ U` and zero otherwise.  The
maps `θ F` satisfy the universal property of sheafification, and the displayed
adjunction is the map induced by composition with `θ F`, natural in both sheaves.
-/
theorem zariski_extension_by_zero_adjunction (X : Scheme.{u})
    (U : Opens X.toRingedSpace.carrier) :
    ∃ (L : TopCat.Sheaf AddCommGrpCat.{u} ((Opens.toTopCat X.toRingedSpace.carrier).obj U) ⥤
        TopCat.Sheaf AddCommGrpCat.{u} X.toRingedSpace.carrier)
      (P : ∀ F : TopCat.Sheaf AddCommGrpCat.{u}
          ((Opens.toTopCat X.toRingedSpace.carrier).obj U),
        (Opens X.toRingedSpace.carrier)ᵒᵖ ⥤ AddCommGrpCat.{u})
      (θ : ∀ F : TopCat.Sheaf AddCommGrpCat.{u}
          ((Opens.toTopCat X.toRingedSpace.carrier).obj U),
        P F ⟶ (TopCat.Sheaf.forget AddCommGrpCat.{u} X.toRingedSpace.carrier).obj (L.obj F)),
      Functor.Additive L ∧
      (∀ (F : TopCat.Sheaf AddCommGrpCat.{u}
          ((Opens.toTopCat X.toRingedSpace.carrier).obj U))
        (V : Opens X.toRingedSpace.carrier),
        (V ≤ U → Nonempty ((P F).obj (op V) ≅
          ((TopCat.Sheaf.forget AddCommGrpCat.{u}
            ((Opens.toTopCat X.toRingedSpace.carrier).obj U)).obj F).obj
              (op ((Opens.map (TopCat.ofHom
                ⟨(fun x : U => (x : X.toRingedSpace.carrier)),
                  continuous_subtype_val⟩)).obj V)))) ∧
        (¬ V ≤ U → IsZero ((P F).obj (op V)))) ∧
      (∀ (F : TopCat.Sheaf AddCommGrpCat.{u}
          ((Opens.toTopCat X.toRingedSpace.carrier).obj U))
        (H : TopCat.Sheaf AddCommGrpCat.{u} X.toRingedSpace.carrier)
        (η : P F ⟶ (TopCat.Sheaf.forget AddCommGrpCat.{u} X.toRingedSpace.carrier).obj H),
        ∃! ψ : L.obj F ⟶ H, θ F ≫ (TopCat.Sheaf.forget AddCommGrpCat.{u}
          X.toRingedSpace.carrier).map ψ = η) ∧
      ∃ adj : L ⊣ TopCat.Sheaf.pullback AddCommGrpCat.{u}
        (TopCat.ofHom ⟨(fun x : U => (x : X.toRingedSpace.carrier)), continuous_subtype_val⟩),
        (∀ (F : TopCat.Sheaf AddCommGrpCat.{u}
          ((Opens.toTopCat X.toRingedSpace.carrier).obj U))
          (G : TopCat.Sheaf AddCommGrpCat.{u} X.toRingedSpace.carrier),
          Function.Bijective (adj.homEquiv F G))
      := by
  sorry

end AlgebraicGeometry
