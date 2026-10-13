module

public import Sheaf.AlgebraicGeometry.EtaleTensorSections
public import Mathlib.AlgebraicGeometry.Modules.Tilde

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- The prescribed comparison on global sections, constructed from two module
isomorphisms rather than chosen from an existence theorem.
Source: Stacks Descent 03DR, equation (35.8.1), and 03DU, item 4.
(blueprint: lem-weil-pbc-etale-open-qcoherent-identification-naturality) -/
noncomputable def etaleOpenTensorSectionsComponentIso {X U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (F : X.Modules) (v : U.Etale) :
    Γ((Scheme.Modules.tensorPullback (v.hom ≫ j)).obj F, ⊤) ≅
      Γ((Scheme.Modules.tensorPullback v.hom).obj
        ((Scheme.Modules.restrictFunctor j).obj F), ⊤) :=
  ((Scheme.Modules.toPresheaf v.left) ⋙
    (evaluation _ AddCommGrpCat.{u}).obj (Opposite.op ⊤)).mapIso
      (((Scheme.Modules.tensorSectionsComp v.hom j).app F).symm ≪≫
        (Scheme.Modules.tensorPullback v.hom).mapIso
          (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction j)).leftAdjointUniq
            (Scheme.Modules.restrictAdjunction j)).app F))

/-- The explicit section comparisons commute with an etale restriction.
Source: Stacks Descent 03DR, equation (35.8.1), and 03DU, item 4.
(blueprint: lem-weil-pbc-etale-open-qcoherent-identification-naturality)

Proof: expand each restriction as the canonical unit for g followed by the normalized
composition comparison and transport along the triangle equation. Naturality of the
unit moves the pullback of the tensor/restriction comparison past section pullback.
The associativity equation for normalized composition, applied to g.left, v.hom and j,
moves the inverse comparison for v.hom and j past the composition comparison for g.
Naturality of tensorSectionsComp moves the module comparison through the remaining
composition map. The two transports agree by g.w and associativity of scheme
composition. Evaluating these module morphism equations at the whole source scheme
proves the displayed equality. Identity arrows give the identity square; for the empty
scheme or the zero module both sides are the unique section homomorphism. -/
theorem etaleOpenTensorSectionsComponent_naturality {X U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (F : X.Modules) {v w : U.Etale} (g : w ⟶ v) :
    Scheme.Modules.etaleTensorSectionsRestriction F
        ((MorphismProperty.Over.map ⊤ (inferInstance : Etale j)).map g) ≫
      (etaleOpenTensorSectionsComponentIso j F w).hom =
    (etaleOpenTensorSectionsComponentIso j F v).hom ≫
      Scheme.Modules.etaleTensorSectionsRestriction
        ((Scheme.Modules.restrictFunctor j).obj F) g := by
  sorry

end AlgebraicGeometry
