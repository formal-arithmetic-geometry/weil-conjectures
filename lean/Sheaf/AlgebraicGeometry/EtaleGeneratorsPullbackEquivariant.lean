/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullback
public import Sheaf.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleIsoTorsor
import WeilConjectures.CategoryTheory.Sites.Torsor
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Pulling back the torsor of generators

Source: Stacks Project, Tag 040E, pullback of local generators, and Tag 03AH.
(blueprint: lem-sc-etale-generators-pullback-equivariant)
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Pullback of generators gives an equivariant map from the inverse-image torsor
into the generator torsor of the tensor pullback.

Source: Stacks Project, Tag 040E, functoriality of the Isom torsor; Tag 03AH.
(blueprint: lem-sc-etale-generators-pullback-equivariant)

Proof: On a trivializing open U, a generator s of L gives the generator 1 tensor s
of the tensor pullback. On an etale object over U, use the pullback of this
trivialization and the composition isomorphism for module pullback. This construction
commutes with restrictions and hence defines a morphism out of the sheafified set
inverse image. Transport this morphism through eT. For each local unit a,
1 tensor (a s) = c_f(a) (1 tensor s). The assumed compatibility of eT with the
pulled-back action gives equivariance on the images of the adjunction units. Every
section of the sheafified inverse image is locally represented by such an image,
and the action is likewise locally represented by pulled-back group sections.
The equivariance identity therefore holds locally and then globally by the sheaf axiom.
The construction is independent of the trivializing cover since its maps agree on
intersections, by compatibility with restrictions. -/
theorem etale_generators_pullback_equivariant
    {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} L]
    [SheafOfModules.IsInvertible.{u, u, u} ((tensorPullback f).obj L)]
    (T' : Sheaf.Torsor ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj X.gmSheaf))
    (eT : (Scheme.etaleSetPullback f).obj (etaleIsoTorsor L).sheaf ≅ T'.sheaf)
    (heT : ∀ (W : X.Etale) (g : X.gmSheaf.obj.obj (op W))
        (t : (etaleIsoTorsor L).sheaf.obj.obj (op W)),
          eT.hom.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W))
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
              (X.smallGrothendieckTopology @Etale)
              (Y.smallGrothendieckTopology @Etale)).unit.app
                  (etaleIsoTorsor L).sheaf).hom.app (op W)
                ((etaleIsoTorsor L).vadd (op W) g t)) =
          T'.vadd (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W))
            (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
                X.gmSheaf).hom.app
              (op W) g)
            (eT.hom.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W))
              (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
                (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
                (X.smallGrothendieckTopology @Etale)
                (Y.smallGrothendieckTopology @Etale)).unit.app
                  (etaleIsoTorsor L).sheaf).hom.app (op W) t))) :
    ∃ σ : T'.sheaf ⟶ (etaleIsoTorsor ((tensorPullback f).obj L)).sheaf,
      ∀ (U : Y.Etaleᵒᵖ)
        (a : ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj X.gmSheaf).obj.obj U)
        (t : T'.sheaf.obj.obj U),
        σ.hom.app U (T'.vadd U a t) =
          (etaleIsoTorsor ((tensorPullback f).obj L)).vadd U
            ((upperStarGmSheafToGmSheaf f).hom.app U a) (σ.hom.app U t) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
