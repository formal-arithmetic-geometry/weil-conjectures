/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Sheaf.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.CategoryTheory.Sites.Torsor

/-!
# Finite étale equivalences and transport of torsors

Source: Stacks Project Tag 0A5G, final paragraph, and Tag 03RV.
(blueprint: lem-weil-pbc-finite-etale-torsor-reflection)
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Transport by inverse image reflects isomorphisms of finite constant torsors.
Source: Stacks Project Tag 0A5G, final paragraph, using Tag 03RV.
(blueprint: lem-weil-pbc-finite-etale-torsor-reflection)

Proof: A torsor under the finite constant group M is étale locally the finite set M,
so Tag 03RV represents its underlying sheaf by a finite étale scheme. Yoneda represents
each constant action map. Inverse image of a representable is the representable of its
base change. For each m in M, translation is a sheaf endomorphism, represented by Yoneda.
The displayed equation for g the constant section m says its inverse image agrees
with translation by m on τ T: after adjunction the two maps agree on every T(W),
so the adjunction bijection makes them equal. Any section of the constant sheaf
is locally constant; naturality and the sheaf condition extend this equality to
all coefficient sections. Thus the equation specifies the full pulled-back action.
An isomorphism between τ T₁ and τ T₂ is therefore an equivariant isomorphism between
the base changes of the representatives. Fullness lifts it and its inverse; faithfulness
lifts their inverse equations and each equivariance equation. Yoneda then gives an
isomorphism of the original sheaf torsors. Empty schemes and the trivial group are
included: the argument uses neither a point nor a nonempty base. -/
theorem finiteEtale_reflects_torsor_transport
    [(@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange]
    {Y Y₀ : Scheme.{u}} (i : Y₀ ⟶ Y)
    (hFE : (MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ i).IsEquivalence)
    (M : Type (u + 1)) [AddCommGroup M] [Finite M]
    (τ : Sheaf.Torsor
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of M)) →
      Sheaf.Torsor ((upperStar AddCommGrpCat.{u + 1} i).obj
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of M))))
    (hτ : ∀ T : Sheaf.Torsor
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of M)), ∃ eT : (Scheme.etaleSetPullback i).obj T.sheaf ≅ (τ T).sheaf,
      let G := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of M)
      (∀ (W : Y.Etale) (g : G.obj.obj (op W)) (t : T.sheaf.obj.obj (op W)),
      eT.hom.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj W))
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (u + 1))
          (Y.smallGrothendieckTopology @Etale)
          (Y₀.smallGrothendieckTopology @Etale)).unit.app T.sheaf).hom.app (op W)
            (T.vadd (op W) g t)) =
      (τ T).vadd (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj W))
        (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app G).hom.app
          (op W) g)
        (eT.hom.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj W))
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (u + 1))
            (Y.smallGrothendieckTopology @Etale)
            (Y₀.smallGrothendieckTopology @Etale)).unit.app T.sheaf).hom.app (op W) t))))
    (T₁ T₂ : Sheaf.Torsor
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of M)))
    (h : τ T₁ ≈ τ T₂) : T₁ ≈ T₂ := by
  sorry

end AlgebraicGeometry.Etale
