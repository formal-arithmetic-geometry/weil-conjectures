/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal

/-!
# Inverse image commutes with internal extension of scalars

Source: the current blueprint, sec-six-functors-basics,
sk-thm-sfb-qlbar-two-colimit/lem-sfb-extend-to-qlbar-constructible.proof.md,
final clause on tensoring local finite presentations on strata.
(blueprint: lem-sfb-internal-extension-inverse-image)
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Inverse image commutes naturally with extension along an arbitrary morphism of
commutative internal ring objects. The rings on the target site are the actual inverse
images. Evaluating the natural isomorphism at `M` gives
`F_S (S ⊗_R M) ≅ F(S) ⊗_{F(R)} F_R(M)`.

Source: the current blueprint, sec-six-functors-basics,
sk-thm-sfb-qlbar-two-colimit/lem-sfb-extend-to-qlbar-constructible.proof.md,
final clause on restricting extended presentations to strata and pro-étale covers.
(blueprint: lem-sfb-internal-extension-inverse-image)

Proof:
1. Write F = g⁻¹ and G = g_*. The monoidal adjunction F ⊣ G lifts to
   F.mapMod A ⊣ G.mapMod (F.obj A) ⋙ Mod.comap (unit.app A), for A = R,S.
   Compose these with the extension--restriction adjunctions along φ and F.map φ.
2. Naturality of the unit gives φ ≫ unit.app S = unit.app R ≫ G.map (F.map φ).
   Restriction along these equal composites is naturally isomorphic, by
   Mod.comapComp and Mod.comapCongr.
3. G.mapModComapIso identifies transport after restriction along F.map φ with
   restriction along G.map (F.map φ) after transport. Together with step 2 this
   identifies the two composite right adjoints.
4. Transport one composite adjunction along this isomorphism and apply uniqueness
   of left adjoints. This produces the required natural isomorphism of module-valued
   functors, with the actual inverse-image rings and the displayed orientation.
-/
theorem internal_extension_inverse_image
    {Z X : Scheme.{u}} (g : Z ⟶ X)
    (R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] :
    Nonempty (Mod.extendScalars φ ⋙ (upperStar Ab.{u + 1} g).mapMod S ≅
      (upperStar Ab.{u + 1} g).mapMod R ⋙
        Mod.extendScalars ((upperStar Ab.{u + 1} g).map φ)) := by
  let F := upperStar Ab.{u + 1} g
  let G := lowerStar Ab.{u + 1} g
  let adj := upperStarLowerStarAdjunction Ab.{u + 1} g
  have sq : φ ≫ adj.unitAlgHom S = adj.unitAlgHom R ≫ G.map (F.map φ) :=
    adj.unit.naturality φ
  let e : (G.mapMod (F.obj S) ⋙ Mod.comap (adj.unitAlgHom S)) ⋙ Mod.comap φ ≅
      Mod.comap (F.map φ) ⋙ (G.mapMod (F.obj R) ⋙ Mod.comap (adj.unitAlgHom R)) :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (G.mapMod (F.obj S))
        ((Mod.comapComp φ (adj.unitAlgHom S)).symm ≪≫
          Mod.comapCongr sq ≪≫
          Mod.comapComp (adj.unitAlgHom R) (G.map (F.map φ))) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (G.mapModComapIso (F.map φ)).symm
        (Mod.comap (adj.unitAlgHom R)) ≪≫
      Functor.associator _ _ _
  exact ⟨((Mod.extendRestrictAdjunction φ).comp (adj.mapModAdjunction S)).leftAdjointUniq
    (((adj.mapModAdjunction R).comp (Mod.extendRestrictAdjunction (F.map φ))).ofNatIsoRight
      e.symm)⟩

end AlgebraicGeometry.ProEtale
