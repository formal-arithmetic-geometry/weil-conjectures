/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups NX and E5
-/
module

public import Sheaf.AlgebraicGeometry.ClassicalContinuityMap
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesImage
import Sheaf.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover

/-!
# Classicality of pro-etale module sheaves is Zariski local

Source: Weil conjectures blueprint, main-20261015, sec-proetale-coefficients,
`sk-thm-pe-constructible-comparison-local`
(blueprint: det-pe-constructible-comparison-local).

Modules over the constant sheaf of a discrete ring are encoded by sheaves valued in
`ModuleCat`. Classicality is the existing predicate
on their underlying set sheaves. Open restriction is the existing sectionwise functor
`openImmersionRestriction`, not a choice of a local presentation.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

private theorem setClassical_restrict (X : Scheme.{u}) (U : X.Opens)
    (F : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) (hF : IsClassical F) :
    IsClassical ((Scheme.proEtaleSetRestriction X (Scheme.ProEt.mk U.ι)).obj F) := by
  intro I _ _ P
  have : IsConnected I := IsCofiltered.isConnected I
  let L : U.toScheme.ProEt ⥤ X.ProEt :=
    MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale U.ι)
  let Q : AffinePresentation X I :=
    { diagram := P.diagram ⋙ L
      affine := P.affine
      etale := fun i ↦ by
        have := P.etale i
        exact inferInstanceAs (Etale ((P.diagram.obj i).hom ≫ U.ι))
      cone := L.mapCone P.cone
      affineVertex := P.affineVertex
      isLimit := Limits.isLimitOfReflects (Over.forget X)
        (Limits.isLimitOfPreserves (Over.forget U.toScheme) P.isLimit) }
  exact hF Q

/-- Classicality descends along any open covering, and restriction to any open subscheme
preserves classicality.

Source: Weil conjectures blueprint, main-20261015,
`sk-thm-pe-constructible-comparison-local`
(blueprint: det-pe-constructible-comparison-local).

Proof:
1. Work with the underlying set sheaf, as in the definition of module classicality.
   The essential-image criterion `proEtaleClassicalSheavesImage` turns each classical
   restriction into an etale presentation. Reindex the open cover by its range in
   `X.Opens`, lifted to `Type (u + 1)`, so arbitrary index universes are allowed.
2. This family covers the pro-etale site: on any object T its inverse-image opens
   cover T, and `mem_topology_of_openImmersion` makes the resulting sieve covering.
   Apply `proEtale_locallyClassical_etaleCover` to descend classicality, and convert
   back using the essential-image criterion. This is Bhatt--Scholze, Lemma 5.1.4.
3. For restriction, an affine etale presentation over an open U is an affine etale
   presentation over X after composition with the open immersion. Cofiltered limits
   are connected limits, so forgetting either over-category preserves the limit;
   the forgetful functor also reflects it. The section diagrams and their continuity
   maps are definitionally the same. Apply classicality on X to that presentation. -/
theorem proEtaleClassical_zariskiLocal (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
    (∀ (I : Type w) (U : I → X.Opens), (⨆ i : I, U i) = ⊤ →
      (∀ i : I, IsClassical
        ((sheafCompose (Scheme.ProEt.topology (U i).toScheme)
          (forget (ModuleCat.{u + 1} Λ))).obj
            ((openImmersionRestriction (ModuleCat.{u + 1} Λ) (U i).ι).obj F))) →
      IsClassical
        ((sheafCompose (Scheme.ProEt.topology X) (forget (ModuleCat.{u + 1} Λ))).obj F)) ∧
    (IsClassical
        ((sheafCompose (Scheme.ProEt.topology X) (forget (ModuleCat.{u + 1} Λ))).obj F) →
      ∀ U : X.Opens, IsClassical
        ((sheafCompose (Scheme.ProEt.topology U.toScheme)
          (forget (ModuleCat.{u + 1} Λ))).obj
            ((openImmersionRestriction (ModuleCat.{u + 1} Λ) U.ι).obj F))) := by
  constructor
  · intro I U hU hF
    classical
    let J := Set.range U
    let V : ULift.{u + 1} J → X.ProEt := fun j ↦ Scheme.ProEt.mk j.down.val.ι
    let G := (sheafCompose (Scheme.ProEt.topology X)
      (forget (ModuleCat.{u + 1} Λ))).obj F
    apply (Scheme.proEtaleClassicalSheavesImage X G).1.mp
    apply (Scheme.proEtale_locallyClassical_etaleCover X G).1
    refine ⟨ULift.{u + 1} J, V, ?_, ?_⟩
    · intro T
      let O (j : J) := T.hom ⁻¹ᵁ j.val
      apply Scheme.ProEt.mem_topology_of_openImmersion _ (fun j : J ↦ (O j).ι)
      · intro x
        have hx : T.hom x ∈ (⨆ i, U i) := by rw [hU]; trivial
        obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
        exact ⟨⟨U i, ⟨i, rfl⟩⟩, ⟨⟨x, hi⟩, rfl⟩⟩
      · intro j
        refine ⟨⟨j⟩, ⟨?_⟩⟩
        exact MorphismProperty.Over.homMk (T.hom.resLE j.val (O j) le_rfl)
          (T.hom.resLE_comp_ι le_rfl)
    · intro j
      rcases j with ⟨⟨_, i, rfl⟩⟩
      exact (Scheme.proEtaleClassicalSheavesImage _ _).1.mpr (hF i)
  · intro hF U
    exact setClassical_restrict X U _ hF

end AlgebraicGeometry.ProEtale
