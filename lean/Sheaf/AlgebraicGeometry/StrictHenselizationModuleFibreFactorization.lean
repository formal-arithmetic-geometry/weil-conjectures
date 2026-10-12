/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Sheaf.AlgebraicGeometry.GeometricFibreExchangeGerms
public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.SixFunctors.BaseChange.GlobalSections
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization
import Sheaf.AlgebraicGeometry.EtaleModuleSetPullbackComparison
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiber

/-! # Factoring fibre restrictions through strict henselization sections

Source: Stacks Project, Tags 03Q9, 03Q1 and 04HX.
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Etale
open Scheme

/-- The module stalk comparison with strict henselization sections, together with
its compatibility with restriction to the given geometric fibre. This assertion
uses no integral or proper hypothesis.

Source: Stacks Project, Tags 03Q9, 03Q1 and 04HX.
(blueprint: lem-sbc-strict-henselization-module-fibre-factorization).

Proof: The marked maps from Spec Omega to all affine pointed neighbourhoods form
a cone. Its unique lift t to their limit is compatible with the structural map.
The closed-fibre theorem for the strict henselization applies to t's image:
its composite with the structural map has image s's point, so that image is the
closed point of the strict henselization.
Pull back X to this limit. Tag 03Q9 identifies its sections with the direct-image
stalk. Apply the module-to-set inverse-image comparison and its unit equation to
the set-valued stalk formula. Since the set comparison and all restriction maps
commute with addition and scalar multiplication, the bijective comparison is a
module isomorphism Theta. Affine pointed neighbourhoods are cofinal, so its
formula extends to every V and v. The pullback lift i has composite g' with the
projection to X. The inverse-image composition isomorphism therefore identifies
i^* q^* F with g'^* F. Global sections followed by the canonical isomorphism to
evaluation at the identity object gives b. Naturality of the units and their
composition equation show that b after restriction along i after Theta takes a
representative z to the unit image restricted along geometricFibreSectionLift:
both lifts have projections f' followed by v and g', so pullback uniqueness makes
them equal. This is the displayed formula, without any injectivity assertion
about restriction along i. All constructions also apply to an empty X. -/
theorem strictHenselizationModuleFibre_factorization
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : IsPullback g' f' f s)
    [QuasiCompact f] [QuasiSeparated f]
    [IsLocalRing (strictHenselizationRing s)]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ∃ (t : Spec (.of Ω) ⟶ strictHenselizationScheme s)
      (ht : t ≫ strictHenselizationStructuralMap s = s),
      t (IsLocalRing.closedPoint Ω) =
        IsLocalRing.closedPoint (strictHenselizationRing s) ∧
      ∃ (i : X' ⟶ pullback f (strictHenselizationStructuralMap s)),
        IsPullback i f' (pullback.snd f (strictHenselizationStructuralMap s)) t ∧
        i ≫ pullback.fst f (strictHenselizationStructuralMap s) = g' ∧
      ∃ Θ : (pointSmallEtale s).sheafFiber.obj ((f)_*[ModuleCat.{u + 1} Λ].obj F) ≅
          (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).obj
            ((pullback.fst f (strictHenselizationStructuralMap s))^*[ModuleCat.{u + 1} Λ].obj F),
      ∃ b : (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).obj
          ((i)^*[ModuleCat.{u + 1} Λ].obj
            ((pullback.fst f (strictHenselizationStructuralMap s))^*[ModuleCat.{u + 1} Λ].obj F)) ≅
          ((g')^*[ModuleCat.{u + 1} Λ].obj F).obj.obj (op (Scheme.Etale.mk (𝟙 X'))),
      ∀ (V : Y.Etale) (v : (pointSmallEtale s).fiber.obj V)
        (z : F.obj.obj (op (f.Etale.obj V))),
        b.hom.hom ((globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) i
          ((pullback.fst f (strictHenselizationStructuralMap s))^*[ModuleCat.{u + 1} Λ].obj F)).hom
          (Θ.hom.hom ((pointSmallEtale s).toPresheafFiber V v
            ((f)_*[ModuleCat.{u + 1} Λ].obj F).obj z))) =
        (geometricFibreSectionRestriction Λ sq.toCommSq F V v).hom z := by
  sorry

end AlgebraicGeometry.Etale
