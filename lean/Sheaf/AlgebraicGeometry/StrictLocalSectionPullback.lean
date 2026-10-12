/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Sheaf.AlgebraicGeometry.QcqsStrictLocalModuleComparison
public import Sheaf.AlgebraicGeometry.GeometricFibreExchangeGerms
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections

/-! # Pullback of strict-local representative sections

Source: Stacks Project, Tags 03Q9 and 0A3U.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- Pulling a strict-local representative section back to the pointed fibre is the
unit restriction along that representative's marked point.
Source: Stacks Project, Tag 03Q9, canonical restriction on representatives, and
Tag 0A3U, degree-zero compatibility in the parent factorization.
(blueprint: lem-weil-pbc-strict-local-section-pullback).

Proof: expand `qcqsStrictLocalSectionRestriction` and the global-sections pullback.
Naturality of terminal evaluation changes the latter into the unit for q followed
by restriction along its terminal lift. Naturality of the unit moves the strict-local
limit-leg restriction past this unit. The composition-unit identity and the inverse
of `upperStarComp` identify the two successive inverse-image units with the unit for
g'. The remaining morphism from the terminal object to g'^*f^*V has outer second
projection identity. Its inner projections are g', by hq, and f' followed by the
marked point: use hqt to replace the map to the strict-local base by f't, then use
hpoint to replace t followed by the limit leg by the marked point. Pullback hom-ext
therefore identifies this morphism with `geometricFibreSectionLift`. The terminal
section/global-section isomorphisms cancel, leaving exactly the stated identity.
No isomorphism of stalks, comparison map a, qcqs hypothesis, or exchange map occurs.
The argument is valid for empty schemes and zero coefficient modules as well. -/
theorem strictLocal_section_pullback
    (Λ : Type (u + 1)) [CommRing Λ] {X' X Y : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : CommSq g' f' f s)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (t : Spec (.of Ω) ⟶ Scheme.strictHenselizationScheme s)
    (hpoint : ∀ j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s),
      t ≫ (Scheme.strictHenselizationCone s).π.app (op (op j)) ≫
        (Spec (unop ((equivSmallModel.{u}
          (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1.left)).isoSpec.inv =
        ((equivSmallModel.{u}
          (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).2.left)
    (q : X' ⟶ pullback f (Scheme.strictHenselizationStructuralMap s))
    (hqt : q ≫ pullback.snd f (Scheme.strictHenselizationStructuralMap s) = f' ≫ t)
    (hq : q ≫ pullback.fst f (Scheme.strictHenselizationStructuralMap s) = g')
    (j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)) :
    qcqsStrictLocalSectionRestriction Λ f s F j ≫
      globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) q
        ((upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).obj F) ≫
      (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map
        ((upperStarComp (ModuleCat.{u + 1} Λ) q
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) g' hq.symm).inv.app F) =
      geometricFibreSectionRestriction Λ sq F
        ((Scheme.AffineEtale.Spec Y).obj
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1)
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).2 ≫
      (Sheaf.ΓNatIsoSheafSections _ _
        (IsTerminal.isTerminalOfObj
          (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ X')
          (Scheme.Etale.mk (𝟙 X')) Over.mkIdTerminal)).inv.app
            ((upperStar (ModuleCat.{u + 1} Λ) g').obj F) := by sorry

end AlgebraicGeometry.Etale
