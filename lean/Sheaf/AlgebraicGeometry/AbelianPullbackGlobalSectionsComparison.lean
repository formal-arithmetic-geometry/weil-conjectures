/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import Sheaf.AlgebraicGeometry.EtaleSetSectionComparison
import Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Coefficient comparison for global sections of inverse images
Source: Stacks Project, Tags 00YV, 03CB and 03CC.
(blueprint: lem-weil-pbc-abelian-pullback-global-sections-comparison). -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- Global sections of an abelian inverse image identify with sections of the set
inverse image on the base-changed terminal object, compatibly with composition.
There is no inverse system or finite-stage lifting assertion here.

Source: Stacks Project, Sites, Tags 00YV, 03CB and 03CC.
(blueprint: lem-weil-pbc-abelian-pullback-global-sections-comparison).

Proof: For each f, use etaleInverseImageAlgebraicStructures to obtain a natural
coefficient isomorphism C_f from the underlying abelian inverse image to the set
inverse image. Its direct-image comparison is the identity on sections and its
unit equation is R_f(C_f) composed with the forgotten abelian unit = the set unit.
Thus these choices are determined by the adjunction hom-set bijection, rather
than by an arbitrary isomorphism. Write T_f for the base change of the terminal
object and t_f : T_f ≅ terminal for PreservesTerminal.iso. Define e_f by the
Gamma-to-terminal-section isomorphism, then restriction along t_f.hom, then
C_f evaluated at T_f. All three maps are invertible, giving a bijection.

For h followed by f, apply the unit equation for C_h to the abelian inverse image
of F and that for C_f to F. Naturality of C_h transports the latter equation
through h inverse image. The resulting composite intertwines the composite
abelian unit with the composite set unit. The abelian composition isomorphism
is the mate of the direct-image composition comparison. The uniqueness clause
of etaleSetInverseImageCompositionUnits identifies its forgotten, conjugated
inverse with the chosen set composition map: both satisfy this same unit equation.
Evaluate this equality at the iterated base change of the terminal object.
Naturality in site objects moves C across the fibre-product pasting isomorphism;
uniqueness of terminal maps identifies the terminal-preservation maps on both
sides. Expanding globalSectionsUpperStarMap cancels the Gamma/terminal-section
isomorphisms. The remaining three factors are precisely the set unit, the set
composition map, and restriction along pullbackComp.hom, which define
etaleSetSectionComparison. Transport along hk gives the displayed equation.
For identities the same unit equations apply. On empty schemes or for the zero
sheaf both sets are singletons. No compactness, affineness, torsion, finiteness,
inverse system or finite-stage descent is used. -/
theorem exists_abelianPullbackGlobalSectionsComparison
    (X : Scheme.{u}) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ∃ e : ∀ (Y : Scheme.{u}) (f : Y ⟶ X),
      ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        ((upperStar AddCommGrpCat.{u + 1} f).obj F)) ≃
      (((Scheme.etaleSetPullback f).obj
        ((sheafForget X.smallEtaleTopology).obj F)).obj.obj
          (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj (⊤_ X.Etale)))),
      ∀ (Y Z : Scheme.{u}) (h : Z ⟶ Y) (f : Y ⟶ X) (k : Z ⟶ X)
        (hk : h ≫ f = k)
        (s : (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          ((upperStar AddCommGrpCat.{u + 1} f).obj F)),
        e Z k ((Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{u + 1}).map
          ((upperStarComp AddCommGrpCat.{u + 1} h f k hk.symm).inv.app F)
          (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} h
            ((upperStar AddCommGrpCat.{u + 1} f).obj F) s)) =
        etaleSetSectionComparison h f k hk
          ((sheafForget X.smallEtaleTopology).obj F) (⊤_ X.Etale) (e Y f s) := by sorry

end AlgebraicGeometry.Etale
