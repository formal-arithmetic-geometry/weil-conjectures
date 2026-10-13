/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.IdealModuleProductStalk
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

/-! # Ambient ideal-power extension for a closed structure module

Source: Stacks Project, Tags 01YB, 01XZ and 01QY.
(blueprint: lem-pc-closed-structure-ambient-ideal-extension)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- Extend a local map from a closed structure module using an ambient ideal power.
Source: Stacks Project, Tag 01YB (lemma-homs-over-open), with Tags 01QY and 01XZ.
(blueprint: lem-pc-closed-structure-ambient-ideal-extension)

Proof: Write H = i_* O_W. A closed immersion is quasi-compact and separated, so H
is quasi-coherent by the quasi-coherent pushforward theorem. On an affine open
Spec A of X its sections are A/K, with the scalar action through the quotient;
these sections are cyclic over A. The affine finite-type criterion makes H finite
type, and the locally Noetherian coherence criterion makes H coherent. The same
criterion makes G quasi-coherent. Apply Tag 01YB with coherent source H and
quasi-coherent target G. Its open complement of the ideal support equals U by hI.
Its surjectivity clause produces n and a map from I^n H agreeing with phi after
the product inclusion on all of U. The recursively formed ideal power and the
ideal-sheaf-data power have the same affine section ideals I(V)^n. Their monic
inclusions therefore identify them as subobjects of O_X, and the induced image
isomorphism identifies their products with H, preserving inclusions. Transport
through this isomorphism. Finally overFunctor followed by overEquiv is naturally
isomorphic to restrictFunctor; conjugation by this natural isomorphism gives the
stated equality. No generic point or integrality is used. At n = 0 the ideal is
the unit ideal; for U empty every local map is the unique map and n = 0 works. -/
theorem closed_structure_ambient_ideal_extension
    {X W : Scheme.{u}} [IsNoetherian X]
    (i : W ⟶ X) [IsClosedImmersion i]
    (I : X.IdealSheafData) (G : X.Modules)
    (hG : RingedSpace.IsCoherent X.toRingedSpace G)
    (U : X.Opens) (hI : (I.support : Set X) = (U : Set X)ᶜ)
    (φ : (restrictFunctor U.ι).obj
        ((pushforward i).obj (SheafOfModules.unit W.ringCatSheaf)) ⟶
      (restrictFunctor U.ι).obj G) :
    ∃ (n : ℕ) (χ : idealModuleProduct (I ^ n).toModulesι
        ((pushforward i).obj (SheafOfModules.unit W.ringCatSheaf)) ⟶ G),
      (restrictFunctor U.ι).map χ =
        (restrictFunctor U.ι).map (idealModuleProductι (I ^ n).toModulesι
          ((pushforward i).obj (SheafOfModules.unit W.ringCatSheaf))) ≫ φ := by sorry

end AlgebraicGeometry.Scheme.Modules
