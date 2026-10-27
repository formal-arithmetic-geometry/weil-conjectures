/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Sheaf.Paper.RefinementComparisonIsomorphism
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness

/-! # Refinement comparison at a retained fixed-scalar witness

Source: blueprint latest, sec-smooth-purity/sk-def-sf-operations,
def-sf-refinement-comparison-isomorphism, part (a)
(blueprint: def-sf-refinement-comparison-isomorphism).

The original refinement constructions are reexported. This interface evaluates the
same specified formula directly at a fixed-scalar witness, without transporting
its underlying object through a second coefficient presentation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.ProEtale

/-- The actual witness transport in part (a) of the refinement comparison, in the
fixed-scalar coordinates of FixedEtaleOriginWitness. No antecedent is chosen.
Source: def-sf-refinement-comparison-isomorphism, part (a), displayed formula
(blueprint: def-sf-refinement-comparison-isomorphism). -/
def refinementProperOpenIsoFixed (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c₁ c₂ : Compactification f}
    (v : c₁.Refinement c₂)
    (M : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (w : X.FixedEtaleOriginWitness Λ M) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c₂.i).mapDerivedCategory.obj M.obj ≅
      (lowerStar (ModuleCat.{u + 1} Λ) v.hom).rightDerivedFunctor.obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c₁.i).mapDerivedCategory.obj
          M.obj) :=
  (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c₂.i).mapDerivedCategory.mapIso w.iso.symm ≪≫
    properOpenProEtaleIso Λ v.hom c₁.i c₂.i v.i_hom w.complex ≪≫
    (lowerStar (ModuleCat.{u + 1} Λ) v.hom).rightDerivedFunctor.mapIso
      ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c₁.i).mapDerivedCategory.mapIso
        w.iso)

end AlgebraicGeometry.ProEtale
