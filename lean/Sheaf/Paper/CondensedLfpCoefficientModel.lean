/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
import Sheaf.AlgebraicGeometry.ProetaleQcqsFpSectionCalculus
import Sheaf.CategoryTheory.SiteModuleSheafGluing
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing
import Sheaf.Paper.ProfinitePointPullback
import Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse

/-!
# Finite coefficient models on one stratum

Source: upstream ModuleObject/Colimit/TwoColimit.lean, (Obj) descent paragraph;
finite-presentation descent, steps 1--3 of the parent descent node.
(blueprint: lem-weil-pbc-condensed-lfp-coefficient-model).
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- A locally finitely presented module on an immersed stratum has a locally finitely
presented model over a finite coefficient field, with the coefficients kept in their
actual inverse-image presentation.

Source: upstream ModuleObject/Colimit/TwoColimit.lean, (Obj) descent paragraph;
steps 1--3 of lem-weil-pbc-condensed-finite-presentation-descent.
(blueprint: lem-weil-pbc-condensed-lfp-coefficient-model).

Proof: the immersion identifies X with a subspace of the noetherian space T, so X is
noetherian and qcqs. The point-pullback comparisons identify the displayed coefficient
rings with the usual condensed rings on X and identify the displayed coefficient map
with their inclusion. Refine a presentation cover to finitely many affine pro-etale
objects. Their pairwise and triple overlaps are qcqs. The coefficient-colimit and qcqs
section calculus lift the finitely many presentation-matrix entries to one finite field.
Take their cokernels over that field. Scalar extension preserves these cokernels.
The Hom clause of the same calculus and tensor adjunction descend the transition
isomorphisms and their inverses on the overlaps. Eventual equality, at a common larger
field, enforces both inverse identities, the diagonal identity, and the cocycle identity.
Ringed-site module gluing now constructs a module on X. Weakly-etale localization and
the pullback-tensor comparison identify its scalar extension locally with M. Sheaf-Hom
gluing gives the global isomorphism. The descended presentation cover proves local finite
presentation of the model. Empty X uses the empty cover and the zero model; zero ranks
use empty matrices. Transport back along the coefficient comparisons gives exactly the
rings, map, and isomorphism below. -/
theorem exists_lfp_finiteCoefficient_model_on_immersion
    (T X : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (f : X ⟶ T) [IsImmersion f] (ℓ : ℕ) [Fact ℓ.Prime]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ)))
    (hM : IsLocallyFinitelyPresented
      ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ)) M) :
    ∃ (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
      (M_E : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))),
      IsLocallyFinitelyPresented
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E)) M_E ∧
      Nonempty ((Mod.extendScalars
        ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E))).obj M_E ≅ M) := by
  sorry

end AlgebraicGeometry.ProEtale
