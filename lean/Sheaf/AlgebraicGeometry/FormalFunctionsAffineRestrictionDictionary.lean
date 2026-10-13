/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Sheaf.Topology.RingedSpaceModuleCohomology
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-! # The affine restriction dictionary for formal functions

Source: Stacks Project, Theorem 02OC and Lemma 088B, affine reduction.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The affine chart identifies the original sections and quotient system with the
sections and quotient system of the restricted proper morphism to a spectrum.
This is a finite-level dictionary; it asserts no completion or limit isomorphism.
Source: Stacks Project, Theorem 02OC and Lemma 088B; Schemes, Tags 01I8 and 01IC.
(blueprint: lem-weil-pbc-formal-functions-affine-restriction-dictionary)

Proof: Let V = f^(-1)U and g = (f restricted to U) followed by U = Spec Gamma(Y,U).
The restriction square is cartesian, so properness of f gives properness of g.
Restriction to V preserves coherence of F. The affine ideal correspondence identifies
J restricted to U with the ideal sheaf associated with J(U). Functoriality of comap,
and the restriction square, then give the displayed equality of ideals on V.
Pushforward sections over U are F sections over V. Global sections of F restricted to
V are the same sections via the restriction top isomorphism. The affine chart formula
for g.appTop identifies their scalar action with the original Gamma(Y,U)-action;
this gives a. Restriction preserves ideal products and powers and preserves cokernels.
The cokernel comparisons give the level maps b_n from the restricted quotient sections
to the original quotient sections. Their composites with quotient projections are the
restriction of those original projections, so these maps give the displayed equation.
Cancel the quotient epimorphisms to check every transition square, giving b as a natural
isomorphism. These steps use only restriction and finite-level quotients; they do not
use the theorem on formal functions. Empty U, F=0, and zero or unit J satisfy the same
restriction and cokernel universal properties.
-/
theorem formalFunctions_affine_restriction_dictionary
    {X Y : Scheme.{u}} [IsNoetherian Y]
    (J : Y.IdealSheafData) (f : X ⟶ Y) [IsProper f] (F : CoherentModules X)
    (U : Y.Opens) (hU : IsAffineOpen U) :
    let R := Γ(Y, U)
    let I := J.ideal ⟨U, hU⟩
    let V := f ⁻¹ᵁ U
    let Z := V.toScheme
    let g := (f ∣_ U) ≫ hU.isoSpec.hom
    let K := (J.comap f).comap V.ι
    let P := (Scheme.Modules.restrictFunctor V.ι).obj F.obj
    let G := RingedSpace.globalSectionsFunctor Z.toRingedSpace ⋙
      ModuleCat.restrictScalars ((Scheme.ΓSpecIso R).inv ≫ g.appTop).hom
    let H := (Scheme.Modules.pushforward f).obj F.obj
    let T := formalCompletionSystem (J.comap f) F.obj ⋙ Scheme.Modules.pushforward f
    let E := SheafOfModules.evaluation Y.ringCatSheaf (op U)
    IsProper g ∧ RingedSpace.IsCoherent Z.toRingedSpace P ∧
      K = (Scheme.IdealSheafData.ofIdealTop
        (I.map (Scheme.ΓSpecIso R).inv.hom)).comap g ∧
      ∃ a : E.obj H ≅ G.obj P,
        ∃ b : formalCompletionSystem K P ⋙ G ≅ T ⋙ E,
          ∀ n : ℕ, a.hom ≫ G.map (formalModuleQuotientπ K (n + 1) P) ≫
            b.hom.app (op n) = E.map ((Scheme.Modules.pushforward f).map
              (formalModuleQuotientπ (J.comap f) (n + 1) F.obj)) := by sorry

end AlgebraicGeometry
