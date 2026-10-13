/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # A Noetherian comparison before choosing a finite-free resolution

Source: Stacks Project, Tag 0A1H, Noetherian approximation paragraph, and Tag 081F.
(blueprint: lem-pc-proper-flat-single-open-noetherian-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe u wX wS
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Local approximation and transport data, without any finite-free resolution of the image.
Source: Stacks Project, Tag 0A1H, approximation paragraph; Tags 081F, 08E5 and 08E7.

Proof: Choose an affine neighbourhood V of x in U. Its ring is the filtered colimit of
its finitely generated Z-subalgebras. Restrict f and F to this neighbourhood. Apply
Noetherian approximation to the tensor data O_X and F[0], enlarging the stage to descend
relative flatness, properness of the morphism and proper term supports. Take T to be
that stage's affine spectrum and W its total open; replacing the stage by W.toScheme
only changes the data by the
canonical total-open isomorphism. Use standard localizations in universe u+1 at all
auxiliary stages. Denote the source by Y, its map by p, and the descended tensor by A.
The descended source is Noetherian: its morphism is finitely presented over a Noetherian
base. Its finitely presented terms are coherent. The perfect-tensor bounded-coherent
lemma gives the boundedness and coherence hypotheses on A. This supplies the
two source cohomology hypotheses below; it does not assert coherence or pseudo-coherence of Rp_*A.

Let g be the comparison from V to W and let L be tensor pullback along g followed by
W.ι, transported to the localized site of V. Tensor pullback is a left adjoint, hence
additive; it preserves finite free modules with their ranks, as does the localized-site
equivalence. For any bounded-above finite-free P representing Rp_*A after restriction
to W, P is K-flat. Termwise tensor pullback therefore computes derived pullback.
Relatively flat derived base change identifies this pullback with the original single
image on V. Compose with open base change and the exact localized-site equivalence.
To compare independent localizations, use their localization universal properties on
Q and compute both direct images by the same K-injective resolution. This proves the
comparison for every such P, without choosing P here. Empty U has no x; F=0 descends
to zero A, and the same comparison applies. No arbitrary existence witness defines
an object: all data below are used only in a theorem proof.
(blueprint: lem-pc-proper-flat-single-open-noetherian-comparison). -/
theorem properFlat_single_open_noetherian_comparison
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f]
    [HasDerivedCategory.{wX}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wS}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (F : X.Modules) [F.IsFinitePresentation] (hF : F.IsFlatOver f) (U : S.Opens)
    [HasDerivedCategory.{wS}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens, HasDerivedCategory.{wS}
      (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    (x : U.toScheme) :
    ∃ V : U.toScheme.Opens, x ∈ V ∧
      ∃ (T Y : Scheme.{u}) (W : T.Opens),
        IsAffine T ∧ IsCompact (W : Set T) ∧ IsNoetherian W.toScheme ∧
        ∃ (dT : HasDerivedCategory.{u + 1}
            (SheafOfModules.{u} (moduleRings T.toRingedSpace)))
          (dW : HasDerivedCategory.{u + 1}
            (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)))
          (dY : HasDerivedCategory.{u + 1}
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
          (dO : ∀ B : W.toScheme.Opens, HasDerivedCategory.{u + 1}
            (SheafOfModules.{u} ((moduleRings W.toScheme.toRingedSpace).over B))),
          letI := dT
          letI := dW
          letI := dY
          letI := dO
          ∃ p : Y ⟶ W.toScheme,
            IsProper p ∧ ∃ A : schemeDerivedCategory Y,
            (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
              IsZero ((DerivedCategory.homologyFunctor
                (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).obj A)) ∧
            (∀ i : ℤ, RingedSpace.IsCoherent Y.toRingedSpace
              ((DerivedCategory.homologyFunctor
                (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).obj A)) ∧
            ∃ (g : V.toScheme ⟶ W.toScheme)
              (L : T.Modules ⥤ SheafOfModules.{u}
                ((moduleRings U.toScheme.toRingedSpace).over V)),
              Nonempty (L ≅ Scheme.Modules.tensorPullback (g ≫ W.ι) ⋙
                (Scheme.Modules.overEquiv V).inverse) ∧
              ∃ hL : L.Additive,
                letI := hL
                (∀ P : CochainComplex T.Modules ℤ,
                  (∃ N : ℤ, ∀ i : ℤ, N < i → IsZero (P.X i)) →
                  (∀ i : ℤ, ∃ r : ℕ, Nonempty (P.X i ≅ SheafOfModules.free
                    (R := moduleRings T.toRingedSpace) (ULift.{u} (Fin r)))) →
                  Nonempty ((schemeOpenRestriction T W).mapDerivedCategory.obj
                    (DerivedCategory.Q.obj P) ≅ (schemeDerivedDirectImage p).obj A) →
                  Nonempty ((SheafOfModules.overFunctor.{u}
                    (moduleRings U.toScheme.toRingedSpace) V).mapDerivedCategory.obj
                    ((schemeOpenRestriction S U).mapDerivedCategory.obj
                      ((schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
                        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F))) ≅
                    DerivedCategory.Q.obj
                      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) := by sorry

end AlgebraicGeometry
