/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.RingTheory.RingPseudoCoherent
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections

/-! # Bounded flat complexes computing proper cohomology -/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- A bounded nonnegative quasi-coherent flat complex computing all base changes.
Source: Stacks Project, Tags 0A1H and 0B91; coherence unit, part (a).
Proof: Choose an affine neighbourhood of t. Its proper inverse image has a finite affine
cover. Separatedness makes nonempty finite intersections affine. Form the alternating
complex of sections of F over these intersections and associate sheaves on the affine
base. It is bounded in [0,d], quasi-coherent, and flat over the base by relative flatness
and the affine local criterion for flatness. After affine base change its terms tensor
with the new base ring and still form the alternating section complex of the pulled-back
cover. Affine quasi-coherent acyclicity and Čech comparison compute higher direct images.
These identifications glue on affine opens of arbitrary new bases. Transport through the
unique isomorphism to a standard fibre product gives the assertion for every cartesian
square. Noetherian approximation of (f,F), proper coherence at the Noetherian stage,
and derived base change show that the ring complex of sections is pseudo-coherent.
Empty inverse images give the zero complex; no lower bound on fibre dimension is
needed.
(blueprint: lem-pc-proper-flat-cohomology-model). -/
theorem exists_proper_flat_cohomology_model {X T : Scheme.{u}} (f : X ⟶ T) (F : X.Modules)
    [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f]
    [HasInjectiveResolutions X.Modules] [F.IsFinitePresentation]
    (hF : F.IsFlatOver f) (t : T) :
    ∃ (U : T.Opens) (C : CochainComplex U.toScheme.Modules ℤ) (d : ℕ),
      t ∈ U ∧ IsAffine U.toScheme ∧ C.IsStrictlyGE 0 ∧ C.IsStrictlyLE d ∧
      (∀ n : ℤ, (C.X n).IsFlatOver (𝟙 U.toScheme)) ∧
      (∀ n : ℤ, (C.X n).IsQuasicoherent) ∧
      (letI : CommRing (U.toScheme.ringCatSheaf.obj.obj (.op ⊤)) :=
        inferInstanceAs (CommRing Γ(U.toScheme, ⊤));
        letI := HasDerivedCategory.standard
          (ModuleCat.{u} (U.toScheme.ringCatSheaf.obj.obj (.op ⊤)));
        DerivedCategory.IsPseudoCoherent (DerivedCategory.Q.obj
          (((SheafOfModules.evaluation.{u} U.toScheme.ringCatSheaf (.op ⊤)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj C))) ∧
      ∀ {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
        [HasInjectiveResolutions X'.Modules], IsPullback g' f' f (g ≫ U.ι) → ∀ q : ℕ,
        Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj C).homology q ≅
          (higherDirectImage f' q).obj ((Modules.pullback g').obj F)) := by sorry

end AlgebraicGeometry.Scheme.Modules
