/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Sheaf.RingTheory.RingPseudoCoherent
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import Sheaf.AlgebraicGeometry.ProperFlatFinitePresentationModel
import Sheaf.AlgebraicGeometry.AffineFinitePresentationFlatShortening

/-! # Pseudo-coherent replacement of universal proper cohomology models -/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

set_option linter.unusedVariables false in
/-- Replace a bounded flat universal cohomology model by a pseudo-coherent one,
preserving the cohomology of every ordinary pullback. No chain map from C is assumed.
Source: Stacks Project, Tags 0A1H, 0B91(2), and 068V (Tor-amplitude representatives).
(blueprint: lem-pc-proper-flat-cohomology-model-properties).
Proof: restrict f and F to the affine U. Write its ring as a filtered colimit of
Noetherian rings. Descend the finitely presented proper morphism and the finitely
presented module, enlarging the stage so that relative flatness holds. At that stage,
proper coherence and a bounded affine Cech complex give a perfect derived direct image.
Derived base change gives a perfect object K over U computing every new base. Its
Tor-amplitude is contained in [0,d]: for every base algebra the supplied comparison
identifies its homology with the ordinary pullback of the flat complex C, which is zero
outside that interval. The amplitude criterion provides a finite projective ring
complex in [0,d] representing K. Associate sheaves to get D; its terms are flat and
quasi-coherent, and its ring complex is pseudo-coherent (finite projectives are summands
of finite free modules and admit bounded-above finite free resolutions). For each g,
identify the cohomology of g*D with the base-changed higher direct images using derived
base change, and compose with the inverse of the supplied comparison for g*C. For a
nonaffine base these are sheaf isomorphisms because both derived base change and the
cohomology comparison are global. The arbitrary-square clause in hcomp permits using
the standard fibre product and its injective resolutions. If U is empty or the inverse
image is empty, the zero complex suffices. -/
theorem proper_flat_cohomology_model_properties {X T : Scheme.{u}} (f : X ⟶ T) (F : X.Modules)
    [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f]
    [HasInjectiveResolutions X.Modules] [F.IsFinitePresentation]
    (hF : F.IsFlatOver f) (t : T) (U : T.Opens)
    (C : CochainComplex U.toScheme.Modules ℤ) (d : ℕ)
    (ht : t ∈ U) (hU : IsAffine U.toScheme) (hCge : C.IsStrictlyGE 0)
    (hCle : C.IsStrictlyLE d)
    (hCflat : ∀ n : ℤ, (C.X n).IsFlatOver (𝟙 U.toScheme))
    (hCqc : ∀ n : ℤ, (C.X n).IsQuasicoherent)
    (hcomp :
      ∀ {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
        [HasInjectiveResolutions X'.Modules], IsPullback g' f' f (g ≫ U.ι) → ∀ q : ℕ,
        Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj C).homology q ≅
          (higherDirectImage f' q).obj ((Modules.pullback g').obj F))) :
    ∃ D : CochainComplex U.toScheme.Modules ℤ,
      D.IsStrictlyGE 0 ∧ D.IsStrictlyLE d ∧
      (∀ n : ℤ, (D.X n).IsFlatOver (𝟙 U.toScheme)) ∧
      (∀ n : ℤ, (D.X n).IsQuasicoherent) ∧
      (letI : CommRing (U.toScheme.ringCatSheaf.obj.obj (.op ⊤)) :=
        inferInstanceAs (CommRing Γ(U.toScheme, ⊤));
        letI := HasDerivedCategory.standard
          (ModuleCat.{u} (U.toScheme.ringCatSheaf.obj.obj (.op ⊤)));
        DerivedCategory.IsPseudoCoherent (DerivedCategory.Q.obj
          (((SheafOfModules.evaluation.{u} U.toScheme.ringCatSheaf (.op ⊤)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj D))) ∧
      ∀ {T' : Scheme.{u}} (g : T' ⟶ U.toScheme) (q : ℕ),
        Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj D).homology q ≅
          (((Modules.pullback g).mapHomologicalComplex _).obj C).homology q) := by
  -- Only the universal comparison and upper bound of C are needed below.
  obtain ⟨B, b, hBge, hBle, hBflat, hBqc, hBfp, hBcomp⟩ :=
    exists_proper_flat_finitePresentation_model f F hF U hU
  have hBC {T' : Scheme.{u}} (g : T' ⟶ U.toScheme) (q : ℕ) :
      Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj B).homology q ≅
        (((Modules.pullback g).mapHomologicalComplex _).obj C).homology q) := by
    have := isGrothendieckAbelian (Limits.pullback f (g ≫ U.ι))
    obtain ⟨eB⟩ := hBcomp g (pullback.fst f (g ≫ U.ι))
      (pullback.snd f (g ≫ U.ι)) (IsPullback.of_hasPullback f (g ≫ U.ι)) q
    obtain ⟨eC⟩ := hcomp g (pullback.fst f (g ≫ U.ι))
      (pullback.snd f (g ≫ U.ι)) (IsPullback.of_hasPullback f (g ≫ U.ι)) q
    exact ⟨eB ≪≫ eC.symm⟩
  have hvan (s : U.toScheme) (q : ℕ) (hq : d < q) :
      IsZero ((((Modules.pullback (U.toScheme.fromSpecResidueField s)).mapHomologicalComplex
        _).obj B).homology q) := by
    obtain ⟨e⟩ := hBC (U.toScheme.fromSpecResidueField s) q
    have := hCle
    have hz : IsZero (C.X (q : ℤ)) := C.isZero_of_isStrictlyLE d q (by omega)
    exact e.isZero_iff.mpr (ShortComplex.isZero_homology_of_isZero_X₂ _
      ((Modules.pullback (U.toScheme.fromSpecResidueField s)).map_isZero hz))
  obtain ⟨D, hDge, hDle, hDflat, hDqc, hDpc, hDB⟩ :=
    exists_affine_finitePresentation_flat_shortening U.toScheme hU B b d
      hBge hBle hBflat hBqc hBfp hvan
  refine ⟨D, hDge, hDle, hDflat, hDqc, hDpc, ?_⟩
  intro T' g q
  obtain ⟨eDB⟩ := hDB g q
  obtain ⟨eBC⟩ := hBC g q
  exact ⟨eDB ≪≫ eBC⟩

end AlgebraicGeometry.Scheme.Modules
