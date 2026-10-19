/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.Paper.FiniteRingSectionDeformation
public import Sheaf.Paper.NoetherianEtaleSectionSpecialization
public import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
public import Sheaf.AlgebraicGeometry.VectorBundleZeroSection
public import Sheaf.AlgebraicGeometry.ConormalGradedAlgebra
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import Sheaf.AlgebraicGeometry.CompactifiableOverField
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.AffineSpace
import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
import Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization
import Sheaf.AlgebraicGeometry.SmoothExceptionalBaseChange
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Compactification.NagataCompactification
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Flat.Basic
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Etale coordinates and the normalized section deformation comparison

Source: blueprint main-20261015, sec-smooth-purity/sk-thm-dnc/sk-thm-dnc.proof.md,
Local construction and normalization at one
(blueprint: lem-per-etale-section-deformation-comparison).

The normal chart is the zero fibre of the fixed Rees map, with coordinates x_i/t.
The locality maps are the published counit-preserving comparisons. No Tate datum occurs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.EtaleSectionDeformationComparison
open NoetherianSectionSpecialization
open FiniteRingSectionDeformation

/-- The zero-fibre coordinates of the standard Rees deformation, followed by the affine
space base map. Thus x_i/t modulo t is the degree-one coordinate, with no linear change.
Source: sk-thm-dnc, Local construction, x_i=t*u_i
(blueprint: lem-per-etale-section-deformation-comparison). -/
def originNormalChart (S : Scheme.{u}) (d : ℕ) :
    (AffineSpace.zeroSection (ULift.{u} (Fin d)) S).ker.normalCone ⟶
      AffineSpace (ULift.{u} (Fin d)) S :=
  (AffineSpace.zeroSection (ULift.{u} (Fin d)) S).ker.normalConeToDeformationSpace ≫
    Scheme.Hom.deformationSpaceToAffineSpace (ULift.{u} (Fin d)) S ≫
      AffineSpace.map (ULift.{u} (Fin d)) (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)

/-- The frame map on the actual Rees cone: first invert the normal map of the open
neighbourhood, then apply the normal map of the etale coordinates and the standard
zero-fibre coordinates. Every factor is fixed by its ring map on representatives.
Source: sk-thm-dnc, Local construction, etale maps of pairs
(blueprint: lem-per-etale-section-deformation-comparison). -/
def normalChart {U V S : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian V] [IsNoetherian S]
    (d : ℕ) (g : V ⟶ S) (s : S ⟶ V) [IsClosedImmersion s]
    (j : U ⟶ V) [IsOpenImmersion j] (sU : S ⟶ U) [IsClosedImmersion sU]
    (sqj : IsPullback sU (𝟙 S) j s)
    (e : U ⟶ AffineSpace (ULift.{u} (Fin d)) S) [Etale e] [IsSeparated e]
    (sqe : IsPullback sU (𝟙 S) e (AffineSpace.zeroSection (ULift.{u} (Fin d)) S)) :
    s.ker.normalCone ⟶ AffineSpace (ULift.{u} (Fin d)) S :=
  letI := LocallyOfFiniteType.isLocallyNoetherian
    (AffineSpace (ULift.{u} (Fin d)) S ↘ S)
  letI := QuasiCompact.compactSpace_of_compactSpace
    (AffineSpace (ULift.{u} (Fin d)) S ↘ S)
  letI : IsNoetherian (AffineSpace (ULift.{u} (Fin d)) S) := ⟨⟩
  letI := (etaleNormalMap_spec j g s sU sqj).1
  inv (etaleNormalMap j g s sU sqj) ≫
    etaleNormalMap e (AffineSpace (ULift.{u} (Fin d)) S ↘ S)
      (AffineSpace.zeroSection (ULift.{u} (Fin d)) S) sU sqe ≫ originNormalChart S d

/-- The map induced by the ideal classes is an isomorphism over S preserving zero.
The Rees-cone presentation is canonically Spec Sym(I/I^2) by the recorded conormal
comparison. Source: sk-thm-dnc, Local construction
(blueprint: lem-per-etale-section-deformation-comparison).
Proof: Step 2 tensors the inclusions J^m into R[x] with the etale chart, obtaining
B tensor J^m=I^m. The Laurent pieces give B[t,I/t]=B tensor R[t,u], x_i=t*u_i.
Step 3 specializes at zero. The specified quotient sends a/t^m modulo t to [a] in
degree m, so the coordinates are exactly [e^*x_i], including their products. This is
the symmetric algebra of the conormal frame. The augmentations kill these generators,
and the constants are fixed, proving both structural identities. The open contains
the whole centre, so its normal map is invertible. Empty S and d=0 are included. -/
theorem normalChart_spec {U V S : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian V] [IsNoetherian S]
    (d : ℕ) (g : V ⟶ S) (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) (j : U ⟶ V) [IsOpenImmersion j]
    (sU : S ⟶ U) [IsClosedImmersion sU] (sqj : IsPullback sU (𝟙 S) j s)
    (e : U ⟶ AffineSpace (ULift.{u} (Fin d)) S) [Etale e] [IsSeparated e]
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) S ↘ S) = j ≫ g)
    (sqe : IsPullback sU (𝟙 S) e (AffineSpace.zeroSection (ULift.{u} (Fin d)) S)) :
    IsIso (normalChart d g s j sU sqj e sqe) ∧
    normalChart d g s j sU sqj e sqe ≫ (AffineSpace (ULift.{u} (Fin d)) S ↘ S) =
      Scheme.Hom.normalConeProj g s ∧
    s.normalConeZeroSection ≫ normalChart d g s j sU sqj e sqe =
      AffineSpace.zeroSection (ULift.{u} (Fin d)) S := by
  sorry

/-- The published section locality map is invertible: it is the section compositor
followed by exact inverse image of the counit-normalized locality isomorphism.
Source: sk-thm-dnc, Local construction; lem-amb-etale-adjoint-locality
(blueprint: lem-per-etale-section-deformation-comparison).
Proof: the inverse-image compositor is an isomorphism. Exact inverse image identifies
left-derived pullback with termwise derived pullback. The locality factor is the uniquely
counit-preserving isomorphism of the recorded dependency. Pullback preserves its inverse,
and composition preserves invertibility. No constructibility restriction is used. -/
theorem sectionLocality_isIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X S : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian S]
    (h : U ⟶ X) [Etale h] [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (f : X ⟶ S) [HasCompactification f] (f' : U ⟶ S) [HasCompactification f']
    (w : h ≫ f = f') (s : S ⟶ X) (s' : S ⟶ U) (hs : s' ≫ h = s) :
    IsIso (etaleSectionMap A h f f' w s s' hs) := by
  sorry

attribute [instance] sectionLocality_isIso

/-- Restrict locality for j and invert locality for e. This is chi_e, from the original
section invariant to the standard affine-space zero-section invariant.
Source: sk-thm-dnc, Local construction, counit-preserving etale locality
(blueprint: lem-per-etale-section-deformation-comparison). -/
def chartComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V S : Scheme.{u}} [IsNoetherian U] [IsNoetherian V] [IsNoetherian S]
    (d : ℕ) (g : V ⟶ S) [HasCompactification g]
    (s : S ⟶ V) (j : U ⟶ V) [IsOpenImmersion j] [QuasiCompact j]
    (sU : S ⟶ U) (hj : sU ≫ j = s)
    (e : U ⟶ AffineSpace (ULift.{u} (Fin d)) S) [Etale e] [IsSeparated e]
    [LocallyOfFiniteType e] [QuasiCompact e]
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) S ↘ S) = j ≫ g)
    (he : sU ≫ e = AffineSpace.zeroSection (ULift.{u} (Fin d)) S)
    [HasCompactification (j ≫ g)]
    [HasCompactification (AffineSpace (ULift.{u} (Fin d)) S ↘ S)] :
    sectionInvariant A g s ⟶
      sectionInvariant A (AffineSpace (ULift.{u} (Fin d)) S ↘ S)
        (AffineSpace.zeroSection (ULift.{u} (Fin d)) S) :=
  letI := LocallyOfFiniteType.isLocallyNoetherian
    (AffineSpace (ULift.{u} (Fin d)) S ↘ S)
  letI := QuasiCompact.compactSpace_of_compactSpace
    (AffineSpace (ULift.{u} (Fin d)) S ↘ S)
  letI : IsNoetherian (AffineSpace (ULift.{u} (Fin d)) S) := ⟨⟩
  etaleSectionMap A j g (j ≫ g) rfl s sU hj ≫
    inv (etaleSectionMap A e (AffineSpace (ULift.{u} (Fin d)) S ↘ S) (j ≫ g)
      w (AffineSpace.zeroSection (ULift.{u} (Fin d)) S) sU he)

/-- Restriction of locality for the specified normal frame. The geometry proof supplies
Noetherianity of the cone, and normalChart_spec supplies its actual projection and zero.
Source: sk-thm-dnc, Local construction, normal frame
(blueprint: lem-per-etale-section-deformation-comparison). -/
def normalComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V S : Scheme.{u}} [IsNoetherian U] [IsNoetherian V] [IsNoetherian S]
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g] [IsSeparated g]
    [QuasiCompact g] [HasCompactification g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    (j : U ⟶ V) [IsOpenImmersion j] (sU : S ⟶ U) [IsClosedImmersion sU]
    (sqj : IsPullback sU (𝟙 S) j s)
    (e : U ⟶ AffineSpace (ULift.{u} (Fin d)) S) [Etale e] [IsSeparated e]
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) S ↘ S) = j ≫ g)
    (sqe : IsPullback sU (𝟙 S) e (AffineSpace.zeroSection (ULift.{u} (Fin d)) S))
    [HasCompactification (Scheme.Hom.normalConeProj g s)]
    [HasCompactification (AffineSpace (ULift.{u} (Fin d)) S ↘ S)] :
    sectionInvariant A (Scheme.Hom.normalConeProj g s) s.normalConeZeroSection ⟶
      sectionInvariant A (AffineSpace (ULift.{u} (Fin d)) S ↘ S)
        (AffineSpace.zeroSection (ULift.{u} (Fin d)) S) :=
  letI := geometry d g s hs
  letI := LocallyOfFiniteType.isLocallyNoetherian
    (AffineSpace (ULift.{u} (Fin d)) S ↘ S)
  letI := QuasiCompact.compactSpace_of_compactSpace
    (AffineSpace (ULift.{u} (Fin d)) S ↘ S)
  letI : IsNoetherian (AffineSpace (ULift.{u} (Fin d)) S) := ⟨⟩
  letI := (normalChart_spec d g s hs j sU sqj e w sqe).1
  inv (etaleSectionMap A (normalChart d g s j sU sqj e sqe)
    (AffineSpace (ULift.{u} (Fin d)) S ↘ S) (Scheme.Hom.normalConeProj g s)
    (normalChart_spec d g s hs j sU sqj e w sqe).2.1
    (AffineSpace.zeroSection (ULift.{u} (Fin d)) S) s.normalConeZeroSection
    (normalChart_spec d g s hs j sU sqj e w sqe).2.2)

/-- The specified specialization, with auxiliary quasi-compactness supplied by geometry.
Source: sk-thm-dnc, restriction at zero
(blueprint: lem-per-etale-section-deformation-comparison). -/
def delta (A : Type (u + 1)) [CommRing A] [Finite A]
    {V S : Scheme.{u}} [IsNoetherian S]
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g] [IsSeparated g]
    [QuasiCompact g] [HasCompactification g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    [HasCompactification (Scheme.Hom.normalConeProj g s)]
    (κ : family A g s ≅
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
          (sectionInvariant A g s)) :
    sectionInvariant A g s ⟶
      sectionInvariant A (Scheme.Hom.normalConeProj g s) s.normalConeZeroSection :=
  letI := geometry d g s hs
  specialization A g s κ

/-- Etale coordinates preserve the actual normalized deformation comparison.
Source: main-20261015, sk-thm-dnc.proof.md, Local construction and normalization
(blueprint: lem-per-etale-section-deformation-comparison).
Proof:
1. Set C=s^*omega_g, F=s-tilde^*omega_g-tilde. Keep atOne and atZero in the formula
   delta=atZero composed with (i0^*kappa)^(-1) and the section compositor.
2. Flatness over R[x] identifies B tensor J^m with I^m. The Laurent pieces give the
   actual Rees chart B[t,I/t]=B tensor R[t,u], x_j=t*u_j; these formulas glue.
3. Its fibres are e at one and exactly normalChart at zero, since e^*x_j/t modulo t
   is the degree-one ideal class. The open deformation contains the whole section.
4. Noetherian permanence and Nagata supply the auxiliary compactifications; etale
   restriction preserves smooth pure dimension. The same finite constant ring is used.
5. Compact-support composition, sum-extension normalization and mate pasting commute
   locality with the canonical smooth exceptional base-change maps, including identity.
6. Compare F by locality to the affine-space family, then by inverse smooth base change
   to a^*(0^*omega_q), obtaining H. Exact inverse image preserves the composites.
7. The two fibre equations are i1^*H=chi_e atOne and i0^*H=chi_lambda atZero;
   base change along a i_r=1 cancels the affine-family comparison.
8. The map (a^*chi_e^(-1))H is normalized at one, hence equals kappa by uniqueness.
   Restrict at zero and invert to obtain delta followed by chi_lambda equals chi_e.
No orientation is chosen. The empty base, zero dimension and nonreduced bases are allowed. -/
theorem etale_section_deformation_comparison
    (ell n : ℕ) [Fact ell.Prime] (hn : 1 ≤ n)
    {V S : Scheme.{u}} [IsNoetherian V] [IsNoetherian S]
    (hS : ∀ x : S, IsUnit (ell : S.presheaf.stalk x))
    (hV : ∀ x : V, IsUnit (ell : V.presheaf.stalk x))
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g]
    [IsSeparated g] [QuasiCompact g] [HasCompactification g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    (hregular : ∀ x : S, ∃ W : V.affineOpens, s x ∈ W.1 ∧
      ∃ r : Fin d → Γ(V, W.1),
        RingTheory.Sequence.IsWeaklyRegular Γ(V, W.1) (List.ofFn r) ∧
          Ideal.span (Set.range r) = s.ker.ideal W)
    {U : Scheme.{u}} [IsNoetherian U] (j : U ⟶ V) [IsOpenImmersion j]
    [QuasiCompact j] (sU : S ⟶ U) [IsClosedImmersion sU]
    (sqj : IsPullback sU (𝟙 S) j s)
    (e : U ⟶ AffineSpace (ULift.{u} (Fin d)) S)
    [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) S ↘ S) = j ≫ g)
    (sqe : IsPullback sU (𝟙 S) e (AffineSpace.zeroSection (ULift.{u} (Fin d)) S))
    [HasCompactification (j ≫ g)]
    [HasCompactification (AffineSpace (ULift.{u} (Fin d)) S ↘ S)]
    [HasCompactification (Scheme.Hom.normalConeProj g s)]
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    (κ : family (Coeff ell n) g s ≅
      (upperStar (ModuleCat.{u + 1} (Coeff ell n))
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
          (sectionInvariant (Coeff ell n) g s))
    (hκ : Normalized (Coeff ell n) g s hs κ) :
    delta (Coeff ell n) d g s hs κ ≫
        normalComparison (Coeff ell n) d g s hs j sU sqj e w sqe =
      chartComparison (Coeff ell n) d g s j sU
        (sqj.w.trans (Category.id_comp s)) e w
        (sqe.w.trans (Category.id_comp (AffineSpace.zeroSection (ULift.{u} (Fin d)) S))) := by
  sorry

end AlgebraicGeometry.Etale.EtaleSectionDeformationComparison
