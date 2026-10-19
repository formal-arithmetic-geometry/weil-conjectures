/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.Paper.PurityDncFiniteRealization
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.Coordinates
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.BaseChange
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Deformation
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality
import Sheaf.AlgebraicGeometry.EtaleLocalNormalForm
import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
import Sheaf.Paper.PurityDncFamilyIntrinsic
import Sheaf.Paper.PurityNormalCone
import Sheaf.Paper.PuritySectionInvariantIntrinsic
import Sheaf.Paper.VectorBundlePurity
import Sheaf.SixFunctors.SmoothDualityBaseChangeCompat

/-! # Canonical fibre comparisons for the deformation of a smooth section

Source: blueprint sec-smooth-purity/sk-lem-geometry, clauses (1)--(5)
(blueprint: lem-pur-dnc-section-geometry).

The normal cone and deformation space are the published extended-Rees constructions.
Fibre comparisons use the actual compact-support adjunction mate; they are not chosen
from the upstream nonempty-isomorphism assertions.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.Dnc


/-- Finite purity coefficients have an exponent invertible on every k-scheme.
Source: blueprint def-pur-conventions; the coefficient residue characteristic is l ≠ p
(blueprint: lem-pur-dnc-section-geometry).
Proof: l to the positive level annihilates O_E/(varpi^n), since its varpi-adic
valuation is at least n. Its image in k, and hence on T, is a unit. This also
applies to the empty scheme and does not require divisibility by the ramification index. -/
theorem invertibleExponent (P : PurityFiniteSetting.{u}) {T : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) : HasInvertibleExponent P.Coefficient T := by
  sorry

/-- Canonical base change of section invariants. The only nonformal factor is
`dualizingComplexBaseChangeMap`, the adjunction mate of inverse compact-support base change.
Source: blueprint sk-lem-geometry (1); smooth duality, arbitrary base change
(blueprint: lem-pur-dnc-section-geometry). -/
noncomputable def sectionBaseChange (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y X' Y' : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [HasCompactification f] [SmoothOfRelativeDimension d f]
    [HasInvertibleExponent Λ X]
    {b : Y' ⟶ Y} {f' : X' ⟶ Y'} {a : X' ⟶ X}
    [HasCompactification f'] [QuasiCompact f'] (sq : IsPullback a f' f b)
    (s : Y ⟶ X) (s' : Y' ⟶ X') (hs : s' ≫ a = b ≫ s) :
    (Etale.upperStar (ModuleCat.{u + 1} Λ) b).leftDerivedFunctor.obj
        (Etale.sectionInvariant Λ f s) ≅ Etale.sectionInvariant Λ f' s' :=
  letI := Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension_general
    Λ f d sq
  letI := (Etale.isIso_dualizingComplexBaseChangeMap_iff Λ sq).2
    (inferInstanceAs (IsIso ((Etale.rightDerivedUpperShriekBaseChangeMap Λ sq).app (𝟙_ _))))
  ((Etale.leftDerivedUpperStarComp _ b s).app _).symm ≪≫
    (Etale.leftDerivedUpperStarComp _ s' a (b ≫ s) hs.symm).app _ ≪≫
    (Etale.upperStar (ModuleCat.{u + 1} Λ) s').leftDerivedFunctor.mapIso
      (asIso (Etale.dualizingComplexBaseChangeMap Λ sq))

/-- Nagata supplies the compactification required by the published realization.
This is derived from separated finite type, not an additional hypothesis.
Proof: the finite-type base is Noetherian, hence quasi-compact and quasi-separated;
apply the published Nagata compactification theorem to the separated finite-type map.
Source: Stacks Tag 0F41; blueprint sk-thm-dnc domain check
(blueprint: lem-pur-dnc-section-geometry). -/
theorem compactifiable (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (g : V ⟶ B) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB] :
    HasCompactification g := by
  sorry

/-- The finite source section invariant, with compactifiability derived in its domain.
Source: blueprint def-pur-section-invariant, finite clause
(blueprint: lem-pur-dnc-section-geometry). -/
noncomputable def sourceSection (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (s : B ⟶ V) :=
  letI := SmoothOfRelativeDimension.smooth d g
  letI := compactifiable P g aB
  P.sectionInvariant g aB s

/-- The ordinary-etale presentation of the same source section invariant.
Source: blueprint finite section invariant and comparison
(blueprint: lem-pur-dnc-section-geometry). -/
noncomputable def sourceEtale (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (s : B ⟶ V) :=
  letI := SmoothOfRelativeDimension.smooth d g
  letI := compactifiable P g aB
  Etale.sectionInvariant P.Coefficient g s

/-- The actual normal-cone projection is compactifiable in the finite-type domain.
Source: blueprint sk-thm-dnc, domain check; sk-lem-geometry (1)
(blueprint: lem-pur-dnc-section-geometry).
Proof: the ideal of a smooth section is locally generated by a regular sequence of
length d. Its associated graded algebra is the symmetric algebra of the conormal
module. Thus this is an affine rank-d vector bundle over B, hence separated and
finite type. The finite-type base is Noetherian and Nagata applies. -/
theorem normalCompactifiable (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) :
    HasCompactification (Scheme.Hom.normalConeProj g s) := by
  sorry

/-- The normal projection is quasi-compact: it is the finite-rank affine bundle
attached to the locally free conormal module.
Source: blueprint normal cone and sk-lem-geometry (1)
(blueprint: lem-pur-dnc-section-geometry).
Proof: the regular-sequence associated-graded calculation identifies the projection
locally with affine d-space, so it is affine and thus quasi-compact. -/
theorem normalQuasiCompact {V B : Scheme.{u}} (d : ℕ) (g : V ⟶ B)
    [SmoothOfRelativeDimension d g] (s : B ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 B) : QuasiCompact (Scheme.Hom.normalConeProj g s) := by
  sorry

/-- The actual normal section invariant, in the same finite sheaf realization.
Source: blueprint def-pur-normal-bundle and sk-thm-dnc, displayed CN
(blueprint: lem-pur-dnc-section-geometry). -/
noncomputable def normalSection (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) :=
  letI := normalCompactifiable P d g aB s hs
  P.sectionInvariant (Scheme.Hom.normalConeProj g s) aB s.normalConeZeroSection

/-- The same normal section invariant on the ordinary etale site, before ν* transport.
Source: blueprint def-pur-normal-bundle and sk-thm-dnc
(blueprint: lem-pur-dnc-section-geometry). -/
noncomputable def normalEtale (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) :=
  letI := normalCompactifiable P d g aB s hs
  Etale.sectionInvariant P.Coefficient (Scheme.Hom.normalConeProj g s)
    s.normalConeZeroSection

/-- The family F = Ls~* Rg~! Λ on the ordinary etale site, before canonical ν* transport.
The source is the constructed DNC, not an unspecified deformation datum.
Source: blueprint def-pur-dnc-section-family, displayed family object
(blueprint: lem-pur-dnc-section-geometry). -/
noncomputable def familyEtale (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g]
    [IsSeparated g] [QuasiCompact g]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) :=
  letI := noetherian P aB
  letI := SmoothOfRelativeDimension.smooth d g
  letI := compactifiable P g aB
  letI := Scheme.Hom.hasCompactification_deformationSpaceProj g s d hs
  Etale.sectionInvariant P.Coefficient (Scheme.Hom.deformationSpaceProj g s)
    s.deformationSpaceSection

/-- The canonical fibre comparison at t=1, built from the actual Rees fibre square.
Source: blueprint sk-lem-geometry (1)
(blueprint: lem-pur-dnc-section-geometry). -/
noncomputable def fibreOne (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g] [IsSeparated g]
    [QuasiCompact g]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) :
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) B)).leftDerivedFunctor.obj
        (familyEtale P d g aB s hs) ≅ sourceEtale P d g aB s :=
  letI := noetherian P aB
  letI := SmoothOfRelativeDimension.smooth d g
  letI := compactifiable P g aB
  letI := Scheme.Hom.hasCompactification_deformationSpaceProj g s d hs
  letI := Scheme.Hom.smoothOfRelativeDimension_deformationSpaceProj d g s hs
  letI := invertibleExponent P (Scheme.Hom.deformationSpaceProj g s ≫
    (AffineSpace (ULift.{u} (Fin 1)) B ↘ B) ≫ aB)
  sectionBaseChange P.Coefficient d (Scheme.Hom.deformationSpaceProj g s)
    (Scheme.Hom.isPullback_deformationSpaceOneFibre g s) s.deformationSpaceSection s
    (Scheme.Hom.comp_deformationSpaceOneFibre hs)

/-- The canonical fibre comparison at t=0 to the actual associated-graded cone.
Source: blueprint sk-lem-geometry (1)
(blueprint: lem-pur-dnc-section-geometry). -/
noncomputable def fibreZero (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g] [IsSeparated g]
    [QuasiCompact g]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) :
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)).leftDerivedFunctor.obj
        (familyEtale P d g aB s hs) ≅ normalEtale P d g aB s hs :=
  letI := noetherian P aB
  letI := SmoothOfRelativeDimension.smooth d g
  letI := compactifiable P g aB
  letI := Scheme.Hom.hasCompactification_deformationSpaceProj g s d hs
  letI := Scheme.Hom.smoothOfRelativeDimension_deformationSpaceProj d g s hs
  letI := normalCompactifiable P d g aB s hs
  letI := normalQuasiCompact d g s hs
  letI := invertibleExponent P (Scheme.Hom.deformationSpaceProj g s ≫
    (AffineSpace (ULift.{u} (Fin 1)) B ↘ B) ≫ aB)
  sectionBaseChange P.Coefficient d (Scheme.Hom.deformationSpaceProj g s)
    (Scheme.Hom.isPullback_normalConeToDeformationSpace g s)
    s.deformationSpaceSection s.normalConeZeroSection
    Scheme.Hom.normalConeZeroSection_comp_normalConeToDeformationSpace

end WeilConjectures.PurityFiniteSetting.Dnc
