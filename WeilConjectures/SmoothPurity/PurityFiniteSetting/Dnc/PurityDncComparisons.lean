/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Dnc.PurityDncFiniteRealization
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.Coordinates
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.BaseChange
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Deformation
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.AlgebraicGeometry.PurityNormalBundle.PurityNormalBundle
import WeilConjectures.AlgebraicGeometry.Purity.PurityNormalProjection
import WeilConjectures.AlgebraicGeometry.DeformationToNormalCone
import WeilConjectures.RingTheory.AssociatedGradedRing
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothDualityBaseChangeCompat

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
  classical
  let l := P.coefficients.l
  let E := P.extension
  have hdvr := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hm : (l : Padic.coefficientExtensionIntegers l E) ∈
      Padic.coefficientExtensionMaximalIdeal l E := by
    apply (hdvr.2.1 _).2
    change spectralNorm (Padic l) E (l : E) < 1
    rw [← map_natCast (algebraMap (Padic l) E),
      spectralNorm_extends (K := Padic l) (L := E)]
    exact Padic.norm_p_lt_one
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
      Padic.coefficientExtensionMaximalIdeal l E :=
    hdvr.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hkill : ((l ^ P.level : ℕ) : P.Coefficient) = 0 := by
    apply ULift.ext
    change ((l ^ P.level : ℕ) :
      Padic.coefficientExtensionIntegers l E ⧸ Padic.coefficientExtensionIdeal l E P.level) = 0
    rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
    rw [Nat.cast_pow]
    change (l : Padic.coefficientExtensionIntegers l E) ^ P.level ∈
      Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
        Set (Padic.coefficientExtensionIntegers l E)) ^ P.level
    rw [hgen]
    exact Ideal.pow_mem_pow hm P.level
  let : Fintype P.field.k₀ := Fintype.ofFinite _
  have : Fact P.field.p.Prime := ⟨P.field.prime⟩
  have : CharP P.field.k₀ P.field.p := charP_of_card_eq_prime_pow
    (by simpa only [← Nat.card_eq_fintype_card] using
      P.field.card_base.trans P.field.cardinality_eq)
  have : CharP P.field.k P.field.p := charP_of_injective_algebraMap' P.field.k₀ P.field.p
  have hl : (l : P.field.k) ≠ 0 := by
    intro hz
    have hdiv := (CharP.cast_eq_zero_iff P.field.k P.field.p l).mp hz
    exact P.coefficients.different
      ((Nat.prime_dvd_prime_iff_eq P.field.prime (Fact.out : l.Prime)).mp hdiv).symm
  refine ⟨l ^ P.level, pow_pos (Nat.Prime.pos Fact.out) _, hkill, ?_⟩
  have hu := ((Ne.isUnit hl).pow P.level).map
    ((Scheme.ΓSpecIso (.of P.field.k)).inv.hom)
  simpa only [map_pow, map_natCast, Nat.cast_pow] using hu.map a.appTop.hom

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
  have := LocallyOfFiniteType.isLocallyNoetherian aB
  have := QuasiCompact.compactSpace_of_compactSpace aB
  exact (NagataCompactification g).hasCompactification

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

private theorem normalAffine {V B : Scheme.{u}} (g : V ⟶ B)
    (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) :
    IsAffineHom (Scheme.Hom.normalConeProj g s) := by
  rw [← Scheme.Hom.purityNormalProjection_eq s g hs]
  have : IsAffineHom (Scheme.Hom.purityNormalProjection s ≫ s) := by
    simp only [Scheme.Hom.purityNormalProjection, IsClosedImmersion.lift_fac]
    infer_instance
  exact IsAffineHom.of_comp _ s

/-- The actual normal-cone projection is compactifiable in the finite-type domain.
Source: blueprint sk-thm-dnc, domain check; sk-lem-geometry (1)
(blueprint: lem-pur-dnc-section-geometry).
Proof: the canonical factorization of the affine cone-to-V map through the closed
section makes the normal projection affine, hence separated and quasi-compact.
The normalConeData of the smooth section supplies its relative smoothness, hence
local finite type. Apply compactifiable over the finite-type base B. -/
theorem normalCompactifiable (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) :
    HasCompactification (Scheme.Hom.normalConeProj g s) := by
  have := normalAffine g s hs
  have : SmoothOfRelativeDimension d (Scheme.Hom.normalConeProj g s) :=
    (Scheme.Hom.normalConeData d hs).smoothOfRelativeDimension_proj
  have := SmoothOfRelativeDimension.smooth d (Scheme.Hom.normalConeProj g s)
  exact compactifiable P (Scheme.Hom.normalConeProj g s) aB

/-- The normal projection is quasi-compact: it is the finite-rank affine bundle
attached to the locally free conormal module.
Source: blueprint normal cone and sk-lem-geometry (1)
(blueprint: lem-pur-dnc-section-geometry).
Proof: the cone-to-V map is affine and factors through the closed section.
Since that section is separated, its factor to B is affine, hence quasi-compact. -/
theorem normalQuasiCompact {V B : Scheme.{u}} (d : ℕ) (g : V ⟶ B)
    [SmoothOfRelativeDimension d g] (s : B ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 B) : QuasiCompact (Scheme.Hom.normalConeProj g s) := by
  have := normalAffine g s hs
  infer_instance

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
