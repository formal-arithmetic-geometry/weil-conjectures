/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.Coherent

import all Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.CoherentKernelCokernelSum
import Sheaf.AlgebraicGeometry.FinitePresentationIntegralFiltration
import Sheaf.AlgebraicGeometry.IntegralIdealProperCohomology
import Sheaf.AlgebraicGeometry.CohomologyFiniteExtension
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import Sheaf.CategoryTheory.TruncationHypercohomology
import Mathlib.Data.Int.Interval
import all Sheaf.AlgebraicGeometry.DerivedDirectImageBoundedBelowQCoh
import all Sheaf.CategoryTheory.HalfPlaneWeakConvergence
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
import WeilConjectures.CategoryTheory.HalfPlaneWeakConvergence
import WeilConjectures.CategoryTheory.TruncationHypercohomology

/-! # Bounded coherent direct image in the Noetherian proper case

Source: Stacks Project, Tag 08E2, specialized to a proper morphism; Tag 02O5.
(blueprint: lem-pc-noetherian-proper-bounded-coherent-image).
-/

@[expose] public section
set_option autoImplicit false
universe u wY wT
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Finite generators and coherent relations give finite local presentations. -/
private theorem finitePresentation_of_coherent {X : Scheme.{u}}
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (h : RingedSpace.IsCoherent X.toRingedSpace F) :
    SheafOfModules.IsFinitePresentation.{u} (R := X.ringCatSheaf) F := by
  sorry

namespace Modules

/-- Integral-ideal devissage gives finite cohomology over an affine base (Tag 02O6). -/
private theorem finite_sections_proper {X T : Scheme.{u}} (f : X ⟶ T) [IsProper f]
    [HasInjectiveResolutions X.Modules] (ℱ : X.Modules) [ℱ.IsFinitePresentation]
    [IsAffine T] [IsNoetherianRing Γ(T, ⊤)]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    Module.Finite Γ(T, ⊤) Γ((higherDirectImage f q).obj ℱ, ⊤) := by
  classical
  have : IsLocallyNoetherian T := isLocallyNoetherian_of_isOpenImmersion T.isoSpec.hom
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := {}
  let R := Γ(T, ⊤)
  let P (M : X.Modules) : Prop := ∀ n : ℕ,
    letI : Module R (M.H n) := Module.compHom _ f.appTop.hom
    Module.Finite R (M.H n)
  have hzero (M : X.Modules) (hM : IsZero M) : P M := by
    intro n
    let : Module R (M.H n) := Module.compHom _ f.appTop.hom
    have hz (x : M.H n) : x = 0 := by
      have h := congrArg (fun φ ↦ H.map φ n x) (hM.eq_of_src (𝟙 M) 0)
      simpa only [H.map_id_apply, H.map_zero_apply] using h
    have : Subsingleton (M.H n) := ⟨fun x y ↦ (hz x).trans (hz y).symm⟩
    infer_instance
  have hiso {M N : X.Modules} (e : M ≅ N) (hM : P M) : P N := by
    intro n
    let : Module R (M.H n) := Module.compHom _ f.appTop.hom
    let : Module R (N.H n) := Module.compHom _ f.appTop.hom
    let eR : M.H n ≃ₗ[R] N.H n :=
      { H.mapLinearEquiv e n with
        map_smul' := fun a x ↦ (H.mapLinearEquiv e n).map_smul (f.appTop a) x }
    have := hM n
    exact Module.Finite.equiv eR
  obtain ⟨m, c, hc, hbot, htop, hpieces⟩ :=
    exists_finitePresentation_integral_filtration X ℱ
  have hpc : ∀ j : Fin (m + 1), P (c j : X.Modules) := by
    intro j
    induction j using Fin.induction with
    | zero =>
      apply hzero
      exact (Subobject.isoOfEq _ _ hbot ≪≫ Subobject.botCoeIsoZero).isZero_iff.mpr
        (isZero_zero X.Modules)
    | succ j ih =>
      let a := Subobject.ofLE (c j.castSucc) (c j.succ) (hc j.castSucc_le_succ)
      let S := ShortComplex.mk a (cokernel.π a) (cokernel.condition a)
      have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel a }
      obtain ⟨Z, i, hi, hZ, I, ⟨e⟩⟩ := hpieces j
      have := hi
      have := hZ
      have hI : P ((pushforward i).obj I.toModules) := by
        intro n
        exact finite_H_pushforward_integral_ideal f Z i I n
      have hQ : P (cokernel a) := hiso e.symm hI
      intro n
      exact finite_H_of_shortExact_middle R f.appTop.hom S hS n (ih n) (hQ n)
  have hF : P ℱ := hiso
    (Subobject.isoOfEq _ _ htop ≪≫ asIso (⊤ : Subobject ℱ).arrow) (hpc _)
  let : Module R (ℱ.H q) := Module.compHom _ f.appTop.hom
  have := hF q
  obtain ⟨e, he⟩ := exists_bijective_semilinearMap_sections_higherDirectImage_H f ℱ q
  let eR : Γ((higherDirectImage f q).obj ℱ, ⊤) →ₗ[R] ℱ.H q :=
    { e.toAddMonoidHom with map_smul' := fun a x ↦ e.map_smulₛₗ a x }
  exact Module.Finite.equiv (LinearEquiv.ofBijective eR he).symm


/-- Higher direct images of a finitely presented quasi-coherent module have finite
global sections over a Noetherian affine base under a proper morphism.
Source: Stacks Project, Tag 02O6, by integral-ideal devissage. -/
theorem finite_sections_proper_on_affine {X T : Scheme.{u}} (f : X ⟶ T) [IsProper f]
    [HasInjectiveResolutions X.Modules] (F : X.Modules) [F.IsFinitePresentation]
    [IsAffine T] [IsNoetherianRing Γ(T, ⊤)] [F.IsQuasicoherent] (q : ℕ) :
    Module.Finite Γ(T, ⊤) Γ((higherDirectImage f q).obj F, ⊤) :=
  finite_sections_proper f F q


/-- Affine-local finite cohomology gives coherent higher direct images (Tag 02O5). -/
private theorem finitePresentation_higherDirectImage_proper
    {X T : Scheme.{u}} (f : X ⟶ T) [IsProper f]
    [HasInjectiveResolutions X.Modules] (ℱ : X.Modules) [ℱ.IsFinitePresentation]
    [IsLocallyNoetherian T]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    ((higherDirectImage f q).obj ℱ).IsFinitePresentation := by
  have hP (V : T.Opens) (hV : IsAffineOpen V) :
      ∃ P : (((higherDirectImage f q).obj ℱ).restrict hV.fromSpec).Presentation, P.IsFinite := by
    have := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
    have : IsNoetherianRing Γ(Spec Γ(T, V), ⊤) :=
      isNoetherianRing_of_ringEquiv _ (Scheme.ΓSpecIso Γ(T, V)).commRingCatIsoToRingEquiv.symm
    have := isGrothendieckAbelian (Limits.pullback f hV.fromSpec)
    obtain ⟨e⟩ := nonempty_higherDirectImage_iso_restrict f ℱ hV.fromSpec _ _
      (IsPullback.of_hasPullback f hV.fromSpec) q
    have : ((Modules.pullback (pullback.fst f hV.fromSpec)).obj ℱ).IsFinitePresentation :=
      (SheafOfModules.isFinitePresentation (Limits.pullback f hV.fromSpec).ringCatSheaf).prop_of_iso
        ((restrictFunctorIsoPullback _).app ℱ) (isFinitePresentation_restrictFunctor _ ℱ)
    have : ((Modules.pullback (pullback.fst f hV.fromSpec)).obj ℱ).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent (Limits.pullback f hV.fromSpec).ringCatSheaf).prop_of_iso
        ((restrictFunctorIsoPullback _).app ℱ) (isQuasicoherent_restrictFunctor _ ℱ)
    have := finite_sections_proper (pullback.snd f hV.fromSpec)
      ((Modules.pullback (pullback.fst f hV.fromSpec)).obj ℱ) q
    let φ : Γ((higherDirectImage (pullback.snd f hV.fromSpec) q).obj
        ((Modules.pullback (pullback.fst f hV.fromSpec)).obj ℱ), ⊤) →ₗ[Γ(Spec Γ(T, V), ⊤)]
        Γ(((higherDirectImage f q).obj ℱ).restrict hV.fromSpec, ⊤) :=
      { toFun := e.hom.app ⊤, map_add' := map_add _, map_smul' := Hom.app_smul e.hom }
    have : Module.Finite Γ(Spec Γ(T, V), ⊤)
        Γ(((higherDirectImage f q).obj ℱ).restrict hV.fromSpec, ⊤) :=
      Module.Finite.of_surjective φ (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).2
    have := finite_sections_top_of_finite
      (((higherDirectImage f q).obj ℱ).restrict hV.fromSpec)
    have := isQuasicoherent_higherDirectImage f ℱ q
    exact exists_presentation_isFinite _
  have (V : T.affineOpens) : IsOpenImmersion (IsAffineOpen.fromSpec (U := V.1) V.2) :=
    IsAffineOpen.isOpenImmersion_fromSpec V.2
  choose P _ using fun V : T.affineOpens ↦ hP V.1 V.2
  refine isFinitePresentation_of_iSup_opensRange_eq_top _ _ ?_ P
  exact (iSup_congr fun V ↦ IsAffineOpen.opensRange_fromSpec V.2).trans
    (iSup_affineOpens_eq_top T)

end Modules

/-- A proper morphism over a Noetherian base preserves bounded coherent cohomology.
This asserts neither a finite-free representative nor pseudo-coherence or a base-change
comparison. Source: Stacks Project, Tag 08E2, Lemma 36.11.3; Tag 02O5.

Proof: Coherence makes every cohomology sheaf quasi-coherent and finite type on the
locally Noetherian source. Its nonzero-stalk locus is closed. Because p is proper, the
closed support is proper over T. Apply the hypercohomology spectral sequence for derived
pushforward. Its E2 terms are the higher direct images of these coherent sheaves, hence
coherent by proper coherence over a Noetherian base (Tag 02O5). In each total degree its
finite filtration has coherent subquotients, so the abutment is coherent. The lower
bound is the lower bound of A, since pushforward is left exact. For the upper bound,
p is quasi-compact and separated and T is quasi-compact. A finite affine cover yields a
uniform bound on the higher direct images of quasi-coherent modules; equivalently use
the derived uniform truncation bound of Tag 08D5. Shift A by its upper cohomology bound
and apply this bound, then shift back. This gives a finite interval containing all image
cohomology. The zero object gives zero image. For an empty source the image is zero.
No relative flatness, finite Tor dimension or finite-free image is used.

The existing proper-support direct-image module cannot be imported here: its current
proof dependencies reach the arbitrary-base pseudo-coherence item. This strictly
Noetherian proper case isolates the calculation needed before approximation pullback.
(blueprint: lem-pc-noetherian-proper-bounded-coherent-image). -/
theorem noetherian_proper_directImage_bounded_coherent
    {Y T : Scheme.{u}} [IsNoetherian T] (p : Y ⟶ T)
    [IsProper p]
    [HasDerivedCategory.{wY}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wT}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    (A : schemeDerivedCategory Y)
    (hbounded : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).obj A))
    (hcoherent : ∀ i : ℤ, RingedSpace.IsCoherent Y.toRingedSpace
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).obj A)) :
    (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) i).obj
          ((schemeDerivedDirectImage p).obj A))) ∧
    (∀ i : ℤ, RingedSpace.IsCoherent T.toRingedSpace
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) i).obj
          ((schemeDerivedDirectImage p).obj A))) := by
  sorry


end AlgebraicGeometry.Scheme
