/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.PuritySectionInvariantIntrinsic
public import Sheaf.Paper.PurityDncInvariance
public import Sheaf.Paper.BasicOperationsCoefficientReduction
public import Sheaf.SixFunctors.FiniteExceptional
public import Sheaf.Paper.PurityNormalCone
public import Sheaf.SecSmoothPurity.PurityDncCoefficientTransport
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.SecSmoothPurity.ScalarExtensionFunctor
import Sheaf.SecSmoothPurity.ReductionExceptional
import Sheaf.Paper.EtaleCompactSupportCoefficientChange
import Sheaf.SecSmoothPurity.ReductionDirectImage
import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
import Sheaf.Paper.FiniteLocalizingExceptionalPreservation
import Sheaf.SecSmoothPurity.ReductionCompatibilities
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses

/-! # Finite reduction of the normalized deformation comparison

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction/
thm-pur-finite-reduction-of-purity.proof.md, Step 3
(blueprint: lem-pur-finite-dnc-normalization-reduction).

The section objects use their published ordinary-etale-origin presentation in the
intrinsic small pro-etale coefficient category. The DNC arrow is transported from the
unique normalized arrow of `existsUnique_dncInvariance`. The coefficient arrow is the
published exceptional counit mate pulled back along the section. Coordinate comparisons
are fixed by the unique counit-normalized etale localization, not by a bare existence
of isomorphisms. The local square is written in the ordinary-etale presentation and
then mapped by the canonical small pro-etale realization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting.FiniteDnc

/-- The same coefficient setting at another positive level; all field and extension data
are retained. Source: finite-reduction Step 3
(blueprint: lem-pur-finite-dnc-normalization-reduction). -/
def atLevel (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) :
    PurityFiniteSetting.{u} := { P with level := m, level_pos := hm }

/-- The actual quotient O_E/(varpi^n) to O_E/(varpi^m), including m=n.
Source: finite-reduction Step 3
(blueprint: lem-pur-finite-dnc-normalization-reduction). -/
def quotient (P : PurityFiniteSetting.{u}) {m : ℕ} (hmn : m ≤ P.level) :
    P.Ring →+* Padic.coefficientExtensionRing P.coefficients.l P.extension m :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)

/-- The actual normalized DNC arrow in the published intrinsic etale-origin realization.
The only choice is from the unique normalization theorem. Both displayed comparisons
are the canonical section comparisons of that theorem.
Source: sk-thm-dnc, uniqueness and normalization
(blueprint: lem-pur-finite-dnc-normalization-reduction). -/
def normalizedDnc (P : PurityFiniteSetting.{u}) {V S : Scheme.{u}}
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g]
    (aS : S ⟶ Spec (.of P.field.k)) [IsSeparated aS]
    [LocallyOfFiniteType aS] [QuasiCompact aS]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S) :
    (ProEtale.reductionSite P.Ring S).obj (Dnc.sourceEtale P d g aS s) ≅
      (ProEtale.reductionSite P.Ring S).obj (Dnc.normalEtale P d g aS s hs) :=
  (sfIntrinsicDerivedEquivalence S P.Ring).functor.mapIso
    ((Dnc.sourceComparison P d g aS s).symm ≪≫
      (Dnc.existsUnique_dncInvariance P d g aS s hs).choose ≪≫
      Dnc.normalComparison P d g aS s hs)

/-- Canonical etale localization of the exceptional functor at the coefficient unit.
It is selected by the unique counit equation, using the same compactifications and
adjunctions as the published exceptional inverse image.
Source: sk-thm-dnc, etale coordinates; etale ambient adjoint locality
(blueprint: lem-pur-finite-dnc-normalization-reduction). -/
def etaleDualizing (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X S : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian S]
    (v : U ⟶ X) [AlgebraicGeometry.Etale v] [IsSeparated v] [QuasiCompact v]
    (f : X ⟶ S) [HasCompactification f] [HasCompactification (v ≫ f)] :
    (Etale.upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.obj
        (Etale.dualizingComplex (ModuleCat.{u + 1} A) f) ≅
      Etale.dualizingComplex (ModuleCat.{u + 1} A) (v ≫ f) :=
  (Etale.leftDerivedUpperStarIsoMapDerivedCategory _ v).app _ ≪≫
    (Etale.existsUnique_etaleAmbientAdjointLocalityIso A v f
      (HasCompactification.compactification f)
      (HasCompactification.compactification (v ≫ f))
      (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} A) f)
      (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} A) (v ≫ f))
      (Etale.rightDerivedUpperShriekAdjunction _ f)
      (Etale.rightDerivedUpperShriekAdjunction _ (v ≫ f))).choose.app (𝟙_ _)

/-- Pulling the canonical etale localization comparison to a section.
Source: sk-thm-dnc, coordinate identifications
(blueprint: lem-pur-finite-dnc-normalization-reduction). -/
def etaleSection (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X S : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian S]
    (v : U ⟶ X) [AlgebraicGeometry.Etale v] [IsSeparated v] [QuasiCompact v]
    (f : X ⟶ S) [HasCompactification f] [HasCompactification (v ≫ f)]
    (σ : S ⟶ U) :
    Etale.sectionInvariant A f (σ ≫ v) ≅ Etale.sectionInvariant A (v ≫ f) σ :=
  (Etale.leftDerivedUpperStarComp _ σ v).app _ ≪≫
    (Etale.upperStar (ModuleCat.{u + 1} A) σ).leftDerivedFunctor.mapIso
      (etaleDualizing A v f)

/-- Equality of the geometric maps induces equality of their section objects.
Source: sk-thm-dnc, centered coordinate equations
(blueprint: lem-pur-finite-dnc-normalization-reduction). -/
def sectionCongr (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} {f f' : X ⟶ S}
    [HasCompactification f] [HasCompactification f'] (hf : f = f')
    {s s' : S ⟶ X} (hs : s = s') :
    Etale.sectionInvariant A f s ≅ Etale.sectionInvariant A f' s' := by
  subst f'
  subst s'
  exact Iso.refl _

/-- The actual identification associated to centered etale coordinates, including the
base-change mate. Here W is an etale neighborhood of the localized section and e is
its etale coordinate map to standard affine space. Neither need be a global isomorphism.
Source: sk-thm-dnc, local standard coordinates
(blueprint: lem-pur-finite-dnc-normalization-reduction). -/
def coordinateIdentification (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S S' W : Scheme.{u}} [IsNoetherian S'] [IsNoetherian W]
    (f : X ⟶ S) [HasCompactification f] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (s : S ⟶ X) (hs : s ≫ f = 𝟙 S) (b : S' ⟶ S)
    (d : ℕ) (j : W ⟶ pullback f b) [AlgebraicGeometry.Etale j]
    [IsSeparated j] [QuasiCompact j]
    (e : W ⟶ AffineSpace (ULift.{u} (Fin d)) S') [AlgebraicGeometry.Etale e]
    [IsSeparated e] [QuasiCompact e]
    (hje : j ≫ pullback.snd f b = e ≫ (AffineSpace (ULift.{u} (Fin d)) S' ↘ S'))
    (σ : S' ⟶ W) (hσj : σ ≫ j = Scheme.Hom.baseChangeSection f s hs b)
    (hσe : σ ≫ e = AffineSpace.zeroSection (ULift.{u} (Fin d)) S') :
    (Etale.upperStar (ModuleCat.{u + 1} A) b).leftDerivedFunctor.obj
        (Etale.sectionInvariant A f s) ⟶
      Etale.sectionInvariant A (AffineSpace (ULift.{u} (Fin d)) S' ↘ S')
        (AffineSpace.zeroSection (ULift.{u} (Fin d)) S') := by
  letI : IsNoetherian (pullback f b) := ⟨⟩
  letI : HasCompactification (j ≫ pullback.snd f b) := inferInstance
  letI : IsNoetherian (AffineSpace (ULift.{u} (Fin d)) S') :=
    isNoetherian_of_locallyOfFiniteType (AffineSpace (ULift.{u} (Fin d)) S' ↘ S')
  letI : HasCompactification (e ≫ (AffineSpace (ULift.{u} (Fin d)) S' ↘ S')) :=
    inferInstance
  exact Etale.NoetherianSectionSpecialization.sectionMap A f (pullback.snd f b) b
      (pullback.fst f b) (IsPullback.of_hasPullback f b) s
      (Scheme.Hom.baseChangeSection f s hs b)
      (Scheme.Hom.baseChangeSection_fst f s hs b) ≫
    (sectionCongr A (f := pullback.snd f b)
      (s := Scheme.Hom.baseChangeSection f s hs b) (s' := σ ≫ j) rfl hσj.symm).hom ≫
    (etaleSection A j (pullback.snd f b) σ).hom ≫
    (sectionCongr A (s := σ) hje rfl).hom ≫
    (etaleSection A e (AffineSpace (ULift.{u} (Fin d)) S' ↘ S') σ).inv ≫
    (sectionCongr A (f := AffineSpace (ULift.{u} (Fin d)) S' ↘ S') rfl hσe).hom


/-- Coefficient compatibility with every centered etale coordinate identification.
The two morphisms are realized on the small pro-etale site, using the canonical
pullback/scalar comparison and the standard-pair coefficient map.
Source: finite-reduction Step 3, local clause
(blueprint: lem-pur-finite-dnc-normalization-reduction). -/
def CoordinateSquares {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X S : Scheme.{u}}
    (f : X ⟶ S) [HasCompactification f] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (s : S ⟶ X) (hs : s ≫ f = 𝟙 S) (d : ℕ) : Prop :=
  ∀ (S' : Scheme.{u}) [IsNoetherian S'] (b : S' ⟶ S)
    [AlgebraicGeometry.Etale b] [IsSeparated b] [QuasiCompact b]
    (W : Scheme.{u}) [IsNoetherian W]
    (j : W ⟶ pullback f b) [AlgebraicGeometry.Etale j]
    [IsSeparated j] [QuasiCompact j]
    (e : W ⟶ AffineSpace (ULift.{u} (Fin d)) S') [AlgebraicGeometry.Etale e]
    [IsSeparated e] [QuasiCompact e]
    (hje : j ≫ pullback.snd f b = e ≫ (AffineSpace (ULift.{u} (Fin d)) S' ↘ S'))
    (σ : S' ⟶ W) (hσj : σ ≫ j = Scheme.Hom.baseChangeSection f s hs b)
    (hσe : σ ≫ e = AffineSpace.zeroSection (ULift.{u} (Fin d)) S'),
    (ProEtale.reductionSite B S').map
      ((Etale.scalarPullbackIso (RingHom.ulift.{u + 1, u + 1, u, u} φ) b).inv.app _ ≫
        (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) b).leftDerivedFunctor.map
          (DncCoefficientTransport.sectionMap (RingHom.ulift φ) f s) ≫
        coordinateIdentification (ULift.{u + 1, u} B) f s hs b d j e hje σ hσj hσe) =
    (ProEtale.reductionSite B S').map
      ((Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) S').map
        (coordinateIdentification (ULift.{u + 1, u} A) f s hs b d j e hje σ hσj hσe) ≫
        DncCoefficientTransport.sectionMap (RingHom.ulift φ)
          (AffineSpace (ULift.{u} (Fin d)) S' ↘ S')
          (AffineSpace.zeroSection (ULift.{u} (Fin d)) S'))

/-- The global normalized DNC square and its two actual coordinate-localization squares.
All compactifications, smoothness and finiteness instances are supplied by the stated
finite-type geometry and finite coefficient setting, rather than extra hypotheses.
Source: finite-reduction Step 3
(blueprint: lem-pur-finite-dnc-normalization-reduction). -/
def Assertions (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) {V S : Scheme.{u}} (d : ℕ) (g : V ⟶ S)
    [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g]
    (aS : S ⟶ Spec (.of P.field.k)) [IsSeparated aS]
    [LocallyOfFiniteType aS] [QuasiCompact aS]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S) : Prop := by
  letI := SmoothOfRelativeDimension.smooth d g
  letI := Dnc.compactifiable P g aS
  letI := Dnc.normalCompactifiable P d g aS s hs
  letI := Dnc.normalQuasiCompact d g s hs
  letI : SmoothOfRelativeDimension d (Scheme.Hom.normalConeProj g s) :=
    (Scheme.Hom.normalConeData d hs).smoothOfRelativeDimension_proj
  letI := SmoothOfRelativeDimension.smooth d (Scheme.Hom.normalConeProj g s)
  letI : Finite (Padic.coefficientExtensionRing P.coefficients.l P.extension m) :=
    Padic.finite_coefficientExtensionRing P.coefficients.l P.extension m hm
  exact
    ((ProEtale.scalarExtensionFunctor (quotient P hmn) S).map
        (normalizedDnc P d g aS s hs).hom ≫
      DncCoefficientTransport.realizedSectionMap (quotient P hmn)
        (Scheme.Hom.normalConeProj g s) s.normalConeZeroSection =
      DncCoefficientTransport.realizedSectionMap (quotient P hmn) g s ≫
        (normalizedDnc (atLevel P m hm) d g aS s hs).hom) ∧
    CoordinateSquares (quotient P hmn) g s hs d ∧
    CoordinateSquares (quotient P hmn) (Scheme.Hom.normalConeProj g s)
      s.normalConeZeroSection (Scheme.Hom.normalConeZeroSection_normalConeProj hs) d

/-- Finite reduction preserves the identity-normalized DNC comparison and both actual
standard-coordinate identifications, including d=0, m=n, and empty schemes.
Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction/
thm-pur-finite-reduction-of-purity.proof.md, Step 3
(blueprint: lem-pur-finite-dnc-normalization-reduction).
Proof: (1) Take R=Z/(ell^n), which maps to A and B since ell belongs to (varpi_E).
The DVR and finite residue field give finite quotients; scalar extension preserves
isomorphisms with its canonical associator. (2) Identify all exceptional coefficient
maps by their counit transposes, using the same compactification and compact-support
comparison; pullback gives the specified section maps. (3) Apply coefficient
composition to R -> A -> B and pull back along each section to get t_B=q Q(t_A),
using the canonical pullback/tensor balancing and scalar associativity. (4) Apply
cyclic-initial-ring DNC coefficient transport separately to R -> A and R -> B;
uniqueness identifies its normalized comparisons with delta_A and delta_B.
(5) Substitute the cocycle in the two DNC squares and cancel the invertible Q(t_A)
to obtain the displayed global square. (6) For either source or normal coordinates,
the chart clause gives lambda_D t_D=t_D_standard T_D(lambda_R). Substitute the same
cocycle for the pair and standard pair, then cancel Q(t_A), yielding exactly both
localization squares. No flatness or ramification-index divisibility is used. -/
theorem finiteDncNormalizationReduction (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    {V S : Scheme.{u}} (d : ℕ) (g : V ⟶ S)
    [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g]
    (aS : S ⟶ Spec (.of P.field.k)) [IsSeparated aS]
    [LocallyOfFiniteType aS] [QuasiCompact aS]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S) :
    Assertions P m hm hmn d g aS s hs := by
  sorry

end WeilConjectures.PurityFiniteSetting.FiniteDnc
