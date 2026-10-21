/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.Paper.StrictLocalKummerTameModule
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Sheaf.Topology.ContinuousMapCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import WeilConjectures.RingTheory.NormalRingIntegrallyClosedTotal
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Topology.Spectral.Basic
import Sheaf.Topology.SpectralSpace.ClopenComponentHomeomorphism
import Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization
import Sheaf.Paper.CartesianCoefficients

/-! # Lisse morphisms on a parameter-root tower

Source: blueprint main-20261015, sec-six-functors-basics,
sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3).
The agent-formulated supplied-root-extension input has no asserted object extension.
(blueprint: lem-sfb-root-tower-lisse-morphism-extension).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- The complement of the parameter divisor on the actual compatible-root algebra.
The quotient presentation `tameRootAlgebra` is the displayed filtered colimit presentation:
its equations impose all root relations and all divisibility transition identifications.
Source: direct-images paragraph (3), supplied-root morphism extension
(blueprint: lem-sfb-root-tower-lisse-morphism-extension). -/
def parameterRootOpen (p : ℕ) {R : Type u} [CommRing R] {r : ℕ} (t : Fin r → R) :
    (Spec (CommRingCat.of (tameRootAlgebra p t))).Opens :=
  PrimeSpectrum.basicOpen (algebraMap R (tameRootAlgebra p t) (∏ i, t i))

/-- The projection from the full parameter-root tower to its affine input chart.
Source: direct-images paragraph (3), supplied-root morphism extension
(blueprint: lem-sfb-root-tower-lisse-morphism-extension). -/
def parameterRootProjection (p : ℕ) {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) : Spec (CommRingCat.of (tameRootAlgebra p t)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (tameRootAlgebra p t)))

/-- The canonical coefficient pullback comparison for a fibre-product square, formed
from the actual module inverse-image composition isomorphisms and the projection equation.
Source: direct-images paragraph (3), base-change naturality
(blueprint: lem-sfb-root-tower-lisse-morphism-extension). -/
def rootTowerRestrictionComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {T V Z : Scheme.{u}} (j : V ⟶ T) (g : Z ⟶ T) :
    CondensedRing.upperStar Λ g ⋙ CondensedRing.upperStar Λ (pullback.fst g j) ≅
      CondensedRing.upperStar Λ j ⋙ CondensedRing.upperStar Λ (pullback.snd g j) :=
  (CondensedRing.upperStarComp Λ (pullback.fst g j) g).symm ≪≫
    eqToIso (congrArg (CondensedRing.upperStar Λ) (pullback.condition (f := g) (g := j))) ≪≫
    CondensedRing.upperStarComp Λ (pullback.snd g j) j

/-- Restriction is bijective on Hom between supplied lisse modules, compatibly with
pro-etale base change of the affine input. The components are exactly the zero loci of
the specified parameters; the empty parameter tuple and empty chart are allowed.
Source: direct-images paragraph (3), supplied-root morphism extension
(blueprint: lem-sfb-root-tower-lisse-morphism-extension).

Proof: (1) `lem-sfb-snc-root-limit-normal-charts` gives normality and injectivity of
multiplication by the parameter product on every affine weakly etale tower chart Q.
(2) Localization Q -> Q[1/s] is injective. Every idempotent of Q[1/s] is integral in
the total fraction ring, hence belongs uniquely to Q by
`lem-weil-pbc-normal-ring-integrally-closed-total`. The Spec clopen/idempotent
bijection identifies this with bijectivity of restriction of clopens.
(3) Both affine schemes are qcqs and spectral. Apply
`lem-sfb-spectral-clopen-component-homeomorphism` to identify their component spaces,
with its normalization on the component quotient maps.
(4) The ultrametric norm makes E totally disconnected. Continuous E-valued functions
factor through the component quotient; transport across that homeomorphism gives unique
continuous extensions. Uniqueness makes this natural on affine site objects.
(5) `lem-weil-pbc-condensed-field-continuous-realization` identifies actual pulled-back
C_E coefficient sections and their restriction with these continuous functions.
(6) Refine a common lisse trivializing cover by affines. A map between finite free
modules is a matrix of coefficient sections. Extend every entry uniquely by (5);
empty matrices include rank zero.
(7) On affine refinements of overlaps, uniqueness of each extended entry makes the
local maps agree. The sheaf axiom glues a unique global linear map. This proves both
surjectivity and injectivity on Hom.
(8) The root presentation commutes with base change, since tensor products preserve
its generators, relations and colimit. Cartesian coefficients and the canonical
pullback composition comparison identify the two restrictions of a pulled-back map.
Apply the same bijectivity on the new chart, locally if necessary, to obtain the
base-changed Hom bijection. Its compatibility is precisely the displayed square.
For r=0 the product is 1 and the open is the entire tower. For an empty chart all
Hom sets are singletons. No extension of objects is constructed. -/
theorem rootTower_lisse_restriction_bijective
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [CharP k p]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (Y : Scheme.{u}) (y : Y ⟶ Spec (.of k)) [LocallyOfFiniteType y] [QuasiCompact y]
    [IsSeparated y]
    (hY : IsRegularScheme Y)
    (A : Type u) [CommRing A] (b : Spec (.of A) ⟶ Y) [Etale b]
    (r : ℕ) (t : Fin r → A) (H : (Spec (.of A)).IdealSheafData)
    (hH : IsStrictNormalCrossingsBoundary H)
    (hproduct : H = Scheme.IdealSheafData.ofIdealTop
      (Ideal.span {(Scheme.ΓSpecIso (CommRingCat.of A)).inv (∏ i, t i)}))
    (hbranches : Set.range (fun i : Fin r ↦ PrimeSpectrum.zeroLocus ({t i} : Set A)) =
      Set.image (Set.image Subtype.val) (irreducibleComponents (H.support : Set (Spec (.of A)))))
    (R : Type u) [CommRing R] (a : A →+* R)
    [WeaklyEtale (Spec.map (CommRingCat.ofHom a))]
    (N N' : Mod
      (Sheaf (Scheme.ProEt.topology (Spec (.of (tameRootAlgebra p (fun i ↦ a (t i))))))
        Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj E)
        (Spec (.of (tameRootAlgebra p (fun i ↦ a (t i)))))))
    (hN : IsLisseCoefficientModule (Profinite.continuousCoefficientRingObj E) N)
    (hN' : IsLisseCoefficientModule (Profinite.continuousCoefficientRingObj E) N') :
    Function.Bijective
      (fun f : N ⟶ N' ↦ (CondensedRing.upperStar (Profinite.continuousCoefficientRingObj E)
        (parameterRootOpen p (fun i ↦ a (t i))).ι).map f) ∧
    ∀ (U' : Scheme.{u}) (v : U' ⟶ Spec (.of R)) [WeaklyEtale v],
      Function.Bijective (fun f :
        (CondensedRing.upperStar (Profinite.continuousCoefficientRingObj E)
          (pullback.fst (parameterRootProjection p (fun i ↦ a (t i))) v)).obj N ⟶
        (CondensedRing.upperStar (Profinite.continuousCoefficientRingObj E)
          (pullback.fst (parameterRootProjection p (fun i ↦ a (t i))) v)).obj N' ↦
        (CondensedRing.upperStar (Profinite.continuousCoefficientRingObj E)
          (pullback.fst
            (pullback.fst (parameterRootProjection p (fun i ↦ a (t i))) v)
            (parameterRootOpen p (fun i ↦ a (t i))).ι)).map f) ∧
      ∀ f : N ⟶ N',
        (CondensedRing.upperStar (Profinite.continuousCoefficientRingObj E)
          (pullback.fst
            (pullback.fst (parameterRootProjection p (fun i ↦ a (t i))) v)
            (parameterRootOpen p (fun i ↦ a (t i))).ι)).map
          ((CondensedRing.upperStar (Profinite.continuousCoefficientRingObj E)
            (pullback.fst (parameterRootProjection p (fun i ↦ a (t i))) v)).map f) ≫
          (rootTowerRestrictionComparison (Profinite.continuousCoefficientRingObj E)
            (parameterRootOpen p (fun i ↦ a (t i))).ι
            (pullback.fst (parameterRootProjection p (fun i ↦ a (t i))) v)).hom.app N' =
        (rootTowerRestrictionComparison (Profinite.continuousCoefficientRingObj E)
          (parameterRootOpen p (fun i ↦ a (t i))).ι
          (pullback.fst (parameterRootProjection p (fun i ↦ a (t i))) v)).hom.app N ≫
          (CondensedRing.upperStar (Profinite.continuousCoefficientRingObj E)
            (pullback.snd
              (pullback.fst (parameterRootProjection p (fun i ↦ a (t i))) v)
              (parameterRootOpen p (fun i ↦ a (t i))).ι)).map
            ((CondensedRing.upperStar (Profinite.continuousCoefficientRingObj E)
              (parameterRootOpen p (fun i ↦ a (t i))).ι).map f) := by
  sorry

end AlgebraicGeometry.ProEtale
