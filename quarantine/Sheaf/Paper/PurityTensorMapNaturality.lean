/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.Paper.SmoothPurityMap
public import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.Paper.SfPreservationClass
import Sheaf.Paper.PullbackTorAmplitude
import Sheaf.Paper.FiniteCoefficientTensorCtf
import Sheaf.Algebra.Homology.RingedDerivedTensorNative
import Sheaf.Paper.CompactSupportProjectionFormula
import Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor

/-! # Naturality of the projection-and-counit tensor transpose

Source: blueprint main-20261015, smooth purity,
prop-pur-smooth-purity-naturality-cover.proof.md, first sentence
(blueprint: lem-pur-tensor-map-naturality).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

/-- The displayed inverse-projection/counit input in ordinary etale coordinates.
This is the inverse adjunction image of the already specified tensor mate, including
its source symmetry and the canonical identification of the degree-zero unit. Expanding
smoothPurityEtaleTheta and projectionTensorMap gives exactly F(symmetry), PF inverse,
counit tensor identity and the left unitor. No arrow is chosen from an existence result.
Source: main-20261015, def-pur-co-smoothness clause 2 and the displayed a_K in
lem-pur-tensor-map-naturality (blueprint: lem-pur-tensor-map-naturality). -/
noncomputable def purityTensorCoefficientInput
    (A : Type (u + 1)) [CommRing A] [Finite A] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f]
    (K₀ : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj
      (((Etale.ordinaryFiniteTensor A X).obj
        ((Etale.ordinaryFinitePullback A f).obj K₀)).obj
          ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} A) f).obj
            (Etale.ordinaryFiniteUnit A Y))) ⟶ K₀ :=
  ((Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ K₀).symm
    (smoothPurityEtaleTheta A f K₀)

/-- The coefficient square after the canonical site comparison. The normalized compact-
support comparison identifies this with u composed with a_K equals a_K' composed with
F(m tensor identity). This is an equality of pro-etale derived morphisms, expressed in
etale-origin coordinates exactly as in the recorded cohomological-smoothness definition.
Source: main-20261015, lem-pur-tensor-map-naturality, second displayed equation
(blueprint: lem-pur-tensor-map-naturality). -/
def PurityTensorCoefficientSquare
    (A : Type (u + 1)) [CommRing A] [Finite A] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f]
    (K₀ K₀' : _root_.DerivedCategory
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) (u₀ : K₀ ⟶ K₀') : Prop :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
      (purityTensorCoefficientInput A f K₀ ≫ u₀) =
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
      ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
        (((Etale.ordinaryFiniteTensor A X).map
          ((Etale.ordinaryFinitePullback A f).map u₀)).app
            ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} A) f).obj
              (Etale.ordinaryFiniteUnit A Y))) ≫ purityTensorCoefficientInput A f K₀')

/-- Naturality of the specified tensor mate and its equivalent coefficient square.
K and K' are arbitrary original pro-etale Dctf objects. Their etale representatives,
representing isomorphisms and a compatible lifted arrow are coordinates, not restrictions:
finite constructible complexes have etale origins and comparison is fully faithful there.
The equation is asserted for every such presentation. The compactification is supplied
by the finite-type geometry; no compactification hypothesis is added.
Source: main-20261015, prop-pur-smooth-purity-naturality-cover.proof.md, first sentence
(blueprint: lem-pur-tensor-map-naturality).
Proof:
1. Put Omega = H(A_Y), M = Lf* K and T = M tensor Omega. By
thm-sf-preservation-class the coefficient unit and Omega are bounded constructible.
By lem-sf-pullback-tor-amplitude M has finite Tor amplitude, and lem-sf-tensor-ctf(i)
makes T bounded constructible. Thus the stated bounded etale-origin Hom bijection applies.
2. Use lem-sf-ringed-derived-native-tensor to identify the K-flat tensor symmetry and
unitors with the natural monoidal constraints. Its bifunctoriality gives interchange.
By fix-prop-projection-formula the projection is natural in K. Move m past symmetry,
then past the inverse projection, by cancelling its two invertible components.
3. Move u past counit tensor identity by tensor interchange, then past the left unitor
by its naturality. Substitution in a_K gives a_K followed by u equals F(m tensor identity)
followed by a_K'. This is PurityTensorCoefficientSquare in comparison coordinates.
4. Apply the single natural Hom bijection of thm-sf-ambient-adjoint-class(2) to that
square. Target naturality gives theta_K followed by H(u); source naturality gives
(m tensor identity) followed by theta_K'. Its injectivity gives the converse.
The canonical comparisons used in smoothPurityTheta transport this calculation to the
original K and K'. No orientation or smooth purity isomorphism is used. -/
theorem purityTensorMap_naturality
    (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (K K' : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)))
    (_hK : ProEtale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} P.Coefficient) Y K)
    (_hK' : ProEtale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} P.Coefficient) Y K')
    (u : K ⟶ K')
    (K₀ K₀' : _root_.DerivedCategory
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (e : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj K₀ ≅ K)
    (e' : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj K₀' ≅ K')
    (u₀ : K₀ ⟶ K₀')
    (_hu : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.map u₀ ≫ e'.hom = e.hom ≫ u) :
    @smoothPurityTheta P X Y f
        (P.finiteComparedCompactification f (Y ↘ Spec (.of P.field.k))).hasCompactification
        K K₀ e ≫
      (@smoothPurityExceptional P X Y f
        (P.finiteComparedCompactification f (Y ↘ Spec (.of P.field.k))).hasCompactification).map
        u =
      ((smoothPurityTensor P.Coefficient X).map
        ((P.smoothPurityPullback f).map u)).app
          (@diagonalDualizing P X Y f
            (P.finiteComparedCompactification f
              (Y ↘ Spec (.of P.field.k))).hasCompactification) ≫
        @smoothPurityTheta P X Y f
          (P.finiteComparedCompactification f (Y ↘ Spec (.of P.field.k))).hasCompactification
          K' K₀' e' ∧
    @PurityTensorCoefficientSquare P.Coefficient _ _ X Y f
      (P.finiteComparedCompactification f (Y ↘ Spec (.of P.field.k))).hasCompactification
      K₀ K₀' u₀ := by
  sorry

end WeilConjectures.PurityFiniteSetting
