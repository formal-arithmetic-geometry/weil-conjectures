/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/
module

public import Sheaf.AlgebraicGeometry.SchemeCharacteristic
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.AbsoluteFrobeniusSite
public import Sheaf.AlgebraicGeometry.FrobeniusTrivializationPullback
public import Sheaf.SecSmoothPurity.DirectImageScalarExchange

/-!
# Absolute Frobenius and finite coefficient change

Source: main-20261015 blueprint, six-functors-basics,
`sk-prop-sf-rf-shriek-preservation/lem-trf-absolute-frobenius-site.proof.md`, final
paragraph; Stacks Tag 0F6W (blueprint: lem-trf-absolute-frobenius-coefficient-naturality).

The scalar extension is the left adjoint of exact derived restriction, hence the ordinary
uncompleted derived tensor product. Its pullback comparison is the scalar-adjunction mate
of the section-normalized restriction comparison. This specifies the transported comparison
without choosing an arbitrary natural isomorphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- Exact derived descent of the relative-Frobenius-normalized module trivialization.
The dependency fixes the site isomorphism by its two projections, then fixes its module
mate by the section-unit equation; the choice therefore takes a uniquely specified map.
Source: Stacks 0F6W; final paragraph of lem-trf-absolute-frobenius-site.proof.md
(blueprint: lem-trf-absolute-frobenius-coefficient-naturality). -/
def coefficientFrobeniusTrivialization (p : ℕ) (hp : p.Prime)
    (X : Scheme.{u}) (hX : X.IsCharacteristic p)
    (A : Type u) [CommRing A] [Finite A] (b : ℕ) :
    proEtaleConstantRingDerivedPullback A (X.iterateFrobenius hp (hX.2 ⊤) b) ≅
      𝟭 (proEtaleDerivedCategory X A) :=
  proEtaleFrobeniusDerivedIso A
    ((absoluteFrobenius_proEtale_trivialization_pullback p hp A).choose_spec.2.choose_spec.2.choose
      X hX b)

/-- The canonical absolute-Frobenius trivialization commutes with every finite unital
coefficient change on the ordinary unbounded derived category, at every nonnegative iterate.

Source: main-20261015 blueprint, final paragraph of
lem-trf-absolute-frobenius-site.proof.md; geometric input Stacks 0F6W
(blueprint: lem-trf-absolute-frobenius-coefficient-naturality).

Proof (the three steps of the DAG):
1. For b=0 the relative-Frobenius site map is identity under identity base change. Its
module mate and derived descent are the identity-pullback comparison. The scalar mate for
identity pullback is identity under these identifications, proving the zero case.
2. For b=1 use the relative Frobenius r_V=(F_V,v) on every weakly etale object. Its
section maps give the normalized exact module inverse-image trivialization of
lem-pur-frobenius-trivialization-pullback. Choose a K-flat resolution of K using
lem-pur-derived-change-of-rings. The inverse coefficient comparison is the transported
comparison of det-prop-scalar-six-pullback (1), through the two finite-discrete constant
ring identifications. On a pure tensor x tensor b, each composite applies restriction
along r_V to x and leaves b unchanged. Tensor balancing gives equality on the tensor
complex; the maps commute with differentials. Exact termwise descent and localization
at quasi-isomorphisms give the desired equality for K, with no flatness assumption.
3. For b+1 use the addition law for the canonical trivializations in
lem-trf-absolute-frobenius-site and lem-pur-frobenius-trivialization-pullback, and the
composition law of det-prop-scalar-six-pullback (1). Whisker the one-step and b-step
commuting squares by the relevant pullbacks and paste them. Naturality of the one-step
trivialization identifies the outer rectangle with the desired b+1 square, after the
canonical composition comparisons. Induction proves the equation for all b. The only
resolutions used are K-flat, so neither B nor K needs flatness or finite Tor amplitude. -/
theorem absoluteFrobenius_coefficient_naturality (p : ℕ) (hp : p.Prime)
    (X : Scheme.{u}) (hX : X.IsCharacteristic p)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    (b : ℕ) (K : proEtaleDerivedCategory X A) :
    (AlgebraicGeometry.ProEtale.directImageScalarPullbackIso φ
      (X.iterateFrobenius hp (hX.2 ⊤) b)).hom.app K ≫
        (AlgebraicGeometry.ProEtale.directImageScalarExtension φ X).map
          ((coefficientFrobeniusTrivialization p hp X hX A b).hom.app K) =
      (coefficientFrobeniusTrivialization p hp X hX B b).hom.app
        ((AlgebraicGeometry.ProEtale.directImageScalarExtension φ X).obj K) := by
  sorry

end AlgebraicGeometry.Scheme
