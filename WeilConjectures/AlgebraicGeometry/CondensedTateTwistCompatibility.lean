/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
public import WeilConjectures.AlgebraicGeometry.InternalSignedTateTwist
public import WeilConjectures.SixFunctors.RingedDerivedMonoidalComparisons
public import WeilConjectures.AlgebraicGeometry.CondensedDerivedTensorComparisonSupplement
public import WeilConjectures.SecSmoothPurity.TransportGeometry
import WeilConjectures.AlgebraicGeometry.RootsOfUnityInverseImageIso
import WeilConjectures.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
import WeilConjectures.AlgebraicGeometry.PurInverseImageTensorHom
import WeilConjectures.Algebra.Homology.SignedLineDerivedBaseChange
import WeilConjectures.AlgebraicGeometry.InvertibleTensorScalarExtension
import WeilConjectures.AlgebraicGeometry.CartesianCoefficients
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCoefficientTerminalSupplement

/-! # Tate twists and finite scalar extension for condensed strict Weil complexes

Source: latest blueprint, sec-purity-real-sheaves/sk-r-real-linear,
lem-wf-tate-twist-compatibility and its proof
(blueprint: lem-wf-tate-twist-compatibility).

The existing root-normalized signed lines and their Weil isomorphisms are used verbatim.
The main statement specifies the underlying objects, arrows and Weil isomorphisms of
both functors, as well as their natural commutation isomorphism on the actual Dctf.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.StrictWeil

open PurityTransport

/-- The canonical c : P_F B to B P_E, using derived composition and the exact-pullback
comparison, rather than a freely chosen commuting isomorphism.
Source: latest blueprint, coefficient square (blueprint: lem-wf-tate-twist-compatibility). -/
def finiteScalarFrobenius (ell : ℕ) [Fact ell.Prime]
    {E F : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ F)
    {X : Scheme.{u}} (g : X ≅ X) :
    finiteCoefficientDerivedExtension X ell h ⋙ action ((Coefficient.rational F).obj ell) g ≅
      action ((Coefficient.rational E).obj ell) g ⋙ finiteCoefficientDerivedExtension X ell h :=
  Functor.isoWhiskerLeft (finiteCoefficientDerivedExtension X ell h)
      (leftDerivedUpperStarIsoMapDerivedCategory ((Coefficient.rational F).obj ell) g.hom).symm
    ≪≫ (derivedPullIso (Profinite.padicSubfieldRingObjMap ell h) g.hom).symm
    ≪≫ Functor.isoWhiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory ((Coefficient.rational E).obj ell) g.hom)
      (finiteCoefficientDerivedExtension X ell h)

/-- The normalized Tate twist is tensor with the signed degree-zero line, with Weil
arrow (phi tensor tau_m) after the canonical inverse tensorator, and sends h to h tensor 1.
Finite scalar extension, with its specified coefficient-composition Weil arrow, commutes
naturally with this twist. All carriers lie in the recorded bounded constructible
finite-Tor full subcategory of the ordinary derived category.

Source: latest blueprint, lem-wf-tate-twist-compatibility, all displayed formulas
(blueprint: lem-wf-tate-twist-compatibility).

Proof: pull back roots of unity along geometric Frobenius and commute the root maps
with the transition powers. Pass through the specified inverse limits, localization
and finite-subextension colimit. For finite rings use the constant-to-condensed
comparison and its terminal-section normalization. This is exactly the existing
`tatePull` and `tateDatum`: the unit at zero, tensor powers at positive integers,
and the evaluation-compatible dual at negative integers. The canonical monoidal
comparison gives `tensorDatum`; bifunctoriality gives the asserted morphism formula.
For E contained in F, on a common compatible-root cover send a tensor (e x) to e(ax).
Changes of root frame multiply both expressions by the same unit, so the line
comparison glues and commutes with root pullback. Extend it through positive powers
and evaluation duals to b_m : B(E_X(m)) isomorphic to F_X(m). The coefficient square
commutes by naturality of pullback from the point, so the canonical derived comparison
`finiteScalarFrobenius` is monoidal and satisfies the Frobenius square for b_m.
Compose the scalar tensorator with 1 tensor b_m. Monoidality and that square give a
strict Weil isomorphism; naturality gives the functor isomorphism below. Finally the
signed lines are locally free of rank one, hence twisting preserves the same strata
and Tor intervals. F_X is finite free over E_X; extension is exact, extends each
finite presentation on the same strata, and preserves each Tor interval by derived
tensor associativity. Thus the functors and comparison restrict to Dctf.

The existential functors below are constrained on every carrier, Weil arrow and
morphism; they are not arbitrary lifts of scalar extension or of tensor product. -/
theorem tateTwistCompatibility (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀))) :
    let X := pullback X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
    let g := modelFrobenius D X₀
    let π : X ⟶ Spec (.of D.k) :=
      pullback.snd X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
    letI : ∀ x : X, Invertible (ell : X.residueField x) := fun x ↦
      (show IsUnit (ell : X.residueField x) by
        simpa only [map_natCast] using
          (primeUnit D ell hEll).map (π.residueFieldAlgebraMap x)).invertible
    ∃ twist : (c : Coefficient ell) → ℤ →
        (Complex (c.obj ell) g ⥤ Complex (c.obj ell) g),
      (∀ (c : Coefficient ell) (m : ℤ) (W : Complex (c.obj ell) g),
        ((twist c m).obj W).carrier.obj =
          W.carrier.obj ⊗ derivedTateLine ell c X m ∧
        HEq ((ObjectProperty.ι _).mapIso ((twist c m).obj W).str)
          (tensorDatum (c.obj ell) g ((ObjectProperty.ι _).mapIso W.str)
            (tateDatum ell c g m))) ∧
      (∀ (c : Coefficient ell) (m : ℤ) (W V : Complex (c.obj ell) g) (h : W ⟶ V),
        HEq (((twist c m).map h).hom.f.hom)
          (h.hom.f.hom ⊗ₘ 𝟙 (derivedTateLine ell c X m))) ∧
      (∀ (E F : PadicAlgCl.FiniteIntermediateField ell) (h : E ≤ F),
        ∃ scalar : Complex ((Coefficient.rational E).obj ell) g ⥤
            Complex ((Coefficient.rational F).obj ell) g,
          (∀ W : Complex ((Coefficient.rational E).obj ell) g,
            (scalar.obj W).carrier.obj =
              (finiteCoefficientDerivedExtension X ell h).obj W.carrier.obj ∧
            HEq ((ObjectProperty.ι _).mapIso (scalar.obj W).str)
              ((finiteScalarFrobenius ell h g).app W.carrier.obj ≪≫
                (finiteCoefficientDerivedExtension X ell h).mapIso
                  ((ObjectProperty.ι _).mapIso W.str))) ∧
          (∀ (W V : Complex ((Coefficient.rational E).obj ell) g) (f : W ⟶ V),
            HEq ((scalar.map f).hom.f.hom)
              ((finiteCoefficientDerivedExtension X ell h).map f.hom.f.hom)) ∧
          (∀ m : ℤ, Nonempty
            (twist (.rational E) m ⋙ scalar ≅ scalar ⋙ twist (.rational F) m))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.StrictWeil
