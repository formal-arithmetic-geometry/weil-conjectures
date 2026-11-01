/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.Sf.SfCommonStageDirectImage
import WeilConjectures.SmoothPurity.Sf.SfRationalDirectImageCoefficientCompatibility
import all WeilConjectures.SmoothPurity.Sf.SfRationalDirectImageAdjunction
import all WeilConjectures.SmoothPurity.Sf.SfCommonStageDirectImage

/-! # Derived direct image and the common-stage compatibility interface

The ordinary ambient direct image of the current blueprint is the generic
`CategoryTheory.Functor.rightDerivedFunctor` applied to
`AlgebraicGeometry.ProEtale.CondensedRing.lowerStar`. The public import of
`ModuleObject.Derived.UpperLowerStar` supplies this construction for every commutative
condensed ring and every scheme morphism, its K-injective computation, the exact
restriction-of-scalars factorization `CondensedRing.rightDerivedLowerStarIso`, and
`CondensedRing.derivedUpperStarLowerStarAdjunction`.

Source: current blueprint sec-proetale-coefficients/sk-prop-sf-open-closed-triangle,
Derived direct image (blueprint: def-weil-derived-direct-image).
No finite-type, boundedness, constructibility or invertibility hypothesis is imposed
on that ambient construction. Integral reconstruction is a consequence for derived-complete
objects, not its definition.

The declarations below retain the earlier common-stage constructible interface for its
existing consumers. They concern a different category and do not define the ambient
ordinary direct image. This interface applies to arbitrary finite-type schemes over k,
without requiring a specified finite-field model. Its sources are Bhatt--Scholze
6.7.2, 6.8.14 and 6.8.15.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (k : Type u) [Field k] (hl : IsUnit (l : k))
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

include k hl in
/-- The common-stage inverse image has the actual direct image as right adjoint.
Source: BS 6.7.2, 6.8.14--6.8.15; blueprint derived-direct-image convention
(blueprint: def-weil-derived-direct-image).
Proof: restrict the integral reduction/limit adjunction using
sfIntegralPullbackLinearAdjunction. Its right functor is the ordinary direct-image
reconstruction of the finite reductions, hence the SfIntegralDirectImage object.
Localize its coefficient-linear Hom bijection, unit and counit at the uniformizer.
The normalized coefficient comparison theorem supplies invertible right mates
for these finite rational adjunctions. The mate counit equation forces the
right-family coherence and unit compatibility. Descend the resulting unit and
counit using the stage-system functors. The finite-stage
triangle identities descend. This constructs a right adjoint to the recorded
commonStageDerivedPullback, with precisely the same canonical adjunction under
its unique adjunction-compatible identification. No descent model over k_0 is needed. -/
theorem geometricCommonStagePull_isLeftAdjoint :
    (commonStageDerivedPullback l Ω f).IsLeftAdjoint := by
  obtain ⟨L, ⟨hΦ, hβ, hm⟩, _⟩ :=
    sfRationalDirectImageCoefficientCompatibility l Ω f
  have hpoint (E : AlgebraicallyClosedCoefficients.Index l Ω) :
      (L.Φ E).IsLeftAdjoint := by
    rw [hΦ]
    exact rationalSystemPullback_isLeftAdjoint l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) k hl f
  let R E := @Functor.rightAdjoint _ _ _ _ (L.Φ E) (hpoint E)
  let a E : L.Φ E ⊣ R E := @Adjunction.ofIsLeftAdjoint _ _ _ _ (L.Φ E) (hpoint E)
  let β {E F : AlgebraicallyClosedCoefficients.Index l Ω} (h : E ≤ F) :
      R E ⋙ (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).T h ≅
        (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T h ⋙ R F := by
    let := hm R a h
    exact asIso ((mateEquiv (a E) (a F) (TwoSquare.mk _ _ _ _ (L.β h).inv)).natTrans)
  have hmate {E F : AlgebraicallyClosedCoefficients.Index l Ω} (h : E ≤ F)
      (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω X E) :
      (L.Φ F).map ((β h).hom.app K) ≫
          (a F).counit.app
            (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T h).obj K) =
        (L.β h).inv.app ((R E).obj K) ≫
          ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T h).map
            ((a E).counit.app K) :=
    mateEquiv_counit (a E) (a F) (TwoSquare.mk _ _ _ _ (L.β h).inv) K
  exact rationalStageAdjunction_descends l Ω f L
    (DirectImageAdjunction.mateFamily L R a β hmate) hΦ hβ a
    (DirectImageAdjunction.mateFamilyUnit L R a β hmate)
    (DirectImageAdjunction.mateFamilyCounit L R a β hmate) (fun _ ↦ rfl) (fun _ ↦ rfl)

/-- The ordinary common-stage direct image, specified by its adjunction universal
property. The choice is unique up to the unique adjunction-compatible isomorphism.
Source: BS 6.8.14--6.8.15 (blueprint: def-weil-derived-direct-image). -/
def geometricCommonStageDirectImage :
    generalAlgebraicallyClosedConstructibleCategory l Ω X ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω Y :=
  @Functor.rightAdjoint _ _ _ _ (commonStageDerivedPullback l Ω f)
    (geometricCommonStagePull_isLeftAdjoint l Ω k hl f)

/-- The unit and counit specifying the common-stage direct-image universal property.
Its comparison with the finite-stage construction is the unique compatible adjoint
comparison, so it retains the localized ordinary completed Hom bijections.
Source: BS 6.8.14--6.8.15 (blueprint: def-weil-derived-direct-image). -/
def geometricCommonStageAdjunction :
    commonStageDerivedPullback l Ω f ⊣ geometricCommonStageDirectImage l Ω k hl f :=
  @Adjunction.ofIsLeftAdjoint _ _ _ _ (commonStageDerivedPullback l Ω f)
    (geometricCommonStagePull_isLeftAdjoint l Ω k hl f)

end WeilConjectures
