/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q82
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleAdjunction
public import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso
import Mathlib.CategoryTheory.Localization.Predicate
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.CategoryTheory.RingedSiteModules

/-!
# Identity normalization of ordinary pro-etale derived pullback

Source: Stacks Project, Tag 09A5, identity specialization of `section-morphism`;
the final sentence of the blueprint proof of `lem-pur-diagonal-base-change`
(blueprint: lem-pur-proetale-derived-pullback-identity).

The coprojection formula fixes the module comparison before scalar extension.
The tensor formulas fix its scalar-transport identification. The final equality
fixes the derived comparison on every cochain representative.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme

/-- The inverse-image module with its action transported by the inverse of the specified
constant-ring comparison. Source: Stacks, Tags 09A5 and 03D2
(blueprint: lem-pur-proetale-derived-pullback-identity). -/
abbrev proEtaleIdentityTransportedInverseImage (X : Scheme.{u})
    (A : Type u) [CommRing A] :=
  proEtaleModuleInverseImage (𝟙 X) (proEtaleConstantRing X A) ⋙
    SheafOfModules.restrictScalars ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (proEtaleConstantRingComparison (𝟙 X) A).inv)

set_option backward.isDefEq.respectTransparency.types false in
/-- The distinguished identity coprojection, followed by restriction along
`U → U ×[X] X`. This is the inverse of the objectwise identity comparison before
extension of scalars. Source: Stacks, Tags 09A5 and 00WX
(blueprint: lem-pur-proetale-derived-pullback-identity). -/
def proEtaleIdentityModuleCoprojection (X : Scheme.{u}) (A : Type u) [CommRing A]
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) (U : X.ProEt)
    (m : M.val.obj (op U)) :
    ((proEtaleModuleInverseImage (𝟙 X) (proEtaleConstantRing X A)).obj M).val.obj
      (op U) :=
  ((proEtaleModuleInverseImage (𝟙 X) (proEtaleConstantRing X A)).obj M).val.map
    ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv.app U).op
    (((SheafOfModules.pullbackPushforwardAdjunction.{u + 1}
      (proEtaleModelRingUnit (𝟙 X) (proEtaleConstantRing X A))).unit.app
        ((proEtaleModuleToModel ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (proEtaleConstantRing X A))).obj M)).val.app
              (AsSmall.up.op.obj (op U)) m)

/-- The sheafification-unit image of `m ⊗ a` in the specified tensor pullback.
The published construction writes the scalar factor first. Source: Stacks, Tag 03EK
(blueprint: lem-pur-proetale-derived-pullback-identity). -/
def proEtaleIdentityPullbackTmul (X : Scheme.{u}) (A : Type u) [CommRing A]
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) (U : X.ProEtᵒᵖ)
    (m : ((proEtaleModuleInverseImage (𝟙 X) (proEtaleConstantRing X A)).obj M).val.obj U)
    (a : (proEtaleConstantRing X A).obj.obj U) :
    ((proEtaleConstantRingPullback.{u} A (𝟙 X)).obj M).val.obj U :=
  letI := WeilConjectures.integralCoefficientAbSheafify.{u, u} X
  letI := WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} X
  letI := SheafOfModules.siteTensor_identity_locallyInjective
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X A))
  letI := SheafOfModules.siteTensor_identity_locallySurjective
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X A))
  (((PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
    (J := ProEt.topology X)
    (R := (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X A))
    (𝟙 _)).unit.app
      (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
        (J := ProEt.topology X) (proEtaleCoefficientInverseImageMap (𝟙 X) A)
        ((proEtaleModuleInverseImage (𝟙 X) (proEtaleConstantRing X A)).obj M))).app U)
    (a ⊗ₜ[((proEtaleSheafInverseImage (𝟙 X) CommRingCat.{u + 1}).obj
      (proEtaleConstantRing X A)).obj.obj U,
        ((proEtaleCoefficientInverseImageMap (𝟙 X) A).hom.app U).hom] m)

/-- The existing unbounded localization in the precise coefficient universes of the
published pro-etale operations. Only existing sheafification instances are instantiated;
the functor is Mathlib's Q. Source: Stacks, Tag 05RU
(blueprint: lem-pur-proetale-derived-pullback-identity). -/
abbrev proEtaleIdentityLocalization (X : Scheme.{u}) (A : Type u) [CommRing A] :
    CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ ⥤
      proEtaleDerivedCategory X A :=
  letI := WeilConjectures.integralCoefficientAbSheafify.{u, u} X
  letI := WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} X
  DerivedCategory.Q

set_option backward.isDefEq.respectTransparency.types false in
/-- The specified identity comparison equals the canonical coefficient map, is linear
after scalar transport, and descends termwise to ordinary unbounded derived pullback.
Source: Stacks, Tag 09A5; blueprint diagonal base-change proof, final sentence
(blueprint: lem-pur-proetale-derived-pullback-identity).

Proof: (1) The distinguished comma object `(U, delta_U)` is initial before taking
opposites: an arrow to `(V, phi)` is forced to be the variable-factor projection of phi.
Its coprojection therefore identifies the inverse-image colimit with the original
sections. These identifications respect restrictions and algebraic operations;
sheafification leaves the already sheaf-valued result unchanged. This is the normalized
comparison of lem-weil-proetale-isomorphism-inverse-image.
(2) The adjoint of its coefficient component sends each constant section to itself.
The sheafification universal property identifies this adjoint with rho, hence identifies
the component with the specified c (def-weil-proetale-inverse-image).
(3) Naturality with products and the action gives e(t m) = e(t)e(m). Transporting the
source action through c inverse makes this comparison and its inverse linear. Its inverse
is the distinguished module coprojection displayed above, by the module Kan-extension
adjunction on the small model. Naturality gives the module natural isomorphism eM.
(4) Apply lem-weil-sheaf-scalar-extension-ring-iso: the scalar-transport comparison sends
m tensor a to c inverse(a)m and sends m back to m tensor 1. Composing with eM gives alpha,
with the two displayed tensor formulas, naturally in the module.
(5) Alpha identifies pullback with the identity, so pullback is additive and exact.
Its termwise maps commute with differentials by naturality, giving the complex
isomorphism b (lem-weil-pbc-exact-functor-derived-factorization).
(6) The localization universal property descends b and its inverse to gamma. Its
representative formula is precisely the factorization followed by Q(b), as displayed
(lem-weil-pbc-localization-universal-property and def-weil-pbc-proetale-operations).
(7) No argument uses a point of X or a nonzero ring. For the zero ring all unitary
modules are zero; for the empty scheme the empty-cover sheaf axiom gives the same
degenerate comparisons. Both cases satisfy the formulas without extra hypotheses. -/
theorem proEtaleDerivedPullback_identity (X : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A] :
    ∃ e : proEtaleSheafInverseImage (𝟙 X) CommRingCat.{u + 1} ≅
        𝟭 (Sheaf (ProEt.topology X) CommRingCat.{u + 1}),
      (∀ (F : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (U : X.ProEt),
        (e.hom.app F).hom.app (op U) =
          ((proEtaleIsoInverseImageIdentification (𝟙 X) CommRingCat.{u + 1}).hom.app F).app
              (op U) ≫
            F.obj.map
              ((MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ X (𝟙 X) rfl).inv.app U).op) ∧
      e.hom.app (proEtaleConstantRing X A) = proEtaleCoefficientInverseImageMap (𝟙 X) A ∧
      ∃ eM : proEtaleIdentityTransportedInverseImage X A ≅
          𝟭 (proEtaleRingModules X (proEtaleConstantRing X A)),
        (∀ (M : proEtaleRingModules X (proEtaleConstantRing X A)) (U : X.ProEt)
          (m : M.val.obj (op U)),
          (eM.inv.app M).val.app (op U) m = proEtaleIdentityModuleCoprojection X A M U m) ∧
        ∃ alpha : proEtaleConstantRingPullback.{u} A (𝟙 X) ≅
            𝟭 (proEtaleRingModules X (proEtaleConstantRing X A)),
          (∀ (M : proEtaleRingModules X (proEtaleConstantRing X A)) (U : X.ProEtᵒᵖ)
            (m : ((proEtaleModuleInverseImage (𝟙 X) (proEtaleConstantRing X A)).obj M).val.obj U)
            (a : (proEtaleConstantRing X A).obj.obj U),
            (alpha.hom.app M).val.app U (proEtaleIdentityPullbackTmul X A M U m a) =
              a • (eM.hom.app M).val.app U m) ∧
          (∀ (M : proEtaleRingModules X (proEtaleConstantRing X A)) (U : X.ProEtᵒᵖ)
            (m : M.val.obj U),
            (alpha.inv.app M).val.app U m =
              proEtaleIdentityPullbackTmul X A M U ((eM.inv.app M).val.app U m) 1) ∧
          ∃ b : (proEtaleConstantRingPullback.{u} A (𝟙 X)).mapHomologicalComplex
                (ComplexShape.up ℤ) ≅
              𝟭 (CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ),
            (∀ (K : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ)
              (j : ℤ), (b.hom.app K).f j = alpha.hom.app (K.X j)) ∧
            ∃ gamma : proEtaleConstantRingDerivedPullback.{u} A (𝟙 X) ≅
                𝟭 (proEtaleDerivedCategory X A),
              ∀ K : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ,
                gamma.hom.app ((proEtaleIdentityLocalization X A).obj K) =
                  (proEtaleRingDerivedPullbackFactors (𝟙 X)
                    (proEtaleConstantRing X A) (proEtaleConstantRing X A)
                    (proEtaleConstantRingComparison (𝟙 X) A)).hom.app K ≫
                    (proEtaleIdentityLocalization X A).map (b.hom.app K) := by
  sorry

end AlgebraicGeometry.Scheme
