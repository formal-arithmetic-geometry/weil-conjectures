/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q154
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.PurityAffineLineOrientation
public import Sheaf.Paper.PurityRankOneLocalCalculation
import Sheaf.Paper.PurityAffineLineOrientationInjectivity

/-! # Uniqueness of the global affine-line orientation

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-a1,
prop-pur-affine-line-orientation-uniqueness and its six-step proof
(blueprint: prop-pur-affine-line-orientation-uniqueness).

## Main definitions

- `OrientationGeometricFamily`: the product of the actual supported fibre groups.
- `OrientationRestrictionData`: the published normalized charts and geometric transports.
- `orientationGeometricRestriction`: restriction of a derived morphism to that product.
- `orientationNormalizedFamily`: the family whose residues are all one.

## Main statement

- `affineLine_orientation_uniqueness`: restriction is injective and the normalized family
  has the global coordinate orientation as its unique preimage.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- The product over geometric k-points of the supported degree-two fibre groups.
The field universe is the scheme universe, as in the recorded orientation theorem;
there is no finite-type condition on a geometric point.
Source: blueprint displayed restriction map
(blueprint: prop-pur-affine-line-orientation-uniqueness). -/
abbrev OrientationGeometricFamily (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k)) :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra P.field.k Ω]
    (y : Spec (CommRingCat.of Ω) ⟶ Y)
    (_hy : y ≫ a = Spec.map (CommRingCat.ofHom (algebraMap P.field.k Ω))),
    P.gysinSupport h (Spec (CommRingCat.of Ω))

/-- Canonical support charts, kernel pullback transports and normalized fibre residues.
Every chart and transport is constrained by the published counit, edge and kernel-unit
formulas. The residue is A-linear and sends the fibre coordinate boundary to one,
independently of the global morphism. This packages existing constructions only.
Source: blueprint restriction map and thm-pur-rank-one-local-calculation normalization
(blueprint: prop-pur-affine-line-orientation-uniqueness). -/
structure OrientationRestrictionData (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k)) where
  chart : OrientationSupportData P h Y
  fibreChart : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra P.field.k Ω]
    (y : Spec (CommRingCat.of Ω) ⟶ Y)
    (_hy : y ≫ a = Spec.map (CommRingCat.ofHom (algebraMap P.field.k Ω))),
    OrientationSupportData P h (Spec (CommRingCat.of Ω))
  transport : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra P.field.k Ω]
    (y : Spec (CommRingCat.of Ω) ⟶ Y)
    (_hy : y ≫ a = Spec.map (CommRingCat.ofHom (algebraMap P.field.k Ω))),
    proEtaleSupportHomTransport P (zeroSection Y)
      (zeroSection (Spec (CommRingCat.of Ω))) (AffineSpace.map (ULift.{u} (Fin 1)) y)
  residue : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra P.field.k Ω]
    (y : Spec (CommRingCat.of Ω) ⟶ Y)
    (_hy : y ≫ a = Spec.map (CommRingCat.ofHom (algebraMap P.field.k Ω))),
    P.gysinSupport h (Spec (CommRingCat.of Ω)) ≅ ModuleCat.of P.Coefficient P.Coefficient
  residue_normalized : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra P.field.k Ω]
    (y : Spec (CommRingCat.of Ω) ⟶ Y)
    (hy : y ≫ a = Spec.map (CommRingCat.ofHom (algebraMap P.field.k Ω))),
    (residue Ω y hy).hom ((fibreChart Ω y hy).coordinateBoundary P h
      (Spec.map (CommRingCat.ofHom (algebraMap P.field.k Ω)))) = 1

/-- The displayed restriction: use the normalized global support chart, then the actual
supported pullback with canonical scalar-extended root-line coefficient map.
Source: blueprint proof step 4
(blueprint: prop-pur-affine-line-orientation-uniqueness). -/
def orientationGeometricRestriction (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {Y : Scheme.{u}}
    {a : Y ⟶ Spec (CommRingCat.of P.field.k)} (D : OrientationRestrictionData P h Y a)
    (m : P.derivedSheaf h Y false ⟶ P.gysinValue h Y) :
    P.OrientationGeometricFamily h Y a :=
  fun Ω _ _ _ y hy ↦ P.orientationSupportRestriction h y (D.transport Ω y hy)
    (D.chart.support.hom (P.gysinHomToSections h Y m))

/-- The actual supported family corresponding to one in every residue module.
Source: blueprint image and normalization clauses
(blueprint: prop-pur-affine-line-orientation-uniqueness). -/
def orientationNormalizedFamily (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {Y : Scheme.{u}}
    {a : Y ⟶ Spec (CommRingCat.of P.field.k)} (D : OrientationRestrictionData P h Y a) :
    P.OrientationGeometricFamily h Y a :=
  fun Ω _ _ _ y hy ↦ (D.residue Ω y hy).inv 1

/-- Geometric restriction on the displayed derived Hom group is injective; its image
contains the normalized all-ones family, with the coordinate Kummer orientation as
its unique preimage. All chart, transport and residue data are produced, not assumed.

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-a1,
prop-pur-affine-line-orientation-uniqueness, statement and six-step proof
(blueprint: prop-pur-affine-line-orientation-uniqueness).

Proof: (1) In the finite purity conventions, gysin_structure concentrates the support
object in degree zero. Apply concentratedComplexShift at zero and fully faithful
single-complex embedding to identify Hom from A with sections of its degree-zero sheaf L.
(2) pur_twist_sheaf_locally_free and constructible_proEtale_origin give an etale model
of the input twist. RetractedSupport.exists_comparison supplies the transported
localization triangle and boundary-edge identity. Its cohomology sequence, together
with relative_kummer, identifies the coordinate boundary with an isomorphism A -> L.
This is precisely H^0 of the orientation from affineLine_orientation.
(3) Hence each morphism is uniquely the orientation composed with multiplication by
some global section a of A. (4) Under the normalized support chart and pair pullback,
multiplication by a restricts to multiplication by its geometric germ. Naturality of
supported_cohomology_hom and exists_support_longExact proves this on supported classes.
Comparison-pullback coherence and isIso_globalGerm_identity identify the germ on the
etale model. rankOne_local_calculation sends the coordinate boundary to one, so the
residue of the restricted morphism is exactly that germ.
(5) For equal restrictions, subtract the two etale scalar endomorphisms. Exactness of
geometric stalks makes their image have zero stalks. The etale stalk isomorphism test
makes the image zero. ComparisonPullbackExact and compact-support comparison full
faithfulness then give equality of the original morphisms. This proves injectivity
without asserting conservativity on arbitrary pro-etale sheaves.
(6) affineLine_orientation gives the global boundary morphism with all residues one.
Injectivity makes it the unique such morphism. No connectedness is required; for the
empty base the Hom group and the empty product are both zero. -/
theorem affineLine_orientation_uniqueness (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] :
    ∃ D : OrientationRestrictionData P h Y a,
      Function.Injective (P.orientationGeometricRestriction h D) ∧
      ∃ m : P.derivedSheaf h Y false ⟶ P.gysinValue h Y,
        D.chart.support.hom (P.gysinHomToSections h Y m) = D.chart.coordinateBoundary P h a ∧
        P.orientationGeometricRestriction h D m = P.orientationNormalizedFamily h D ∧
        ∀ m' : P.derivedSheaf h Y false ⟶ P.gysinValue h Y,
          P.orientationGeometricRestriction h D m' = P.orientationNormalizedFamily h D →
            m' = m := by
  classical
  obtain ⟨_, _, _, _, chart, m, hm, hf⟩ := P.affineLine_orientation h Y a
  choose fibreChart transport residue hnormalized hrestriction using hf
  let D : OrientationRestrictionData P h Y a :=
    { chart := chart
      fibreChart := fibreChart
      transport := transport
      residue := residue
      residue_normalized := hnormalized }
  have hfamily : P.orientationGeometricRestriction h D m =
      P.orientationNormalizedFamily h D := by
    funext Ω _ _ _ y hy
    apply (ModuleCat.mono_iff_injective (D.residue Ω y hy).hom).mp inferInstance
    change (residue Ω y hy).hom
        (P.orientationSupportRestriction h y (transport Ω y hy)
          (chart.support.hom (P.gysinHomToSections h Y m))) =
      (residue Ω y hy).hom ((residue Ω y hy).inv 1)
    rw [hrestriction]
    exact (ConcreteCategory.congr_hom (residue Ω y hy).inv_hom_id 1).symm
  have hinj : Function.Injective (P.orientationGeometricRestriction h D) := by
    intro m₁ m₂ heq
    apply orientation_support_restriction_ext P h Y a D.chart D.transport m₁ m₂
    intro Ω _ _ _ y hy
    exact congrArg (fun z ↦ z Ω y hy) heq
  exact ⟨D, hinj, m, hm, hfamily, fun m' hm' ↦ hinj (hm'.trans hfamily.symm)⟩

end WeilConjectures.PurityFiniteSetting
