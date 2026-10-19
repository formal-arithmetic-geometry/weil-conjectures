/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q154
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.PurityAffineLineOrientation
public import Sheaf.Paper.PurityRankOneLocalCalculation
import Sheaf.Paper.PurityAffineLineSupportStalk

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

private theorem supportTransport_terminalMap_eq (P : PurityFiniteSetting.{u})
    {T Y : Scheme.{u}} (f : T ⟶ Y)
    (p q : proEtaleSupportHomTransport P (zeroSection Y) (zeroSection T)
      (AffineSpace.map (ULift.{u} (Fin 1)) f)) : p.terminalMap = q.terminalMap := by
  apply MorphismProperty.Over.Hom.ext
  apply (cancel_mono (pullback.snd (𝟙 (Line Y))
    (AffineSpace.map (ULift.{u} (Fin 1)) f))).1
  exact (CategoryTheory.Over.w ((MorphismProperty.Over.forget _ _ _).map p.terminalMap)).trans
    (CategoryTheory.Over.w ((MorphismProperty.Over.forget _ _ _).map q.terminalMap)).symm

private theorem supportTransport_supportUnit_eq (P : PurityFiniteSetting.{u})
    {T Y : Scheme.{u}} (f : T ⟶ Y)
    (p q : proEtaleSupportHomTransport P (zeroSection Y) (zeroSection T)
      (AffineSpace.map (ULift.{u} (Fin 1)) f)) : p.supportUnit = q.supportUnit := by
  apply NatTrans.ext
  funext F
  apply (cancel_mono (kernel.ι _)).1
  rw [p.supportUnit_spec, q.supportUnit_spec, supportTransport_terminalMap_eq P f p q]

private theorem orientationSupportRestriction_transport_independent
    (P : PurityFiniteSetting.{u}) (h : P.ramificationIndex ∣ P.level)
    {T Y : Scheme.{u}} (f : T ⟶ Y)
    (p q : proEtaleSupportHomTransport P (zeroSection Y) (zeroSection T)
      (AffineSpace.map (ULift.{u} (Fin 1)) f)) :
    P.orientationSupportRestriction h f p = P.orientationSupportRestriction h f q := by
  have hpq := supportTransport_supportUnit_eq P f p q
  unfold orientationSupportRestriction SupportHomPair.Transport.derivedMap
  rw [hpq]

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

set_option backward.isDefEq.respectTransparency false in
/-- Geometric restriction on the displayed derived Hom group is injective; its image
contains the normalized all-ones family, with the coordinate Kummer orientation as
its unique preimage. All chart, transport and residue data are produced, not assumed.

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-a1,
prop-pur-affine-line-orientation-uniqueness, statement and six-step proof
(blueprint: prop-pur-affine-line-orientation-uniqueness).

Proof:
1. The orientation theorem gives a global chart, a coordinate morphism, normalized
 fibre charts, transports and residue isomorphisms. These define the restriction
 data. Applying the residue isomorphisms proves the normalized-family equality.
2. Two transports over the same base map have equal terminal maps, by cancellation
 against the monic projection from the pullback of the identity. Their support
 units agree after the monic kernel inclusion, hence agree. Their derived support
 restrictions therefore agree as well.
3. For two morphisms with equal restrictions, gysin_structure gives an etale model
 H for the degree-zero sheaf. Fullness of comparison lifts their degree-zero sheaf
 maps from the coefficient unit to maps f,g:A_Y -> H.
4. At the algebraic closure of each residue field of Y, the support-stalk comparison
 turns equality of supported restrictions into f_y(1)=g_y(1); step 2 permits its
 choice of transport. The constant-sheaf stalk is A, and linear maps out of A are
 determined by 1. Thus the whole stalk maps agree. Etale geometric-stalk
 extensionality gives f=g.
5. The lifted equations now identify the degree-zero maps and their evaluations.
 Injectivity of gysinHomToSections gives equality of the derived morphisms. Apply
 this injectivity to the normalized family for uniqueness. The empty-base case
 is covered by the same stalk extensionality theorem. -/
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
  obtain ⟨_, _, _, _, D, m, hm, hfib⟩ := P.affineLine_orientation h Y a
  choose fibreChart transport residue hres hnorm using hfib
  let data : OrientationRestrictionData P h Y a :=
    { chart := D
      fibreChart := fibreChart
      transport := transport
      residue := residue
      residue_normalized := hres }
  have hnormalized : P.orientationGeometricRestriction h data m =
      P.orientationNormalizedFamily h data := by
    funext Ω iField iClosed iAlgebra y hy
    apply (ConcreteCategory.bijective_of_isIso (data.residue Ω y hy).hom).1
    change (residue Ω y hy).hom
        (P.orientationSupportRestriction h y (transport Ω y hy)
          (D.support.hom (P.gysinHomToSections h Y m))) =
      (residue Ω y hy).hom ((residue Ω y hy).inv 1)
    rw [Iso.inv_hom_id_apply]
    exact hnorm Ω y hy
  let : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} P.Coefficient)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have hinj : Function.Injective (P.orientationGeometricRestriction h data) := by
    intro m₁ m₂ heq
    obtain ⟨_, _, ⟨H, ⟨e⟩, _⟩, hbij, _⟩ := P.gysin_structure h Y a
    let ν := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y
    let q := DerivedCategory.homologyFunctor
      (ProEtale.RetractedSupport.ProSheaves P Y) 0
    let v (x : P.derivedSheaf h Y false ⟶ P.gysinValue h Y) :=
      (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ProEtale.RetractedSupport.ProSheaves P Y) 0).inv.app (P.constant Y) ≫ q.map x
    obtain ⟨f, hf⟩ := ν.map_surjective (v m₁ ≫ e.inv)
    obtain ⟨g, hg⟩ := ν.map_surjective (v m₂ ≫ e.inv)
    have hf' : ν.map f ≫ e.hom = v m₁ := by rw [hf]; simp
    have hg' : ν.map g ≫ e.hom = v m₂ := by rw [hg]; simp
    have hfg : f = g := by
      apply Scheme.sheafHom_ext_of_sheafFiber_map_algClosurePoint
      intro y₀
      let Ω := AlgebraicClosure (Y.residueField y₀)
      let y := Y.algClosurePoint y₀
      let : Algebra P.field.k Ω := (Spec.preimage (y ≫ a)).hom.toAlgebra
      have hy : y ≫ a = Spec.map (CommRingCat.ofHom (algebraMap P.field.k Ω)) := by
        exact (Spec.map_preimage (y ≫ a)).symm
      let Φ := Scheme.pointSmallEtale y
      obtain ⟨p, γ, hγ⟩ := P.affineLine_support_stalk h Y a data.chart H e Ω y hy
      have heval := congrArg (fun z ↦ γ.hom (z Ω y hy)) heq
      change γ.hom (P.orientationSupportRestriction h y (data.transport Ω y hy)
          (data.chart.support.hom (P.gysinHomToSections h Y m₁))) =
        γ.hom (P.orientationSupportRestriction h y (data.transport Ω y hy)
          (data.chart.support.hom (P.gysinHomToSections h Y m₂))) at heval
      change γ.hom (P.orientationSupportRestriction h y (data.transport Ω y hy)
          (data.chart.support.hom (P.gysinEvaluate Y (v m₁)))) =
        γ.hom (P.orientationSupportRestriction h y (data.transport Ω y hy)
          (data.chart.support.hom (P.gysinEvaluate Y (v m₂)))) at heval
      rw [orientationSupportRestriction_transport_independent P h y
        (data.transport Ω y hy) p, ← hf', ← hg', hγ f, hγ g] at heval
      apply (cancel_epi (Φ.sheafFiberConstantSheafIso
        (ModuleCat.of P.Coefficient P.Coefficient)).inv).1
      apply ModuleCat.hom_ext
      apply LinearMap.ext_ring
      exact heval
    apply hbij.1
    change P.gysinEvaluate Y (v m₁) = P.gysinEvaluate Y (v m₂)
    rw [← hf', ← hg', hfg]
  refine ⟨data, hinj, m, hm, hnormalized, ?_⟩
  intro m' hm'
  exact hinj (hm'.trans hnormalized.symm)

end WeilConjectures.PurityFiniteSetting
