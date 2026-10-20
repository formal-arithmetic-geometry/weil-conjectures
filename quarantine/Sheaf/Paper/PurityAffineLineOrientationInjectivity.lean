/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D8
-/
module

public import Sheaf.Paper.PurityAffineLineOrientation
import Sheaf.Paper.PurityAffineLineSupportStalk
import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful

/-! # Injectivity from geometric supported restrictions

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-a1,
prop-pur-affine-line-orientation-uniqueness, proof Steps 4--5
(blueprint: lem-pur-affine-line-orientation-injectivity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport

namespace WeilConjectures.PurityFiniteSetting

private theorem orientationSupportRestriction_transport_eq (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {T Y : Scheme.{u}} (f : T ⟶ Y)
    (p q : proEtaleSupportHomTransport P (zeroSection Y) (zeroSection T)
      (AffineSpace.map (ULift.{u} (Fin 1)) f)) :
    P.orientationSupportRestriction h f p = P.orientationSupportRestriction h f q := by
  let B := MorphismProperty.Over.pullback @WeaklyEtale ⊤
    (AffineSpace.map (ULift.{u} (Fin 1)) f)
  have ht : p.terminalMap = q.terminalMap := by
    apply ((proEtaleSupportHomPair P (zeroSection Y)).isTerminal.isTerminalObj B _).hom_ext
  have hu : p.supportUnit = q.supportUnit := by
    apply NatTrans.ext
    funext F
    apply (cancel_mono (kernel.ι _)).1
    rw [p.supportUnit_spec, q.supportUnit_spec, ht]
  unfold orientationSupportRestriction SupportHomPair.Transport.derivedMap
  rw [hu]

private theorem orientationEtaleUnitGerm_injective (P : PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (H : EtSheaves P Y) {f g : P.constantEtale Y ⟶ H}
    (he : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (y : Spec (CommRingCat.of Ω) ⟶ Y),
      P.orientationEtaleUnitGerm f y = P.orientationEtaleUnitGerm g y) : f = g := by
  apply ((Scheme.isConservativeFamilyOfPoints_ulift_pointSmallEtale Y).jointlyFaithful
    (ModuleCat.{u + 1} P.Coefficient)).map_injective
  rintro ⟨_, ⟨x⟩⟩
  let q := (Scheme.pointSmallEtale (Y.algClosurePoint x)).ulift.{u + 1}
  let E := q.sheafFiberConstantSheafIso (ModuleCat.of P.Coefficient P.Coefficient)
  apply (cancel_epi E.inv).1
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  exact he _ (Y.algClosurePoint x)

/-- A morphism into the zero-section Gysin object is determined by all its supported
geometric restrictions. This is the stalk-conservativity part of the uniqueness proof;
the residue calculation and the construction of the normalized family are separate.

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-a1,
prop-pur-affine-line-orientation-uniqueness, proof Steps 4--5
(blueprint: lem-pur-affine-line-orientation-injectivity).

Proof: Use the supported-Hom identification to represent a morphism by a section of the
zero-degree etale model. Pullback of a supported class is natural in the coefficient map,
and the comparison of etale and pro-etale inverse images preserves that class. At an
algebraically closed geometric point, global sections are the geometric stalk. Equality
of all supported restrictions therefore gives equality of all etale stalk maps. Exactness
of geometric stalks applied to the image of their difference, followed by conservativity
of the geometric-point family, gives equality of the etale maps. Full faithfulness of
the comparison and full faithfulness of the degree-zero embedding then gives equality
of the original derived morphisms. This argument applies to empty bases and zero maps.
-/
theorem orientation_support_restriction_ext (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (chart : OrientationSupportData P h Y)
    (transport : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra P.field.k Ω]
      (y : Spec (CommRingCat.of Ω) ⟶ Y)
      (_hy : y ≫ a = Spec.map (CommRingCat.ofHom (algebraMap P.field.k Ω))),
      proEtaleSupportHomTransport P (zeroSection Y)
        (zeroSection (Spec (CommRingCat.of Ω))) (AffineSpace.map (ULift.{u} (Fin 1)) y)) :
    ∀ m₁ m₂ : P.derivedSheaf h Y false ⟶ P.gysinValue h Y,
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra P.field.k Ω]
        (y : Spec (CommRingCat.of Ω) ⟶ Y)
        (hy : y ≫ a = Spec.map (CommRingCat.ofHom (algebraMap P.field.k Ω))),
        P.orientationSupportRestriction h y (transport Ω y hy)
          (chart.support.hom (P.gysinHomToSections h Y m₁)) =
          P.orientationSupportRestriction h y (transport Ω y hy)
            (chart.support.hom (P.gysinHomToSections h Y m₂))) →
      m₁ = m₂ := by
  classical
  intro m₁ m₂ heq
  obtain ⟨H, e, hs⟩ := P.affineLine_support_stalk h Y a chart
  let t₁ := (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (ProSheaves P Y) 0).inv.app (P.constant Y) ≫
      (DerivedCategory.homologyFunctor (ProSheaves P Y) 0).map m₁
  let t₂ := (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (ProSheaves P Y) 0).inv.app (P.constant Y) ≫
      (DerivedCategory.homologyFunctor (ProSheaves P Y) 0).map m₂
  obtain ⟨f₁, hf₁⟩ := (comparisonUpperStar (Modules P) Y).map_surjective (t₁ ≫ e.inv)
  obtain ⟨f₂, hf₂⟩ := (comparisonUpperStar (Modules P) Y).map_surjective (t₂ ≫ e.inv)
  have ht₁ : (comparisonUpperStar (Modules P) Y).map f₁ ≫ e.hom = t₁ := by
    rw [hf₁]
    simp
  have ht₂ : (comparisonUpperStar (Modules P) Y).map f₂ ≫ e.hom = t₂ := by
    rw [hf₂]
    simp
  have hf : f₁ = f₂ := by
    apply orientationEtaleUnitGerm_injective P Y H
    intro Ω _ _ y
    let r := (Spec.preimage (y ≫ a)).hom
    let : Algebra P.field.k Ω := r.toAlgebra
    have hy : y ≫ a = Spec.map (CommRingCat.ofHom (algebraMap P.field.k Ω)) := by
      change y ≫ a = Spec.map (Spec.preimage (y ≫ a))
      exact (Spec.map_preimage _).symm
    obtain ⟨p, v, hv⟩ := hs Ω y hy
    apply (ModuleCat.mono_iff_injective v.hom).mp inferInstance
    rw [← hv f₁, ← hv f₂, ht₁, ht₂]
    rw [orientationSupportRestriction_transport_eq P h y p (transport Ω y hy)]
    exact heq Ω y hy
  apply (P.gysin_structure h Y a).2.2.2.1.injective
  change P.gysinEvaluate Y t₁ = P.gysinEvaluate Y t₂
  rw [← ht₁, ← ht₂, hf]

end WeilConjectures.PurityFiniteSetting
