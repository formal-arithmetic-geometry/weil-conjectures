/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.GenericComponentData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Sheaf.Topology.ProfiniteCondensedRing

/-! # Components and geometric generic fibres

Source: Hemo--Richarz--Scholbach, proof of Theorem 4.13, diagram (4.4).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.ProEt

/-- The ordinary ring and module data of the component comparison.
Source: HRS, proof following (4.4)
(blueprint: lem-zl-generic-component-coefficient-comparison). -/
structure GenericComponentCoefficientData
    (T V : Scheme.{u}) [IsAffine T] [IsAffine V]
    (A : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    (AU : Sheaf (topology T) RingCat.{u + 1})
    (AV : Sheaf (topology V) RingCat.{u + 1}) where
  LU : Sheaf ((coherentTopology Profinite.{u}).over (componentProfinite T)) RingCat.{u + 1} ⥤
    Sheaf (topology T) RingCat.{u + 1}
  LV : Sheaf ((coherentTopology Profinite.{u}).over (componentProfinite V)) RingCat.{u + 1} ⥤
    Sheaf (topology V) RingCat.{u + 1}
  adjU : LU ⊣ genericComponentRingPush T
  adjV : LV ⊣ genericComponentRingPush V
  iU : LU.obj (A.over (componentProfinite T)) ≅ AU
  iV : LV.obj (A.over (componentProfinite V)) ≅ AV
  γ : A.over (componentProfinite V) ⟶ (genericComponentRingPush V).obj AV
  hγ : γ = adjV.unit.app (A.over (componentProfinite V)) ≫
    (genericComponentRingPush V).map iV.hom
  hLU : Nonempty (LU ⋙ sheafCompose (topology T) (CategoryTheory.forget RingCat.{u + 1}) ≅
    sheafCompose ((coherentTopology Profinite.{u}).over (componentProfinite T))
      (CategoryTheory.forget RingCat.{u + 1}) ⋙ (genericComponentProjection T).inverse)
  hLV : Nonempty (LV ⋙ sheafCompose (topology V) (CategoryTheory.forget RingCat.{u + 1}) ≅
    sheafCompose ((coherentTopology Profinite.{u}).over (componentProfinite V))
      (CategoryTheory.forget RingCat.{u + 1}) ⋙ (genericComponentProjection V).inverse)
  t : (genericComponentFunctor V).obj (Over.mk (𝟙 (componentProfinite V))) ≅ ProEt.mk (𝟙 V)
  eΓ : (A.over (componentProfinite V)).obj.obj (op (Over.mk (𝟙 (componentProfinite V)))) ≅
    AV.obj.obj (op (ProEt.mk (𝟙 V)))
  heΓ : eΓ.hom = γ.hom.app (op (Over.mk (𝟙 (componentProfinite V)))) ≫ AV.obj.map t.inv.op
  eM : ringedSiteModules.{u + 1} (A.over (componentProfinite V)) ≌ ringedSiteModules.{u + 1} AV
  hadj : Nonempty (eM.functor ⊣ SheafOfModules.pushforward γ)
  hAdd : eM.functor.Additive
  hscalar : GenericComponentConstantScalarCompatibility
    (A.over (componentProfinite V)) AV (Over.mk (𝟙 (componentProfinite V)))
    (ProEt.mk (𝟙 V)) eΓ eM

/-- Ordinary coefficients and module sheaves under the component projection.
Source: HRS, proof of Theorem 4.13, the coefficient comparison following (4.4);
Stacks Project, Modules on Sites, Tags 03D1--03D3
(blueprint: lem-zl-generic-component-coefficient-comparison).

Proof: the component test-object construction identifies the structural point inverse
image with component inverse image after restriction to the profinite slice. Present
the given ring-valued presentations through their isomorphisms with the arbitrary
condensed ring and its two inverse images. Lift the set inverse images to rings; the
right adjoints are restriction along the same component functors. The structural
comparison gives iU and iV, with the adjunction-unit ring map γ as displayed.
Finite-limit preservation makes the terminal component test object terminal, giving
t. On V the set equivalence transports module actions and linear maps to inverse
additive module equivalences. Its right adjoint is precisely pushforward along γ.
Terminal evaluation of its unit gives the ring isomorphism eΓ and its stated equation.
Apply the same transport to constant-ring sheaves to obtain ER. Both composites of
constant realization are
left adjoint to global sections, hence canonically isomorphic. For scalar maps aS
and aV, agreement on constant sections implies agreement of the sheaf maps, by the
constant-sheafification adjunction and naturality of the terminal restriction maps.
Thus the scalar-restriction square commutes, so its left-adjoint square commutes.
The argument allows empty sites, zero coefficient rings and independent localization
universes. -/
theorem generic_component_coefficient_comparison
    (T V : Scheme.{u}) [IsAffine T] [IsAffine V]
    [(genericComponentProjection V).inverse.IsEquivalence]
    (Λ : Profinite.CondensedRing.{u})
    (A : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    (AU : Sheaf (topology T) RingCat.{u + 1})
    (AV : Sheaf (topology V) RingCat.{u + 1})
    (hA : Nonempty (Mon.mk ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj A) ≅ Λ))
    (hAU : Nonempty (Mon.mk ((sheafCompose (topology T)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj AU) ≅
        AlgebraicGeometry.ProEtale.coefficientRing T Λ))
    (hAV : Nonempty (Mon.mk ((sheafCompose (topology V)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj AV) ≅
        AlgebraicGeometry.ProEtale.coefficientRing V Λ)) :
    Nonempty (GenericComponentCoefficientData T V A AU AV) := by
  sorry

end AlgebraicGeometry.Scheme.ProEt
