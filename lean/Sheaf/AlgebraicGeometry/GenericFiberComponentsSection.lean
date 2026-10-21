/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1, SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.GenericComponentData
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.RingTheory.ProEtale.WContractible
import Sheaf.AlgebraicGeometry.GenericFiberComponentSection
import Sheaf.AlgebraicGeometry.GenericComponentSiteComparison
import Sheaf.AlgebraicGeometry.GenericComponentCoefficientComparison
import Sheaf.AlgebraicGeometry.GenericComponentScalarTransport
import Sheaf.Paper.GeometricFieldProEtaleEvaluation
import Sheaf.CategoryTheory.InternalRingSheafPresentation
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Sites.LeftExact

/-! # Sections of the generic-fibre component map

Source: HRS, proof of Theorem 4.13, diagram (4.4).
-/

@[expose] public section

set_option autoImplicit false

universe u wR wS wV wCJ wCK

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.ProEt

attribute [local irreducible] genericComponentProjection genericComponentFunctor
  GenericComponentScalarCompatibility GenericComponentOrdinaryScalarCompatibility
  GenericComponentConstantScalarCompatibility

set_option linter.unusedVariables false in
/-- The generic-fibre component map is a split surjection and gives the component-site
comparison, including its coefficient and derived-category consequences.

Source: Hemo--Richarz--Scholbach, proof of Theorem 4.13, irreducible case and diagram
(4.4); fibre-product points from Stacks Tag 03H4
(blueprint: lem-zl-generic-fiber-components-section).

Proof for stage 3, following the seven DAG steps:
1. By affine fibre products and ind-etale stability, V is affine and ind-etale over Ω.
   Affine schemes are qcqs and spectral; the spectral component theorem makes S and Sη
   profinite. The first projection induces r on the actual quotient component spaces.
2. For a component of U choose a point q. Flat going-down gives a generalization q₀
   over the generic point of X, in the same component. The nonzero tensor product of
   κ(q₀) and Ω over κ(η) has a prime; the fibre-product-point theorem lifts q₀ to V.
   Thus r is surjective, including the empty case.
3. W-contractibility makes S extremally disconnected. Gleason's section theorem splits
   the continuous surjection r.
4. Use `affine_component_site_projection` for U and V. For E over S, base change of U_E
   is V_(E ×_S Sη), with the same locally ringed space and inverse-image structure sheaf.
   Naturality identifies the test-object functors and hence their geometric morphisms.
5. The geometric-field and ind-etale basis theorems identify V with Ω[Sη] and its affine
   ind-etale basis with profinite sets over Sη. Finite covers are exactly finite jointly
   surjective families. The resulting sheaf equivalence is the component inverse image.
6. Base change of Ω[E] along V → Spec Ω is Ω[Sη × E]; hence the structure map corresponds
   to Sη → *. The analogous identity for U gives p_U = q_S π_U. Transporting ring
   operations gives the coefficient comparisons for every condensed coefficient ring.
7. Transport module actions and linear maps along that same coefficient comparison.
   The inverse module functor is left adjoint to restriction along the component functor
   with the adjunction-unit ring map γ. This equivalence is additive and exact. Apply
   it termwise and descend at all quasi-isomorphisms to get the unbounded derived
   equivalence, with its Q-factorization. Terminal evaluation identifies global scalar
   actions by eΓ. Thus the ordinary extension-of-constants left adjoints commute, as do
   their unbounded left derived functors by the localization universal property. In the
   commutative constant-sheaf presentation this is precisely the displayed comparison
   after `commutativeSiteDerivedConstantModuleFunctor`, with constants normalized by
   `realizationRingUnit`. For R = Γ(*,Λ) and its constant-section map this gives the
   scalar extensions used after HRS (4.4).
-/
theorem generic_fiber_components_section
    (X : Scheme.{u}) [IsAffine X] [Nonempty X] [IrreducibleSpace X]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (η : AlgebraicGeometry.Scheme.Spec.obj (Opposite.op (CommRingCat.of Ω)) ⟶ X)
    (hη : ∀ x : (AlgebraicGeometry.Scheme.Spec.obj (Opposite.op (CommRingCat.of Ω))),
      η x = genericPoint X)
    (U : X.ProEt) [IsAffine U.left]
    (hind : RingHom.IndEtaleAcrossUniverses U.hom.appTop.hom)
    (hw : IsWContractibleRing Γ(U.left, ⊤)) :
    letI : IsAffineHom (show U.left ⟶ X from U.hom) :=
      isAffineHom_of_isAffine (show U.left ⟶ X from U.hom)
    letI : IsAffineHom η := isAffineHom_of_isAffine η
    letI : IsAffine (pullback U.hom η) :=
      instIsAffinePullbackSchemeOfIsAffineHom_1 (show U.left ⟶ X from U.hom) η
    let V : Scheme := pullback U.hom η
    let S : Profinite.{u} := Scheme.ProEt.componentProfinite U.left
    let Sη : Profinite.{u} := Scheme.ProEt.componentProfinite V
    let r : C(Sη, S) :=
      ⟨(pullback.fst U.hom η).continuous.connectedComponentsMap,
        (pullback.fst U.hom η).continuous.connectedComponentsMap_continuous⟩
    (∃ s : C(S, Sη), Function.LeftInverse r s) ∧
      (∃ (ρ : GeometricMorphism
          (Sheaf ((coherentTopology Profinite.{u}).over Sη) (Type (u + 1)))
          (Sheaf ((coherentTopology Profinite.{u}).over S) (Type (u + 1))))
        (g : GeometricMorphism
          (Sheaf (Scheme.ProEt.topology V) (Type (u + 1)))
          (Sheaf (Scheme.ProEt.topology U.left) (Type (u + 1)))),
        ρ.inverse = (coherentTopology Profinite.{u}).overMapPullback
            (Type (u + 1)) (ConcreteCategory.ofHom r : Sη ⟶ S) ∧
        Nonempty (ρ.direct ≅
          (Over.pullback (ConcreteCategory.ofHom r : Sη ⟶ S)).sheafPushforwardContinuous
            (Type (u + 1))
            ((coherentTopology Profinite.{u}).over S)
            ((coherentTopology Profinite.{u}).over Sη)) ∧
        g.inverse = Scheme.proEtaleSheafInverseImage
            (pullback.fst U.hom η) (Type (u + 1)) ∧
        (genericComponentProjection V).inverse.IsEquivalence ∧
        Nonempty (ρ.inverse ⋙ (genericComponentProjection V).inverse ≅
          (genericComponentProjection U.left).inverse ⋙ g.inverse)) ∧
      (∃ pΩ : GeometricMorphism
          (Sheaf (topology (AlgebraicGeometry.Scheme.Spec.obj
            (op (CommRingCat.of Ω)))) (Type (u + 1)))
          (Sheaf (coherentTopology Profinite.{u}) (Type (u + 1))),
        Nonempty (pΩ.direct ⋙
            sheafToPresheaf (coherentTopology Profinite.{u}) (Type (u + 1)) ≅
          sheafToPresheaf (topology (AlgebraicGeometry.Scheme.Spec.obj
            (op (CommRingCat.of Ω)))) (Type (u + 1)) ⋙
          (Functor.whiskeringLeft _ _ (Type (u + 1))).obj
            (AlgebraicGeometry.ProEtale.profiniteToProEtOf
              (AlgebraicGeometry.Scheme.Spec.obj (op (CommRingCat.of Ω)))).op) ∧
        Nonempty ((coherentTopology Profinite.{u}).overPullback (Type (u + 1)) Sη ⋙
            (genericComponentProjection V).inverse ≅
          pΩ.inverse ⋙ Scheme.proEtaleSheafInverseImage
            (pullback.snd U.hom η) (Type (u + 1)))) ∧
      (∀ Λ : Profinite.CondensedRing.{u},
        ∃ (A : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
          (AU : Sheaf (topology U.left) RingCat.{u + 1})
          (AV : Sheaf (topology V) RingCat.{u + 1}),
        Nonempty (Mon.mk ((sheafCompose (coherentTopology Profinite.{u})
            (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj A) ≅ Λ) ∧
        Nonempty (Mon.mk ((sheafCompose (topology U.left)
            (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj AU) ≅
          AlgebraicGeometry.ProEtale.coefficientRing U.left Λ) ∧
        Nonempty (Mon.mk ((sheafCompose (topology V)
            (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj AV) ≅
          AlgebraicGeometry.ProEtale.coefficientRing V Λ) ∧
        ∃ (LU : Sheaf ((coherentTopology Profinite.{u}).over S) RingCat.{u + 1} ⥤
            Sheaf (topology U.left) RingCat.{u + 1})
          (LV : Sheaf ((coherentTopology Profinite.{u}).over Sη) RingCat.{u + 1} ⥤
            Sheaf (topology V) RingCat.{u + 1})
          (adjU : LU ⊣ genericComponentRingPush U.left)
          (adjV : LV ⊣ genericComponentRingPush V)
          (iU : LU.obj (A.over S) ≅ AU)
          (iV : LV.obj (A.over Sη) ≅ AV)
          (γ : A.over Sη ⟶ (genericComponentRingPush V).obj AV),
        γ = adjV.unit.app (A.over Sη) ≫ (genericComponentRingPush V).map iV.hom ∧
        Nonempty (LU ⋙ sheafCompose (topology U.left) (CategoryTheory.forget RingCat.{u + 1}) ≅
          sheafCompose ((coherentTopology Profinite.{u}).over S)
            (CategoryTheory.forget RingCat.{u + 1}) ⋙ (genericComponentProjection U.left).inverse) ∧
        Nonempty (LV ⋙ sheafCompose (topology V) (CategoryTheory.forget RingCat.{u + 1}) ≅
          sheafCompose ((coherentTopology Profinite.{u}).over Sη)
            (CategoryTheory.forget RingCat.{u + 1}) ⋙ (genericComponentProjection V).inverse) ∧
        ∃ (t : (genericComponentFunctor V).obj (Over.mk (𝟙 Sη)) ≅ ProEt.mk (𝟙 V))
          (eΓ : (A.over Sη).obj.obj (op (Over.mk (𝟙 Sη))) ≅
            AV.obj.obj (op (ProEt.mk (𝟙 V)))),
        eΓ.hom = γ.hom.app (op (Over.mk (𝟙 Sη))) ≫ AV.obj.map t.inv.op ∧
        ∃ eM : ringedSiteModules.{u + 1} (A.over Sη) ≌ ringedSiteModules.{u + 1} AV,
        Nonempty (eM.functor ⊣ SheafOfModules.pushforward γ) ∧
        ∃ (_ : eM.functor.Additive),
        ∀ [HasDerivedCategory.{wS} (ringedSiteModules.{u + 1} (A.over Sη))]
          [HasDerivedCategory.{wV} (ringedSiteModules.{u + 1} AV)],
        ∃ eD : DerivedCategory (ringedSiteModules.{u + 1} (A.over Sη)) ≌
            DerivedCategory (ringedSiteModules.{u + 1} AV),
        Nonempty (DerivedCategory.Q ⋙ eD.functor ≅
          eM.functor.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ∧
        GenericComponentScalarCompatibility.{u, wR, wS, wV, wCJ, wCK}
          (A.over Sη) AV (Over.mk (𝟙 Sη)) (ProEt.mk (𝟙 V)) eΓ eD) := by
  let : IsAffineHom (show U.left ⟶ X from U.hom) :=
    isAffineHom_of_isAffine (show U.left ⟶ X from U.hom)
  let : IsAffineHom η := isAffineHom_of_isAffine η
  let : IsAffine (pullback U.hom η) :=
    instIsAffinePullbackSchemeOfIsAffineHom_1 (show U.left ⟶ X from U.hom) η
  dsimp only
  have hs := generic_fiber_component_section X Ω η hη U hw
  obtain ⟨he, hsquare, hpoint⟩ := generic_component_site_comparison X Ω η U hind
  let r : componentProfinite (pullback U.hom η) ⟶ componentProfinite U.left :=
    ConcreteCategory.ofHom
      ⟨(pullback.fst U.hom η).continuous.connectedComponentsMap,
        (pullback.fst U.hom η).continuous.connectedComponentsMap_continuous⟩
  let ρ : GeometricMorphism
      (Sheaf ((coherentTopology Profinite.{u}).over
        (componentProfinite (pullback U.hom η))) (Type (u + 1)))
      (Sheaf ((coherentTopology Profinite.{u}).over
        (componentProfinite U.left)) (Type (u + 1))) :=
    { inverse := (coherentTopology Profinite.{u}).overMapPullback (Type (u + 1)) r
      direct := (Over.pullback r).sheafPushforwardContinuous (Type (u + 1)) _ _
      adj := (Over.mapPullbackAdj r).sheafPushforwardContinuous _ _
      leftExact := inferInstance }
  let g : GeometricMorphism
      (Sheaf (topology (pullback U.hom η)) (Type (u + 1)))
      (Sheaf (topology U.left) (Type (u + 1))) :=
    { inverse := proEtaleSheafInverseImage (pullback.fst U.hom η) (Type (u + 1))
      direct := proEtaleSheafDirectImage (pullback.fst U.hom η) (Type (u + 1))
      adj := proEtaleSheafAdjunction (pullback.fst U.hom η) (Type (u + 1))
      leftExact := by
        let : AB5OfSize.{u, u + 1} (Type (u + 1)) :=
          AB5OfSize_of_univLE.{u, u + 1, u + 1, u + 1} _
        let : RepresentablyFlat (proEtaleBaseChange (pullback.fst U.hom η)) :=
          flat_of_preservesFiniteLimits _
        unfold proEtaleSheafInverseImage Functor.sheafPullbackConstruction.sheafPullback
        have : PreservesFiniteLimits
            ((proEtaleBaseChange (pullback.fst U.hom η)).op.lan :
              (U.left.ProEtᵒᵖ ⥤ Type (u + 1)) ⥤
                (pullback U.hom η).ProEtᵒᵖ ⥤ Type (u + 1)) := by
          apply CategoryTheory.preservesFiniteLimits_op_lan_of_flat
        infer_instance }
  let pΩ : GeometricMorphism
      (Sheaf (topology (Spec (.of Ω))) (Type (u + 1)))
      (Sheaf (coherentTopology Profinite.{u}) (Type (u + 1))) :=
    { inverse := AlgebraicGeometry.ProEtale.profinitePointSetSchemeInverseImage (Spec (.of Ω))
      direct := AlgebraicGeometry.ProEtale.geometricFieldRestriction (Spec (.of Ω)) (Type (u + 1))
      adj := AlgebraicGeometry.ProEtale.geometricFieldPointAdjunction (Spec (.of Ω))
      leftExact := AlgebraicGeometry.ProEtale.profinite_point_pullback_set_coherence.1 _ }
  refine ⟨hs, ⟨ρ, g, rfl, ⟨Iso.refl _⟩, rfl, he, hsquare⟩,
    ⟨pΩ, ⟨Iso.refl _⟩, hpoint⟩, ?_⟩
  intro Λ
  have hpres : ∃ A : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1},
      Nonempty (Mon.mk ((sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj A) ≅ Λ) :=
    internal_ring_sheaf_presentation.{u + 1, u + 1, u}
      (coherentTopology Profinite.{u}) Λ
  obtain ⟨A, hA⟩ := hpres
  have hpresU : ∃ AU : Sheaf (topology U.left) RingCat.{u + 1},
      Nonempty (Mon.mk ((sheafCompose (topology U.left)
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj AU) ≅
          AlgebraicGeometry.ProEtale.coefficientRing U.left Λ) :=
    internal_ring_sheaf_presentation.{u + 1, u + 1, u} (topology U.left)
      (AlgebraicGeometry.ProEtale.coefficientRing U.left Λ)
  obtain ⟨AU, hAU⟩ := hpresU
  have hpresV : ∃ AV : Sheaf (topology (pullback U.hom η)) RingCat.{u + 1},
      Nonempty (Mon.mk ((sheafCompose (topology (pullback U.hom η))
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj AV) ≅
          AlgebraicGeometry.ProEtale.coefficientRing (pullback U.hom η) Λ) :=
    internal_ring_sheaf_presentation.{u + 1, u + 1, u} (topology (pullback U.hom η))
      (AlgebraicGeometry.ProEtale.coefficientRing (pullback U.hom η) Λ)
  obtain ⟨AV, hAV⟩ := hpresV
  have hc : Nonempty (GenericComponentCoefficientData U.left (pullback U.hom η) A AU AV) :=
    @generic_component_coefficient_comparison U.left (pullback U.hom η) _ _ he
      Λ A AU AV hA hAU hAV
  cases hc with
  | intro p =>
    refine ⟨A, AU, AV, hA, hAU, hAV, p.LU, p.LV, p.adjU, p.adjV,
      p.iU, p.iV, p.γ, p.hγ, p.hLU, p.hLV, p.t, p.eΓ, p.heΓ, p.eM, p.hadj, p.hAdd, ?_⟩
    have hordinary := generic_component_ordinary_scalar_transport
      (genericComponentFunctor (pullback U.hom η))
      (A.over (componentProfinite (pullback U.hom η))) AV p.γ
      (Over.mk (𝟙 (componentProfinite (pullback U.hom η))))
      (ProEt.mk (𝟙 (pullback U.hom η))) p.t p.eΓ p.heΓ
      p.eM p.hadj p.hscalar
    let := p.hAdd
    intro _ _
    exact generic_component_derived_scalar_transport
      (A.over (componentProfinite (pullback U.hom η))) AV
      (Over.mk (𝟙 (componentProfinite (pullback U.hom η))))
      (ProEt.mk (𝟙 (pullback U.hom η))) p.eΓ p.eM hordinary

end AlgebraicGeometry.Scheme.ProEt
