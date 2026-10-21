/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q109
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
public import Sheaf.NumberTheory.Padics.CoefficientExtension
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite

/-! # Finite derived pullback and normalized slice cohomology

Source: Stacks Project, sites.tex, Tag 03CE (lemma-localize-given-products);
homology.tex, Tag 010N (lemma-exact-functor); derived.tex, Tag 015F
(lemma-right-derived-exact-functor); the graph calculation in the expanded proof of
lem-pur-etale-iso-descent, steps 2--3
(blueprint: lem-pur-finite-pullback-localization-cohomology).

The structure below packages exactly the normalized comparisons in the statement.
Its graph equation uses the specified module adjunction unit at the composed object
and restriction along the graph. It therefore fixes the module comparison on sections.
The cohomology equation uses the canonical cycles/boundaries comparison, rather than
an unspecified isomorphism of cohomology objects.
-/

@[expose] public section

set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The conclusions of the finite localization comparison, retaining their normalizations.
The coefficient isomorphism fixes constant sections. The inverse of `moduleComparison`
is the graph coprojection: take the canonical module adjunction unit at the composed
object and then restrict along the graph, the unit of composition/base change on sites.
`derived_on_complexes` specifies its degreewise descent through localization.
`cohomology_formula` uses the exact-functor cycles/boundaries comparison; the final
field spells out its naturality for every derived arrow, including roofs.

Source: Stacks, Tags 03CE, 010N and 015F, and the graph calculation in the expanded
lem-pur-etale-iso-descent proof, steps 2--3
(blueprint: lem-pur-finite-pullback-localization-cohomology). -/
structure ProEtaleFiniteLocalizationComparison {X : Scheme.{u}} (U : X.ProEt)
    (A : Type u) [CommRing A] where
  [finite : Finite A]
  ringIso : proEtaleConstantRing U.left A ≅
    (AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
      U.hom U.prop).obj (proEtaleConstantRing X A)
  constantSections : ∀ V : U.left.ProEt,
    (toSheafify (ProEt.topology U.left)
      ((Functor.const U.left.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1, u} A)))).app (op V) ≫ ringIso.hom.hom.app (op V) =
      (toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1, u} A)))).app
            (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V))
  [restrictionAdditive : (proEtaleObjectModuleRestriction U A ringIso).Additive]
  [restrictionLimits : PreservesFiniteLimits (proEtaleObjectModuleRestriction U A ringIso)]
  [restrictionColimits : PreservesFiniteColimits (proEtaleObjectModuleRestriction U A ringIso)]
  moduleComparison : sfIntrinsicPullback A U.hom ≅ proEtaleObjectModuleRestriction U A ringIso
  module_graph : ∀ (M : proEtaleRingModules X (proEtaleConstantRing X A))
      (V : U.left.ProEt)
      (x : M.val.obj (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V))),
    (moduleComparison.inv.app M).val.app (op V) x =
      ((sfIntrinsicPullback A U.hom).obj M).val.map
        (proEtaleObjectInverseImageIndexPoint U V).hom.op
        (((sfIntrinsicConstantModuleAdjunction U.hom A).unit.app M).val.app
          (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V)) x)
  derivedComparison : sfIntrinsicDerivedPullback A U.hom ≅
    (proEtaleObjectModuleRestriction U A ringIso).mapDerivedCategory
  derived_on_complexes : ∀ K : CochainComplex
      (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ,
    derivedComparison.hom.app (DerivedCategory.Q.obj K) ≫
        (proEtaleObjectModuleRestriction U A ringIso).mapDerivedCategoryFactors.hom.app K =
      (sfIntrinsicPullback A U.hom).mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex moduleComparison.hom (.up ℤ)).app K)
  cohomologyComparison : ∀ r : ℤ,
    sfIntrinsicDerivedPullback A U.hom ⋙
        DerivedCategory.homologyFunctor
          (proEtaleRingModules U.left (proEtaleConstantRing U.left A)) r ≅
      DerivedCategory.homologyFunctor
          (proEtaleRingModules X (proEtaleConstantRing X A)) r ⋙
        proEtaleObjectModuleRestriction U A ringIso
  cohomology_formula : ∀ r : ℤ,
    cohomologyComparison r =
      Functor.isoWhiskerRight derivedComparison
          (DerivedCategory.homologyFunctor
            (proEtaleRingModules U.left (proEtaleConstantRing U.left A)) r) ≪≫
        ((proEtaleObjectModuleRestriction U A ringIso).mapDerivedCategoryHomologyFunctorIso
          r).symm
  cohomology_naturality : ∀ (r : ℤ) (K L : proEtaleDerivedCategory X A) (ψ : K ⟶ L),
    (DerivedCategory.homologyFunctor
        (proEtaleRingModules U.left (proEtaleConstantRing U.left A)) r).map
          ((sfIntrinsicDerivedPullback A U.hom).map ψ) ≫
        (cohomologyComparison r).hom.app L =
      (cohomologyComparison r).hom.app K ≫
        (proEtaleObjectModuleRestriction U A ringIso).map
          ((DerivedCategory.homologyFunctor
            (proEtaleRingModules X (proEtaleConstantRing X A)) r).map ψ)

private theorem coefficientDirect_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] (U : Y.ProEtᵒᵖ) :
    (toSheafify (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).app U ≫
      (proEtaleCoefficientDirectImageMap f A).hom.app U =
    (toSheafify (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).app
        ((proEtaleBaseChange f).op.obj U) := by
  have h := ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))
      ((proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
        (proEtaleConstantRing X A))).apply_symm_apply
      (Functor.whiskerLeft (proEtaleBaseChange f).op
        (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1, u} A)))))
  exact congrArg (fun z ↦ z.app U) h
private theorem coefficient_restriction_counit {X : Scheme.{u}} (W : X.ProEt)
    (A : Type u) [CommRing A]
    (e : proEtaleConstantRing W.left A ≅
      (AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
        W.hom W.prop).obj (proEtaleConstantRing X A))
    (he : ∀ U : W.left.ProEt,
      (toSheafify (ProEt.topology W.left)
        ((Functor.const W.left.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1, u} A)))).app (op U) ≫ e.hom.hom.app (op U) =
        (toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1, u} A)))).app
              (op ((MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).obj U))) :
    Functor.whiskerRight (NatTrans.op
      (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ W.hom W.prop trivial).counit)
        (proEtaleConstantRing X A).obj =
      (proEtaleCoefficientDirectImageMap W.hom A).hom ≫
        (proEtaleBaseChange W.hom).op.whiskerLeft e.hom.hom := by
  let T := (proEtaleSheafDirectImage W.hom CommRingCat.{u + 1}).obj
    ((AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
      W.hom W.prop).obj (proEtaleConstantRing X A))
  apply sheafify_hom_ext (ProEt.topology X) _ _ T.property
  apply NatTrans.ext
  funext U
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [← Category.assoc, coefficientDirect_unit]
  erw [he]
  have h := (toSheafify (ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).naturality
      ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤
        W.hom W.prop trivial).counit.app U.unop).op
  simpa [proEtaleConstantRing, constantSheaf, proEtaleBaseChange] using h.symm

private theorem coefficient_restriction_unit {X : Scheme.{u}} (W : X.ProEt)
    (A : Type u) [CommRing A]
    (e : proEtaleConstantRing W.left A ≅
      (AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
        W.hom W.prop).obj (proEtaleConstantRing X A))
    (he : ∀ U : W.left.ProEt,
      (toSheafify (ProEt.topology W.left)
        ((Functor.const W.left.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1, u} A)))).app (op U) ≫ e.hom.hom.app (op U) =
        (toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1, u} A)))).app
              (op ((MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).obj U))) :
    e.hom.hom ≫ (MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).op.whiskerLeft
      (proEtaleCoefficientDirectImageMap W.hom A).hom ≫
      Functor.whiskerRight (NatTrans.op
        (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ W.hom W.prop trivial).unit)
          (proEtaleConstantRing W.left A).obj = 𝟙 _ := by
  apply sheafify_hom_ext (ProEt.topology W.left) _ _ (proEtaleConstantRing W.left A).property
  apply NatTrans.ext
  funext U
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.id_app]
  rw [← Category.assoc, ← Category.assoc, he]
  erw [coefficientDirect_unit]
  have h := (toSheafify (ProEt.topology W.left)
    ((Functor.const W.left.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).naturality
      ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤
        W.hom W.prop trivial).unit.app U.unop).op
  simpa [proEtaleConstantRing, constantSheaf, proEtaleBaseChange] using h.symm


/-- Finite-level derived pullback is normalized slice restriction and commutes with
cohomology, naturally on all unbounded derived morphisms. The positive coefficient
level is written `n + 1`; thus every integer level at least one is included.
The source and target are the ordinary intrinsic constant-ring module categories.

Source: Stacks, sites.tex, Tag 03CE; homology.tex, Tag 010N; derived.tex, Tag 015F
(blueprint: lem-pur-finite-pullback-localization-cohomology).

Proof, following the node's six steps:
1. lem-sfb-proetale-object-inverse-image-restriction gives the constant-section
   normalized ring isomorphism `e`. Naturality of the sheafification unit proves the
   two scalar equations of the site adjunction, and pushforwardPushforwardAdj gives a
   module adjunction `a` whose left adjoint is restriction. Uniqueness of left adjoints
   against sfIntrinsicConstantModuleAdjunction gives moduleComparison; its inverse is
   the transpose of the intrinsic unit, which is module_graph.
2. sfIntrinsicPullback is additive and exact (def-weil-pbc-proetale-operations); these
   instances transfer along moduleComparison, and sfIntrinsicDerivedPullback is its
   mapDerivedCategory.
3. mapDerivedCategoryNatIso (lem-sfb-exact-derived-natural-iso) gives
   derivedComparison, and mapDerivedCategoryNatIso_fac is derived_on_complexes.
4. mapDerivedCategoryHomologyFunctorIso (lem-weil-pbc-exact-functor-complex-cohomology,
   def-weil-derived-cohomology-sheaves) is the normalized cycles/boundaries comparison.
5. It is constructed by Localization.liftNatIso
   (lem-weil-pbc-localization-universal-property), hence natural on every derived
   arrow, including roofs.
6. Compose with the cohomology of derivedComparison: cohomology_formula holds by
   definition and cohomology_naturality is naturality of this isomorphism. -/
theorem finite_pullback_localization_cohomology
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) (X : Scheme.{u}) (U : X.ProEt)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : U.left, Invertible (l : U.left.residueField x)] :
    Nonempty (ProEtaleFiniteLocalizationComparison U
      (Padic.coefficientExtensionRing l E (n + 1))) := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  have : Finite A :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  obtain ⟨comparison, e, he, _, _⟩ :=
    (proEtaleObjectInverseImageRestriction X U A).2.2.2.2
  let : (MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).IsContinuous
      (ProEt.topology U.left) (ProEt.topology X) :=
    ProEt.isContinuous_overMap (V := U.left) (U := X) U.prop
  let : (proEtaleBaseChange U.hom).IsContinuous
      (ProEt.topology X) (ProEt.topology U.left) :=
    ProEt.isContinuous_overPullback U.hom
  let R := proEtaleConstantRing X A
  let S := proEtaleConstantRing U.left A
  let φ : ((sheafCompose (ProEt.topology U.left)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) ⟶
      ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).sheafPushforwardContinuous
        RingCat.{u + 1} (ProEt.topology U.left) (ProEt.topology X)).obj
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) :=
    ⟨Functor.whiskerRight e.hom.hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  let ψ : ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⟶
      ((proEtaleBaseChange U.hom).sheafPushforwardContinuous
        RingCat.{u + 1} (ProEt.topology X) (ProEt.topology U.left)).obj
        ((sheafCompose (ProEt.topology U.left)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) :=
    ⟨Functor.whiskerRight (proEtaleCoefficientDirectImageMap U.hom A).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ U.hom U.prop trivial
  have H₁ := coefficient_restriction_counit U A e he
  have H₂ := coefficient_restriction_unit U A e he
  let a : proEtaleObjectModuleRestriction U A e ⊣
      proEtaleConstantModuleDirectImage U.hom A :=
    SheafOfModules.pushforwardPushforwardAdj.{u + 1} adj φ ψ
      (congrArg (fun t ↦ Functor.whiskerRight t
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) H₁)
      (congrArg (fun t ↦ Functor.whiskerRight t
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) H₂)
  let b := sfIntrinsicConstantModuleAdjunction U.hom A
  let m := b.leftAdjointUniq a
  have : (proEtaleObjectModuleRestriction U A e).Additive := Functor.additive_of_iso m
  have : PreservesFiniteLimits (proEtaleObjectModuleRestriction U A e) :=
    preservesFiniteLimits_of_natIso m
  have : PreservesFiniteColimits (proEtaleObjectModuleRestriction U A e) :=
    preservesFiniteColimits_of_natIso m
  let d := Functor.mapDerivedCategoryNatIso m
  let c := fun r : ℤ ↦ Functor.isoWhiskerRight d
      (DerivedCategory.homologyFunctor
        (proEtaleRingModules U.left (proEtaleConstantRing U.left A)) r) ≪≫
    ((proEtaleObjectModuleRestriction U A e).mapDerivedCategoryHomologyFunctorIso r).symm
  refine ⟨{
    ringIso := e
    constantSections := he
    moduleComparison := m
    module_graph := ?_
    derivedComparison := d
    derived_on_complexes := ?_
    cohomologyComparison := c
    cohomology_formula := fun _ ↦ rfl
    cohomology_naturality := ?_ }⟩
  · intro M V x
    have hm : m.inv.app M = (a.homEquiv M _).symm (b.unit.app M) := by
      apply (a.homEquiv M _).injective
      exact (Adjunction.homEquiv_leftAdjointUniq_hom_app a b M).trans
        ((a.homEquiv M _).apply_symm_apply _).symm
    rw [hm, Adjunction.homEquiv_counit]
    rfl
  · intro K
    exact Functor.mapDerivedCategoryNatIso_fac m K
  · intro r K L f
    exact (c r).hom.naturality f

end AlgebraicGeometry.Scheme
