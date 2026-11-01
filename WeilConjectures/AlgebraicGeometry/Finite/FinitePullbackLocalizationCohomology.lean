/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleObjectInverseImageRestrictionSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index

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

end AlgebraicGeometry.Scheme
