/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.AlgebraicGeometry.PicardTermwiseModels

/-! # Composition equation for explicit termwise comparison morphisms

Source: Stacks Project, Tags 06YJ and 0D5S.
(blueprint: lem-sc-picard-termwise-composite-counit)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

attribute [local instance] Functor.additive_of_preserves_binary_products

variable [∀ Y : Scheme.{v},
  HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]

/-- The composites of a fixed morphism with the pinned tensor-pullback counits
satisfy the composition equation. No perfectness, invertibility, or representation
of E on the open site is assumed: this is an equation of explicitly given morphisms.

Source: Stacks Project, Tag 0D5S, composition of derived pullbacks, and Tag 06YJ,
computation on complexes.
(blueprint: lem-sc-picard-termwise-composite-counit)

Proof:
1. Substitute t = s;U.ι, s' = i;s and t' = i;t using hf, hs and ht.
   The remaining factorization hf' is the associativity equality. Replace its
   proof by that equality using proof irrelevance, retaining its eqToIso as the
   associativity transport in the composition law. Put P = overEquiv(U)(K).
2. The defining left-derived-lift equation of the pinned c(i,s), evaluated on
   the image of P in the homotopy category, says that c(i,s).hom followed by
   the composite counit equals the successive counits followed by the ordinary
   tensor-pullback composition comparison. Whisker with the complex quotient.
   The natural isomorphism quotientCompQhIso and the factorization of tensor
   pullback through the homotopy quotient identify these counits with
   picardTermwiseCounit. The same factorization identifies the inverse of the
   ordinary comparison with picardTermwiseModelRestrictionIso. Cancel the two
   comparison isomorphisms to obtain the inverse-composition counit equation.
3. Expand b. Naturality of c(i,s).inv at e moves e through this equation.
   The associativity law for c(i,s,U.ι), evaluated at E, identifies the two
   inverse-composition paths from L(i;s;U.ι)(E). Reassociate composition and
   substitute the equation of step 2. This is exactly the displayed equality.
   No counit is canceled as an isomorphism; the argument applies to arbitrary
   e and arbitrary complexes, including the zero complex and empty schemes. -/
theorem picard_termwise_composite_counit
    (W : Scheme.{v}) (E : schemeDerivedCategory W) (U : W.Opens)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (e : (derivedPullback U.ι).obj E ⟶ DerivedCategory.Q.obj
      (((Modules.overEquiv U).functor.mapHomologicalComplex (.up ℤ)).obj K)) :
    let c : ∀ {X Y Z : Scheme.{v}} (f : X ⟶ Y) (g : Y ⟶ Z),
        derivedPullback g ⋙ derivedPullback f ≅ derivedPullback (f ≫ g) :=
      fun f g ↦ Classical.choose (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition))) f g
    let P := ((Modules.overEquiv U).functor.mapHomologicalComplex (.up ℤ)).obj K
    let b : ∀ {T : Scheme.{v}} (t : T ⟶ W) (s : T ⟶ U.toScheme),
        s ≫ U.ι = t → ((derivedPullback t).obj E ⟶
          DerivedCategory.Q.obj (picardTermwiseModel W U K s)) :=
      fun {T} t s hf ↦
        ((c s U.ι ≪≫ eqToIso
          (congrArg (fun g : T ⟶ W ↦ derivedPullback g) hf)).inv.app E) ≫
        (derivedPullback s).map e ≫ (picardTermwiseCounit s).app P
    ∀ {T T' : Scheme.{v}} (i : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ W)
      (s : T ⟶ U.toScheme) (s' : T' ⟶ U.toScheme)
      (ht : i ≫ t = t') (hs : i ≫ s = s')
      (hf : s ≫ U.ι = t) (hf' : s' ≫ U.ι = t'),
      b t' s' hf' ≫
          DerivedCategory.Q.map (picardTermwiseModelRestrictionIso W U K i s s' hs).hom =
        ((c i t ≪≫ eqToIso
          (congrArg (fun g : T' ⟶ W ↦ derivedPullback g) ht)).inv.app E) ≫
          (derivedPullback i).map (b t s hf) ≫
            (picardTermwiseCounit i).app (picardTermwiseModel W U K s) := by sorry

end
end AlgebraicGeometry.Scheme
