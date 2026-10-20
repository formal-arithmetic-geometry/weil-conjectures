/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q57
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Sheaf.AlgebraicGeometry.ProEtalePointPullback
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
import Sheaf.CategoryTheory.SheafTensor
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs

/-!
# Coefficient sections and localization

Source: Stacks Project, sites.tex, Tags 00Y0 and 03EH; proetale.tex, Tag 098T;
canonical coefficient specialization using the blueprint pullback-from-point comparison
(blueprint: lem-sfb-coefficient-sections-localization).

Stage-2 validation: N6 checked the recorded statement, dependency interfaces, and
universe parameters against the shared live library on 2026-10-18.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The unit of the section ring, obtained by evaluating the internal ring unit.
Source: Stacks, Tag 00Y0 (blueprint: lem-sfb-coefficient-sections-localization). -/
noncomputable def sfbSectionOne
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u}) (T : X.ProEt) : (condensedRingObj Λ X).obj.obj (op T) :=
  ((Functor.LaxMonoidal.ε (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ≫
    (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
      (MonObj.one (X := condensedRingObj Λ X))).app (op T)).hom (ULift.up (1 : ℤ))

/-- Multiplication of sections, using the lax tensorator of evaluation followed by
internal multiplication. Source: Stacks, Tag 00Y0
(blueprint: lem-sfb-coefficient-sections-localization). -/
noncomputable def sfbSectionMul
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u}) (T : X.ProEt)
    (a b : (condensedRingObj Λ X).obj.obj (op T)) :
    (condensedRingObj Λ X).obj.obj (op T) :=
  ((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X) (condensedRingObj Λ X) ≫
    (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
      (MonObj.mul (X := condensedRingObj Λ X))).app (op T)).hom (a ⊗ₜ[ℤ] b)

/-- The graph of a map to a test object, as a map from the final object to its base change.
Source: Stacks, Tag 03CE (blueprint: lem-sfb-coefficient-sections-localization). -/
noncomputable def sfbSectionGraph {X Y : Scheme.{u}} (f : X ⟶ Y) (T : Y.ProEt)
    (a : X ⟶ T.left) (ha : a ≫ T.hom = f) :
    Scheme.ProEt.mk (𝟙 X) ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj T :=
  MorphismProperty.Over.homMk
    (pullback.lift a (𝟙 X) (ha.trans (Category.id_comp f).symm))
    (pullback.lift_snd _ _ _) trivial

/-- The section map `θ_T`: apply the actual coefficient mate `η` and restrict along the
 diagonal. This is the evaluation of `α` after inverse-image restriction, without choosing
 an arbitrary isomorphism. Source: Stacks, Tags 00Y0 and 03CE
(blueprint: lem-sfb-coefficient-sections-localization). -/
noncomputable def sfbCoefficientSectionMap
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    {B : Scheme.{u}} (T : B.ProEt) :
    (condensedRingObj Λ B).obj.obj (op T) ⟶
      (condensedRingObj Λ T.left).obj.obj (op (Scheme.ProEt.mk (𝟙 T.left))) :=
  (condensedPushforwardHom Λ T.hom).hom.app (op T) ≫
    (condensedRingObj Λ T.left).obj.map
      (sfbSectionGraph T.hom T (𝟙 T.left) (Category.id_comp T.hom)).op

/-- The global-section map `f^sharp`, expressed by the coefficient mate and the canonical
map from the final object to its base change. Source: Stacks, Tag 03EH
(blueprint: lem-sfb-coefficient-sections-localization). -/
noncomputable def sfbCoefficientGlobalMap
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (condensedRingObj Λ Y).obj.obj (op (Scheme.ProEt.mk (𝟙 Y))) ⟶
      (condensedRingObj Λ X).obj.obj (op (Scheme.ProEt.mk (𝟙 X))) :=
  (condensedPushforwardHom Λ f).hom.app (op (Scheme.ProEt.mk (𝟙 Y))) ≫
    (condensedRingObj Λ X).obj.map
      (sfbSectionGraph f (Scheme.ProEt.mk (𝟙 Y)) f (Category.comp_id f)).op

/-- The unique arrow to the final pro-etale test object.
Source: Stacks, Tag 00Y0 (blueprint: lem-sfb-coefficient-sections-localization). -/
def sfbSectionFinalArrow (X : Scheme.{u}) (T : X.ProEt) :
    T ⟶ Scheme.ProEt.mk (𝟙 X) :=
  MorphismProperty.Over.homMk T.hom (Category.comp_id T.hom) trivial

/-- Coefficient sections over site objects are global sections after pullback, naturally
in every morphism of test objects and compatibly with multiplication endomorphisms.
The bijective additive map with its unit and product equations is the ring isomorphism
`θ`. Global sections are evaluated at the final object. The endomorphisms `m` below
are fixed on every test object by multiplication by the restricted global section.
The regular-module isomorphism `q` is normalized by `q(1 ⊗ a) = α(a)`; linearity
then gives `q(b ⊗ a) = b α(a)`, so this is the canonical scalar-extension comparison.

Source: Stacks, sites.tex, Tags 00Y0, 03CE and 03EH; proetale.tex, Tag 098T;
blueprint `lem-sfb-eta-comp` and `def-sfb-modobj-extension`
(blueprint: lem-sfb-coefficient-sections-localization).

Proof plan:
1. `lem-weil-proetale-weakly-etale-localization` identifies the small site with the
   slice, by composition and cancellation of weakly etale maps. The coverings agree.
   Clause (1) of `lem-sfb-proetale-object-inverse-image-restriction` computes abelian
   and ring inverse image as restriction; its distinguished graph coprojection is
   initial in the Kan index. This is the same sheafified Kan construction as
   `def-sfb-finite-upper-star` and `def-weil-proetale-inverse-image`.
2. Restrict the coefficient ring and apply `sk-def-sfb-coefficient-morphisms`.
   Evaluate the resulting ring isomorphism at the final object. The ring operations
   are those of restriction (`def-pur-localized-ringed-site`), giving the unit and
   product equations, and the additive component is invertible.
3. The adjunction unit on T sends a section to its restriction along the projection
   T ×_B V → T. Thus applying eta and restricting along the diagonal gives exactly
   this evaluation of alpha. At a final object this also computes f^sharp as
   alpha composed with pullback of the section-as-map from the monoidal unit.
4. For h : W → V use its graph W → V ×_B W. Naturality of the coefficient sheaf
   map identifies restriction of eta along this graph with theta_W of the ordinary
   restriction of the original section, including nonconstant sections.
5. `lem-sfb-eta-comp`, with `def-sfb-finite-lower-star-comp`, identifies this value
   with h^sharp(theta_V(s)): base-changing the diagonal gives that very graph.
   No monomorphism assumption is used.
6. By `def-sfb-module-upper-star`, `def-sfb-modobj-extension` and
   `sk-def-sfb-sheaf-tensor`, module pullback is S ⊗_R inverseImage(-). On the regular
   module the canonical comparison sends b ⊗ a to b alpha(a), with inverse b ↦ b ⊗ 1.
   Balancing proves both inverse identities and the normalization in the statement.
7. Multiplication pulls back to b ⊗ a ↦ b ⊗ ta; its image is
   b alpha(ta) = alpha(t)b alpha(a). Equality on the tensor projection and its
   sheafification proves the asserted endomorphism identity. Step 5 identifies
   alpha(t) with theta_W of the sheaf restriction. -/
theorem sfbCoefficientSectionsLocalization
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (B : Scheme.{u}) :
    (∀ V : B.ProEt, ∃ e : Over V ≌ V.left.ProEt,
      (∀ T : Over V, (e.functor.obj T).left = T.left.left) ∧
      (∀ T : Over V, HEq (e.functor.obj T).hom T.hom.left) ∧
      (∀ (T T' : Over V) (a : T ⟶ T'), HEq (e.functor.map a).left a.left.left) ∧
      (∀ T : V.left.ProEt, (e.inverse.obj T).left.left = T.left) ∧
      (∀ T : V.left.ProEt, HEq (e.inverse.obj T).hom.left T.hom) ∧
      (∀ (T T' : V.left.ProEt) (a : T ⟶ T'), HEq (e.inverse.map a).left.left a.left) ∧
      (∀ (T : V.left.ProEt) (S : Sieve T),
        S ∈ Scheme.ProEt.topology V.left T ↔
          S.functorPushforward e.inverse ∈
            (Scheme.ProEt.topology B).over V (e.inverse.obj T)) ∧
      Nonempty (upperStar Ab.{u + 1} V.hom ≅
        localizationRestriction Ab.{u + 1} V.hom V.prop)) ∧
    (∀ V : B.ProEt,
      IsIso (sfbCoefficientSectionMap Λ V) ∧
      (sfbCoefficientSectionMap Λ V).hom (sfbSectionOne Λ B V) =
        sfbSectionOne Λ V.left (Scheme.ProEt.mk (𝟙 V.left)) ∧
      ∀ a b : (condensedRingObj Λ B).obj.obj (op V),
        (sfbCoefficientSectionMap Λ V).hom (sfbSectionMul Λ B V a b) =
          sfbSectionMul Λ V.left (Scheme.ProEt.mk (𝟙 V.left))
            ((sfbCoefficientSectionMap Λ V).hom a) ((sfbCoefficientSectionMap Λ V).hom b)) ∧
    (∀ (V W : B.ProEt) (h : W ⟶ V)
      (s : (condensedRingObj Λ B).obj.obj (op V)),
      (sfbCoefficientGlobalMap Λ h.left).hom ((sfbCoefficientSectionMap Λ V).hom s) =
        (sfbCoefficientSectionMap Λ W).hom ((condensedRingObj Λ B).obj.map h.op s)) ∧
    ∃ m : ∀ (X : Scheme.{u}),
        (condensedRingObj Λ X).obj.obj (op (Scheme.ProEt.mk (𝟙 X))) →
          (Mod.regular (condensedRingObj Λ X) ⟶ Mod.regular (condensedRingObj Λ X)),
      (∀ (X : Scheme.{u})
        (r : (condensedRingObj Λ X).obj.obj (op (Scheme.ProEt.mk (𝟙 X))))
        (T : X.ProEt) (a : (condensedRingObj Λ X).obj.obj (op T)),
        (m X r).hom.hom.app (op T) a = sfbSectionMul Λ X T
          ((condensedRingObj Λ X).obj.map (sfbSectionFinalArrow X T).op r) a) ∧
      ∀ (V W : B.ProEt) (h : W ⟶ V),
        ∃ q : (CondensedRing.upperStar Λ h.left).obj
            (Mod.regular (condensedRingObj Λ V.left)) ≅
              Mod.regular (condensedRingObj Λ W.left),
          Mod.extendUnitHom (condensedPullbackHom Λ h.left)
              (((upperStar Ab.{u + 1} h.left).mapMod (condensedRingObj Λ V.left)).obj
                (Mod.regular (condensedRingObj Λ V.left))) ≫ q.hom.hom =
            condensedPullbackHom Λ h.left ∧
          ∀ s : (condensedRingObj Λ B).obj.obj (op V),
            (CondensedRing.upperStar Λ h.left).map
                (m V.left ((sfbCoefficientSectionMap Λ V).hom s)) ≫ q.hom =
              q.hom ≫ m W.left ((sfbCoefficientSectionMap Λ W).hom
                ((condensedRingObj Λ B).obj.map h.op s)) := by
  sorry

end AlgebraicGeometry.ProEtale
