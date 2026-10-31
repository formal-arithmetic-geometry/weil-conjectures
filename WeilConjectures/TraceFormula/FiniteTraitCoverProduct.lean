/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictLocalizationMap
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic

import WeilConjectures.RingTheory.StrictHenselizationCotangentDimension
import WeilConjectures.RingTheory.StrictHenselizationDimension
import WeilConjectures.AlgebraicGeometry.StrictHenselizationDVR
import WeilConjectures.RingTheory.StrictHenselizationRegular
import WeilConjectures.AlgebraicGeometry.IndEtaleStrictLocalInvariance
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.ClosedPointDimensionLocalRing
import WeilConjectures.RingTheory.CompletionDimension
import WeilConjectures.RingTheory.CompletionRegularLocal
import WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct
import WeilConjectures.RingTheory.SmoothOverFieldRegularLocal

/-!
# Products of finite covers of strictly local traits

Source: Stacks Project, Tags 05WR, 0GIP, 0C0S; blueprint
`det-tf-restriction-zero-covers`, proof (ii).
(blueprint: lem-trf-finite-trait-cover-product).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing

namespace AlgebraicGeometry.FiniteTraitCoverProduct

/-- The input for one factor, including witnesses to the assumed descent to a finite
morphism over an étale pointed curve neighbourhood. The isomorphism `e` identifies the
arbitrary strictly local trait `Spec A` with the strict localization of that covering
curve, over the ground field, and `induced` says that it induces the given map `p`.
Source: blueprint `det-tf-restriction-zero-covers`, proof (ii), and Stacks 05WR, 0GIP
(blueprint: lem-trf-finite-trait-cover-product). -/
structure Cover (k : Type u) [Field k] [IsAlgClosed k] where
  C : Scheme.{u}
  f : C ⟶ Spec (.of k)
  curve : IsCurve f
  smooth : Smooth f
  x : Spec (.of k) ⟶ C
  x_f : x ≫ f = 𝟙 _
  A : CommRingCat.{u}
  [alg : Algebra k A]
  [domain : IsDomain A]
  [dvr : IsDiscreteValuationRing A]
  [strictlyHenselian : IsStrictlyHenselianLocalRing A]
  residue : A →ₐ[k] k
  residue_ker : RingHom.ker residue.toRingHom = maximalIdeal A
  p : Spec A ⟶ Scheme.strictLocalization x
  over_k : p ≫ Scheme.strictLocalizationToBase x ≫ f =
    Spec.map (CommRingCat.ofHom (algebraMap k A))
  degree : ℕ
  degree_pos : 1 ≤ degree
  finiteFlat : p.IsFiniteLocallyFreeOfDegree degree
  etale_off : ∀ V : (Scheme.strictLocalization x).Opens,
    closedPoint (Scheme.strictHenselization x) ∉ V → Etale (p ∣_ V)
  U : Scheme.{u}
  j : U ⟶ C
  etale_j : Etale j
  C' : Scheme.{u}
  g : C' ⟶ U
  finite_g : IsFinite g
  covering_curve : IsCurve (g ≫ j ≫ f)
  smooth_cover : Smooth (g ≫ j ≫ f)
  c : Spec (.of k) ⟶ C'
  c_g_j : c ≫ (g ≫ j) = x
  e : Spec A ≅ Scheme.strictLocalization c
  e_over_k : e.hom ≫ Scheme.strictLocalizationToBase c ≫ g ≫ j ≫ f =
    Spec.map (CommRingCat.ofHom (algebraMap k A))
  induced : p = e.hom ≫ Scheme.strictLocalizationMap (g ≫ j) c ≫
    eqToHom (congrArg Scheme.strictLocalization c_g_j)

attribute [instance] Cover.alg Cover.domain Cover.dvr Cover.strictlyHenselian
attribute [instance] Cover.curve Cover.smooth Cover.finiteFlat Cover.etale_j Cover.finite_g
attribute [instance] Cover.covering_curve Cover.smooth_cover

variable {k : Type u} [Field k] [IsAlgClosed k] (D₁ D₂ : Cover k)

/-- The indicated rational point of the product of the base curves.
Source: blueprint proof (ii) (blueprint: lem-trf-finite-trait-cover-product). -/
noncomputable def basePoint : Spec (.of k) ⟶ pullback D₁.f D₂.f :=
  pullback.lift D₁.x D₂.x (D₁.x_f.trans D₂.x_f.symm)

/-- The strict local surface of the product of the base curves.
Source: blueprint proof (ii) (blueprint: lem-trf-finite-trait-cover-product). -/
noncomputable abbrev surface : Scheme.{u} :=
  Scheme.strictLocalization (basePoint D₁ D₂)

/-- The first canonical map from the strict local surface to a strict local factor.
Source: Stacks 0GIP (blueprint: lem-trf-finite-trait-cover-product). -/
noncomputable def q₁ : surface D₁ D₂ ⟶ Scheme.strictLocalization D₁.x :=
  Scheme.strictLocalizationMap (pullback.fst D₁.f D₂.f) (basePoint D₁ D₂) ≫
    eqToHom (congrArg Scheme.strictLocalization (pullback.lift_fst _ _ _))

/-- The second canonical map from the strict local surface to a strict local factor.
Source: Stacks 0GIP (blueprint: lem-trf-finite-trait-cover-product). -/
noncomputable def q₂ : surface D₁ D₂ ⟶ Scheme.strictLocalization D₂.x :=
  Scheme.strictLocalizationMap (pullback.snd D₁.f D₂.f) (basePoint D₁ D₂) ≫
    eqToHom (congrArg Scheme.strictLocalization (pullback.lift_snd _ _ _))

/-- The product over the ground field of the two strict local base traits.
Source: blueprint proof (ii) (blueprint: lem-trf-finite-trait-cover-product). -/
noncomputable abbrev baseTraits : Scheme.{u} :=
  pullback (Scheme.strictLocalizationToBase D₁.x ≫ D₁.f)
    (Scheme.strictLocalizationToBase D₂.x ≫ D₂.f)

/-- The canonical map to the product of strict local traits, constructed using the
functorial strict-localization maps, not chosen from an existence assertion.
Source: Stacks 0GIP (blueprint: lem-trf-finite-trait-cover-product). -/
noncomputable def surfaceMap : surface D₁ D₂ ⟶ baseTraits D₁ D₂ :=
  pullback.lift (q₁ D₁ D₂) (q₂ D₁ D₂) (by
    have transport {C : Scheme.{u}} {x y : Spec (.of k) ⟶ C} (h : x = y) :
        eqToHom (congrArg Scheme.strictLocalization h) ≫
          Scheme.strictLocalizationToBase y = Scheme.strictLocalizationToBase x := by
      cases h
      exact Category.id_comp _
    have h₁ : q₁ D₁ D₂ ≫ Scheme.strictLocalizationToBase D₁.x =
        Scheme.strictLocalizationToBase (basePoint D₁ D₂) ≫ pullback.fst D₁.f D₂.f := by
      unfold q₁
      rw [Category.assoc, transport (pullback.lift_fst D₁.x D₂.x _)]
      exact Scheme.strictLocalizationMap_comp_strictLocalizationToBase _ _
    have h₂ : q₂ D₁ D₂ ≫ Scheme.strictLocalizationToBase D₂.x =
        Scheme.strictLocalizationToBase (basePoint D₁ D₂) ≫ pullback.snd D₁.f D₂.f := by
      unfold q₂
      rw [Category.assoc, transport (pullback.lift_snd D₁.x D₂.x _)]
      exact Scheme.strictLocalizationMap_comp_strictLocalizationToBase _ _
    simp only [← Category.assoc, h₁, h₂]
    simpa only [Category.assoc] using
      congrArg (fun a ↦ Scheme.strictLocalizationToBase (basePoint D₁ D₂) ≫ a)
        (pullback.condition (f := D₁.f) (g := D₂.f)))

/-- The product over k of the two covering traits.
Source: blueprint proof (ii) (blueprint: lem-trf-finite-trait-cover-product). -/
noncomputable abbrev coverTraits : Scheme.{u} :=
  pullback (Spec.map (CommRingCat.ofHom (algebraMap k D₁.A)))
    (Spec.map (CommRingCat.ofHom (algebraMap k D₂.A)))

/-- The product of the two given finite flat morphisms.
Source: blueprint proof (ii) (blueprint: lem-trf-finite-trait-cover-product). -/
noncomputable def coverMap : coverTraits D₁ D₂ ⟶ baseTraits D₁ D₂ :=
  pullback.map _ _ _ _ D₁.p D₂.p (𝟙 _) ((Category.comp_id _).trans D₁.over_k.symm)
    ((Category.comp_id _).trans D₂.over_k.symm)

/-- The displayed fibre product T ×_(X₁ ×_k X₂) (X₁' ×_k X₂'), with no localization
or choice of a component added to its construction.
Source: blueprint proof (ii) (blueprint: lem-trf-finite-trait-cover-product). -/
noncomputable abbrev chart : Scheme.{u} :=
  pullback (surfaceMap D₁ D₂) (coverMap D₁ D₂)

/-- The product of the smooth covering curves.
Source: blueprint proof (ii) (blueprint: lem-trf-finite-trait-cover-product). -/
noncomputable abbrev coveringCurves : Scheme.{u} :=
  pullback (D₁.g ≫ D₁.j ≫ D₁.f) (D₂.g ≫ D₂.j ≫ D₂.f)

/-- The indicated rational point of the product of the covering curves.
Source: blueprint proof (ii) (blueprint: lem-trf-finite-trait-cover-product). -/
noncomputable def coveringPoint : Spec (.of k) ⟶ coveringCurves D₁ D₂ :=
  pullback.lift D₁.c D₂.c
    ((Category.assoc D₁.c (D₁.g ≫ D₁.j) D₁.f).symm.trans
      ((congrArg (fun a ↦ a ≫ D₁.f) D₁.c_g_j).trans
        (D₁.x_f.trans (D₂.x_f.symm.trans
          ((congrArg (fun a ↦ a ≫ D₂.f) D₂.c_g_j).symm.trans
            (Category.assoc D₂.c (D₂.g ≫ D₂.j) D₂.f))))))

/-- The canonical map from the displayed fibre product to the product of covering curves.
Source: blueprint proof (ii) (blueprint: lem-trf-finite-trait-cover-product). -/
noncomputable def toCoveringCurves : chart D₁ D₂ ⟶ coveringCurves D₁ D₂ :=
  pullback.snd _ _ ≫ pullback.map _ _ _ _
    (D₁.e.hom ≫ Scheme.strictLocalizationToBase D₁.c)
    (D₂.e.hom ≫ Scheme.strictLocalizationToBase D₂.c) (𝟙 _)
    (by simpa only [Category.assoc, Category.comp_id] using D₁.e_over_k.symm)
    (by simpa only [Category.assoc, Category.comp_id] using D₂.e_over_k.symm)

/-- The canonical map from an affine target's coordinate ring into a source stalk.
Source: structure-sheaf germ and pullback of sections, used in blueprint proof (ii)
(blueprint: lem-trf-finite-trait-cover-product). -/
noncomputable def toStalk {X : Scheme.{u}} {A : CommRingCat.{u}}
    (f : X ⟶ Spec A) (t : X) : A →+* X.presheaf.stalk t :=
  (X.presheaf.germ ⊤ t trivial).hom.comp (f.appTop.hom.comp (Scheme.ΓSpecIso A).inv.hom)

/-- The map to the first covering trait.
Source: blueprint proof (ii) (blueprint: lem-trf-finite-trait-cover-product). -/
noncomputable def r₁ : chart D₁ D₂ ⟶ Spec D₁.A :=
  pullback.snd _ _ ≫ pullback.fst _ _

/-- The map to the second covering trait.
Source: blueprint proof (ii) (blueprint: lem-trf-finite-trait-cover-product). -/
noncomputable def r₂ : chart D₁ D₂ ⟶ Spec D₂.A :=
  pullback.snd _ _ ≫ pullback.snd _ _

/-- The canonical coefficient map k → O_(T',t').
Source: blueprint proof (ii) (blueprint: lem-trf-finite-trait-cover-product). -/
noncomputable def coefficients (t : chart D₁ D₂) : k →+* (chart D₁ D₂).presheaf.stalk t :=
  (toStalk (r₁ D₁ D₂) t).comp (algebraMap k D₁.A)

/-- The completed local ring, defined by the actual maximal-ideal adic completion.
Source: Stacks 0C0S (blueprint: lem-trf-finite-trait-cover-product). -/
noncomputable abbrev completion (t : chart D₁ D₂) :=
  AdicCompletion (maximalIdeal ((chart D₁ D₂).presheaf.stalk t))
    ((chart D₁ D₂).presheaf.stalk t)

/-- The product chart is local and strictly henselian, is the strict localization of
its smooth covering surface, and has the two specified uniformizers as parameters and
as power-series coordinates on its completion. Preservation of every adic filtration
term expresses continuity for the adic topologies; the coefficient equation expresses
that the ring isomorphism is a k-algebra isomorphism.

Source: Stacks 05WR, 0GIP, 0C0S; blueprint `det-tf-restriction-zero-covers`, proof (ii)
(blueprint: lem-trf-finite-trait-cover-product).

Proof:
1. Descend both covers to the supplied smooth covering curves. Strict-localization
   invariance for ind-étale maps identifies the strict localization of T' at the
   indicated closed point with that of the product of these curves. T' is affine
   finite over the strictly henselian surface T. Its closed fibre is the tensor
   product of two finite local k-algebras with nilpotent maximal ideals and residue
   field k. Their tensor product has nilpotent maximal ideal and quotient k, hence
   is local. The finite-over-henselian decomposition then has just one factor.
   Thus T' itself is local strictly henselian and equals that strict localization.
2. The covering surface is smooth of relative dimension two. Its local ring at the
   rational point is regular of dimension two, as is its strict henselization.
   Uniformizers in the two curve local rings generate the surface maximal ideal.
   Étale cotangent invariance and Nakayama carry this to the strict localizations.
   Any specified uniformizer differs from such a generator by a unit, so the two
   given images generate the maximal ideal and are a regular system of parameters.
3. Tensor bases for the finite free trait covers and then base change to T. The
   resulting finite flat rank is the product of the two ranks; no localization of
   the displayed fibre product is required.
4. Complete this Noetherian regular local ring. Completion preserves regularity,
   dimension, residue field, and the maximal-ideal generators. The canonical k-map
   is a coefficient field. Stacks 0C0S gives the continuous power-series map with
   these two variable images. Completeness gives surjectivity and regularity and
   dimension two give injectivity. It carries the variable-ideal powers exactly to
   the extended maximal-ideal powers, as recorded in the last clause. -/
theorem finite_trait_cover_product (D₁ D₂ : Cover k) :
    IsAffine (chart D₁ D₂) ∧
    ∃ t : chart D₁ D₂, IsClosed ({t} : Set (chart D₁ D₂)) ∧
      (∀ z : chart D₁ D₂, z ⤳ t) ∧
      IsStrictlyHenselianLocalRing ((chart D₁ D₂).presheaf.stalk t) ∧
      (∃ e : chart D₁ D₂ ≅ Scheme.strictLocalization (coveringPoint D₁ D₂),
        e.hom ≫ Scheme.strictLocalizationToBase (coveringPoint D₁ D₂) =
          toCoveringCurves D₁ D₂) ∧
      ∃ (_ : IsNoetherianRing ((chart D₁ D₂).presheaf.stalk t)),
        IsRegularLocalRing ((chart D₁ D₂).presheaf.stalk t) ∧
        ringKrullDim ((chart D₁ D₂).presheaf.stalk t) = 2 ∧
        ∀ (ξ : D₁.A) (η : D₂.A), Irreducible ξ → Irreducible η →
          IsRegularSystemOfParameters
            [toStalk (r₁ D₁ D₂) t ξ, toStalk (r₂ D₁ D₂) t η] ∧
          ∃ e : MvPowerSeries (Fin 2) k ≃+* completion D₁ D₂ t,
            (∀ a : k, e (MvPowerSeries.C a) =
              algebraMap _ (completion D₁ D₂ t) (coefficients D₁ D₂ t a)) ∧
            e (MvPowerSeries.X 0) =
              algebraMap _ (completion D₁ D₂ t) (toStalk (r₁ D₁ D₂) t ξ) ∧
            e (MvPowerSeries.X 1) =
              algebraMap _ (completion D₁ D₂ t) (toStalk (r₂ D₁ D₂) t η) ∧
            ∀ n : ℕ, Ideal.comap e.toRingHom
              ((maximalIdeal ((chart D₁ D₂).presheaf.stalk t)).map
                (algebraMap _ (completion D₁ D₂ t)) ^ n) =
              Ideal.span (Set.range (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) k)) ^ n := by
  sorry

end AlgebraicGeometry.FiniteTraitCoverProduct
