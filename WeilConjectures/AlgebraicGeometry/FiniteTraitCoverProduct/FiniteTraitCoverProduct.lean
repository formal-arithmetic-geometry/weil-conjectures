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
public import Mathlib.Algebra.Polynomial.Eval.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Smooth.IntegralClosure
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import WeilConjectures.Algebra.Category.ModuleCat.FilteredColimitFlat
public import WeilConjectures.AlgebraicGeometry.Curve.BoundaryNeighbourhood
public import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.GeometricFiberEtaleCount
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.SmallStrictHenselizationIndEtale
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselianFiniteAlgebraFactor
public import WeilConjectures.AlgebraicGeometry.Strict.Henselization.StrictHenselizationCanonicalMap
public import WeilConjectures.AlgebraicGeometry.Strict.Henselization.StrictHenselizationClosedFiberComparison
public import WeilConjectures.AlgebraicGeometry.Strict.Henselization.StrictHenselizationClosedLift
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import WeilConjectures.RingTheory.AdicCompletionNoetherian
public import WeilConjectures.RingTheory.ClosedPointDimensionLocalRing
public import WeilConjectures.RingTheory.CompletionDimension
public import WeilConjectures.RingTheory.CompletionRegularLocal
public import WeilConjectures.RingTheory.FilteredColimitAlgebrasTensorElementwise
public import WeilConjectures.RingTheory.FiniteLocalHenselian
public import WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct
public import WeilConjectures.RingTheory.FinitePresentationDescent
public import WeilConjectures.RingTheory.IsStrictHenselization
public import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
public import WeilConjectures.RingTheory.PowerSeriesUniversalPropertyComplete
public import WeilConjectures.RingTheory.ProEtale.HenselianLocalRing
public import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleStability
public import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleUniverseTransport
public import WeilConjectures.RingTheory.ProperBaseChange.SmoothOverFieldRegularLocal
public import WeilConjectures.RingTheory.StrictHenselizationCotangentDimension
public import WeilConjectures.RingTheory.StrictHenselizationDimension
public import WeilConjectures.RingTheory.StrictHenselizationNoetherian
public import WeilConjectures.RingTheory.StrictHenselizationRegular
public import WeilConjectures.RingTheory.StrictHenselizationTrait
public import WeilConjectures.RingTheory.StrictHenselizationTriples
public import WeilConjectures.TraceFormula.CurveLocal.CoverCurves

/-!
# Equal-degree finite trait covers and their product

Source: blueprint `det-tf-restriction-zero-covers`, clause (ii), with the
normalization input from proof (i) (blueprint: lem-trf-finite-trait-cover-product).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing

namespace AlgebraicGeometry.FiniteTraitCoverProduct

/-- A smooth pointed curve over an algebraically closed field.
Source: blueprint `det-tf-restriction-zero-covers`, clause (ii)
(blueprint: lem-trf-finite-trait-cover-product). -/
structure CurvePoint (k : Type u) [Field k] [IsAlgClosed k] where
  C : Scheme.{u}
  f : C ⟶ Spec (.of k)
  curve : IsCurve f
  smooth : Smooth f
  relativeDimension : SmoothOfRelativeDimension 1 f
  x : Spec (.of k) ⟶ C
  x_f : x ≫ f = 𝟙 _

attribute [instance] CurvePoint.curve CurvePoint.smooth CurvePoint.relativeDimension

attribute [instance] Cover.alg Cover.domain Cover.noetherian Cover.dvr Cover.regular
attribute [instance] Cover.strictlyHenselian Cover.Salg Cover.Sdomain Cover.Snoetherian
attribute [instance] Cover.Sdvr Cover.Sregular Cover.SstrictlyHenselian Cover.SalgK
attribute [instance] Cover.extensionField Cover.fractionAlgebra Cover.separable
attribute [instance] Cover.finiteExtension Cover.extensionAlgebra Cover.fractionTower

variable {k : Type u} [Field k] [IsAlgClosed k] (D₁ D₂ : Cover k)

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

/-- The marked point on the product of the base curves.
Source: blueprint proof (ii) (blueprint: lem-trf-finite-trait-cover-product). -/
noncomputable def basePoint : Spec (.of k) ⟶ pullback D₁.base.f D₂.base.f :=
  pullback.lift D₁.base.x D₂.base.x
    (D₁.base.x_f.trans D₂.base.x_f.symm)

/-- The strict local surface of the product of the base curves.
Source: blueprint proof (ii) (blueprint: lem-trf-finite-trait-cover-product). -/
noncomputable abbrev surface : Scheme.{u} :=
  Scheme.strictLocalization (basePoint D₁ D₂)

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

/-- The completed local ring at a point of the product.
Source: Stacks Tag 0C0S (blueprint: lem-trf-finite-trait-cover-product). -/
noncomputable abbrev completion (t : product D₁ D₂) :=
  AdicCompletion (maximalIdeal ((product D₁ D₂).presheaf.stalk t))
    ((product D₁ D₂).presheaf.stalk t)

/-- The coefficient map from the ground field to a product stalk.
Source: blueprint proof (ii) (blueprint: lem-trf-finite-trait-cover-product). -/
noncomputable def coefficients (t : product D₁ D₂) : k →+* (product D₁ D₂).presheaf.stalk t :=
  (toStalk (pullback.snd _ _ ≫ pullback.fst _ _) t).comp (algebraMap k D₁.S)

private theorem rational_point_unique {R : CommRingCat.{u}} [IsLocalRing R]
    (b : Spec R ⟶ Spec (.of k)) (s t : Spec (.of k) ⟶ Spec R)
    (hs : s ≫ b = 𝟙 _) (ht : t ≫ b = 𝟙 _) : s = t := by
  let i := (Spec.preimage b).hom
  let ε := (Spec.preimage s).hom
  let δ := (Spec.preimage t).hom
  have he : ε.comp i = RingHom.id k := by
    have h : Spec.preimage b ≫ Spec.preimage s = 𝟙 _ := by
      apply Spec.map_injective
      simpa only [Spec.map_comp, Spec.map_preimage, Spec.map_id] using hs
    exact congrArg CommRingCat.Hom.hom h
  have hd : δ.comp i = RingHom.id k := by
    have h : Spec.preimage b ≫ Spec.preimage t = 𝟙 _ := by
      apply Spec.map_injective
      simpa only [Spec.map_comp, Spec.map_preimage, Spec.map_id] using ht
    exact congrArg CommRingCat.Hom.hom h
  have hε (a : k) : ε (i a) = a := RingHom.congr_fun he a
  have hδ (a : k) : δ (i a) = a := RingHom.congr_fun hd a
  have hkerε : RingHom.ker ε = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective ε
      (fun a => ⟨i a, hε a⟩))
  have hkerδ : RingHom.ker δ = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective δ
      (fun a => ⟨i a, hδ a⟩))
  rw [← Spec.map_preimage s, ← Spec.map_preimage t]
  congr 1
  ext r
  have hr : r - i (ε r) ∈ RingHom.ker ε := by
    change ε (r - i (ε r)) = 0
    rw [map_sub, hε, sub_self]
  rw [hkerε, ← hkerδ, RingHom.mem_ker, map_sub, hδ, sub_eq_zero] at hr
  exact hr.symm

private theorem normalization_chart
    (C : Scheme.{u}) (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (x : Spec (.of k) ⟶ C) (hx : x ≫ f = 𝟙 _)
    (A S : CommRingCat.{u}) [IsDomain A] [Algebra A S]
    (β : Scheme.strictHenselizationRing x ≃+* A)
    (L : Type u) [Field L] [Algebra A L]
    [Algebra (FractionRing A) L] [IsScalarTower A (FractionRing A) L]
    [Module.Finite (FractionRing A) L] [Algebra.IsSeparable (FractionRing A) L]
    (eS : S ≃ₐ[A] integralClosure A L) :
    ∃ (C₀ C₁ : Scheme.{u}) (j : C₀ ⟶ C) (g : C₁ ⟶ C₀)
      (_c₀ : Spec (.of k) ⟶ C₀) (c : Spec (.of k) ⟶ C₁),
      Etale j ∧ IsCurve (g ≫ j ≫ f) ∧ Smooth (g ≫ j ≫ f) ∧ IsFinite g ∧
      c ≫ g ≫ j = x ∧
      ∃ e : Spec S ≅ Scheme.strictLocalization c,
        e.hom ≫ Scheme.strictLocalizationToBase c ≫ g ≫ j =
          Spec.map (CommRingCat.ofHom (algebraMap A S)) ≫
            Spec.map (CommRingCat.ofHom β.toRingHom) ≫
              Scheme.strictHenselizationStructuralMap x := by
  classical
  let R := Scheme.strictHenselizationRing x
  let : Algebra R A := β.toRingHom.toAlgebra
  let fracAlg : Algebra R (FractionRing A) :=
    ((algebraMap A (FractionRing A)).comp β.toRingHom).toAlgebra
  let : SMul R (FractionRing A) := fracAlg.toSMul
  let : IsFractionRing R (FractionRing A) :=
    IsFractionRing.of_ringEquiv_left β (fun _ => rfl)
  let : Algebra R L := ((algebraMap A L).comp β.toRingHom).toAlgebra
  let : IsScalarTower R (FractionRing A) L := .of_algebraMap_eq fun r => by
    change algebraMap A L (β r) =
      algebraMap (FractionRing A) L (algebraMap A (FractionRing A) (β r))
    exact IsScalarTower.algebraMap_apply A (FractionRing A) L _
  let J : integralClosure R L ≃+* integralClosure A L :=
    { toFun := fun z => ⟨z.1, (β.isIntegral_iff rfl z.1).mp z.2⟩
      invFun := fun z => ⟨z.1, (β.isIntegral_iff rfl z.1).mpr z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  let θ := J.trans eS.symm.toRingEquiv
  have hθ (r : R) : θ (algebraMap R (integralClosure R L) r) =
      algebraMap A S (β r) := by
    exact eS.symm.commutes (β r)
  obtain ⟨_, _, _, _, _, hnorm⟩ :=
    Scheme.separable_strict_trait_normalization k C f x hx
  obtain ⟨_, _, _, _, _, _, _, _, _, C₀, C₁, j, g, c₀, c,
    hj, _, _, hcurve, hsmooth, hg, h₁, h₀, e₀, e₁, he₀, he₁⟩ :=
    hnorm (FractionRing A) L
  have : IsIso (CommRingCat.ofHom (e₁.trans θ).toRingHom) :=
    (e₁.trans θ).toCommRingCatIso.isIso_hom
  let e : Spec S ≅ Scheme.strictLocalization c :=
    asIso (Spec.map (CommRingCat.ofHom (e₁.trans θ).toRingHom)) ≪≫
      asIso (Spec.map (Scheme.smallStrictHenselizationColimitIso c).inv)
  have square :
      Spec.map (CommRingCat.ofHom (e₁.trans θ).toRingHom) ≫
        Scheme.strictHenselizationMap g c =
      Spec.map (CommRingCat.ofHom ((algebraMap A S).comp β.toRingHom)) ≫
        Spec.map (CommRingCat.ofHom e₀.toRingHom) ≫
          Spec.map (eqToHom (congrArg Scheme.strictHenselizationRing h₁)) := by
    rw [← Spec.map_preimage (Scheme.strictHenselizationMap g c)]
    simp only [← Spec.map_comp]
    congr 1
    ext r
    change θ (e₁ ((Spec.preimage (Scheme.strictHenselizationMap g c)).hom r)) = _
    rw [he₁, hθ]
    rfl
  have transport {Z : Scheme.{u}} {a b : Spec (.of k) ⟶ Z} (h : a = b) :
      Spec.map (eqToHom (congrArg Scheme.strictHenselizationRing h)) ≫
        Scheme.strictHenselizationStructuralMap a =
      Scheme.strictHenselizationStructuralMap b := by
    subst b
    simp
  have hb : Spec.map (CommRingCat.ofHom e₀.toRingHom) ≫
      Scheme.strictHenselizationStructuralMap c₀ ≫ j =
      Scheme.strictHenselizationStructuralMap x := by
    rw [← Scheme.strictHenselizationMap_over j c₀, ← Category.assoc, he₀]
    have spec_transport {Z : Scheme.{u}} {a b : Spec (.of k) ⟶ Z} (h : a = b) :
        Spec.map (eqToHom (congrArg Scheme.strictHenselizationRing h)) =
          eqToHom (congrArg Scheme.strictHenselizationScheme h.symm) := by
      subst b
      exact Spec.map_id _
    rw [← spec_transport h₀]
    exact transport h₀
  refine ⟨C₀, C₁, j, g, c₀, c, hj, hcurve, hsmooth, hg, ?_, e, ?_⟩
  · rw [← Category.assoc, h₁, h₀]
  · have hsmall : e.hom ≫ Scheme.strictLocalizationToBase c =
        Spec.map (CommRingCat.ofHom (e₁.trans θ).toRingHom) ≫
          Scheme.strictHenselizationStructuralMap c := by
      simpa only [e, Iso.trans_hom, asIso_hom, Category.assoc] using
        congrArg (fun z ↦ Spec.map (CommRingCat.ofHom (e₁.trans θ).toRingHom) ≫ z)
          (Scheme.smallStrictHenselizationColimitIso_toBase c)
    calc
      _ = Spec.map (CommRingCat.ofHom (e₁.trans θ).toRingHom) ≫
          Scheme.strictHenselizationStructuralMap c ≫ g ≫ j := by
        simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ g ≫ j) hsmall
      _ = (Spec.map (CommRingCat.ofHom (e₁.trans θ).toRingHom) ≫
          Scheme.strictHenselizationMap g c) ≫
            Scheme.strictHenselizationStructuralMap (c ≫ g) ≫ j := by
        simpa only [Category.assoc] using
          congrArg (fun z ↦ Spec.map (CommRingCat.ofHom (e₁.trans θ).toRingHom) ≫ z ≫ j)
            (Scheme.strictHenselizationMap_over g c).symm
      _ = Spec.map (CommRingCat.ofHom ((algebraMap A S).comp β.toRingHom)) ≫
          Spec.map (CommRingCat.ofHom e₀.toRingHom) ≫
            Spec.map (eqToHom (congrArg Scheme.strictHenselizationRing h₁)) ≫
              Scheme.strictHenselizationStructuralMap (c ≫ g) ≫ j := by
        rw [square]
        simp only [Category.assoc]
      _ = Spec.map (CommRingCat.ofHom ((algebraMap A S).comp β.toRingHom)) ≫
          Scheme.strictHenselizationStructuralMap x := by
        rw [reassoc_of% transport h₁, hb]
      _ = _ := by
        exact (congrArg (fun z ↦ z ≫ Scheme.strictHenselizationStructuralMap x)
          (Spec.map_comp (CommRingCat.ofHom β.toRingHom)
            (CommRingCat.ofHom (algebraMap A S)))).trans (Category.assoc _ _ _)

private structure Descent (D : Cover k) where
  U : Scheme.{u}
  j : U ⟶ D.base.C
  etale_j : Etale j
  C' : Scheme.{u}
  g : C' ⟶ U
  finite_g : IsFinite g
  covering_curve : IsCurve (g ≫ j ≫ D.base.f)
  smooth_cover : Smooth (g ≫ j ≫ D.base.f)
  c : Spec (.of k) ⟶ C'
  c_g_j : c ≫ (g ≫ j) = D.base.x
  e : Spec D.S ≅ Scheme.strictLocalization c
  over_base : e.hom ≫ Scheme.strictLocalizationToBase c ≫ g ≫ j =
    D.p ≫ Scheme.strictLocalizationToBase D.base.x

private theorem descent_over_k (D : Cover k) (E : Descent D) :
    E.e.hom ≫ Scheme.strictLocalizationToBase E.c ≫ E.g ≫ E.j ≫ D.base.f =
      Spec.map (CommRingCat.ofHom (algebraMap k D.S)) := by
  calc
    _ = D.p ≫ Scheme.strictLocalizationToBase D.base.x ≫ D.base.f := by
      simpa only [Category.assoc] using congrArg (· ≫ D.base.f) E.over_base
    _ = _ := D.over_k

private theorem descent_point_over_k (D : Cover k) (E : Descent D) :
    E.c ≫ E.g ≫ E.j ≫ D.base.f = 𝟙 _ := by
  simpa only [Category.assoc] using
    (congrArg (· ≫ D.base.f) E.c_g_j).trans D.base.x_f

private noncomputable def descent_residue (D : Cover k) (E : Descent D) : D.S →ₐ[k] k where
  __ := (Spec.preimage (Spec.map (Scheme.strictHenselizationEval E.c) ≫ E.e.inv)).hom
  commutes' a := by
    have hp : (Spec.map (Scheme.strictHenselizationEval E.c) ≫ E.e.inv) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k D.S)) = 𝟙 _ := by
      rw [← descent_over_k D E, Category.assoc, Iso.inv_hom_id_assoc,
        ← Category.assoc, Scheme.spec_map_strictHenselizationEval_comp_strictLocalizationToBase]
      exact descent_point_over_k D E
    have hi : CommRingCat.ofHom (algebraMap k D.S) ≫
        Spec.preimage (Spec.map (Scheme.strictHenselizationEval E.c) ≫ E.e.inv) = 𝟙 _ := by
      apply Spec.map_injective
      simpa only [Spec.map_comp, Spec.map_preimage, Spec.map_id] using hp
    exact congrArg (fun f : CommRingCat.of k ⟶ CommRingCat.of k => f.hom a) hi

private theorem descent_residue_ker (D : Cover k) (E : Descent D) :
    RingHom.ker (descent_residue D E).toRingHom = maximalIdeal D.S :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _
    (fun a => ⟨algebraMap k D.S a, (descent_residue D E).commutes a⟩))

private theorem degree_basechange {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ Y)
    (d : ℕ) [f.IsFiniteLocallyFreeOfDegree d] :
    (pullback.fst g f).IsFiniteLocallyFreeOfDegree d := by
  have : (pullback.fst g f).IsFiniteLocallyFree := ⟨⟩
  exact ⟨fun z => (f.fiberDegree_of_isPullback
    (IsPullback.of_hasPullback g f).flip z).trans
      (Scheme.Hom.IsFiniteLocallyFreeOfDegree.fiberDegree_eq _)⟩

private theorem fiberDegree_sections {X T : Scheme.{u}} [IsAffine X] [IsAffine T]
    (f : X ⟶ T) [IsFinite f] [Flat f] (t : T) :
    let : Algebra Γ(T, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    f.fiberDegree t = Module.rankAtStalk Γ(X, ⊤) (T.isoSpec.hom t) := by
  let : Algebra Γ(T, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  have : Module.Finite Γ(T, ⊤) Γ(X, ⊤) := f.finite_appTop
  have : Module.Flat Γ(T, ⊤) Γ(X, ⊤) := f.flat_appTop
  let s := Spec.map f.appTop
  have H : IsPullback X.isoSpec.inv s f T.isoSpec.inv :=
    IsPullback.of_horiz_isIso ⟨(Scheme.isoSpec_inv_naturality f).symm⟩
  have h := f.fiberDegree_of_isPullback H (T.isoSpec.hom t)
  rw [Scheme.hom_inv_apply] at h
  rw [← h]
  change (Spec.map (CommRingCat.ofHom (algebraMap Γ(T, ⊤) Γ(X, ⊤)))).fiberDegree _ = _
  rw [Scheme.Hom.fiberDegree_SpecMap]
  exact Ideal.finrank_fiber_eq_rankAtStalk _

private theorem degree_product {P X Y T : Scheme.{u}}
    [IsAffine X] [IsAffine Y] [IsAffine T]
    (a : P ⟶ X) (b : P ⟶ Y) (f : X ⟶ T) (g : Y ⟶ T)
    (H : IsPullback a b f g) (n m : ℕ)
    [f.IsFiniteLocallyFreeOfDegree n] [g.IsFiniteLocallyFreeOfDegree m] :
    (a ≫ f).IsFiniteLocallyFreeOfDegree (n * m) := by
  have : IsFinite a := by rw [← H.isoPullback_hom_fst]; infer_instance
  have : Flat a := by rw [← H.isoPullback_hom_fst]; infer_instance
  have : LocallyOfFinitePresentation a := by
    rw [← H.isoPullback_hom_fst]; infer_instance
  have : IsAffine P := isAffine_of_isAffineHom a
  have : (a ≫ f).IsFiniteLocallyFree := ⟨⟩
  let R := Γ(T, ⊤)
  let B := Γ(X, ⊤)
  let C := Γ(Y, ⊤)
  let Q := Γ(P, ⊤)
  let : Algebra R B := f.appTop.hom.toAlgebra
  let : Algebra R C := g.appTop.hom.toAlgebra
  let : Algebra R Q := (a ≫ f).appTop.hom.toAlgebra
  let : Algebra B Q := a.appTop.hom.toAlgebra
  let : Algebra C Q := b.appTop.hom.toAlgebra
  have : IsScalarTower R B Q := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R C Q := .of_algebraMap_eq fun r => by
    change (a ≫ f).appTop.hom r = (g.appTop ≫ b.appTop).hom r
    rw [H.w, Scheme.Hom.comp_appTop]
  have : Module.Finite R B := f.finite_appTop
  have : Module.Finite R C := g.finite_appTop
  have : Module.Flat R B := f.flat_appTop
  have : Module.Flat R C := g.flat_appTop
  have : Algebra.IsPushout R B C Q :=
    CommRingCat.isPushout_iff_isPushout.mp (isPushout_appTop_of_isPullback H)
  let e : B ⊗[R] C ≃ₗ[R] Q :=
    ((Algebra.IsPushout.equiv R B C Q).restrictScalars R).toLinearEquiv
  refine ⟨fun t => ?_⟩
  rw [fiberDegree_sections]
  change Module.rankAtStalk Q (T.isoSpec.hom t) = n * m
  rw [← Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_tensorProduct]
  change Module.rankAtStalk B (T.isoSpec.hom t) *
    Module.rankAtStalk C (T.isoSpec.hom t) = n * m
  rw [← fiberDegree_sections f t, ← fiberDegree_sections g t,
    Scheme.Hom.IsFiniteLocallyFreeOfDegree.fiberDegree_eq (f := f) (d := n),
    Scheme.Hom.IsFiniteLocallyFreeOfDegree.fiberDegree_eq (f := g) (d := m)]

private theorem coverMap_degree (D₁ D₂ : Cover k) :
    (coverMap D₁ D₂).IsFiniteLocallyFreeOfDegree (D₁.degree * D₂.degree) := by
  let := D₁.finiteFlat
  let := D₂.finiteFlat
  let f₁ := Scheme.strictLocalizationToBase D₁.base.x ≫ D₁.base.f
  let f₂ := Scheme.strictLocalizationToBase D₂.base.x ≫ D₂.base.f
  let a₁ := Spec.map (CommRingCat.ofHom (algebraMap k D₁.S))
  let a₂ := Spec.map (CommRingCat.ofHom (algebraMap k D₂.S))
  let π₁ := pullback.fst (pullback.fst f₁ f₂) D₁.p
  let π₂ := pullback.fst (pullback.snd f₁ f₂) D₂.p
  let := degree_basechange D₁.p (pullback.fst f₁ f₂) D₁.degree
  let := degree_basechange D₂.p (pullback.snd f₁ f₂) D₂.degree
  have H := pullback_lift_map_isPullback a₁ a₂ f₁ f₂ D₁.p D₂.p (𝟙 _)
    D₁.over_k.symm D₂.over_k.symm
  have hdeg := degree_product _ _ π₁ π₂ H D₁.degree D₂.degree
  simpa only [π₁, pullback.lift_fst, coverMap, f₁, f₂, a₁, a₂] using hdeg

private theorem product_degree (D₁ D₂ : Cover k) (hdegree : D₁.degree = D₂.degree) :
    (pullback.fst (surfaceMap D₁ D₂) (coverMap D₁ D₂)).IsFiniteLocallyFreeOfDegree
      (D₁.degree * D₁.degree) := by
  let := coverMap_degree D₁ D₂
  simpa only [hdegree] using
    degree_basechange (coverMap D₁ D₂) (surfaceMap D₁ D₂) (D₁.degree * D₂.degree)

/-- The product chart is local and strictly henselian, is the strict localization of
its smooth covering model_surface, and has the two specified uniformizers as parameters and
as power-series coordinates on its model_completion. Preservation of every adic filtration
term expresses continuity for the adic topologies; the coefficient equation expresses
that the ring isomorphism is a k-algebra isomorphism.

Source: Stacks 05WR, 0GIP, 0C0S; blueprint `det-tf-restriction-zero-covers`, proof (ii)
(blueprint: lem-trf-finite-trait-cover-product).

Proof:
1. The chart is finite over the affine strict local base. Each closed-fibre rational
   point is the pair of the two residue points, hence its closed fibre is a singleton.
   Its affine coordinate ring is local. The strictly henselian idempotent-factor
   criterion makes this finite local algebra strictly henselian.
2. Construct inverse chart comparisons using the universal property of strict
   localization and the defining pullback. This identifies the chart both with the
   strict localization of the covering-curve product and with that of the affine-trait
   product, compatibly with the corresponding structural maps.
3. Smooth neighbourhoods of the covering points have relative dimension one, since
   their strict henselizations are the supplied DVRs. Their product is smooth of
   relative dimension two. The source-library smooth strict-henselization theorem
   gives regularity and dimension two. On the affine-trait product, the source-library
   product-parameter theorem applies directly to any specified uniformizers. Transport
   its ideal equality to the chart's closed-point stalk, tracking the two generators
   by the tensor projections and naturality of the germ map.
4. The rational point retracts the specified coefficient map, which therefore
   identifies k with the residue field. Completion preserves this residue field,
   regularity, dimension and the maximal-ideal generators. Apply the complete regular
   local coefficient-coordinate theorem to the specified coefficient map and these
   two parameters. Its coefficient, variable and ideal-power equations give the
   asserted isomorphism. -/
private theorem model_finite_trait_cover_product (M₁ M₂ : ModelCover k) :
    IsAffine (chart M₁ M₂) ∧
    ∃ t : chart M₁ M₂, IsClosed ({t} : Set (chart M₁ M₂)) ∧
      (∀ z : chart M₁ M₂, z ⤳ t) ∧
      IsStrictlyHenselianLocalRing ((chart M₁ M₂).presheaf.stalk t) ∧
      (∃ e : chart M₁ M₂ ≅ Scheme.strictLocalization (coveringPoint M₁ M₂),
        e.hom ≫ Scheme.strictLocalizationToBase (coveringPoint M₁ M₂) =
          toCoveringCurves M₁ M₂) ∧
      ∃ (_ : IsNoetherianRing ((chart M₁ M₂).presheaf.stalk t)),
        IsRegularLocalRing ((chart M₁ M₂).presheaf.stalk t) ∧
        ringKrullDim ((chart M₁ M₂).presheaf.stalk t) = 2 ∧
        ∀ (ξ : M₁.A) (η : M₂.A), Irreducible ξ → Irreducible η →
          IsRegularSystemOfParameters
            [model_toStalk (r₁ M₁ M₂) t ξ, model_toStalk (r₂ M₁ M₂) t η] ∧
          ∃ e : MvPowerSeries (Fin 2) k ≃+* model_completion M₁ M₂ t,
            (∀ a : k, e (MvPowerSeries.C a) =
              algebraMap _ (model_completion M₁ M₂ t) (model_coefficients M₁ M₂ t a)) ∧
            e (MvPowerSeries.X 0) =
              algebraMap _ (model_completion M₁ M₂ t) (model_toStalk (r₁ M₁ M₂) t ξ) ∧
            e (MvPowerSeries.X 1) =
              algebraMap _ (model_completion M₁ M₂ t) (model_toStalk (r₂ M₁ M₂) t η) ∧
            ∀ n : ℕ, Ideal.comap e.toRingHom
              ((maximalIdeal ((chart M₁ M₂).presheaf.stalk t)).map
                (algebraMap _ (model_completion M₁ M₂ t)) ^ n) =
              Ideal.span (Set.range (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) k)) ^ n := by
  let P := chart M₁ M₂
  let t := P.isoSpec.inv (closedPoint Γ(P, ⊤))
  let R := P.presheaf.stalk t
  have := (chart_regular M₁ M₂).1
  have : IsRegularLocalRing R := .of_ringEquiv (stalkEquiv P).symm
  have : IsStrictlyHenselianLocalRing R := .of_ringEquiv (stalkEquiv P).symm
  have hdim : ringKrullDim R = 2 :=
    (ringKrullDim_eq_of_ringEquiv (stalkEquiv P)).trans (chart_regular M₁ M₂).2
  have hclosed : IsClosed ({t} : Set P) := by
    rw [show t = t₀ M₁ M₂ from canonical_point_eq M₁ M₂]
    exact t₀_closed M₁ M₂
  refine ⟨inferInstance, t, hclosed, ?_, inferInstance, exists_chart_iso M₁ M₂,
    inferInstance, inferInstance, hdim, ?_⟩
  · intro z
    have h := (specializes_closedPoint (P.isoSpec.hom z)).map P.isoSpec.inv.continuous
    have hz := Scheme.hom_inv_apply P.isoSpec z
    simpa only [hz] using h
  · intro ξ η hξ hη
    have hm : maximalIdeal R =
        Ideal.span {model_toStalk (r₁ M₁ M₂) t ξ, model_toStalk (r₂ M₁ M₂) t η} :=
      chart_parameters M₁ M₂ ξ η hξ hη
    constructor
    · constructor
      · change Ideal.span {z : R | z ∈
            [model_toStalk (r₁ M₁ M₂) t ξ, model_toStalk (r₂ M₁ M₂) t η]} = maximalIdeal R
        rw [show {z : R | z ∈ [model_toStalk (r₁ M₁ M₂) t ξ, model_toStalk (r₂ M₁ M₂) t η]} =
          {model_toStalk (r₁ M₁ M₂) t ξ, model_toStalk (r₂ M₁ M₂) t η} from by ext z; simp]
        exact hm.symm
      · change (2 : WithBot ℕ∞) = ringKrullDim R
        exact hdim.symm
    · let C := model_completion M₁ M₂ t
      let ι : R →+* C := algebraMap R C
      have : IsNoetherianRing C := AdicCompletion.isNoetherianRing (maximalIdeal R)
      have : IsRegularLocalRing C := (AdicCompletion.isRegularLocalRing_iff R).mp inferInstance
      have : IsAdicComplete (maximalIdeal C) C := inferInstance
      have hdimC : ringKrullDim C = (2 : WithBot ℕ∞) :=
        (RingTheory.completion_dimension R).1.trans hdim
      let c := ι.comp (model_coefficients M₁ M₂ t)
      have hresR : Function.Bijective ((residue R).comp (model_coefficients M₁ M₂ t)) := by
        exact coefficients_residue_at M₁ M₂ t (canonical_point_eq M₁ M₂)
      have hres : Function.Bijective ((residue C).comp c) := by
        have h := (AdicCompletion.residueField_map_bijective R).comp hresR
        exact h
      let xs : Fin 2 → C := ![ι (model_toStalk (r₁ M₁ M₂) t ξ),
        ι (model_toStalk (r₂ M₁ M₂) t η)]
      have hgen : Ideal.span (Set.range xs) = maximalIdeal C := by
        calc
          Ideal.span (Set.range xs) = Ideal.span
              {ι (model_toStalk (r₁ M₁ M₂) t ξ), ι (model_toStalk (r₂ M₁ M₂) t η)} := by
            simp only [xs, Matrix.range_cons_cons_empty]
          _ = (Ideal.span {model_toStalk (r₁ M₁ M₂) t ξ,
              model_toStalk (r₂ M₁ M₂) t η}).map ι := by
            rw [Ideal.map_span, Set.image_pair]
          _ = (maximalIdeal R).map ι := congrArg (Ideal.map ι) hm.symm
          _ = maximalIdeal C := (AdicCompletion.maximalIdeal_eq_map (R := R)).symm
      have hxs : ∀ i, xs i ∈ maximalIdeal C := fun i =>
        hgen ▸ Ideal.subset_span ⟨i, rfl⟩
      have hcoordinates :
          ∃ e : MvPowerSeries (Fin 2) k ≃+* C,
            (∀ a : k, e (MvPowerSeries.C a) = c a) ∧
            (∀ i : Fin 2, e (MvPowerSeries.X i) = xs i) ∧
            (∀ n : ℕ, Ideal.comap e.toRingHom (maximalIdeal C ^ n) =
              Ideal.span (Set.range (MvPowerSeries.X : Fin 2 →
                MvPowerSeries (Fin 2) k)) ^ n) := by
        exact (exists_ringEquiv_regular_complete_coefficients k C 2 hdimC
          c hres xs hxs hgen).1
      obtain ⟨e, heC, heX, heI⟩ := hcoordinates
      refine ⟨e, heC, heX 0, heX 1, ?_⟩
      intro n
      have hmax : maximalIdeal C = (maximalIdeal R).map ι :=
        AdicCompletion.maximalIdeal_eq_map
      simpa only [hmax] using heI n

private theorem coefficients_residue_at (M₁ M₂ : ModelCover k) (t :
    chart M₁ M₂) (ht : t = t₀ M₁ M₂) :
    Function.Bijective ((residue ((chart M₁ M₂).presheaf.stalk t)).comp
      (model_coefficients M₁ M₂ t)) := by
  subst t
  exact coefficients_residue M₁ M₂

private theorem canonical_point_eq (M₁ M₂ : ModelCover k) :
    (chart M₁ M₂).isoSpec.inv (closedPoint Γ(chart M₁ M₂, ⊤)) = t₀ M₁ M₂ := by
  apply closed_eq_t₀ M₁ M₂
  apply isClosed_singleton_of_isClosedImmersion (chart M₁ M₂).isoSpec.hom
  have hh := Scheme.hom_inv_apply (chart M₁ M₂).isoSpec.symm
    (closedPoint Γ(chart M₁ M₂, ⊤))
  rw [Iso.symm_hom, Iso.symm_inv] at hh
  rw [hh]
  exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr
    (maximalIdeal.isMaximal Γ(chart M₁ M₂, ⊤))

private theorem coefficients_residue (M₁ M₂ : ModelCover k) :
    Function.Bijective ((residue ((chart M₁ M₂).presheaf.stalk (t₀ M₁ M₂))).comp
      (model_coefficients M₁ M₂ (t₀ M₁ M₂))) := by
  apply coefficient_residue_bijective _ (Scheme.stalkClosedPointTo (closedLift M₁ M₂)).hom
  intro a
  have h := toStalk_comp (r₁ M₁ M₂) (closedLift M₁ M₂)
  rw [closedLift_r₁, Spec.preimage_map] at h
  have ha := congrArg (fun f : M₁.A ⟶ CommRingCat.of k => f (algebraMap k M₁.A a)) h
  have hb : M₁.residue.toRingHom (algebraMap k M₁.A a) = a := M₁.residue.commutes a
  simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, model_coefficients,
    t₀, RingHom.comp_apply] using ha.trans hb

private theorem coefficient_residue_bijective {R : Type u} [CommRing R] [IsLocalRing R]
    (c : k →+* R) (ψ : R →+* k) (hψ : ∀ a, ψ (c a) = a) :
    Function.Bijective ((residue R).comp c) := by
  have hs : Function.Surjective ψ := fun a => ⟨c a, hψ a⟩
  have hker := ker_eq_maximalIdeal ψ hs
  refine ⟨RingHom.injective _, ?_⟩
  intro z
  obtain ⟨r, rfl⟩ := residue_surjective z
  refine ⟨ψ r, ?_⟩
  change residue R (c (ψ r)) = residue R r
  apply sub_eq_zero.mp
  rw [← map_sub, residue_eq_zero_iff, ← hker, RingHom.mem_ker, map_sub, hψ, sub_self]

private theorem chart_parameters (M₁ M₂ : ModelCover k) (ξ : M₁.A) (η : M₂.A)
    (hξ : Irreducible ξ) (hη : Irreducible η) :
    let P := chart M₁ M₂
    let t := P.isoSpec.inv (closedPoint Γ(P, ⊤))
    maximalIdeal (P.presheaf.stalk t) =
      Ideal.span {model_toStalk (r₁ M₁ M₂) t ξ, model_toStalk (r₂ M₁ M₂) t η} := by
  let P := chart M₁ M₂
  let t := P.isoSpec.inv (closedPoint Γ(P, ⊤))
  let T := M₁.A ⊗[k] M₂.A
  let a₁ := Spec.map (CommRingCat.ofHom (algebraMap k M₁.A))
  let a₂ := Spec.map (CommRingCat.ofHom (algebraMap k M₂.A))
  obtain ⟨e, he⟩ := exists_traits_iso M₁ M₂
  let eS := P.isoSpec.symm ≪≫ e
  let eR := ringEquivOfSpecIso eS
  let E := eR.symm.trans (stalkEquiv P).symm
  have hξ' : RingHom.ker M₁.residue = Ideal.span {ξ} :=
    M₁.residue_ker.trans ((IsDiscreteValuationRing.irreducible_iff_uniformizer ξ).mp hξ)
  have hη' : RingHom.ker M₂.residue = Ideal.span {η} :=
    M₂.residue_ker.trans ((IsDiscreteValuationRing.irreducible_iff_uniformizer η).mp hη)
  obtain ⟨ρ, hρ, hm⟩ := Scheme.strictHenselization_maximalIdeal_eq_span_pair a₁ a₂
    (𝟙 (Spec M₁.A)) (𝟙 (Spec M₂.A)) (Category.id_comp _) (Category.id_comp _)
    M₁.residue M₂.residue hξ' hη' (traitsPoint M₁ M₂)
    (by simp only [traitsPoint, a₁, a₂, pullback.lift_fst, Category.comp_id])
    (by simp only [traitsPoint, a₁, a₂, pullback.lift_snd, Category.comp_id])
  have hρ' : Spec.map ρ = Scheme.strictLocalizationToBase (traitsPoint M₁ M₂) ≫
      (pullbackSpecIso k M₁.A M₂.A).hom := by
    rw [← hρ]
    simp only [Scheme.productChart, a₁, a₂, pullback.map_id, Category.comp_id,
      Category.assoc, Iso.inv_hom_id]
  let F : P ⟶ Spec (.of T) :=
    pullback.snd (model_surfaceMap M₁ M₂) (model_coverMap M₁ M₂) ≫
      (pullbackSpecIso k M₁.A M₂.A).hom
  have hF : eS.hom ≫ Spec.map ρ = P.isoSpec.inv ≫ F := by
    rw [hρ']
    change (P.isoSpec.inv ≫ e.hom) ≫ _ ≫ _ = _
    rw [Category.assoc, ← Category.assoc e.hom, he]
  have hR : Spec.preimage (P.isoSpec.inv ≫ F) =
      ρ ≫ Spec.preimage eS.hom := by
    apply Spec.map_injective
    simpa only [Spec.map_preimage, Spec.map_comp] using hF.symm
  have hE : ∀ z : T, E (ρ z) = model_toStalk F t z := by
    intro z
    apply (stalkEquiv P).injective
    have hz := congrArg (fun f : CommRingCat.of T ⟶ Γ(P, ⊤) => f z)
      ((toStalk_comp F P.isoSpec.inv).trans hR)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hz
    simpa only [E, eR, RingEquiv.trans_apply, RingEquiv.apply_symm_apply,
      ringEquivOfSpecIso_symm_apply, stalkEquiv_apply] using hz.symm
  have hF₁ : F ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft : M₁.A →ₐ[k] T).toRingHom) = r₁ M₁ M₂ := by
    dsimp only [F, r₁]
    rw [Category.assoc]
    change _ ≫ (pullbackSpecIso k M₁.A M₂.A).hom ≫
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) = _
    rw [pullbackSpecIso_hom_fst]
  have hF₂ : F ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : M₂.A →ₐ[k] T).toRingHom) = r₂ M₁ M₂ := by
    dsimp only [F, r₂]
    rw [Category.assoc]
    change _ ≫ (pullbackSpecIso k M₁.A M₂.A).hom ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        M₂.A →ₐ[k] M₁.A ⊗[k] M₂.A).toRingHom) = _
    exact congrArg (_ ≫ ·) (pullbackSpecIso_hom_snd k M₁.A M₂.A)
  have hE₁ : E (ρ (ξ ⊗ₜ[k] (1 : M₂.A))) = model_toStalk (r₁ M₁ M₂) t ξ := by
    rw [hE, ← hF₁, toStalk_spec_comp]
    rfl
  have hE₂ : E (ρ ((1 : M₁.A) ⊗ₜ[k] η)) = model_toStalk (r₂ M₁ M₂) t η := by
    rw [hE, ← hF₂, toStalk_spec_comp]
    rfl
  have := (chart_regular M₁ M₂).1
  have : IsRegularLocalRing (P.presheaf.stalk t) :=
    .of_ringEquiv (stalkEquiv P).symm
  have hh := congrArg (Ideal.map E.toRingHom) hm
  rw [map_maximalIdeal_of_surjective E.toRingHom E.surjective,
    Ideal.map_span, Set.image_pair] at hh
  change maximalIdeal (P.presheaf.stalk t) = _
  change maximalIdeal (P.presheaf.stalk t) =
    Ideal.span {E (ρ (ξ ⊗ₜ[k] 1)), E (ρ (1 ⊗ₜ[k] η))} at hh
  rw [hE₁, hE₂] at hh
  exact hh

private theorem toStalk_spec_comp {P : Scheme.{u}} {A B : CommRingCat.{u}}
    (f : P ⟶ Spec B) (h : A ⟶ B) (t : P) :
    model_toStalk (f ≫ Spec.map h) t = (model_toStalk f t).comp h.hom := by
  change (((Scheme.ΓSpecIso A).inv ≫ (f ≫ Spec.map h).appTop) ≫
    P.presheaf.germ ⊤ t trivial).hom =
    ((h ≫ (Scheme.ΓSpecIso B).inv ≫ f.appTop) ≫
      P.presheaf.germ ⊤ t trivial).hom
  rw [Scheme.Hom.comp_appTop, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality]
  simp only [Category.assoc]

private theorem toStalk_comp {P : Scheme.{u}} {A R : CommRingCat.{u}}
    [IsLocalRing R] (f : P ⟶ Spec A) (g : Spec R ⟶ P) :
    (CommRingCat.ofHom (model_toStalk f (g (closedPoint R)))) ≫
      Scheme.stalkClosedPointTo g = Spec.preimage (g ≫ f) := by
  change (((Scheme.ΓSpecIso A).inv ≫ f.appTop) ≫
    P.presheaf.germ ⊤ _ trivial) ≫ _ = _
  rw [Category.assoc, Scheme.germ_stalkClosedPointTo]
  simp only [Scheme.Hom.appTop, TopologicalSpace.Opens.map_top, eqToIso_refl,
    Iso.op_refl, Functor.mapIso_refl, Iso.refl_trans, Category.assoc]
  have h := Scheme.ΓSpecIso_inv_naturality (Spec.preimage (g ≫ f))
  rw [Spec.map_preimage, Scheme.Hom.comp_appTop] at h
  change (Scheme.ΓSpecIso A).inv ≫ f.appTop ≫ g.appTop ≫
    (Scheme.ΓSpecIso R).hom = _
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    (congrArg (· ≫ (Scheme.ΓSpecIso R).hom) h).symm

private theorem exists_traits_iso (M₁ M₂ : ModelCover k) :
    ∃ e : chart M₁ M₂ ≅ Scheme.strictLocalization (traitsPoint M₁ M₂),
      e.hom ≫ Scheme.strictLocalizationToBase (traitsPoint M₁ M₂) =
        pullback.snd (model_surfaceMap M₁ M₂) (model_coverMap M₁ M₂) := by
  let P := chart M₁ M₂
  let v := pullback.snd (model_surfaceMap M₁ M₂) (model_coverMap M₁ M₂)
  have hv : v ≫ traitsToCurves M₁ M₂ = toCoveringCurves M₁ M₂ := rfl
  have hpv : closedLift M₁ M₂ ≫ v = traitsPoint M₁ M₂ := by
    apply pullback.hom_ext
    · simpa only [v, traitsPoint, Category.assoc, pullback.lift_fst, r₁] using
        closedLift_r₁ M₁ M₂
    · simpa only [v, traitsPoint, Category.assoc, pullback.lift_snd, r₂] using
        closedLift_r₂ M₁ M₂
  let p₀ := closedLift M₁ M₂ ≫ P.isoSpec.hom
  have hp₀ : p₀ (closedPoint k) = closedPoint Γ(P, ⊤) := by
    apply IsLocalRing.eq_closedPoint_of_isClosed
    apply isClosed_singleton_of_isClosedImmersion P.isoSpec.inv
    simpa only [p₀, ← Scheme.Hom.comp_apply, Category.assoc, Iso.hom_inv_id,
      Category.comp_id] using t₀_closed M₁ M₂
  obtain ⟨κ, hκ, hpκ⟩ :=
    Scheme.exists_hom_strictLocalization_of_isStrictlyHenselianLocalRing
      (traitsPoint M₁ M₂) (P.isoSpec.inv ≫ v) p₀ hp₀ (by
        simpa only [p₀, Category.assoc, Iso.hom_inv_id_assoc] using hpv)
  have := Scheme.isStrictlyHenselianLocalRing_strictHenselization' (traitsPoint M₁ M₂)
  let q := Spec.map (Scheme.strictHenselizationEval (traitsPoint M₁ M₂))
  have hq := Scheme.spec_map_strictHenselizationEval_apply (traitsPoint M₁ M₂) (closedPoint k)
  obtain ⟨ℓ, hℓ, hpℓ⟩ := exists_hom_chart M₁ M₂ q hq
    (Scheme.strictLocalizationToBase (traitsPoint M₁ M₂) ≫ traitsToCurves M₁ M₂) (by
      rw [← Category.assoc,
        Scheme.spec_map_strictHenselizationEval_comp_strictLocalizationToBase]
      exact traitsPoint_curves M₁ M₂)
  have hℓv : ℓ ≫ v = Scheme.strictLocalizationToBase (traitsPoint M₁ M₂) := by
    apply traits_hom_ext M₁ M₂ q hq
    · simpa only [Category.assoc, hv] using hℓ
    · rw [← Category.assoc, hpℓ, hpv]
      exact (Scheme.spec_map_strictHenselizationEval_comp_strictLocalizationToBase _).symm
  let e : P ≅ Scheme.strictLocalization (traitsPoint M₁ M₂) :=
    { hom := P.isoSpec.hom ≫ κ
      inv := ℓ
      hom_inv_id := by
        rw [← cancel_epi P.isoSpec.inv]
        simp only [Category.assoc, Iso.inv_hom_id_assoc, Category.comp_id]
        apply hom_chart_ext M₁ M₂ p₀ hp₀
        · rw [Category.assoc, hℓ, ← Category.assoc, hκ, Category.assoc, hv]
        · rw [← Category.assoc, hpκ, hpℓ]
          simp only [p₀, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      inv_hom_id := by
        refine Scheme.hom_strictLocalization_ext (traitsPoint M₁ M₂) ?_ q
          (closedPoint k) hq ?_
        · rw [Category.assoc, Category.assoc, hκ, Iso.hom_inv_id_assoc,
            hℓv, Category.id_comp]
        · rw [reassoc_of% hpℓ]
          simpa only [p₀, Category.assoc, Category.comp_id] using hpκ }
  refine ⟨e, ?_⟩
  change (P.isoSpec.hom ≫ κ) ≫ _ = _
  rw [Category.assoc, hκ, Iso.hom_inv_id_assoc]

private theorem traits_hom_ext (M₁ M₂ : ModelCover k) {R : CommRingCat.{u}} [IsLocalRing R]
    (p₀ : Spec (.of k) ⟶ Spec R) (hp₀ : p₀ (closedPoint k) = closedPoint R)
    {a b : Spec R ⟶ model_coverTraits M₁ M₂}
    (h : a ≫ traitsToCurves M₁ M₂ = b ≫ traitsToCurves M₁ M₂)
    (hp : p₀ ≫ a = p₀ ≫ b) : a = b := by
  apply pullback.hom_ext
  · rw [← cancel_mono M₁.e.hom]
    refine Scheme.hom_strictLocalization_ext M₁.c ?_ p₀ (closedPoint k) hp₀ ?_
    · simpa only [traitsToCurves, pullback.map, Category.assoc, pullback.lift_fst] using
        congrArg (· ≫ pullback.fst (M₁.g ≫ M₁.j ≫ M₁.f) (M₂.g ≫ M₂.j ≫ M₂.f)) h
    · rw [Category.assoc, Category.assoc, reassoc_of% hp]
  · rw [← cancel_mono M₂.e.hom]
    refine Scheme.hom_strictLocalization_ext M₂.c ?_ p₀ (closedPoint k) hp₀ ?_
    · simpa only [traitsToCurves, pullback.map, Category.assoc, pullback.lift_snd] using
        congrArg (· ≫ pullback.snd (M₁.g ≫ M₁.j ≫ M₁.f) (M₂.g ≫ M₂.j ≫ M₂.f)) h
    · rw [Category.assoc, Category.assoc, reassoc_of% hp]

private theorem traitsPoint_curves (M₁ M₂ : ModelCover k) :
    traitsPoint M₁ M₂ ≫ traitsToCurves M₁ M₂ = coveringPoint M₁ M₂ := by
  apply pullback.hom_ext <;>
    simp only [traitsPoint, traitsToCurves, coveringPoint, Category.assoc,
      pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc, reassoc_of% point_e M₁, reassoc_of% point_e M₂,
      Scheme.spec_map_strictHenselizationEval_comp_strictLocalizationToBase]

private noncomputable def traitsPoint (M₁ M₂ : ModelCover k) :
    Spec (.of k) ⟶ model_coverTraits M₁ M₂ :=
  pullback.lift (Spec.map (CommRingCat.ofHom M₁.residue.toRingHom))
    (Spec.map (CommRingCat.ofHom M₂.residue.toRingHom)) (by rw [residue_comp, residue_comp])

private noncomputable def traitsToCurves (M₁ M₂ : ModelCover k) :
    model_coverTraits M₁ M₂ ⟶ coveringCurves M₁ M₂ :=
  pullback.map _ _ _ _ (M₁.e.hom ≫ Scheme.strictLocalizationToBase M₁.c)
    (M₂.e.hom ≫ Scheme.strictLocalizationToBase M₂.c) (𝟙 _)
    (by simpa only [Category.assoc, Category.comp_id] using M₁.e_over_k.symm)
    (by simpa only [Category.assoc, Category.comp_id] using M₂.e_over_k.symm)

private theorem chart_regular (M₁ M₂ : ModelCover k) :
    IsRegularLocalRing Γ(chart M₁ M₂, ⊤) ∧ ringKrullDim Γ(chart M₁ M₂, ⊤) = 2 := by
  obtain ⟨e, _⟩ := exists_chart_iso M₁ M₂
  let eR := ringEquivOfSpecIso ((chart M₁ M₂).isoSpec.symm ≪≫ e)
  obtain ⟨hreg, hdim⟩ := covering_regular M₁ M₂
  exact ⟨.of_ringEquiv eR.symm, (ringKrullDim_eq_of_ringEquiv eR).trans hdim⟩

private theorem stalkEquiv_apply (P : Scheme.{u}) [IsAffine P]
    [IsLocalRing Γ(P, ⊤)] (a : P.presheaf.stalk
      (P.isoSpec.inv (closedPoint Γ(P, ⊤)))) :
    stalkEquiv P a = (Scheme.stalkClosedPointTo P.isoSpec.inv).hom a := rfl

private theorem ringEquivOfSpecIso_symm_apply {A B : CommRingCat.{u}}
    (e : Spec A ≅ Spec B) (b : B) :
    (ringEquivOfSpecIso e).symm b = (Spec.preimage e.hom).hom b := rfl

private noncomputable def stalkEquiv (P : Scheme.{u}) [IsAffine P]
    [IsLocalRing Γ(P, ⊤)] :
    P.presheaf.stalk (P.isoSpec.inv (closedPoint Γ(P, ⊤))) ≃+* Γ(P, ⊤) :=
  ((asIso (P.isoSpec.inv.stalkMap (closedPoint Γ(P, ⊤)))) ≪≫
    stalkClosedPointIso Γ(P, ⊤)).commRingCatIsoToRingEquiv

private theorem covering_regular (M₁ M₂ : ModelCover k) :
    IsRegularLocalRing (Scheme.strictHenselization (coveringPoint M₁ M₂)) ∧
      ringKrullDim (Scheme.strictHenselization (coveringPoint M₁ M₂)) = 2 := by
  obtain ⟨V₁, c₁, hc₁, h₁⟩ := curve_neighborhood M₁
  obtain ⟨V₂, c₂, hc₂, h₂⟩ := curve_neighborhood M₂
  let f₁ := V₁.ι ≫ M₁.g ≫ M₁.j ≫ M₁.f
  let f₂ := V₂.ι ≫ M₂.g ≫ M₂.j ≫ M₂.f
  let j : pullback f₁ f₂ ⟶ coveringCurves M₁ M₂ :=
    pullback.map _ _ _ _ V₁.ι V₂.ι (𝟙 _) (by simp [f₁]) (by simp [f₂])
  have : IsOpenImmersion j := by dsimp [j]; infer_instance
  let c : Spec (.of k) ⟶ pullback f₁ f₂ := pullback.lift c₁ c₂ (by
    simp only [f₁, f₂, ← Category.assoc, hc₁, hc₂]
    simp only [Category.assoc, coveringPoint_to_k])
  have hc : c ≫ j = coveringPoint M₁ M₂ := by
    apply pullback.hom_ext <;>
      simp only [c, j, coveringPoint, pullback.map, Category.assoc,
        pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
        pullback.lift_snd_assoc, hc₁, hc₂]
  have : SmoothOfRelativeDimension (1 + 1) (pullback.fst f₁ f₂ ≫ f₁) :=
    smoothOfRelativeDimension_comp (n := 1) (m := 1) _ _
  obtain ⟨hreg, hdim⟩ :=
    Scheme.isRegularLocalRing_strictHenselization_of_smoothOfRelativeDimension
      (pullback.fst f₁ f₂ ≫ f₁) (1 + 1) c (by
        rw [← Category.assoc, show c ≫ pullback.fst f₁ f₂ = c₁ from
          pullback.lift_fst _ _ _]
        simp only [f₁, ← Category.assoc, hc₁]
        simpa only [Category.assoc] using coveringPoint_to_k M₁)
  let e := Scheme.strictHenselizationEquivOfIsOpenImmersion j c
  rw [← hc]
  exact ⟨.of_ringEquiv e.symm, (ringKrullDim_eq_of_ringEquiv e).trans hdim⟩

private theorem curve_neighborhood (D : ModelCover k) :
    ∃ (V : D.C'.Opens) (cV : Spec (.of k) ⟶ V),
      cV ≫ V.ι = D.c ∧ SmoothOfRelativeDimension 1 (V.ι ≫ D.g ≫ D.j ≫ D.f) := by
  let f := D.g ≫ D.j ≫ D.f
  obtain ⟨U, V, _, _, hx, hVU, d, hd⟩ :=
    Smooth.exists_smoothOfRelativeDimension_resLE f (D.c (closedPoint k))
  have hdim : SmoothOfRelativeDimension d (V.ι ≫ f) := by
    rw [← Scheme.Hom.resLE_comp_ι f hVU]
    have : SmoothOfRelativeDimension (d + 0) (f.resLE U V hVU ≫ U.ι) := inferInstance
    simpa using this
  let cV := IsOpenImmersion.lift V.ι D.c (by
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim z (closedPoint k)]
    exact ⟨⟨_, hx⟩, rfl⟩)
  have hcV : cV ≫ V.ι = D.c := IsOpenImmersion.lift_fac _ _ _
  have hcVk : cV ≫ (V.ι ≫ f) = 𝟙 _ := by
    rw [← Category.assoc, hcV]
    exact coveringPoint_to_k D
  obtain ⟨_, hdimV⟩ :=
    Scheme.isRegularLocalRing_strictHenselization_of_smoothOfRelativeDimension
      (V.ι ≫ f) d cV hcVk
  let e := Scheme.strictHenselizationEquivOfIsOpenImmersion V.ι cV
  have hdimC : ringKrullDim (Scheme.strictHenselization D.c) = d := by
    rw [← hcV, ringKrullDim_eq_of_ringEquiv e]
    exact hdimV
  have hd1 : (d : WithBot ℕ∞) = 1 := by
    rw [← hdimC, ← ringKrullDim_eq_of_ringEquiv (ringEquivOfSpecIso D.e)]
    exact IsDiscreteValuationRing.ringKrullDim_eq_one D.A
  have hd : d = 1 := by exact_mod_cast hd1
  subst d
  exact ⟨V, cV, hcV, hdim⟩

private noncomputable def ringEquivOfSpecIso {A B : CommRingCat.{u}}
    (e : Spec A ≅ Spec B) : A ≃+* B :=
  Iso.commRingCatIsoToRingEquiv
    { hom := Spec.preimage e.inv
      inv := Spec.preimage e.hom
      hom_inv_id := Spec.map_injective (by simp)
      inv_hom_id := Spec.map_injective (by simp) }

private theorem exists_chart_iso (M₁ M₂ : ModelCover k) :
    ∃ e : chart M₁ M₂ ≅ Scheme.strictLocalization (coveringPoint M₁ M₂),
      e.hom ≫ Scheme.strictLocalizationToBase (coveringPoint M₁ M₂) =
        toCoveringCurves M₁ M₂ := by
  let P := chart M₁ M₂
  let p₀ := closedLift M₁ M₂ ≫ P.isoSpec.hom
  have hp₀ : p₀ (closedPoint k) = closedPoint Γ(P, ⊤) := by
    apply IsLocalRing.eq_closedPoint_of_isClosed
    apply isClosed_singleton_of_isClosedImmersion P.isoSpec.inv
    simpa only [p₀, ← Scheme.Hom.comp_apply, Category.assoc, Iso.hom_inv_id,
      Category.comp_id] using t₀_closed M₁ M₂
  obtain ⟨κ, hκ, hpκ⟩ :=
    Scheme.exists_hom_strictLocalization_of_isStrictlyHenselianLocalRing
      (coveringPoint M₁ M₂) (P.isoSpec.inv ≫ toCoveringCurves M₁ M₂) p₀ hp₀ (by
        simpa only [p₀, Category.assoc, Iso.hom_inv_id_assoc] using
          closedLift_toCovering M₁ M₂)
  have := Scheme.isStrictlyHenselianLocalRing_strictHenselization'
    (coveringPoint M₁ M₂)
  obtain ⟨ℓ, hℓ, hpℓ⟩ := exists_hom_chart M₁ M₂
    (Spec.map (Scheme.strictHenselizationEval (coveringPoint M₁ M₂)))
    (Scheme.spec_map_strictHenselizationEval_apply _ _)
    (Scheme.strictLocalizationToBase (coveringPoint M₁ M₂))
    (Scheme.spec_map_strictHenselizationEval_comp_strictLocalizationToBase _)
  let e : P ≅ Scheme.strictLocalization (coveringPoint M₁ M₂) :=
    { hom := P.isoSpec.hom ≫ κ
      inv := ℓ
      hom_inv_id := by
        rw [← cancel_epi P.isoSpec.inv]
        simp only [Category.assoc, Iso.inv_hom_id_assoc, Category.comp_id]
        apply hom_chart_ext M₁ M₂ p₀ hp₀
        · rw [Category.assoc, hℓ, hκ]
        · rw [← Category.assoc, hpκ, hpℓ]
          simp only [p₀, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      inv_hom_id := by
        refine Scheme.hom_strictLocalization_ext (coveringPoint M₁ M₂) ?_
          (Spec.map (Scheme.strictHenselizationEval (coveringPoint M₁ M₂)))
          (closedPoint k) (Scheme.spec_map_strictHenselizationEval_apply _ _) ?_
        · rw [Category.assoc, Category.assoc, hκ, Iso.hom_inv_id_assoc,
            hℓ, Category.id_comp]
        · rw [reassoc_of% hpℓ]
          simpa only [p₀, Category.assoc, Category.comp_id] using hpκ }
  refine ⟨e, ?_⟩
  change (P.isoSpec.hom ≫ κ) ≫ _ = _
  rw [Category.assoc, hκ, Iso.hom_inv_id_assoc]

private theorem exists_hom_chart (M₁ M₂ : ModelCover k) {R : CommRingCat.{u}}
    [IsStrictlyHenselianLocalRing R]
    (p₀ : Spec (.of k) ⟶ Spec R) (hp₀ : p₀ (closedPoint k) = closedPoint R)
    (a : Spec R ⟶ coveringCurves M₁ M₂) (ha : p₀ ≫ a = coveringPoint M₁ M₂) :
    ∃ ℓ : Spec R ⟶ chart M₁ M₂,
      ℓ ≫ toCoveringCurves M₁ M₂ = a ∧ p₀ ≫ ℓ = closedLift M₁ M₂ := by
  obtain ⟨ℓT, hℓT, hpT⟩ :=
    Scheme.exists_hom_strictLocalization_of_isStrictlyHenselianLocalRing
      (model_basePoint M₁ M₂) (a ≫ coveringMap M₁ M₂) p₀ hp₀ (by
        rw [← Category.assoc, ha, coveringPoint_map])
  obtain ⟨ℓ₁, hℓ₁, hp₁⟩ :=
    Scheme.exists_hom_strictLocalization_of_isStrictlyHenselianLocalRing M₁.c
      (a ≫ pullback.fst (M₁.g ≫ M₁.j ≫ M₁.f) (M₂.g ≫ M₂.j ≫ M₂.f)) p₀ hp₀ (by
        rw [← Category.assoc, ha]
        exact pullback.lift_fst _ _ _)
  obtain ⟨ℓ₂, hℓ₂, hp₂⟩ :=
    Scheme.exists_hom_strictLocalization_of_isStrictlyHenselianLocalRing M₂.c
      (a ≫ pullback.snd (M₁.g ≫ M₁.j ≫ M₁.f) (M₂.g ≫ M₂.j ≫ M₂.f)) p₀ hp₀ (by
        rw [← Category.assoc, ha]
        exact pullback.lift_snd _ _ _)
  let a₁ := ℓ₁ ≫ M₁.e.inv
  let a₂ := ℓ₂ ≫ M₂.e.inv
  have hpa₁ : p₀ ≫ a₁ = Spec.map (CommRingCat.ofHom M₁.residue.toRingHom) := by
    dsimp [a₁]
    rw [← Category.assoc, hp₁, ← point_e, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
    rfl
  have hpa₂ : p₀ ≫ a₂ = Spec.map (CommRingCat.ofHom M₂.residue.toRingHom) := by
    dsimp [a₂]
    rw [← Category.assoc, hp₂, ← point_e, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
    rfl
  have hA₁ : a₁ ≫ M₁.p = ℓT ≫ model_q₁ M₁ M₂ := by
    refine Scheme.hom_strictLocalization_ext M₁.x ?_ p₀ (closedPoint k) hp₀ ?_
    · dsimp only [a₁]
      simp only [Category.assoc, p_toBase, Iso.inv_hom_id_assoc]
      rw [← Category.assoc, hℓ₁, Category.assoc, q₁_toBase M₁ M₂,
        reassoc_of% hℓT]
      simp only [coveringMap, pullback.map, pullback.lift_fst]
    · rw [← Category.assoc, hpa₁, point_p, ← Category.assoc, hpT, point_q₁]
  have hA₂ : a₂ ≫ M₂.p = ℓT ≫ model_q₂ M₁ M₂ := by
    refine Scheme.hom_strictLocalization_ext M₂.x ?_ p₀ (closedPoint k) hp₀ ?_
    · dsimp only [a₂]
      simp only [Category.assoc, p_toBase, Iso.inv_hom_id_assoc]
      rw [← Category.assoc, hℓ₂, Category.assoc, q₂_toBase M₁ M₂,
        reassoc_of% hℓT]
      simp only [coveringMap, pullback.map, pullback.lift_snd]
    · rw [← Category.assoc, hpa₂, point_p, ← Category.assoc, hpT, point_q₂]
  have h₁ : a₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap k M₁.A)) =
      ℓT ≫ Scheme.strictLocalizationToBase (model_basePoint M₁ M₂) ≫
        pullback.fst M₁.f M₂.f ≫ M₁.f := by
    rw [← M₁.over_k, ← Category.assoc, ← Category.assoc, hA₁,
      Category.assoc, Category.assoc, reassoc_of% q₁_toBase M₁ M₂]
  have h₂ : a₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap k M₂.A)) =
      ℓT ≫ Scheme.strictLocalizationToBase (model_basePoint M₁ M₂) ≫
        pullback.snd M₁.f M₂.f ≫ M₂.f := by
    rw [← M₂.over_k, ← Category.assoc, ← Category.assoc, hA₂,
      Category.assoc, Category.assoc, reassoc_of% q₂_toBase M₁ M₂]
  let aA : Spec R ⟶ model_coverTraits M₁ M₂ := pullback.lift a₁ a₂ (by
    rw [h₁, h₂, pullback.condition])
  have hsq : ℓT ≫ model_surfaceMap M₁ M₂ = aA ≫ model_coverMap M₁ M₂ := by
    apply pullback.hom_ext
    · simp only [model_surfaceMap, model_coverMap, aA, pullback.map, Category.assoc,
        pullback.lift_fst, pullback.lift_fst_assoc]
      exact hA₁.symm
    · simp only [model_surfaceMap, model_coverMap, aA, pullback.map, Category.assoc,
        pullback.lift_snd, pullback.lift_snd_assoc]
      exact hA₂.symm
  let ℓ : Spec R ⟶ chart M₁ M₂ := pullback.lift ℓT aA hsq
  refine ⟨ℓ, ?_, ?_⟩
  · apply pullback.hom_ext
    · rw [Category.assoc, r₁_toCovering]
      simpa only [ℓ, r₁, aA, a₁, Category.assoc, pullback.lift_snd_assoc,
        pullback.lift_fst_assoc, Iso.inv_hom_id_assoc] using hℓ₁
    · rw [Category.assoc, r₂_toCovering]
      simpa only [ℓ, r₂, aA, a₂, Category.assoc, pullback.lift_snd_assoc,
        pullback.lift_snd_assoc, Iso.inv_hom_id_assoc] using hℓ₂
  · apply chart_point_unique
    simpa only [ℓ, Category.assoc, pullback.lift_fst] using hpT

private theorem hom_chart_ext (M₁ M₂ : ModelCover k) {R : CommRingCat.{u}} [IsLocalRing R]
    (p₀ : Spec (.of k) ⟶ Spec R) (hp₀ : p₀ (closedPoint k) = closedPoint R)
    {ℓ₁ ℓ₂ : Spec R ⟶ chart M₁ M₂}
    (h : ℓ₁ ≫ toCoveringCurves M₁ M₂ = ℓ₂ ≫ toCoveringCurves M₁ M₂)
    (hp : p₀ ≫ ℓ₁ = p₀ ≫ ℓ₂) : ℓ₁ = ℓ₂ := by
  have hT : ℓ₁ ≫ π M₁ M₂ = ℓ₂ ≫ π M₁ M₂ := by
    refine Scheme.hom_strictLocalization_ext (model_basePoint M₁ M₂) ?_ p₀ (closedPoint k) hp₀ ?_
    · simpa only [Category.assoc, chart_over_base] using
        congrArg (· ≫ coveringMap M₁ M₂) h
    · rw [reassoc_of% hp]
  have hA₁ : ℓ₁ ≫ r₁ M₁ M₂ = ℓ₂ ≫ r₁ M₁ M₂ := by
    rw [← cancel_mono M₁.e.hom]
    refine Scheme.hom_strictLocalization_ext M₁.c ?_ p₀ (closedPoint k) hp₀ ?_
    · simpa only [Category.assoc, r₁_toCovering] using
        congrArg (· ≫ pullback.fst (M₁.g ≫ M₁.j ≫ M₁.f)
          (M₂.g ≫ M₂.j ≫ M₂.f)) h
    · rw [Category.assoc, Category.assoc, reassoc_of% hp]
  have hA₂ : ℓ₁ ≫ r₂ M₁ M₂ = ℓ₂ ≫ r₂ M₁ M₂ := by
    rw [← cancel_mono M₂.e.hom]
    refine Scheme.hom_strictLocalization_ext M₂.c ?_ p₀ (closedPoint k) hp₀ ?_
    · simpa only [Category.assoc, r₂_toCovering] using
        congrArg (· ≫ pullback.snd (M₁.g ≫ M₁.j ≫ M₁.f)
          (M₂.g ≫ M₂.j ≫ M₂.f)) h
    · rw [Category.assoc, Category.assoc, reassoc_of% hp]
  apply pullback.hom_ext hT
  apply pullback.hom_ext
  · simpa only [Category.assoc, r₁] using hA₁
  · simpa only [Category.assoc, r₂] using hA₂

private theorem closedLift_toCovering (M₁ M₂ : ModelCover k) :
    closedLift M₁ M₂ ≫ toCoveringCurves M₁ M₂ = coveringPoint M₁ M₂ := by
  apply pullback.hom_ext
  · rw [Category.assoc, r₁_toCovering, ← Category.assoc, closedLift_r₁,
      ← Category.assoc, point_e,
      Scheme.spec_map_strictHenselizationEval_comp_strictLocalizationToBase]
    exact (pullback.lift_fst _ _ _).symm
  · rw [Category.assoc, r₂_toCovering, ← Category.assoc, closedLift_r₂,
      ← Category.assoc, point_e,
      Scheme.spec_map_strictHenselizationEval_comp_strictLocalizationToBase]
    exact (pullback.lift_snd _ _ _).symm

private theorem chart_over_base (M₁ M₂ : ModelCover k) :
    toCoveringCurves M₁ M₂ ≫ coveringMap M₁ M₂ =
      π M₁ M₂ ≫ Scheme.strictLocalizationToBase (model_basePoint M₁ M₂) := by
  apply pullback.hom_ext
  · rw [Category.assoc, coveringMap, pullback.map, pullback.lift_fst, ← Category.assoc,
      r₁_toCovering, Category.assoc, Category.assoc, ← p_toBase,
      ← Category.assoc, r₁_p, Category.assoc, q₁_toBase, Category.assoc]
  · rw [Category.assoc, coveringMap, pullback.map, pullback.lift_snd, ← Category.assoc,
      r₂_toCovering, Category.assoc, Category.assoc, ← p_toBase,
      ← Category.assoc, r₂_p, Category.assoc, q₂_toBase, Category.assoc]

private theorem r₂_toCovering (M₁ M₂ : ModelCover k) : toCoveringCurves M₁ M₂ ≫
    pullback.snd (M₁.g ≫ M₁.j ≫ M₁.f) (M₂.g ≫ M₂.j ≫ M₂.f) =
      r₂ M₁ M₂ ≫ M₂.e.hom ≫ Scheme.strictLocalizationToBase M₂.c := by
  simp only [toCoveringCurves, r₂, Category.assoc, pullback.map, pullback.lift_snd]

private theorem r₁_toCovering (M₁ M₂ : ModelCover k) : toCoveringCurves M₁ M₂ ≫
    pullback.fst (M₁.g ≫ M₁.j ≫ M₁.f) (M₂.g ≫ M₂.j ≫ M₂.f) =
      r₁ M₁ M₂ ≫ M₁.e.hom ≫ Scheme.strictLocalizationToBase M₁.c := by
  simp only [toCoveringCurves, r₁, Category.assoc, pullback.map, pullback.lift_fst]

private theorem p_toBase (D : ModelCover k) :
    D.p ≫ Scheme.strictLocalizationToBase D.x =
      D.e.hom ≫ Scheme.strictLocalizationToBase D.c ≫ D.g ≫ D.j := by
  exact D.over_base

private theorem coveringPoint_map (M₁ M₂ : ModelCover k) : coveringPoint M₁ M₂ ≫ coveringMap M₁ M₂ =
    model_basePoint M₁ M₂ := by
  apply pullback.hom_ext <;>
    simp only [coveringPoint, coveringMap, model_basePoint, Category.assoc,
      pullback.map, pullback.lift_fst, pullback.map, pullback.lift_snd, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc, pullback.lift_fst, pullback.lift_snd,
      M₁.c_g_j, M₂.c_g_j]

private noncomputable def coveringMap (M₁ M₂ : ModelCover k) :
    coveringCurves M₁ M₂ ⟶ pullback M₁.f M₂.f :=
  pullback.map _ _ _ _ (M₁.g ≫ M₁.j) (M₂.g ≫ M₂.j) (𝟙 _)
    (by simp only [Category.comp_id, Category.assoc])
    (by simp only [Category.comp_id, Category.assoc])

private instance chartRing_strict (M₁ M₂ : ModelCover k) :
    IsStrictlyHenselianLocalRing Γ(chart M₁ M₂, ⊤) := by
  let φ := Spec.preimage ((chart M₁ M₂).isoSpec.inv ≫ π M₁ M₂)
  have hφ : Spec.map φ = (chart M₁ M₂).isoSpec.inv ≫ π M₁ M₂ := Spec.map_preimage _
  have hfin : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]
    infer_instance
  algebraize [φ.hom]
  have := Scheme.isStrictlyHenselianLocalRing_strictHenselization' (model_basePoint M₁ M₂)
  obtain ⟨e, he, he1, hsh⟩ := IsStrictlyHenselianLocalRing.exists_isIdempotentElem_quotient
    (Scheme.strictHenselization (model_basePoint M₁ M₂)) Γ(chart M₁ M₂, ⊤)
    (maximalIdeal Γ(chart M₁ M₂, ⊤))
  rcases he.eq_zero_or_one_of_isLocalRing with rfl | rfl
  · exact ((maximalIdeal.isMaximal Γ(chart M₁ M₂, ⊤)).ne_top
      ((Ideal.eq_top_iff_one (maximalIdeal Γ(chart M₁ M₂, ⊤))).mpr
        (by rwa [sub_zero] at he1))).elim
  · rw [sub_self, Ideal.span_singleton_eq_bot.mpr rfl] at hsh
    exact .of_ringEquiv (RingEquiv.quotientBot _)

private instance chartRing_local (M₁ M₂ : ModelCover k) : IsLocalRing Γ(chart M₁ M₂, ⊤) := by
  have : Nontrivial Γ(chart M₁ M₂, ⊤) :=
    ((chart M₁ M₂).presheaf.germ ⊤ (t₀ M₁ M₂) trivial).hom.domain_nontrivial
  refine .of_unique_max_ideal ?_
  obtain ⟨m, hm⟩ := Ideal.exists_maximal Γ(chart M₁ M₂, ⊤)
  refine ⟨m, hm, fun m' hm' ↦ ?_⟩
  have key (n : Ideal Γ(chart M₁ M₂, ⊤)) (hn : n.IsMaximal) :
      (chart M₁ M₂).isoSpec.inv ⟨n, hn.isPrime⟩ = t₀ M₁ M₂ := by
    refine closed_eq_t₀ M₁ M₂
      (isClosed_singleton_of_isClosedImmersion (chart M₁ M₂).isoSpec.hom ?_)
    have hh := Scheme.hom_inv_apply (chart M₁ M₂).isoSpec.symm ⟨n, hn.isPrime⟩
    rw [Iso.symm_hom, Iso.symm_inv] at hh
    rw [hh]
    exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr hn
  have h := (key m' hm').trans (key m hm).symm
  exact congrArg PrimeSpectrum.asIdeal ((chart M₁ M₂).isoSpec.inv.isOpenEmbedding.injective h)

private theorem closed_eq_t₀ (M₁ M₂ : ModelCover k) {w : chart M₁ M₂}
    (hw : IsClosed ({w} : Set (chart M₁ M₂))) : w = t₀ M₁ M₂ :=
  chart_fiber_eq M₁ M₂ (π_closed M₁ M₂ hw) (π_t₀ M₁ M₂)

private theorem t₀_closed (M₁ M₂ : ModelCover k) : IsClosed ({t₀ M₁ M₂} : Set (chart M₁ M₂)) := by
  obtain ⟨w, hw, hcl⟩ :=
    (isClosed_closure (s := ({t₀ M₁ M₂} : Set (chart M₁ M₂)))).exists_closed_singleton
      ⟨t₀ M₁ M₂, subset_closure rfl⟩
  have hwt : w = t₀ M₁ M₂ := chart_fiber_eq M₁ M₂ (π_closed M₁ M₂ hcl) (π_t₀ M₁ M₂)
  simpa only [hwt] using hcl

private theorem π_closed (M₁ M₂ : ModelCover k) {w :
    chart M₁ M₂} (hw : IsClosed ({w} : Set (chart M₁ M₂))) :
    π M₁ M₂ w = closedPoint (Scheme.strictHenselization (model_basePoint M₁ M₂)) := by
  apply IsLocalRing.eq_closedPoint_of_isClosed
  have h := (π M₁ M₂).isClosedMap _ hw
  simpa only [Set.image_singleton] using h

private theorem π_t₀ (M₁ M₂ : ModelCover k) : π M₁ M₂ (t₀ M₁ M₂) =
    closedPoint (Scheme.strictHenselization (model_basePoint M₁ M₂)) := by
  rw [t₀, ← Scheme.Hom.comp_apply, closedLift_fst]
  exact Scheme.spec_map_strictHenselizationEval_apply _ _

private noncomputable abbrev t₀ (M₁ M₂ : ModelCover k) :
    chart M₁ M₂ := closedLift M₁ M₂ (closedPoint k)

private theorem chart_fiber_eq (M₁ M₂ : ModelCover k) {w w' : chart M₁ M₂}
    (hw : π M₁ M₂ w = closedPoint (Scheme.strictHenselization (model_basePoint M₁ M₂)))
    (hw' : π M₁ M₂ w' = closedPoint (Scheme.strictHenselization (model_basePoint M₁ M₂))) :
    w = w' := by
  let pt := Spec.map (Scheme.strictHenselizationEval (model_basePoint M₁ M₂))
  have ht : pt default = closedPoint (Scheme.strictHenselization (model_basePoint M₁ M₂)) :=
    Scheme.spec_map_strictHenselizationEval_apply _ _
  obtain ⟨x, rfl⟩ := Scheme.Hom.GeometricFiber.exists_apply_default_eq (π M₁ M₂) pt w
    (hw.trans ht.symm)
  obtain ⟨x', rfl⟩ := Scheme.Hom.GeometricFiber.exists_apply_default_eq (π M₁ M₂) pt w'
    (hw'.trans ht.symm)
  rw [chart_point_unique M₁ M₂ x.1 x.2, chart_point_unique M₁ M₂ x'.1 x'.2]

private noncomputable abbrev π (M₁ M₂ : ModelCover k) : chart M₁ M₂ ⟶ model_surface M₁ M₂ :=
  pullback.fst (model_surfaceMap M₁ M₂) (model_coverMap M₁ M₂)

private theorem chart_point_unique (M₁ M₂ : ModelCover k) (χ : Spec (.of k) ⟶ chart M₁ M₂)
    (hχ : χ ≫ pullback.fst (model_surfaceMap M₁ M₂) (model_coverMap M₁ M₂) =
      Spec.map (Scheme.strictHenselizationEval (model_basePoint M₁ M₂))) :
    χ = closedLift M₁ M₂ := by
  apply pullback.hom_ext
  · exact hχ.trans (closedLift_fst M₁ M₂).symm
  · apply pullback.hom_ext
    · change χ ≫ r₁ M₁ M₂ = closedLift M₁ M₂ ≫ r₁ M₁ M₂
      rw [closedLift_r₁]
      apply fiber_point_unique M₁
      rw [Category.assoc, r₁_p, ← Category.assoc, hχ, point_q₁]
    · change χ ≫ r₂ M₁ M₂ = closedLift M₁ M₂ ≫ r₂ M₁ M₂
      rw [closedLift_r₂]
      apply fiber_point_unique M₂
      rw [Category.assoc, r₂_p, ← Category.assoc, hχ, point_q₂]

private theorem r₂_p (M₁ M₂ : ModelCover k) : r₂ M₁ M₂ ≫ M₂.p =
    pullback.fst (model_surfaceMap M₁ M₂) (model_coverMap M₁ M₂) ≫ model_q₂ M₁ M₂ := by
  have h := congrArg (fun a ↦ a ≫ pullback.snd _ _)
    (pullback.condition (f := model_surfaceMap M₁ M₂) (g := model_coverMap M₁ M₂))
  simpa only [model_surfaceMap, model_coverMap, r₂, Category.assoc, pullback.lift_snd,
    pullback.map, pullback.lift_snd] using h.symm

private theorem r₁_p (M₁ M₂ : ModelCover k) : r₁ M₁ M₂ ≫ M₁.p =
    pullback.fst (model_surfaceMap M₁ M₂) (model_coverMap M₁ M₂) ≫ model_q₁ M₁ M₂ := by
  have h := congrArg (fun a ↦ a ≫ pullback.fst _ _)
    (pullback.condition (f := model_surfaceMap M₁ M₂) (g := model_coverMap M₁ M₂))
  simpa only [model_surfaceMap, model_coverMap, r₁, Category.assoc, pullback.lift_fst,
    pullback.map, pullback.lift_fst] using h.symm

private theorem closedLift_r₂ (M₁ M₂ : ModelCover k) :
    closedLift M₁ M₂ ≫ r₂ M₁ M₂ =
      Spec.map (CommRingCat.ofHom M₂.residue.toRingHom) := by
  simp only [closedLift, r₂, pullback.lift_snd_assoc, pullback.lift_snd]

private theorem closedLift_r₁ (M₁ M₂ : ModelCover k) :
    closedLift M₁ M₂ ≫ r₁ M₁ M₂ =
      Spec.map (CommRingCat.ofHom M₁.residue.toRingHom) := by
  simp only [closedLift, r₁, pullback.lift_snd_assoc, pullback.lift_fst]

private theorem closedLift_fst (M₁ M₂ : ModelCover k) :
    closedLift M₁ M₂ ≫ pullback.fst (model_surfaceMap M₁ M₂) (model_coverMap M₁ M₂) =
      Spec.map (Scheme.strictHenselizationEval (model_basePoint M₁ M₂)) :=
  pullback.lift_fst _ _ _

private noncomputable def closedLift (M₁ M₂ : ModelCover k) : Spec (.of k) ⟶ chart M₁ M₂ :=
  pullback.lift (Spec.map (Scheme.strictHenselizationEval (model_basePoint M₁ M₂)))
    (pullback.lift (Spec.map (CommRingCat.ofHom M₁.residue.toRingHom))
      (Spec.map (CommRingCat.ofHom M₂.residue.toRingHom))
      ((residue_comp M₁).trans (residue_comp M₂).symm)) (by
    apply pullback.hom_ext
    · simp only [Category.assoc, model_surfaceMap, pullback.lift_fst, model_coverMap,
        pullback.map, pullback.lift_fst, pullback.lift_fst_assoc]
      exact (point_q₁ M₁ M₂).trans (point_p M₁).symm
    · simp only [Category.assoc, model_surfaceMap, pullback.lift_snd, model_coverMap,
        pullback.map, pullback.lift_snd, pullback.lift_snd_assoc]
      exact (point_q₂ M₁ M₂).trans (point_p M₂).symm)

private theorem point_q₂ (M₁ M₂ : ModelCover k) :
    Spec.map (Scheme.strictHenselizationEval (model_basePoint M₁ M₂)) ≫ model_q₂ M₁ M₂ =
      Spec.map (Scheme.strictHenselizationEval M₂.x) := by
  unfold model_q₂
  rw [← Category.assoc,
    Scheme.spec_map_strictHenselizationEval_comp_strictLocalizationMap]
  have transport {C : Scheme.{u}} {x y : Spec (.of k) ⟶ C} (h : x = y) :
      Spec.map (Scheme.strictHenselizationEval x) ≫
        eqToHom (congrArg Scheme.strictLocalization h) =
      Spec.map (Scheme.strictHenselizationEval y) := by
    cases h
    exact Category.comp_id _
  exact transport (pullback.lift_snd M₁.x M₂.x _)

private theorem point_q₁ (M₁ M₂ : ModelCover k) :
    Spec.map (Scheme.strictHenselizationEval (model_basePoint M₁ M₂)) ≫ model_q₁ M₁ M₂ =
      Spec.map (Scheme.strictHenselizationEval M₁.x) := by
  unfold model_q₁
  rw [← Category.assoc,
    Scheme.spec_map_strictHenselizationEval_comp_strictLocalizationMap]
  have transport {C : Scheme.{u}} {x y : Spec (.of k) ⟶ C} (h : x = y) :
      Spec.map (Scheme.strictHenselizationEval x) ≫
        eqToHom (congrArg Scheme.strictLocalization h) =
      Spec.map (Scheme.strictHenselizationEval y) := by
    cases h
    exact Category.comp_id _
  exact transport (pullback.lift_fst M₁.x M₂.x _)

private theorem q₂_toBase (M₁ M₂ : ModelCover k) :
    model_q₂ M₁ M₂ ≫ Scheme.strictLocalizationToBase M₂.x =
      Scheme.strictLocalizationToBase (model_basePoint M₁ M₂) ≫ pullback.snd M₁.f M₂.f := by
  unfold model_q₂
  rw [Category.assoc]
  have transport {C : Scheme.{u}} {x y : Spec (.of k) ⟶ C} (h : x = y) :
      eqToHom (congrArg Scheme.strictLocalization h) ≫
        Scheme.strictLocalizationToBase y = Scheme.strictLocalizationToBase x := by
    cases h
    exact Category.id_comp _
  rw [transport (pullback.lift_snd M₁.x M₂.x _)]
  exact Scheme.strictLocalizationMap_comp_strictLocalizationToBase _ _

private theorem q₁_toBase (M₁ M₂ : ModelCover k) :
    model_q₁ M₁ M₂ ≫ Scheme.strictLocalizationToBase M₁.x =
      Scheme.strictLocalizationToBase (model_basePoint M₁ M₂) ≫ pullback.fst M₁.f M₂.f := by
  unfold model_q₁
  rw [Category.assoc]
  have transport {C : Scheme.{u}} {x y : Spec (.of k) ⟶ C} (h : x = y) :
      eqToHom (congrArg Scheme.strictLocalization h) ≫
        Scheme.strictLocalizationToBase y = Scheme.strictLocalizationToBase x := by
    cases h
    exact Category.id_comp _
  rw [transport (pullback.lift_fst M₁.x M₂.x _)]
  exact Scheme.strictLocalizationMap_comp_strictLocalizationToBase _ _

private instance chart_isAffine (M₁ M₂ : ModelCover k) : IsAffine (chart M₁ M₂) :=
  isAffine_of_isAffineHom (pullback.fst (model_surfaceMap M₁ M₂) (model_coverMap M₁ M₂))

private instance finite_coverMap (M₁ M₂ : ModelCover k) : IsFinite (model_coverMap M₁ M₂) := by
  unfold model_coverMap
  exact MorphismProperty.pullbackMap (P := @IsFinite) inferInstance inferInstance
    M₁.over_k.symm M₂.over_k.symm

private theorem fiber_point_unique (D : ModelCover k) (χ : Spec (.of k) ⟶ Spec D.A)
    (hχ : χ ≫ D.p = Spec.map (Scheme.strictHenselizationEval D.x)) :
    χ = Spec.map (CommRingCat.ofHom D.residue.toRingHom) := by
  apply point_unique D χ
  rw [← D.over_k, ← Category.assoc, ← Category.assoc, hχ, Category.assoc, point_rational_base]

private theorem point_rational_base (D : ModelCover k) :
    Spec.map (Scheme.strictHenselizationEval D.x) ≫
      Scheme.strictLocalizationToBase D.x ≫ D.f = 𝟙 _ := by
  rw [← Category.assoc,
    Scheme.spec_map_strictHenselizationEval_comp_strictLocalizationToBase, D.x_f]

private theorem point_p (D : ModelCover k) :
    Spec.map (CommRingCat.ofHom D.residue.toRingHom) ≫ D.p =
      Spec.map (Scheme.strictHenselizationEval D.x) := by
  apply rational_point_unique (Scheme.strictLocalizationToBase D.x ≫ D.f)
  · rw [Category.assoc, D.over_k]
    exact residue_comp D
  · rw [← Category.assoc,
      Scheme.spec_map_strictHenselizationEval_comp_strictLocalizationToBase, D.x_f]

private theorem point_e (D : ModelCover k) :
    Spec.map (CommRingCat.ofHom D.residue.toRingHom) ≫ D.e.hom =
      Spec.map (Scheme.strictHenselizationEval D.c) := by
  have hp := point_unique D (Spec.map (Scheme.strictHenselizationEval D.c) ≫ D.e.inv) (by
    rw [← D.e_over_k, Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc,
      Scheme.spec_map_strictHenselizationEval_comp_strictLocalizationToBase]
    exact coveringPoint_to_k D)
  rw [← hp, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem coveringPoint_to_k (D : ModelCover k) : D.c ≫ D.g ≫ D.j ≫ D.f = 𝟙 _ := by
  simpa only [Category.assoc] using
    (congrArg (· ≫ D.f) D.c_g_j).trans D.x_f

private theorem residue_comp (D : ModelCover k) :
    Spec.map (CommRingCat.ofHom D.residue.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k D.A)) = 𝟙 _ := by
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext a
  exact D.residue.commutes a

private theorem point_unique (D : ModelCover k) (χ : Spec (.of k) ⟶ Spec D.A)
    (hχ : χ ≫ Spec.map (CommRingCat.ofHom (algebraMap k D.A)) = 𝟙 _) :
    χ = Spec.map (CommRingCat.ofHom D.residue.toRingHom) := by
  let φ := Spec.preimage χ
  have hφ : Spec.map φ = χ := Spec.map_preimage _
  have hc : (CommRingCat.ofHom (algebraMap k D.A)) ≫ φ = 𝟙 _ := by
    apply Spec.map_injective
    simpa only [Spec.map_comp, hφ, Spec.map_id] using hχ
  have hsurj : Function.Surjective φ.hom := fun a ↦ ⟨algebraMap k D.A a, by
    have hh := congrArg (fun f ↦ f.hom a) hc
    exact hh⟩
  have hker : RingHom.ker φ.hom = maximalIdeal D.A :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective φ.hom hsurj)
  rw [← hφ]
  congr 1
  ext a
  have hs : a - algebraMap k D.A (D.residue a) ∈ RingHom.ker D.residue.toRingHom := by
    change D.residue (a - algebraMap k D.A (D.residue a)) = 0
    simp
  rw [D.residue_ker, ← hker, RingHom.mem_ker, map_sub, sub_eq_zero] at hs
  have hh := congrArg (fun f ↦ f.hom (D.residue a)) hc
  exact hs.trans hh

/-- The completed local ring, defined by the actual maximal-ideal adic completion.
Source: Stacks 0C0S (blueprint: lem-trf-finite-trait-cover-product). -/
private noncomputable abbrev model_completion (M₁ M₂ : ModelCover k) (t : chart M₁ M₂) :=
  AdicCompletion (maximalIdeal ((chart M₁ M₂).presheaf.stalk t))
    ((chart M₁ M₂).presheaf.stalk t)

/-- The canonical coefficient map k → O_(T',t').
Source: blueprint proof (ii) (blueprint: lem-trf-finite-trait-cover-product). -/
private noncomputable def model_coefficients (M₁ M₂ : ModelCover k) (t :
    chart M₁ M₂) : k →+* (chart M₁ M₂).presheaf.stalk t :=
  (model_toStalk (r₁ M₁ M₂) t).comp (algebraMap k M₁.A)

/-- The canonical map from an affine target's coordinate ring into a source stalk.
Source: structure-sheaf germ and pullback of sections, used in blueprint proof (ii)
(blueprint: lem-trf-finite-trait-cover-product). -/
private noncomputable def model_toStalk {X : Scheme.{u}} {A : CommRingCat.{u}}
    (f : X ⟶ Spec A) (t : X) : A →+* X.presheaf.stalk t :=
  (X.presheaf.germ ⊤ t trivial).hom.comp (f.appTop.hom.comp (Scheme.ΓSpecIso A).inv.hom)

/-- The displayed fibre product T ×_(X₁ ×_k X₂) (X₁' ×_k X₂'), with no localization
or choice of a component added to its construction.
Source: blueprint proof (ii) (blueprint: lem-trf-finite-trait-cover-product). -/
private noncomputable abbrev chart (M₁ M₂ : ModelCover k) : Scheme.{u} :=
  pullback (model_surfaceMap M₁ M₂) (model_coverMap M₁ M₂)

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

/-- The map to the first covering trait.
Source: blueprint proof (ii) (blueprint: lem-trf-finite-trait-cover-product). -/
noncomputable def r₁ : chart D₁ D₂ ⟶ Spec D₁.A :=
  pullback.snd _ _ ≫ pullback.fst _ _

/-- The map to the second covering trait.
Source: blueprint proof (ii) (blueprint: lem-trf-finite-trait-cover-product). -/
noncomputable def r₂ : chart D₁ D₂ ⟶ Spec D₂.A :=
  pullback.snd _ _ ≫ pullback.snd _ _

/-- The product of the two given finite flat morphisms.
Source: blueprint proof (ii) (blueprint: lem-trf-finite-trait-cover-product). -/
private noncomputable def model_coverMap (M₁ M₂ : ModelCover k) :
    model_coverTraits M₁ M₂ ⟶ model_baseTraits M₁ M₂ :=
  pullback.map _ _ _ _ M₁.p M₂.p (𝟙 _) ((Category.comp_id _).trans M₁.over_k.symm)
    ((Category.comp_id _).trans M₂.over_k.symm)

/-- The product over k of the two covering traits.
Source: blueprint proof (ii) (blueprint: lem-trf-finite-trait-cover-product). -/
private noncomputable abbrev model_coverTraits (M₁ M₂ : ModelCover k) : Scheme.{u} :=
  pullback (Spec.map (CommRingCat.ofHom (algebraMap k M₁.A)))
    (Spec.map (CommRingCat.ofHom (algebraMap k M₂.A)))

/-- The canonical map to the product of strict local traits, constructed using the
functorial strict-localization maps, not chosen from an existence assertion.
Source: Stacks 0GIP (blueprint: lem-trf-finite-trait-cover-product). -/
private noncomputable def model_surfaceMap (M₁ M₂ : ModelCover k) :
    model_surface M₁ M₂ ⟶ model_baseTraits M₁ M₂ :=
  pullback.lift (model_q₁ M₁ M₂) (model_q₂ M₁ M₂) (by
    have transport {C : Scheme.{u}} {x y : Spec (.of k) ⟶ C} (h : x = y) :
        eqToHom (congrArg Scheme.strictLocalization h) ≫
          Scheme.strictLocalizationToBase y = Scheme.strictLocalizationToBase x := by
      cases h
      exact Category.id_comp _
    have h₁ : model_q₁ M₁ M₂ ≫ Scheme.strictLocalizationToBase M₁.x =
        Scheme.strictLocalizationToBase (model_basePoint M₁ M₂) ≫ pullback.fst M₁.f M₂.f := by
      unfold model_q₁
      rw [Category.assoc, transport (pullback.lift_fst M₁.x M₂.x _)]
      exact Scheme.strictLocalizationMap_comp_strictLocalizationToBase _ _
    have h₂ : model_q₂ M₁ M₂ ≫ Scheme.strictLocalizationToBase M₂.x =
        Scheme.strictLocalizationToBase (model_basePoint M₁ M₂) ≫ pullback.snd M₁.f M₂.f := by
      unfold model_q₂
      rw [Category.assoc, transport (pullback.lift_snd M₁.x M₂.x _)]
      exact Scheme.strictLocalizationMap_comp_strictLocalizationToBase _ _
    simp only [← Category.assoc, h₁, h₂]
    simpa only [Category.assoc] using
      congrArg (fun a ↦ Scheme.strictLocalizationToBase (model_basePoint M₁ M₂) ≫ a)
        (pullback.condition (f := M₁.f) (g := M₂.f)))

/-- The product over the ground field of the two strict local base traits.
Source: blueprint proof (ii) (blueprint: lem-trf-finite-trait-cover-product). -/
private noncomputable abbrev model_baseTraits (M₁ M₂ : ModelCover k) : Scheme.{u} :=
  pullback (Scheme.strictLocalizationToBase M₁.x ≫ M₁.f)
    (Scheme.strictLocalizationToBase M₂.x ≫ M₂.f)

/-- The second canonical map from the strict local surface to a strict local factor.
Source: Stacks 0GIP (blueprint: lem-trf-finite-trait-cover-product). -/
private noncomputable def model_q₂ (M₁ M₂ : ModelCover k) :
    model_surface M₁ M₂ ⟶ Scheme.strictLocalization M₂.x :=
  Scheme.strictLocalizationMap (pullback.snd M₁.f M₂.f) (model_basePoint M₁ M₂) ≫
    eqToHom (congrArg Scheme.strictLocalization (pullback.lift_snd _ _ _))

/-- The first canonical map from the strict local surface to a strict local factor.
Source: Stacks 0GIP (blueprint: lem-trf-finite-trait-cover-product). -/
private noncomputable def model_q₁ (M₁ M₂ : ModelCover k) :
    model_surface M₁ M₂ ⟶ Scheme.strictLocalization M₁.x :=
  Scheme.strictLocalizationMap (pullback.fst M₁.f M₂.f) (model_basePoint M₁ M₂) ≫
    eqToHom (congrArg Scheme.strictLocalization (pullback.lift_fst _ _ _))

/-- The strict local surface of the product of the base curves.
Source: blueprint proof (ii) (blueprint: lem-trf-finite-trait-cover-product). -/
private noncomputable abbrev model_surface (M₁ M₂ : ModelCover k) : Scheme.{u} :=
  Scheme.strictLocalization (model_basePoint M₁ M₂)

/-- The indicated rational point of the product of the base curves.
Source: blueprint proof (ii) (blueprint: lem-trf-finite-trait-cover-product). -/
private noncomputable def model_basePoint (M₁ M₂ : ModelCover k) :
    Spec (.of k) ⟶ pullback M₁.f M₂.f :=
  pullback.lift M₁.x M₂.x (M₁.x_f.trans M₂.x_f.symm)

/-- Internal chart data for one factor, constructed from normalization below.
The isomorphism `e` identifies the covering trait with the strict localization of its
smooth covering curve. The equation `over_base` identifies their structural maps.
Source: blueprint `det-tf-restriction-zero-covers`, proof (ii), and Stacks 05WR, 0GIP
(blueprint: lem-trf-finite-trait-cover-product). -/
private structure ModelCover (k : Type u) [Field k] [IsAlgClosed k] where
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
  over_base : p ≫ Scheme.strictLocalizationToBase x =
    e.hom ≫ Scheme.strictLocalizationToBase c ≫ g ≫ j

end AlgebraicGeometry.FiniteTraitCoverProduct
