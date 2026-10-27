/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Sheaf.Paper.PurityDiagonalBaseChangeCompared
public import Sheaf.Paper.PurityDncInvariance
public import Sheaf.Paper.FixedFinitePositiveCoefficientTwist
public import Sheaf.Paper.PurityConventions
public import Sheaf.AlgebraicGeometry.VectorBundleIntegrationCharts
public import Sheaf.AlgebraicGeometry.AmbientAffineTranslationTrace
public import Sheaf.AlgebraicGeometry.ReesConeNormalizedExistence
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.AlgebraicGeometry.VectorBundleIntegration
public import Sheaf.Paper.VectorIntegrationSiteComparison
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.PuritySectionInvariantIntrinsic
public import Sheaf.Paper.PurityNormalProjection
public import Sheaf.Targets.VectorBundlePurity
public import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.Paper.AffineDiagonalGradedCoordinates

/-! # Constructions for affine diagonal integration

Source: main-20261015, smooth-purity, projection-purity-agreement proof,
Agreement on the model (blueprint: lem-pur-affine-diagonal-integration-orientation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

private lemma towerIso_over (S : Scheme.{u}) (d : ℕ) :
    (affineTraceAffineSpaceIso S d).inv ≫ affineTraceProjection S d =
      AffineSpace (ULift.{u} (Fin d)) S ↘ S := by
  apply (cancel_epi (affineTraceAffineSpaceIso S d).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  exact (AffineSpace.homOfVector_over _ _).symm

private lemma towerIso_coord (S : Scheme.{u}) (d : ℕ) (j : Fin d) :
    (affineTraceAffineSpaceIso S d).inv.appTop (affineTraceCoordinate S d j) =
      AffineSpace.coord S (ULift.up j) := by
  have h := congrArg (fun f ↦ f.appTop (AffineSpace.coord S (ULift.up j)))
    (affineTraceAffineSpaceIso S d).inv_hom_id
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    affineTraceAffineSpaceIso, asIso_hom, affineTraceToAffineSpace,
    AffineSpace.homOfVector_appTop_coord, Scheme.Hom.id_appTop, ConcreteCategory.id_apply] using h

private lemma tower_ext (S : Scheme.{u}) (d : ℕ)
    {X : Scheme.{u}} {f g : X ⟶ affineTraceTower S d}
    (hp : f ≫ affineTraceProjection S d = g ≫ affineTraceProjection S d)
    (hc : ∀ j, f.appTop (affineTraceCoordinate S d j) =
      g.appTop (affineTraceCoordinate S d j)) : f = g := by
  apply (cancel_mono (affineTraceAffineSpaceIso S d).hom).mp
  apply AffineSpace.hom_ext
  · simpa only [Category.assoc, affineTraceAffineSpaceIso, asIso_hom,
      affineTraceToAffineSpace, AffineSpace.homOfVector_over] using hp
  · rintro ⟨j⟩
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      affineTraceAffineSpaceIso, asIso_hom, affineTraceToAffineSpace,
      AffineSpace.homOfVector_appTop_coord] using hc j

private lemma translation_step_over (S : Scheme.{u}) (d : ℕ)
    (a : Fin (d + 1) → Γ(S, ⊤)) :
    (Etale.ambientAffineTranslation S (d + 1) a).hom ≫
      (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d) =
        (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d) ≫
          (Etale.ambientAffineTranslation S d (fun i ↦ a i.castSucc)).hom := by
  change (AffineSpace.translation
    (fun _ : PUnit.{u + 1} ↦ -(affineTraceProjection S d).appTop (a (Fin.last d))) ≫
      AffineSpace.map PUnit.{u + 1}
        (Etale.ambientAffineTranslation S d (fun i ↦ a i.castSucc)).hom) ≫ _ = _
  -- The last-coordinate translation is over the preceding tower stage.
  rw [Category.assoc, AffineSpace.map_over, ← Category.assoc, AffineSpace.translation_over]

private lemma translation_over (S : Scheme.{u}) (d : ℕ) (a : Fin d → Γ(S, ⊤)) :
    (Etale.ambientAffineTranslation S d a).hom ≫ affineTraceProjection S d =
      affineTraceProjection S d := by
  induction d with
  | zero => exact Category.id_comp _
  | succ d ih =>
    change (Etale.ambientAffineTranslation S (d + 1) a).hom ≫
      ((AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d) ≫
        affineTraceProjection S d) = _
    rw [← Category.assoc, translation_step_over S d a,
      Category.assoc, ih]
    rfl

private lemma translation_coord (S : Scheme.{u}) (d : ℕ) (a : Fin d → Γ(S, ⊤))
    (i : Fin d) :
    (Etale.ambientAffineTranslation S d a).hom.appTop (affineTraceCoordinate S d i) =
      affineTraceCoordinate S d i - (affineTraceProjection S d).appTop (a i) := by
  induction d with
  | zero => exact Fin.elim0 i
  | succ d ih =>
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp only [affineTraceCoordinate, Fin.lastCases_last]
      dsimp only [Etale.ambientAffineTranslation, Iso.trans_hom, Functor.mapIso_hom,
        Etale.ambientAffineTranslationIso]
      change (AffineSpace.translation
        (fun _ : PUnit.{u + 1} ↦ -(affineTraceProjection S d).appTop (a (Fin.last d))) ≫
          AffineSpace.map PUnit.{u + 1}
            (Etale.ambientAffineTranslation S d (fun j ↦ a j.castSucc)).hom).appTop
              (AffineSpace.coord (affineTraceTower S d) PUnit.unit) = _
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.map_appTop_coord,
        AffineSpace.translation_appTop_coord]
      change _ = AffineSpace.coord (affineTraceTower S d) PUnit.unit -
        ((AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d) ≫
          affineTraceProjection S d).appTop (a (Fin.last d))
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, map_neg, sub_eq_add_neg]
    · simp only [affineTraceCoordinate, Fin.lastCases_castSucc]
      let q := AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d
      change (Etale.ambientAffineTranslation S (d + 1) a).hom.appTop
        (q.appTop (affineTraceCoordinate S d j)) = q.appTop (affineTraceCoordinate S d j) -
          (q ≫ affineTraceProjection S d).appTop (a j.castSucc)
      have h := congrArg (fun f ↦ f.appTop (affineTraceCoordinate S d j))
        (translation_step_over S d a)
      change (Etale.ambientAffineTranslation S (d + 1) a).hom.appTop
        (q.appTop (affineTraceCoordinate S d j)) =
          q.appTop ((Etale.ambientAffineTranslation S d
            (fun k ↦ a k.castSucc)).hom.appTop (affineTraceCoordinate S d j)) at h
      exact h.trans ((congrArg (fun z ↦ q.appTop z) (ih (fun k ↦ a k.castSucc) j)).trans
        ((map_sub q.appTop.hom _ _).trans rfl))

/-- The ordered coordinate model, with rank zero literally the base.
Source: Agreement on the model (blueprint: lem-pur-affine-diagonal-integration-orientation). -/
abbrev affineDiagonalSpace (Y : Scheme.{u}) (d : ℕ) := affineTraceTower Y d

/-- The specified ordered affine projection.
Source: Agreement on the model (blueprint: lem-pur-affine-diagonal-integration-orientation). -/
abbrev affineDiagonalProjection (Y : Scheme.{u}) (d : ℕ) := affineTraceProjection Y d

/-- Ordered coordinates on the self-product, retaining y minus x.
Source: Agreement on the model (blueprint: lem-pur-affine-diagonal-integration-orientation). -/
def affineDiagonalDifferences (Y : Scheme.{u}) (d : ℕ) (i : Fin d) :=
  (pullback.snd (affineDiagonalProjection Y d) (affineDiagonalProjection Y d)).appTop
      (affineTraceCoordinate Y d i) -
    (pullback.fst (affineDiagonalProjection Y d) (affineDiagonalProjection Y d)).appTop
      (affineTraceCoordinate Y d i)

/-- A coordinate difference is a unique section of the actual diagonal ideal.
Source: Agreement on the model, I=(y_i-x_i)
(blueprint: lem-pur-affine-diagonal-integration-orientation).
Proof: diagonal pullback sends both coordinate functions to the same function.
The kernel ideal therefore contains their difference. The first ideal power is
that ideal, by ConormalGradedAlgebra.presentation.powerIdentification. Its
inclusion into the structure sheaf is monic, giving uniqueness. -/
theorem affineDiagonalDifference_lift (Y : Scheme.{u}) (d : ℕ) (i : Fin d) :
    ∃! b : (ConormalGradedAlgebra.power
        (pullback.diagonal (affineDiagonalProjection Y d)) 1).val.obj (op ⊤),
      (ConormalGradedAlgebra.powerInclusion
        (pullback.diagonal (affineDiagonalProjection Y d)) 1).val.app (op ⊤) b =
          affineDiagonalDifferences Y d i := by
  let p := affineDiagonalProjection Y d
  let s := pullback.diagonal p
  let x := affineDiagonalDifferences Y d i
  have hx : s.appTop x = 0 := by
    dsimp only [x, affineDiagonalDifferences]
    rw [map_sub]
    change s.appTop ((pullback.snd p p).appTop (affineTraceCoordinate Y d i)) -
      s.appTop ((pullback.fst p p).appTop (affineTraceCoordinate Y d i)) = 0
    simp only [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, s,
      pullback.diagonal_snd, pullback.diagonal_fst, Scheme.Hom.id_appTop,
      ConcreteCategory.id_apply, sub_self]
  have hk : s.ker.subschemeι.appTop x = 0 := by
    apply (asIso s.toImage.appTop).commRingCatIsoToRingEquiv.injective
    change s.toImage.appTop (s.ker.subschemeι.appTop x) = s.toImage.appTop 0
    rw [map_zero]
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      Scheme.Hom.toImage_imageι]
    exact hx
  obtain ⟨b, hb⟩ := (s.ker.range_toModulesι_app_eq ⊤).superset hk
  exact ⟨b, hb, fun c hc ↦ s.ker.injective_toModulesι_app ⊤ (hc.trans hb.symm)⟩

/-- The actual degree-one ideal representative, uniquely determined by its inclusion.
Source: Agreement on the model (blueprint: lem-pur-affine-diagonal-integration-orientation). -/
def affineDiagonalDifferenceLift (Y : Scheme.{u}) (d : ℕ) (i : Fin d) :=
  (affineDiagonalDifference_lift Y d i).exists.choose

/-- The ordered homogeneous normal functions on the relative-Spec cone.
Source: Agreement on the model, v_i=[y_i-x_i]
(blueprint: lem-pur-affine-diagonal-integration-orientation). -/
def affineDiagonalNormalFunction (Y : Scheme.{u}) (d : ℕ) (i : Fin d) :
    Γ(PurityNormalBundle.normalCone (pullback.diagonal (affineDiagonalProjection Y d)), ⊤) :=
  let s := pullback.diagonal (affineDiagonalProjection Y d)
  let A := (ConormalGradedAlgebra.presentation s).algebra
  let b := ConormalGradedAlgebra.homogeneousClass s A
    (ConormalGradedAlgebra.presentation s).inclusion 1 ⊤ (affineDiagonalDifferenceLift Y d i)
  let c := A.right.obj.map (homOfLE (by simp)).op b
  (PurityNormalBundle.normalCone s).presheaf.map (homOfLE (by simp)).op
    ((Etale.FiniteSmoothPurity.coneAlgebraIso s).hom.right.hom.app (op ⊤) c)

/-- Normal coordinates on the actual extended-Rees zero fibre. The comparison q is
required to preserve every homogeneous representative; no arbitrary bundle map enters.
Source: Agreement on the model (blueprint: lem-pur-affine-diagonal-integration-orientation). -/
def affineDiagonalNormalCoordinates (Y : Scheme.{u}) (d : ℕ)
    (q : (pullback.diagonal (affineDiagonalProjection Y d)).ker.normalCone ≅
      PurityNormalBundle.normalCone (pullback.diagonal (affineDiagonalProjection Y d))) :
    (pullback.diagonal (affineDiagonalProjection Y d)).ker.normalCone ⟶
      affineTraceTower (affineDiagonalSpace Y d) d :=
  AffineSpace.homOfVector
      (Scheme.Hom.normalConeProj (pullback.fst (affineDiagonalProjection Y d)
        (affineDiagonalProjection Y d)) (pullback.diagonal (affineDiagonalProjection Y d)))
      (fun i : ULift.{u} (Fin d) ↦ q.hom.appTop (affineDiagonalNormalFunction Y d i.down)) ≫
    (affineTraceAffineSpaceIso (affineDiagonalSpace Y d) d).inv

/-- The concrete normal coordinates are an isomorphism, and the projection is smooth
of pure dimension d. This includes the empty list of generators.
Source: Agreement on the model, normal-coordinate calculation
(blueprint: lem-pur-affine-diagonal-integration-orientation).
Proof: on Spec R rewrite R[x,y] as R[x,u] by u=y-x, with inverse y=x+u.
The powers of I=(u) have their homogeneous monomial bases, so gr_I R[x,u]
is R[x,v], with v the degree-one class of u. The normalized Rees comparison
sends this class to u/t modulo t. The constructed coordinate map is therefore
Spec of the polynomial-algebra identification, hence invertible and over X.
The projection is the rank-d affine-space projection, hence smooth of that
relative dimension. These coordinate maps commute with localization and glue.
For d=0 all polynomial substitutions and both projections are identities. -/
theorem affineDiagonalNormalCoordinates_spec (Y : Scheme.{u}) (d : ℕ)
    (q : (pullback.diagonal (affineDiagonalProjection Y d)).ker.normalCone ≅
      PurityNormalBundle.normalCone (pullback.diagonal (affineDiagonalProjection Y d)))
    (_hq : Etale.FiniteSmoothPurity.ReesConeNormalized
      (pullback.diagonal (affineDiagonalProjection Y d)) q) :
    IsIso (affineDiagonalNormalCoordinates Y d q) ∧
    affineDiagonalNormalCoordinates Y d q ≫ affineTraceProjection (affineDiagonalSpace Y d) d =
      Scheme.Hom.normalConeProj (pullback.fst (affineDiagonalProjection Y d)
        (affineDiagonalProjection Y d)) (pullback.diagonal (affineDiagonalProjection Y d)) := by
  let p := affineDiagonalProjection Y d
  let s := pullback.diagonal p
  let π := Scheme.Hom.normalConeProj (pullback.fst p p) s
  let v : PurityNormalBundle.normalCone s ⟶
      AffineSpace (ULift.{u} (Fin d)) (affineDiagonalSpace Y d) :=
    AffineSpace.homOfVector (PurityNormalBundle.projection s)
      (fun i ↦ affineDiagonalNormalFunction Y d i.down)
  have hv : IsIso v := PurityNormalBundle.affineDiagonalGradedCoordinates_isIso Y d
    (affineDiagonalDifferenceLift Y d)
    (fun i ↦ (affineDiagonalDifference_lift Y d i).exists.choose_spec)
  have hqπ : q.hom ≫ PurityNormalBundle.projection s = π :=
    _hq.1.trans (Scheme.Hom.purityNormalProjection_eq s
      (pullback.fst p p) (pullback.diagonal_fst p))
  have heq : affineDiagonalNormalCoordinates Y d q =
      q.hom ≫ v ≫ (affineTraceAffineSpaceIso (affineDiagonalSpace Y d) d).inv := by
    dsimp only [affineDiagonalNormalCoordinates, v]
    rw [← Category.assoc, AffineSpace.comp_homOfVector, hqπ]
    rfl
  constructor
  · rw [heq]
    infer_instance
  · simp only [heq, Category.assoc, towerIso_over, v, AffineSpace.homOfVector_over]
    exact hqπ

/-- The y-coordinate presentation of the first projection; translation is y -> y-x.
Source: Agreement on the model (blueprint: lem-pur-affine-diagonal-integration-orientation). -/
def affineDiagonalProductCoordinates (Y : Scheme.{u}) (d : ℕ) :
    pullback (affineDiagonalProjection Y d) (affineDiagonalProjection Y d) ⟶
      affineTraceTower (affineDiagonalSpace Y d) d :=
  AffineSpace.homOfVector
      (pullback.fst (affineDiagonalProjection Y d) (affineDiagonalProjection Y d))
      (fun i : ULift.{u} (Fin d) ↦
        (pullback.snd (affineDiagonalProjection Y d) (affineDiagonalProjection Y d)).appTop
          (affineTraceCoordinate Y d i.down)) ≫
    (affineTraceAffineSpaceIso (affineDiagonalSpace Y d) d).inv

/-- The self-product is the trivial bundle in the displayed y coordinates.
Source: Agreement on the model (blueprint: lem-pur-affine-diagonal-integration-orientation).
Proof: the inverse pairs the base point with the point having the given y
coordinates, using the fibre-product universal property. The two composites
agree on the base projection and on every coordinate, so are identities.
The coordinate definition preserves the projection. Empty coordinate lists give
identity maps, and the formulas work on every affine chart of an arbitrary base. -/
theorem affineDiagonalProductCoordinates_spec (Y : Scheme.{u}) (d : ℕ) :
    IsIso (affineDiagonalProductCoordinates Y d) ∧
      affineDiagonalProductCoordinates Y d ≫ affineTraceProjection (affineDiagonalSpace Y d) d =
        pullback.fst (affineDiagonalProjection Y d) (affineDiagonalProjection Y d) := by
  let X := affineDiagonalSpace Y d
  let p := affineDiagonalProjection Y d
  let T := affineTraceTower X d
  let t := affineTraceProjection X d
  let y : T ⟶ X := AffineSpace.homOfVector (t ≫ p)
    (fun i : ULift.{u} (Fin d) ↦ affineTraceCoordinate X d i.down) ≫
      (affineTraceAffineSpaceIso Y d).inv
  have hy : y ≫ p = t ≫ p := by
    simp only [y, p, affineDiagonalProjection, Category.assoc, towerIso_over,
      AffineSpace.homOfVector_over]
  have hyc (i : Fin d) : y.appTop (affineTraceCoordinate Y d i) =
      affineTraceCoordinate X d i := by
    change (AffineSpace.homOfVector (t ≫ p)
      (fun j : ULift.{u} (Fin d) ↦ affineTraceCoordinate X d j.down)).appTop
        ((affineTraceAffineSpaceIso Y d).inv.appTop (affineTraceCoordinate Y d i)) = _
    rw [towerIso_coord]
    exact AffineSpace.homOfVector_appTop_coord _ _ _
  let g : T ⟶ pullback p p := pullback.lift t y hy.symm
  have hproj : affineDiagonalProductCoordinates Y d ≫ t = pullback.fst p p := by
    simp only [affineDiagonalProductCoordinates, t, X, p, Category.assoc,
      towerIso_over, AffineSpace.homOfVector_over]
  have hcoord (i : Fin d) :
      (affineDiagonalProductCoordinates Y d).appTop (affineTraceCoordinate X d i) =
        (pullback.snd p p).appTop (affineTraceCoordinate Y d i) := by
    simp only [affineDiagonalProductCoordinates, X, p, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply, towerIso_coord, AffineSpace.homOfVector_appTop_coord]
  refine ⟨⟨⟨g, ?_, ?_⟩⟩, hproj⟩
  · apply pullback.hom_ext
    · change affineDiagonalProductCoordinates Y d ≫ (g ≫ pullback.fst p p) =
        pullback.fst p p
      rw [show g ≫ pullback.fst p p = t from pullback.lift_fst _ _ _]
      exact hproj
    · change affineDiagonalProductCoordinates Y d ≫ (g ≫ pullback.snd p p) =
        pullback.snd p p
      rw [show g ≫ pullback.snd p p = y from pullback.lift_snd _ _ _]
      apply tower_ext Y d
      · change (affineDiagonalProductCoordinates Y d ≫ y) ≫ p = pullback.snd p p ≫ p
        rw [Category.assoc, hy, ← Category.assoc, hproj, pullback.condition]
      · intro i
        rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hyc, hcoord]
  · apply tower_ext X d
    · change (g ≫ affineDiagonalProductCoordinates Y d) ≫ t = t
      rw [Category.assoc, hproj]
      exact pullback.lift_fst _ _ _
    · intro i
      change (g ≫ affineDiagonalProductCoordinates Y d).appTop
        (affineTraceCoordinate X d i) = affineTraceCoordinate X d i
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hcoord,
        ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
      rw [show g ≫ pullback.snd p p = y from pullback.lift_snd _ _ _]
      exact hyc i

-- Avoid unfolding the cone coordinate construction in later derived-map statements.
attribute [local irreducible] affineDiagonalNormalCoordinates
  affineDiagonalNormalFunction affineDiagonalDifferenceLift
  Etale.FiniteSmoothPurity.ReesConeNormalized
  Etale.affineLinearCompactComparison
  Etale.affineLinearCoefficientDescent Etale.vectorIntegrationBaseCoefficientPullback

/-- Trivial-bundle integration transpose in a specified coordinate presentation.
The ordered counit and compact-support comparison define the actual trace. Its
exceptional transpose is pulled along the coordinate isomorphism using the
counit-transposed dualizing base-change map, and the pure-root Tate restriction.
Source: Agreement on the model; affine-space top trace
(blueprint: lem-pur-affine-diagonal-integration-orientation). -/
def affineDiagonalPresentedTranspose (P : PurityFiniteSetting.{u})
    {U B : Scheme.{u}} (d : ℕ) (f : U ⟶ B) [HasCompactification f] [QuasiCompact f]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : P.Coefficient) = 0)
    (e : U ≅ affineTraceTower B d) (he : e.hom ≫ affineTraceProjection B d = f) :
    Etale.affineLinearBaseCoefficient P.Coefficient (P.coefficients.l ^ (r + 1)) hA U d ⟶
      Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) f :=
  letI := P.noetherian aB
  let N := P.coefficients.l ^ (r + 1)
  let hN := pow_pos P.coefficients.prime.out.pos (r + 1)
  let t := Etale.ambientAffineTraceTransport N hN P.Coefficient hA
  let D := Etale.ambientAffineTraceDatum N hN P.Coefficient hA
  let q := affineTraceProjection B d
  letI := affineTraceNoetherian B d
  let sq : IsPullback e.hom f q (𝟙 B) :=
    IsPullback.of_horiz_isIso ⟨he.trans (Category.comp_id f).symm⟩
  let Q := (Etale.affineTraceRight P.Coefficient N hA B d).obj
    (Etale.ordinaryFiniteUnit P.Coefficient B)
  let tr := (Etale.affineLinearCompactComparison N hN P.Coefficient hA B
    (WeilConjectures.PurityConventions.coefficientPower_isUnit P B aB r) d).inv ≫
      Etale.affineTraceCounit P.Coefficient N hA t D B
        (WeilConjectures.PurityConventions.coefficientPower_isUnit P B aB r) d
  let z := (Etale.rightDerivedUpperShriekAdjunction
    (ModuleCat.{u + 1} P.Coefficient) q).homEquiv Q (𝟙_ _) tr
  let c := Etale.affineLinearCoefficientDescent P.Coefficient N hA t B
    (WeilConjectures.PurityConventions.coefficientPower_isUnit P B aB r) d
  (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient N hA t f
    (WeilConjectures.PurityConventions.coefficientPower_isUnit P B aB r) d).inv ≫
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) e.hom q f he.symm).hom.app
      (Etale.affineLinearBaseCoefficient P.Coefficient N hA B d) ≫
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) e.hom).leftDerivedFunctor.map c.inv ≫
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) e.hom).leftDerivedFunctor.map z ≫
    Etale.dualizingComplexBaseChangeMap P.Coefficient sq

/-- Integration in a coordinate presentation, with its compactification transport.
It is the inverse exceptional Hom bijection applied to the explicit transported
counit transpose above; thus the map is determined by the actual ordered trace.
Source: Agreement on the model, trace and its exceptional transpose
(blueprint: lem-pur-affine-diagonal-integration-orientation). -/
def affineDiagonalPresentedIntegration (P : PurityFiniteSetting.{u})
    {U B : Scheme.{u}} (d : ℕ) (f : U ⟶ B) [HasCompactification f] [QuasiCompact f]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : P.Coefficient) = 0)
    (e : U ≅ affineTraceTower B d) (he : e.hom ≫ affineTraceProjection B d = f) :=
  ((Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} P.Coefficient) f).homEquiv
    (Etale.affineLinearBaseCoefficient P.Coefficient
      (P.coefficients.l ^ (r + 1)) hA U d) (𝟙_ _)).symm
        (P.affineDiagonalPresentedTranspose d f aB r hA e he)

/-- The specified translation h(x,y)=(x,y-x), using the tautological vector on X.
Source: Agreement on the model, ordered translation
(blueprint: lem-pur-affine-diagonal-integration-orientation). -/
def affineDiagonalTranslatedCoordinates (Y : Scheme.{u}) (d : ℕ) :=
  affineDiagonalProductCoordinates Y d ≫
    (Etale.ambientAffineTranslation (affineDiagonalSpace Y d) d
      (affineTraceCoordinate Y d)).hom

/-- The ordered difference coordinates are an isomorphism over X, taking the
actual diagonal to the zero section. The coordinate equation fixes the sign and order.
Source: Agreement on the model, h and its inverse
(blueprint: lem-pur-affine-diagonal-integration-orientation).
Proof: substitute u_i=y_i-x_i and y_i=x_i+u_i in polynomial charts. These substitutions
are mutually inverse and commute with localization. Their base projection is x;
restriction to the diagonal kills every u_i, giving the zero section. The formula
for appTop follows from the defining translation and the coordinate presentation.
At rank zero the lists are empty and the substitution is the identity. -/
theorem affineDiagonalTranslatedCoordinates_spec (Y : Scheme.{u}) (d : ℕ) :
    IsIso (affineDiagonalTranslatedCoordinates Y d) ∧
    affineDiagonalTranslatedCoordinates Y d ≫ affineTraceProjection (affineDiagonalSpace Y d) d =
      pullback.fst (affineDiagonalProjection Y d) (affineDiagonalProjection Y d) ∧
    pullback.diagonal (affineDiagonalProjection Y d) ≫
        affineDiagonalTranslatedCoordinates Y d ≫
          (affineTraceAffineSpaceIso (affineDiagonalSpace Y d) d).hom =
      AffineSpace.zeroSection (ULift.{u} (Fin d)) (affineDiagonalSpace Y d) ∧
    ∀ i : Fin d,
      (affineDiagonalTranslatedCoordinates Y d).appTop
        (affineTraceCoordinate (affineDiagonalSpace Y d) d i) =
          affineDiagonalDifferences Y d i := by
  let X := affineDiagonalSpace Y d
  let p := affineDiagonalProjection Y d
  let t := affineTraceProjection X d
  let a := affineTraceCoordinate Y d
  let e := affineDiagonalProductCoordinates Y d
  let h := affineDiagonalTranslatedCoordinates Y d
  have he : IsIso e := (affineDiagonalProductCoordinates_spec Y d).1
  have hep : e ≫ t = pullback.fst p p := (affineDiagonalProductCoordinates_spec Y d).2
  have hp : h ≫ t = pullback.fst p p := by
    change (e ≫ (Etale.ambientAffineTranslation X d a).hom) ≫ t = _
    rw [Category.assoc, translation_over, hep]
  have hc (i : Fin d) : h.appTop (affineTraceCoordinate X d i) =
      affineDiagonalDifferences Y d i := by
    change (e ≫ (Etale.ambientAffineTranslation X d a).hom).appTop
      (affineTraceCoordinate X d i) = _
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, translation_coord, map_sub,
      ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hep]
    change e.appTop (affineTraceCoordinate X d i) -
      (pullback.fst p p).appTop (a i) = _
    change (AffineSpace.homOfVector (pullback.fst p p)
      (fun j : ULift.{u} (Fin d) ↦ (pullback.snd p p).appTop
        (affineTraceCoordinate Y d j.down))).appTop
          ((affineTraceAffineSpaceIso X d).inv.appTop (affineTraceCoordinate X d i)) -
            (pullback.fst p p).appTop (a i) = _
    rw [towerIso_coord, AffineSpace.homOfVector_appTop_coord]
    rfl
  refine ⟨?_, hp, ?_, hc⟩
  · change IsIso (e ≫ (Etale.ambientAffineTranslation X d a).hom)
    infer_instance
  · apply AffineSpace.hom_ext
    · rw [AffineSpace.zeroSection_over]
      change (pullback.diagonal p ≫ h ≫ (affineTraceAffineSpaceIso X d).hom) ≫
        (AffineSpace (ULift.{u} (Fin d)) X ↘ X) = 𝟙 X
      have ho : (affineTraceAffineSpaceIso X d).hom ≫
          (AffineSpace (ULift.{u} (Fin d)) X ↘ X) = t :=
        AffineSpace.homOfVector_over _ _
      rw [Category.assoc, Category.assoc, ho, hp, pullback.diagonal_fst]
    · rintro ⟨i⟩
      change (pullback.diagonal p ≫ h ≫ (affineTraceAffineSpaceIso X d).hom).appTop
        (AffineSpace.coord X (ULift.up i)) =
          (AffineSpace.zeroSection (ULift.{u} (Fin d)) X).appTop
            (AffineSpace.coord X (ULift.up i))
      have hcoord : (affineTraceAffineSpaceIso X d).hom.appTop
          (AffineSpace.coord X (ULift.up i)) = affineTraceCoordinate X d i :=
        AffineSpace.homOfVector_appTop_coord _ _ _
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hcoord, hc,
        AffineSpace.zeroSection_appTop_coord]
      change (pullback.diagonal p).appTop
        ((pullback.snd p p).appTop (a i) - (pullback.fst p p).appTop (a i)) = 0
      rw [map_sub, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
        ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
        pullback.diagonal_snd, pullback.diagonal_fst, sub_self]

/-- Smoothness in the concrete ordered-tower presentation of the affine bundle.
Source: sbc-lem-affine-space-smooth and its coordinate-preserving affine-space iso
(blueprint: lem-pur-affine-diagonal-integration-orientation).
Proof: affineTraceAffineSpaceIso identifies the projection with the affine-space
projection on ULift (Fin d). The recorded smoothness instance has dimension
Nat.card (ULift (Fin d))=d. Composition with this isomorphism preserves that
dimension; the identity tower at d=0 and the empty base are included. -/
theorem affineDiagonalProjection_smooth (Y : Scheme.{u}) (d : ℕ) :
    SmoothOfRelativeDimension d (affineDiagonalProjection Y d) := by
  have h : SmoothOfRelativeDimension d
      (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) := by
    simpa using (AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin d)) Y)
  let e := affineTraceAffineSpaceIso Y d
  have he : e.hom ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) =
      affineDiagonalProjection Y d := AffineSpace.homOfVector_over _ _
  rw [← he]
  exact (MorphismProperty.cancel_left_of_respectsIso
    (P := @SmoothOfRelativeDimension d) e.hom _).2 h

/-- Tensor the root-power comparison in the prescribed order, shifting each factor
by two. The zero-fold comparison is identity, so no orientation scalar is chosen.
Source: Agreement on the model, exponent-independence clause
(blueprint: lem-pur-affine-diagonal-integration-orientation). -/
def affineDiagonalPowerComparison (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) (r r' : ℕ)
    (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : P.Coefficient) = 0)
    (hA' : ((P.coefficients.l ^ (r' + 1) : ℕ) : P.Coefficient) = 0)
    (e : Scheme.finiteEtaleTateLine T (P.coefficients.l ^ (r' + 1)) P.Coefficient hA' ≅
      Scheme.finiteEtaleTateLine T (P.coefficients.l ^ (r + 1)) P.Coefficient hA) :
    (d : ℕ) →
      Etale.affineLinearBaseCoefficient P.Coefficient (P.coefficients.l ^ (r' + 1)) hA' T d ≅
      Etale.affineLinearBaseCoefficient P.Coefficient (P.coefficients.l ^ (r + 1)) hA T d
  | 0 => Iso.refl _
  | d + 1 => Etale.ordinaryFiniteTensorRightMapIso P.Coefficient T
      (P.affineDiagonalPowerComparison T r r' hA hA' e d)
      ((shiftFunctor _ (2 : ℤ)).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso e))

/-- Normalized Tate restriction for the annihilator presentation ell^(r+1).
Source: pure-root tensor pullback (blueprint: lem-pur-affine-diagonal-integration-orientation). -/
def affineDiagonalTateRestriction (P : PurityFiniteSetting.{u})
    (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : P.Coefficient) = 0)
    {U B : Scheme.{u}} (f : U ⟶ B) (aB : B ⟶ Spec (.of P.field.k)) (d : ℕ) :=
  Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
    (P.coefficients.l ^ (r + 1)) hA
    (Etale.ambientAffineTraceTransport (P.coefficients.l ^ (r + 1))
      (pow_pos P.coefficients.prime.out.pos (r + 1)) P.Coefficient hA)
    f (WeilConjectures.PurityConventions.coefficientPower_isUnit P B aB r) d


end WeilConjectures.PurityFiniteSetting
