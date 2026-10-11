/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import WeilConjectures.RingTheory.ProEtale.ClosedLiftPushout

/-!
# Lifting the affine pro-étale site of a closed subscheme

Let `X = Spec A` be affine and `i : Z ⟶ X` a closed immersion, so `Z = Spec (A ⧸ I)`. Base change
along `i` is a functor `u : X.AffineProEt ⥤ Z.AffineProEt` between the affine pro-étale sites
(`AlgebraicGeometry.Scheme.AffineProEt.baseChange`). This file constructs its left adjoint
`v : Z.AffineProEt ⥤ X.AffineProEt`, sending `V = Spec C̄` to `Spec H_A(C̄)`, where `H_A(C̄)` is
the ind-étale `A`-algebra `Algebra.ClosedLift A C̄` (blueprint `def-exc-closed-site-lift`), and
shows that the unit `V ⟶ u (v V)` is an isomorphism (blueprint `lem-exc-closed-site-adjunction`).

## Main definitions

- `AlgebraicGeometry.Scheme.AffineProEt.closedLift`: the functor `v`.
- `AlgebraicGeometry.Scheme.AffineProEt.closedLiftAdjunction`: the adjunction `v ⊣ u`.

## Main results

- `AlgebraicGeometry.Scheme.AffineProEt.isIso_closedLiftAdjunction_unit`: `u v ≅ 𝟭`.

## Implementation notes

The functor `v` is the left adjoint built by `CategoryTheory.Adjunction.leftAdjointOfEquiv` from
the universal property of the map `η_V : V ⟶ u (v V)` given by `H_A(C̄) ⟶ C̄`: morphisms
`v V ⟶ Y` are the `A`-algebra maps `Γ(Y) ⟶ H_A(C̄)`, and these correspond to the `A`-algebra maps
`Γ(Y) ⟶ C̄` since `Γ(Y)` is ind-étale over `A` (`Algebra.ClosedLift.bijective_comp_toAlgHom`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.AffineProEt

variable {X Z : Scheme.{u}} (i : Z ⟶ X)

/-- Base change along an affine morphism `i : Z ⟶ X`, as a functor between the affine pro-étale
sites: the functor `u` of blueprint `def-exc-closed-site-lift`. -/
noncomputable abbrev baseChange [IsAffineHom i] : X.AffineProEt ⥤ Z.AffineProEt :=
  MorphismProperty.Over.pullback proAffineEtale ⊤ i

/-- The `Γ(X)`-algebra structure on the global sections of an object of `Z.AffineProEt`. -/
noncomputable abbrev algebraΓ (V : Z.AffineProEt) : Algebra Γ(X, ⊤) Γ(V.left, ⊤) :=
  (V.hom ≫ i).appTop.hom.toAlgebra

/-- The ring `H_A(C̄)` of blueprint `def-exc-ind-etale-closed-lift` for `A = Γ(X)` and
`C̄ = Γ(V)`. -/
noncomputable def closedLiftRing (V : Z.AffineProEt) : CommRingCat.{u} :=
  letI := algebraΓ i V
  .of (Algebra.ClosedLift Γ(X, ⊤) Γ(V.left, ⊤))

/-- The structure map `A ⟶ H_A(C̄)`. -/
noncomputable def closedLiftRingAlgebraMap (V : Z.AffineProEt) : Γ(X, ⊤) ⟶ closedLiftRing i V :=
  letI := algebraΓ i V
  CommRingCat.ofHom (algebraMap Γ(X, ⊤) (Algebra.ClosedLift Γ(X, ⊤) Γ(V.left, ⊤)))

/-- The map `H_A(C̄) ⟶ C̄`. -/
noncomputable def closedLiftRingToΓ (V : Z.AffineProEt) : closedLiftRing i V ⟶ Γ(V.left, ⊤) :=
  letI := algebraΓ i V
  CommRingCat.ofHom (Algebra.ClosedLift.toAlgHom Γ(X, ⊤) Γ(V.left, ⊤)).toRingHom

@[reassoc]
lemma closedLiftRingAlgebraMap_toΓ (V : Z.AffineProEt) :
    closedLiftRingAlgebraMap i V ≫ closedLiftRingToΓ i V = (V.hom ≫ i).appTop := by
  let := algebraΓ i V
  ext a
  exact (Algebra.ClosedLift.toAlgHom Γ(X, ⊤) Γ(V.left, ⊤)).commutes a

lemma indEtale_closedLiftRingAlgebraMap (V : Z.AffineProEt) :
    (closedLiftRingAlgebraMap i V).hom.IndEtale := by
  let := algebraΓ i V
  exact (RingHom.IndEtale.algebraMap_iff Γ(X, ⊤) (Algebra.ClosedLift Γ(X, ⊤) Γ(V.left, ⊤))).2
    inferInstance

variable [IsAffine X]

/-- Blueprint `def-exc-closed-site-lift`, on objects: the lift `v(V) = Spec H_A(Γ(V))` of an
object `V` of the affine pro-étale site of `Z`. -/
noncomputable def closedLiftObj (V : Z.AffineProEt) : X.AffineProEt :=
  mk (Spec.map (closedLiftRingAlgebraMap i V) ≫ X.isoSpec.inv)
    (proAffineEtale.comp_mem _ _
      (proAffineEtale_Spec_iff.2 (indEtale_closedLiftRingAlgebraMap i V))
      (proAffineEtale.of_isAffine _))

@[simp]
lemma closedLiftObj_left (V : Z.AffineProEt) :
    (closedLiftObj i V).left = Spec (closedLiftRing i V) :=
  rfl

@[simp]
lemma closedLiftObj_hom (V : Z.AffineProEt) :
    (closedLiftObj i V).hom = Spec.map (closedLiftRingAlgebraMap i V) ≫ X.isoSpec.inv :=
  rfl

/-- A morphism of affine schemes over `X` out of `Spec R` is `Spec` of its ring map on global
sections, composed with `isoSpec`. -/
lemma eq_specMap_preimage {R : CommRingCat.{u}} {Y : Scheme.{u}} [IsAffine Y]
    (g : Spec R ⟶ Y) : g = Spec.map (Spec.preimage (g ≫ Y.isoSpec.hom)) ≫ Y.isoSpec.inv := by
  rw [Spec.map_preimage, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- For a morphism `g : Spec R ⟶ Y` over `X` to an affine `X`-scheme `h : Y ⟶ X`, the ring map
`Γ(Y) ⟶ R` of `g` is compatible with the maps from `Γ(X)`. -/
lemma appTop_comp_specPreimage {R : CommRingCat.{u}} (f : Γ(X, ⊤) ⟶ R) {Y : Scheme.{u}}
    [IsAffine Y] (h : Y ⟶ X) (g : Spec R ⟶ Y) (hg : g ≫ h = Spec.map f ≫ X.isoSpec.inv) :
    h.appTop ≫ Spec.preimage (g ≫ Y.isoSpec.hom) = f := by
  refine Spec.map_injective ?_
  rw [Spec.map_comp, Spec.map_preimage, Category.assoc, Scheme.isoSpec_hom_naturality,
    ← Category.assoc, hg, Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable [IsClosedImmersion i]

/-- The map `V ⟶ u(v(V))`, induced by `H_A(Γ(V)) ⟶ Γ(V)`. -/
noncomputable def closedLiftUnit (V : Z.AffineProEt) :
    V ⟶ (baseChange i).obj (closedLiftObj i V) :=
  MorphismProperty.Over.homMk
    (pullback.lift (V.left.isoSpec.hom ≫ Spec.map (closedLiftRingToΓ i V)) V.hom (by
      rw [closedLiftObj_hom, Category.assoc, ← Spec.map_comp_assoc,
        closedLiftRingAlgebraMap_toΓ, Scheme.isoSpec_hom_naturality_assoc, Iso.hom_inv_id,
        Category.comp_id]))
    (pullback.lift_snd _ _ _)

@[reassoc (attr := simp)]
lemma closedLiftUnit_left_fst (V : Z.AffineProEt) :
    (closedLiftUnit i V).left ≫ pullback.fst _ _ =
      V.left.isoSpec.hom ≫ Spec.map (closedLiftRingToΓ i V) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma closedLiftUnit_left_snd (V : Z.AffineProEt) :
    (closedLiftUnit i V).left ≫ pullback.snd _ _ = V.hom :=
  pullback.lift_snd _ _ _

/-- The universal property of `closedLiftUnit`: every morphism `V ⟶ u(Y)` factors uniquely
through `V ⟶ u(v(V))`. -/
lemma bijective_closedLiftUnit_comp (V : Z.AffineProEt) (Y : X.AffineProEt) :
    Function.Bijective fun g : closedLiftObj i V ⟶ Y ↦
      closedLiftUnit i V ≫ (baseChange i).map g := by
  let := algebraΓ i V
  have : IsAffine ((𝟭 Scheme).obj Y.left) := inferInstanceAs (IsAffine Y.left)
  have : IsAffine ((Functor.fromPUnit X).obj Y.right) := inferInstanceAs (IsAffine X)
  let : Algebra Γ(X, ⊤) Γ(Y.left, ⊤) := Y.hom.appTop.hom.toAlgebra
  have : Algebra.IndEtale Γ(X, ⊤) Γ(Y.left, ⊤) :=
    (RingHom.IndEtale.algebraMap_iff _ _).1
      (indEtale_appTop_of_proAffineEtale Y.prop)
  have hbij := Algebra.ClosedLift.bijective_comp_toAlgHom (A := Γ(X, ⊤)) (C := Γ(V.left, ⊤))
    Γ(Y.left, ⊤)
  -- the ring map `Γ(Y) ⟶ H_A(Γ(V))` of a morphism `v(V) ⟶ Y`
  let pre (g : closedLiftObj i V ⟶ Y) : Γ(Y.left, ⊤) ⟶ closedLiftRing i V :=
    Spec.preimage (g.left ≫ Y.left.isoSpec.hom)
  have hpre (g : closedLiftObj i V ⟶ Y) : g.left = Spec.map (pre g) ≫ Y.left.isoSpec.inv :=
    eq_specMap_preimage g.left
  -- as an `A`-algebra map
  let alg (g : closedLiftObj i V ⟶ Y) :
      Γ(Y.left, ⊤) →ₐ[Γ(X, ⊤)] Algebra.ClosedLift Γ(X, ⊤) Γ(V.left, ⊤) :=
    { (pre g).hom with
      commutes' a := congrArg (fun f ↦ f.hom a) (appTop_comp_specPreimage
        (closedLiftRingAlgebraMap i V) Y.hom g.left (MorphismProperty.Over.w g)) }
  -- the composite with `pullback.fst` of the image of `g`
  have hfst (g : closedLiftObj i V ⟶ Y) :
      (closedLiftUnit i V ≫ (baseChange i).map g).left ≫ pullback.fst _ _ =
        V.left.isoSpec.hom ≫ Spec.map (pre g ≫ closedLiftRingToΓ i V) ≫
          Y.left.isoSpec.inv := by
    rw [MorphismProperty.Comma.comp_left, Category.assoc, MorphismProperty.Over.pullback_map_left,
      pullback.lift_fst, closedLiftUnit_left_fst_assoc, hpre g, Spec.map_comp_assoc]
  refine ⟨fun g g' h ↦ ?_, fun ψ ↦ ?_⟩
  · have h' := congrArg (fun f ↦ f.left ≫ pullback.fst Y.hom i) h
    dsimp only at h'
    rw [hfst, hfst, cancel_epi, cancel_mono] at h'
    have h1 : pre g ≫ closedLiftRingToΓ i V = pre g' ≫ closedLiftRingToΓ i V :=
      Spec.map_injective h'
    have h2 : alg g = alg g' := by
      refine hbij.1 (AlgHom.coe_ringHom_injective ?_)
      exact congrArg CommRingCat.Hom.hom h1
    have h3 : pre g = pre g' := CommRingCat.hom_ext (congrArg AlgHom.toRingHom h2)
    exact MorphismProperty.Over.Hom.ext (by rw [hpre g, hpre g', h3])
  · let b : V.left ⟶ Y.left := ψ.left ≫ pullback.fst _ _
    have hb : b ≫ Y.hom = V.hom ≫ i := by
      simp only [b, Category.assoc, pullback.condition]
      rw [← Category.assoc]
      exact congrArg (· ≫ i) (MorphismProperty.Over.w ψ)
    let β : Γ(Y.left, ⊤) →ₐ[Γ(X, ⊤)] Γ(V.left, ⊤) :=
      { b.appTop.hom with
        commutes' a := by
          change b.appTop (Y.hom.appTop a) = (V.hom ≫ i).appTop a
          rw [← hb, Scheme.Hom.comp_appTop]
          rfl }
    obtain ⟨φ, hφ⟩ := hbij.2 β
    let φ' : Γ(Y.left, ⊤) ⟶ closedLiftRing i V := CommRingCat.ofHom φ.toRingHom
    have hφ' : φ' ≫ closedLiftRingToΓ i V = b.appTop :=
      CommRingCat.hom_ext (congrArg AlgHom.toRingHom hφ)
    let g : closedLiftObj i V ⟶ Y := MorphismProperty.Over.homMk
      (Spec.map φ' ≫ Y.left.isoSpec.inv) (by
        rw [closedLiftObj_hom, Category.assoc, ← Scheme.isoSpec_inv_naturality,
          ← Spec.map_comp_assoc]
        congr 2
        ext a
        exact φ.commutes a)
    have hg : pre g = φ' := by
      change Spec.preimage ((Spec.map φ' ≫ Y.left.isoSpec.inv) ≫ Y.left.isoSpec.hom) = φ'
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Spec.preimage_map]
    refine ⟨g, MorphismProperty.Over.Hom.ext (pullback.hom_ext ?_ ?_)⟩
    · rw [hfst, hg, hφ', ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    · rw [MorphismProperty.Comma.comp_left, Category.assoc,
        MorphismProperty.Over.pullback_map_left, pullback.lift_snd, closedLiftUnit_left_snd]
      exact (MorphismProperty.Over.w ψ).symm

/-- The hom-set bijection `(v(V) ⟶ Y) ≃ (V ⟶ u(Y))` of blueprint
`lem-exc-closed-site-adjunction`. -/
noncomputable def closedLiftHomEquiv (V : Z.AffineProEt) (Y : X.AffineProEt) :
    (closedLiftObj i V ⟶ Y) ≃ (V ⟶ (baseChange i).obj Y) :=
  Equiv.ofBijective _ (bijective_closedLiftUnit_comp i V Y)

/-- Blueprint `def-exc-closed-site-lift`: for `X = Spec A` affine and a closed immersion
`i : Z ⟶ X`, the functor `v : Z.AffineProEt ⥤ X.AffineProEt`, `Spec C̄ ↦ Spec H_A(C̄)`, whose maps
are the opposites of the maps of `A`-algebras `H_A(C̄') ⟶ H_A(C̄)` supplied by the universal
property of `H_A`. -/
noncomputable def closedLift : Z.AffineProEt ⥤ X.AffineProEt :=
  Adjunction.leftAdjointOfEquiv (closedLiftHomEquiv i)
    fun _ _ _ _ _ ↦ by simp [closedLiftHomEquiv]

@[simp]
lemma closedLift_obj (V : Z.AffineProEt) : (closedLift i).obj V = closedLiftObj i V :=
  rfl

/-- Blueprint `lem-exc-closed-site-adjunction`: the functor `v` of
`AlgebraicGeometry.Scheme.AffineProEt.closedLift` is left adjoint to base change `u`. -/
noncomputable def closedLiftAdjunction : closedLift i ⊣ baseChange i :=
  Adjunction.adjunctionOfEquivLeft _ _

lemma closedLiftAdjunction_unit_app (V : Z.AffineProEt) :
    (closedLiftAdjunction i).unit.app V = closedLiftUnit i V := by
  simp [closedLiftAdjunction, Adjunction.adjunctionOfEquivLeft, closedLiftHomEquiv]

/-- The square `Spec Γ(V) ⟶ Spec H_A(Γ(V))`, `V ⟶ Z`, `Spec H_A(Γ(V)) ⟶ X`, `Z ⟶ X` is
cartesian: this is `Algebra.ClosedLift.isPushout_reduction`, since `Γ(V)` is ind-étale over
`Γ(Z) = A ⧸ I` (blueprint `lem-exc-closed-lift-reduction`). -/
lemma isPullback_closedLiftUnit (V : Z.AffineProEt) :
    IsPullback (V.left.isoSpec.hom ≫ Spec.map (closedLiftRingToΓ i V)) V.hom
      (closedLiftObj i V).hom i := by
  have : IsAffine Z := isAffine_of_isAffineHom i
  have : IsAffine ((𝟭 Scheme).obj V.left) := inferInstanceAs (IsAffine V.left)
  have : IsAffine ((Functor.fromPUnit Z).obj V.right) := inferInstanceAs (IsAffine Z)
  let := algebraΓ i V
  let π := i.appTop
  have hπ : Function.Surjective π := (IsClosedImmersion.isAffine_surjective_of_isAffine i).2
  let J := RingHom.ker π.hom
  let eq : Γ(X, ⊤) ⧸ J ≃+* Γ(Z, ⊤) := RingHom.quotientKerEquivOfSurjective hπ
  let : Algebra (Γ(X, ⊤) ⧸ J) Γ(V.left, ⊤) := (V.hom.appTop.hom.comp eq.toRingHom).toAlgebra
  have : IsScalarTower Γ(X, ⊤) (Γ(X, ⊤) ⧸ J) Γ(V.left, ⊤) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      change (V.hom ≫ i).appTop a = V.hom.appTop (eq (Ideal.Quotient.mk J a))
      rw [RingHom.quotientKerEquivOfSurjective_apply_mk, Scheme.Hom.comp_appTop]
      rfl
  have : Algebra.IndEtale (Γ(X, ⊤) ⧸ J) Γ(V.left, ⊤) :=
    (RingHom.IndEtale.algebraMap_iff _ _).1
      (RingHom.IndEtale.isStableUnderBaseChange.localizationPreserves.away.respectsIso.2 _ _
        (indEtale_appTop_of_proAffineEtale V.prop))
  have hpo : IsPushout (closedLiftRingAlgebraMap i V) π (closedLiftRingToΓ i V)
      V.hom.appTop :=
    (Algebra.ClosedLift.isPushout_reduction _ _ J).of_iso (Iso.refl _) (Iso.refl _)
      eq.toCommRingCatIso (Iso.refl _) ((Category.comp_id _).trans (Category.id_comp _).symm)
      (by ext a; exact RingHom.quotientKerEquivOfSurjective_apply_mk hπ a)
      ((Category.comp_id _).trans (Category.id_comp _).symm) (by ext a; rfl)
  exact (isPullback_SpecMap_of_isPushout _ _ _ _ hpo).of_iso V.left.isoSpec.symm (Iso.refl _)
    Z.isoSpec.symm X.isoSpec.symm (by simp) (Scheme.isoSpec_inv_naturality V.hom) (by simp)
    (Scheme.isoSpec_inv_naturality i)

instance isIso_closedLiftUnit (V : Z.AffineProEt) : IsIso (closedLiftUnit i V) := by
  have hpb := isPullback_closedLiftUnit i V
  have : (closedLiftUnit i V).left = hpb.isoPullback.hom := by
    refine pullback.hom_ext ?_ ?_
    · rw [closedLiftUnit_left_fst, IsPullback.isoPullback_hom_fst]
    · rw [closedLiftUnit_left_snd, IsPullback.isoPullback_hom_snd]
  have : IsIso (closedLiftUnit i V).left := by
    rw [this]
    infer_instance
  let e : V ≅ (baseChange i).obj (closedLiftObj i V) :=
    MorphismProperty.Over.isoMk (asIso (closedLiftUnit i V).left)
      (MorphismProperty.Over.w (closedLiftUnit i V))
  have he : e.hom = closedLiftUnit i V := MorphismProperty.Over.Hom.ext rfl
  rw [← he]
  infer_instance

/-- Blueprint `lem-exc-closed-site-adjunction`, the unit: `u ∘ v` is canonically the identity,
since `H_A(C̄)` reduces to `C̄` (blueprint `lem-exc-closed-lift-reduction`). -/
instance isIso_closedLiftAdjunction_unit : IsIso (closedLiftAdjunction i).unit := by
  have (V : Z.AffineProEt) : IsIso ((closedLiftAdjunction i).unit.app V) := by
    rw [closedLiftAdjunction_unit_app]
    exact isIso_closedLiftUnit i V
  exact NatIso.isIso_of_isIso_app _

/-- The lift `v` is fully faithful, being a left adjoint with invertible unit. -/
noncomputable def fullyFaithfulClosedLift : (closedLift i).FullyFaithful :=
  (closedLiftAdjunction i).fullyFaithfulLOfIsIsoUnit

end AlgebraicGeometry.Scheme.AffineProEt
