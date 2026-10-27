/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q45
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Sheaf.AlgebraicGeometry.Morphisms.GeometricallyIntegralFibreNeighbourhood
import Sheaf.TraceFormula.SmoothComponentPureTranscendental
import WeilConjectures.PointCount

/-!
# Geometrically integral base refinement of a finite-over-smooth diagram

Source: Stacks Project, more-morphisms.tex, Tag 057K,
lemma-local-local-structure-finite-type, proof from the connected component `T` through
its outer pullback diagram and marked residue-field identifications.
(blueprint: lem-trf-finite-smooth-integral-base-refinement).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem isIso_residueFieldMap_of_surjectiveOnStalks
    {X Y : Scheme.{u}} (f : X ⟶ Y) [SurjectiveOnStalks f] (x : X) :
    IsIso (f.residueFieldMap x) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨(f.residueFieldMap x).hom.injective, ?_⟩
  apply Function.Surjective.of_comp (g := Y.residue (f x))
  change Function.Surjective (Y.residue (f x) ≫ f.residueFieldMap x)
  rw [Scheme.residue_residueFieldMap]
  exact (X.residue_surjective x).comp (f.stalkMap_surjective x)

private theorem residueField_square
    {Z X Y S : Scheme.{u}} (p : Z ⟶ X) (q : Z ⟶ Y)
    (f : X ⟶ S) (g : Y ⟶ S) (hc : p ≫ f = q ≫ g)
    (z : Z) (x : X) (y : Y) (s : S)
    (hx : p z = x) (hy : q z = y) (hs : f x = s) (ht : g y = s) :
    (S.residueFieldCongr hs).inv ≫ f.residueFieldMap x ≫
        (X.residueFieldCongr hx).inv ≫ p.residueFieldMap z =
      (S.residueFieldCongr ht).inv ≫ g.residueFieldMap y ≫
        (Y.residueFieldCongr hy).inv ≫ q.residueFieldMap z := by
  subst x y s
  simp only [Scheme.residueFieldCongr_refl, Iso.refl_inv, Category.id_comp]
  rw [← Scheme.residueFieldMap_comp, Scheme.Hom.residueFieldMap_congr hc]
  simp

private theorem pullback_fibre_comparison_isIso
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (y : Y) [IsIso (g.residueFieldMap y)] :
    IsIso (pullback.map (pullback.snd f g) (Y.fromSpecResidueField y)
      f (S.fromSpecResidueField (g y)) (pullback.fst f g)
      (Spec.map (g.residueFieldMap y)) g pullback.condition.symm
      (g.SpecMap_residueFieldMap_fromSpecResidueField y).symm) := by
  exact (isPullback_fiberToSpecResidueField_of_isPullback
    (IsPullback.of_hasPullback f g) y).isIso_fst_of_isIso

private theorem pullback_residueFieldMap_isIso
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (z : ↥(pullback f g)) [IsIso (g.residueFieldMap (pullback.snd f g z))] :
    IsIso ((pullback.fst f g).residueFieldMap z) := by
  let q := pullback.snd f g
  let y := q z
  let F := pullback.map q (Y.fromSpecResidueField y)
    f (S.fromSpecResidueField (g y)) (pullback.fst f g)
    (Spec.map (g.residueFieldMap y)) g pullback.condition.symm
    (g.SpecMap_residueFieldMap_fromSpecResidueField y).symm
  have : IsIso F := pullback_fibre_comparison_isIso f g y
  let c := q.asFiber z
  have hc : q.fiberι y c = z := q.fiberι_asFiber z
  have : IsIso ((q.fiberι y).residueFieldMap c) :=
    isIso_residueFieldMap_of_surjectiveOnStalks _ _
  have : IsIso ((F ≫ f.fiberι (g y)).residueFieldMap c) := by
    rw [Scheme.residueFieldMap_comp]
    have : IsIso ((f.fiberι (g y)).residueFieldMap (F c)) :=
      isIso_residueFieldMap_of_surjectiveOnStalks _ _
    infer_instance
  have heq : F ≫ f.fiberι (g y) = q.fiberι y ≫ pullback.fst f g := by
    simp [F, Scheme.Hom.fiberι, pullback.map]
  have : IsIso ((q.fiberι y ≫ pullback.fst f g).residueFieldMap c) := heq ▸ inferInstance
  rw [Scheme.residueFieldMap_comp] at this
  have hfinal : IsIso ((pullback.fst f g).residueFieldMap (q.fiberι y c)) :=
    IsIso.of_isIso_comp_right _ ((q.fiberι y).residueFieldMap c)
  exact Eq.mp (congrArg
    (fun t ↦ IsIso ((pullback.fst f g).residueFieldMap t)) hc) hfinal

private theorem pullback_point_ext_of_residueFieldMap_isIso
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (z z' : ↥(pullback f g))
    [IsIso (g.residueFieldMap (pullback.snd f g z'))]
    (hx : pullback.fst f g z = pullback.fst f g z')
    (hy : pullback.snd f g z = pullback.snd f g z') : z = z' := by
  let T := Scheme.Pullback.Triplet.ofPoint z'
  have : IsIso (g.residueFieldMap T.y) := by
    change IsIso (g.residueFieldMap (pullback.snd f g z'))
    infer_instance
  have : IsIso ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y) :=
    inferInstance
  have : IsIso T.tensorInl :=
    (IsPushout.of_hasPushout _ _).isIso_inl_of_isIso
  have : Subsingleton (Spec T.tensor) :=
    (Scheme.homeoOfIso (asIso (Spec.map T.tensorInl))).injective.subsingleton
  apply Scheme.Pullback.carrierEquiv.injective
  apply Scheme.Pullback.carrierEquiv_eq_iff.mpr
  refine ⟨Scheme.Pullback.Triplet.ext hx hy, ?_⟩
  change (Spec.map _ _ : Spec T.tensor) = _
  exact Subsingleton.elim _ _

private theorem transport_rationalFunctionField
    {k k' L L' : Type u} [Field k] [Field k'] [Field L] [Field L']
    (a : k →+* L) (a' : k' →+* L') (α : k ≃+* k') (β : L ≃+* L')
    (hc : ∀ t, β (a t) = a' (α t)) :
    letI := a.toAlgebra
    letI := a'.toAlgebra
    (∃ r : ℕ, Nonempty (L ≃ₐ[k] FractionRing (MvPolynomial (Fin r) k))) →
      ∃ r : ℕ, Nonempty (L' ≃ₐ[k'] FractionRing (MvPolynomial (Fin r) k')) := by
  let := a.toAlgebra
  let := a'.toAlgebra
  rintro ⟨r, ⟨φ⟩⟩
  let δ : FractionRing (MvPolynomial (Fin r) k) ≃+*
      FractionRing (MvPolynomial (Fin r) k') :=
    IsFractionRing.ringEquivOfRingEquiv (MvPolynomial.mapEquiv (Fin r) α)
  refine ⟨r, ⟨{ β.symm.trans (φ.toRingEquiv.trans δ) with commutes' := ?_ }⟩⟩
  intro t
  change δ (φ (β.symm (a' t))) = algebraMap k' _ t
  have hβ : β.symm (a' t) = a (α.symm t) := by
    apply β.injective
    simpa only [β.apply_symm_apply, α.apply_symm_apply] using (hc (α.symm t)).symm
  rw [hβ]
  change δ (φ (algebraMap k L (α.symm t))) = _
  rw [φ.commutes]
  change δ (algebraMap (MvPolynomial (Fin r) k)
    (FractionRing (MvPolynomial (Fin r) k)) (MvPolynomial.C (α.symm t))) = _
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  simp only [MvPolynomial.mapEquiv_apply, MvPolynomial.map_C, RingHom.coe_coe,
    RingEquiv.apply_symm_apply]
  exact (IsScalarTower.algebraMap_apply k' (MvPolynomial (Fin r) k')
    (FractionRing (MvPolynomial (Fin r) k')) t).symm

private theorem purelyTranscendental_of_rational
    {k L : Type u} [Field k] [Field L] [Algebra k L]
    (h : ∃ r : ℕ, Nonempty (L ≃ₐ[k] FractionRing (MvPolynomial (Fin r) k))) :
    Algebra.IsPurelyTranscendentalExtension k L := by
  obtain ⟨r, ⟨e⟩⟩ := h
  let f : MvPolynomial (Fin r) k →ₐ[k] L :=
    e.symm.toAlgHom.comp (IsScalarTower.toAlgHom k
      (MvPolynomial (Fin r) k) (FractionRing (MvPolynomial (Fin r) k)))
  let t : Fin r → L := fun i ↦ f (MvPolynomial.X i)
  have hf : Function.Injective f :=
    e.symm.injective.comp (IsFractionRing.injective _ _)
  have ht : AlgebraicIndependent k t :=
    (MvPolynomial.algebraicIndependent_X (Fin r) k).map' hf
  have heval : MvPolynomial.aeval t = f := by
    ext i
    simp [t]
  refine ⟨Set.range t, ht.coe_range, ?_⟩
  apply top_unique
  intro x _
  rw [IntermediateField.mem_adjoin_range_iff]
  obtain ⟨p, q, _, hpq⟩ :=
    IsFractionRing.div_surjective (MvPolynomial (Fin r) k) (e x)
  refine ⟨p, q, ?_⟩
  rw [heval]
  change x = e.symm (algebraMap _ _ p) / e.symm (algebraMap _ _ q)
  rw [← map_div₀, hpq, e.symm_apply_apply]

private theorem exists_integral_fibre_open
    {Y S : Scheme.{u}} (h : Y ⟶ S) [Smooth h]
    [LocallyOfFiniteType h] [QuasiCompact h] (x : Y)
    (htrans : ∃ r : ℕ, Nonempty
      (@AlgEquiv (S.residueField (h x)) (Y.residueField x)
        (FractionRing (MvPolynomial (Fin r) (S.residueField (h x)))) _ _ _
        (h.residueFieldMap x).hom.toAlgebra inferInstance)) :
    ∃ T : (h.fiber (h x)).Opens,
      h.asFiber x ∈ T ∧ GeometricallyIntegral (T.ι ≫ h.fiberToSpecResidueField (h x)) := by
  let k := S.residueField (h x)
  let C := h.fiber (h x)
  let c := h.asFiber x
  let j := h.fiberToSpecResidueField (h x)
  let COver : C.Over (Spec (.of k)) := h.fiberOverSpecResidueField (h x)
  let := COver
  have : Smooth j := inferInstanceAs (Smooth (pullback.snd _ _))
  have : LocallyOfFiniteType j := inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
  have : QuasiCompact j := inferInstanceAs (QuasiCompact (pullback.snd _ _))
  have hc : h.fiberι (h x) c = x := h.fiberι_asFiber x
  have : IsIso ((h.fiberι (h x)).residueFieldMap c) :=
    isIso_residueFieldMap_of_surjectiveOnStalks _ _
  let β : Y.residueField x ≅ C.residueField c :=
    (Y.residueFieldCongr hc).symm ≪≫ asIso ((h.fiberι (h x)).residueFieldMap c)
  have hp : h.asFiberHom x = Spec.map β.inv ≫ C.fromSpecResidueField c := by
    apply (cancel_mono (h.fiberι (h x))).mp
    rw [h.asFiberHom_fiberι]
    rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Spec.map_comp_assoc]
    simp only [β, Iso.trans_inv, Iso.symm_inv, asIso_inv,
      IsIso.hom_inv_id_assoc]
    exact (Y.residueFieldCongr_fromSpecResidueField hc).symm
  have hβ : h.residueFieldMap x ≫ β.hom =
      CommRingCat.ofHom (j.residueFieldAlgebraMap c) := by
    apply (cancel_mono β.inv).mp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    apply Spec.map_injective
    rw [Spec.map_comp, j.specMap_residueFieldAlgebraMap, ← Category.assoc, ← hp]
    exact (h.asFiberHom_fiberToSpecResidueField x).symm
  have htrans' := transport_rationalFunctionField (h.residueFieldMap x).hom
    (j.residueFieldAlgebraMap c) (RingEquiv.refl k) β.commRingCatIsoToRingEquiv
    (fun t ↦ congrArg (fun a ↦ a.hom t) hβ) htrans
  have hpure : @Algebra.IsPurelyTranscendentalExtension k (C.residueField c) _ _
      (j.residueFieldAlgebraMap c).toAlgebra :=
    @purelyTranscendental_of_rational k (C.residueField c) inferInstance inferInstance
      (j.residueFieldAlgebraMap c).toAlgebra htrans'
  obtain ⟨T, hT, _, hTI⟩ := @exists_geometricallyIntegral_connectedComponent k inferInstance
    C COver (inferInstanceAs (LocallyOfFiniteType j))
    (inferInstanceAs (QuasiCompact j)) (inferInstanceAs (Smooth j)) c hpure
  refine ⟨T, ?_, hTI⟩
  rw [← SetLike.mem_coe, hT]
  exact mem_connectedComponent

private theorem fibre_transport_ι {Y S : Scheme.{u}} (h : Y ⟶ S)
    {s t : S} (e : s = t) :
    eqToHom (congrArg h.fiber e) ≫ h.fiberι t = h.fiberι s := by
  cases e
  simp

/-- A finite-over-smooth pointed diagram admits an elementary etale base refinement with
geometrically integral fibres, preserving the singleton finite fibre and marked residue fields.
Here `y₀ = π₀ w₀` and `s₀ = h₀ (π₀ w₀)`. Rational function fields in finitely many variables
are expressed literally as `FractionRing (MvPolynomial (Fin r) k)`, including `r = 0`.
Both residue-field squares use the actual induced maps, transported along the marked-point
identities by `residueFieldCongr`; no arbitrary field identifications are substituted.

Source: Stacks Project, more-morphisms.tex, Tag 057K,
lemma-local-local-structure-finite-type, connected component `T` and outer pullback diagram.
(blueprint: lem-trf-finite-smooth-integral-base-refinement).

Proof:
1. Finite presentation implies finite type by `lem-a1-map-over-base-finite-presentation`
   and `def-weil-finite-type-morphism`; finite-type and smooth-relative-dimension base change
   (`lem-sfb-finite-type-composition-base-change`,
   `lem-sbc-smooth-relative-dimension-permanence`) give a finite-type smooth special fibre.
   By `lem-weil-pbc-fibre-product-points` and
   `lem-weil-pbc-fibre-product-point-residue-field`, its point over `y₀` is unique and has
   residue field `κ(y₀)`, since `κ(y₀) ⊗_κ(s₀) κ(s₀) = κ(y₀)`.
   Apply `lem-trf-smooth-component-pure-transcendental`: its connected component `T` is
   open, quasi-compact and geometrically integral, hence geometrically irreducible.
2. Apply `lem-trf-geometrically-integral-fibre-neighbourhood` to `T`. This supplies affine
   `S₁`, an elementary etale map `e` and a quasi-compact open `V` with geometrically integral
   fibres and prescribed special fibre `T`. Smooth relative dimension is preserved by base
   change and restriction (`lem-sbc-smooth-relative-dimension-permanence`), since open
   immersions are etale (`lem-weil-pbc-etale-composition-cancellation`) and smooth of
   dimension zero (`lem-weil-pbc-etale-smooth-zero-dimensional-fibres`).
3. The projection `v : V ⟶ Y₀` is etale by base change and composition
   (`lem-weil-pbc-etale-scheme-base-change`, `lem-weil-pbc-etale-composition-cancellation`).
   Pull back `π₀` along `v`. The projection `ρ` is etale by the same base-change lemma,
   and `π₁` is finite by `lem-weil-pbc-finite-morphism-permanence`.
4. Write `α : κ(s₀) ≃ κ(s₁)` for the induced isomorphism. The tensor-field isomorphism
   `κ(y₀) ⊗_κ(s₀) κ(s₁) ≃ κ(y₀)` sends `a ⊗ b` to `a ι(α⁻¹(b))` and has inverse
   `a ↦ a ⊗ 1`. The fibre-product point lemma gives a unique point over `(y₀,s₁)`;
   its image in the old special fibre is the point of `T` from step 1, so it lies in `V`.
   The fibre-product residue-field lemma and open-immersion residue-field naturality
   (`lem-weil-pbc-residue-field-point-naturality`) give the canonical isomorphism
   `β : κ(y₀) ≃ κ(y₁)` and its compatibility with `α`.
5. Every point of the new finite fibre projects to `w₀` by the singleton-fibre hypothesis.
   The tensor-field isomorphism `κ(w₀) ⊗_κ(y₀) κ(y₁) ≃ κ(w₀)` sends `a ⊗ b` to
   `a j(β⁻¹(b))`, with inverse `a ↦ a ⊗ 1`. The fibre-product point and residue-field
   lemmas give the unique `w₁`, its image `w₀`, and the canonical residue-field isomorphism.
   The tensor formulas agree on the structural fields, giving the two displayed squares.
   Transport the original finite-variable rational function field isomorphism through
   `α` and `β`; this gives the final rational extension with the same identifications.
-/
theorem exists_finite_smooth_integral_base_refinement
    {S₀ Y₀ W₀ : Scheme.{u}} [IsAffine S₀] [IsAffine Y₀]
    (n : ℕ) (h₀ : Y₀ ⟶ S₀) [SmoothOfRelativeDimension n h₀]
    [LocallyOfFinitePresentation h₀] [QuasiCompact h₀] [QuasiSeparated h₀]
    (π₀ : W₀ ⟶ Y₀) [IsFinite π₀] (w₀ : W₀)
    (hfibre : π₀ ⁻¹' ({π₀ w₀} : Set Y₀) = ({w₀} : Set W₀))
    (htrans : ∃ r : ℕ, Nonempty
      (@AlgEquiv (S₀.residueField (h₀ (π₀ w₀))) (Y₀.residueField (π₀ w₀))
        (FractionRing (MvPolynomial (Fin r) (S₀.residueField (h₀ (π₀ w₀))))) _ _ _
        (h₀.residueFieldMap (π₀ w₀)).hom.toAlgebra inferInstance)) :
    ∃ (S₁ : Scheme.{u}) (e : S₁ ⟶ S₀) (s₁ : S₁)
      (hs : e s₁ = h₀ (π₀ w₀)),
      IsAffine S₁ ∧ Etale e ∧ IsIso (e.residueFieldMap s₁) ∧
      ∃ V : (pullback h₀ e).Opens,
        IsCompact (V : Set ↥(pullback h₀ e)) ∧
        SmoothOfRelativeDimension n (V.ι ≫ pullback.snd h₀ e) ∧
        GeometricallyIntegral (V.ι ≫ pullback.snd h₀ e) ∧
        Etale (V.ι ≫ pullback.fst h₀ e) ∧
        Etale (pullback.fst π₀ (V.ι ≫ pullback.fst h₀ e)) ∧
        IsFinite (pullback.snd π₀ (V.ι ≫ pullback.fst h₀ e)) ∧
        ∃ (y₁ : V.toScheme)
          (hy : (V.ι ≫ pullback.fst h₀ e) y₁ = π₀ w₀)
          (hyS : (V.ι ≫ pullback.snd h₀ e) y₁ = s₁)
          (w₁ : ↥(pullback π₀ (V.ι ≫ pullback.fst h₀ e)))
          (hw : pullback.snd π₀ (V.ι ≫ pullback.fst h₀ e) w₁ = y₁)
          (hr : pullback.fst π₀ (V.ι ≫ pullback.fst h₀ e) w₁ = w₀),
          (∀ y : V.toScheme,
            (V.ι ≫ pullback.fst h₀ e) y = π₀ w₀ →
            (V.ι ≫ pullback.snd h₀ e) y = s₁ → y = y₁) ∧
          (pullback.snd π₀ (V.ι ≫ pullback.fst h₀ e)) ⁻¹'
            ({y₁} : Set V.toScheme) = ({w₁} : Set ↥(pullback π₀
              (V.ι ≫ pullback.fst h₀ e))) ∧
          IsIso ((V.ι ≫ pullback.fst h₀ e).residueFieldMap y₁) ∧
          IsIso ((pullback.fst π₀ (V.ι ≫ pullback.fst h₀ e)).residueFieldMap w₁) ∧
          (h₀.residueFieldMap (π₀ w₀) ≫ (Y₀.residueFieldCongr hy).inv ≫
              (V.ι ≫ pullback.fst h₀ e).residueFieldMap y₁ =
            (S₀.residueFieldCongr hs).inv ≫ e.residueFieldMap s₁ ≫
              (S₁.residueFieldCongr hyS).inv ≫
              (V.ι ≫ pullback.snd h₀ e).residueFieldMap y₁) ∧
          (π₀.residueFieldMap w₀ ≫ (W₀.residueFieldCongr hr).inv ≫
              (pullback.fst π₀ (V.ι ≫ pullback.fst h₀ e)).residueFieldMap w₁ =
            (Y₀.residueFieldCongr hy).inv ≫
              (V.ι ≫ pullback.fst h₀ e).residueFieldMap y₁ ≫
              (V.toScheme.residueFieldCongr hw).inv ≫
              (pullback.snd π₀ (V.ι ≫ pullback.fst h₀ e)).residueFieldMap w₁) ∧
          (∃ r : ℕ, Nonempty
            (@AlgEquiv (S₁.residueField s₁) (V.toScheme.residueField y₁)
              (FractionRing (MvPolynomial (Fin r) (S₁.residueField s₁))) _ _ _
              (((S₁.residueFieldCongr hyS).inv ≫
                (V.ι ≫ pullback.snd h₀ e).residueFieldMap y₁).hom.toAlgebra)
              inferInstance)) := by
  -- Use the canonical cartesian fibre comparison for the marked residue-field identifications.
  have : Smooth h₀ := SmoothOfRelativeDimension.smooth n h₀
  obtain ⟨T, hxT, hTI⟩ := exists_integral_fibre_open h₀ (π₀ w₀) htrans
  have : GeometricallyIntegral (T.ι ≫ h₀.fiberToSpecResidueField (h₀ (π₀ w₀))) := hTI
  obtain ⟨S₁, e, s₁, hs, hSA, he, heκ, V, hVc, hVI, hVT⟩ :=
    exists_geometricallyIntegral_fibre_neighbourhood h₀ (h₀ (π₀ w₀)) T
  have : Etale e := he
  have : IsIso (e.residueFieldMap s₁) := heκ
  let q := pullback.snd h₀ e
  let p := pullback.fst h₀ e
  let F := pullback.map q (S₁.fromSpecResidueField s₁)
    h₀ (S₀.fromSpecResidueField (e s₁)) p (Spec.map (e.residueFieldMap s₁)) e
    pullback.condition.symm (e.SpecMap_residueFieldMap_fromSpecResidueField s₁).symm
  have : IsIso F := pullback_fibre_comparison_isIso h₀ e s₁
  let E : q.fiber s₁ ≅ h₀.fiber (h₀ (π₀ w₀)) :=
    asIso F ≪≫ eqToIso (congrArg h₀.fiber hs)
  let c₁ := E.inv (h₀.asFiber (π₀ w₀))
  have hEc : E.hom c₁ = h₀.asFiber (π₀ w₀) := by
    change (E.inv ≫ E.hom) _ = _
    simp
  have hEι : E.hom ≫ h₀.fiberι (h₀ (π₀ w₀)) = q.fiberι s₁ ≫ p := by
    dsimp only [E, Iso.trans_hom, asIso_hom, eqToIso.hom]
    rw [Category.assoc, fibre_transport_ι h₀ hs]
    simp [F, q, p, Scheme.Hom.fiberι, pullback.map]
  have hpy : p (q.fiberι s₁ c₁) = π₀ w₀ := by
    have H := congrArg (fun a ↦ a c₁) hEι
    simpa only [Scheme.Hom.comp_apply, hEc, Scheme.Hom.fiberι_asFiber] using H.symm
  have hqy : q (q.fiberι s₁ c₁) = s₁ :=
    (q.range_fiberι s₁).le ⟨c₁, rfl⟩
  have hcV : q.fiberι s₁ c₁ ∈ V := by
    change c₁ ∈ q.fiberι s₁ ⁻¹ᵁ V
    rw [hVT]
    change E.hom c₁ ∈ T
    rw [hEc]
    exact hxT
  let y₁ : V.toScheme := ⟨q.fiberι s₁ c₁, hcV⟩
  let v := V.ι ≫ p
  let h₁ := V.ι ≫ q
  have hy : v y₁ = π₀ w₀ := hpy
  have hyS : h₁ y₁ = s₁ := hqy
  have heκy : IsIso (e.residueFieldMap (q (V.ι y₁))) := by
    change IsIso (e.residueFieldMap (h₁ y₁))
    rw [hyS]
    infer_instance
  have hyv : ∀ y : V.toScheme, v y = π₀ w₀ → h₁ y = s₁ → y = y₁ := by
    intro y hy' hyS'
    apply V.ι.isOpenEmbedding.injective
    apply pullback_point_ext_of_residueFieldMap_isIso h₀ e
    · exact hy'.trans hy.symm
    · exact hyS'.trans hyS.symm
  have : IsIso (p.residueFieldMap (V.ι y₁)) :=
    pullback_residueFieldMap_isIso h₀ e (V.ι y₁)
  have hvκ : IsIso (v.residueFieldMap y₁) := by
    dsimp only [v]
    rw [Scheme.residueFieldMap_comp]
    infer_instance
  have : Etale v := inferInstanceAs (Etale (V.ι ≫ pullback.fst h₀ e))
  obtain ⟨w₁, hr, hw⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := π₀) (g := v) w₀ y₁ hy.symm
  have hvκw : IsIso (v.residueFieldMap (pullback.snd π₀ v w₁)) := by
    rw [hw]
    exact hvκ
  have hwκ : IsIso ((pullback.fst π₀ v).residueFieldMap w₁) :=
    pullback_residueFieldMap_isIso π₀ v w₁
  have hwf : (pullback.snd π₀ v) ⁻¹' ({y₁} : Set V.toScheme) =
      ({w₁} : Set ↥(pullback π₀ v)) := by
    ext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    refine ⟨fun hwy ↦ ?_, fun H ↦ H ▸ hw⟩
    have hπ : π₀ (pullback.fst π₀ v w) = π₀ w₀ := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, hwy, hy]
    have hrw : pullback.fst π₀ v w = w₀ := by
      have H : pullback.fst π₀ v w ∈ π₀ ⁻¹' ({π₀ w₀} : Set Y₀) := hπ
      rw [hfibre] at H
      exact H
    exact pullback_point_ext_of_residueFieldMap_isIso π₀ v w w₁
      (hrw.trans hr.symm) (hwy.trans hw.symm)
  have hcomm : v ≫ h₀ = h₁ ≫ e := by
    simp only [v, h₁, Category.assoc, p, q, pullback.condition]
  have hsq := residueField_square v h₁ h₀ e hcomm y₁ (π₀ w₀) s₁
    (h₀ (π₀ w₀)) hy hyS rfl hs
  have hsq' := residueField_square (pullback.fst π₀ v) (pullback.snd π₀ v)
    π₀ v pullback.condition w₁ w₀ y₁ (π₀ w₀) hr hw rfl hy
  simp only [Scheme.residueFieldCongr_refl, Iso.refl_inv, Category.id_comp] at hsq hsq'
  let α : S₀.residueField (h₀ (π₀ w₀)) ≅ S₁.residueField s₁ :=
    (S₀.residueFieldCongr hs).symm ≪≫ asIso (e.residueFieldMap s₁)
  let β : Y₀.residueField (π₀ w₀) ≅ V.toScheme.residueField y₁ :=
    (Y₀.residueFieldCongr hy).symm ≪≫ asIso (v.residueFieldMap y₁)
  have htrans₁ := transport_rationalFunctionField (h₀.residueFieldMap (π₀ w₀)).hom
    (((S₁.residueFieldCongr hyS).inv ≫ h₁.residueFieldMap y₁).hom)
    α.commRingCatIsoToRingEquiv β.commRingCatIsoToRingEquiv
    (fun t ↦ congrArg (fun a ↦ a.hom t) hsq) htrans
  let := smoothOfRelativeDimension_isStableUnderBaseChange n
  have : SmoothOfRelativeDimension n q :=
    MorphismProperty.pullback_snd h₀ e inferInstance
  have hVsm : SmoothOfRelativeDimension n h₁ := by
    have H : SmoothOfRelativeDimension (0 + n) h₁ := inferInstance
    simpa only [Nat.zero_add] using H
  exact ⟨S₁, e, s₁, hs, hSA, he, heκ, V, hVc, hVsm, hVI,
    inferInstance, inferInstance, inferInstance, y₁, hy, hyS, w₁, hw, hr,
    hyv, hwf, hvκ, hwκ, hsq, hsq', htrans₁⟩

end AlgebraicGeometry
