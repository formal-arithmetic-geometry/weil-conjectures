/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q06
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
import Mathlib.AlgebraicGeometry.Group.Smooth
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.FiniteType
import WeilConjectures.Mathlib.RingTheory.Nilpotent.GeometricallyReduced

/-!
# Smooth split-lattice torus projections and reduced products

Source: ILO, Travaux de Gabber, Exposé VIII, Lemma 3.2.12(i), printed p.104,
and the torus product in 3.2.19, printed p.106; Stacks Project, Tags 034N and 01J2
(blueprint: lem-trf-split-lattice-torus-projection).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Algebra.TensorProduct.rightAlgebra

private theorem lattice_domain (k : Type u) [Field k] (L : Type u) [AddCommGroup L]
    (r : ℕ) (b : Module.Basis (Fin r) ℤ L) (K : Type v) [Field K] :
    IsDomain (AddMonoidAlgebra K L) := by
  have : UniqueSums L := UniqueSums.of_injective_addHom b.repr.toAddMonoidHom.toAddHom
    b.repr.injective inferInstance
  infer_instance

private noncomputable def lattice_scalarEquiv
    (k : Type u) [Field k] (L : Type u) [AddCommGroup L]
    (K : Type v) [Field K] [Algebra k K] :
    @AlgEquiv K (AddMonoidAlgebra k L ⊗[k] K) (AddMonoidAlgebra K L)
      _ _ _ (Algebra.TensorProduct.rightAlgebra (R := k)) _ :=
  (Algebra.TensorProduct.commRight k K (AddMonoidAlgebra k L)).symm.trans
    (AddMonoidAlgebra.scalarTensorEquiv k K)

private theorem lattice_reduced_tensor
    (k : Type u) [Field k] (L : Type u) [AddCommGroup L]
    (r : ℕ) (b : Module.Basis (Fin r) ℤ L)
    (R : Type v) [CommRing R] [Algebra k R] [_root_.IsReduced R] :
    _root_.IsReduced (R ⊗[k] AddMonoidAlgebra k L) := by
  apply isReduced_tensorProduct_of_forall_residueField
  intro p
  have := lattice_domain k L r b p.asIdeal.ResidueField
  exact isReduced_of_injective
    (AddMonoidAlgebra.scalarTensorEquiv k p.asIdeal.ResidueField (M := L)).toRingHom
    (AddMonoidAlgebra.scalarTensorEquiv k p.asIdeal.ResidueField (M := L)).injective

private theorem lattice_reduced_pullback
    (k : Type u) [Field k] (L : Type u) [AddCommGroup L]
    (r : ℕ) (b : Module.Basis (Fin r) ℤ L)
    (Y : Scheme.{u}) (y : Y ⟶ Spec (.of k)) [IsReduced Y] :
    IsReduced (pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k (AddMonoidAlgebra k L)))) y) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap k (AddMonoidAlgebra k L)))
  refine @IsReduced.of_openCover _ (Y.affineOpenCover.openCover.pullback₁ (pullback.snd f y)) ?_
  intro i
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Y.affineOpenCover.f i ≫ y)
  algebraize [φ.hom]
  have : _root_.IsReduced (Y.affineOpenCover.X i) :=
    (affine_isReduced_iff _).mp (isReduced_of_isOpenImmersion (Y.affineOpenCover.f i))
  have := lattice_reduced_tensor k L r b (Y.affineOpenCover.X i)
  have : _root_.IsReduced (AddMonoidAlgebra k L ⊗[k] Y.affineOpenCover.X i) :=
    isReduced_of_injective (Algebra.TensorProduct.comm k _ _).toRingHom
      (Algebra.TensorProduct.comm k _ _).injective
  have : IsReduced (pullback f (Spec.map φ)) :=
    isReduced_of_isOpenImmersion (pullbackSpecIso k (AddMonoidAlgebra k L)
      (Y.affineOpenCover.X i)).hom
  exact isReduced_of_isOpenImmersion
    ((pullbackLeftPullbackSndIso f y (Y.affineOpenCover.f i)) ≪≫
      pullback.congrHom rfl hφ.symm).hom

/-- Split-lattice torus projections are smooth, have the augmentation section, and are
surjective. The torus is smooth over its field, its scalar extension is the specified group
algebra over every extension field and is a domain, and its products with reduced algebras
and reduced schemes are reduced. The `K`-algebra structure on the right tensor factor is
specified explicitly by `Algebra.TensorProduct.rightAlgebra`.

Source: ILO, Exposé VIII, Lemma 3.2.12(i), p.104, and 3.2.19, p.106; Stacks Tags 034N,
`lemma-geometrically-reduced-any-reduced-base-change`, and 01J2, `lemma-affine-reduced`
(blueprint: lem-trf-split-lattice-torus-projection).

Proof plan:
1. Apply `lem-trf-lattice-torus-coordinates-action` to the integral basis. On every affine
   base chart Spec R the product has ring R[t_i,u_i]/(t_i*u_i-1). This gives local finite
   presentation, without the extra monoscheme assumptions of that node's action clause.
2. For a square-zero ideal I in B, lift inverse units vbar,wbar in B/I to v,w in B.
   If d = v*w-1 lies in I, then w*(1-d) is an inverse of v because d^2=0. Lift the basis
   monomials this way and extend using unique integral coordinates to a k-algebra map.
   Pair its spectrum with the prescribed map to Y using the fibre-product property.
   The lifting criterion of `def-sbc-smooth-morphisms`, with
   `def-sbc-first-order-thickening`, proves smoothness of the projection.
3. Augmentation sends every monomial to one and retracts the scalar inclusion. Pair its
   spectrum with the identity of Y to obtain the displayed section. It proves pointwise
   surjectivity. Taking Y=Spec k gives smoothness of the torus itself.
4. Scalar extension sends e^l tensor c to c*e^l. Its inverse sends a finite sum of c_l*e^l
   to the sum of e^l tensor c_l. The tensor relations of
   `def-weil-pbc-module-tensor-product` give a well-defined map; checking monomial tensors
   proves multiplicativity, scalar compatibility, and both inverse identities.
5. The basis generates a finitely generated positive submonoid of the torsion-free group L.
   Apply `lem-trf-monoid-algebra-domain-fraction` over K to obtain that K[L] is a domain.
   It is reduced, hence so is the field-extended algebra in step 4. Apply
   `lem-trf-geometrically-reduced-base-change` to obtain reducedness for every reduced R.
6. The affine charts in step 1 are reduced by step 5 and
   `lem-weil-pbc-affine-scheme-reduced-iff`. Their local rings cover those of the product,
   proving reducedness by `def-pc-reduced-scheme`. Empty Y, reducible Y, zero R, arbitrary
   characteristic and inseparable extensions are allowed. For r=0 the basis is empty,
   L is zero, and the projection is the identity up to the canonical isomorphism. -/
theorem split_lattice_torus_projection
    (k : Type u) [Field k] (L : Type u) [AddCommGroup L]
    (r : ℕ) (_b : Module.Basis (Fin r) ℤ L)
    (Y : Scheme.{u}) (y : Y ⟶ Spec (.of k)) :
    Smooth (pullback.snd
      (Spec.map (CommRingCat.ofHom (algebraMap k (AddMonoidAlgebra k L)))) y) ∧
    (∃ s : Y ⟶ pullback
        (Spec.map (CommRingCat.ofHom (algebraMap k (AddMonoidAlgebra k L)))) y,
      s ≫ pullback.snd
        (Spec.map (CommRingCat.ofHom (algebraMap k (AddMonoidAlgebra k L)))) y = 𝟙 Y ∧
      s ≫ pullback.fst
        (Spec.map (CommRingCat.ofHom (algebraMap k (AddMonoidAlgebra k L)))) y =
          y ≫ Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.lift k k L 1).toRingHom)) ∧
    Surjective (pullback.snd
      (Spec.map (CommRingCat.ofHom (algebraMap k (AddMonoidAlgebra k L)))) y) ∧
    Smooth (Spec.map (CommRingCat.ofHom (algebraMap k (AddMonoidAlgebra k L)))) ∧
    (∀ (K : Type (max u v)) [Field K] [Algebra k K],
      (∃ e : @AlgEquiv K (AddMonoidAlgebra k L ⊗[k] K) (AddMonoidAlgebra K L)
          _ _ _ (Algebra.TensorProduct.rightAlgebra (R := k)) _,
        ∀ (l : L) (c : K),
          e (AddMonoidAlgebra.single l (1 : k) ⊗ₜ[k] c) = AddMonoidAlgebra.single l c) ∧
      IsDomain (AddMonoidAlgebra K L)) ∧
    (∀ (R : Type (max u w)) [CommRing R] [Algebra k R] [_root_.IsReduced R],
      _root_.IsReduced (R ⊗[k] AddMonoidAlgebra k L)) ∧
    (IsReduced Y → IsReduced (pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k (AddMonoidAlgebra k L)))) y)) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap k (AddMonoidAlgebra k L)))
  have hgeom : GeometricallyReduced f := by
    refine ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.mpr ?_⟩
    intro K _ _
    exact lattice_reduced_pullback k L r _b _ _
  have : GeometricallyReduced f := hgeom
  have : Module.Finite ℤ L := Module.Finite.of_basis _b
  have : AddGroup.FG L := Module.Finite.iff_addGroup_fg.mp this
  have : Algebra.FiniteType k (AddMonoidAlgebra k L) :=
    AddMonoidAlgebra.finiteType_iff_group_fg.mpr this
  have : LocallyOfFiniteType f := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have : GrpObj (Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap k (AddMonoidAlgebra k L))))) :=
    inferInstanceAs (GrpObj ((Spec (.of (AddMonoidAlgebra k L))).asOver (Spec (.of k))))
  have hsmooth : Smooth f := smooth_of_grpObj f
  have : Smooth f := hsmooth
  let ε := Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.lift k k L 1).toRingHom)
  have hε : ε ≫ f = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext c
    simp
  let s : Y ⟶ pullback f y := pullback.lift (y ≫ ε) (𝟙 Y) (by simp [Category.assoc, hε])
  have hs : s ≫ pullback.snd f y = 𝟙 Y := pullback.lift_snd ..
  refine ⟨inferInstance, ⟨s, hs, pullback.lift_fst ..⟩, ?_, hsmooth, ?_, ?_, ?_⟩
  · constructor
    intro x
    refine ⟨s x, ?_⟩
    change (s ≫ pullback.snd f y) x = x
    rw [hs]
    rfl
  · intro K _ _
    refine ⟨⟨lattice_scalarEquiv k L K, ?_⟩, lattice_domain k L r _b K⟩
    intro l c
    apply (lattice_scalarEquiv k L K).symm.injective
    simp [lattice_scalarEquiv, AlgEquiv.symm_trans_apply]
  · intro R _ _ _
    exact lattice_reduced_tensor k L r _b R
  · intro hY
    have := hY
    exact lattice_reduced_pullback k L r _b Y y

end AlgebraicGeometry
