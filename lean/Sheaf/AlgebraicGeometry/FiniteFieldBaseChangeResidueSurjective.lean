/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A8
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Algebra.Category.Ring.Constructions
public import WeilConjectures.PointCount
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.IntegralDomain

/-! # Residue tensors for constant extensions of finite fields

Source: Stacks Project, Schemes, Tag 01JT, lemma-points-fibre-product.
(blueprint: lem-zl-finite-field-base-change-residue-surjective)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry

/-- The actual residue tensor map at a closed point of a finite constant extension
is surjective. The equation `h` identifies the two actual base-field maps.
Source: Stacks Project, Schemes, Tag 01JT, lemma-points-fibre-product, residue-field clause.
(blueprint: lem-zl-finite-field-base-change-residue-surjective)

Proof: the finite-type closed-point criterion makes the residue field K finite.
The image A of the specified pushout map is a finite subring of K, hence a field:
multiplication by any nonzero element is injective and therefore surjective.
The images of both actual residue embeddings lie in A. Their spectrum maps,
composed with the canonical residue-field point of X, define a point t of the
fibre product over A. The compatibility h is exactly the pullback equation.
Composing t with Spec of the inclusion A into K gives the canonical point of z,
as is checked on the two projections. In particular t has image z. The
field-valued-point correspondence supplies a map d from kappa(z) to A.
Naturality and uniqueness of that correspondence imply that inclusion after d is
the identity of K. Thus each element of K lies in A and has a pushout preimage.
The construction retains both factor maps and works for each nonsplit tensor
component; the empty case is vacuous. This is a direct universal-property proof
of the finite-field case of the residue-field assertion in Tag 01JT. -/
theorem finiteFieldBaseChangeResidue_surjective
    {k F : Type u} [Field k] [Finite k] [Field F] [Finite F]
    (i : k →+* F) {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (z : ↥(pullback f (Spec.map (CommRingCat.ofHom i))))
    (hz : z ∈ closedPoints (↥(pullback f (Spec.map (CommRingCat.ofHom i)))))
    (h : CommRingCat.ofHom (f.residueFieldAlgebraMap
        (pullback.fst f (Spec.map (CommRingCat.ofHom i)) z)) ≫
        (pullback.fst f (Spec.map (CommRingCat.ofHom i))).residueFieldMap z =
      CommRingCat.ofHom i ≫ CommRingCat.ofHom
        ((pullback.snd f (Spec.map (CommRingCat.ofHom i))).residueFieldAlgebraMap z)) :
    Function.Surjective (pushout.desc
      ((pullback.fst f (Spec.map (CommRingCat.ofHom i))).residueFieldMap z)
      (CommRingCat.ofHom
        ((pullback.snd f (Spec.map (CommRingCat.ofHom i))).residueFieldAlgebraMap z)) h).hom := by
  classical
  let g := Spec.map (CommRingCat.ofHom i)
  let Y := pullback f g
  let p : Y ⟶ X := pullback.fst f g
  let q : Y ⟶ Spec (.of F) := pullback.snd f g
  let K := Y.residueField z
  let : Algebra F K := (q.residueFieldAlgebraMap z).toAlgebra
  have : Module.Finite F K := q.finite_residueField_of_isClosed z hz
  have : Finite K := Module.finite_of_finite F
  let a := CommRingCat.ofHom (f.residueFieldAlgebraMap (p z))
  let b := CommRingCat.ofHom i
  let e := p.residueFieldMap z
  let j := CommRingCat.ofHom (q.residueFieldAlgebraMap z)
  let ψ := (pushout.desc e j h).hom
  let A := ψ.range
  let : Finite A := inferInstance
  let : Field A := (Finite.isField_of_domain A).toField
  let e' : X.residueField (p z) →+* A := e.hom.codRestrict A (fun x ↦
    ⟨(pushout.inl a b).hom x,
      congrArg (fun t ↦ t.hom x) (pushout.inl_desc e j h)⟩)
  let j' : F →+* A := j.hom.codRestrict A (fun x ↦
    ⟨(pushout.inr a b).hom x,
      congrArg (fun t ↦ t.hom x) (pushout.inr_desc e j h)⟩)
  have hc : (Spec.map (CommRingCat.ofHom e') ≫ X.fromSpecResidueField (p z)) ≫ f =
      Spec.map (CommRingCat.ofHom j') ≫ g := by
    rw [Category.assoc, ← f.specMap_residueFieldAlgebraMap, ← Spec.map_comp,
      ← Spec.map_comp]
    apply congrArg Spec.map
    ext x
    exact congrArg (fun t ↦ t.hom x) h
  let t : Spec (.of A) ⟶ Y := pullback.lift
    (Spec.map (CommRingCat.ofHom e') ≫ X.fromSpecResidueField (p z))
    (Spec.map (CommRingCat.ofHom j')) hc
  let ι : CommRingCat.of A ⟶ CommRingCat.of K := CommRingCat.ofHom A.subtype
  have hpoint : Spec.map ι ≫ t = Y.fromSpecResidueField z := by
    apply pullback.hom_ext
    · change (Spec.map ι ≫ t) ≫ p = _
      rw [Category.assoc, pullback.lift_fst, ← Category.assoc, ← Spec.map_comp]
      change Spec.map e ≫ X.fromSpecResidueField (p z) = _
      exact p.SpecMap_residueFieldMap_fromSpecResidueField z
    · change (Spec.map ι ≫ t) ≫ q = _
      rw [Category.assoc, pullback.lift_snd, ← Spec.map_comp]
      change Spec.map j = _
      exact q.specMap_residueFieldAlgebraMap z
  have hw : t (IsLocalRing.closedPoint A) = z := by
    have hh := congrArg (fun r : Spec (.of K) ⟶ Y ↦ r (IsLocalRing.closedPoint K)) hpoint
    change t (Spec.map ι (IsLocalRing.closedPoint K)) =
      Y.fromSpecResidueField z (IsLocalRing.closedPoint K) at hh
    rw [Scheme.fromSpecResidueField_apply] at hh
    exact (congrArg t (Subsingleton.elim (IsLocalRing.closedPoint A)
      (Spec.map ι (IsLocalRing.closedPoint K)))).trans hh
  let d : Y.residueField z ⟶ CommRingCat.of A :=
    (Y.residueFieldCongr hw).inv ≫ Y.descResidueField (Scheme.stalkClosedPointTo t)
  have hd : Spec.map d ≫ Y.fromSpecResidueField z = t := by
    simp only [d, Spec.map_comp, Category.assoc]
    rw [Scheme.residueFieldCongr_inv, Scheme.residueFieldCongr_fromSpecResidueField]
    exact Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField A Y t
  have hsplit : d ≫ ι = 𝟙 (CommRingCat.of K) := by
    change d ≫ ι = 𝟙 (Y.residueField z)
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_id]
    apply (cancel_mono (Y.fromSpecResidueField z)).mp
    rw [Category.assoc, hd, hpoint]
    exact (Category.id_comp _).symm
  intro x
  have hx : (d.hom x : K) = x := congrArg (fun r ↦ r.hom x) hsplit
  obtain ⟨y, hy⟩ := (d.hom x).property
  exact ⟨y, hy.trans hx⟩

end AlgebraicGeometry
