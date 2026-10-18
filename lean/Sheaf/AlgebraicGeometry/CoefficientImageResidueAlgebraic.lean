/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Algebraic residues of coefficient-enlarged images of étale algebras

Source: Stacks Project, Tag 0F0X, second paragraph, with the compatible models of Tag 0F0U
(blueprint: lem-kun-coefficient-image-residue-algebraic).
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem image_residue_algebraic
    (R : Type u) [CommRing R] [IsDomain R]
    (L : Type u) [Field L] [Algebra R L] [Algebra (FractionRing R) L]
    [IsScalarTower R (FractionRing R) L] [Algebra.IsAlgebraic (FractionRing R) L]
    (E B : CommRingCat.{u}) (r : R →+* E) (b : E →+* B) (h : L →+* B)
    (hcomp : b.comp r = h.comp (algebraMap R L)) :
    letI : Algebra L B := h.toAlgebra
    let S := Algebra.adjoin L (Set.range b)
    let β : E →+* S := b.codRestrict S (fun x ↦ Algebra.subset_adjoin ⟨x, rfl⟩)
    ∀ (q : Ideal S) (hq : q.IsPrime),
      letI : q.IsPrime := hq
      @Algebra.IsAlgebraic (Ideal.comap β q).ResidueField q.ResidueField _ _
        (Ideal.ResidueField.map _ _ β rfl).toAlgebra := by
  classical
  let : Algebra L B := h.toAlgebra
  let S := Algebra.adjoin L (Set.range b)
  let β : E →+* S := b.codRestrict S (fun x ↦ Algebra.subset_adjoin ⟨x, rfl⟩)
  dsimp only
  intro q hq
  let : q.IsPrime := hq
  let w : Ideal E := Ideal.comap β q
  let δ : w.ResidueField →+* q.ResidueField := Ideal.ResidueField.map w q β rfl
  let : Algebra w.ResidueField q.ResidueField := δ.toAlgebra
  let σ : L →+* q.ResidueField := (algebraMap S q.ResidueField).comp (algebraMap L S)
  let ρ : R →+* w.ResidueField := (algebraMap E w.ResidueField).comp r
  have hcomm : δ.comp ρ = σ.comp (algebraMap R L) := by
    ext x
    change δ (algebraMap E w.ResidueField (r x)) =
      algebraMap S q.ResidueField (algebraMap L S (algebraMap R L x))
    rw [Ideal.ResidueField.map_algebraMap]
    congr 1
    apply Subtype.ext
    exact DFunLike.congr_fun hcomp x
  have hρ : Function.Injective ρ := by
    apply Function.Injective.of_comp (f := δ)
    change Function.Injective (δ.comp ρ)
    rw [hcomm]
    have hi : Function.Injective (algebraMap R L) := by
      rw [IsScalarTower.algebraMap_eq R (FractionRing R) L]
      exact (algebraMap (FractionRing R) L).injective.comp
        (IsFractionRing.injective R (FractionRing R))
    exact σ.injective.comp hi
  let φ : FractionRing R →+* w.ResidueField := IsFractionRing.lift hρ
  have hφ : δ.comp φ = σ.comp (algebraMap (FractionRing R) L) := by
    apply IsFractionRing.ringHom_ext (A := R)
    intro x
    simp only [RingHom.comp_apply, φ, IsFractionRing.lift_algebraMap]
    rw [← IsScalarTower.algebraMap_apply R (FractionRing R) L]
    exact DFunLike.congr_fun hcomm x
  have hσ (x : L) : IsAlgebraic w.ResidueField (σ x) :=
    (Algebra.IsAlgebraic.isAlgebraic (R := FractionRing R) x).ringHom_of_comp_eq
      φ σ φ.injective hφ
  let T := integralClosure w.ResidueField q.ResidueField
  have hv (x : S) : algebraMap S q.ResidueField x ∈ T := by
    obtain ⟨x, hx⟩ := x
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨e, rfl⟩ := hx
      change _root_.IsIntegral w.ResidueField (algebraMap S q.ResidueField (β e))
      rw [← Ideal.ResidueField.map_algebraMap w q β rfl]
      exact isIntegral_algebraMap (x := algebraMap E w.ResidueField e)
    | algebraMap x => exact (hσ x).isIntegral
    | add x y hx hy ihx ihy =>
      change (algebraMap S q.ResidueField ((⟨x, hx⟩ : S) + ⟨y, hy⟩)) ∈ T
      rw [map_add]
      exact T.add_mem ihx ihy
    | mul x y hx hy ihx ihy =>
      change (algebraMap S q.ResidueField ((⟨x, hx⟩ : S) * ⟨y, hy⟩)) ∈ T
      rw [map_mul]
      exact T.mul_mem ihx ihy
  change @Algebra.IsAlgebraic w.ResidueField q.ResidueField _ _ δ.toAlgebra
  refine ⟨fun z ↦ ?_⟩
  obtain ⟨x, y, hy, hz⟩ := IsFractionRing.div_surjective (S ⧸ q) z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hx : _root_.IsIntegral w.ResidueField (algebraMap S q.ResidueField x) := hv x
  have hy : _root_.IsIntegral w.ResidueField (algebraMap S q.ResidueField y) := hv y
  rw [← hz, Ideal.algebraMap_quotient_residueField_mk,
    Ideal.algebraMap_quotient_residueField_mk]
  simpa only [div_eq_mul_inv] using (hx.mul hy.inv).isAlgebraic

set_option backward.isDefEq.respectTransparency.types false in
private theorem algebraic_residue_spec {A C : CommRingCat.{u}} (f : A ⟶ C)
    (x : Spec C)
    (halg : @Algebra.IsAlgebraic ((Spec.map f) x).asIdeal.ResidueField
      x.asIdeal.ResidueField _ _ (Ideal.ResidueField.map _ _ f.hom rfl).toAlgebra) :
    @Algebra.IsAlgebraic ((Spec A).residueField ((Spec.map f) x))
      ((Spec C).residueField x) _ _ ((Spec.map f).residueFieldMap x).hom.toAlgebra := by
  have hsq : (Spec.map f).residueFieldMap x ≫ (Spec.residueFieldIso C x).hom =
      (Spec.residueFieldIso A ((Spec.map f) x)).hom ≫
        CommRingCat.ofHom (Ideal.ResidueField.map _ x.asIdeal f.hom rfl) := by
    rw [← cancel_epi ((Spec A).residue _), residue_residueFieldMap_assoc,
      Spec.residue_residueFieldIso_hom, Spec.residue_residueFieldIso_hom_assoc,
      ← localRingHom_comp_stalkIso]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    congr 1
  let : Algebra ((Spec.map f) x).asIdeal.ResidueField x.asIdeal.ResidueField :=
    (Ideal.ResidueField.map _ _ f.hom rfl).toAlgebra
  let : Algebra.IsAlgebraic ((Spec.map f) x).asIdeal.ResidueField
      x.asIdeal.ResidueField := halg
  let : Algebra ((Spec A).residueField ((Spec.map f) x)) ((Spec C).residueField x) :=
    ((Spec.map f).residueFieldMap x).hom.toAlgebra
  apply Algebra.IsAlgebraic.of_ringHom_of_comp_eq
    (Spec.residueFieldIso A ((Spec.map f) x)).hom.hom
    (Spec.residueFieldIso C x).hom.hom
    (Spec.residueFieldIso A ((Spec.map f) x)).commRingCatIsoToRingEquiv.surjective
    (Spec.residueFieldIso C x).commRingCatIsoToRingEquiv.injective
  exact (congrArg CommRingCat.Hom.hom hsq).symm

set_option backward.isDefEq.respectTransparency.types false in
private theorem algebraic_residue_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    (hf : @Algebra.IsAlgebraic (Y.residueField (f x)) (X.residueField x)
      _ _ (f.residueFieldMap x).hom.toAlgebra)
    (hg : @Algebra.IsAlgebraic (Z.residueField (g (f x))) (Y.residueField (f x))
      _ _ (g.residueFieldMap (f x)).hom.toAlgebra) :
    @Algebra.IsAlgebraic (Z.residueField ((f ≫ g) x)) (X.residueField x)
      _ _ ((f ≫ g).residueFieldMap x).hom.toAlgebra := by
  let : Algebra (Z.residueField (g (f x))) (Y.residueField (f x)) :=
    (g.residueFieldMap (f x)).hom.toAlgebra
  let : Algebra (Y.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  let : Algebra (Z.residueField (g (f x))) (X.residueField x) :=
    ((f ≫ g).residueFieldMap x).hom.toAlgebra
  let : IsScalarTower (Z.residueField (g (f x))) (Y.residueField (f x))
      (X.residueField x) := IsScalarTower.of_algebraMap_eq' (by
    exact congrArg CommRingCat.Hom.hom (residueFieldMap_comp f g x))
  let : Algebra.IsAlgebraic (Z.residueField (g (f x))) (Y.residueField (f x)) := hg
  let : Algebra.IsAlgebraic (Y.residueField (f x)) (X.residueField x) := hf
  change Algebra.IsAlgebraic (Z.residueField (g (f x))) (X.residueField x)
  exact Algebra.IsAlgebraic.trans _ (Y.residueField (f x)) _

/-- Adjoining a coefficient field algebraic over the generic field of a shared domain
preserves algebraicity of all residue extensions of an étale stage.

Source: Stacks Project, Tag 0F0X, second paragraph, and Tag 0F0U, compatible-model footnote
(blueprint: lem-kun-coefficient-image-residue-algebraic).

Proof: write `S` for the image algebra and fix a prime `q` of `S`. Contract it to the
étale stage `E`, obtaining `w`, and then to the affine base, obtaining `p`. Étaleness
makes the extension at `w/p` finite separable. The map from the field `L` to the residue
field at `q` is injective, so every nonzero element of `R` has nonzero image at `w`.
Consequently the shared map from `R` extends uniquely to an embedding of its fraction
field in the residue field at `w`. Each element of `L` is algebraic over that fraction
field, hence its image is algebraic over the residue field at `w`. The residue field at
`q` is generated as a field by the images of `E` and `L`, since `S` is their generated
ring. Every rational expression uses finitely many algebraic elements; their finite
simple adjunctions form a finite-dimensional extension. Thus the extension at `q/w` is
algebraic. Transitivity with the finite extension at `w/p` proves the claim. Passing
between the affine scheme and its spectrum preserves these residue maps.
-/
theorem coefficientImage_residue_algebraic
    (R : Type u) [CommRing R] [IsDomain R]
    (L : Type u) [Field L] [Algebra R L] [Algebra (FractionRing R) L]
    [IsScalarTower R (FractionRing R) L] [Algebra.IsAlgebraic (FractionRing R) L]
    (X : Scheme.{u}) [IsAffine X] (E B : CommRingCat.{u})
    (a : Γ(X, ⊤) ⟶ E) (ha : Etale (Spec.map a))
    (r : CommRingCat.of R ⟶ Γ(X, ⊤)) (b : E ⟶ B) (h : L →+* B)
    (hcomp : r ≫ a ≫ b =
      CommRingCat.ofHom (algebraMap R L) ≫ CommRingCat.ofHom h) :
    letI : Algebra L B := h.toAlgebra
    let S := Algebra.adjoin L (Set.range b.hom)
    let g := Spec.map (CommRingCat.ofHom ((b.hom.comp a.hom).codRestrict S
      (fun x ↦ Algebra.subset_adjoin ⟨a.hom x, rfl⟩))) ≫ X.isoSpec.inv
    ∀ v : Spec (.of S),
      @Algebra.IsAlgebraic (X.residueField (g v)) ((Spec (.of S)).residueField v)
        _ _ ((g.residueFieldMap v).hom.toAlgebra) := by
  classical
  let : Algebra L B := h.toAlgebra
  let S := Algebra.adjoin L (Set.range b.hom)
  let β : E ⟶ CommRingCat.of S := CommRingCat.ofHom
    (b.hom.codRestrict S (fun x ↦ Algebra.subset_adjoin ⟨x, rfl⟩))
  let f := Spec.map β
  let g := Spec.map a ≫ X.isoSpec.inv
  dsimp only
  intro v
  have hr : b.hom.comp (a.hom.comp r.hom) = h.comp (algebraMap R L) :=
    congrArg CommRingCat.Hom.hom hcomp
  have hf := algebraic_residue_spec β v
    (image_residue_algebraic R L E B (a.hom.comp r.hom) b.hom h hr
      v.asIdeal v.isPrime)
  let : Etale (Spec.map a) := ha
  have hg : @Algebra.IsAlgebraic (X.residueField (g (f v)))
      ((Spec E).residueField (f v)) _ _ (g.residueFieldMap (f v)).hom.toAlgebra := by
    let : Algebra (X.residueField (g (f v))) ((Spec E).residueField (f v)) :=
      (g.residueFieldMap (f v)).hom.toAlgebra
    exact inferInstance
  have hh := algebraic_residue_comp f g v hf hg
  have heq : f ≫ g = Spec.map (CommRingCat.ofHom
      ((b.hom.comp a.hom).codRestrict S
        (fun x ↦ Algebra.subset_adjoin ⟨a.hom x, rfl⟩))) ≫ X.isoSpec.inv := by
    dsimp [f, g]
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
  rw [heq] at hh
  exact hh

end AlgebraicGeometry.Scheme
