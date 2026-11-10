/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Residue comparison for affine product models over a stalk

Source: Stacks Project, Tag 0307; residue comparison in step 3 of
lem-sbc-cartier-generic-stalk-galois-model-core. -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem residueMap_bijective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [SurjectiveOnStalks f] (x : X) : Function.Bijective (f.residueFieldMap x) := by
  refine ⟨(f.residueFieldMap x).hom.injective, ?_⟩
  intro z
  obtain ⟨w, rfl⟩ := IsLocalRing.residue_surjective (R := X.presheaf.stalk x) z
  obtain ⟨v, rfl⟩ := f.stalkMap_surjective x w
  exact ⟨IsLocalRing.residue _ v, rfl⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem spec_residue_naturality (R S : CommRingCat.{u}) (alg : Algebra R S)
    (q : Spec S) :
    letI := alg
    let p : Spec R := ⟨q.asIdeal.under R, inferInstance⟩
    letI := Localization.AtPrime.algebraOfLiesOver p.asIdeal q.asIdeal
    (Spec.map (CommRingCat.ofHom (algebraMap R S))).residueFieldMap q ≫
      (Spec.residueFieldIso S q).hom =
      (Spec.residueFieldIso R p).hom ≫ CommRingCat.ofHom
        (algebraMap p.asIdeal.ResidueField q.asIdeal.ResidueField) := by
  let := alg
  let := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
  dsimp only
  apply (cancel_epi (Spec.residueFieldIso R
    (⟨q.asIdeal.under R, inferInstance⟩ : Spec R)).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  apply CommRingCat.hom_ext
  apply Ideal.ResidueField.ringHom_ext
  ext r
  change ((CommRingCat.ofHom (algebraMap R _) ≫
    (Spec.residueFieldIso R _).inv ≫ _ ≫ (Spec.residueFieldIso S q).hom) r) = _
  rw [Spec.algebraMap_residueFieldIso_inv_assoc]
  change (((ΓSpecIso R).inv ≫ (Spec R).Γevaluation _ ≫ _ ≫
    (Spec.residueFieldIso S q).hom) r) = _
  erw [Γevaluation_naturality_assoc, ← ΓSpecIso_inv_naturality_assoc]
  change ((CommRingCat.ofHom (algebraMap R S) ≫ (ΓSpecIso S).inv ≫
    (Spec S).presheaf.germ ⊤ q trivial ≫ (Spec S).residue q ≫
    (Spec.residueFieldIso S q).hom) r) = _
  rw [← Spec.algebraMap_residueFieldIso_inv_assoc, Iso.inv_hom_id, Category.comp_id]
  change algebraMap S q.asIdeal.ResidueField (algebraMap R S r) = _
  exact (IsScalarTower.algebraMap_apply R S q.asIdeal.ResidueField r).symm.trans
    (IsScalarTower.algebraMap_apply R (q.asIdeal.under R).ResidueField
      q.asIdeal.ResidueField r)


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A product presentation over the actual base stalk identifies residue extensions.

Source: Stacks Project, Tag 0307, and the residue comparison in step 3 of
lem-sbc-cartier-generic-stalk-galois-model-core.
(blueprint: lem-sbc-stalk-product-residue-comparison)

Proof: Lift x to the stalk base change using the closed point of Spec O_{N,s}
and the existence of pullback points. The stalk morphism is a preimmersion, as
is its base change. A morphism surjective on stalks induces a surjective map of
residue fields; as a map of fields it is injective, hence an isomorphism. The supplied isomorphism
takes this lifted point into
one of the disjoint affine components Spec S_i, giving its index i and prime q.
The equation over Spec O_{N,s} identifies the contraction of q with the base
closed point. The residue fields of affine scheme points are the fraction fields
of their prime quotients. These identifications give e and f. Prove naturality of the affine
residue-field isomorphisms by precomposing with the base ring: evaluation
naturality and the Gamma-Spec isomorphism give the equality on each ring element.
The ideal residue-field universal property extends it to the field. Combine
this naturality with residueFieldMap_comp and the supplied structural-map
equality to prove the square. If the index type is empty then no x
can lie over s, so that case is vacuous. No arbitrary domain algebra is used: the
specified scheme isomorphism is essential. -/
theorem stalk_product_residue_comparison
    {N X : Scheme.{u}} (f : X ⟶ N) (s : N)
    (I : Type) (S : I → CommRingCat.{u})
    (alg : ∀ i, Algebra (N.presheaf.stalk s) (S i)) :
    letI := alg
    ∀ (c : pullback f (N.fromSpecStalk s) ≅ ∐ fun i : I ↦ Spec (S i)),
      c.hom ≫ Sigma.desc (fun i : I ↦
        Spec.map (CommRingCat.ofHom (algebraMap (N.presheaf.stalk s) (S i)))) =
          pullback.snd f (N.fromSpecStalk s) →
      ∀ (x : X), f x = s →
        ∃ (i : I) (q : Ideal (S i)) (hq : q.IsPrime),
          letI := hq
          letI := Localization.AtPrime.algebraOfLiesOver
            (q.under (N.presheaf.stalk s)) q
          letI := (f.residueFieldMap x).hom.toAlgebra
          ∃ (e : N.residueField (f x) ≃+*
              (q.under (N.presheaf.stalk s)).ResidueField)
            (g : X.residueField x ≃+* q.ResidueField),
            (algebraMap (q.under (N.presheaf.stalk s)).ResidueField
              q.ResidueField).comp e.toRingHom =
              g.toRingHom.comp (algebraMap (N.residueField (f x))
                (X.residueField x)) := by
  let := alg
  intro c hc x hx
  let R := N.presheaf.stalk s
  let a := N.fromSpecStalk s
  obtain ⟨z, hzx, hzy⟩ := Pullback.exists_preimage_pullback (f := f) (g := a) x
    (IsLocalRing.closedPoint R) (hx.trans fromSpecStalk_closedPoint.symm)
  obtain ⟨i, y, hy⟩ := (sigmaOpenCover (fun i : I ↦ Spec (S i))).exists_eq (c.hom z)
  change Sigma.ι (fun i : I ↦ Spec (S i)) i y = c.hom z at hy
  have hcy : c.inv (Sigma.ι (fun i : I ↦ Spec (S i)) i y) = z := by
    rw [hy]
    rw [← Hom.comp_apply, Iso.hom_inv_id]
    rfl
  let d := Sigma.ι (fun i : I ↦ Spec (S i)) i ≫ c.inv ≫ pullback.fst f a
  let b := Spec.map (CommRingCat.ofHom (algebraMap R (S i)))
  have hdxy : d y = x := by
    change pullback.fst f a (c.inv (Sigma.ι (fun i : I ↦ Spec (S i)) i y)) = x
    rw [hcy, hzx]
  have hd : d ≫ f = b ≫ a := by
    dsimp only [d]
    rw [Category.assoc, Category.assoc, pullback.condition]
    erw [← hc]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Sigma.ι_comp_desc_assoc]
    rfl
  rcases hdxy with rfl
  have hk : f (d y) = a (b y) := by
    rw [← Hom.comp_apply, hd, Hom.comp_apply]
    rfl
  let q := y.asIdeal
  let : q.IsPrime := y.isPrime
  let := Localization.AtPrime.algebraOfLiesOver (q.under R) q
  let ei : N.residueField (f (d y)) ≅ CommRingCat.of (q.under R).ResidueField :=
    N.residueFieldCongr hk ≪≫
      (RingEquiv.ofBijective (a.residueFieldMap (b y)).hom
        (residueMap_bijective a (b y))).toCommRingCatIso ≪≫
      Spec.residueFieldIso R (b y)
  let fi : X.residueField (d y) ≅ CommRingCat.of q.ResidueField :=
    (RingEquiv.ofBijective (d.residueFieldMap y).hom
      (residueMap_bijective d y)).toCommRingCatIso ≪≫ Spec.residueFieldIso (S i) y
  have hsquare : ei.hom ≫ CommRingCat.ofHom
      (algebraMap (q.under R).ResidueField q.ResidueField) =
      f.residueFieldMap (d y) ≫ fi.hom := by
    dsimp only [ei, fi, Iso.trans_hom]
    simp only [Category.assoc]
    change (N.residueFieldCongr hk).hom ≫ a.residueFieldMap (b y) ≫
      (Spec.residueFieldIso R (b y)).hom ≫ _ =
        f.residueFieldMap (d y) ≫ d.residueFieldMap y ≫
          (Spec.residueFieldIso (S i) y).hom
    erw [← spec_residue_naturality R (S i) (alg i) y]
    have he := Hom.residueFieldMap_congr hd y
    simp only [residueFieldMap_comp] at he
    convert! congrArg (fun m ↦ m ≫ (Spec.residueFieldIso (S i) y).hom) he.symm using 1
  refine ⟨i, q, inferInstance, ei.commRingCatIsoToRingEquiv,
    fi.commRingCatIsoToRingEquiv, ?_⟩
  exact congrArg CommRingCat.Hom.hom hsquare


end AlgebraicGeometry.Scheme
