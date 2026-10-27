/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q103
-/
module

public import WeilConjectures.RingTheory.PairHenselization
public import Sheaf.RingTheory.IndEtaleUniverseTransport
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.Algebra.Field.Equiv

/-! # The pair-colimit at a prime as an ind-etale henselian local model

Source: Stacks Project, More on Algebra, Tags 0A02 and 0A03; Algebra, Tag 00CR;
Pro-etale Cohomology, Tag 097K
(blueprint: lem-trf-prime-pair-colimit-ind-etale-model).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace RingTheory

private theorem across_of_indEtale {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (h : f.IndEtale) : f.IndEtaleAcrossUniverses := by
  have hi : RingHom.RespectsIso (@RingHom.IndEtale.{u}) :=
    RingHom.IndEtale.isStableUnderBaseChange.localizationPreserves.away.respectsIso
  exact hi.1 _ (ULift.ringEquiv.symm : B ≃+* ULift.{u} B)
    (hi.2 _ (ULift.ringEquiv : ULift.{u} A ≃+* A) h)

private theorem local_of_henselian_pair
    {R C : Type u} [CommRing R] [IsLocalRing R] [CommRing C] (f : R →+* C)
    (h : HenselianRing C ((IsLocalRing.maximalIdeal R).map f))
    (hq : Function.Bijective (Ideal.quotientMap
      ((IsLocalRing.maximalIdeal R).map f) f Ideal.le_comap_map)) :
    ∃ hC : HenselianLocalRing C,
      @IsLocalRing.maximalIdeal C _ hC.toIsLocalRing = (IsLocalRing.maximalIdeal R).map f := by
  classical
  let J := (IsLocalRing.maximalIdeal R).map f
  let q := Ideal.quotientMap J f Ideal.le_comap_map
  let e := RingEquiv.ofBijective q hq
  let : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _
  have hfield : IsField (C ⧸ J) := e.symm.toMulEquiv.isField (Field.toIsField _)
  have hJ : J.IsMaximal := Ideal.Quotient.maximal_of_isField J hfield
  let : J.IsMaximal := hJ
  let : Field (C ⧸ J) := Ideal.Quotient.field J
  let : IsLocalHom (Ideal.Quotient.mk J) := isLocalHom_of_le_jacobson_bot J h.jac
  let : IsLocalRing C := (Ideal.Quotient.mk J).domain_isLocalRing
  have hm : IsLocalRing.maximalIdeal C = J := (IsLocalRing.eq_maximalIdeal hJ).symm
  have hC : HenselianLocalRing C :=
    { is_henselian := by
        intro g hg a ha hu
        rw [hm] at ha ⊢
        exact h.is_henselian g hg a ha (hu.map (Ideal.Quotient.mk J)) }
  exact ⟨hC, hm⟩

private theorem quotient_bijective_of_equiv
    {R D C : Type u} [CommRing R] [CommRing D] [CommRing C]
    (m : Ideal R) (f : R →+* D) (g : R →+* C) (E : D ≃+* C)
    (ht : E.toRingHom.comp f = g)
    (hq : Function.Bijective (Ideal.quotientMap (m.map f) f Ideal.le_comap_map)) :
    Function.Bijective (Ideal.quotientMap (m.map g) g Ideal.le_comap_map) := by
  let e := Ideal.quotientEquiv (m.map f) (m.map g) E
    (by
      change m.map g = (m.map f).map E.toRingHom
      rw [Ideal.map_map, ht])
  have heq : Ideal.quotientMap (m.map g) g Ideal.le_comap_map =
      e.toRingHom.comp (Ideal.quotientMap (m.map f) f Ideal.le_comap_map) := by
    ext x
    change Ideal.Quotient.mk _ (g x) = Ideal.Quotient.mk _ (E (f x))
    exact congrArg (Ideal.Quotient.mk _) (DFunLike.congr_fun ht x).symm
  rw [heq]
  exact e.bijective.comp hq

set_option maxHeartbeats 1200000 in
-- Comparing colimits in the full neighborhood category elaborates large dependent types.
/-- The given ring-colimit of a small skeleton of the pair neighborhoods of `Aₚ` is
also an algebra-colimit, henselian local with unchanged residue field, and ind-etale
over both `Aₚ` and `A`.

Source: Stacks Project, More on Algebra, Tags 0A02 and 0A03; Algebra, Tag 00CR;
Pro-etale Cohomology, Tag 097K
(blueprint: lem-trf-prime-pair-colimit-ind-etale-model).

The under category records precisely the algebra structure and all algebra maps.
The cocone `c` supplies the specified structural map and coprojections; only its
underlying ring-colimit property is assumed. Its algebra-colimit property is concluded
for this same cocone. The quotient map is the structural map, not a chosen isomorphism.

Proof (the five steps of the node):
1. Apply lem-weil-pbc-pair-henselization to the maximal-ideal pair of `Aₚ`.
   Transport filteredness to the small skeleton through its equivalence. For an
   algebra cocone, the ring-colimit descent preserves the base map: check this at
   the representative of the identity algebra. Ring uniqueness then gives algebra
   uniqueness. Extend skeleton cocones by representative isomorphisms, identifying
   this cocone with the pair-colimit over `Aₚ`. Transfer the henselian-pair and
   structural quotient-isomorphism conclusions to its vertex.
2. The affine-etale bridge lem-weil-pbc-etale-ring-map-iff-etale-affine makes every
   stage finitely presented. This filtered algebra presentation proves ind-etaleness
   of the structural map, by def-weil-pbc-ind-etale-algebra.
3. Put `J = mC`. If a maximal ideal `q` does not contain `J`, the finite cyclic
   algebra `C/q` has zero quotient modulo `J`. Its distinct idempotents zero and one
   then lift the same idempotent, contradicting henselianness. Hence `J` lies in every
   maximal ideal. The quotient is the field `k`, so `C` is local with maximal ideal
   `J` and is henselian local. Injectivity of the structural quotient map shows that
   the inverse image of `J` is `m`, so the structural map is local.
4. Apply lem-weil-pbc-localization-colimit-principal-localizations to `A` and the
   complement of `p`. Principal localizations are etale by
   lem-weil-pbc-principal-localization-open-immersion and
   lem-weil-pbc-etale-composition-cancellation, and finitely presented by the affine
   bridge. Check the algebra universal property at the stage indexed by one. This
   proves ind-etaleness of the specified localization map `A → Aₚ`.
5. Apply the composition clause of lem-weil-pbc-ind-etale-stability to the two
   specified maps. No Noetherian hypothesis is used. -/
theorem prime_pair_colimit_indEtale_model
    (A : Type u) [CommRing A] (p : Ideal A) [p.IsPrime]
    (I : Type u) [SmallCategory I] (_hI : Skeletal I)
    (e : I ≌ ObjectProperty.FullSubcategory
      (fun B : Under (CommRingCat.of (Localization.AtPrime p)) ↦
        AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map B.hom) ∧
          Function.Bijective (Ideal.quotientMap
            ((IsLocalRing.maximalIdeal (Localization.AtPrime p)).map B.hom.hom)
            B.hom.hom Ideal.le_comap_map)))
    (c : Cocone (e.functor ⋙ ObjectProperty.ι _))
    (_hc : IsColimit ((Under.forget (CommRingCat.of (Localization.AtPrime p))).mapCocone c)) :
    IsFiltered I ∧
      (∀ i : I, (e.functor.obj i).obj.hom.hom.FinitePresentation) ∧
      Nonempty (IsColimit c) ∧
      (∃ hC : HenselianLocalRing c.pt.right,
        @IsLocalRing.maximalIdeal c.pt.right _ hC.toIsLocalRing =
          (IsLocalRing.maximalIdeal (Localization.AtPrime p)).map c.pt.hom.hom) ∧
      IsLocalHom c.pt.hom.hom ∧
      Function.Bijective (Ideal.quotientMap
        ((IsLocalRing.maximalIdeal (Localization.AtPrime p)).map c.pt.hom.hom)
        c.pt.hom.hom Ideal.le_comap_map) ∧
      RingHom.IndEtaleAcrossUniverses (algebraMap A (Localization.AtPrime p)) ∧
      RingHom.IndEtaleAcrossUniverses c.pt.hom.hom ∧
      RingHom.IndEtaleAcrossUniverses
        (c.pt.hom.hom.comp (algebraMap A (Localization.AtPrime p))) := by
  classical
  let R := Localization.AtPrime p
  let m := IsLocalRing.maximalIdeal R
  obtain ⟨_, hf, d, ⟨hd⟩, hdh, hdq⟩ := pair_henselization R m
  let := hf
  let : IsFiltered I := IsFiltered.of_equivalence e.symm
  let : IsConnected I := IsFiltered.isConnected I
  have hc : IsColimit c := isColimitOfReflects (Under.forget _) _hc
  let t := (hd.whiskerEquivalence e).coconePointUniqueUpToIso hc
  let E : d.pt.right ≃+* c.pt.right := CategoryTheory.Iso.commRingCatIsoToRingEquiv
    ((Under.forget _).mapIso t)
  have ht : E.toRingHom.comp d.pt.hom.hom = c.pt.hom.hom :=
    congrArg CommRingCat.Hom.hom (Under.w t.hom)
  obtain ⟨hD, hmD⟩ := local_of_henselian_pair (R := R) d.pt.hom.hom hdh hdq
  let := hD
  let : HenselianLocalRing c.pt.right := HenselianLocalRing.of_ringEquiv E
  have hmC : IsLocalRing.maximalIdeal c.pt.right = m.map c.pt.hom.hom := by
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal E, hmD]
    change (m.map d.pt.hom.hom).map E.toRingHom = m.map c.pt.hom.hom
    rw [Ideal.map_map, ht]
  have hq := quotient_bijective_of_equiv m d.pt.hom.hom c.pt.hom.hom E ht hdq
  have hlocal : IsLocalHom c.pt.hom.hom :=
    ((IsLocalRing.local_hom_TFAE c.pt.hom.hom).out 2 0).mp (by rw [hmC])
  have het (i : I) : (e.functor.obj i).obj.hom.hom.Etale :=
    (AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)
      (φ := (e.functor.obj i).obj.hom)).mp (e.functor.obj i).property.1
  have hindR : (algebraMap A R).IndEtale := by
    apply (RingHom.IndEtale.algebraMap_iff A R).mpr
    infer_instance
  have hindC : c.pt.hom.hom.IndEtale := by
    apply (RingHom.IndEtale.iff_exists c.pt.hom).mpr
    refine ⟨I, inferInstance, inferInstance, _, ?_, _, _hc, ?_⟩
    · exact
        { app i := (e.functor.obj i).obj.hom
          naturality i j f := by
            simp [Under.w] }
    · intro i
      exact ⟨het i, Under.w (c.ι.app i)⟩
  exact ⟨inferInstance, fun i ↦ (het i).2, ⟨hc⟩, ⟨inferInstance, hmC⟩,
    hlocal, hq, across_of_indEtale _ hindR, across_of_indEtale _ hindC,
    across_of_indEtale _ (hindC.comp hindR)⟩

end RingTheory
