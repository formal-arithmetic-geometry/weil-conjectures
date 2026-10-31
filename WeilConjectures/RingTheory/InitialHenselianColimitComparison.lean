/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.IndEtaleUniverseTransport
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import WeilConjectures.RingTheory.MapIntoHenselianColimit

/-!
# Initial henselian local algebras and colimit presentations

Source: Stacks Project, Algebra, Tag 08HR, and Categories, Tag 002F
(blueprint: lem-trf-initial-henselian-colimit-comparison).

The comparison uses only the initial local-map property of `H`. The conclusion
transports the entire specified cocone, with its legs postcomposed by `f`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace Algebra

private theorem across_iff {A B : Type u} [CommRing A] [CommRing B]
    (a : A →+* B) : a.IndEtaleAcrossUniverses ↔ a.IndEtale := by
  have hi : RingHom.RespectsIso (@RingHom.IndEtale.{u}) :=
    RingHom.IndEtale.isStableUnderBaseChange.localizationPreserves.away.respectsIso
  constructor
  · intro h
    exact hi.2 _ (ULift.ringEquiv.symm : A ≃+* ULift.{u} A)
      (hi.1 _ (ULift.ringEquiv : ULift.{u} B ≃+* B) h)
  · intro h
    exact hi.1 _ (ULift.ringEquiv.symm : B ≃+* ULift.{u} B)
      (hi.2 _ (ULift.ringEquiv : ULift.{u} A ≃+* A) h)

private theorem initial_of_indEtale
    (R C T : Type u) [CommRing R] [IsLocalRing R]
    [CommRing C] [IsLocalRing C] [Algebra R C]
    [CommRing T] [HenselianLocalRing T] [Algebra R T]
    [IsLocalHom (algebraMap R C)] [IsLocalHom (algebraMap R T)]
    (hind : Algebra.IndEtale R C)
    (hres : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap R C))) :
    ∃! f : C →ₐ[R] T, IsLocalHom f.toRingHom := by
  classical
  let p := IsLocalRing.maximalIdeal R
  let q := IsLocalRing.maximalIdeal C
  let m := IsLocalRing.maximalIdeal T
  have hp : p = q.comap (algebraMap R C) :=
    (IsLocalRing.maximalIdeal_comap _).symm
  have hm : p = m.comap (algebraMap R T) :=
    (IsLocalRing.maximalIdeal_comap _).symm
  let eR : IsLocalRing.ResidueField R ≃+* p.ResidueField :=
    RingEquiv.ofBijective (algebraMap _ _) p.bijective_algebraMap_quotient_residueField
  let eC : IsLocalRing.ResidueField C ≃+* q.ResidueField :=
    RingEquiv.ofBijective (algebraMap _ _) q.bijective_algebraMap_quotient_residueField
  let s := Ideal.ResidueField.map p q (algebraMap R C) hp
  let t := Ideal.ResidueField.map p m (algebraMap R T) hm
  have hs (x : IsLocalRing.ResidueField R) :
      s (eR x) = eC (IsLocalRing.ResidueField.map (algebraMap R C) x) := by
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
    exact Ideal.ResidueField.map_algebraMap p q (algebraMap R C) hp r
  have hbij : Function.Bijective s := by
    refine ⟨RingHom.injective s, ?_⟩
    intro y
    obtain ⟨c, rfl⟩ := eC.surjective y
    obtain ⟨r, rfl⟩ := hres.surjective c
    exact ⟨eR r, hs r⟩
  let e := RingEquiv.ofBijective s hbij
  let τ := t.comp e.symm.toRingHom
  have hτ : τ.comp s = t := by
    apply RingHom.ext
    intro x
    exact congrArg t (e.symm_apply_apply x)
  let : Algebra.IndEtale R C := hind
  obtain ⟨I, _, _, pres, het⟩ :=
    Algebra.IndEtale.exists_colimitPresentation (R := R) (S := C)
  let : HasColimit pres.diag := pres.hasColimit
  have hpres : Nonempty (colimit pres.diag ≅ CommAlgCat.of R C) :=
    ⟨(colimit.isColimit pres.diag).coconePointUniqueUpToIso pres.isColimit⟩
  obtain ⟨f, ⟨hf, hfred⟩, huniq⟩ :=
    map_into_henselian_colimit R T C I pres.diag hpres het q p hp hm τ hτ
  have islocal (g : C →ₐ[R] T) (hg : q = m.comap g.toRingHom) :
      IsLocalHom g.toRingHom :=
    ((IsLocalRing.local_hom_TFAE g.toRingHom).out 4 0).mp hg.symm
  refine ⟨f, islocal f hf, ?_⟩
  intro g hg
  have hq : q = m.comap g.toRingHom :=
    (IsLocalRing.maximalIdeal_comap g.toRingHom).symm
  apply huniq g
  refine ⟨hq, ?_⟩
  apply RingHom.ext
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  change Ideal.ResidueField.map q m g.toRingHom hq (s x) = t (e.symm (e x))
  rw [e.symm_apply_apply]
  have hc : (Ideal.ResidueField.map q m g.toRingHom hq).comp s = t := by
    apply Ideal.ResidueField.ringHom_ext
    ext r
    simp only [RingHom.comp_apply, s, t, Ideal.ResidueField.map_algebraMap]
    exact congrArg (algebraMap T m.ResidueField) (g.commutes r)
  exact DFunLike.congr_fun hc x

private theorem algColimitOfRing
    {P : Type u} [CommRing P] {I : Type u} [SmallCategory I] [IsFiltered I]
    {D : I ⥤ CommAlgCat.{u} P} (c : Cocone D)
    (hc : IsColimit ((forget₂ (CommAlgCat.{u} P) CommRingCat.{u}).mapCocone c)) :
    Nonempty (IsColimit c) := by
  classical
  let U := forget₂ (CommAlgCat.{u} P) CommRingCat.{u}
  let i : I := IsFiltered.nonempty.some
  have commutes (s : Cocone D) (r : P) :
      (hc.desc (U.mapCocone s)).hom (algebraMap P c.pt r) = algebraMap P s.pt r := by
    have hι : (c.ι.app i).hom (algebraMap P (D.obj i) r) = algebraMap P c.pt r :=
      (c.ι.app i).hom.commutes r
    exact (congrArg (hc.desc (U.mapCocone s)).hom hι).symm.trans
      ((ConcreteCategory.congr_hom (hc.fac (U.mapCocone s) i)
        (algebraMap P (D.obj i) r)).trans ((s.ι.app i).hom.commutes r))
  refine ⟨
    { desc := fun s ↦ CommAlgCat.ofHom
        { __ := (hc.desc (U.mapCocone s)).hom
          commutes' := commutes s }
      fac := ?_
      uniq := ?_ }⟩
  · intro s j
    apply CommAlgCat.hom_ext
    apply AlgHom.coe_ringHom_injective
    exact congrArg CommRingCat.Hom.hom (hc.fac (U.mapCocone s) j)
  · intro s m hm
    apply CommAlgCat.hom_ext
    apply AlgHom.coe_ringHom_injective
    exact congrArg CommRingCat.Hom.hom
      (hc.uniq (U.mapCocone s) (U.map m) (fun j ↦ congrArg U.map (hm j)))

/-- An initial henselian local algebra agrees with a henselian ind-etale local
algebra having the base residue field, and inherits every specified presentation.

Source: Stacks Project, Algebra, Tag 08HR (lemma-map-into-henselian-colimit),
Categories, Tag 002F (definition-colimit), and Pro-etale, Tag 097I
(blueprint: lem-trf-initial-henselian-colimit-comparison).

Proof:
1. For any henselian local `T` with local map `a : R → T`, form the residue map
   `tau = e_T e_C⁻¹`. Apply `lem-weil-pbc-map-into-henselian-colimit` to the
   ind-etale presentation of `C`, at its maximal ideal. Locality identifies its
   inverse image with the maximal ideal of `R`. The lemma gives a unique local
   `R`-map inducing `tau`. Every local `R`-map induces this same residue map,
   because `e_C` is bijective. Hence `C` is initial among henselian local algebras.
2. Apply this to `T = H` to obtain `f`, and the assumed property of `H` to `C`
   to obtain `g`. Local maps compose. Uniqueness for `C` proves `g f = id`, and
   uniqueness for `H` proves `f g = id`. The same uniqueness proves uniqueness
   of each local algebra map separately.
3. Postcompose each leg `lambda_i` by `f`. For any compatible ring cocone
   `t_i : D_i → B`, its unique mediator `v : C → B` gives `v g : H → B`.
   The two inverse identities prove its factorization and uniqueness. Thus
   the transported cocone is a colimit in rings, by Tag 002F.
4. For a `P`-algebra cocone, choose an index, which exists by filteredness.
   The equation on that leg forces the ring mediator to preserve the specified
   `P`-structure. This gives the algebra-colimit property for the same cocone.
   Scalar towers express exactly the composites `P → R → C` and `P → R → H`.
5. If every stage is etale and finitely presented over `P`, this very filtered
   colimit cocone is an ind-etale presentation of the specified map `P → H`,
   by `def-weil-pbc-ind-etale-algebra` and Tag 097I.
-/
theorem initial_henselian_colimit_comparison
    (R C H : Type u) [CommRing R] [IsLocalRing R]
    [CommRing C] [HenselianLocalRing C] [Algebra R C]
    [CommRing H] [HenselianLocalRing H] [Algebra R H]
    [IsLocalHom (algebraMap R C)] [IsLocalHom (algebraMap R H)]
    (hC : RingHom.IndEtaleAcrossUniverses (algebraMap R C))
    (hres : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap R C)))
    (hH : ∀ (T : Type u) [CommRing T] [HenselianLocalRing T]
      (a : R →+* T), IsLocalHom a →
      ∃! b : H →+* T, IsLocalHom b ∧ b.comp (algebraMap R H) = a) :
    ∃ (f : C →ₐ[R] H) (g : H →ₐ[R] C),
      IsLocalHom f.toRingHom ∧ IsLocalHom g.toRingHom ∧
      (∀ f' : C →ₐ[R] H, IsLocalHom f'.toRingHom → f' = f) ∧
      (∀ g' : H →ₐ[R] C, IsLocalHom g'.toRingHom → g' = g) ∧
      g.comp f = AlgHom.id R C ∧ f.comp g = AlgHom.id R H ∧
      ∀ (P : Type u) [CommRing P] [Algebra P R] [Algebra P C] [Algebra P H]
        [IsScalarTower P R C] [IsScalarTower P R H]
        (I : Type u) [SmallCategory I] [IsFiltered I]
        (D : I ⥤ CommAlgCat.{u} P)
        (legs : D ⟶ (Functor.const I).obj (CommAlgCat.of P C)),
        IsColimit ((forget₂ (CommAlgCat.{u} P) CommRingCat.{u}).mapCocone
          (Cocone.mk (CommAlgCat.of P C) legs)) →
        Nonempty (IsColimit ((forget₂ (CommAlgCat.{u} P) CommRingCat.{u}).mapCocone
          ((Cocone.mk (CommAlgCat.of P C) legs).extend
            (CommAlgCat.ofHom (f.restrictScalars P))))) ∧
        Nonempty (IsColimit ((Cocone.mk (CommAlgCat.of P C) legs).extend
          (CommAlgCat.ofHom (f.restrictScalars P)))) ∧
        ((∀ i : I, Algebra.Etale P (D.obj i) ∧ Algebra.FinitePresentation P (D.obj i)) →
          RingHom.IndEtaleAcrossUniverses (algebraMap P H)) := by
  classical
  have hind : Algebra.IndEtale R C :=
    (RingHom.IndEtale.algebraMap_iff R C).mp ((across_iff _).mp hC)
  obtain ⟨f, hf, hfu⟩ := initial_of_indEtale R C H hind hres
  have : IsLocalHom f.toRingHom := hf
  obtain ⟨g₀, ⟨hg₀, hgR⟩, hgu⟩ := hH C (algebraMap R C) inferInstance
  let g : H →ₐ[R] C :=
    { __ := g₀
      commutes' := fun r ↦ DFunLike.congr_fun hgR r }
  have hg : IsLocalHom g.toRingHom := hg₀
  have hgu' (g' : H →ₐ[R] C) (hg' : IsLocalHom g'.toRingHom) : g' = g := by
    apply AlgHom.coe_ringHom_injective
    exact hgu g'.toRingHom ⟨hg', RingHom.ext g'.commutes⟩
  have hgf : g.comp f = AlgHom.id R C := by
    obtain ⟨_, _, hu⟩ := initial_of_indEtale R C C hind hres
    exact (hu (g.comp f) (RingHom.isLocalHom_comp g.toRingHom f.toRingHom)).trans
      (hu (AlgHom.id R C) (isLocalHom_id C)).symm
  have hfg : f.comp g = AlgHom.id R H := by
    obtain ⟨_, _, hu⟩ := hH H (algebraMap R H) inferInstance
    apply AlgHom.coe_ringHom_injective
    exact (hu (f.comp g).toRingHom ⟨RingHom.isLocalHom_comp f.toRingHom g.toRingHom,
      RingHom.ext (f.comp g).commutes⟩).trans
      (hu (RingHom.id H) ⟨inferInstance, rfl⟩).symm
  refine ⟨f, g, hf, hg, hfu, hgu', hgf, hfg, ?_⟩
  intro P _ _ _ _ _ _ I _ _ D legs hc
  let e : CommAlgCat.of P C ≅ CommAlgCat.of P H :=
    CommAlgCat.isoMk ((AlgEquiv.ofAlgHom f g hfg hgf).restrictScalars P)
  let U := forget₂ (CommAlgCat.{u} P) CommRingCat.{u}
  let c := (Cocone.mk (CommAlgCat.of P C) legs).extend e.hom
  have hr : IsColimit (U.mapCocone c) :=
    hc.ofIsoColimit (Cocone.ext (U.mapIso e) (fun _ ↦ rfl))
  have ha : IsColimit c := (algColimitOfRing c hr).some
  refine ⟨⟨hr⟩, ⟨ha⟩, ?_⟩
  intro het
  apply (across_iff _).mpr
  apply (RingHom.IndEtale.algebraMap_iff P H).mpr
  exact ⟨⟨I, inferInstance, inferInstance, ⟨D, c.ι, ha⟩, fun i ↦ (het i).1⟩⟩

end Algebra
