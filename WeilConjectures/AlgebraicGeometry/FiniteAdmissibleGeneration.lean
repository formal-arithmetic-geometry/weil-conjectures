/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingEtaleCompactGenerators
import WeilConjectures.AlgebraicGeometry.FiniteFieldEtaleFreeCompact
import WeilConjectures.AlgebraicGeometry.Affine.AffineEtaleFreeDetection
import WeilConjectures.CategoryTheory.CompactGeneratorsBuildObjects
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.CategoryTheory.Skeletal

/-! # Finite admissible generation helper

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
`sk-prop-ctf-finite-comparison`, statement and proof
(blueprint: new-ctf-finite-admissible-generation).

The proof uses compact affine-etale free complexes over `ULift A`. Their shifts
jointly detect objects, and the compact-generator telescope places every unbounded
object in every localizing subcategory containing these finite-Tor generators.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- Finite admissible generation helper.

Source: blueprint `sk-prop-ctf-finite-comparison`, proof steps 4--6
(blueprint: new-ctf-finite-admissible-generation).

Proof: in the algebraically closed case, use the finite-ring compact
generator family. In the finite-field case, use the affine-etale free compact
family. Transport its tests along the skeleton equivalence by explicit free-Yoneda
isomorphisms, and apply affine-etale-free detection. In either case, form the
coproduct of the detecting family and apply the compact-generator telescope
construction. Closure under shifts, triangles, and ambient coproducts puts
every telescope stage and its cone in the localizing closure; rotating the
telescope triangle then puts every unbounded object in that closure. -/
theorem finiteAdmissibleGeneration
    (k : Type u) [Field k] (hbase : Finite k ∨ IsAlgClosed k)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (algebraMap ℤ k (ℓ : ℤ)))
    (A : Type u) [CommRing A] [Finite A] (hA : ∃ n : ℕ, (ℓ : A) ^ n = 0)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))] :
    CategoryTheory.localizingClosure
        (Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1} A) X ⊓
          _root_.DerivedCategory.finiteTorAmplitude _) = ⊤ := by
  classical
  let R := ULift.{u + 1} A
  have hnil : ∃ n : ℕ, (ℓ : R) ^ n = 0 := by
    obtain ⟨n, hn⟩ := hA
    refine ⟨n, (ULift.ringEquiv : R ≃+* A).injective ?_⟩
    simpa only [map_pow, map_natCast, map_zero] using hn
  have hunit : IsUnit (ℓ : k) := by simpa only [map_natCast] using hℓ
  let Sgen := Etale.DerivedCategory.isBoundedConstructible R X ⊓
    _root_.DerivedCategory.finiteTorAmplitude _
  have hfamily : ∃ hc : HasCoproducts.{u + 1} (Etale.DerivedCategoryModule R X),
      LocallySmall.{u + 1} (Etale.DerivedCategoryModule R X) ∧
      ∃ (S : Type (u + 1)) (E : S → Etale.DerivedCategoryModule R X),
        (∀ s, Sgen (E s)) ∧
        (∀ s, @IsCompactObject (Etale.DerivedCategoryModule R X) _ _ hc (E s)) ∧
        ∀ (M N : Etale.DerivedCategoryModule R X) (f : M ⟶ N),
          (∀ s (n : ℤ), Function.Bijective (fun (a : (E s)⟦n⟧ ⟶ M) ↦ a ≫ f)) →
            IsIso f := by
    rcases hbase with hfin | hclosed
    · let := hfin
      have hchar : ℓ ≠ ringChar k := by
        intro h
        exact ((isUnit_iff_not_dvd_char k ℓ).mp hunit) (h ▸ dvd_refl ℓ)
      let B := Skeleton X.AffineEtale
      let e := skeletonEquivalence X.AffineEtale
      obtain ⟨hc, hsmall, hf⟩ := Etale.finiteField_affineEtaleFree_compact
        ℓ Fact.out hchar hnil (X ↘ Spec (.of k)) B e (skeleton_skeletal _)
      let := hc
      refine ⟨hc, hsmall, B, fun U ↦ Etale.affineEtaleFreeComplex R X (e.functor.obj U),
        ?_, ?_, ?_⟩
      · intro U
        exact ⟨(hf U).2.2.1, 0, 0,
          Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp (hf U).2.2.2.1⟩
      · intro U
        exact (hf U).2.2.2.2.1
      · intro M N f hh
        apply Etale.isIso_of_affineEtaleFreeComplex R X f
        intro U n
        let i := (Scheme.AffineEtale.Spec X).mapIso (e.counitIso.app U)
        let ipre : Presheaf.freeYoneda ((Scheme.AffineEtale.Spec X).obj
              (e.functor.obj (e.inverse.obj U))) (ModuleCat.of R R) ≅
            Presheaf.freeYoneda ((Scheme.AffineEtale.Spec X).obj U) (ModuleCat.of R R) :=
          { hom :=
              { app V := Sigma.map' (fun t ↦ t ≫ i.hom) (fun _ ↦ 𝟙 _)
                naturality V W g := by
                  apply Sigma.hom_ext
                  intro t
                  simp [Presheaf.freeYoneda, Category.assoc] }
            inv :=
              { app V := Sigma.map' (fun t ↦ t ≫ i.inv) (fun _ ↦ 𝟙 _)
                naturality V W g := by
                  apply Sigma.hom_ext
                  intro t
                  simp [Presheaf.freeYoneda, Category.assoc] }
            hom_inv_id := by
              apply NatTrans.ext
              funext V
              apply Sigma.hom_ext
              intro t
              simp [Presheaf.freeYoneda, Category.assoc]
            inv_hom_id := by
              apply NatTrans.ext
              funext V
              apply Sigma.hom_ext
              intro t
              simp [Presheaf.freeYoneda, Category.assoc] }
        let ish := (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).mapIso ipre
        let ic : (Etale.affineEtaleFreeComplex R X
              (e.functor.obj (e.inverse.obj U)))⟦n⟧ ≅
            (Etale.affineEtaleFreeComplex R X U)⟦n⟧ :=
          (shiftFunctor (Etale.DerivedCategoryModule R X) n).mapIso
          ((_root_.DerivedCategory.singleFunctor _ 0).mapIso ish)
        constructor
        · intro a b hab
          apply (cancel_epi ic.hom).mp
          apply (hh (e.inverse.obj U) n).injective
          simpa only [Category.assoc] using congrArg (fun z ↦ ic.hom ≫ z) hab
        · intro a
          obtain ⟨b, hb⟩ := (hh (e.inverse.obj U) n).surjective (ic.hom ≫ a)
          refine ⟨ic.inv ≫ b, ?_⟩
          change (ic.inv ≫ b) ≫ f = a
          change b ≫ f = ic.hom ≫ a at hb
          rw [Category.assoc, hb, Iso.inv_hom_id_assoc]
    · let := hclosed
      obtain ⟨hc, hsmall, hcompact, S, E, hE, hdetect⟩ :=
        Etale.finiteRing_compactGenerators ℓ Fact.out hunit (X ↘ Spec (.of k)) hnil
      let := hc
      exact ⟨hc, hsmall, S, E, (fun s ↦ by
        obtain ⟨hbc, a, b, _, ht⟩ := hE s
        exact ⟨hbc, a, b, Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp ht⟩),
        (fun s ↦ hcompact _ (hE s)), hdetect⟩
  obtain ⟨hc, hsmall, S, E, hE, hcompact, hdetect⟩ := hfamily
  let := hc
  let := hsmall
  let : Zero (Etale.DerivedCategoryModule R X) := HasZeroObject.zero' _
  have hgenerate : IsTriangulatedGeneratingFamily E := by
    intro K hK
    by_contra! hn
    have hzero (s : S) (n : ℤ) (f : E s ⟶ K⟦n⟧) : f = 0 := by
      have h := congrArg (fun g ↦ Sigma.ι E s ≫ g)
        (hn n (Sigma.desc (Pi.single s f)))
      simpa using h
    have hshift (s : S) (n : ℤ) (f : (E s)⟦n⟧ ⟶ K) : f = 0 := by
      let e := (shiftEquiv (Etale.DerivedCategoryModule R X) n).toAdjunction.homEquiv (E s) K
      apply e.injective
      rw [hzero s (-n) (e f)]
      simp [e, Adjunction.homEquiv_apply]
    have : IsIso (0 : (0 : Etale.DerivedCategoryModule R X) ⟶ K) := by
      apply hdetect
      intro s n
      constructor
      · intro f g _
        exact (isZero_zero _).eq_of_tgt f g
      · intro f
        refine ⟨0, ?_⟩
        simp only [zero_comp, hshift s n f]
    exact hK ((isZero_zero _).of_iso
      (asIso (0 : (0 : Etale.DerivedCategoryModule R X) ⟶ K)).symm)
  apply top_unique
  intro K _ P hP hcontains
  let := hP.1
  let := hP.2.1
  have hsumsBig (I : Type (u + 2)) : P.IsClosedUnderColimitsOfShape (Discrete I) := by
    constructor
    rintro L ⟨hL⟩
    let : HasColimit hL.diag := ⟨_, hL.isColimit⟩
    exact P.prop_of_iso ((colimit.isColimit hL.diag).coconePointUniqueUpToIso hL.isColimit)
      (hP.2.2 hL.diag inferInstance (fun i ↦ hL.prop_diag_obj (Discrete.mk i)))
  have hsums (I : Type (u + 1)) : P.IsClosedUnderColimitsOfShape (Discrete I) :=
    (P.isClosedUnderColimitsOfShape_iff_of_equivalence
      (Discrete.equivalence (Equiv.ulift : ULift.{u + 2} I ≃ I))).1 (hsumsBig _)
  have hsum {I : Type (u + 1)} (F : I → Etale.DerivedCategoryModule R X)
      (hF : ∀ i, P (F i)) : P (∐ F) := by
    let := hsums I
    exact P.prop_colimit (Discrete.functor F) (fun i ↦ hF i.as)
  have hshift (s : S) (n : ℤ) : P ((E s)⟦n⟧) :=
    P.le_shift n _ (hcontains _ (hE s))
  obtain ⟨Y, t, hstart, hsteps, q, r, htel⟩ :=
    compactGenerators_buildObjects.{u + 1, u + 1} E hcompact hgenerate K
  have hshape (Z : Etale.DerivedCategoryModule R X)
      (hZ : ∃ (J : Type (u + 1)) (i : J → S) (m : J → ℤ),
        Nonempty (Z ≅ ∐ fun j : J ↦ (E (i j))⟦m j⟧)) : P Z := by
    obtain ⟨J, i, m, ⟨e⟩⟩ := hZ
    exact P.prop_of_iso e.symm (hsum _ (fun j ↦ hshift (i j) (m j)))
  obtain ⟨Z, a, b, hZ, hdist⟩ := hsteps
  have hY (n : ℕ) : P (Y n) := by
    induction n with
    | zero => exact hshape _ hstart
    | succ n ih =>
      exact P.ext_of_isTriangulatedClosed₃ _ (hdist n) (hshape _ (hZ n)) ih
  have hPsum := hsum (fun n : ULift.{u + 1} ℕ ↦ Y n.down) (fun n ↦ hY n.down)
  exact P.ext_of_isTriangulatedClosed₃ _ htel hPsum hPsum

end AlgebraicGeometry.ProEtale
