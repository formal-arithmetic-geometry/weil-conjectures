/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Data.Int.Interval
import Sheaf.Algebra.Homology.RingedSiteBoundedFreeRHomMapQuasiIso
import Sheaf.Algebra.Homology.RingedSiteBoundedFreeRHomFiniteSupport

/-!
# Bounded-above finite-projective internal Hom on a ringed site

Source: Stacks Project, Cohomology on Sites, Tag 08JI,
lemma-Rhom-complex-of-direct-summands-finite-free
(blueprint: lem-weil-pbc-ringed-site-bounded-free-rhom-model).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- A bounded-above complex of summands of finite free module sheaves computes internal
RHom into a bounded-below complex. The comparison is the localized Hom map into any
K-injective replacement. The product projections identify each term with the indicated
finite coproduct, and give the differential `d_N f - (-1)^n f d_P`.

Source: Stacks Project, Cohomology on Sites, Tag 08JI
(blueprint: lem-weil-pbc-ringed-site-bounded-free-rhom-model).

Proof:
1. Apply the finite-projective Hom comparison to obtain a quasi-isomorphism into
   every K-injective replacement. Localization sends this map to an isomorphism.
2. Choose the functorial K-injective replacement of N. The existing computation
   of derived internal Hom with a K-injective target identifies its localized Hom
   complex with RHom(QP,QN). Compose the two isomorphisms.
3. Apply the finite-support calculation. Outside a-n ≤ i ≤ b an internal Hom
   factor vanishes; the remaining finite product is the finite coproduct. Its
   projections retain the defining Hom differential and its sign. -/
theorem ringedSite_boundedFree_rhom_model
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w}
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    (P N : CochainComplex
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (a b : ℤ)
    (hP : ∀ i : ℤ, b < i → IsZero (P.X i))
    (hN : ∀ j : ℤ, j < a → IsZero (N.X j))
    (hfinite : ∀ i : ℤ, ∃ r : ℕ,
      ∃ s : P.X i ⟶ SheafOfModules.free
        (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (ULift.{u} (Fin r)),
      ∃ t : SheafOfModules.free
        (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (ULift.{u} (Fin r))
          ⟶ P.X i, s ≫ t = 𝟙 (P.X i)) :
    Nonempty (DerivedCategory.Q.obj (homComplex (R := R) P N) ≅
      (derivedInternalHom J R).obj (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj N)) ∧
    (∀ (I : CochainComplex (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
      [I.IsKInjective] (α : N ⟶ I) [QuasiIso α],
      IsIso (DerivedCategory.Q.map (((homComplexFunctor (R := R)).obj (op P)).map α))) ∧
    ∃ π : ∀ (n p q : ℤ), p + n = q →
        ((homComplex (R := R) P N).X n ⟶ SheafOfModules.homObj (R := R) (P.X p) (N.X q)),
      (∀ n : ℤ, Nonempty (IsLimit (Fan.mk ((homComplex (R := R) P N).X n)
        (fun p : ℤ ↦ π n p (p + n) rfl)))) ∧
      (∀ (n m p q q' p' : ℤ) (_hnm : n + 1 = m)
        (hpq : p + m = q) (hq' : p + n = q') (hp' : p' + n = q),
        (homComplex (R := R) P N).d n m ≫ π m p q hpq =
          π n p q' hq' ≫ SheafOfModules.homObjMap (R := R) (𝟙 (P.X p)) (N.d q' q) -
            n.negOnePow • (π n p' q hp' ≫
              SheafOfModules.homObjMap (R := R) (P.d p p') (𝟙 (N.X q)))) ∧
      (∀ n : ℤ, ∃ ι : ∀ i : ↥(Finset.Icc (a - n) b),
          SheafOfModules.homObj (R := R) (P.X i) (N.X (i + n)) ⟶ (homComplex (R := R) P N).X n,
        Nonempty (IsColimit (Cofan.mk ((homComplex (R := R) P N).X n) ι)) ∧
        ∀ (i : ↥(Finset.Icc (a - n) b)) (p : ℤ),
          ι i ≫ π n p (p + n) rfl =
            if h : (i : ℤ) = p then
              eqToHom (congrArg (fun k : ℤ ↦
                SheafOfModules.homObj (R := R) (P.X k) (N.X (k + n))) h)
            else 0) := by
  classical
  have hP' : ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero (P.X i) := ⟨b, hP⟩
  have hmap (I : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
      [I.IsKInjective] (α : N ⟶ I) [QuasiIso α] :
      IsIso (DerivedCategory.Q.map (((homComplexFunctor (R := R)).obj (op P)).map α)) := by
    have hq := ringedSite_boundedFree_rhom_map_quasiIso J R P hP' hfinite I N ⟨a, hN⟩ α
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hq
  have hfiniteSupport := ringedSite_boundedFree_rhom_finiteSupport J R P N a b hP hN
  refine ⟨?_, ?_, hfiniteSupport⟩
  · let A := SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
    let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
    let I := CochainComplex.kInjectiveResolutionFunctor.{u} A
    let η := CochainComplex.toKInjectiveResolution.{u} A
    have hα : QuasiIso (η.app N) :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app A N).2
    let eM : DerivedCategory.Q.obj (I.obj N) ≅ DerivedCategory.Q.obj N :=
      (asIso (DerivedCategory.Q.map (η.app N))).symm
    obtain ⟨e⟩ := derivedInternalHom_obj_iso J R
      (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N) P (I.obj N)
      (Iso.refl _) eM
    have hq : IsIso (DerivedCategory.Q.map
        (((homComplexFunctor (R := R)).obj (op P)).map (η.app N))) :=
      hmap (I.obj N) (η.app N)
    exact ⟨asIso (DerivedCategory.Q.map
        (((homComplexFunctor (R := R)).obj (op P)).map (η.app N))) ≪≫ e.symm⟩
  · intro I _ α _
    exact hmap I α

end CategoryTheory
