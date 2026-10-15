/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.Algebra.Homology.DerivedInternalHom
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Data.Int.Interval
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.CategoryTheory.DoubleComplexTotal
import Sheaf.Algebra.Homology.FirstQuadrantTotalComparison
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMap
import Sheaf.Algebra.Homology.HomComplex
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom

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
1. Module sheaves are Grothendieck (`prop-pur-kinjective-resolutions-exist`), hence have
   enough injectives (`lem-sp-grothendieck-enough-injectives`). The bounded-below injective
   representative (`lem-weil-pbc-dplus-injective-representative`) and the localization
   bijection (`lem-weil-pbc-kinjective-hom-derived`) give a bounded-below K-injective
   replacement map from N.
2. Internal Hom from a finite free sheaf is a finite power of the target. Thus it
   preserves quasi-isomorphisms; splitting the idempotent proves the same for a summand.
3. Form the first-quadrant double complex Hom(P^(b-u), N^(a+v)), and similarly for the
   replacement. Translate degrees by c = a-b. Multiplication on each summand by
   (-1)^(uv+u(u-1)/2+u(c+1)) identifies its total differential with the Hom differential.
4. The map of columns is a quasi-isomorphism by step 2. First-quadrant total comparison
   (`lem-sc-first-quadrant-total-column-comparison`) makes the Hom map a quasi-isomorphism.
5. Internal Hom into a K-injective computes derived internal Hom. Comparisons of
   replacements lift uniquely up to homotopy by `lem-weil-pbc-kinjective-hom-derived`;
   Hom preserves target homotopies and `lem-pur-rhom-well-defined` gives independence.
6. All product factors outside a-n ≤ i ≤ b vanish. Removing them leaves a finite
   product, canonically the finite coproduct, including the empty interval. The original
   Hom differential retains exactly its sign. -/
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
  sorry

end CategoryTheory
