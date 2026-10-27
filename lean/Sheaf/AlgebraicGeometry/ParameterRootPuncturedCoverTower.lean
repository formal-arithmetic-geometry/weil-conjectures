/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Sheaf.Paper.StrictLocalKummerTameModule
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.RingTheory.ParameterRootColimit
import Sheaf.RingTheory.ParameterRootLocalization
import Sheaf.RingTheory.PresentedRingColimit
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.Algebra.CharP.Invertible
import Sheaf.AlgebraicGeometry.EtaleComparison

/-! # Punctured simultaneous parameter-root towers

Source: Stacks 00UB, 00UC, 090N, 03PL, 01YW; ILO IX Proposition 2.1, p.133;
Bhatt--Scholze Definitions 4.1.1 and 4.2.1.
(blueprint: lem-sfb-parameter-root-punctured-cover-tower).

The finite root quotients are written directly using the polynomial and quotient APIs.
The full quotient is the existing compatible-root construction.
All existential maps below are specified on coefficients and root generators, or on
localization maps; thus the statement specifies the canonical maps uniquely.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
namespace ParameterRootTower

/-- The finite root quotient with the original parameter product inverted.
Source: ILO IX 2.1, punctured root presentation
(blueprint: lem-sfb-parameter-root-punctured-cover-tower). -/
abbrev puncturedLevel {H : Type u} [CommRing H] {r : ℕ} (t : Fin r → H) (n : ℕ) :=
  Localization.Away (algebraMap H
    (MvPolynomial (Fin r) H ⧸ Ideal.span
      (Set.range (fun i : Fin r ↦ MvPolynomial.X i ^ n - MvPolynomial.C (t i)))) (∏ i, t i))

/-- The actual full compatible-root quotient with the same denominator inverted.
Source: Stacks 090N and the compatible-root presentation in direct-images paragraph (3)
(blueprint: lem-sfb-parameter-root-punctured-cover-tower). -/
abbrev puncturedFull (p : ℕ) {H : Type u} [CommRing H] {r : ℕ} (t : Fin r → H) :=
  Localization.Away (algebraMap H (ProEtale.tameRootAlgebra p t) (∏ i, t i))

/-- The localized finite structural map, obtained by the localization universal property.
Source: Stacks 00CO and ILO IX 2.1
(blueprint: lem-sfb-parameter-root-punctured-cover-tower). -/
def levelMap {H : Type u} [CommRing H] {r : ℕ} (t : Fin r → H) (n : ℕ) :
    Localization.Away (∏ i, t i) →+* puncturedLevel t n :=
  IsLocalization.Away.map _ _ (algebraMap H
    (MvPolynomial (Fin r) H ⧸ Ideal.span
      (Set.range (fun i : Fin r ↦ MvPolynomial.X i ^ n - MvPolynomial.C (t i))))) (∏ i, t i)

/-- The localized full structural map uses the real compatible-root quotient.
Source: Stacks 00CO, 090N and Bhatt--Scholze 4.1.1
(blueprint: lem-sfb-parameter-root-punctured-cover-tower). -/
def fullMap (p : ℕ) {H : Type u} [CommRing H] {r : ℕ} (t : Fin r → H) :
    Localization.Away (∏ i, t i) →+* puncturedFull p t :=
  IsLocalization.Away.map _ _ (algebraMap H (ProEtale.tameRootAlgebra p t)) (∏ i, t i)

end ParameterRootTower
open ProEtale ParameterRootTower

/-- The prime-to-p parameter-root tower has the specified power transitions, bounded
monomial bases, finite etale faithfully flat punctured maps, and a pro-etale limit cover.
Source: Stacks 00UB, 00UC, 090N, 03PL, 01YW; ILO IX 2.1; Bhatt--Scholze 4.1.1, 4.2.1
(blueprint: lem-sfb-parameter-root-punctured-cover-tower).

Proof (the eleven steps of the DAG):
1. The divisibility index is nonempty (order one) and directed (use the product).
   If m=nq, then n and q are positive and prime to p. Bezout makes each a unit
   in every characteristic-p coefficient ring, including all its localizations.
2. Polynomial evaluation and quotient descent give the transition x_n -> x_m^q.
   Adjoining qth roots of x_n gives the mth-root quotient: the mutually inverse
   maps fix coefficients and send the new variables to x_m. Check relations and
   compositions on generators. Exponent multiplication proves the functor laws.
3. Apply lem-weil-pbc-monic-quotient-free successively to the variables. Nested
   unique expansions give the basis indexed by Fin r -> Fin n, and for a
   transition by Fin r -> Fin (m/n). Their cardinalities are n^r and (m/n)^r.
4. Localize these presentations at the original product. The inverse comparison
   maps fix coefficients, roots and the inverse denominator. Each parameter is
   a unit, with inverse the product of the other parameters divided by f;
   x_n has inverse x_n^(n-1)/t. The same bases work after localization.
5. A finite nonempty basis identifies tensoring with a finite product of copies
   of the module, naturally in module maps. Exactness is preserved coordinatewise
   and reflected using one coordinate. This is faithful flatness by
   def-weil-pbc-faithfully-flat-ring-map, also for the empty parameter tuple.
6. Apply lem-sfb-unit-binomial-finite-etale successively using the units of
   steps 1 and 4, and lem-weil-pbc-etale-covering-composition. Finiteness follows
   from the displayed finite bases and def-weil-finite-integral-morphism.
7. Faithful flatness also gives surjectivity on spectra by
   lem-weil-pbc-faithfully-flat-surjective-spectrum.
8. The full compatible-root presentation has exactly the colimit universal
   property. Localization commutes with it: the inverse denominator comes from
   level one; the two induced maps fix coefficients, roots and this inverse.
   This gives the localized colimit universal property with its exact inclusions.
9. Apply lem-weil-pbc-directed-colimit-faithfully-flat-algebras (090N) to the fixed
   localized base, then surjectivity on spectra. By
   lem-weil-pbc-spec-small-colimit-limit, the same spectrum cone is a limit in
   schemes, expressed below by its unique factorization against every test scheme.
10. The finite levels are finitely presented etale algebras. Thus their filtered
    colimit is ind-etale, hence weakly etale by det-pe-morphisms-etale-comparison.
    Affine inverse images and surjectivity supply the fpqc covering condition of
    def-weil-pbc-proetale-covering, not merely a pro-etale object.
11. No step uses Noetherianity or nontriviality. For r=0 all algebras are H and
    f=1; for n=1 evaluation gives H. Equal-order transitions fix every generator.
    Nilpotent f gives zero localizations and empty spectra, permitted coverings.
-/
theorem parameterRoot_punctured_cover_tower (p : ℕ) (hp : p.Prime)
    (H : Type u) [CommRing H] [CharP H p] (r : ℕ) (t : Fin r → H) :
    ∃ (transition : ∀ (n m : TameRootOrder p), n.val ∣ m.val →
        (MvPolynomial (Fin r) H ⧸ Ideal.span
          (Set.range (fun i : Fin r ↦ MvPolynomial.X i ^ n.val - MvPolynomial.C (t i)))) →ₐ[H]
        (MvPolynomial (Fin r) H ⧸ Ideal.span
          (Set.range (fun i : Fin r ↦ MvPolynomial.X i ^ m.val - MvPolynomial.C (t i)))))
      (inclusion : ∀ n : TameRootOrder p,
        (MvPolynomial (Fin r) H ⧸ Ideal.span
          (Set.range (fun i : Fin r ↦ MvPolynomial.X i ^ n.val - MvPolynomial.C (t i)))) →ₐ[H]
        tameRootAlgebra p t)
      (localizedTransition : ∀ (n m : TameRootOrder p), n.val ∣ m.val →
        puncturedLevel t n.val →+* puncturedLevel t m.val)
      (localizedInclusion : ∀ n : TameRootOrder p,
        puncturedLevel t n.val →+* puncturedFull p t),
    (∀ (n m : TameRootOrder p) (h : n.val ∣ m.val) (i : Fin r),
      transition n m h (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
        Ideal.Quotient.mk _ (MvPolynomial.X i) ^ (m.val / n.val)) ∧
    (∀ n, transition n n (dvd_refl n.val) = AlgHom.id H _) ∧
    (∀ (n m l : TameRootOrder p) (h : n.val ∣ m.val) (h' : m.val ∣ l.val),
      (transition m l h').comp (transition n m h) = transition n l (h.trans h')) ∧
    (∀ n : TameRootOrder p,
      ∃ b : Module.Basis (Fin r → Fin n.val) H
          ((MvPolynomial (Fin r) H ⧸ Ideal.span
          (Set.range (fun i : Fin r ↦ MvPolynomial.X i ^ n.val - MvPolynomial.C (t i))))),
        ∀ e, b e = ∏ i, Ideal.Quotient.mk _ (MvPolynomial.X i) ^ (e i).val) ∧
    (∀ (n m : TameRootOrder p) (h : n.val ∣ m.val),
      (∃ e : (MvPolynomial (Fin r) ((MvPolynomial (Fin r) H ⧸ Ideal.span
          (Set.range (fun i : Fin r ↦ MvPolynomial.X i ^ n.val - MvPolynomial.C (t i))))) ⧸
          Ideal.span
          (Set.range (fun i : Fin r ↦ MvPolynomial.X i ^ (m.val / n.val) -
            MvPolynomial.C (Ideal.Quotient.mk _ (MvPolynomial.X i))))) ≃+*
            (MvPolynomial (Fin r) H ⧸ Ideal.span
          (Set.range (fun i : Fin r ↦ MvPolynomial.X i ^ m.val - MvPolynomial.C (t i)))),
        (∀ a : (MvPolynomial (Fin r) H ⧸ Ideal.span
          (Set.range (fun i : Fin r ↦ MvPolynomial.X i ^ n.val - MvPolynomial.C (t i)))),
          e (algebraMap _ _ a) =
          transition n m h a) ∧
        ∀ i : Fin r, e (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
          Ideal.Quotient.mk _ (MvPolynomial.X i)) ∧
      (∃ b : @Module.Basis (Fin r → Fin (m.val / n.val))
          ((MvPolynomial (Fin r) H ⧸ Ideal.span
          (Set.range (fun i : Fin r ↦ MvPolynomial.X i ^ n.val - MvPolynomial.C (t i)))))
          ((MvPolynomial (Fin r) H ⧸ Ideal.span
          (Set.range (fun i : Fin r ↦ MvPolynomial.X i ^ m.val - MvPolynomial.C (t i)))))
          _ _ (@Algebra.toModule _ _ _ _ (transition n m h).toRingHom.toAlgebra),
        ∀ e, b e = ∏ i, Ideal.Quotient.mk _ (MvPolynomial.X i) ^ (e i).val)) ∧
    (∀ (n : TameRootOrder p) (i : Fin r),
      inclusion n (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
        Ideal.Quotient.mk _ (MvPolynomial.X (i, n))) ∧
    (∀ (n m : TameRootOrder p) (h : n.val ∣ m.val),
      (inclusion m).comp (transition n m h) = inclusion n) ∧
    (∀ (Q : Type u) [CommRing Q]
        (a : ∀ n : TameRootOrder p, (MvPolynomial (Fin r) H ⧸ Ideal.span
          (Set.range (fun i : Fin r ↦ MvPolynomial.X i ^ n.val - MvPolynomial.C (t i)))) →+* Q),
      (∀ (n m : TameRootOrder p) (h : n.val ∣ m.val),
        (a m).comp (transition n m h).toRingHom = a n) →
      ∃! g : tameRootAlgebra p t →+* Q,
        ∀ n, g.comp (inclusion n).toRingHom = a n) ∧
    (∀ (n m : TameRootOrder p) (h : n.val ∣ m.val)
        (a : (MvPolynomial (Fin r) H ⧸ Ideal.span
          (Set.range (fun i : Fin r ↦ MvPolynomial.X i ^ n.val - MvPolynomial.C (t i))))),
      localizedTransition n m h (algebraMap _ _ a) =
        algebraMap _ _ (transition n m h a)) ∧
    (∀ n : TameRootOrder p, RingHom.FaithfullyFlat (levelMap t n.val) ∧
      IsFinite (Spec.map (CommRingCat.ofHom (levelMap t n.val))) ∧
      Etale (Spec.map (CommRingCat.ofHom (levelMap t n.val))) ∧
      Surjective (Spec.map (CommRingCat.ofHom (levelMap t n.val)))) ∧
    (∀ (n m : TameRootOrder p) (h : n.val ∣ m.val),
      RingHom.FaithfullyFlat (localizedTransition n m h) ∧
      IsFinite (Spec.map (CommRingCat.ofHom (localizedTransition n m h))) ∧
      Etale (Spec.map (CommRingCat.ofHom (localizedTransition n m h))) ∧
      Surjective (Spec.map (CommRingCat.ofHom (localizedTransition n m h)))) ∧
    (∀ (n : TameRootOrder p) (a : (MvPolynomial (Fin r) H ⧸ Ideal.span
          (Set.range (fun i : Fin r ↦ MvPolynomial.X i ^ n.val - MvPolynomial.C (t i))))),
      localizedInclusion n (algebraMap _ _ a) = algebraMap _ _ (inclusion n a)) ∧
    (∀ (n m : TameRootOrder p) (h : n.val ∣ m.val),
      (localizedInclusion m).comp (localizedTransition n m h) = localizedInclusion n) ∧
    (∀ n, (localizedInclusion n).comp (levelMap t n.val) = fullMap p t) ∧
    (∀ (Q : Type u) [CommRing Q]
        (a : ∀ n : TameRootOrder p, puncturedLevel t n.val →+* Q),
      (∀ (n m : TameRootOrder p) (h : n.val ∣ m.val),
        (a m).comp (localizedTransition n m h) = a n) →
      ∃! g : puncturedFull p t →+* Q, ∀ n, g.comp (localizedInclusion n) = a n) ∧
    (∀ (Z : Scheme.{u})
        (a : ∀ n : TameRootOrder p, Z ⟶ Spec (.of (puncturedLevel t n.val))),
      (∀ (n m : TameRootOrder p) (h : n.val ∣ m.val),
        a m ≫ Spec.map (CommRingCat.ofHom (localizedTransition n m h)) = a n) →
      ∃! g : Z ⟶ Spec (.of (puncturedFull p t)),
        ∀ n, g ≫ Spec.map (CommRingCat.ofHom (localizedInclusion n)) = a n) ∧
    RingHom.FaithfullyFlat (fullMap p t) ∧
    Surjective (Spec.map (CommRingCat.ofHom (fullMap p t))) ∧
    Presieve.singleton (Spec.map (CommRingCat.ofHom (fullMap p t))) ∈
      Scheme.proetalePrecoverage (Spec (.of (Localization.Away (∏ i, t i)))) ∧
    Function.Bijective (algebraMap H
          ((MvPolynomial (Fin r) H ⧸ Ideal.span
          (Set.range (fun i : Fin r ↦ MvPolynomial.X i ^ 1 - MvPolynomial.C (t i)))))) ∧
    (r = 0 → (∀ n : TameRootOrder p,
      Function.Bijective (algebraMap H
          ((MvPolynomial (Fin r) H ⧸ Ideal.span
          (Set.range (fun i : Fin r ↦ MvPolynomial.X i ^ n.val - MvPolynomial.C (t i))))))) ∧
      Function.Bijective (algebraMap H (tameRootAlgebra p t))) := by
  let tr := fun (n m : TameRootOrder p) (h : n.val ∣ m.val) ↦
    Algebra.ParameterRoot.transition t n.val m.val h
  let inc := Algebra.ParameterRoot.inclusion t p
  let s := ∏ i, t i
  let lt := fun (n m : TameRootOrder p) (h : n.val ∣ m.val) ↦
    Algebra.LocalizationColimit.map s (tr n m h)
  let li := fun n ↦ Algebra.LocalizationColimit.map s (inc n)
  have hli (n m : TameRootOrder p) (h : n.val ∣ m.val) :
      (li m).comp (lt n m h) = li n := by
    rw [Algebra.LocalizationColimit.map_comp, Algebra.ParameterRoot.inclusion_comp]
  have hbase (n : TameRootOrder p) : (li n).comp (levelMap t n.val) = fullMap p t :=
    Algebra.LocalizationColimit.map_base s (inc n)
  have hlcol (Q : Type u) [CommRing Q] (a : ∀ n : TameRootOrder p,
      puncturedLevel t n.val →+* Q)
      (ha : ∀ n m (h : n.val ∣ m.val), (a m).comp (lt n m h) = a n) :
      ∃! g : puncturedFull p t →+* Q, ∀ n, g.comp (li n) = a n := by
    exact Algebra.LocalizationColimit.existsUnique_lift
      (⟨1, Nat.zero_lt_one, Nat.coprime_one_left p⟩ : TameRootOrder p)
      (fun n ↦ Algebra.ParameterRoot.Ring t n.val) (tameRootAlgebra p t)
      (fun n m ↦ n.val ∣ m.val) tr inc
      (fun _ _ a ha ↦ Algebra.ParameterRoot.full_isColimit t p a ha) s Q a ha
  have hunit (n : TameRootOrder p) : IsUnit (n.val : H) := by
    have hcop := hp.coprime_iff_not_dvd.mp n.property.2.symm
    let := invertibleOfCoprime (R := H) (hp.coprime_iff_not_dvd.mpr hcop).symm
    exact isUnit_of_invertible _
  have hlevel (n : TameRootOrder p) :
      (levelMap t n.val).FaithfullyFlat ∧ (levelMap t n.val).Finite ∧
      (levelMap t n.val).Etale := by
    obtain ⟨hfin, hff⟩ := Algebra.ParameterRoot.localized_finite_faithfullyFlat
      t n.val s n.property.1
    exact ⟨hff, hfin, Algebra.ParameterRoot.punctured_etale t n.val n.property.1 (hunit n)⟩
  have hgeometry {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
      (hff : f.FaithfullyFlat) (hfin : f.Finite) (he : f.Etale) :
      f.FaithfullyFlat ∧ IsFinite (Spec.map (CommRingCat.ofHom f)) ∧
      Etale (Spec.map (CommRingCat.ofHom f)) ∧
      Surjective (Spec.map (CommRingCat.ofHom f)) := by
    exact ⟨hff, (IsFinite.SpecMap_iff (CommRingCat.ofHom f)).mpr hfin,
      (HasRingHomProperty.Spec_iff (P := @Etale)).mpr he,
      (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom f)).mpr hff |>.2⟩
  let I := ULift.{u} (Algebra.ParameterRoot.DirectedIndex p)
  let idx : TameRootOrder p → I := fun n ↦ ⟨⟨n⟩⟩
  let ord : I → TameRootOrder p := fun i ↦ i.down.order
  let D := fun i : I ↦ puncturedLevel t (ord i).val
  let TR := fun (i j : I) (h : i ≤ j) ↦ lt (ord i) (ord j) h
  let IN := fun i : I ↦ li (ord i)
  have hid (i : I) : TR i i le_rfl = RingHom.id _ := by
    change Algebra.LocalizationColimit.map s
      (Algebra.ParameterRoot.transition t (ord i).val (ord i).val _) = _
    rw [Algebra.ParameterRoot.transition_self t _ (ord i).property.1,
      Algebra.LocalizationColimit.map_id]
  have hcomp (i j k : I) (h : i ≤ j) (h' : j ≤ k) :
      (TR j k h').comp (TR i j h) = TR i k (h.trans h') := by
    rw [Algebra.LocalizationColimit.map_comp, Algebra.ParameterRoot.transition_comp]
  have hinc (i j : I) (h : i ≤ j) : (IN j).comp (TR i j h) = IN i :=
    hli (ord i) (ord j) h
  have hcol (Q : Type u) [CommRing Q] (a : ∀ i : I, D i →+* Q)
      (ha : ∀ i j (h : i ≤ j), (a j).comp (TR i j h) = a i) :
      ∃! g : puncturedFull p t →+* Q, ∀ i, g.comp (IN i) = a i := by
    obtain ⟨g, hg, hu⟩ := hlcol Q (fun n ↦ a (idx n))
      (fun n m h ↦ ha (idx n) (idx m) h)
    refine ⟨g, fun i ↦ ?_, fun k hk ↦ hu k (fun n ↦ hk (idx n))⟩
    exact hg (ord i)
  have hfull : (fullMap p t).FaithfullyFlat ∧ (fullMap p t).IndEtale := by
    apply Algebra.PresentedRingColimit.faithfullyFlat_indEtale D TR hid hcomp
      (puncturedFull p t) IN hinc hcol (fun i ↦ levelMap t (ord i).val)
      (fullMap p t)
    · intro i j h
      exact Algebra.LocalizationColimit.map_base s (tr (ord i) (ord j) h)
    · exact fun i ↦ hbase (ord i)
    · exact fun i ↦ (hlevel (ord i)).1
    · exact fun i ↦ (hlevel (ord i)).2.2
  have hscheme (Z : Scheme.{u}) (a : ∀ n : TameRootOrder p,
      Z ⟶ Spec (.of (puncturedLevel t n.val)))
      (ha : ∀ n m (h : n.val ∣ m.val),
        a m ≫ Spec.map (CommRingCat.ofHom (lt n m h)) = a n) :
      ∃! g : Z ⟶ Spec (.of (puncturedFull p t)),
        ∀ n, g ≫ Spec.map (CommRingCat.ofHom (li n)) = a n := by
    obtain ⟨g, hg, hu⟩ := Algebra.PresentedRingColimit.scheme_existsUnique D TR hid hcomp
      (puncturedFull p t) IN hinc hcol Z (fun i ↦ a (ord i))
      (fun i j h ↦ ha (ord i) (ord j) h)
    exact ⟨g, fun n ↦ hg (idx n), fun k hk ↦ hu k (fun i ↦ hk (ord i))⟩
  refine ⟨tr, inc, lt, li, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, hli, hbase, hlcol, hscheme, hfull.1, ?_, ?_, ?_, ?_⟩
  · exact fun n m h i ↦ Algebra.ParameterRoot.transition_root t n.val m.val h i
  · exact fun n ↦ Algebra.ParameterRoot.transition_self t n.val n.property.1
  · exact fun n m l h h' ↦ Algebra.ParameterRoot.transition_comp t n.val m.val l.val h h'
  · exact fun n ↦ Algebra.ParameterRoot.exists_basis t n.val n.property.1
  · intro n m h
    have hq : 0 < m.val / n.val := Nat.div_pos (Nat.le_of_dvd m.property.1 h) n.property.1
    exact ⟨⟨Algebra.ParameterRoot.refineEquiv t n.val m.val h,
      Algebra.ParameterRoot.refineEquiv_algebraMap t n.val m.val h,
      Algebra.ParameterRoot.refineEquiv_root t n.val m.val h⟩,
      Algebra.ParameterRoot.exists_transition_basis t n.val m.val h hq⟩
  · exact fun n i ↦ Algebra.ParameterRoot.inclusion_root t p n i
  · exact fun n m h ↦ Algebra.ParameterRoot.inclusion_comp t p n m h
  · exact fun Q _ a ha ↦ Algebra.ParameterRoot.full_isColimit t p a ha
  · exact fun n m h a ↦ Algebra.LocalizationColimit.map_apply s (tr n m h) a
  · exact fun n ↦ hgeometry _ (hlevel n).1 (hlevel n).2.1 (hlevel n).2.2
  · intro n m h
    have hq : 0 < m.val / n.val := Nat.div_pos (Nat.le_of_dvd m.property.1 h) n.property.1
    obtain ⟨hfin, hff⟩ := Algebra.ParameterRoot.localized_transition_finite_faithfullyFlat
      t n.val s m.val h hq
    exact hgeometry _ hff hfin (Algebra.ParameterRoot.punctured_transition_etale
      t n.val m.val h n.property.1 m.property.1 (hunit n) (hunit m))
  · exact fun n a ↦ Algebra.LocalizationColimit.map_apply s (inc n) a
  · exact (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (fullMap p t))).mpr hfull.1 |>.2
  · let : Algebra (Localization.Away s) (puncturedFull p t) := (fullMap p t).toAlgebra
    have hi : Algebra.IndEtale (Localization.Away s) (puncturedFull p t) := hfull.2
    have hw := etale_indEtale_weaklyEtale_comparison.2.1 _ _ hi
    have : Surjective (Spec.map (CommRingCat.ofHom (fullMap p t))) :=
      (flat_and_surjective_SpecMap_iff _).mpr hfull.1 |>.2
    exact Scheme.Hom.singleton_mem_propQCPrecoverage hw
  · exact (Algebra.ParameterRoot.oneEquiv t).symm.bijective
  · intro hr
    subst r
    exact ⟨fun n ↦ (Algebra.ParameterRoot.emptyEquiv n.val t).symm.bijective,
      Algebra.ParameterRoot.full_empty_bijective p t⟩

end AlgebraicGeometry
