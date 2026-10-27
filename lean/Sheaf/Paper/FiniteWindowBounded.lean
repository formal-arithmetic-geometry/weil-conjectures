/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.UniformConstructibleExt
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.Paper.ConstructibleIndExtBound
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Lower-tail vanishing for bounded ind-constructible complexes

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-finite-window,
sk-lem-finite-window-bounded.md and its proof (blueprint: det-finite-window-bounded).

The two statements cover finite subextensions E and the condensed algebraic closure.
IndCons is the replete filtered-colimit closure `ObjectProperty.ind` of finite constant-model
constructibility. Dic membership is imposed on every cohomology sheaf in the ordinary
ambient derived category. Boundedness means finite support of the cohomology sheaves.
Ext uses its standard size convention and `Abelian.Ext.homAddEquiv` identifies it with
shifted ambient derived morphisms.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem hom_subsingleton_of_iso
    {A : Type*} [Category A] {S M N : A} (e : M ≅ N)
    (h : Subsingleton (S ⟶ M)) : Subsingleton (S ⟶ N) := by
  constructor
  intro f g
  have hfg : f ≫ e.inv = g ≫ e.inv := h.elim _ _
  simpa using congrArg (fun k ↦ k ≫ e.hom) hfg

/-- Finite cohomology support and vanishing on each cohomology summand suffice.
This is the source library's degreewise bounded devissage, applied to Hom vanishing. -/
private theorem hom_subsingleton_of_finite_cohomology
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (S L : DerivedCategory A)
    (hf : {q : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor A q).obj L)}.Finite)
    (hH : ∀ q : ℤ, Subsingleton
      (S ⟶ (DerivedCategory.singleFunctor A q).obj
        ((DerivedCategory.homologyFunctor A q).obj L))) :
    Subsingleton (S ⟶ L) := by
  classical
  let Q : ObjectProperty (DerivedCategory A) := fun M ↦ Subsingleton (S ⟶ M)
  have : Q.IsClosedUnderIsomorphisms :=
    ⟨fun e h ↦ hom_subsingleton_of_iso e h⟩
  let P : ℤ → ObjectProperty A := fun q N ↦ Q ((DerivedCategory.singleFunctor A q).obj N)
  have (q : ℤ) : (P q).IsClosedUnderIsomorphisms :=
    ⟨fun e h ↦ hom_subsingleton_of_iso ((DerivedCategory.singleFunctor A q).mapIso e) h⟩
  have hQzero : ∀ M, IsZero M → Q M := by
    intro M hM
    exact ⟨fun f g ↦ hM.eq_of_tgt f g⟩
  have hQext : ∀ T ∈ distTriang (DerivedCategory A),
      Q T.obj₁ → Q T.obj₃ → Q T.obj₂ := by
    intro T hT h₁ h₃
    refine subsingleton_of_forall_eq 0 fun f ↦ ?_
    obtain ⟨g, hg⟩ := Pretriangulated.Triangle.coyoneda_exact₂ T hT f
      (h₃.elim _ _)
    rw [hg, h₁.elim g 0, zero_comp]
  obtain ⟨a, ha⟩ := hf.bddBelow
  obtain ⟨b, hb⟩ := hf.bddAbove
  have hge : L.IsGE a := (DerivedCategory.isGE_iff L a).mpr fun q hq ↦ by
    by_contra h
    exact (not_le_of_gt hq) (ha h)
  have hle : L.IsLE b := (DerivedCategory.isLE_iff L b).mpr fun q hq ↦ by
    by_contra h
    exact (not_le_of_gt hq) (hb h)
  exact DerivedCategory.prop_of_bounded_of_degreewise Q hQzero hQext P
    (fun _ _ h ↦ h) L ⟨⟨a, hge⟩, ⟨b, hle⟩⟩ hH

private theorem hom_single_of_ext_bound
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (C B : A) (d : ℕ) (q : ℤ) (hq : q ≤ -(d : ℤ) - 1)
    (hExt : Subsingleton
      (@Abelian.Ext _ _ _ (HasExt.standard _) C B (-q).toNat)) :
    Subsingleton ((DerivedCategory.singleFunctor A 0).obj C ⟶
      (DerivedCategory.singleFunctor A q).obj B) := by
  have : HasExt A := HasExt.standard A
  have hcast : ((-q).toNat : ℤ) = -q := Int.toNat_of_nonneg (by omega)
  have : Subsingleton ((DerivedCategory.singleFunctor A 0).obj C ⟶
      ((DerivedCategory.singleFunctor A 0).obj B)⟦((-q).toNat : ℤ)⟧) :=
    Equiv.subsingleton (Abelian.Ext.homEquiv (X := C) (Y := B)).symm
  have hshift : Subsingleton ((DerivedCategory.singleFunctor A 0).obj C ⟶
      ((DerivedCategory.singleFunctor A 0).obj B)⟦-q⟧) := by
    simpa only [hcast] using this
  exact hom_subsingleton_of_iso
    (((DerivedCategory.singleFunctors A).shiftIso (-q) q 0 (by omega)).app B) hshift

/-- Lower-tail vanishing for bounded complexes with finite-subextension coefficients.
The bound d_C is a chosen nonnegative integer satisfying the uniform constructible Ext
property, rather than a choice of witness from the existence theorem.
Source: blueprint main-20261015, sk-lem-finite-window-bounded, statement and proof
(blueprint: det-finite-window-bounded).

Proof:
1. Finite cohomology support supplies lower and upper cohomological bounds.
For S = C[0], the property Q(M) = Subsingleton Hom(S,M) is invariant under
isomorphism, contains zero objects, and is closed under middle terms of
distinguished triangles: coyoneda_exact₂ factors every map through the first
term once its composite into the third term vanishes.
2. Apply DerivedCategory.prop_of_bounded_of_degreewise with the degree-q heart
property Q(N[q]). This is the already proved truncation induction; it requires
only vanishing on each cohomology sheaf placed in its own degree.
3. Above -d_C-1 the cohomology sheaf is zero. At every other degree q, put
r = (-q).toNat. Then d_C < r and r = -q as integers. The sheaf-only input
constructibleInd_extBound applies to H^q(L), using hL and the supplied bound.
4. Ext.homEquiv and singleFunctors.shiftIso identify the resulting zero Ext
group with Hom(C[0], H^q(L)[-q]), completing the degreewise induction.
The general-scheme ind-sheaf Ext input is left in its own named theorem; the
existing indHeartII_vanishing has extra Noetherian hypotheses. -/
theorem finiteWindow_bounded
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u})
    (C : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hC : IsConstantModelConstructible (Profinite.continuousMapRingObj E) X C)
    (d_C : ℕ)
    (hExt : ∀ N : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E) X),
      IsConstantModelConstructible (Profinite.continuousMapRingObj E) X N →
      ∀ r : ℕ, d_C < r →
        Subsingleton (@Abelian.Ext _ _ _ (HasExt.standard _) C N r))
    (L : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X)))
    (hL : ∀ q : ℤ, ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
      ((DerivedCategory.homologyFunctor _ q).obj L))
    (hbounded : {q : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor _ q).obj L)}.Finite)
    (hvanish : ∀ q : ℤ, -(d_C : ℤ) - 1 < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj L)) :
    Subsingleton ((DerivedCategory.singleFunctor _ 0).obj C ⟶ L) := by
  apply hom_subsingleton_of_finite_cohomology _ L hbounded
  intro q
  by_cases hq : -(d_C : ℤ) - 1 < q
  · exact ⟨fun f g ↦ ((DerivedCategory.singleFunctor _ q).map_isZero (hvanish q hq)).eq_of_tgt
      f g⟩
  · apply hom_single_of_ext_bound C _ d_C q (by omega)
    exact constructibleInd_extBound ℓ E _ (Or.inl rfl) X C hC d_C hExt
      _ (hL q) (-q).toNat (by omega)

/-- Lower-tail vanishing for bounded complexes with condensed algebraic-closure coefficients.
The bound d_C is a chosen nonnegative integer satisfying the uniform constructible Ext
property, rather than a choice of witness from the existence theorem.
Source: blueprint main-20261015, sk-lem-finite-window-bounded, statement and proof
(blueprint: det-finite-window-bounded).

Proof:
1. Finite cohomology support supplies lower and upper cohomological bounds.
For S = C[0], the property Q(M) = Subsingleton Hom(S,M) is invariant under
isomorphism, contains zero objects, and is closed under middle terms of
distinguished triangles: coyoneda_exact₂ factors every map through the first
term once its composite into the third term vanishes.
2. Apply DerivedCategory.prop_of_bounded_of_degreewise with the degree-q heart
property Q(N[q]). This is the already proved truncation induction; it requires
only vanishing on each cohomology sheaf placed in its own degree.
3. Above -d_C-1 the cohomology sheaf is zero. At every other degree q, put
r = (-q).toNat. Then d_C < r and r = -q as integers. The sheaf-only input
constructibleInd_extBound applies to H^q(L), using hL and the supplied bound.
4. Ext.homEquiv and singleFunctors.shiftIso identify the resulting zero Ext
group with Hom(C[0], H^q(L)[-q]), completing the degreewise induction.
The general-scheme ind-sheaf Ext input is left in its own named theorem; the
existing indHeartII_vanishing has extra Noetherian hypotheses. -/
theorem finiteWindow_bounded_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u})
    (C : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
    (hC : IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X C)
    (d_C : ℕ)
    (hExt : ∀ N : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X),
      IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X N →
      ∀ r : ℕ, d_C < r →
        Subsingleton (@Abelian.Ext _ _ _ (HasExt.standard _) C N r))
    (L : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)))
    (hL : ∀ q : ℤ, ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
      ((DerivedCategory.homologyFunctor _ q).obj L))
    (hbounded : {q : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor _ q).obj L)}.Finite)
    (hvanish : ∀ q : ℤ, -(d_C : ℤ) - 1 < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj L)) :
    Subsingleton ((DerivedCategory.singleFunctor _ 0).obj C ⟶ L) := by
  apply hom_subsingleton_of_finite_cohomology _ L hbounded
  intro q
  by_cases hq : -(d_C : ℤ) - 1 < q
  · exact ⟨fun f g ↦ ((DerivedCategory.singleFunctor _ q).map_isZero (hvanish q hq)).eq_of_tgt
      f g⟩
  · apply hom_single_of_ext_bound C _ d_C q (by omega)
    exact constructibleInd_extBound ℓ ⟨⊥, inferInstance⟩ _ (Or.inr rfl) X C hC d_C hExt
      _ (hL q) (-q).toNat (by omega)


end AlgebraicGeometry.ProEtale
