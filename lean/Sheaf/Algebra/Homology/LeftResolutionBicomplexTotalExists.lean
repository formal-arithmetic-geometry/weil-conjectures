/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.FromJoel.Algebra.Homology.LeftResolution.CochainComplexMinus

/-!
# Finite diagonal totals for the bounded-minus resolution bicomplex

Source: `WeilConjectures/FromJoel/Algebra/Homology/LeftResolution/CochainComplexMinus.lean`,
lines 48--108 (blueprint: lem-sfb-left-resolution-bicomplex-total-exists).
-/

@[expose] public section

set_option linter.style.haveILetI false

universe vA uA vC uC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.LeftResolution

/--
For a bounded-above complex, the resolution bicomplex and its termwise image have
finite diagonal totals and the stated zero support.

Source: `WeilConjectures/FromJoel/Algebra/Homology/LeftResolution/CochainComplexMinus.lean`,
lines 48--108 (blueprint: lem-sfb-left-resolution-bicomplex-total-exists).

Proof (the four clauses of the source argument):
1. `Λ.bicomplexFunctor.obj K` is the bicomplex whose `(p,q)` term is the
   `q`-th term of the objectwise cochain resolution of `K.X p`; its two
   differentials are inherited from the two complex directions.
2. The resolution columns are strictly supported in degrees `q ≤ 0`, and the
   same support holds after applying `ι`, so both bidegree terms are zero for
   `q > 0`.
3. The hypothesis `hK` gives strict support of `K` in degrees `p ≤ b`. The
   corresponding support instance for the bicomplex (and its mapped image)
   makes every bidegree term zero for `p > b`.
4. `HomologicalComplex₂.hasTotal_of_isStrictlyLE` applied with bounds `b` and
   `0` supplies the diagonal total complexes for the bicomplex and its image.
-/
theorem leftResolution_bicomplex_total_exists
    {A : Type uA} [Category.{vA, uA} A] [Abelian A]
    {C : Type uC} [Category.{vC, uC} C] [Preadditive C]
    [HasZeroObject C] [HasFiniteCoproducts C]
    {ι : C ⥤ A} [ι.Full] [ι.Faithful] [ι.Additive]
    (Λ : LeftResolution ι) [Λ.F.PreservesZeroMorphisms]
    (K : CochainComplex A ℤ) (b : ℤ)
    (hK : ∀ p : ℤ, b < p → IsZero (K.X p)) :
    (∀ (p q : ℤ), 0 < q →
      IsZero (((Λ.bicomplexFunctor.obj K).X p).X q)) ∧
    (∀ (p q : ℤ), b < p →
      IsZero (((Λ.bicomplexFunctor.obj K).X p).X q)) ∧
    (∀ (p q : ℤ), 0 < q →
      IsZero ((((ι.mapHomologicalComplex₂ (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj (Λ.bicomplexFunctor.obj K)).X p).X q)) ∧
    (∀ (p q : ℤ), b < p →
      IsZero ((((ι.mapHomologicalComplex₂ (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj (Λ.bicomplexFunctor.obj K)).X p).X q)) ∧
    (Λ.bicomplexFunctor.obj K).HasTotal (ComplexShape.up ℤ) ∧
    ((ι.mapHomologicalComplex₂ (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)).obj (Λ.bicomplexFunctor.obj K)).HasTotal
      (ComplexShape.up ℤ) := by
  letI : K.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff K b).2 hK
  constructor
  · intro p q hq
    exact CochainComplex.isZero_of_isStrictlyLE _ 0 q hq
  constructor
  · intro p q hp
    have hz : IsZero ((Λ.bicomplexFunctor.obj K).X p) :=
      CochainComplex.isZero_of_isStrictlyLE _ b p hp
    exact (HomologicalComplex.eval _ _ q).map_isZero hz
  constructor
  · intro p q hq
    exact CochainComplex.isZero_of_isStrictlyLE _ 0 q hq
  constructor
  · intro p q hp
    have hz : IsZero (((ι.mapHomologicalComplex₂ (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj (Λ.bicomplexFunctor.obj K)).X p) :=
      CochainComplex.isZero_of_isStrictlyLE _ b p hp
    exact (HomologicalComplex.eval _ _ q).map_isZero hz
  constructor
  · exact HomologicalComplex₂.hasTotal_of_isStrictlyLE _ b 0
  · exact HomologicalComplex₂.hasTotal_of_isStrictlyLE _ b 0


end CategoryTheory.Abelian.LeftResolution
