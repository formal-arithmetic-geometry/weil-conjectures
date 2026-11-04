/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Additive

/-! # Subcomplexes cut out by degreewise retracts

`HomologicalComplex.ofRetract` is the complex with terms `T n`, mapped to `K.X n` by `i n` with a
retraction `s n`, whose differential `i ≫ K.d ≫ s` is compatible with `i` (the image of `i` is
stable under the differential).
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {V : Type*} [Category V] [Preadditive V] {ι : Type*} {c : ComplexShape ι}

/-- The subcomplex of `K` given by degreewise objects `T n` with maps `i n : T n ⟶ K.X n`
and `s n : K.X n ⟶ T n` such that the differential of `K` restricted along `i` is unchanged
by the idempotent `s ≫ i`.  The differential is `i ≫ K.d ≫ s`. -/
@[simps]
def ofRetract (K : HomologicalComplex V c) (T : ι → V) (i : ∀ n, T n ⟶ K.X n)
    (s : ∀ n, K.X n ⟶ T n) (hd : ∀ n m, i n ≫ K.d n m ≫ s m ≫ i m = i n ≫ K.d n m) :
    HomologicalComplex V c where
  X := T
  d n m := i n ≫ K.d n m ≫ s m
  shape n m h := by rw [K.shape n m h, zero_comp, comp_zero]
  d_comp_d' n m l _ _ := by
    rw [Category.assoc, Category.assoc, reassoc_of% (hd n m), K.d_comp_d_assoc, zero_comp,
      comp_zero]

/-- The inclusion of the subcomplex `ofRetract K T i s hd` into `K`. -/
@[simps]
def ofRetractι (K : HomologicalComplex V c) (T : ι → V) (i : ∀ n, T n ⟶ K.X n)
    (s : ∀ n, K.X n ⟶ T n) (hd : ∀ n m, i n ≫ K.d n m ≫ s m ≫ i m = i n ≫ K.d n m) :
    ofRetract K T i s hd ⟶ K where
  f := i
  comm' n m _ := by rw [ofRetract_d, Category.assoc, Category.assoc, hd]

/-- The inclusion of `ofRetract K T i s hd` is a monomorphism when `s` retracts `i`. -/
lemma mono_ofRetractι (K : HomologicalComplex V c) (T : ι → V) (i : ∀ n, T n ⟶ K.X n)
    (s : ∀ n, K.X n ⟶ T n) (hd : ∀ n m, i n ≫ K.d n m ≫ s m ≫ i m = i n ≫ K.d n m)
    (hi : ∀ n, i n ≫ s n = 𝟙 _) : Mono (ofRetractι K T i s hd) :=
  mono_of_mono_f _ fun n ↦ (SplitMono.mk (s n) (hi n)).mono

/-- The comparison map between two subcomplexes given by retracts, when the first one
factors through the second. -/
@[simps]
def ofRetractMap (K : HomologicalComplex V c) {T T' : ι → V} {i : ∀ n, T n ⟶ K.X n}
    {s : ∀ n, K.X n ⟶ T n} {hd : ∀ n m, i n ≫ K.d n m ≫ s m ≫ i m = i n ≫ K.d n m}
    {i' : ∀ n, T' n ⟶ K.X n} {s' : ∀ n, K.X n ⟶ T' n}
    {hd' : ∀ n m, i' n ≫ K.d n m ≫ s' m ≫ i' m = i' n ≫ K.d n m}
    (h : ∀ n, i' n ≫ s n ≫ i n = i' n) :
    ofRetract K T' i' s' hd' ⟶ ofRetract K T i s hd where
  f n := i' n ≫ s n
  comm' n m _ := by
    rw [ofRetract_d, ofRetract_d, Category.assoc, reassoc_of% (h n), Category.assoc,
      Category.assoc, reassoc_of% (hd' n m)]

/-- The comparison map `ofRetractMap` commutes with the two inclusions into `K`. -/
lemma ofRetractMap_comp_ofRetractι (K : HomologicalComplex V c) {T T' : ι → V}
    {i : ∀ n, T n ⟶ K.X n} {s : ∀ n, K.X n ⟶ T n}
    {hd : ∀ n m, i n ≫ K.d n m ≫ s m ≫ i m = i n ≫ K.d n m}
    {i' : ∀ n, T' n ⟶ K.X n} {s' : ∀ n, K.X n ⟶ T' n}
    {hd' : ∀ n m, i' n ≫ K.d n m ≫ s' m ≫ i' m = i' n ≫ K.d n m}
    (h : ∀ n, i' n ≫ s n ≫ i n = i' n) :
    ofRetractMap K (hd := hd) (hd' := hd') h ≫ ofRetractι K T i s hd =
      ofRetractι K T' i' s' hd' := by
  ext n
  exact (Category.assoc _ _ _).trans (h n)

end HomologicalComplex
