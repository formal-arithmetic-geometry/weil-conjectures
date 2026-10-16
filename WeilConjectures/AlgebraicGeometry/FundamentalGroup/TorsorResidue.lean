/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.BoundaryValuation

/-!
# The residue of a `ℤ / N`-torsor at a boundary point of a curve

Let `U ⊆ C` be a nonempty open of an integral scheme, `Ω` a separable closure of the function
field `k(C)` and `η : Spec Ω ⟶ U` the generic geometric point. For a `ℤ / N`-torsor `T` on `U`,
the Galois group `Gal(Ω / k(C))` acts on the points of `T` over `η`, through a character
`χ_T : Gal(Ω / k(C)) → ℤ / N` (`AlgebraicGeometry.Scheme.EtaleTorsor.galoisCharacter`):
`Spec σ ≫ t = t ≫ (χ_T(σ) +ᵥ ·)`. It is the monodromy character of `T` restricted to the Galois
group of the generic point (`AlgebraicGeometry.Scheme.EtaleTorsor.galoisCharacter_eq_monodromy`).

For an element `ξ ∈ Ω`, a *Kummer element* of `χ` against `ξ` is `x ≠ 0` in `Ω` with
`σ x = ξ ^ χ(σ) x` for all `σ`, whose `N`-th power lies in `k(C)`. Two Kummer elements differ by
a factor in `k(C)`, so that the order of vanishing `ord_z (x ^ N) mod N` at a point `z` does not
depend on the choice: this is the *Kummer residue*
`AlgebraicGeometry.Scheme.EtaleTorsor.kummerResidue χ z ξ ∈ ℤ / N`.

Let now `C` be a curve over a field `k` containing the `N`-th roots of unity, `N` invertible in
`k`. Every torsor has Kummer elements against every `N`-th root of unity `ξ ∈ μ_N(k)` (from the
Kummer element against a primitive root,
`AlgebraicGeometry.Scheme.EtaleTorsor.exists_kummer_element`),
and the Kummer residues against products of roots of unity add up. This defines the *residue*

`res_z(T) : μ_N(k) →+ ℤ / N`, an element of `Hom(μ_N, ℤ / N) = ℤ / N (-1)`

(`AlgebraicGeometry.Scheme.EtaleTorsor.residue`), the residue map of blueprint
`lem-wf-open-curve-residue-sequence`.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme.EtaleTorsor

open FiniteEtale

variable {C U : Scheme.{u}} [IsIntegral C] (j : U ⟶ C) [IsOpenImmersion j] [Nonempty U]

local notation "Ω" => SeparableClosure (Scheme.functionField C)

/-- The generic geometric point `Spec Ω ⟶ U` of a nonempty open `U` of an integral scheme `C`,
for `Ω` the separable closure of the function field of `C`. -/
noncomputable abbrev genericGeometricPoint : Spec (.of Ω) ⟶ U :=
  pointOfAlgebra Ω (genericPointLift j)

variable {N : ℕ} [NeZero N] (T : EtaleTorsor (ULift.{u + 1} (ZMod N)) U)

/-- A `k(C)`-automorphism `σ` of `Ω` moves a point of a `ℤ / N`-torsor over the generic geometric
point by translation. -/
lemma exists_specMap_comp_eq (σ : Gal(Ω/C.functionField)) (t : Spec (.of Ω) ⟶ T.P)
    (ht : t ≫ T.π = genericGeometricPoint j) :
    ∃ m : ZMod N, Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ t = t ≫ T.vadd ⟨m⟩ := by
  have ht' : (Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ t) ≫ T.π =
      genericGeometricPoint j := by
    rw [Category.assoc, ht]
    exact specMapIso_hom_comp_pointOfAlgebra _ σ
  obtain ⟨m, hm⟩ := T.exists_fiber_map_vaddHom (genericGeometricPoint j)
    (Over.homMk t ht : (fiber (genericGeometricPoint j)).obj T.toFiniteEtale)
    (Over.homMk _ ht')
  exact ⟨m.down, (congrArg CommaMorphism.left hm).symm⟩

/-- The point of a torsor over the generic geometric point used to define the Galois character. -/
noncomputable def genericFiberPoint : Spec (.of Ω) ⟶ T.P :=
  (T.nonempty_fiber (genericGeometricPoint j)).some.left

lemma genericFiberPoint_comp : T.genericFiberPoint j ≫ T.π = genericGeometricPoint j :=
  fiber_left_comp _ _

/-- The **Galois character** `χ_T : Gal(Ω / k(C)) → ℤ / N` of a `ℤ / N`-torsor `T` on `U`: a
`k(C)`-automorphism `σ` of `Ω` moves the points of `T` over the generic geometric point by
`χ_T(σ)`. -/
noncomputable def galoisCharacter (σ : Gal(Ω/C.functionField)) : ZMod N :=
  (T.exists_specMap_comp_eq j σ _ (T.genericFiberPoint_comp j)).choose

/-- `σ` moves every point of `T` over the generic geometric point by `χ_T(σ)`. -/
lemma specMap_comp_eq_comp_vadd_galoisCharacter (σ : Gal(Ω/C.functionField))
    (t : Spec (.of Ω) ⟶ T.P) (ht : t ≫ T.π = genericGeometricPoint j) :
    Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ t = t ≫ T.vadd ⟨T.galoisCharacter j σ⟩ := by
  have h₀ := (T.exists_specMap_comp_eq j σ _ (T.genericFiberPoint_comp j)).choose_spec
  obtain ⟨a, ha⟩ := T.exists_fiber_map_vaddHom (genericGeometricPoint j)
    (Over.homMk (T.genericFiberPoint j) (T.genericFiberPoint_comp j) :
      (fiber (genericGeometricPoint j)).obj T.toFiniteEtale) (Over.homMk t ht)
  have ht₀ : t = T.genericFiberPoint j ≫ T.vadd a := (congrArg CommaMorphism.left ha).symm
  rw [ht₀, reassoc_of% h₀, Category.assoc, ← T.add_vadd, ← T.add_vadd, add_comm]
  rfl

/-- The Galois character is characterised by the action on one point. -/
lemma galoisCharacter_eq_of_specMap_comp_eq (σ : Gal(Ω/C.functionField))
    (t : Spec (.of Ω) ⟶ T.P) (ht : t ≫ T.π = genericGeometricPoint j) {m : ZMod N}
    (h : Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ t = t ≫ T.vadd ⟨m⟩) :
    T.galoisCharacter j σ = m :=
  congrArg ULift.down (T.eq_of_comp_vadd_eq t
    ((T.specMap_comp_eq_comp_vadd_galoisCharacter j σ t ht).symm.trans h) default)

/-- Isomorphic torsors have the same Galois character. -/
lemma galoisCharacter_eq_of_isIsomorphic {T T' : EtaleTorsor (ULift.{u + 1} (ZMod N)) U}
    (h : T.IsIsomorphic T') : T.galoisCharacter j = T'.galoisCharacter j := by
  obtain ⟨φ, hφπ, hφv⟩ := h
  ext σ
  have ht : (T.genericFiberPoint j ≫ φ.hom) ≫ T'.π = genericGeometricPoint j := by
    rw [Category.assoc, hφπ, T.genericFiberPoint_comp j]
  refine (T'.galoisCharacter_eq_of_specMap_comp_eq j σ _ ht ?_).symm
  rw [← Category.assoc, T.specMap_comp_eq_comp_vadd_galoisCharacter j σ _
    (T.genericFiberPoint_comp j), Category.assoc, hφv, Category.assoc]

section Monodromy

variable [ConnectedSpace U] {Ω' : Type u} [Field Ω'] [IsSepClosed Ω'] {s : Spec (.of Ω') ⟶ U}
  (τ : fiber (genericGeometricPoint j) ≅ fiber s)
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]

/-- The Galois character of a torsor is its monodromy character composed with the map
`Gal(Ω / k(C)) → π₁(U, s)` of the generic point. -/
lemma galoisCharacter_eq_monodromy (σ : Gal(Ω/C.functionField)) :
    T.galoisCharacter j σ =
      (T.monodromy s G (galoisToFundamentalGroup (genericPointLift j) τ G σ)).toAdd.down :=
  T.galoisCharacter_eq_of_specMap_comp_eq j σ _ (T.genericFiberPoint_comp j)
    (specMap_comp_eq_comp_vadd_monodromy (genericPointLift j) τ G T σ _
      (T.genericFiberPoint_comp j))

end Monodromy

section KummerResidue

variable [IsLocallyNoetherian C]

omit [Nonempty U] in
/-- An element of `Ω` fixed by `Gal(Ω / k(C))` lies in `k(C)`. -/
lemma exists_algebraMap_eq_of_forall_apply_eq {y : Ω}
    (h : ∀ σ : Gal(Ω/C.functionField), σ y = y) :
    ∃ f : C.functionField, algebraMap C.functionField Ω f = y := by
  have hmem : y ∈ IntermediateField.fixedField
      (⊥ : IntermediateField C.functionField Ω).fixingSubgroup := by
    rw [IntermediateField.mem_fixedField_iff]
    exact fun σ _ ↦ h σ
  rw [InfiniteGalois.fixedField_fixingSubgroup] at hmem
  exact IntermediateField.mem_bot.1 hmem

omit [IsIntegral C] [IsLocallyNoetherian C] in
/-- The order of vanishing of a power. -/
lemma _root_.AlgebraicGeometry.Scheme.ord_pow {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] {g : X.functionField} (hg : g ≠ 0) (n : ℕ) (x : X) :
    X.ord (g ^ n) x = n * X.ord g x := by
  induction n with
  | zero =>
    have h := Scheme.ord_mul (x := x) (one_ne_zero (α := X.functionField)) one_ne_zero
    rw [mul_one] at h
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    omega
  | succ n ih =>
    rw [pow_succ, Scheme.ord_mul (pow_ne_zero n hg) hg, ih]
    push_cast
    ring

/-- `ξ ^ (a + b).val = ξ ^ a.val * ξ ^ b.val` for an `N`-th root of unity `ξ`. -/
lemma _root_.pow_zmod_val_add {M : Type*} [Monoid M] {ξ : M} (hξ : ξ ^ N = 1) (a b : ZMod N) :
    ξ ^ (a + b).val = ξ ^ a.val * ξ ^ b.val := by
  rw [← pow_add, ZMod.val_add, ← Nat.mod_add_div (a.val + b.val) N, pow_add, pow_mul, hξ,
    one_pow, mul_one, Nat.mod_add_div]

variable (C) in
open Classical in
/-- The **Kummer residue** at `z` of a function `χ : Gal(Ω / k(C)) → ℤ / N` against `ξ ∈ Ω`:
`ord_z (x ^ N) mod N` for a Kummer element `x` of `χ` against `ξ`, i.e. `x ≠ 0` with `x ^ N` in
`k(C)` and `σ x = ξ ^ χ(σ) x` for all `σ`. It does not depend on the choice of `x`
(`AlgebraicGeometry.Scheme.EtaleTorsor.kummerResidue_eq`), and is `0` if there is no Kummer
element. -/
noncomputable def kummerResidue (χ : Gal(Ω/C.functionField) → ZMod N) (z : C) (ξ : Ω) :
    ZMod N :=
  if h : ∃ x : Ω, ∃ f : C.functionField, x ≠ 0 ∧ algebraMap C.functionField Ω f = x ^ N ∧
      ∀ σ : Gal(Ω/C.functionField), σ x = ξ ^ (χ σ).val * x
  then (C.ord h.choose_spec.choose z : ZMod N) else 0

omit [Nonempty U] [IsLocallyNoetherian C] in
lemma ne_zero_of_algebraMap_eq_pow {x : Ω} (hx : x ≠ 0) {f : C.functionField}
    (hf : algebraMap C.functionField Ω f = x ^ N) : f ≠ 0 := fun h ↦
  hx (pow_eq_zero_iff (NeZero.ne N) |>.1 (by rw [← hf, h, map_zero]))

omit [Nonempty U] in
/-- The Kummer residue is computed by any Kummer element. -/
theorem kummerResidue_eq {χ : Gal(Ω/C.functionField) → ZMod N} (z : C) {ξ x : Ω}
    {f : C.functionField} (hx : x ≠ 0) (hf : algebraMap C.functionField Ω f = x ^ N)
    (hχ : ∀ σ : Gal(Ω/C.functionField), σ x = ξ ^ (χ σ).val * x) :
    kummerResidue C χ z ξ = (C.ord f z : ZMod N) := by
  have h : ∃ x : Ω, ∃ f : C.functionField, x ≠ 0 ∧ algebraMap C.functionField Ω f = x ^ N ∧
      ∀ σ : Gal(Ω/C.functionField), σ x = ξ ^ (χ σ).val * x := ⟨x, f, hx, hf, hχ⟩
  rw [kummerResidue, dif_pos h]
  obtain ⟨hx', hf', hχ'⟩ := h.choose_spec.choose_spec
  set x' := h.choose
  set f' := h.choose_spec.choose
  -- `x' / x` is fixed by the Galois group, hence lies in `k(C)`
  have hξ (σ : Gal(Ω/C.functionField)) : ξ ^ (χ σ).val ≠ 0 := by
    have : σ x ≠ 0 := (map_ne_zero_iff _ σ.injective).2 hx
    rw [hχ σ] at this
    exact left_ne_zero_of_mul this
  obtain ⟨g, hg⟩ := exists_algebraMap_eq_of_forall_apply_eq (C := C) (y := x' / x) fun σ ↦ by
    rw [map_div₀, hχ σ, hχ' σ, mul_div_mul_left _ _ (hξ σ)]
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, div_eq_zero_iff] at hg
    exact hg.elim hx' hx
  have hf0 := ne_zero_of_algebraMap_eq_pow hx hf
  have hff : f' = f * g ^ N := (algebraMap C.functionField Ω).injective (by
    rw [hf', map_mul, map_pow, hf, hg, ← mul_pow, mul_div_cancel₀ _ hx])
  rw [hff, Scheme.ord_mul hf0 (pow_ne_zero N hg0), Scheme.ord_pow hg0]
  push_cast
  rw [ZMod.natCast_self, zero_mul, add_zero]

omit [Nonempty U] in
/-- The Kummer residue against a product is the sum of the Kummer residues. -/
theorem kummerResidue_mul {χ : Gal(Ω/C.functionField) → ZMod N} (z : C) {ξ ξ' x x' : Ω}
    {f f' : C.functionField} (hx : x ≠ 0) (hf : algebraMap C.functionField Ω f = x ^ N)
    (hχ : ∀ σ : Gal(Ω/C.functionField), σ x = ξ ^ (χ σ).val * x) (hx' : x' ≠ 0)
    (hf' : algebraMap C.functionField Ω f' = x' ^ N)
    (hχ' : ∀ σ : Gal(Ω/C.functionField), σ x' = ξ' ^ (χ σ).val * x') :
    kummerResidue C χ z (ξ * ξ') = kummerResidue C χ z ξ + kummerResidue C χ z ξ' := by
  have hf0 := ne_zero_of_algebraMap_eq_pow hx hf
  have hf0' := ne_zero_of_algebraMap_eq_pow hx' hf'
  rw [kummerResidue_eq z hx hf hχ, kummerResidue_eq z hx' hf' hχ',
    kummerResidue_eq z (mul_ne_zero hx hx') (f := f * f') (by rw [map_mul, hf, hf', mul_pow])
      (fun σ ↦ by rw [map_mul, hχ, hχ', mul_pow]; ring),
    Scheme.ord_mul hf0 hf0']
  push_cast
  rfl

omit [Nonempty U] in
/-- The Kummer residue of a sum of characters is the sum of the Kummer residues. -/
theorem kummerResidue_add {χ χ' : Gal(Ω/C.functionField) → ZMod N} (z : C) {ξ x x' : Ω}
    (hξ : ξ ^ N = 1) {f f' : C.functionField} (hx : x ≠ 0)
    (hf : algebraMap C.functionField Ω f = x ^ N)
    (hχ : ∀ σ : Gal(Ω/C.functionField), σ x = ξ ^ (χ σ).val * x) (hx' : x' ≠ 0)
    (hf' : algebraMap C.functionField Ω f' = x' ^ N)
    (hχ' : ∀ σ : Gal(Ω/C.functionField), σ x' = ξ ^ (χ' σ).val * x') :
    kummerResidue C (χ + χ') z ξ = kummerResidue C χ z ξ + kummerResidue C χ' z ξ := by
  have hf0 := ne_zero_of_algebraMap_eq_pow hx hf
  have hf0' := ne_zero_of_algebraMap_eq_pow hx' hf'
  rw [kummerResidue_eq z hx hf hχ, kummerResidue_eq z hx' hf' hχ',
    kummerResidue_eq z (mul_ne_zero hx hx') (f := f * f') (by rw [map_mul, hf, hf', mul_pow])
      (fun σ ↦ by rw [map_mul, hχ, hχ', Pi.add_apply, pow_zmod_val_add hξ]; ring),
    Scheme.ord_mul hf0 hf0']
  push_cast
  rfl

end KummerResidue

end AlgebraicGeometry.Scheme.EtaleTorsor
