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

end AlgebraicGeometry.Scheme.EtaleTorsor
