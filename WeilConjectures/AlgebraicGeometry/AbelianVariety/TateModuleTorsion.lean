/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints
public import WeilConjectures.GroupTheory.TateModuleQuotient

/-!
# The Tate module of an abelian variety and its torsion points

Let `A` be an abelian variety over a field `K` and `ℓ` a prime. Since `A(K̄)` is `ℓ`-divisible,
the projection `T_ℓ A → A[ℓ ^ n](K̄)` induces an isomorphism `T_ℓ A / ℓ ^ n T_ℓ A ≃ A[ℓ ^ n](K̄)`.
The groups `A[ℓ ^ n](K̄)`, the transition maps and these projections are equivariant for
`Gal(K̄ / K)`. For `ℓ` invertible in `K` they do not change when `K̄` is replaced by a larger
algebraically closed field `Ω`: the map `A(K̄) → A(Ω)` is bijective on `ℓ ^ n`-torsion, and
induces an isomorphism of Tate modules.

## Main definitions

- `AlgebraicGeometry.IsAbelianVariety.tateModuleQuotientAddEquivTorsionBy`:
  `T_ℓ A / ℓ ^ n T_ℓ A ≃ A[ℓ ^ n](K̄)`.
- `AlgebraicGeometry.IsAbelianVariety.geometricPointsToPoints`: the map `A(K̄) → A(Ω)` for an
  extension `Ω` of `K̄`.

## Main statements

- `IsAbelianVariety.geometricPointsAddEquiv_zsmul_and_toTorsionBy_galoisRepresentation`:
  the Galois action commutes with the transition maps and with the projections from `T_ℓ A`.
- `AlgebraicGeometry.IsAbelianVariety.bijOn_geometricPointsToPoints_torsionBy`:
  `A[ℓ ^ n](K̄) → A[ℓ ^ n](Ω)` is bijective.
- `AlgebraicGeometry.IsAbelianVariety.bijective_tateModuleMap_geometricPointsToPoints`:
  `T_ℓ A` does not change when `K̄` is replaced by `Ω`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

open scoped Pointwise

namespace AlgebraicGeometry.IsAbelianVariety

variable {K : Type u} [Field K] (ℓ : ℕ) [Fact ℓ.Prime] (A : Over (Spec (.of K))) [GrpObj A]
  [IsAbelianVariety A]

/-- Blueprint `proposition-integral-tate-module--3`: the Tate module modulo `ℓ ^ n`.

Let `A` be an abelian variety over `K` and `ℓ` a prime. The canonical projection
`T_ℓ A → A[ℓ ^ n](K̄)` to the `n`-th coordinate
(`AddCommGroup.tateModule.toTorsionBy`) induces an isomorphism
`T_ℓ A / ℓ ^ n T_ℓ A ≃ A[ℓ ^ n](K̄)` (`tateModuleQuotientAddEquivTorsionBy_mk`), since `A(K̄)` is
`ℓ`-divisible (`AlgebraicGeometry.IsAbelianVariety.exists_zsmul_eq_geometricPoints`). -/
noncomputable def tateModuleQuotientAddEquivTorsionBy (n : ℕ) :
    tateModule ℓ A ⧸ ((ℓ : ℤ_[ℓ]) ^ n • (⊤ : Submodule ℤ_[ℓ] (tateModule ℓ A))) ≃+
      AddSubgroup.torsionBy (Additive (Scheme.specAlgebraicClosure K ⟶ A)) ((ℓ : ℤ) ^ n) :=
  AddCommGroup.tateModule.quotientAddEquivTorsionBy ℓ _
    (exists_zsmul_eq_geometricPoints A ℓ (Fact.out : ℓ.Prime).pos) n

/-- The isomorphism `T_ℓ A / ℓ ^ n T_ℓ A ≃ A[ℓ ^ n](K̄)` is induced by the projection to the
`n`-th coordinate. -/
@[simp]
theorem tateModuleQuotientAddEquivTorsionBy_mk (n : ℕ) (t : tateModule ℓ A) :
    tateModuleQuotientAddEquivTorsionBy ℓ A n (Submodule.Quotient.mk t) =
      AddCommGroup.tateModule.toTorsionBy ℓ _ n t :=
  rfl

/-- Blueprint `proposition-integral-tate-module--4` (Galois equivariance): the Galois action on
the torsion points of an abelian variety.

For `σ ∈ Gal(K̄ / K)`, acting on `A(K̄)` by coordinates
(`AlgebraicGeometry.IsAbelianVariety.geometricPointsAddEquiv`) and hence on each `A[ℓ ^ n](K̄)`
(`AddSubgroup.torsionByCongr`): the action commutes with the transition maps, multiplication by
`ℓ`, and with the projections `T_ℓ A → A[ℓ ^ n](K̄)`, `T_ℓ A` carrying the Galois representation
`AlgebraicGeometry.IsAbelianVariety.galoisRepresentation`. -/
theorem geometricPointsAddEquiv_zsmul_and_toTorsionBy_galoisRepresentation
    (σ : Gal(AlgebraicClosure K/K)) (n : ℕ) :
    (∀ x, geometricPointsAddEquiv (A := A) σ ((ℓ : ℤ) • x) =
      (ℓ : ℤ) • geometricPointsAddEquiv σ x) ∧
      ∀ t : tateModule ℓ A,
        AddCommGroup.tateModule.toTorsionBy ℓ _ n (galoisRepresentation ℓ A σ t) =
          AddSubgroup.torsionByCongr (geometricPointsAddEquiv σ) _
            (AddCommGroup.tateModule.toTorsionBy ℓ _ n t) :=
  ⟨fun x ↦ map_zsmul _ _ x, fun _ ↦ rfl⟩

section BaseChange

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra (AlgebraicClosure K) Ω]
  [IsScalarTower K (AlgebraicClosure K) Ω]

variable (Ω) in
/-- The morphism `Spec Ω ⟶ Spec K̄` over `K` induced by a field extension `Ω` of `K̄`. -/
noncomputable def specToSpecAlgebraicClosure :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) ⟶ Scheme.specAlgebraicClosure K :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure K) Ω))) <| by
    change _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

omit [IsAbelianVariety A] in
variable (Ω) in
/-- The map `A(K̄) → A(Ω)` on points, for a field extension `Ω` of `K̄`. -/
noncomputable def geometricPointsToPoints :
    Additive (Scheme.specAlgebraicClosure K ⟶ A) →+
      Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) ⟶ A) :=
  AddMonoidHom.mk' (fun P ↦ .ofMul (specToSpecAlgebraicClosure Ω ≫ P.toMul)) fun P Q ↦
    congrArg Additive.ofMul (MonObj.comp_mul _ P.toMul Q.toMul)

omit [IsAbelianVariety A] in
/-- The map `A(K̄) → A(Ω)` is injective, since `Spec Ω ⟶ Spec K̄` is faithfully flat, hence an
epimorphism of schemes. -/
theorem injective_geometricPointsToPoints :
    Function.Injective (geometricPointsToPoints A Ω) := by
  have h : (algebraMap (AlgebraicClosure K) Ω).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance
  obtain ⟨_, _⟩ := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap (AlgebraicClosure K) Ω))).2 h
  have : Epi (Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure K) Ω))) :=
    Flat.epi_of_flat_of_surjective _
  intro P Q hPQ
  refine Additive.toMul.injective (Over.OverMorphism.ext ?_)
  exact (cancel_epi (Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure K) Ω)))).mp
    (congrArg (fun R ↦ (Additive.toMul R).left) hPQ)

/-- Blueprint `proposition-integral-tate-module--4` (independence of the algebraically closed
field): the torsion points do not change under extension of the algebraically closed field.

Let `A` be an abelian variety over `K`, `ℓ` a prime invertible in `K` and `Ω` an algebraically
closed field extension of `K̄`. Then `A(K̄) → A(Ω)` maps `A[ℓ ^ n](K̄)` bijectively onto
`A[ℓ ^ n](Ω)`: it is injective (`injective_geometricPointsToPoints`) and both groups are
`(ℤ / ℓ ^ n) ^ (2 g)`
(`AlgebraicGeometry.IsAbelianVariety.nonempty_addEquiv_torsionBy_points`). Being additive, the
map commutes with the transition maps. -/
theorem bijOn_geometricPointsToPoints_torsionBy [IsAlgClosed Ω] (hℓ : (ℓ : K) ≠ 0) (n : ℕ) :
    Set.BijOn (geometricPointsToPoints A Ω)
      (AddSubgroup.torsionBy (Additive (Scheme.specAlgebraicClosure K ⟶ A)) ((ℓ : ℤ) ^ n))
      (AddSubgroup.torsionBy
        (Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) ⟶ A))
        ((ℓ : ℤ) ^ n)) := by
  have hp : ¬ ringChar K ∣ ℓ ^ n := fun h ↦
    pow_ne_zero n hℓ (by exact_mod_cast (ringChar.spec K (ℓ ^ n)).2 h)
  have hn : 0 < ℓ ^ n := pow_pos (Fact.out : ℓ.Prime).pos n
  obtain ⟨e⟩ := nonempty_addEquiv_torsionBy_points (K' := AlgebraicClosure K) A (ringChar K)
    (ℓ ^ n) hn hp
  obtain ⟨e'⟩ := nonempty_addEquiv_torsionBy_points (K' := Ω) A (ringChar K) (ℓ ^ n) hn hp
  rw [Nat.cast_pow] at e e'
  have := Finite.of_equiv _ e'.symm.toEquiv
  have hmaps : Set.MapsTo (geometricPointsToPoints A Ω)
      (AddSubgroup.torsionBy (Additive (Scheme.specAlgebraicClosure K ⟶ A)) ((ℓ : ℤ) ^ n))
      (AddSubgroup.torsionBy
        (Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) ⟶ A))
        ((ℓ : ℤ) ^ n)) := fun x hx ↦
    AddSubgroup.apply_mem_torsionBy (geometricPointsToPoints A Ω) hx
  have hinj := injective_geometricPointsToPoints A (Ω := Ω)
  refine ⟨hmaps, hinj.injOn, ?_⟩
  have hbij := (hmaps.restrict_inj.2 hinj.injOn).bijective_of_nat_card_le <|
    ((Nat.card_congr e'.toEquiv).trans (Nat.card_congr e.toEquiv).symm).le
  intro y hy
  obtain ⟨x, hx⟩ := hbij.2 ⟨y, hy⟩
  exact ⟨x, x.2, congrArg Subtype.val hx⟩

/-- Blueprint `proposition-integral-tate-module--4` (independence of the algebraically closed
field): the Tate module does not change under extension of the algebraically closed field.

Let `A` be an abelian variety over `K`, `ℓ` a prime invertible in `K` and `Ω` an algebraically
closed field extension of `K̄`. Then the map `T_ℓ A → T_ℓ (A(Ω))` induced by `A(K̄) → A(Ω)` is
bijective. As it acts coordinatewise, it commutes with the projections to the torsion points,
which are identified by
`AlgebraicGeometry.IsAbelianVariety.bijOn_geometricPointsToPoints_torsionBy`. -/
theorem bijective_tateModuleMap_geometricPointsToPoints [IsAlgClosed Ω] (hℓ : (ℓ : K) ≠ 0) :
    Function.Bijective
      (AddCommGroup.tateModule.map (ℓ := ℓ) (geometricPointsToPoints A Ω)) := by
  have hinj := injective_geometricPointsToPoints A (Ω := Ω)
  refine ⟨fun s t hst ↦ Subtype.ext <| funext fun n ↦ hinj ?_, fun s ↦ ?_⟩
  · exact congrFun (congrArg Subtype.val hst) n
  · choose x hx hxs using fun n ↦ (bijOn_geometricPointsToPoints_torsionBy ℓ A hℓ n).2.2
      (AddCommGroup.tateModule.pow_zsmul_coe s n)
    refine ⟨⟨x, fun n ↦ hx n, fun n ↦ hinj ?_⟩, Subtype.ext <| funext hxs⟩
    rw [map_zsmul, hxs, hxs]
    exact AddCommGroup.tateModule.zsmul_coe_succ s n

end BaseChange

end AlgebraicGeometry.IsAbelianVariety
