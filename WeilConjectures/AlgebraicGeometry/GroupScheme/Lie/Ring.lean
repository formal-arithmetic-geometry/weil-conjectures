/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Bracket

/-!
# The Lie algebra of a group scheme over a ring

The Lie algebra of a group scheme over `Spec R` through the points with values in the ring of
dual numbers.
-/

@[expose] public section

universe u

open CategoryTheory TrivSqZeroExt
open scoped MonObj

namespace AlgebraicGeometry

/-! ### Group schemes over a ring -/

section Ring

variable {R : Type u} [CommRing R]

namespace GrpObj

variable (G : Over (Spec (.of R))) [GrpObj G]

/-- The `R`-module structure on `Lie(G)` for a group scheme over `Spec R`, through
`R ≅ Γ(Spec R, 𝒪)`. -/
noncomputable instance : Module R (Lie G) :=
  Module.compHom (Lie G) (Scheme.ΓSpecIso (.of R)).inv.hom

/-- `Lie(G)` is a Lie algebra over `R`. (blueprint: `sk-d-tangent`) -/
noncomputable instance : LieAlgebra R (Lie G) where
  lie_smul := by sorry

variable {G} {H : Over (Spec (.of R))} [GrpObj H]

/-- The differential `df : Lie(G) → Lie(H)` of a homomorphism of group schemes `f : G ⟶ H` over
`R`: on infinitesimal points, `v ↦ v ≫ f`. It is a homomorphism of Lie algebras.
(blueprint: `sk-d-tangent`) -/
noncomputable def differential (f : G ⟶ H) [IsMonHom f] : Lie G →ₗ⁅R⁆ Lie H where
  toFun x := lieEquiv H (infPointsMap f ((lieEquiv G).symm x))
  map_add' x y := by
    simp only [lieEquiv_symm_add, map_mul, lieEquiv_mul]
  map_smul' c x := by
    change _ = c • lieEquiv H _
    rw [show c • x = (Scheme.ΓSpecIso (.of R)).inv.hom c • x from rfl, lieEquiv_symm_smul,
      show infPointsMap f (infPointsScale G _ ((lieEquiv G).symm x)) =
        infPointsScale H _ (infPointsMap f ((lieEquiv G).symm x)) from
          Subtype.ext ((coe_infPointsMap_apply _ _).trans (Category.assoc _ _ _))]
    exact toLie_infPointsScale H _ _
  map_lie' {x y} := by
    simp only [lie_def, Equiv.symm_apply_apply, infPointsMap_infBracket]

theorem differential_apply (f : G ⟶ H) [IsMonHom f] (x : Lie G) :
    differential f x = lieEquiv H (infPointsMap f ((lieEquiv G).symm x)) :=
  rfl

theorem differential_congr {f g : G ⟶ H} [IsMonHom f] [IsMonHom g] (e : f = g) :
    differential f = differential g := by
  subst e; rfl

theorem differential_id : differential (𝟙 G) = LieHom.id := by
  sorry

theorem differential_comp {K : Over (Spec (.of R))} [GrpObj K] (f : G ⟶ H) (g : H ⟶ K)
    [IsMonHom f] [IsMonHom g] : differential (f ≫ g) = (differential g).comp (differential f) := by
  sorry

/-- The differential of a monomorphism of group schemes, for instance of a closed immersion, is
injective. -/
theorem differential_injective (f : G ⟶ H) [IsMonHom f] [Mono f] :
    Function.Injective (differential f) := by
  sorry

/-- If the commutators of the points of `H` over `Spec R[ε, δ]/(ε², δ²)` factor through the
subgroup scheme `f : G ⟶ H`, then the brackets of tangent vectors of `H` are tangent to `G`: the
bracket is the mixed term of the commutator of the points `1 + εx` and `1 + δy`.
(blueprint: `sk-i-restriction`) -/
theorem lie_mem_range_differential_of_commutator_mem (f : G ⟶ H) [IsMonHom f] [Mono f]
    (hf : ∀ a b : Scheme.dualNumbers₂Over (Spec (.of R)) ⟶ H,
      a * b * a⁻¹ * b⁻¹ ∈ (IsMonHom.monoidHom f _).range)
    (x y : Lie H) : ⁅x, y⁆ ∈ (differential f).range := by
  obtain ⟨u, hu⟩ :=
    infBracket_mem_range_infPointsMap f hf ((lieEquiv H).symm x) ((lieEquiv H).symm y)
  exact (LieHom.mem_range _ _).2
    ⟨lieEquiv G u, by rw [differential_apply, Equiv.symm_apply_apply, hu, lie_def]⟩

/-- If the subgroup scheme `f : G ⟶ H` contains the commutators of `H`, then the brackets of
tangent vectors of `H` are tangent to `G`. (blueprint: `sk-i-restriction`) -/
theorem lie_mem_range_differential_of_containsCommutators (f : G ⟶ H) [IsMonHom f] [Mono f]
    [IsMonHom.ContainsCommutators f] (x y : Lie H) : ⁅x, y⁆ ∈ (differential f).range :=
  lie_mem_range_differential_of_commutator_mem f (fun a b ↦ MonoidHom.mem_range.2
    (IsMonHom.ContainsCommutators.exists_comp_eq_commutator f a b)) x y

/-- The tangent vectors of a central subgroup scheme `f : G ⟶ H` are central in `Lie(H)`: for
`x ∈ Lie(G)` and `y ∈ Lie(H)` the points `1 + εx` and `1 + δy` commute over `R[ε, δ]/(ε², δ²)`,
so the mixed term `⁅df(x), y⁆` of their commutator vanishes. (blueprint: `sk-p-comparison`) -/
theorem range_differential_le_center (f : G ⟶ H) [IsMonHom f]
    (hf : ∀ (X : Over (Spec (.of R))) (a : X ⟶ G) (b : X ⟶ H), (a ≫ f) * b = b * (a ≫ f)) :
    (differential f).range ≤ (LieAlgebra.center R (Lie H) : LieSubalgebra R (Lie H)) := by
  sorry

/-- The differential of an open immersion of group schemes `f : G ⟶ H` is bijective: every
infinitesimal point of `H` has the same underlying map as the identity section, hence factors
through the open subscheme `G`. -/
theorem differential_bijective_of_isOpenImmersion (f : G ⟶ H) [IsMonHom f]
    [IsOpenImmersion f.left] : Function.Bijective (differential f) := by
  sorry

/-- An open immersion of group schemes `G ⟶ H` identifies `Lie(G)` with `Lie(H)`. -/
noncomputable def lieEquivOfIsOpenImmersion (f : G ⟶ H) [IsMonHom f] [IsOpenImmersion f.left] :
    Lie G ≃ₗ⁅R⁆ Lie H :=
  LieEquiv.ofBijective _ (differential_bijective_of_isOpenImmersion f)

end GrpObj

/-! ### Points with values in the ring of dual numbers -/

/-- The `A`-points `X(A)` of a scheme `X` over `R`: the morphisms `Spec A ⟶ X` over `Spec R`. For a
group scheme `X` they form a group by `Hom.group`. -/
abbrev points (X : Over (Spec (.of R))) (A : Type u) [CommRing A] [Algebra R A] :=
  (Spec (.of A)).asOver (Spec (.of R)) ⟶ X

/-- The map `X(A) → X(B)` induced by an `R`-algebra homomorphism `φ : A → B`: precomposition with
`Spec φ : Spec B ⟶ Spec A`. -/
noncomputable def points.map (X : Over (Spec (.of R))) {A B : Type u} [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] (φ : A →ₐ[R] B) (x : points X A) : points X B :=
  (Spec.map (CommRingCat.ofHom φ.toRingHom)).asOver (Spec (.of R)) ≫ x

variable (G : Over (Spec (.of R))) [GrpObj G]

/-- The tangent group `T_1 G = ker(G(R[ε]) → G(R))` of a group scheme `G` over `R`: the points of
`G` with values in the ring of dual numbers that reduce to the identity modulo `ε`. Through the
isomorphism `(Spec R)[ε] ≅ Spec R[ε]` these are the infinitesimal points of `G`.
(blueprint: `sk-d-tangent`) -/
noncomputable def tangentGroup : Subgroup (points G (DualNumber R)) :=
  (pointsPrecomp G ((Spec.map (CommRingCat.ofHom (fstHom R R R).toRingHom)).asOver _)).ker

theorem mem_tangentGroup {x : points G (DualNumber R)} :
    x ∈ tangentGroup G ↔ points.map G (fstHom R R R) x = 1 :=
  MonoidHom.mem_ker

/-- The isomorphism `(Spec R)[ε] ⟶ Spec R[ε]` as a morphism over `Spec R`. -/
noncomputable def dualNumbersToSpecOver :
    Scheme.dualNumbersOver (Spec (.of R)) ⟶ (Spec (.of (DualNumber R))).asOver (Spec (.of R)) :=
  Over.homMk (Scheme.dualNumbersToSpec (.of R)) (Scheme.dualNumbersToSpec_comp_specMap (.of R))

instance : IsIso (dualNumbersToSpecOver (R := R)) := by
  have : IsIso ((Over.forget _).map (dualNumbersToSpecOver (R := R))) :=
    Scheme.isIso_dualNumbersToSpec (.of R)
  exact isIso_of_reflects_iso _ (Over.forget _)

/-- The point `ε ↦ 0` of `Spec R[ε]` is the closed immersion `i : S ⟶ S[ε]` through
`(Spec R)[ε] ≅ Spec R[ε]`. -/
theorem specMap_fstHom_asOver_eq :
    (Spec.map (CommRingCat.ofHom (fstHom R R R).toRingHom)).asOver (Spec (.of R)) =
      CartesianMonoidalCategory.toUnit _ ≫ Scheme.dualNumbersιOver (Spec (.of R)) ≫
        dualNumbersToSpecOver := by
  ext1
  simp [dualNumbersToSpecOver, Scheme.ι_comp_dualNumbersToSpec, Over.toUnit_left,
    specOverSpec_over]
  rfl

/-- An infinitesimal point gives a point of the tangent group through `(Spec R)[ε] ≅ Spec R[ε]`. -/
theorem GrpObj.inv_dualNumbersToSpecOver_comp_mem_tangentGroup
    {v : Scheme.dualNumbersOver (Spec (.of R)) ⟶ G} (hv : v ∈ GrpObj.infPoints G) :
    inv dualNumbersToSpecOver ≫ v ∈ tangentGroup G := by
  rw [mem_tangentGroup, points.map, specMap_fstHom_asOver_eq]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [(GrpObj.mem_infPoints G).1 hv, MonObj.comp_one]

/-- A point of the tangent group gives an infinitesimal point through `(Spec R)[ε] ≅ Spec R[ε]`. -/
theorem GrpObj.dualNumbersToSpecOver_comp_mem_infPoints {x : points G (DualNumber R)}
    (hx : x ∈ tangentGroup G) :
    dualNumbersToSpecOver ≫ x ∈ GrpObj.infPoints G := by
  rw [mem_tangentGroup, points.map, specMap_fstHom_asOver_eq] at hx
  -- Writing `Over.homMk (𝟙 (Spec (.of R)))` rather than `Over.homMk (𝟙 _)` avoids a slow kernel
  -- check.
  let s : Over.mk (𝟙 (Spec (.of R))) ⟶ (Spec (.of R)).asOver (Spec (.of R)) :=
    Over.homMk (𝟙 (Spec (.of R))) (by simp [specOverSpec_over])
  have e : s ≫ CartesianMonoidalCategory.toUnit _ = 𝟙 _ :=
    CartesianMonoidalCategory.toUnit_unique _ _
  simp only [Category.assoc] at hx
  have h := congrArg (s ≫ ·) hx
  simp only [MonObj.comp_one] at h
  rw [← Category.assoc s, e, Category.id_comp] at h
  exact (GrpObj.mem_infPoints G).2 h

/-- The infinitesimal points of `G` are the points with values in the ring of dual numbers reducing
to the identity, through `(Spec R)[ε] ≅ Spec R[ε]`. -/
noncomputable def GrpObj.infPointsEquivTangentGroup : GrpObj.infPoints G ≃* tangentGroup G where
  toFun v :=
    ⟨inv dualNumbersToSpecOver ≫ v.1, GrpObj.inv_dualNumbersToSpecOver_comp_mem_tangentGroup G v.2⟩
  invFun x := ⟨dualNumbersToSpecOver ≫ x.1, GrpObj.dualNumbersToSpecOver_comp_mem_infPoints G x.2⟩
  left_inv v := Subtype.ext (IsIso.hom_inv_id_assoc dualNumbersToSpecOver v.1)
  right_inv x := Subtype.ext (IsIso.inv_hom_id_assoc dualNumbersToSpecOver x.1)
  map_mul' _ _ := Subtype.ext (MonObj.comp_mul _ _ _)

@[simp]
theorem GrpObj.coe_infPointsEquivTangentGroup_apply (v : GrpObj.infPoints G) :
    (GrpObj.infPointsEquivTangentGroup G v : points G (DualNumber R)) =
      inv dualNumbersToSpecOver ≫ (v : Scheme.dualNumbersOver _ ⟶ G) :=
  rfl

end Ring

end AlgebraicGeometry
