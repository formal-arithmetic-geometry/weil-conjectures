/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import WeilConjectures.AlgebraicGeometry.AbelianScheme.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify

/-!
# The `ℓ`-adic Tate module of an abelian scheme

Let `A` be an abelian scheme over a base scheme `S` and let `ℓ` be a prime. The `ℓ ^ n`-torsion
`A[ℓ ^ n] = ker [ℓ ^ n]` is the group scheme `AlgebraicGeometry.torsionSubgroupScheme A (ℓ ^ n)`
over `S`; its sheaf of points on the small étale site of `S` is
`AlgebraicGeometry.torsionSheaf A (ℓ ^ n)`, the sheaf of abelian groups `U ↦ A[ℓ ^ n](U)`.
Multiplication by `ℓ` maps `A[ℓ ^ (n + 1)]` to `A[ℓ ^ n]`, and the `ℓ`-adic Tate module of `A`
is the inverse limit

```
  T_ℓ A = lim_n A[ℓ ^ n]
```

of these sheaves along multiplication by `ℓ`, a sheaf of abelian groups on the small étale site
of `S`. Its rational form is `V_ℓ A = ℚ ⊗ T_ℓ A`, the sheaf associated to `U ↦ ℚ ⊗ T_ℓ A(U)`; as
`T_ℓ A` is a sheaf of `ℤ_[ℓ]`-modules this is `ℚ_[ℓ] ⊗_{ℤ_[ℓ]} T_ℓ A`.

For an abelian variety `A` over a field `K`, the global sections of `T_ℓ A` over `Spec K̄`, that
is, the stalk of `T_ℓ A` at the geometric point `Spec K̄ ⟶ Spec K`, are the blueprint's
`T_ℓ A = lim_n A[ℓ ^ n](K̄)`, the Tate module `AddCommGroup.tateModule` of the group of geometric
points. Over an algebraically closed field the global sections of `T_ℓ A` are free of rank
`2 * g` over `ℤ_[ℓ]`.

The sheaves take values in `Ab.{u + 1}`, abelian groups one universe above the base scheme
`S : Scheme.{u}`, following the convention of the `SixFunctors` and `ConstructibleSheaf`
folders; this is the universe in which sheafification on the small étale site is available
(`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`). The groups of points of
`A[n]` live in `Type u` and are lifted with `AddCommGrpCat.uliftFunctor`.

## Main definitions

- `AlgebraicGeometry.torsionPresheaf`: the presheaf of abelian groups `U ↦ G[n](U)` on the
  schemes over `S`, for a commutative group scheme `G` over `S`; it is represented by the
  torsion subgroup scheme `G[n] = ker [n]`
  (`AlgebraicGeometry.torsionPresheafRepresentableBy`).
- `AlgebraicGeometry.torsionSheaf`: its restriction to the small étale site of `S`, the sheaf
  of points of `G[n]`.
- `AlgebraicGeometry.torsionSheafMul`: multiplication by `k` as a map `G[m * k] ⟶ G[m]`.
- `AlgebraicGeometry.IsAbelianScheme.tateModuleSystem`: the inverse system `n ↦ A[ℓ ^ n]` along
  multiplication by `ℓ`.
- `AlgebraicGeometry.IsAbelianScheme.tateModule`,
  `AlgebraicGeometry.IsAbelianScheme.rationalTateModule`: `T_ℓ A = lim_n A[ℓ ^ n]` and
  `V_ℓ A = ℚ ⊗ T_ℓ A`.

## Main statements

- `AlgebraicGeometry.isSheaf_torsionSheafPresheaf`: the presheaf of points of `G[n]` is a sheaf
  for the small étale topology.
- `AlgebraicGeometry.IsAbelianScheme.nonempty_addEquiv_Γ_tateModule`:
  `Γ(Spec K, T_ℓ A) ≅ ℤ_[ℓ] ^ (2g)` over an algebraically closed field `K`.
- `AlgebraicGeometry.IsAbelianScheme.nonempty_addEquiv_Γ_rationalTateModule`:
  `Γ(Spec K, V_ℓ A) ≅ ℚ_[ℓ] ^ (2g)`.

## TODO

- `T_ℓ A` is a sheaf of `ℤ_[ℓ]`-modules, `ℤ_[ℓ]` acting on `A[ℓ ^ n]` through `ℤ/ℓ ^ n`; this
  structure is not declared, and the rank statements are stated as isomorphisms of abelian
  groups.
- The functoriality of `T_ℓ` in `A` — the action of an endomorphism of `A` — and the
  identification of the stalk of `T_ℓ A` at a geometric point `Spec Ω ⟶ S` with the Tate
  module `AddCommGroup.tateModule ℓ (A(Ω))` of the group of `Ω`-points, which carries the
  action of `π₁(S)`, are what the Weil conjectures actually use, and are not declared here.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite

namespace AlgebraicGeometry

variable {S : Scheme.{u}} {K : Type u} [Field K]

section Torsion

variable (G : Over S) [GrpObj G] [IsCommMonObj G]

omit [IsCommMonObj G] in
/-- Composition with the `m`-fold sum `[m] = 𝟙 G ^ m` of a group scheme is the `m`-th power on
points: `s ≫ [m] = s ^ m`. -/
theorem comp_npow_id {U : Over S} (s : U ⟶ G) (m : ℕ) : s ≫ 𝟙 G ^ m = s ^ m := by
  rw [MonObj.comp_pow, Category.comp_id]

/-- A point `s : U ⟶ G` lies in the kernel of `[m]` exactly when `s ^ m = 1`. -/
theorem mem_ker_npow_id_iff {U : Over S} (s : U ⟶ G) (m : ℕ) :
    s ∈ MonoidHom.ker (IsMonHom.monoidHom (𝟙 G ^ m) U) ↔ s ^ m = 1 := by
  rw [MonoidHom.mem_ker, IsMonHom.monoidHom_apply, comp_npow_id]

/-- Blueprint `sk-def-av-tate`: `ℓ`-adic Tate module.

The presheaf of points of the `n`-torsion `G[n] = ker [n]` of a commutative group scheme `G`
over `S`: it sends an `S`-scheme `U` to the group `G[n](U)` of `U`-points `s : U ⟶ G` of `G` with
`s ≫ [n] = 1`, written additively. It is the presheaf `CategoryTheory.GrpObj.kerPresheaf` of the
`n`-fold sum `[n] = 𝟙 G ^ n`, which the kernel `AlgebraicGeometry.torsionSubgroupScheme G n`
represents (`AlgebraicGeometry.torsionPresheafRepresentableBy`). -/
noncomputable def torsionPresheaf (n : ℕ) : (Over S)ᵒᵖ ⥤ Ab.{u} where
  obj U := AddCommGrpCat.of (Additive (MonoidHom.ker (IsMonHom.monoidHom (𝟙 G ^ n) U.unop)))
  map φ := AddCommGrpCat.ofHom
    (MonoidHom.toAdditive ((GrpObj.kerPresheaf (𝟙 G ^ n)).map φ).hom)
  map_id U := by ext s; exact Subtype.ext (Category.id_comp _)
  map_comp φ ψ := by ext s; exact Subtype.ext (Category.assoc _ _ _)

/-- The torsion subgroup scheme `G[n] = ker [n]` represents the presheaf of points
`AlgebraicGeometry.torsionPresheaf G n`. -/
noncomputable def torsionPresheafRepresentableBy (n : ℕ) :
    (torsionPresheaf G n ⋙ forget Ab.{u}).RepresentableBy (torsionSubgroupScheme G n) :=
  GrpObj.kerRepresentableBy (𝟙 G ^ n)

/-- Multiplication by `k` on points, `G[m * k](U) →* G[m](U)`, `s ↦ s ^ k`. -/
noncomputable def torsionPointsPow (m k : ℕ) (U : Over S) :
    MonoidHom.ker (IsMonHom.monoidHom (𝟙 G ^ (m * k)) U) →*
      MonoidHom.ker (IsMonHom.monoidHom (𝟙 G ^ m) U) where
  toFun s := ⟨s.1 ^ k, by
    have h := (mem_ker_npow_id_iff G s.1 (m * k)).mp s.2
    rw [mem_ker_npow_id_iff, ← pow_mul, mul_comm k m]
    exact h⟩
  map_one' := Subtype.ext (one_pow k)
  map_mul' a b := Subtype.ext (mul_pow a.1 b.1 k)

/-- Multiplication by `k` maps the `m * k`-torsion of `G` to the `m`-torsion: on points it is
`s ↦ s ^ k`, a homomorphism `G[m * k](U) → G[m](U)` natural in `U`. -/
noncomputable def torsionPresheafMul (m k : ℕ) :
    torsionPresheaf G (m * k) ⟶ torsionPresheaf G m where
  app U := AddCommGrpCat.ofHom (MonoidHom.toAdditive (torsionPointsPow G m k U.unop))
  naturality U V φ := by
    apply AddCommGrpCat.hom_ext
    ext s
    exact Subtype.ext (MonObj.comp_pow _ _ _).symm

/-- The presheaf of points of the `n`-torsion `G[n] = ker [n]` on the small étale site of `S`:
the restriction of `AlgebraicGeometry.torsionPresheaf G n` to the étale `S`-schemes, with values
lifted to `Ab.{u + 1}`. -/
noncomputable def torsionSheafPresheaf (n : ℕ) : S.Etaleᵒᵖ ⥤ Ab.{u + 1} :=
  (MorphismProperty.Over.forget @Etale ⊤ S).op ⋙ torsionPresheaf G n ⋙
    AddCommGrpCat.uliftFunctor.{u + 1, u}

/-- The presheaf of points of `G[n]` on the small étale site of `S` is a sheaf: a scheme over
`S` represents a sheaf for the fpqc topology, hence for the étale topology, on the schemes over
`S`, and the small étale site is a full subcategory on which the étale coverings are the same. -/
theorem isSheaf_torsionSheafPresheaf (n : ℕ) :
    Presheaf.IsSheaf S.smallEtaleTopology (torsionSheafPresheaf G n) :=
  sorry

/-- Blueprint `sk-def-av-tate`: `ℓ`-adic Tate module.

The sheaf of points of the `n`-torsion `G[n] = ker [n]` of a commutative group scheme `G` over
`S` on the small étale site of `S`: the restriction of `AlgebraicGeometry.torsionPresheaf G n`,
the presheaf `U ↦ G[n](U)` of the groups of `U`-points of `G` killed by `[n]`, to the étale
`S`-schemes `U`, with values lifted to `Ab.{u + 1}`. -/
noncomputable def torsionSheaf (n : ℕ) : Sheaf S.smallEtaleTopology Ab.{u + 1} :=
  ⟨torsionSheafPresheaf G n, isSheaf_torsionSheafPresheaf G n⟩

/-- Multiplication by `k` as a morphism of presheaves on the small étale site,
`AlgebraicGeometry.torsionPresheafMul` restricted to the étale `S`-schemes and lifted. -/
noncomputable def torsionSheafMulHom (m k : ℕ) :
    torsionSheafPresheaf G (m * k) ⟶ torsionSheafPresheaf G m :=
  Functor.whiskerLeft (MorphismProperty.Over.forget @Etale ⊤ S).op
    (Functor.whiskerRight (torsionPresheafMul G m k) AddCommGrpCat.uliftFunctor.{u + 1, u})

/-- Multiplication by `k` as a morphism of sheaves `G[m * k] ⟶ G[m]`. -/
noncomputable def torsionSheafMul (m k : ℕ) : torsionSheaf G (m * k) ⟶ torsionSheaf G m :=
  ObjectProperty.homMk (torsionSheafMulHom G m k)

end Torsion

namespace IsAbelianScheme

/- `AlgebraicGeometry.IsAbelianScheme.isCommMonObj` is a theorem, not an instance; it is made a
local instance here so that an abelian scheme is a commutative group scheme, whose torsion
subgroup schemes are group schemes and whose points form abelian groups. -/
attribute [local instance] IsAbelianScheme.isCommMonObj

variable (ℓ : ℕ) [Fact ℓ.Prime]

section general_base

variable (A : Over S) [GrpObj A] [IsAbelianScheme A]

/-- Blueprint `sk-def-av-tate`: `ℓ`-adic Tate module.

The inverse system `n ↦ A[ℓ ^ n]` of the sheaves of points of the `ℓ ^ n`-torsion subgroup
schemes `A[ℓ ^ n] = ker [ℓ ^ n]` of an abelian scheme `A` over `S`, the transition map from
level `n + 1` to level `n` being multiplication by `ℓ`. -/
noncomputable def tateModuleSystem : ℕᵒᵖ ⥤ Sheaf S.smallEtaleTopology Ab.{u + 1} :=
  Functor.ofOpSequence (X := fun n ↦ torsionSheaf A (ℓ ^ n)) fun n ↦ torsionSheafMul A (ℓ ^ n) ℓ

/-- Blueprint `sk-def-av-tate`: `ℓ`-adic Tate module.

The *`ℓ`-adic Tate module* of an abelian scheme `A` over `S` is the inverse limit
`T_ℓ A = lim_n A[ℓ ^ n]` of the sheaves of points of the torsion subgroup schemes
`A[ℓ ^ n] = ker [ℓ ^ n]` on the small étale site of `S`, the transition map from level `n + 1`
to level `n` being multiplication by `ℓ`. It is a sheaf of abelian groups on `S`, and in fact of
`ℤ_[ℓ]`-modules. For an abelian variety `A` over a field `K` its sections over `Spec K̄` are the
blueprint's `T_ℓ A = lim_n A[ℓ ^ n](K̄)`. -/
noncomputable def tateModule : Sheaf S.smallEtaleTopology Ab.{u + 1} :=
  limit (tateModuleSystem ℓ A)

/-- The rational Tate module `V_ℓ A = ℚ ⊗ T_ℓ A` of an abelian scheme `A` over `S`: the sheaf
associated to the presheaf `U ↦ ℚ ⊗_ℤ T_ℓ A(U)`. As `T_ℓ A` is a sheaf of `ℤ_[ℓ]`-modules and
`ℚ ⊗_ℤ ℤ_[ℓ] = ℚ_[ℓ]`, this is `ℚ_[ℓ] ⊗_{ℤ_[ℓ]} T_ℓ A`. -/
noncomputable def rationalTateModule : Sheaf S.smallEtaleTopology Ab.{u + 1} :=
  (presheafToSheaf S.smallEtaleTopology Ab.{u + 1}).obj
    ((tateModule ℓ A).obj ⋙ (forget₂ (ModuleCat.{u + 1} ℤ) Ab.{u + 1}).inv ⋙
      ModuleCat.extendScalars (Int.castRingHom ℚ) ⋙ forget₂ (ModuleCat.{u + 1} ℚ) Ab.{u + 1})

end general_base

/-- Blueprint `sk-prop-av-tate-rank`: The `ℓ`-adic Tate module is free of rank `2g`.

Let `A` be an abelian variety of dimension `g` over an algebraically closed field `K` and let
`ℓ ≠ char K`. Then `T_ℓ A ≅ ℤ_[ℓ] ^ (2 * g)`, where `T_ℓ A = lim_n A[ℓ ^ n](K)` is the group of
global sections of the sheaf `T_ℓ A` on the small étale site of `Spec K`. -/
theorem nonempty_addEquiv_Γ_tateModule [IsAlgClosed K] (p : ℕ) [CharP K p] (hℓ : ℓ ≠ p)
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianScheme A] :
    Nonempty ((Sheaf.Γ (Spec (.of K)).smallEtaleTopology Ab.{u + 1}).obj (tateModule ℓ A) ≃+
      (Fin (2 * IsAbelianScheme.dim A) → ℤ_[ℓ])) :=
  sorry

/-- Blueprint `sk-prop-av-tate-rank`: The `ℓ`-adic Tate module is free of rank `2g`.

Let `A` be an abelian variety of dimension `g` over an algebraically closed field `K` and let
`ℓ ≠ char K`. Then `V_ℓ A ≅ ℚ_[ℓ] ^ (2 * g)`, where `V_ℓ A = ℚ ⊗ lim_n A[ℓ ^ n](K)` is the group
of global sections of the sheaf `V_ℓ A` on the small étale site of `Spec K`. -/
theorem nonempty_addEquiv_Γ_rationalTateModule [IsAlgClosed K] (p : ℕ) [CharP K p]
    (hℓ : ℓ ≠ p) (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianScheme A] :
    Nonempty ((Sheaf.Γ (Spec (.of K)).smallEtaleTopology Ab.{u + 1}).obj
      (rationalTateModule ℓ A) ≃+ (Fin (2 * IsAbelianScheme.dim A) → ℚ_[ℓ])) :=
  sorry

end IsAbelianScheme

end AlgebraicGeometry
