/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.SixFunctors.Etale.Derived.Localization

/-!
# Kummer classes, their boundaries, and cup products with supports

The three cohomological constructions out of which the fundamental class of a regular closed
immersion is glued (`sk-thm-regular`):

* the *Kummer class* `κ(u) ∈ H¹(X, Λ(1))` of a unit `u`, the rank-one datum of
  `sk-def-purity-conv`, supplied by `AlgebraicGeometry.Etale.HasTateTwist`;
* the *Kummer boundary* `∂κ(f) ∈ H²_{V(f)}(U, Λ(1))` of a global function `f`: `f` is a unit
  on the open complement `U ∖ V(f)`, and the boundary of the supported localization triangle
  of `V(f) ⊂ U` carries its Kummer class to a class supported on `V(f)`;
* the *cup product with supports*
  `H^a_{Z₁}(U, M) × H^b_{Z₂}(U, N) ⟶ H^{a+b}_{Z₁ ∩ Z₂}(U, M ⊗ N)`.

A class with supports in `Z`, of degree `n` and coefficients `L`, is a morphism
`Λ_U ⟶ (Ri_! Ri^! L)[n]`, where `i : Z ⟶ U` is the closed immersion. The supported term is
`Ri_!`, as in the supported localization triangle
`AlgebraicGeometry.Etale.supportedLocalizationTriangle`; for a closed immersion it is `Ri_*`.

## Implementation notes

The closed subscheme `V(s)` cut out by a set `s` of global sections is
`(IdealSheafData.ofIdealTop (Ideal.span s)).subscheme`; its underlying set is the zero locus
of `s` (`AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι_ofIdealTop_span`).

Two morphisms are *defined* as `Classical.choose` of a uniqueness statement whose proof is
not yet formalised: the product of supports
`AlgebraicGeometry.Etale.supportedProduct` and the restriction of supports along a smooth
morphism `AlgebraicGeometry.Etale.supportedRestriction`. Both are lifts through the counit
`Ri_! Ri^! L ⟶ L` of a morphism whose source is supported on `Z`; the lift exists by the
supported localization triangle and is unique because there are no morphisms from an object
supported on `Z` to one pushed forward from the open complement
(`AlgebraicGeometry.Etale.subsingleton_hom_shift_rightDerivedLowerShriek_rightDerivedLowerStar`).

The cup product is stated for classes whose degree shift is carried by the coefficients,
`Λ_U ⟶ Ri_! Ri^! (M[a])`: the compatibility of the derived tensor product with shifts is not
yet available, and a class of degree `a` with coefficients `M` becomes one of this form through
the shift compatibility of `Ri_!` and `Ri^!`
(`AlgebraicGeometry.Etale.commShiftRightDerivedLowerShriek`). The twists are then combined with
the identification `Λ(m)[2m] ⊗ Λ(m')[2m'] ≅ Λ(m + m')[2(m + m')]` of the Tate twist datum.

## Main definitions

- `AlgebraicGeometry.Etale.kummerClass`: `κ(u) ∈ H¹(X, Λ(1))`.
- `AlgebraicGeometry.Etale.kummerBoundary`: `∂κ(f) ∈ H²_{V(f)}(U, Λ(1))`.
- `AlgebraicGeometry.Etale.supportedProduct`:
  `Ri₁_! Ri₁^! M ⊗ Ri₂_! Ri₂^! N ⟶ Ri_! Ri^! (M ⊗ N)` for `Z = Z₁ ∩ Z₂`.
- `AlgebraicGeometry.Etale.cupWithSupports`: the cup product of classes with supports.
- `AlgebraicGeometry.Etale.supportedRestriction`: restriction of supports along a smooth
  morphism.

## Main statements

- `AlgebraicGeometry.Etale.leftDerivedUpperStar_map_kummerClass`,
  `AlgebraicGeometry.Etale.kummerClass_mul`
- `AlgebraicGeometry.Etale.existsUnique_supportedProduct`
- `AlgebraicGeometry.Etale.existsUnique_supportedRestriction`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

/-- The zero locus of `insert a s` is the intersection of the zero loci of `a` and of `s`. -/
lemma Scheme.zeroLocus_insert {X : Scheme.{u}} {U : X.Opens} (a : Γ(X, U)) (s : Set Γ(X, U)) :
    X.zeroLocus (insert a s) = X.zeroLocus {a} ∩ X.zeroLocus s := by
  ext x
  simp

namespace Scheme.IdealSheafData

/-- The closed subscheme cut out by a set `s` of global sections has the zero locus of `s` as
underlying set. -/
lemma range_subschemeι_ofIdealTop_span {X : Scheme.{u}} (s : Set Γ(X, ⊤)) :
    Set.range (ofIdealTop (Ideal.span s)).subschemeι.base = X.zeroLocus s := by
  simp [range_subschemeι, coe_support_ofIdealTop, Scheme.zeroLocus_span]

end Scheme.IdealSheafData

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [HasTateTwist Λ]

section Kummer

variable {X Y : Scheme.{u}}

/-- The identification `Lf^* Λ_Y(m) ≅ Λ_X(m)` of the Tate twist datum. -/
noncomputable def leftDerivedUpperStarTateObjectIso (f : X ⟶ Y) (m : ℤ) :
    (L((f)^*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ Y m) ≅ tateObject Λ X m :=
  HasTateTwist.leftDerivedUpperStarTwistObjectIso f m

/-- The identification `Lf^* Λ_Y ≅ Λ_X` of the constant complexes, through
`Λ_Y ≅ Λ_Y(0)` and `Lf^* Λ_Y(0) ≅ Λ_X(0)` of the Tate twist datum. -/
noncomputable def leftDerivedUpperStarConstantComplexIso (f : X ⟶ Y) :
    (L((f)^*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ Y) ≅ constantComplex Λ X :=
  (L((f)^*[ModuleCat.{u + 1} Λ])).mapIso (HasTateTwist.twistObjectZeroIso (Λ := Λ) Y).symm ≪≫
    HasTateTwist.leftDerivedUpperStarTwistObjectIso f 0 ≪≫ HasTateTwist.twistObjectZeroIso X

/-- Blueprint `sk-def-purity-conv`: Purity conventions and the rank-one datum

The *Kummer class* `κ(u) ∈ H¹(X, Λ(1)) = Hom(Λ_X, Λ_X(1)[1])` of a unit `u ∈ Γ(X, 𝒪_X)ˣ`,
from the rank-one datum of `AlgebraicGeometry.Etale.HasTateTwist`. In the concrete model,
`Λ(1) = μ_{ℓ^N} ⊗ Λ` with `ℓ^N Λ = 0`, it is the boundary of `u` in the Kummer sequence
`0 → μ_{ℓ^N} → 𝔾_m → 𝔾_m → 0` (`AlgebraicGeometry.Scheme.kummerSequence`), tensored with `Λ`;
for the coordinate `t` of `𝔾_{m,Y}` it is the class `κ(t)` of `sk-def-purity-conv`. -/
noncomputable def kummerClass (u : Γ(X, ⊤)ˣ) :
    constantComplex Λ X ⟶ (tateObject Λ X 1)⟦(1 : ℤ)⟧ :=
  HasTateTwist.kummerClass X u

/-- The Kummer class is natural under pullback: `Lf^* κ(u) = κ(f^* u)`, along the
identifications `Lf^* Λ_Y ≅ Λ_X` and `Lf^* Λ_Y(1) ≅ Λ_X(1)`. -/
theorem leftDerivedUpperStar_map_kummerClass (f : X ⟶ Y) (u : Γ(Y, ⊤)ˣ) :
    (L((f)^*[ModuleCat.{u + 1} Λ])).map (kummerClass Λ u) ≫
        ((L((f)^*[ModuleCat.{u + 1} Λ])).commShiftIso (1 : ℤ)).hom.app (tateObject Λ Y 1) ≫
          (leftDerivedUpperStarTateObjectIso Λ f 1).hom⟦(1 : ℤ)⟧' =
      (leftDerivedUpperStarConstantComplexIso Λ f).hom ≫
        kummerClass Λ (Units.map f.appTop.hom.toMonoidHom u) :=
  HasTateTwist.leftDerivedUpperStar_map_kummerClass f u

/-- The Kummer class is multiplicative: `κ(uv) = κ(u) + κ(v)`. -/
theorem kummerClass_mul (u v : Γ(X, ⊤)ˣ) :
    kummerClass Λ (u * v) = kummerClass Λ u + kummerClass Λ v :=
  HasTateTwist.kummerClass_mul X u v

end Kummer

section Boundary

variable {U : Scheme.{u}} (f : Γ(U, ⊤))

/-- The closed subscheme `V(f)` of `U` cut out by `f` and the basic open `U_f` are
complementary. -/
lemma range_subschemeι_ofIdealTop_span_singleton :
    Set.range (IdealSheafData.ofIdealTop (Ideal.span {f})).subschemeι.base =
      (Set.range (U.basicOpen f).ι.base)ᶜ := by
  rw [IdealSheafData.range_subschemeι_ofIdealTop_span, Scheme.Opens.range_ι,
    Scheme.zeroLocus_singleton]

/-- A global function `f` restricts to a unit on the basic open `U_f = U ∖ V(f)`. -/
noncomputable def basicOpenUnit : Γ(U.basicOpen f, ⊤)ˣ :=
  (Scheme.isUnit_ι_appTop_basicOpen U f).unit

/-- Blueprint `sk-thm-regular`: Purity for regular closed immersions

The *Kummer boundary* `∂κ(f) ∈ H²_{V(f)}(U, Λ(1))` of a global function `f` on `U`. Write
`i : V(f) ⟶ U` for the closed subscheme cut out by `f` and `j : U_f ⟶ U` for its open
complement, on which `f` is a unit. The Kummer class `κ(f|_{U_f}) ∈ H¹(U_f, Λ(1))`, read through
`Lj^* Λ_U ≅ Λ_{U_f}` and `Lj^* Λ_U(1) ≅ Λ_{U_f}(1)`, is adjoint under `Lj^* ⊣ Rj_*` to a class
`Λ_U ⟶ (Rj_* Lj^* Λ_U(1))[1]`, and the boundary
`δ : Rj_* Lj^* Λ_U(1) ⟶ (Ri_! Ri^! Λ_U(1))[1]` of the supported localization triangle
(`AlgebraicGeometry.Etale.supportedLocalizationBoundary`) carries it to

`∂κ(f) : Λ_U ⟶ (Ri_! Ri^! Λ_U(1))[2]`.

The supported term is `Ri_!`, as in the supported localization triangle; for the closed
immersion `i` it is `Ri_*`. -/
noncomputable def kummerBoundary :
    constantComplex Λ U ⟶
      ((R((IdealSheafData.ofIdealTop (Ideal.span {f})).subschemeι)_![ModuleCat.{u + 1} Λ]).obj
        ((R((IdealSheafData.ofIdealTop (Ideal.span {f})).subschemeι)^![ModuleCat.{u + 1} Λ]).obj
          (tateObject Λ U 1)))⟦(2 : ℤ)⟧ :=
  ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (U.basicOpen f).ι).homEquiv _ _
      ((leftDerivedUpperStarConstantComplexIso Λ (U.basicOpen f).ι).hom ≫
        kummerClass Λ (basicOpenUnit f) ≫
          (leftDerivedUpperStarTateObjectIso Λ (U.basicOpen f).ι 1).inv⟦(1 : ℤ)⟧')) ≫
    ((R(((U.basicOpen f).ι)_*[ModuleCat.{u + 1} Λ])).commShiftIso (1 : ℤ)).hom.app _ ≫
      (supportedLocalizationBoundary (ModuleCat.{u + 1} Λ) _ _
        (range_subschemeι_ofIdealTop_span_singleton f) (tateObject Λ U 1))⟦(1 : ℤ)⟧' ≫
        (shiftFunctorAdd' _ (1 : ℤ) 1 2 rfl).inv.app _

end Boundary

section CupProduct

/- The supports machinery is stated for an arbitrary closed symmetric monoidal Grothendieck
abelian coefficient category `A`: it does not involve the coefficient ring. -/
variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {U Z₁ Z₂ Z : Scheme.{u}}

/-- Blueprint `sk-thm-regular`: Purity for regular closed immersions

**Supports on everything.** For a closed immersion `i : Z ⟶ U` that is surjective, every
morphism `φ : K ⟶ L` factors uniquely through the counit `Ri_! Ri^! L ⟶ L`, which is an
isomorphism: the open complement of `Z` is empty, so the supported localization triangle
degenerates. -/
theorem existsUnique_comp_counit_of_range_eq_univ (i : Z ⟶ U) [IsClosedImmersion i]
    (hi : Set.range i.base = Set.univ)
    {K L : DerivedCategory (Sheaf U.smallEtaleTopology A)} (φ : K ⟶ L) :
    ∃! ψ : K ⟶ (R(i)_![A]).obj ((R(i)^![A]).obj L),
      ψ ≫ (rightDerivedUpperShriekAdjunction A i).counit.app L = φ :=
  sorry

/-- The lift `K ⟶ Ri_! Ri^! L` of a morphism `φ : K ⟶ L` along a surjective closed immersion
`i`, through the counit of `Ri_! ⊣ Ri^!`.

It is *defined* as `Classical.choose` of
`AlgebraicGeometry.Etale.existsUnique_comp_counit_of_range_eq_univ`, whose proof is not yet
formalised; uniqueness is what makes the choice canonical. -/
noncomputable def liftCounitOfRangeEqUniv (i : Z ⟶ U) [IsClosedImmersion i]
    (hi : Set.range i.base = Set.univ)
    {K L : DerivedCategory (Sheaf U.smallEtaleTopology A)} (φ : K ⟶ L) :
    K ⟶ (R(i)_![A]).obj ((R(i)^![A]).obj L) :=
  (existsUnique_comp_counit_of_range_eq_univ A i hi φ).exists.choose

/-- Blueprint `sk-thm-regular`: Purity for regular closed immersions

**The product of supports.** Let `i₁ : Z₁ ⟶ U`, `i₂ : Z₂ ⟶ U` and `i : Z ⟶ U` be closed
immersions with `Z = Z₁ ∩ Z₂`. The tensor product of the two counits
`Ri₁_! Ri₁^! M ⊗ Ri₂_! Ri₂^! N ⟶ M ⊗ N` factors uniquely through the counit
`Ri_! Ri^! (M ⊗ N) ⟶ M ⊗ N`.

Its source is supported on `Z₁ ∩ Z₂`, so its composite with the unit
`M ⊗ N ⟶ Rj_* Lj^* (M ⊗ N)` of the open complement `j` of `Z` vanishes and the supported
localization triangle provides the factorisation; it is unique because there are no
morphisms from an object supported on `Z` to `(Rj_* Lj^* (M ⊗ N))[-1]`
(`AlgebraicGeometry.Etale.subsingleton_hom_shift_rightDerivedLowerShriek_rightDerivedLowerStar`
after the projection formula). -/
theorem existsUnique_supportedProduct (i₁ : Z₁ ⟶ U) (i₂ : Z₂ ⟶ U) (i : Z ⟶ U)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion i]
    (h : Set.range i.base = Set.range i₁.base ∩ Set.range i₂.base)
    (M N : DerivedCategory (Sheaf U.smallEtaleTopology A)) :
    ∃! ψ : ((derivedTensor A U).obj ((R(i₁)_![A]).obj ((R(i₁)^![A]).obj M))).obj
        ((R(i₂)_![A]).obj ((R(i₂)^![A]).obj N)) ⟶
          (R(i)_![A]).obj ((R(i)^![A]).obj (((derivedTensor A U).obj M).obj N)),
      ψ ≫ (rightDerivedUpperShriekAdjunction A i).counit.app (((derivedTensor A U).obj M).obj N) =
        ((derivedTensor A U).map ((rightDerivedUpperShriekAdjunction A i₁).counit.app M)).app _ ≫
          ((derivedTensor A U).obj M).map ((rightDerivedUpperShriekAdjunction A i₂).counit.app N) :=
  sorry

/-- The *product of supports* `Ri₁_! Ri₁^! M ⊗ Ri₂_! Ri₂^! N ⟶ Ri_! Ri^! (M ⊗ N)` for closed
immersions with `Z = Z₁ ∩ Z₂`: the unique factorisation of the tensor product of the counits
through the counit of `Ri_! ⊣ Ri^!`.

It is *defined* as `Classical.choose` of
`AlgebraicGeometry.Etale.existsUnique_supportedProduct`, whose proof is not yet formalised;
uniqueness is what makes the choice canonical. -/
noncomputable def supportedProduct (i₁ : Z₁ ⟶ U) (i₂ : Z₂ ⟶ U) (i : Z ⟶ U)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion i]
    (h : Set.range i.base = Set.range i₁.base ∩ Set.range i₂.base)
    (M N : DerivedCategory (Sheaf U.smallEtaleTopology A)) :
    ((derivedTensor A U).obj ((R(i₁)_![A]).obj ((R(i₁)^![A]).obj M))).obj
        ((R(i₂)_![A]).obj ((R(i₂)^![A]).obj N)) ⟶
      (R(i)_![A]).obj ((R(i)^![A]).obj (((derivedTensor A U).obj M).obj N)) :=
  (existsUnique_supportedProduct A i₁ i₂ i h M N).exists.choose

/-- Blueprint `sk-thm-regular`: Purity for regular closed immersions

The *cup product with supports* of classes `α : K ⟶ Ri₁_! Ri₁^! M` supported on `Z₁` and
`β : K ⟶ Ri₂_! Ri₂^! N` supported on `Z₂`, a class supported on `Z = Z₁ ∩ Z₂`:

`α ∪ β : K ⟶ K ⊗ K ⟶ Ri₁_! Ri₁^! M ⊗ Ri₂_! Ri₂^! N ⟶ Ri_! Ri^! (M ⊗ N)`,

where `Δ : K ⟶ K ⊗ K` is a diagonal and the last map is
`AlgebraicGeometry.Etale.supportedProduct`. For cohomology classes `K = Λ_U` is the unit and
`Δ` the inverse of the unitor `Λ_U ⊗ Λ_U ≅ Λ_U` (`AlgebraicGeometry.Etale.constantComplexDiagonal`).
Degrees are carried by the coefficients: a class of degree `a` is a class with coefficients
`M[a]`. -/
noncomputable def cupWithSupports (i₁ : Z₁ ⟶ U) (i₂ : Z₂ ⟶ U) (i : Z ⟶ U)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion i]
    (h : Set.range i.base = Set.range i₁.base ∩ Set.range i₂.base)
    {K M N : DerivedCategory (Sheaf U.smallEtaleTopology A)}
    (Δ : K ⟶ ((derivedTensor A U).obj K).obj K)
    (α : K ⟶ (R(i₁)_![A]).obj ((R(i₁)^![A]).obj M))
    (β : K ⟶ (R(i₂)_![A]).obj ((R(i₂)^![A]).obj N)) :
    K ⟶ (R(i)_![A]).obj ((R(i)^![A]).obj (((derivedTensor A U).obj M).obj N)) :=
  Δ ≫ ((derivedTensor A U).map α).app K ≫ ((derivedTensor A U).obj _).map β ≫
    supportedProduct A i₁ i₂ i h M N

/-- A class `K ⟶ (Ri_! Ri^! L)[n]` of degree `n` with supports, read as a class with
coefficients `L[n]`, `K ⟶ Ri_! Ri^! (L[n])`, through the shift compatibility of `Ri_!` and
`Ri^!`. -/
noncomputable def shiftSupportedClass (i : Z ⟶ U) [IsClosedImmersion i] (n : ℤ)
    {L : DerivedCategory (Sheaf U.smallEtaleTopology (A))}
    (α : 𝟙_ (DerivedCategory (Sheaf U.smallEtaleTopology A)) ⟶
      ((R(i)_![A]).obj ((R(i)^![A]).obj L))⟦n⟧) :
    𝟙_ (DerivedCategory (Sheaf U.smallEtaleTopology A)) ⟶
      (R(i)_![A]).obj ((R(i)^![A]).obj (L⟦n⟧)) :=
  α ≫ ((R(i)_![A]).commShiftIso n).inv.app _ ≫
    (R(i)_![A]).map
      (((R(i)^![A]).commShiftIso n).inv.app L)

end CupProduct

section BoundaryProduct

variable (U : Scheme.{u}) in
/-- The diagonal `Λ_U ⟶ Λ_U ⊗ Λ_U`, the inverse of the identification
`Λ_U ⊗ Λ_U ≅ Λ_U(0) ⊗ Λ_U(0) ≅ Λ_U(0) ≅ Λ_U` of the Tate twist datum. It is the diagonal along
which cohomology classes are multiplied. -/
noncomputable def constantComplexDiagonal :
    constantComplex Λ U ⟶
      ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj (constantComplex Λ U)).obj
        (constantComplex Λ U) :=
  (HasTateTwist.twistObjectZeroIso (Λ := Λ) U).inv ≫ eqToHom (by rw [add_zero]) ≫
    (HasTateTwist.twistObjectAddIso U 0 0).inv ≫
      ((derivedTensor (ModuleCat.{u + 1} Λ) U).map (HasTateTwist.twistObjectZeroIso U).hom).app _ ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj _).map (HasTateTwist.twistObjectZeroIso U).hom

variable {U : Scheme.{u}}

/-- The zero locus of a tuple `f : Fin (n + 1) → Γ(U, ⊤)` is the intersection of the zero
locus of `f 0` and of the zero locus of the remaining entries. -/
lemma range_subschemeι_ofIdealTop_span_range_succ {n : ℕ} (f : Fin (n + 1) → Γ(U, ⊤)) :
    Set.range (IdealSheafData.ofIdealTop (Ideal.span (Set.range f))).subschemeι.base =
      Set.range (IdealSheafData.ofIdealTop (Ideal.span {f 0})).subschemeι.base ∩
        Set.range (IdealSheafData.ofIdealTop
          (Ideal.span (Set.range (Fin.tail f)))).subschemeι.base := by
  simp only [IdealSheafData.range_subschemeι_ofIdealTop_span]
  rw [Fin.range_fin_succ, Scheme.zeroLocus_insert]

/-- The zero locus of the empty tuple is everything. -/
lemma range_subschemeι_ofIdealTop_span_range_zero (f : Fin 0 → Γ(U, ⊤)) :
    Set.range (IdealSheafData.ofIdealTop (Ideal.span (Set.range f))).subschemeι.base =
      Set.univ := by
  rw [IdealSheafData.range_subschemeι_ofIdealTop_span, Set.range_eq_empty,
    Scheme.zeroLocus_empty_eq_univ]

/-- Blueprint `sk-thm-regular`: Purity for regular closed immersions

The *iterated cup product of Kummer boundaries* of a tuple `f = (f₁, …, f_n)` of global
functions on `U`:

`∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_n) ∈ H^{2n}_{V(f)}(U, Λ(n)) = Hom(Λ_U, Ri_! Ri^! (Λ_U(n)[2n]))`,

where `i : V(f) ⟶ U` is the closed subscheme cut out by `f₁, …, f_n`. It is built by recursion
on `n`: the empty product is the unit class `Λ_U ≅ Λ_U(0)` supported everywhere
(`AlgebraicGeometry.Etale.liftCounitOfRangeEqUniv`), and
`∂κ(f₁) ∪ (∂κ(f₂) ∪ ⋯ ∪ ∂κ(f_n))` is the cup product with supports
(`AlgebraicGeometry.Etale.cupWithSupports`) over `V(f₁) ∩ V(f₂, …, f_n) = V(f)`, followed by
`Λ(1)[2] ⊗ Λ(n - 1)[2(n - 1)] ≅ Λ(n)[2n]` of the Tate twist datum. All the classes have even
degree, so no sign is involved. -/
noncomputable def kummerBoundaryProduct : {n : ℕ} → (f : Fin n → Γ(U, ⊤)) →
    constantComplex Λ U ⟶
      (R((IdealSheafData.ofIdealTop
          (Ideal.span (Set.range f))).subschemeι)_![ModuleCat.{u + 1} Λ]).obj
        ((R((IdealSheafData.ofIdealTop
          (Ideal.span (Set.range f))).subschemeι)^![ModuleCat.{u + 1} Λ]).obj
          ((tateObject Λ U n)⟦2 * (n : ℤ)⟧))
  | 0, f => liftCounitOfRangeEqUniv (ModuleCat.{u + 1} Λ) _
      (range_subschemeι_ofIdealTop_span_range_zero f)
      ((HasTateTwist.twistObjectZeroIso (Λ := Λ) U).inv ≫
        (shiftFunctorZero' _ (2 * (0 : ℤ)) (by simp)).inv.app _ ≫ eqToHom rfl)
  | n + 1, f =>
      cupWithSupports (ModuleCat.{u + 1} Λ) _ _ _ (range_subschemeι_ofIdealTop_span_range_succ f)
          (constantComplexDiagonal Λ U)
          (shiftSupportedClass (ModuleCat.{u + 1} Λ) _ (2 * 1)
            (kummerBoundary Λ (f 0) ≫ eqToHom (by rw [mul_one]; rfl)))
          (kummerBoundaryProduct (Fin.tail f)) ≫
        (R(_)_![ModuleCat.{u + 1} Λ]).map ((R(_)^![ModuleCat.{u + 1} Λ]).map
          ((HasTateTwist.shiftTwistObjectAddIso U 1 n).hom ≫
            eqToHom (by rw [show (1 + (n : ℤ)) = ((n + 1 : ℕ) : ℤ) by push_cast; ring]; rfl)))

end BoundaryProduct

section Restriction

variable {U X Z Z' : Scheme.{u}}

/-- Blueprint `sk-thm-regular`: Purity for regular closed immersions

**Restriction of supports along a smooth morphism.** Let `e : U ⟶ X` be smooth, `i : Z ⟶ X`
a closed immersion and `i' : Z' ⟶ U` its base change along `e`. For `L ∈ D(X_ét, Λ)`,
`L' ∈ D(U_ét, Λ)` and `τ : Le^* L ≅ L'`, the composite
`Le^* (Ri_! Ri^! L) ⟶ Le^* L ≅ L'` factors uniquely through the counit
`Ri'_! Ri'^! L' ⟶ L'`: by smooth base change `Le^* Ri_! Ri^! L ≅ Ri'_! Ri'^! Le^* L` is
supported on `Z'`, and there are no morphisms from an object supported on `Z'` to one pushed
forward from its open complement. -/
theorem existsUnique_supportedRestriction (e : U ⟶ X) [Smooth e] (i : Z ⟶ X) (i' : Z' ⟶ U)
    [IsClosedImmersion i] [IsClosedImmersion i'] (g : Z' ⟶ Z) (hg : IsPullback g i' i e)
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L' : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (τ : (L((e)^*[ModuleCat.{u + 1} Λ])).obj L ≅ L') :
    ∃! ψ : (L((e)^*[ModuleCat.{u + 1} Λ])).obj
        ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![ModuleCat.{u + 1} Λ]).obj L)) ⟶
          (R(i')_![ModuleCat.{u + 1} Λ]).obj ((R(i')^![ModuleCat.{u + 1} Λ]).obj L'),
      ψ ≫ (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i').counit.app L' =
        (L((e)^*[ModuleCat.{u + 1} Λ])).map
          ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i).counit.app L) ≫ τ.hom :=
  sorry

/-- The *restriction of supports* `Le^* (Ri_! Ri^! L) ⟶ Ri'_! Ri'^! L'` along a smooth
`e : U ⟶ X`, for the base change `i'` of a closed immersion `i` and an identification
`τ : Le^* L ≅ L'`: the unique factorisation of `Le^* (Ri_! Ri^! L) ⟶ Le^* L ≅ L'` through the
counit of `Ri'_! ⊣ Ri'^!`.

It is *defined* as `Classical.choose` of
`AlgebraicGeometry.Etale.existsUnique_supportedRestriction`, whose proof is not yet
formalised; uniqueness is what makes the choice canonical. -/
noncomputable def supportedRestriction (e : U ⟶ X) [Smooth e] (i : Z ⟶ X) (i' : Z' ⟶ U)
    [IsClosedImmersion i] [IsClosedImmersion i'] (g : Z' ⟶ Z) (hg : IsPullback g i' i e)
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L' : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (τ : (L((e)^*[ModuleCat.{u + 1} Λ])).obj L ≅ L') :
    (L((e)^*[ModuleCat.{u + 1} Λ])).obj
        ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![ModuleCat.{u + 1} Λ]).obj L)) ⟶
      (R(i')_![ModuleCat.{u + 1} Λ]).obj ((R(i')^![ModuleCat.{u + 1} Λ]).obj L') :=
  (existsUnique_supportedRestriction Λ e i i' g hg L L' τ).exists.choose

/-- The restriction of a class `γ : Λ_X ⟶ Ri_! Ri^! L` with supports along a smooth
`e : U ⟶ X`: `Λ_U ≅ Le^* Λ_X ⟶ Le^* (Ri_! Ri^! L) ⟶ Ri'_! Ri'^! L'`, the last map being
`AlgebraicGeometry.Etale.supportedRestriction`. -/
noncomputable def restrictSupportedClass (e : U ⟶ X) [Smooth e] (i : Z ⟶ X) (i' : Z' ⟶ U)
    [IsClosedImmersion i] [IsClosedImmersion i'] (g : Z' ⟶ Z) (hg : IsPullback g i' i e)
    {L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {L' : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (τ : (L((e)^*[ModuleCat.{u + 1} Λ])).obj L ≅ L')
    (γ : constantComplex Λ X ⟶
      (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![ModuleCat.{u + 1} Λ]).obj L)) :
    constantComplex Λ U ⟶
      (R(i')_![ModuleCat.{u + 1} Λ]).obj ((R(i')^![ModuleCat.{u + 1} Λ]).obj L') :=
  (leftDerivedUpperStarConstantComplexIso Λ e).inv ≫
    (L((e)^*[ModuleCat.{u + 1} Λ])).map γ ≫ supportedRestriction Λ e i i' g hg L L' τ

/-- The identification `Le^* (Λ_X(m)[2m]) ≅ Λ_U(m)[2m]`, through the shift compatibility of
`Le^*` and the identification `Le^* Λ_X(m) ≅ Λ_U(m)` of the Tate twist datum. -/
noncomputable def leftDerivedUpperStarTateShiftIso (e : U ⟶ X) (m : ℤ) :
    (L((e)^*[ModuleCat.{u + 1} Λ])).obj ((tateObject Λ X m)⟦2 * m⟧) ≅
      (tateObject Λ U m)⟦2 * m⟧ :=
  ((L((e)^*[ModuleCat.{u + 1} Λ])).commShiftIso (2 * m)).app _ ≪≫
    (shiftFunctor _ (2 * m)).mapIso (leftDerivedUpperStarTateObjectIso Λ e m)

end Restriction

end Etale

end AlgebraicGeometry
