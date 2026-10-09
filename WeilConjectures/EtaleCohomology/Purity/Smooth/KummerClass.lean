/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.Supports

/-!
# Kummer classes and their boundaries

The cohomological constructions out of which the fundamental class of a regular closed
immersion is glued (`sk-thm-regular`):

* the *Kummer class* `κ(u) ∈ H¹(X, Λ(1))` of a unit `u`, the rank-one datum of
  `sk-def-purity-conv`: the boundary of `u` in the Kummer sequence `0 → μ_n → 𝔾ₘ → 𝔾ₘ → 0`
  (`n = ringChar Λ`), with coefficients extended to `Λ`;
* the *Kummer boundary* `∂κ(f) ∈ H²_{V(f)}(U, Λ(1))` of a global function `f`: `f` is a unit
  on the open complement `U ∖ V(f)`, and the boundary of the supported localization triangle
  of `V(f) ⊂ U` carries its Kummer class to a class supported on `V(f)`;
* the iterated cup product with supports `∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_n)`, supported on `V(f₁, …, f_n)`.

A class with supports in `Z`, of degree `n` and coefficients `L`, is a morphism
`Λ_U ⟶ (Ri_! Ri^! L)[n]`, where `i : Z ⟶ U` is the closed immersion; the operations on such
classes are those of `WeilConjectures.SixFunctors.Etale.Derived.Supports`.

## Implementation notes

The Kummer class is constructed without a change-of-coefficients functor on derived
categories: the Kummer sequence is first pulled back along `u : ℤ_X ⟶ 𝔾ₘ`, giving the
extension `0 → μ_n → E_u → ℤ_X → 0` of `ℤ_X` by `μ_n`; extending scalars to `Λ` keeps it short
exact (`ℤ_X` is torsion-free), and `κ(u)` is the connecting morphism of the resulting short
exact sequence of sheaves of `Λ`-modules, precomposed with `Λ_X ⟶ Λ ⊗ ℤ_X`. The construction
needs the exponent of `Λ` to be invertible on `X`, for exactness of the Kummer sequence.

The rank-one normalisation, that the boundary `∂κ(t)` of the coordinate of `𝔸¹_B` is the
fundamental class of the zero section, is the theorem
`AlgebraicGeometry.Etale.isIso_supportedClassMap_kummerBoundary_coord` (`sk-prop-a1`) of
`WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine`.

## Main definitions

- `AlgebraicGeometry.Etale.unitToGmSheaf`: a unit `u` as a map `ℤ_X ⟶ 𝔾ₘ`.
- `AlgebraicGeometry.Etale.kummerExtension`: the pullback of the Kummer sequence along `u`.
- `AlgebraicGeometry.Etale.kummerClass`: `κ(u) ∈ H¹(X, Λ(1))`.
- `AlgebraicGeometry.Etale.kummerBoundary`: `∂κ(f) ∈ H²_{V(f)}(U, Λ(1))`.
- `AlgebraicGeometry.Etale.supportedClassMap`: the adjoint `Λ_Z ⟶ Ri^! L` of a class with
  supports.
- `AlgebraicGeometry.Etale.cupWithSupportsTateObject`: the cup product of classes with supports
  and Tate coefficients.
- `AlgebraicGeometry.Etale.kummerBoundaryProduct`: `∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_n)`.

## Main statements

- `AlgebraicGeometry.Etale.kummerExtensionScalars_shortExact`
- `AlgebraicGeometry.Etale.leftDerivedUpperStar_map_kummerClass`,
  `AlgebraicGeometry.Etale.kummerClass_mul`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

section Kummer

variable {X Y : Scheme.{u}}

variable (X) in
/-- The constant étale sheaf `ℤ_X` of abelian groups on `X`. -/
noncomputable abbrev constantSheafInt : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- A unit `u ∈ Γ(X, 𝒪_X)ˣ` as a morphism of étale sheaves `ℤ_X ⟶ 𝔾ₘ`, `1 ↦ u`: the global
section `u` of `𝔾ₘ`, read through the adjunction between the constant sheaf and the sections
over the final object of `X_ét`. -/
noncomputable def unitToGmSheaf (u : Γ(X, ⊤)ˣ) : constantSheafInt X ⟶ X.gmSheaf :=
  ((constantSheafAdj _ _ terminalIsTerminal).homEquiv _ _).symm
    (AddCommGrpCat.ofHom ((zmultiplesHom _
      (ULift.up (Additive.ofMul (Units.map (⊤_ X.Etale).hom.appTop.hom.toMonoidHom u)) :
        X.gmSheaf.obj.obj (Opposite.op (⊤_ X.Etale)))).comp
      AddEquiv.ulift.toAddMonoidHom))

/-- The *Kummer extension* of a unit `u`: the pullback of the Kummer sequence
`0 → μ_n → 𝔾ₘ → 𝔾ₘ → 0` (`AlgebraicGeometry.Scheme.kummerSequence`) along `u : ℤ_X ⟶ 𝔾ₘ`,

```
0 ──▶ μ_n ──▶ 𝔾ₘ ×_{𝔾ₘ} ℤ_X ──▶ ℤ_X ──▶ 0,
```

the sheaf of `n`-th roots of `u`. Its exactness when `n` is invertible is inherited from that
of the Kummer sequence; it is not part of the definition. -/
noncomputable def kummerExtension (n : ℕ) (u : Γ(X, ⊤)ˣ) :
    ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  ShortComplex.mk
    (pullback.lift (kernel.ι (n • 𝟙 X.gmSheaf)) 0 (by rw [kernel.condition, zero_comp]))
    (pullback.snd (n • 𝟙 X.gmSheaf) (unitToGmSheaf u)) (pullback.lift_snd _ _ _)

/-- The Kummer extension of `u` for `n = ringChar Λ`, with coefficients extended to `Λ`:

```
0 ──▶ Λ ⊗ μ_n = Λ_X(1) ──▶ Λ ⊗ (𝔾ₘ ×_{𝔾ₘ} ℤ_X) ──▶ Λ ⊗ ℤ_X ──▶ 0.
``` -/
noncomputable def kummerExtensionScalars (u : Γ(X, ⊤)ˣ) :
    ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (kummerExtension (ringChar Λ) u).map (sheafExtendScalars Λ X)

/-- The Kummer extension with coefficients in `Λ` is short exact when the exponent of `Λ` is
invertible on `X`: the Kummer extension itself is (a pullback of the Kummer sequence,
`AlgebraicGeometry.Scheme.kummerSequence_shortExact`), and extending scalars preserves its
exactness because the quotient `ℤ_X` is torsion-free, so `Tor₁^ℤ(Λ, ℤ_X) = 0`. -/
theorem kummerExtensionScalars_shortExact [HasInvertibleExponent Λ X] (u : Γ(X, ⊤)ˣ) :
    (kummerExtensionScalars Λ u).ShortExact :=
  sorry

variable (X) in
/-- The map `Λ_X ⟶ Λ ⊗ ℤ_X`, `1 ↦ 1 ⊗ 1`, from the unit of the monoidal structure on étale sheaves
of `Λ`-modules (the sheafified constant presheaf `Λ`). -/
noncomputable def unitToSheafExtendScalars :
    𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⟶
      (sheafExtendScalars Λ X).obj (constantSheafInt X) :=
  (presheafToSheaf _ _).map ((Functor.const _).map (ModuleCat.ofHom
      (LinearMap.toSpanSingleton Λ (TensorProduct ℤ Λ (ULift.{u + 1} ℤ))
        ((1 : Λ) ⊗ₜ[ℤ] (ULift.up 1 : ULift.{u + 1} ℤ))) :
          ModuleCat.of Λ Λ ⟶ (addCommGrpExtendScalars Λ).obj (AddCommGrpCat.of (ULift ℤ))) ≫
    (Functor.constComp _ _ (addCommGrpExtendScalars Λ)).inv ≫
    Functor.whiskerRight (toSheafify _ _) (addCommGrpExtendScalars Λ))

/-- Blueprint `sk-def-purity-conv`: Purity conventions and the rank-one datum

The *Kummer class* `κ(u) ∈ H¹(X, Λ(1)) = Hom(Λ_X, Λ_X(1)[1])` of a unit `u ∈ Γ(X, 𝒪_X)ˣ`: the
image of `u` under the boundary `Γ(X, 𝔾ₘ) ⟶ H¹(X, μ_n)` of the Kummer sequence
`0 → μ_n → 𝔾ₘ → 𝔾ₘ → 0`, `n = ringChar Λ`, with coefficients extended to `Λ`. Concretely it is
the connecting morphism (`CategoryTheory.ShortComplex.ShortExact.singleδ`) of the pullback of
the Kummer sequence along `u : ℤ_X ⟶ 𝔾ₘ`, tensored with `Λ`
(`AlgebraicGeometry.Etale.kummerExtensionScalars`), precomposed with `Λ_X ⟶ Λ ⊗ ℤ_X`.
Equivalently `κ(u)` is the class of the `μ_n`-torsor of `n`-th roots of `u`. For `u = t` the
coordinate of `𝔾_{m,Y}` this is the class `κ(t)` of `sk-def-purity-conv`. -/
noncomputable def kummerClass [HasInvertibleExponent Λ X] (u : Γ(X, ⊤)ˣ) :
    constantComplex Λ X ⟶ (tateObject Λ X 1)⟦(1 : ℤ)⟧ :=
  (unitIsoSingle (ModuleCat.{u + 1} Λ) X).hom ≫
    (DerivedCategory.singleFunctor _ 0).map (unitToSheafExtendScalars Λ X) ≫
      (kummerExtensionScalars_shortExact Λ u).singleδ

/-- The Kummer class is natural under pullback: `Lf^* κ(u) = κ(f^* u)`, along the
identifications `Lf^* Λ_Y ≅ Λ_X` and `Lf^* Λ_Y(1) ≅ Λ_X(1)`:

```
Lf^* Λ_Y ──Lf^* κ(u)──▶ Lf^*(Λ_Y(1)[1]) ≅ (Lf^* Λ_Y(1))[1]
   │ ≅                              │ ≅
   ▼                                ▼
  Λ_X ───────κ(f^* u)──────────▶ Λ_X(1)[1]
``` -/
theorem leftDerivedUpperStar_map_kummerClass [HasInvertibleExponent Λ Y] (f : X ⟶ Y)
    (u : Γ(Y, ⊤)ˣ) :
    haveI : HasInvertibleExponent Λ X := .of_hom f
    (L((f)^*[ModuleCat.{u + 1} Λ])).map (kummerClass Λ u) ≫
        ((L((f)^*[ModuleCat.{u + 1} Λ])).commShiftIso (1 : ℤ)).hom.app (tateObject Λ Y 1) ≫
          (leftDerivedUpperStarTateObjectIso f 1).hom⟦(1 : ℤ)⟧' =
      (leftDerivedUpperStarConstantComplexIso Λ f).hom ≫
        kummerClass Λ (Units.map f.appTop.hom.toMonoidHom u) :=
  sorry

/-- The Kummer class is multiplicative: `κ(uv) = κ(u) + κ(v)`; the Kummer boundary is a group
homomorphism. -/
theorem kummerClass_mul [HasInvertibleExponent Λ X] (u v : Γ(X, ⊤)ˣ) :
    kummerClass Λ (u * v) = kummerClass Λ u + kummerClass Λ v :=
  sorry

end Kummer

section Boundary

variable {U : Scheme.{u}} [HasInvertibleExponent Λ U] (f : Γ(U, ⊤))

/-- The *Kummer boundary* `∂κ(f) ∈ H²_{V(f)}(U, Λ(1))` of a global function `f` on `U`. Write
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
      ((R(U.zeroLocusSubschemeι {f})_![ModuleCat.{u + 1} Λ]).obj
        ((R(U.zeroLocusSubschemeι {f})^![ModuleCat.{u + 1} Λ]).obj (tateObject Λ U 1)))⟦(2 : ℤ)⟧ :=
  haveI : HasInvertibleExponent Λ (U.basicOpen f) := .of_hom (U.basicOpen f).ι
  ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (U.basicOpen f).ι).homEquiv _ _
      ((leftDerivedUpperStarConstantComplexIso Λ (U.basicOpen f).ι).hom ≫
        kummerClass Λ (U.basicOpenUnit f) ≫
          (leftDerivedUpperStarTateObjectIso (U.basicOpen f).ι 1).inv⟦(1 : ℤ)⟧')) ≫
    ((R(((U.basicOpen f).ι)_*[ModuleCat.{u + 1} Λ])).commShiftIso (1 : ℤ)).hom.app _ ≫
      (supportedLocalizationBoundary (ModuleCat.{u + 1} Λ) _ _
        (range_zeroLocusSubschemeι_singleton f) (tateObject Λ U 1))⟦(1 : ℤ)⟧' ≫
        (shiftFunctorAdd' _ (1 : ℤ) 1 2 rfl).inv.app _

end Boundary

section SupportedClassMap

variable {X Z : Scheme.{u}}

/-- The *adjoint* `Λ_Z ⟶ Ri^! L` of a class `γ : Λ_X ⟶ Ri_! Ri^! L` supported on the closed
immersion `i : Z ⟶ X`: the transpose of `γ` along the forget-supports map `Ri_! ⟶ Ri_*`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekTranspose`), read through `Li^* Λ_X ≅ Λ_Z`.
For `γ` the fundamental class of `Z` it is the map `cl_i`, `1 ↦ [Z ⊂ X]`. -/
noncomputable def supportedClassMap (i : Z ⟶ X) [IsClosedImmersion i]
    {L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (γ : constantComplex Λ X ⟶
      (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![ModuleCat.{u + 1} Λ]).obj L)) :
    constantComplex Λ Z ⟶ (R(i)^![ModuleCat.{u + 1} Λ]).obj L :=
  (compactificationConstantComplexIso Λ i).inv ≫
    rightDerivedLowerShriekTranspose (ModuleCat.{u + 1} Λ) i γ

end SupportedClassMap

section BoundaryProduct

variable (U : Scheme.{u}) [HasInvertibleExponent Λ U] in
/-- The diagonal `Λ_U ⟶ Λ_U ⊗ Λ_U` along which cohomology classes are multiplied: the inverse of
the identification `Λ_U ⊗ Λ_U = Λ_U(0) ⊗ Λ_U(0) ≅ Λ_U(0) = Λ_U` of
`AlgebraicGeometry.Etale.tateObjectAddIso`. By the unit law
`AlgebraicGeometry.Etale.tateObjectAddIso_zero_left` it is the inverse of the left unitor; it
is not written as such because the kernel cannot compare the unitor of the monoidal derived
category with the derived tensor product of étale sheaves in reasonable time. -/
noncomputable def constantComplexDiagonal :
    constantComplex Λ U ⟶
      ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj (constantComplex Λ U)).obj
        (constantComplex Λ U) :=
  (tateObjectZeroIso Λ U).inv ≫ eqToHom (by rw [add_zero]) ≫
    (tateObjectAddIso Λ U 0 0).inv ≫
      ((derivedTensor (ModuleCat.{u + 1} Λ) U).map (tateObjectZeroIso Λ U).hom).app _ ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj _).map (tateObjectZeroIso Λ U).hom

variable {U Z₁ Z₂ Z : Scheme.{u}} [HasInvertibleExponent Λ U]

/-- The cup product with supports of classes `α ∈ H^{2m}_{Z₁}(U, Λ(m))` and
`β ∈ H^{2m'}_{Z₂}(U, Λ(m'))`, a class in `H^{2(m + m')}_{Z₁ ∩ Z₂}(U, Λ(m + m'))`: the cup
product `AlgebraicGeometry.Etale.cupWithSupports` along the diagonal `Λ_U ≅ Λ_U ⊗ Λ_U`
(`AlgebraicGeometry.Etale.constantComplexDiagonal`), followed by
`Λ(m)[2m] ⊗ Λ(m')[2m'] ≅ Λ(m + m')[2(m + m')]` (`AlgebraicGeometry.Etale.shiftTateObjectAddIso`).
-/
noncomputable def cupWithSupportsTateObject (i₁ : Z₁ ⟶ U) (i₂ : Z₂ ⟶ U) (i : Z ⟶ U)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion i]
    (h : Set.range i.base = Set.range i₁.base ∩ Set.range i₂.base) {m m' : ℤ}
    (α : constantComplex Λ U ⟶ (R(i₁)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i₁)^![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ U m)⟦2 * m⟧)))
    (β : constantComplex Λ U ⟶ (R(i₂)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i₂)^![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ U m')⟦2 * m'⟧))) :
    constantComplex Λ U ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i)^![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ U (m + m'))⟦2 * (m + m')⟧)) :=
  cupWithSupports (ModuleCat.{u + 1} Λ) i₁ i₂ i h (constantComplexDiagonal Λ U) α β ≫
    (R(i)_![ModuleCat.{u + 1} Λ]).map ((R(i)^![ModuleCat.{u + 1} Λ]).map
      (shiftTateObjectAddIso Λ U m m').hom)

/-- The *iterated cup product of Kummer boundaries* of a tuple `f = (f₁, …, f_n)` of global
functions on `U`:

`∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_n) ∈ H^{2n}_{V(f)}(U, Λ(n)) = Hom(Λ_U, Ri_! Ri^! (Λ_U(n)[2n]))`,

where `i : V(f) ⟶ U` is the closed subscheme cut out by `f₁, …, f_n`. It is built by recursion
on `n`: the empty product is the unit class `Λ_U ≅ Λ_U(0)` supported everywhere
(`AlgebraicGeometry.Etale.liftCounitOfRangeEqUniv`), and
`∂κ(f₁) ∪ (∂κ(f₂) ∪ ⋯ ∪ ∂κ(f_n))` is the cup product with supports
(`AlgebraicGeometry.Etale.cupWithSupportsTateObject`) over `V(f₁) ∩ V(f₂, …, f_n) = V(f)`. All
the classes have even degree, so no sign is involved. -/
noncomputable def kummerBoundaryProduct : {n : ℕ} → (f : Fin n → Γ(U, ⊤)) →
    constantComplex Λ U ⟶
      (R(U.zeroLocusSubschemeι (Set.range f))_![ModuleCat.{u + 1} Λ]).obj
        ((R(U.zeroLocusSubschemeι (Set.range f))^![ModuleCat.{u + 1} Λ]).obj
          ((tateObject Λ U n)⟦2 * (n : ℤ)⟧))
  | 0, f => liftCounitOfRangeEqUniv (ModuleCat.{u + 1} Λ) _
      (by rw [Set.range_eq_empty f, range_zeroLocusSubschemeι_empty])
      ((tateObjectZeroIso Λ U).inv ≫
        (shiftFunctorZero' _ (2 * (0 : ℤ)) (by simp)).inv.app _)
  | n + 1, f =>
      cupWithSupportsTateObject Λ (U.zeroLocusSubschemeι {f 0})
          (U.zeroLocusSubschemeι (Set.range (Fin.tail f))) (U.zeroLocusSubschemeι (Set.range f))
          (by rw [Fin.range_fin_succ, range_zeroLocusSubschemeι_insert]) (m := 1)
          (shiftSupportedClass (ModuleCat.{u + 1} Λ) _ 2 (kummerBoundary Λ (f 0)))
          (kummerBoundaryProduct (Fin.tail f)) ≫
        eqToHom (by rw [Nat.cast_succ, add_comm (1 : ℤ)])

end BoundaryProduct

end Etale

end AlgebraicGeometry
