/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.CategoryTheory.Localization.Linear
public import Mathlib.RingTheory.Flat.TorsionFree
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.SmulCokernel
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.HomologySequenceShortExact

/-!
# The universal coefficient sequences of a reduction modulo a scalar

Let `R` be a commutative ring, `r ∈ R`, and let `C ⟶[r] C ⟶ C' ⟶ C⟦1⟧` be a distinguished
triangle of the derived category `D(R)` whose first map is the multiplication by `r`. For `r`
a nonzerodivisor `C'` is the reduction `C ⊗ᴸ_R R/(r)`, the cone of `r`. The long exact
cohomology sequence of the triangle breaks into the *universal coefficient sequences*

`0 ⟶ Hⁱ(C) ⊗_R R/(r) ⟶ Hⁱ(C') ⟶ Hⁱ⁺¹(C)[r] ⟶ 0`,

where `M[r] = Submodule.torsionBy R M r` is the `r`-torsion of `M`, that is
`Tor₁^R(M, R/(r))` for `r` a nonzerodivisor.

## Main definitions

- `DerivedCategory.universalCoefficientSequence`: the short complex
  `Hⁱ(C) ⊗_R R/(r) ⟶ Hⁱ(C') ⟶ Hⁱ⁺¹(C)[r]`.

## Main statements

- `DerivedCategory.universalCoefficientSequence_shortExact`: it is short exact.
- `DerivedCategory.isIso_universalCoefficientSequence_f`: if `r` is a nonzerodivisor on
  `Hⁱ⁺¹(C)` (for instance if `Hⁱ⁺¹(C)` is projective and `r` a nonzerodivisor of `R`,
  `DerivedCategory.isIso_universalCoefficientSequence_f_of_projective`), then
  `Hⁱ(C) ⊗_R R/(r) ≅ Hⁱ(C')`: the reduction of the cohomology is the cohomology of the reduction.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace DerivedCategory

section Linear

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C] (R : Type*) [Ring R]
  [Linear R C]

/-- The homology functors of homological complexes in an `R`-linear category are `R`-linear. -/
local instance linear_homologicalComplexHomologyFunctor {ι : Type*} (c : ComplexShape ι)
    (i : ι) : (HomologicalComplex.homologyFunctor C c i).Linear R where
  map_smul φ r := ShortComplex.homologyMap_smul _ r

/-- The homology functors of the derived category of an `R`-linear abelian category are
`R`-linear. -/
lemma linear_homologyFunctor' (n : ℤ) : (homologyFunctor C n).Linear R := by
  have : Localization.Lifting Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n) (homologyFunctor C n) :=
    ⟨homologyFunctorFactors C n⟩
  rw [← Localization.functor_linear_iff Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) R
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n) (homologyFunctor C n)]
  infer_instance

/-- The homology functors of the derived category commute with the multiplication by a
scalar. -/
lemma homologyFunctor_map_smul_id (n : ℤ) (X : DerivedCategory C) (r : R) :
    (homologyFunctor C n).map (r • 𝟙 X) = r • 𝟙 ((homologyFunctor C n).obj X) := by
  have := linear_homologyFunctor' R (C := C) n
  rw [Functor.map_smul, Functor.map_id]

end Linear

variable {R : Type u} [CommRing R] [HasDerivedCategory.{u} (ModuleCat.{u} R)]

section UniversalCoefficient

variable {C C' : DerivedCategory (ModuleCat.{u} R)} (r : R) (g : C ⟶ C') (h : C' ⟶ C⟦(1 : ℤ)⟧)
  (hT : Triangle.mk (r • 𝟙 C) g h ∈ distTriang _) (n₀ n₁ : ℤ) (hn : n₀ + 1 = n₁)

/-- The cokernel of the multiplication by `r` on `Hⁿ(C)` is `Hⁿ(C) ⊗_R R/(r)`. -/
noncomputable def cokernelHomologyFunctorMapSmulIdIso (n : ℤ) :
    cokernel ((homologyFunctor (ModuleCat.{u} R) n).map (r • 𝟙 C)) ≅
      ModuleCat.of R ((homologyFunctor (ModuleCat.{u} R) n).obj C ⊗[R]
        (R ⧸ Ideal.span {r})) :=
  cokernelIsoOfEq (homologyFunctor_map_smul_id R n C r) ≪≫ ModuleCat.cokernelSmulIdIso _ r

/-- The kernel of the multiplication by `r` on `Hⁿ(C)` is the `r`-torsion of `Hⁿ(C)`. -/
noncomputable def kernelHomologyFunctorMapSmulIdIso (n : ℤ) :
    kernel ((homologyFunctor (ModuleCat.{u} R) n).map (r • 𝟙 C)) ≅
      ModuleCat.of R (Submodule.torsionBy R ((homologyFunctor (ModuleCat.{u} R) n).obj C) r) :=
  kernelIsoOfEq (homologyFunctor_map_smul_id R n C r) ≪≫ ModuleCat.kernelSmulIdIso _ r

/-- Blueprint `prop-pod-integral-degreewise-form`: Integral degreewise form (the algebraic
input).

The universal coefficient sequence `Hⁿ⁰(C) ⊗_R R/(r) ⟶ Hⁿ⁰(C') ⟶ Hⁿ¹(C)[r]`, `n₀ + 1 = n₁`,
of a distinguished triangle `C ⟶[r] C ⟶ C' ⟶ C⟦1⟧` of `D(R)`: the first map is induced by
`Hⁿ⁰(C ⟶ C')`, the second by the connecting morphism. Here `M[r]` is the `r`-torsion
`Submodule.torsionBy R M r`, which is `Tor₁^R(M, R/(r))` for `r` a nonzerodivisor. -/
noncomputable def universalCoefficientSequence : ShortComplex (ModuleCat.{u} R) :=
  let S := (homologyFunctor (ModuleCat.{u} R) 0).homologySequenceCokernelKernel _ hT n₀ n₁ hn
  ShortComplex.mk (X₂ := (homologyFunctor (ModuleCat.{u} R) n₀).obj C')
    ((cokernelHomologyFunctorMapSmulIdIso r n₀).inv ≫ S.f)
    (S.g ≫ (kernelHomologyFunctorMapSmulIdIso r n₁).hom) (by simp [S.zero])

/-- The universal coefficient sequence is isomorphic to the short complex cut out of the
homology sequence of the triangle. -/
noncomputable def universalCoefficientSequenceIso :
    (homologyFunctor (ModuleCat.{u} R) 0).homologySequenceCokernelKernel _ hT n₀ n₁ hn ≅
      universalCoefficientSequence r g h hT n₀ n₁ hn :=
  ShortComplex.isoMk (cokernelHomologyFunctorMapSmulIdIso r n₀) (Iso.refl _)
    (kernelHomologyFunctorMapSmulIdIso r n₁)
    (by simp [universalCoefficientSequence]) (by simp [universalCoefficientSequence])

/-- Blueprint `prop-pod-integral-degreewise-form`: Integral degreewise form (the algebraic
input).

**The universal coefficient sequences.** For a distinguished triangle `C ⟶[r] C ⟶ C' ⟶ C⟦1⟧`
of `D(R)` whose first map is the multiplication by `r` (for `r` a nonzerodivisor, `C'` is the
reduction `C ⊗ᴸ_R R/(r)`), the sequence

`0 ⟶ Hⁿ⁰(C) ⊗_R R/(r) ⟶ Hⁿ⁰(C') ⟶ Hⁿ¹(C)[r] ⟶ 0`, `n₀ + 1 = n₁`,

is short exact. -/
theorem universalCoefficientSequence_shortExact :
    (universalCoefficientSequence r g h hT n₀ n₁ hn).ShortExact :=
  ShortComplex.shortExact_of_iso (universalCoefficientSequenceIso r g h hT n₀ n₁ hn)
    ((homologyFunctor (ModuleCat.{u} R) 0).homologySequenceCokernelKernel_shortExact _ hT n₀ n₁
      hn)

/-- Blueprint `prop-pod-integral-degreewise-form`: Integral degreewise form (the algebraic
input).

**The cohomology of the reduction is the reduction of the cohomology** when `r` is a
nonzerodivisor on `Hⁿ¹(C)`: the map `Hⁿ⁰(C) ⊗_R R/(r) ⟶ Hⁿ⁰(C')` is an isomorphism. -/
theorem isIso_universalCoefficientSequence_f
    (hreg : IsSMulRegular ((homologyFunctor (ModuleCat.{u} R) n₁).obj C) r) :
    IsIso (universalCoefficientSequence r g h hT n₀ n₁ hn).f := by
  rw [(universalCoefficientSequence_shortExact r g h hT n₀ n₁ hn).isIso_f_iff,
    ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun x y ↦ Subtype.ext ?_⟩
  refine hreg ?_
  rw [(Submodule.mem_torsionBy_iff _ _).1 x.2, (Submodule.mem_torsionBy_iff _ _).1 y.2]

/-- Blueprint `prop-pod-integral-degreewise-form`: Integral degreewise form (the algebraic
input).

If `r` is a nonzerodivisor of `R` and `Hⁿ¹(C)` is projective (for instance finite free), the
map `Hⁿ⁰(C) ⊗_R R/(r) ⟶ Hⁿ⁰(C')` is an isomorphism: the Tor term of the universal coefficient
sequence vanishes. -/
theorem isIso_universalCoefficientSequence_f_of_projective (hr : r ∈ nonZeroDivisors R)
    [Module.Projective R ((homologyFunctor (ModuleCat.{u} R) n₁).obj C)] :
    IsIso (universalCoefficientSequence r g h hT n₀ n₁ hn).f :=
  isIso_universalCoefficientSequence_f r g h hT n₀ n₁ hn
    (Module.Flat.isSMulRegular_of_nonZeroDivisors hr)

end UniversalCoefficient

end DerivedCategory
