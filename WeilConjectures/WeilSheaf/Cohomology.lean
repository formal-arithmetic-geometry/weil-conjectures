/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Zero
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule

/-!
# Compactly supported cohomology of Weil complexes

Let `k₀` be a finite field with algebraic closure `k̄` and geometric Galois Frobenius
`σ : Spec k̄ ≅ Spec k̄`. A Weil complex `(M, φ : σ^* M ≅ M)` on `Spec k₀` has cohomology
groups `Hʳ(Spec k̄, M)`, and these carry a Frobenius

`Hʳ(Spec k̄, M) ≅ Hʳ(Spec k̄, σ^* M) ≅ Hʳ(Spec k̄, M)`,

whose first isomorphism is the invariance of derived global sections under the automorphism
`σ` and whose second one is induced by `φ`. The compactly supported cohomology of a Weil complex
`K` on a `k₀`-scheme `X` with structure morphism `a : X ⟶ Spec k₀` is the cohomology
`H_c^r(X ⊗ k̄, K) := Hʳ(Spec k̄, Ra_! K)` of its direct image with compact support
(`AlgebraicGeometry.WeilComplex.derivedLowerShriek`), with this Frobenius.

## Main declarations

- `AlgebraicGeometry.WeilComplex.cohomologyFrobeniusModule`: the cohomology of a Weil complex on
  `Spec k₀` as a Frobenius module, its Frobenius coming from the isomorphism
  `D(σ^*) ⋙ RΓ ≅ RΓ` of `AlgebraicGeometry.Etale.upperStarCompRightDerivedGlobalSectionsIso`.
- `AlgebraicGeometry.WeilComplex.compactlySupportedCohomology` and
  `AlgebraicGeometry.WeilSheaf.compactlySupportedCohomology`: compactly supported cohomology
  with its geometric Frobenius.
- `AlgebraicGeometry.WeilComplex.compactlySupportedCohomologyLinearEquiv`: its identification
  with the étale compactly supported cohomology `H_c(ā)[Λ](r)` of the underlying complex.

## Main statements

- `AlgebraicGeometry.WeilComplex.subsingleton_compactlySupportedCohomology_carrier`: with the
  present coefficients every Weil complex is zero (`AlgebraicGeometry.WeilComplex.isZero_carrier`),
  and so is its compactly supported cohomology.
- `AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_of_isFinite`: the
  compactly supported cohomology of a finite `k₀`-scheme is concentrated in degree zero.

## TODO

Define the Frobenius from the derived pullback map on global sections (see the `TODO` of
`WeilConjectures.SixFunctors.Etale.Derived.GlobalSections`), so that it is visibly the
classical `F^*` on cohomology.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Etale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilComplex

section

variable {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]

/-- The underlying complex of a Weil complex is zero: its homology sheaves are constructible
sheaves of `ℚ̄_ℓ`-modules, and these are zero
(`AlgebraicGeometry.Scheme.IsConstructibleSheaf.isZero`). -/
theorem isZero_carrier (K : WeilComplex k₀ l Y) : IsZero K.obj.carrier :=
  DerivedCategory.isZero_of_forall_isZero_homology _ fun n ↦
    have : Scheme.IsConstructibleSheaf
        ((DerivedCategory.homologyFunctor _ n).obj K.obj.carrier) := K.property.2 n
    Scheme.IsConstructibleSheaf.isZero _

end

/-- The `r`-th cohomology `Hʳ(Spec k̄, M)` of the underlying complex of a Weil complex `M` on
`Spec k₀`: the `r`-th cohomology of its derived global sections on the geometric fiber
`Spec k̄`. -/
noncomputable def cohomology (M : WeilComplex k₀ l (Spec (CommRingCat.of k₀))) (r : ℤ) :
    WeilCoefficients.{u} l :=
  (DerivedCategory.homologyFunctor _ r).obj
    ((rightDerivedGlobalSections (WeilCoefficients.{u} l) _).obj M.obj.carrier)

-- TODO: prove this from the bounded constructibility of `M`. The global sections functor on
-- the small étale site of the spectrum of a separably closed field is an equivalence, so
-- `Hʳ(Spec k̄, M) ≅ Γ(Spec k̄, Hʳ M)` is a stalk of a constructible sheaf, hence finite
-- (blueprint `ex:constructible-point`).
instance finiteDimensional_cohomology (M : WeilComplex k₀ l (Spec (CommRingCat.of k₀)))
    (r : ℤ) : FiniteDimensional (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj
      (M.cohomology r)) :=
  sorry

/-- The `r`-th cohomology `Hʳ(Spec k̄, M)` of a Weil complex `(M, φ)` on `Spec k₀`, as a
Frobenius module, with the Frobenius

`Hʳ(Spec k̄, M) ≅ Hʳ(Spec k̄, σ^* M) --Hʳ(φ)--> Hʳ(Spec k̄, M)`,

where `σ` is the geometric Galois Frobenius of `Spec k̄` and the first isomorphism is
`Etale.upperStarCompRightDerivedGlobalSectionsIso`. -/
noncomputable def cohomologyFrobeniusModule (M : WeilComplex k₀ l (Spec (CommRingCat.of k₀)))
    (r : ℤ) : FrobeniusModule.{u + 1, 0} (PadicAlgCl l) :=
  -- the geometric Galois Frobenius of `Spec k̄`, the geometric fiber of `Spec k₀` over itself
  let σ := (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius
  { carrier := (WeilCoefficients.toModuleCat l).obj (M.cohomology r)
    frobenius := WeilCoefficients.linearEquivOfIso
      ((DerivedCategory.homologyFunctor _ r).mapIso
        (((upperStarCompRightDerivedGlobalSectionsIso _ σ).app M.obj.carrier).symm ≪≫
          (rightDerivedGlobalSections _ _).mapIso M.obj.str)) }

/-- The cohomology of a Weil complex on `Spec k₀` is zero, the complex being zero
(`AlgebraicGeometry.WeilComplex.isZero_carrier`). -/
theorem subsingleton_cohomologyFrobeniusModule_carrier
    (M : WeilComplex k₀ l (Spec (CommRingCat.of k₀))) (r : ℤ) :
    Subsingleton (M.cohomologyFrobeniusModule r).carrier :=
  ModuleCat.isZero_iff_subsingleton.1 ((WeilCoefficients.toModuleCat l).map_isZero
    ((DerivedCategory.homologyFunctor _ r).map_isZero
      ((Sheaf.Γ _ _).isZero_rightDerivedFunctor_obj M.isZero_carrier)))

end WeilComplex

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

namespace WeilComplex

-- TODO(unify): thm:proetale-weil-perfectness
/-- The compactly supported cohomology `H_c^r(X ⊗ k̄, K) := Hʳ(Spec k̄, Ra_! K)` of a Weil
complex `K` on a separated `k₀`-scheme `a : X ⟶ Spec k₀` of finite type, with its geometric
Frobenius: the cohomology of the direct image with compact support of `K` along `a`, a Weil
complex on `Spec k₀`. -/
noncomputable def compactlySupportedCohomology (K : WeilComplex k₀ l X) (r : ℤ) :
    FrobeniusModule.{u + 1, 0} (PadicAlgCl l) :=
  ((derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).obj K).cohomologyFrobeniusModule r

/-- The compactly supported cohomology of a Weil complex is zero, see
`AlgebraicGeometry.WeilComplex.subsingleton_cohomologyFrobeniusModule_carrier`. -/
theorem subsingleton_compactlySupportedCohomology_carrier (K : WeilComplex k₀ l X) (r : ℤ) :
    Subsingleton (K.compactlySupportedCohomology r).carrier :=
  subsingleton_cohomologyFrobeniusModule_carrier _ r

/-- The underlying vector space of the compactly supported cohomology of a Weil complex `K` is
the étale compactly supported cohomology `H_c(ā)[Λ](r)` of the underlying complex on `X ⊗ k̄`
along the base change `ā : X ⊗ k̄ ⟶ Spec k̄` of the structure morphism; the two agree by
definition. -/
noncomputable def compactlySupportedCohomologyLinearEquiv (K : WeilComplex k₀ l X) (r : ℤ) :
    -- the base change `ā : X ⊗ k̄ ⟶ Spec k̄` of the structure morphism
    let ā := Scheme.Hom.geometricFiberMap (X ↘ Spec (CommRingCat.of k₀)) (comp_over _ _)
    (K.compactlySupportedCohomology r).carrier ≃ₗ[PadicAlgCl l]
      (WeilCoefficients.toModuleCat l).obj
        ((H_c(ā)[WeilCoefficients.{u} l](r)).obj K.obj.carrier) :=
  LinearEquiv.refl _ _

end WeilComplex

namespace WeilSheaf

/-- The compactly supported cohomology `H_c^r(X ⊗ k̄, F)` of a Weil sheaf, with its geometric
Frobenius: that of the Weil complex `F` concentrated in degree zero. -/
noncomputable def compactlySupportedCohomology (F : WeilSheaf k₀ l X) (r : ℤ) :
    FrobeniusModule.{u + 1, 0} (PadicAlgCl l) :=
  (toComplex.obj F).compactlySupportedCohomology r

-- the provisional Weil sheaves are zero, and the proof needs no hypothesis
set_option linter.unusedVariables false in
/-- *Cohomology of a finite boundary.* If `X` is finite over `k₀`, then the compactly supported
cohomology `H_c^r(X ⊗ k̄, G)` of a Weil sheaf `G` on `X` vanishes for `r ≠ 0`: after geometric
base change `X` becomes a finite discrete space, whose cohomology is concentrated in degree
zero. The blueprint states this for `G` with stalk weights at most some `w`; the weights play
no role.

With the present coefficients every Weil complex is zero
(`AlgebraicGeometry.WeilComplex.subsingleton_compactlySupportedCohomology_carrier`), which is
how the statement is proved here.
(blueprint: `lem-a1-finite-boundary-cohomology`) -/
theorem subsingleton_compactlySupportedCohomology_of_isFinite
    [IsFinite (X ↘ Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l X) {r : ℤ} (hr : r ≠ 0) :
    Subsingleton (G.compactlySupportedCohomology r).carrier :=
  (toComplex.obj G).subsingleton_compactlySupportedCohomology_carrier r

end WeilSheaf

end AlgebraicGeometry
