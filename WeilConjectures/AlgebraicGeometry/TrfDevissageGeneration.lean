/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TraceFormulaCoefficientConventions
public import WeilConjectures.SixFunctors.FlatModel

/-!
# Constructible devissage and the need for lisse coefficients

Source: Weil conjectures blueprint, `sec-six-functors/sk-lem-sf-ctf-generation/`
`lem-trf-devissage-generation.md`, statement and Steps 0--3
(blueprint: lem-trf-devissage-generation).

The lisse-flat generator family is the published `sfProEtaleClosureGenerators`.
Closed direct image is exact, so its sheaf-level formula in degree zero represents
`Rg_*j_!L`. The second clause of the statement is an existential obstruction to replacing
all such L by the constant rank-one coefficient sheaf; it is not a claim for every X.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

/-- The constant-coefficient subfamily in the final sentence of the statement.
The actual stratum immersion factors through its scheme-theoretic closure, and the
coefficient sheaf is the sheafification of the constant regular module A. The canonical
intrinsic realization retains its scalar action. Closed direct image is exact, so this
sheaf in degree zero is also `Rg_*j_!A_U`.
Source: blueprint `lem-trf-devissage-generation`, statement and Step 3
(blueprint: lem-trf-devissage-generation). -/
def trfConstantClosureGenerators (X : Scheme.{u}) (A : Type u) [CommRing A] [Finite A] :
    ObjectProperty (proEtaleDerivedCategory X A) :=
  fun K ↦ ∃ (str : Stratification X) (i : Fin str.n)
    (j : str.domain i ⟶ (str.immersion i).image) (_ : IsOpenImmersion j),
    j ≫ (str.immersion i).imageι = str.immersion i ∧
    Nonempty (K ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj
      ((sfIntrinsicModuleEquivalence X A).functor.obj
        ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
          (str.immersion i).imageι).obj
          ((ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).obj
            ((constantSheaf (ProEt.topology (str.domain i))
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
                (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)))))))

/-- Bounded constructible complexes of finite Tor amplitude are exactly the ambient thick
closure of the lisse flat locally closed extension generators. `T` supplies the coefficient
conventions; X is any separated finite-type scheme over its algebraic closure k.
Source: blueprint `lem-trf-devissage-generation`, statement and Steps 0--2
(blueprint: lem-trf-devissage-generation).

The existing `proEtaleThickGeneration_eq` proves generation with the same closure
family, including its scheme-theoretic closure factorization. To apply it, the coefficient
ring is finite by `Padic.finite_coefficientExtensionRing` and is annihilated by a positive
power of l: the spectral absolute value puts l in the maximal ideal, so l^n belongs to
its nth power, which is the coefficient quotient ideal. Finally a finite subset of the
integers is bounded above and below, and every integer interval is finite. This identifies
the finite support formulation of bounded cohomology with the interval formulation in
`proEtaleThickGeneration_eq`. -/
theorem trf_devissage_generation (T : WeilConjectures.TraceFormulaCoefficientConventions.{u})
    (X : Scheme.{u}) (aX : X ⟶ Spec (.of T.datum.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX] :
    WeilConjectures.finiteTorConstructible T.coefficients.l T.coefficientField T.level
      T.level_pos X =
    (@sfProEtaleClosureGenerators X T.coefficientRing inferInstance
      (Padic.finite_coefficientExtensionRing T.coefficients.l T.coefficientField
        T.level T.level_pos)).triangEnvelope := by
  sorry

/-- Constant rank-one coefficients do not generate in general: there is a separated
finite-type X with admissible coefficients and a ctf complex outside their thick closure.
Source: blueprint `lem-trf-devissage-generation`, final sentence and Step 3
(blueprint: lem-trf-devissage-generation).

Proof: use the coefficient datum with base field the algebraic closure of F_5,
ell=3, the base coefficient extension, and level one. The coefficient ideal is
maximal, so its quotient is nonzero of characteristic three. The punctured line is
an open subscheme of the affine line and hence has a separated finite-type structure
map. The quadratic cover and its geometric point with a two-cycle give an exact
module fibre functor F, a natural endomorphism t, and a flat lisse generator L.
The endomorphism vanishes on the constant stratum generators but is not nilpotent
on F(L). Nilpotence on each cohomology fibre defines a thick subcategory: powers
intertwine with all maps, and exponents add in extensions. This subcategory contains
the constant generators, so contains their thick envelope. Degree-zero homology of
L recovers L, contradicting nonnilpotence if L belonged to that envelope. The already
proved generation equality puts L in the finite-Tor constructible category. The
separate geometric fibre lemma supplies precisely the local-model and monodromy
calculation; the closure, coefficient, and explicit cover arguments are proved here. -/
theorem exists_trf_constant_coefficients_not_generating :
    ∃ (T : WeilConjectures.TraceFormulaCoefficientConventions.{u})
      (X : Scheme.{u}) (aX : X ⟶ Spec (.of T.datum.k)),
      LocallyOfFiniteType aX ∧ QuasiCompact aX ∧ IsSeparated aX ∧
      ∃ K : proEtaleDerivedCategory X T.coefficientRing,
        WeilConjectures.finiteTorConstructible T.coefficients.l T.coefficientField
          T.level T.level_pos X K ∧
        ¬ (@trfConstantClosureGenerators X T.coefficientRing inferInstance
          (Padic.finite_coefficientExtensionRing T.coefficients.l T.coefficientField
            T.level T.level_pos)).triangEnvelope K := by
  sorry

end AlgebraicGeometry
