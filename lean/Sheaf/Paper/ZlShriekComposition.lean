/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Sheaf.Paper.ZlFrobeniusCompactSupportComparison
public import Sheaf.Paper.PbcQbarCategory
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.WeilSheaf.LowerShriekFunctoriality
import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius

/-! # Composition of exceptional direct images, compatibly with Frobenius

Source: blueprint main-20261015, sec-deligne-laumon-general,
sk-l-dl-general-composition/lem-zl-shriek-composition.md and its proof;
prop-functor-package, clause (3)
(blueprint: lem-zl-shriek-composition).

The comparison is on the actual common-stage category. Frobenius compatibility
is stated on completed integral representatives, before raw rationalization and
common-stage descent. It is an equality of the prescribed adjunction mates,
not existence of unspecified Frobenius structures on the output objects.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open PurCompactSupport GeneralAlgebraicallyClosedCoefficients

/-- The natural compact-support compositor commutes with geometric Frobenius.
The three coefficient actions are presentations of the already normalized functors,
not arbitrary maps or an additional hypothesis on input objects. The first equation
fixes the inverse component at (E,K) to [E,alpha_E]. The second is the Frobenius
square on every integral representative, with all three compactifications arbitrary.
Ordinary inverse image along a scheme isomorphism is exact, preserves the actual
Roos completion map, and computes completed inverse image. Thus this square is
precisely Frobenius compatibility for the recorded constructible pullback. Raw
rationalization extends it to every rational arrow, including Weil structures with
no stable integral lattice; common-stage descent gives the Weil-pair assertion.

Source: blueprint main-20261015, lem-zl-shriek-composition, proof;
prop-functor-package, clause (3) (blueprint: lem-zl-shriek-composition).

Proof, following the two steps of the DAG:
1. Base change the given finite-type separated schemes and morphisms to the fixed
closure using lem-pod-separated-finite-type-base-change. On the common-stage
category C_Y of def-weil-algebraically-closed-coefficients, clause (3) of
prop-functor-package gives the natural composition comparison. Equivalently use
the normalized integral, rational and common-stage comparisons of
lem-zl-field-shriek-composition-qcqs. They identify each finite component with the
specified localized integral compositor. Bounded constructibility of the integral
compact-support operation makes the second functor applicable.
2. By lem-fix-weil-operations the canonical composition comparison is equivariant.
On completed representatives this is the displayed square: transpose the proper
and open Frobenius comparisons under their adjunctions and use the natural
pullback-composition comparisons. Mate pasting and the triangle identities show
that the composite comparison agrees with the comparison for the composite.
The projection-normalized realization isomorphisms retain this equality before
localization. Rationalize it and include each coefficient stage. Naturality in
all rational morphisms permits an arbitrary rational Weil isomorphism, without
assuming an invariant lattice. For a Weil pair (K,theta), the equation becomes
beta theta_A = theta_B F_Z^*(beta), exactly the morphism condition of
def-weil-weil-sheaf-complex. Composing with beta inverse proves the inverse is
also a Weil morphism; naturality restricts to the category of fixed pairs. -/
theorem zlShriekComposition
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X₀ Y₀ Z₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom] [IsSeparated Z₀.hom]
    (f₀ : X₀ ⟶ Y₀) (g₀ : Y₀ ⟶ Z₀)
    [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    [IsSeparated g₀.left] [LocallyOfFiniteType g₀.left] [QuasiCompact g₀.left]
    (cf₀ : Compactification f₀.left) (cg₀ : Compactification g₀.left)
    (cfg₀ : Compactification (f₀ ≫ g₀).left)
    (Sf : SfCompactSupportCoefficientAction l D.k (coefficientPrimeUnit l D hl) Ω
      (zlGeometricCompactification D f₀ cf₀))
    (Sg : SfCompactSupportCoefficientAction l D.k (coefficientPrimeUnit l D hl) Ω
      (zlGeometricCompactification D g₀ cg₀))
    (Sfg : SfCompactSupportCoefficientAction l D.k (coefficientPrimeUnit l D hl) Ω
      (zlGeometricCompositeCompactification D f₀ g₀ cfg₀)) :
    (∃ β : Sfg.system.functor ≅ Sf.system.functor ⋙ Sg.system.functor,
      ∀ (L : Padic.FiniteCoefficientFields l Ω)
        (K : Stage l Ω (D.geometricFiber X₀).left L),
        HEq (β.inv.app ⟨L, K⟩)
          ((inclusion (l := l) (Ω := Ω) (Y := (D.geometricFiber Z₀).left) L).map
            ((sfFieldShriekCompositionRational D l hl
              (zlGeometricCompactification D f₀ cf₀)
              (zlGeometricCompactification D g₀ cg₀)
              (zlGeometricCompositeCompactification D f₀ g₀ cfg₀)
              (AlgebraicallyClosedCoefficients.Coefficient l Ω L)).hom.app K))) ∧
    ∀ (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
      (K : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left),
      (zlAmbientFrobenius D l E Z₀).map
          (zlCompletedShriekCompositor D f₀ cf₀ l E hl g₀ cg₀ cfg₀ K).hom ≫
        (zlCompactSupportFrobenius D (f₀ ≫ g₀) cfg₀ l E).hom.app K.obj =
      (zlCompactSupportFrobenius D g₀ cg₀ l E).hom.app
          ((image (completed l E) (zlGeometricCompactification D f₀ cf₀)).obj K.obj) ≫
        (image (completed l E) (zlGeometricCompactification D g₀ cg₀)).map
          ((zlCompactSupportFrobenius D f₀ cf₀ l E).hom.app K.obj) ≫
        (zlCompletedShriekCompositor D f₀ cf₀ l E hl g₀ cg₀ cfg₀
          ⟨(zlAmbientFrobenius D l E X₀).obj K.obj,
            zlAmbientFrobenius_constructible D l E hl X₀ K⟩).hom := by
  sorry

end WeilConjectures
