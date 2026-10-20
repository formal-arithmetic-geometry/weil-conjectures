/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Paper.IntegralHeartLocalModel
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Sheaf.Paper.CompletedConstantSheafReduction
import Sheaf.Paper.ConstantModuleSectionProperties
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Sheaf.Algebra.Homology.RingedSiteBoundedFreeRHomModel
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Paper.DerivedNakayamaResolution

/-!
# Duals of integral constructible sheaves on a stratum

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-int-integral-heart,
`sk-lem-int-integral-heart-dualizable.md`; Stacks Project, Tags 08JJ and 0FPU
(blueprint: det-lem-int-integral-heart-dualizable).

The coefficient ring and scalar realization are exactly those of IntegralHeartLocalModel.
In particular, coefficients are continuous completed coefficients, not the constant DVR.
The small presentation of the finite extension keeps its universe independent of the site.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
  [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]

/-- Restrict the sheaf to a stratum and place it in degree zero. This is only an
abbreviation for the recorded inverse image and single-complex functors.
Source: blueprint integral-heart-dualizable, notation C restricted to S
(blueprint: det-lem-int-integral-heart-dualizable). -/
abbrev integralHeartStratumComplex {X S : Scheme.{u}} (f : S ⟶ X)
    (C : SmallAdicCompletion.Modules ℓ E X) : integralHeartDerivedCategory.{u} ℓ E S :=
  (DerivedCategory.singleFunctor _ 0).obj
    ((CondensedRing.upperStar (SmallAdicCompletion.Coefficients.integerRing ℓ E) f).obj C)

/-- Local duality, the two Tor bounds, and the residue-sheaf example. The module N is
chosen separately on each chart; no freeness or torsion-freeness of N is assumed.
`ExactPairing K D` includes evaluation D tensor K to the unit, coevaluation from the
unit to K tensor D, and both triangle identities. The displayed dual is the recorded
relative derived internal Hom into the completed coefficient unit.

Source: blueprint main-20261015, integral-heart-dualizable; Stacks 08JJ and 0FPU
(blueprint: det-lem-int-integral-heart-dualizable).

Proof, following the ten DAG steps:
1. The coefficient DVR is a PID and Noetherian. A finite module N has a presentation
A^b onto N with finitely generated torsion-free kernel. The kernel is finite free by
lem-sc-dvr-fg-torsionfree-free, giving 0 -> A^a -> A^b -> N -> 0 on each chart.
2. The integral-limit theorem identifies R with the limit of the constant finite
quotients. CompletedConstantSheafReduction makes R flat over the constant A; the
constant-module exactness theorem then turns this into the two-term finite free
resolution P=[R^a -> R^b] in degrees -1,0 of the restricted sheaf.
3. Exact slice restriction preserves cohomology and quasi-isomorphisms. Derived tensor
pullback and internal-Hom restriction commute with this restriction. Isomorphisms and
cohomology vanishing are detected on the cover using sheaf local isomorphisms and the
unbounded-derived cohomology criterion. No equality of derived maps is detected locally.
4. Derived-Hom currying and the global-sections/Hom identification give the standard
closed adjunction. Its evaluation e:D tensor K -> R is the transpose of id_D and
restricts to the same canonical evaluation on every chart.
5. The bounded-free Hom model represents D by Hom(P,R), namely
[R^b -> R^a] in degrees 0,1 with differential minus the transpose of the matrix.
Negating degree one gives the positive-transpose convention. Both complexes are K-flat
by the bounded-above-flat theorem.
6. For every module sheaf G, tensor with P and with its dual computes the derived
tensors. Their term supports give [-1,0] and [0,1]. Restriction and local vanishing
give the same bounds globally, without any restriction on the test sheaf G.
7. Define alpha:K tensor D -> RHom(K,K) by transposing id_K tensor e. On a chart it
is the finite-free evaluation comparison. Its inverse sends a map h to the finite sum
of h(e_j) tensor e_j^*. These formulas commute with the minus-transpose differential,
including rank zero. Thus alpha is locally, and hence globally, invertible.
8. Transpose id_K to u:R -> RHom(K,K) and put eta=alpha inverse composed with u.
Adjunction naturality gives (id_K tensor e)(eta tensor id_K)=id_K, the first triangle.
9. For g=(e tensor id_D)(id_D tensor eta), tensor interchange gives
 e(g tensor id_K)=e(id_D tensor id_K) using the first triangle. The injective adjunction
bijection Hom(D,RHom(K,R)) to Hom(D tensor K,R) implies g=id_D, the second triangle.
10. At residue level one the coefficient resolution is 0 -> R --pi--> R -> R/pi -> 0.
Its dual is [R --(-pi)--> R] in degrees 0,1. The differential is injective with cokernel
R/pi, so the quotient map is a quasi-isomorphism to (R/pi)[-1], in degree one.
The residue object below is the existing positive-level-zero finiteModule, i.e. n=1;
changing the chosen uniformizer by a unit leaves this quotient unchanged. -/
theorem integralHeartDualizable
    (X : Scheme.{u}) (C : SmallAdicCompletion.Modules ℓ E X)
    (_hC : IsConstantModelConstructible (SmallAdicCompletion.Coefficients.integerRing ℓ E) X C)
    (s : Scheme.Stratification X) (a : Fin s.n)
    (_hmodel : ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage (s.domain a),
      ∀ i : 𝒰.I₀,
        ∃ N : ModuleCat.{u + 1} (integralHeartScalars.{u} ℓ E),
          Module.Finite (integralHeartScalars.{u} ℓ E) N ∧
          Nonempty ((CondensedRing.upperStar (SmallAdicCompletion.Coefficients.integerRing ℓ E)
              (𝒰.f i ≫ s.immersion a)).obj C ≅
            (integralHeartRealization.{u} ℓ E (𝒰.X i)).obj N)) :
    Nonempty (ExactPairing (integralHeartStratumComplex ℓ E (s.immersion a) C)
      (((CondensedRing.derivedHom (SmallAdicCompletion.Coefficients.integerRing ℓ E)
        (s.domain a)).obj (op (integralHeartStratumComplex ℓ E (s.immersion a) C))).obj
          (𝟙_ (integralHeartDerivedCategory.{u} ℓ E (s.domain a))))) ∧
    DerivedCategory.torAmplitudeIn _ (-1) 0
      (integralHeartStratumComplex ℓ E (s.immersion a) C) ∧
    DerivedCategory.torAmplitudeIn _ 0 1
      (((CondensedRing.derivedHom (SmallAdicCompletion.Coefficients.integerRing ℓ E)
        (s.domain a)).obj (op (integralHeartStratumComplex ℓ E (s.immersion a) C))).obj
          (𝟙_ (integralHeartDerivedCategory.{u} ℓ E (s.domain a)))) ∧
    Nonempty
      ((((CondensedRing.derivedHom (SmallAdicCompletion.Coefficients.integerRing ℓ E)
          (s.domain a)).obj (op ((DerivedCategory.singleFunctor _ 0).obj
            (SmallAdicCompletion.finiteModule ℓ E (s.domain a) 0)))).obj
              (𝟙_ (integralHeartDerivedCategory.{u} ℓ E (s.domain a)))) ≅
        ((DerivedCategory.singleFunctor _ 0).obj
          (SmallAdicCompletion.finiteModule ℓ E (s.domain a) 0))⟦(-1 : ℤ)⟧) := by
  sorry

end AlgebraicGeometry.ProEtale
