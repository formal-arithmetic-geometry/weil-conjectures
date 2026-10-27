/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D7
-/
module

public import Sheaf.Paper.ConcreteProjectionReductionData
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.FiniteTorAmplitudeSites

/-! # Invertibility of the concrete compact-support quotient comparison

Source: Stacks Tag 0GL6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.ConcreteProjectionReduction
open AlgebraicGeometry.ProEtale.OpenScalarTensor

/-- The specified scalar-adjunction comparison is invertible on finite-Tor
constructible inputs. The structure maps of X and Y need not be separated.
Source: Stacks Tag 0GL6, remark-Rf-lower-shriek-change-of-rings.
(blueprint: lem-sf-concrete-support-scalar-isomorphism).

Proof: the ordinary scalar extension of K is bounded constructible: on a bounded
finite-projective local model its tensor with the finite quotient has the same
Tor interval, and constructibility descends along the finite stratification.
Apply finiteCompactSupportScalarComparison to the intrinsic compact-support
presentation and this actual reduced input. Identify ringed constant direct image
with canonical constant direct image by transposing the constant-section structure
map. Identify the two open extensions by the unit-preserving uniqueness isomorphism
of their adjunctions. Exact localization and the right-derived direct-image
comparison give the resulting proper/open presentation isomorphism. The two
restriction-of-scalars squares agree under it: on the open this follows from the
open-unit equations, and on the proper factor from the normalized K-injective
comparison. Transpose this equality under scalar adjunctions. It identifies the
canonical invertible comparison just obtained with PurCompactSupport.comparison.
The two outer scalarIso factors in supportComparison are isomorphisms, so that
specified map is invertible. The construction works for any compactification,
including identity reductions, empty schemes and the zero input. -/
theorem supportComparison_quotient_isIso
    (m : Models.{u}) (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n)
    (X Y : Over (Spec (CommRingCat.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (c : Compactification f.left)
    (K : proEtaleDerivedCategory X.left (Padic.coefficientExtensionRing C.l E n))
    (hK : finiteTorConstructible C.l E n hn X.left K) :
    IsIso (supportComparison m (quotient C.l E hkn) c K) := by
  sorry

end WeilConjectures.ConcreteProjectionReduction
