/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.Paper.QcqsOpenClosedTree
public import Sheaf.Paper.DerivedNakayamaResolution
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Mathlib.Algebra.Homology.Double

/-! # Classical Koszul cohomology along support paths

Source: Stacks Tags 09AF, 09BM, 09BN and 09A6.
(blueprint: lem-sfb-support-pullback-koszul-classical).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Classical scalar Koszul cohomology remains classical along a support path and pullback.
Source: Stacks Tags 09AF, 09BM, 09BN, 09A5 and 09A6.
(blueprint: lem-sfb-support-pullback-koszul-classical).

Proof: induct on the path. The root uses the identity functor. At an open branch, extension
by zero is exact and commutes with comparison inverse image. At a closed branch, the
immersion is qcqs and its open complement is quasi-compact by the split-tree hypotheses.
Its pro-etale direct image is exact; degree zero of direct-image comparison therefore
identifies its action on a classical sheaf with comparison pullback of the etale direct
image. Internal-module operations transport identifies the underlying abelian functors.
All these operations are linear, so they carry the scalar differential to the same scalar
differential, and exactness identifies homology before and after each operation. Finally
module pullback is exact and its comparison square commutes for every morphism v, without
a qcqs assumption on v. Apply this square to each classical cohomology antecedent.
The empty path and empty schemes are included, and no finiteness of I is required.
-/
theorem support_pullback_koszul_classical
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    {X S : Scheme.{u}} {tree : QcqsOpenClosedTree X} (p : tree.Path S)
    (I : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (DerivedNakayama.integerRing ℓ E) S))
    (n : ℕ)
    (hI : ∀ q : ℤ, (comparisonUpperStar Ab.{u + 1} S).essImage
      ((HomologicalComplex.double
        (((DerivedNakayama.scalarOnModules ℓ E S
          ((DerivedNakayama.derived_nakayama_resolution ℓ E).choose ^ n)).app
            I).hom) (c := ComplexShape.up ℤ) (i₀ := -1) (i₁ := 0) (by decide)).homology q))
    {U : Scheme.{u}} (v : U ⟶ X) :
    ∀ q : ℤ, (comparisonUpperStar Ab.{u + 1} U).essImage
      ((HomologicalComplex.double
        (((DerivedNakayama.scalarOnModules ℓ E U
          ((DerivedNakayama.derived_nakayama_resolution ℓ E).choose ^ n)).app
            ((CondensedRing.upperStar (DerivedNakayama.integerRing ℓ E) v).obj
              ((p.extension (DerivedNakayama.integerRing ℓ E)).obj I))).hom)
        (c := ComplexShape.up ℤ) (i₀ := -1) (i₁ := 0)
        (by decide)).homology q) := by sorry

end AlgebraicGeometry.ProEtale
