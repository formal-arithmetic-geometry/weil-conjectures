/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedTensor
public import WeilConjectures.Algebra.Homology.ChangeOfRingsComplex
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Homology.HomologicalComplex
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlat
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
public import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellation
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellation
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.AlgebraicGeometry.CompleteCoefficientDatum

/-!
# Adic coefficient datum and reduction tower

Source: literature/blueprint/master/blueprint/sec-proper-base-change/
sk-thm-properbasechange/def-weil-pbc-complete-coefficient-datum.md, order 1255
(blueprint: def-weil-pbc-complete-coefficient-datum).

The construction uses one K-flat model with flat terms. Quotient reductions are actual
changed complexes. The ordinary balancing and transition maps are specified uniquely on
local tensor generators; their images under localization are the canonical derived maps.

## Main definitions

- `CompleteCoefficientDatum`: the ring, ideal, torsion, and perfectness conditions.
- `AdicKFlatModel`: one flat-term K-flat representative of an arbitrary derived object.
- `adicReduction`, `adicReductionUnderlying`: the quotient reduction and its scalar restriction.
- `adicTransition`: the localized map induced by the quotient homomorphism.
- `adicNormalization`: the localized scalar-extension balancing isomorphism.

## Main statements

- `adicKFlatModel_exists`: availability of models for every unbounded derived object.
- `adicTransition_id`, `adicTransition_comp`: the transition identities.
- `adicNormalization_cocycle`, `adicNormalization_unit`: normalization coherence.
- `adicReductionUnderlying_tensor`: comparison with the recorded derived tensor product.
-/

@[expose] public section

universe t

open CategoryTheory MonoidalCategory
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme

/-- The constant commutative ring sheaf, before forgetting commutativity.
Source: blueprint order 1255 (blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable abbrev adicConstantRing (X : Scheme.{t}) (A : Type t) [CommRing A] :=
  (constantSheaf (ProEt.topology X) CommRingCat.{t + 1}).obj
    (CommRingCat.of (ULift.{t + 1, t} A))

/-- The underlying constant ring sheaf used by the recorded pro-etale derived category.
Source: blueprint order 1255 (blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable abbrev adicModuleRing (X : Scheme.{t}) (A : Type t) [CommRing A] :=
  (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj (adicConstantRing X A)

end AlgebraicGeometry.Scheme
