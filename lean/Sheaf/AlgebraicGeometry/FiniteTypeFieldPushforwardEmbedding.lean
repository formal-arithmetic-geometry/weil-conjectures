/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.ConstructibleSheaf.FinitePushforward
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.ConstructibleSheaf.Pullback
import Sheaf.AlgebraicGeometry.ConstructibleFieldFiniteSeparableConstant
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.AlgebraicGeometry.Properties
import WeilConjectures.AlgebraicGeometry.WeilPbcNormalizationInResidueFieldExtension
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import Sheaf.AlgebraicGeometry.NormalGenericConstant
import Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear
import Sheaf.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.SixFunctors.Finite.Stalk
import Sheaf.AlgebraicGeometry.ConstructibleFiniteSelection

/-!
# Finite-pushforward embeddings over a field

Source: smooth purity blueprint, unit `sk-prop-sf-cbc`, order 1607;
Stacks Project, Tag 09Z6 (3), finite-type specialization
(blueprint: lem-fin-finite-type-pushforward-embedding).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- A constructible Z/N-module sheaf on a finite-type scheme over a field embeds into
finitely many finite pushforwards of constant finite Z/N-modules. The additive groups
of these modules are abelian and killed by N. The lift only places coefficients in the
universe of the recorded constructibility predicate; `NeZero N` expresses finiteness
of Z/N. The empty family is allowed.

Source: smooth purity blueprint, `sk-prop-sf-cbc`, order 1607; Stacks Tag 09Z6 (3)
(blueprint: lem-fin-finite-type-pushforward-embedding).

Proof:
1. A field spectrum is locally Noetherian. Local finite type and quasi-compactness
   make X Noetherian, hence quasi-separated; no separatedness is required.
2. For each x, pull F back to its residue field and trivialize after a finite separable
   extension K, with finite module value M. This uses constructible pullback and
   `lem-weil-pbc-constructible-field-finite-separable-constant`.
3. Give the closure of x its reduced structure and normalize it in K. It is integral
   and finite type over the field. Finiteness of normalization in this finite field
   extension gives a finite map h : Y → X with Y normal integral Noetherian and
   generic inclusion e : Spec K → Y.
4. By `lem-fin-normal-generic-constant`, the constant M on Y is e_* of constant M
   on Spec K. This isomorphism is linear by naturality in M. The two module
   adjunctions, with inverse-image composition, give a linear map F → h_* M.
5. Pulling the adjoint h^* F → M back along e is an isomorphism: the counit composed
   with the pullback of the constant-unit map is the constant-pullback isomorphism,
   and the corresponding counit equation for the trivialization gives that isomorphism.
6. Lift any geometric point over x through Spec K to Y. Composing the stalk map
   of F → h_* M with germ restriction to this lift gives the isomorphism of step 5,
   by the unit-germ identity. Thus the original stalk map is injective.
7. Carry this out for each x and forget module actions. Constructible Noetherian
   finite selection gives a finite subfamily whose sum is injective on all stalks.
   All component maps are linear, so its finite-sum map is linear and mono in module
   sheaves as well. Each h is finite and each M finite abelian killed by N.
   For empty X or zero F the empty biproduct suffices.
-/
theorem exists_mono_finite_pushforward_of_finiteType_field
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    (N : ℕ) [NeZero N]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N))))
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F) :
    ∃ (n : ℕ) (Y : Fin n → Scheme.{u}) (h : ∀ i : Fin n, Y i ⟶ X),
      (∀ i : Fin n, IsFinite (h i)) ∧
      ∃ (M : Fin n → ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N))),
        (∀ i : Fin n, Finite (M i)) ∧
        ∃ (φ : F ⟶ ⨁ fun i : Fin n ↦
          (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N))) (h i)).obj
            ((constantSheaf (Y i).smallEtaleTopology
              (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N)))).obj (M i))), Mono φ := by
  sorry

end AlgebraicGeometry.Etale
