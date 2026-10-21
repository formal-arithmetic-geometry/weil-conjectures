/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q64
-/
module

public import Sheaf.Paper.GaloisPartitionModules
public import Sheaf.CategoryTheory.LocallyConstantFiniteTypeModules
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Data.ZMod.Basic
import Sheaf.CategoryTheory.Sites.OrientedClosedBaseLocalization
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.AlgebraicGeometry.EtaleInternalHomLocalization
import Sheaf.AlgebraicGeometry.GaloisPartitionExactRefinement
import Sheaf.Paper.GaloisLocalizationUniformBounds

/-!
# Closed/open dévissage for the finite-Tor internal-Hom condition

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé XVII,
Definition 7.6.8 and Lemma 7.6.10, p. 313
(blueprint: lem-per-ctf-hom-localization-devissage).

## Main declarations

- `SatisfiesConditionB`: the three uniform partition, upper-bound and constructibility clauses.
- `ctf_hom_localization_devissage`: gluing this condition from closed and open restrictions.

The partition classes are the existing `Scheme.GaloisPartition.boundedDerived`.
Constructibility uses finitely generated geometric stalks, also for infinite coefficients.
The dualizing hypothesis spells out the canonical evaluation-transpose arrow.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The three clauses of condition (B): one output partition and upper bound for each
input partition, with constructibility preserved for constructible inputs in that class.
Source: ILO XVII, Definition 7.6.8, p. 313
(blueprint: lem-per-ctf-hom-localization-devissage). -/
def SatisfiesConditionB (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) (K : DerivedCategoryModule A X) : Prop :=
  ∀ P : Scheme.GaloisPartition X, ∃ P' : Scheme.GaloisPartition X, ∃ c : ℤ,
    ∀ N : DerivedCategoryModule A X, P.boundedDerived A N →
      P'.boundedDerived A (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj N) ∧
      (N.IsLE 0 → (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj N).IsLE c) ∧
      (DerivedCategory.constructibleHomology (ModuleCat.{u + 1} A) X N →
        DerivedCategory.constructibleHomology (ModuleCat.{u + 1} A) X
          (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj N))

/-- Closed/open dévissage for condition (B).
Source: ILO XVII, Lemma 7.6.10, p. 313
(blueprint: lem-per-ctf-hom-localization-devissage).

Proof:
1. Fix P. The uniform localization bounds of lem-per-galois-localization-uniform-bounds
supply partitions P_Z, P_U for Ri!N and j*N, independent of N in D^b_P, preserving
constructibility. If N is in D^{≤0}, the upper bounds are d_i and 0.
2. Apply the assumed condition (B) for i*K to P_Z. It supplies Q_Z,c_Z for
C_N = RHom(i*K,Ri!N), with constructibility. Apply the upper-bound clause to
(Ri!N)[d_i]; Hom commutes with shifting its second argument
(def-pur-derived-internal-hom), so C_N is in D^{≤c_Z+d_i}.
3. Condition (B) for j*K supplies Q_U,c_U for E_N = RHom(j*K,j*N).
Apply lem-per-galois-localization-uniform-bounds to the fixed Q_U to obtain Q_X,d_j.
Then B_N = Rj_*E_N is bounded in D^b_{Q_X}, constructible for constructible N,
and has upper bound c_U+d_j for N in D^{≤0}.
4. Exact closed direct image (lem-trf-oriented-closed-base-localization) gives
H^q(i_*C_N) = i_*H^q(C_N). Glue Q_Z with the connected reduced components of U,
using identity covers, to get Q_0 on X. Thus A_N = i_*C_N belongs to D^b_{Q_0},
preserves constructibility and has the same upper bound. Choose a common refinement R
of Q_0,Q_X using lem-per-galois-partition-exact-refinement.
5. The triangle of lem-per-etale-internal-hom-localization is
A_N → RHom(K,N) → B_N → A_N[1]. By lem-sf-derived-homology-long-exact, its middle
cohomology is an extension of coker(H^{q-1}B_N → H^q A_N) by
ker(H^q B_N → H^{q+1} A_N). The exact abelian and extension-closed W_R class
(lem-per-galois-partition-exact-refinement) contains it. Boundedness and the bound
max(c_Z+d_i,c_U+d_j) follow from the same sequence. The constructible subcategory is
closed under these kernels, cokernels and extensions, giving the last clause.
The partition and bound depend only on P and the fixed K,i,j, as required. -/
theorem ctf_hom_localization_devissage
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A] [Algebra (ZMod l) A]
    (hDual : (fun (R : Type (u + 1)) [CommRing R] ↦ ∃ Q : DerivedCategoryModule R X,
      DerivedCategory.boundedConstructible
        (ModuleCat.{u + 1} R) X Q ∧
      ∀ M : DerivedCategoryModule R X,
        DerivedCategory.boundedConstructible
          (ModuleCat.{u + 1} R) X M →
        DerivedCategory.boundedConstructible
          (ModuleCat.{u + 1} R) X
          (((derivedHom (ModuleCat.{u + 1} R) X).obj
            (op M)).obj Q) ∧
        IsIso
          ((derivedTensorHomAdjunction (ModuleCat.{u + 1} R)
            (((derivedHom (ModuleCat.{u + 1} R) X).obj
              (op M)).obj Q)).homEquiv M Q
            (((derivedTensorSymmetry (ModuleCat.{u + 1} R) X).hom.app
                (((derivedHom (ModuleCat.{u + 1} R) X).obj
                  (op M)).obj Q)).app M ≫
              (derivedTensorHomAdjunction
                (ModuleCat.{u + 1} R) M).counit.app Q))) (ULift.{u + 1} (ZMod l)))
    {Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j]
    (hcomp : Set.range i.base ∩ Set.range j.base = (∅ : Set X) ∧
      Set.range i.base ∪ Set.range j.base = Set.univ)
    (K : DerivedCategoryModule A X)
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X K)
    (hi : SatisfiesConditionB A Z
      ((Etale.upperStar (ModuleCat.{u + 1} A) i).mapDerivedCategory.obj K))
    (hj : SatisfiesConditionB A U
      ((Etale.upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj K)) :
    SatisfiesConditionB A X K := by
  sorry

end AlgebraicGeometry.Etale
