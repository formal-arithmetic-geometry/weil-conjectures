/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.Borel
public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Sheaf.AlgebraicGeometry.TorusCharacterTangentWeights
public import Sheaf.AlgebraicGeometry.RhoSectionModuleData
public import Sheaf.AlgebraicGeometry.GroupScheme.RationalHighestWeightData
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.AlgebraicGeometry.Pullbacks
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations

/-! # Simplicity of the infinitesimal induced Steinberg module

Source: Jantzen, Representations of Algebraic Groups, II.3.18 and II.9.1;
Kaneda, On the Frobenius morphism of flag schemes (1994), Section 2.5, (4)--(9),
printed pp.322--323 (corroboration).
(blueprint: lem-sfb-steinberg-infinitesimal-induced-simple)

The Frobenius twists are specified by cartesian squares over the field power map.
The normalization on global functions specifies the relative Frobenius uniquely:
on the tensor-product coordinate algebra it sends c tensor a to a c^(p^r).
The next two cartesian squares specify L = S_r T and P = B_r T as schemes,
including their nonreduced structure. Z is the recorded actual semi-invariant
subspace of F[L]. The last formula specifies its coaction by left translation
on every algebra-valued point, rather than only on F-points.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj TensorProduct

namespace AlgebraicGeometry

/-- Left translation on the actual infinitesimal induced Steinberg module is rational,
finite-dimensional, nonzero and simple, including for the trivial group and p = 2.

Source: Jantzen, II.3.18, with the G_r T notation of II.9.1; corroborated by Kaneda,
Section 2.5, (4)--(9), pp.322--323.
(blueprint: lem-sfb-steinberg-infinitesimal-induced-simple)

Proof plan (the node's infinitesimal argument, not global induced-module dimensions):
1. Apply lem-sfb-frobenius-kernel-induced-dual-pbw at eta = (p^r-1)rho.
   It supplies rational left translation, dimension q^N, and the dual identification
   M = Dist(S_r) tensor_{Dist(B_r)} F_lambda = Z dual, with nonzero v = 1 tensor 1.
   Its opposite-radical PBW map H = Dist(U^-_r) to M, h to hv, is an isomorphism.
   Semisimple implies reductive by lem-sfb-reductive-borel-pair-structure, and
   lem-sfb-reductive-root-subgroup-parametrizations supplies both signs of root maps.
2. By lem-sfb-unipotent-frobenius-distribution-socle, the augmentation ideal J of H
   is nilpotent and its annihilator in M is the line F f_top v. For a nonzero
   Dist(S_r)-submodule W, choose the largest n with J^n W nonzero. Then J^n W
   is contained in that line and in W, so W contains f_top v.
3. By lem-sfb-steinberg-top-distribution-recovery, e_top f_top v = c v with c a unit.
   Thus W contains v and hence every a v, so W = M.
4. For a coaction-stable V in Z, restriction to S_r makes its annihilator in Z dual
   stable under Dist(S_r), using the antipode formula for the dual action from
   lem-sfb-frobenius-kernel-induced-dual-pbw. Step 3 makes that annihilator zero
   or all of Z dual. Finite-dimensional linear duality then gives V = Z or V = 0.
   Finally q^N is positive. For the trivial group all products are empty and Z = F;
   no step excludes p = 2 or divides by a factorial.
-/
theorem steinberg_infinitesimal_induced_simple
    {F : Type u} [Field F] [IsAlgClosed F]
    (p : ℕ) [Fact p.Prime] [CharP F p] (r : ℕ) (hr : 1 ≤ r)
    (S : Grp (Over (Spec (.of F)))) (hS : IsSemisimpleGroupScheme S.X)
    (hsc : ∀ (S' : Over (Spec (.of F))) [GrpObj S'],
      IsSemisimpleGroupScheme S' → ∀ (f : S' ⟶ S.X) [IsMonHom f],
      Surjective f.left → IsFinite (GrpObj.ker f).hom →
      (∀ (A : Type u) [CommRing A] [Algebra F A]
        (x : StandardGroupSchemes.affine F A ⟶ GrpObj.ker f)
        (g : StandardGroupSchemes.affine F A ⟶ S'),
        (x ≫ GrpObj.kerι f) * g = g * (x ≫ GrpObj.kerι f)) → IsIso f)
    (T B U : Grp (Over (Spec (.of F))))
    (iT : T ⟶ S) (iB : B ⟶ S) (j : T ⟶ B) (iU : U ⟶ B)
    (hT : ReductiveTorusCentralizer.IsMaximalTorus iT)
    (hsplit : ∃ n : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F n))
    (hB : IsBorelGroupScheme iB.hom.hom) (hj : j ≫ iB = iT)
    (hUclosed : IsClosedSubgroupScheme iU.hom.hom)
    (hUnormal : IsNormalSubgroupScheme iU.hom.hom)
    (hUsmooth : Smooth U.X.hom) (hUconnected : ConnectedSpace U.X.left)
    (hUunipotent : SolvableGroupStructure.IsUnipotent U)
    (hUmax : ∀ (N : Grp (Over (Spec (.of F)))) (iN : N ⟶ B),
      IsClosedSubgroupScheme iN.hom.hom → IsNormalSubgroupScheme iN.hom.hom →
      Smooth N.X.hom → ConnectedSpace N.X.left →
      SolvableGroupStructure.IsUnipotent N → ∃ f : N ⟶ U, f ≫ iU = iN)
    [IsCommMonObj (StandardGroupSchemes.multiplicative F)] [ModObj T.X B.X]
    (hconj : γ[T.X,B.X] =
      (fst T.X B.X ≫ j.hom.hom) * snd T.X B.X * (fst T.X B.X ≫ j.hom.hom)⁻¹)
    (Φplus : Finset (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
    (hΦplus : ∀ χ, χ ∈ Φplus ↔
      χ ≠ 1 ∧ TorusCharacterTangent.weightSpace T B χ ≠ ⊥)
    (ρ : T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))
    (hρ : ρ ^ 2 = ∏ α ∈ Φplus, α)
    (ρB : B ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))
    (hρB : j ≫ ρB = ρ) (hρU : iU ≫ ρB = 1)
    (Sq Tq : Over (Spec (.of F)))
    (πS : Sq.left ⟶ S.X.left) (πT : Tq.left ⟶ T.X.left)
    (hSq : IsPullback πS Sq.hom S.X.hom
      (Spec.map (CommRingCat.ofHom (iterateFrobenius F p r))))
    (hTq : IsPullback πT Tq.hom T.X.hom
      (Spec.map (CommRingCat.ofHom (iterateFrobenius F p r))))
    (iTq : Tq ⟶ Sq) (hiTq : iTq.left ≫ πS = πT ≫ iT.hom.hom.left)
    (Fr : S.X ⟶ Sq)
    (hFr : ∀ c : Γ(S.X.left, ⊤), Fr.left.appTop (πS.appTop c) = c ^ (p ^ r))
    (L P : Grp (Over (Spec (.of F)))) [IsAffine L.X.left]
    (iL : L ⟶ S) (tL : L.X ⟶ Tq)
    (hL : IsPullback tL iL.hom.hom iTq Fr)
    (iP : P ⟶ L) (pB : P ⟶ B)
    (hP : IsPullback pB.hom.hom iP.hom.hom iB.hom.hom iL.hom.hom)
    (Z : Submodule F (RhoSection.Coordinate L.X))
    (hZ : Z = RhoSection.sectionModule L P iP (pB ≫ ρB) (p ^ r - 1)) :
    FiniteDimensional F Z ∧
      ∃ c : Z →ₗ[F] Z ⊗[F] RationalHighestWeight.coordinateAlgebra L,
        HopfAction.Coassociative F (RationalHighestWeight.coordinateAlgebra L) Z c ∧
        HopfAction.Counital F (RationalHighestWeight.coordinateAlgebra L) Z c ∧
        (∀ (A : Type u) [CommRing A] [Algebra F A]
          (h x : StandardGroupSchemes.affine F A ⟶ L.X) (f : Z)
          (n : ℕ) (fi : Fin n → Z)
          (ai : Fin n → RationalHighestWeight.coordinateAlgebra L),
          c f = ∑ i, fi i ⊗ₜ[F] ai i →
          ∑ i, RhoSection.evaluate x (fi i).val *
            (Scheme.ΓSpecIso (.of A)).hom (h.left.appTop (ai i)) =
              RhoSection.evaluate (h⁻¹ * x) f.val) ∧
        RationalHighestWeight.IsSimple c := by
  sorry

end AlgebraicGeometry
