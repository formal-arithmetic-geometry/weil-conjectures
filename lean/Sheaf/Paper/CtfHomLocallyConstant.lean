/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q59
-/
module

public import Sheaf.Paper.GaloisPartitionModules
public import Sheaf.CategoryTheory.LocallyConstantFiniteTypeModules
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Data.ZMod.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Sheaf.AlgebraicGeometry.PointedEtaleStalk
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteProjectiveInternalHomEvaluation
import Sheaf.Paper.ConstantSheafSectionsLocallyConstant
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
import Sheaf.AlgebraicGeometry.GaloisPartitionExactRefinement
import Sheaf.AlgebraicGeometry.NoetherianCtfFlatModel
import Sheaf.Paper.GaloisPartitionTensorClosure
import WeilConjectures.SixFunctors.Etale.Derived.Tensor

/-!
# Condition (B) for flat locally constant constructible sheaves

Source: ILO, Travaux de Gabber, Expose XVII, Lemma 7.6.11, p. 314
(blueprint: lem-per-ctf-hom-locally-constant).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.Etale

/-- A flat locally constant constructible sheaf satisfies condition (B), with no widening
of the cohomological interval. Local constancy is etale-local; no finite etale cover of a
whole connected component is assumed to trivialize F.
Source: ILO XVII, Lemma 7.6.11, p. 314
(blueprint: lem-per-ctf-hom-locally-constant).

Proof:
1. Exact tensor with F commutes with cohomology, so F[0] is K-flat and has Tor amplitude
[0,0] (lem-weil-pbc-exact-functor-complex-cohomology, def-kun-derived-tensor).
Apply lem-per-noetherian-ctf-flat-model in [0,0] to obtain a Galois partition Q with
finite projective constant fibres for F on its covers.
2. On every nonempty etale trivialization of F, choose a geometric point and lift it
through a cover of Q. The two stalk descriptions identify its constant module with one
of these finite projective modules (def-weil-pbc-geometric-stalks and
prop-weil-pbc-inverse-image-modules-exact). Thus F is locally a finite free summand.
3. Put T(G)=Hom(F,G), D=T(A_X). Precomposition with a finite-free retraction expresses
T locally as the image of a constant idempotent on a finite sum. It is exact, and D is
flat locally constant of finite type. Constant sheaf sections are locally constant maps
(lem-weil-pbc-constant-sheaf-sections-locally-constant). Finite-projective evaluation
identifies D tensor G with T(G) (lem-pc-finite-projective-internal-hom-evaluation).
The cover detects these isomorphisms (lem-sfb-sheaf-cover-local-isomorphism).
4. Exact inverse image preserves the finite retraction calculation, hence commutes
with T and identifies the pullback of D on the covers of Q with the constant duals.
In particular D belongs to W_Q.
5. A K-injective representative I of N computes RHom(F,N) as T(I). Exactness of T
shows H^q RHom(F,N)=T(H^q N)=D tensor H^q N, for every integer q.
6. Apply lem-per-galois-partition-exact-refinement to P and Q. The common refinement R
contains their weak classes, and lem-per-galois-partition-tensor-closure puts all the
sheaves D tensor H^q N in W_R.
7. The cohomology formula preserves [u,v]. R depends only on P and F and refines P.
The empty scheme uses the empty partition. No dualizing complex is used.
8. If N is constructible, restrict each cohomology sheaf to a finite locally closed
stratification. Joint etale trivializations identify T(H^q N) with Hom_A(M,B), with M
finite projective and B finitely generated. It is a summand of a finite sum of B and
hence finitely generated. This proves the final constructibility assertion. -/
theorem ctf_hom_locallyConstant
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A] [Algebra (ZMod l) A]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hF : Scheme.IsFiniteLocallyConstantSheaf F)
    (hFlat : exactFunctor _ _ (tensorLeft F)) :
    ∀ P : Scheme.GaloisPartition X, ∃ P' : Scheme.GaloisPartition X,
      P'.Refines P (ULift.{u + 1} (ZMod l)) ∧ ∀ (a b : ℤ), a ≤ b → ∀ N : DerivedCategoryModule A X,
        P.boundedDerived A N →
        (∀ q : ℤ, q < a ∨ b < q →
          IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj N)) →
        P'.boundedDerived A
          (((derivedHom (ModuleCat.{u + 1} A) X).obj
            (op ((_root_.DerivedCategory.singleFunctor _ 0).obj F))).obj N) ∧
        (∀ q : ℤ, q < a ∨ b < q →
          IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
            (((derivedHom (ModuleCat.{u + 1} A) X).obj
              (op ((_root_.DerivedCategory.singleFunctor _ 0).obj F))).obj N))) ∧
        (DerivedCategory.constructibleHomology (ModuleCat.{u + 1} A) X N →
          DerivedCategory.constructibleHomology (ModuleCat.{u + 1} A) X
            (((derivedHom (ModuleCat.{u + 1} A) X).obj
              (op ((_root_.DerivedCategory.singleFunctor _ 0).obj F))).obj N)) := by
  sorry

end AlgebraicGeometry.Etale
