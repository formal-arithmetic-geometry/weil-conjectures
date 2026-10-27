/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q109
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousOrbitQuotientGeometry
public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension

import Sheaf.AlgebraicGeometry.GroupScheme.SmoothGroupOrbitGeometry
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Sheaf.AlgebraicGeometry.ProjectiveClosedIntersectionDimension

/-! # Fixed points on a proper homogeneous space

Source: Milne, Algebraic Groups (2017), Corollary 20.12, printed p.411,
and Proposition 20.11, printed pp.410--411; Theorem 7.18, printed p.143
(blueprint: lem-sfb-proper-homogeneous-torus-fixed-bound).

The right-coset presheaf is the coequalizer of projection and right multiplication.
The map to the represented quotient has the sheafification universal property.
Equivariance of q specifies the induced left torus action. Fixedness is tested on
all commutative F-algebras, so it retains the scheme-theoretic meaning.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- A torus has at least dim(X)+1 distinct universally fixed rational points on a
proper homogeneous space X = G/H. The subgroup H may be nonreduced, disconnected
or nonnormal. The torus may have rank zero and need not be maximal. Properness
includes the separated finite-type hypotheses on X. No finite fixed-locus
hypothesis is made. The integer d records the actual topological Krull dimension.

Source: Milne, Corollary 20.12, p.411, Proposition 20.11, pp.410--411,
and Theorem 7.18, p.143
(blueprint: lem-sfb-proper-homogeneous-torus-fixed-bound).

Proof, following the seven steps of the node:
1. By lem-sfb-chevalley-scheme-line-stabilizer choose a nonzero representation V
   and a line with stabilizer H. The homogeneous quotient and smooth orbit geometry
   identify X equivariantly with its locally closed orbit in P(V). Projective-space
   separatedness, proper-over-separated and proper-immersion-closed make this a
   closed immersion. The identity coset makes X nonempty.
2. Prove the projective estimate for every nonempty closed S-stable subscheme Z
   of P(V), by induction on dim(V)-1. The Hilbert-polynomial dimension lemma gives
   finite nonnegative dimension, and the monomial count gives dim(P^m)=m. In
   ambient dimension zero the standard chart is Spec(F), with its unique point.
3. The split-torus weight decomposition gives an eigenbasis. The separating
   cocharacter of lem-sfb-projective-torus-fixed-weight-schemes separates its
   distinct characters. Order the integer weights with the first minimal. The
   span of the remaining basis vectors gives a stable hyperplane Q=P(W).
   Form the scheme-theoretic intersection Y=Z ×[P(V)] Q, using standard charts.
4. If the support of Z is contained in Q, Y has the same underlying topology and
   dimension; induction on P(W) proves the bound. Otherwise the Jacobson lemma
   gives a closed point of Z outside Q, and the closed-point residue-field lemma
   makes it rational. Normalize its first homogeneous coordinate to one.
5. In that affine chart send each coordinate to a_i t^(m_i-m_0). The nonnegative
   weights define an A^1-map, agreeing with the cocharacter orbit on G_m. Every
   defining equation vanishes in F[t,t^-1], hence in F[t]; the map lands in Z.
   At zero only coordinates of the minimal weight remain. Their characters are
   equal by separation, so every S(A) acts on the representing vector by the
   same unit. Its line is unchanged for every F-algebra A. This fixed point p
   is outside Y.
6. If dim(Z)=0, p suffices. Otherwise the projective closed-intersection dimension
   lemma gives Y nonempty with dim(Y) at least dim(Z)-1. Induction gives dim(Z)
   distinct fixed points in Y; adjoining p gives the required extra point.
7. Apply this estimate to the closed image of X. The equivariant closed immersion
   preserves topology, dimension and all algebra-valued fixedness equalities, so
   the points pull back to X. No finiteness of the full fixed set is needed.
   Rank zero gives a trivial action; G=H gives the single point of Spec(F).
-/
theorem proper_homogeneous_torus_fixed_bound
    {F : Type u} [Field F] [IsAlgClosed F]
    (G H : Over (Spec (.of F))) [GrpObj G] [GrpObj H]
    [IsAffine G.left] [Smooth G.hom] [ConnectedSpace G.left]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (iH : H ⟶ G) [IsClosedSubgroupScheme iH]
    (X : Over (Spec (.of F))) [IsProper X.hom]
    (q : G ⟶ X)
    (ηq : coequalizer (yoneda.map (fst G H))
      (yoneda.map (lift (fst G H) (snd G H ≫ iH) ≫ μ[G])) ⟶ yoneda.obj X)
    (hηq : coequalizer.π _ _ ≫ ηq = yoneda.map q)
    (hquot : ∀ Z : Sheaf (Scheme.fppfTopology.over (Spec (.of F))) (Type u),
      Function.Bijective (fun f : yoneda.obj X ⟶ Z.obj ↦ ηq ≫ f))
    (S : Grp (Over (Spec (.of F))))
    (iS : S.X ⟶ G) [IsClosedSubgroupScheme iS]
    (hsplit : ∃ r : ℕ, Nonempty (S ≅ MultiplicativeType.splitTorus F r))
    [ModObj S.X X]
    (haction : (𝟙 S.X ⊗ₘ q) ≫ γ[S.X, X] = (iS ⊗ₘ 𝟙 G) ≫ μ[G] ≫ q) :
    ∃ (d : ℕ) (x : Fin (d + 1) → (𝟙_ (Over (Spec (.of F))) ⟶ X)),
      topologicalKrullDim X.left = (d : WithBot ℕ∞) ∧ Function.Injective x ∧
      ∀ (j : Fin (d + 1)) (A : Type u) [CommRing A] [Algebra F A]
        (s : StandardGroupSchemes.affine F A ⟶ S.X),
        s • (toUnit (StandardGroupSchemes.affine F A) ≫ x j) =
          toUnit (StandardGroupSchemes.affine F A) ≫ x j := by
  sorry

end AlgebraicGeometry
