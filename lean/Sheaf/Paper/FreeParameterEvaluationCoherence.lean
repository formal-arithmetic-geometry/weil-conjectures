/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q155
-/
module

public import Sheaf.Paper.FreeParameterEvaluationData
public import Sheaf.Paper.FreeParameterRelativeMaps
public import Sheaf.Paper.FreeParameterDegreeZeroData
public import Sheaf.Paper.FreeParameterScalarMaps
public import Sheaf.Paper.FreeParameterMatrixCoordinates

/-! # Canonical free-parameter evaluation data and coherence.
Source: Stacks 08J7, 07A6, 07A7 (blueprint: lem-sfb-free-parameter-evaluation-coherence). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FreeParameterEvaluation
variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]

/-- Factorization uses the dependency's actual normalized gamma, and naturality
holds for every derived coefficient arrow without invertibility hypotheses.
Source: Stacks 08J7, node proof steps 1--4
(blueprint: lem-sfb-free-parameter-evaluation-coherence).
Proof: use G.freeGenerators and G.localization to identify the rho-transpose of
G.gamma with universal-generator evaluation. The defining closed transpose of beta
then makes gamma beta have precisely the transpose defining c. Injectivity of the
pull-push Hom equivalence proves factorization. Naturality of both counits and the
point-composition comparison proves the displayed square for every derived arrow. -/
theorem factorization_and_naturality (X : Scheme.{u}) (P : Profinite.{u})
    (G : ProfiniteFreeSlice.Comparison R.X X P) :
    (∀ N : DerivedCategory (PointModules R),
      comparisonApp R X P N = beta R X P N ≫ G.gamma.hom.app ((pointPullD R X).obj N) ≫
        (CondensedRing.moduleObjectDerivedPushforward R.X (projection X P)).map
          ((pointCompD R X P G).hom.app N)) ∧
    ∀ (N N' : DerivedCategory (PointModules R)) (v : N ⟶ N'),
      (pointPullD R X).map ((functions R P).map v) ≫ comparisonApp R X P N' =
        comparisonApp R X P N ≫
          (CondensedRing.moduleObjectDerivedPushforward R.X (projection X P)).map
            ((pointPullD R (testScheme X P)).map v) := by
  sorry

/-- Gamma commutes with every relative parameter map and every derived coefficient
map. Evaluating the free map at any generalized generator t gives the generator a t;
thus this is the whole-family identity, not a test only on points.
Source: Stacks 08J7, node proof steps 6--7
(blueprint: lem-sfb-free-parameter-evaluation-coherence).
Proof: transpose both sides by the P'-projection adjunction. The free adjunction
sends [t] to [a t]. The unit defining pushParameterApp and its counit contract by
the triangle identity, leaving evaluation at the same a t, followed by v.
The normalized evaluation field of G and G' and injectivity of transposition
then give the equality for arbitrary derived K,K' and v. -/
theorem whole_family (V : Scheme.{u}) (P P' : Profinite.{u})
    (G : ProfiniteFreeSlice.Comparison R.X V P)
    (G' : ProfiniteFreeSlice.Comparison R.X V P')
    (a : testScheme V P' ⟶ testScheme V P)
    (ha : a ≫ projection V P = projection V P')
    (K K' : DerivedCategory (Modules R V)) (v : K ⟶ K') :
    (schemeParameterMap R V P P' G G' a ha).app K ≫
      (schemeFunctions R V P').map v ≫ G'.gamma.hom.app K' =
    G.gamma.hom.app K ≫ pushParameterApp R V P P' a ha K ≫
      (CondensedRing.moduleObjectDerivedPushforward R.X (projection V P')).map
        ((CondensedRing.upperStar R.X (projection V P')).mapDerivedCategory.map v) := by
  sorry

/-- The c-square follows for the independently beta-conjugated action.
Source: Stacks 08J7 (blueprint: lem-sfb-free-parameter-evaluation-coherence).
Proof: substitute c=gamma beta, cancel the target beta against its inverse, and
apply whole_family. Naturality of point-composition provides the final target map. -/
theorem conjugated_action (V : Scheme.{u}) (P P' : Profinite.{u})
    (G : ProfiniteFreeSlice.Comparison R.X V P)
    (G' : ProfiniteFreeSlice.Comparison R.X V P')
    (a : testScheme V P' ⟶ testScheme V P)
    (ha : a ≫ projection V P = projection V P')
    (N N' : DerivedCategory (PointModules R))
    (v : (pointPullD R V).obj N ⟶ (pointPullD R V).obj N')
    [IsIso (beta R V P N)] [IsIso (beta R V P' N')] :
    conjugatedAction R V P P' G G' a ha N N' v ≫ comparisonApp R V P' N' =
    comparisonApp R V P N ≫
      (CondensedRing.moduleObjectDerivedPushforward R.X (projection V P)).map
        ((pointComposition R (projection V P)).inv.app N) ≫
      pushParameterApp R V P P' a ha ((pointPullD R V).obj N) ≫
      (CondensedRing.moduleObjectDerivedPushforward R.X (projection V P')).map
        ((CondensedRing.upperStar R.X (projection V P')).mapDerivedCategory.map v) ≫
      (CondensedRing.moduleObjectDerivedPushforward R.X (projection V P')).map
        ((pointComposition R (projection V P')).hom.app N') := by
  sorry

/-- Parameter naturality and pro-etale base change with the actual adjunction mates.
Source: Stacks 08J7 and 07A7, node proof steps 4--5
(blueprint: lem-sfb-free-parameter-evaluation-coherence).
Proof: transpose each square. The free map sends [t'] to [j t']; base change sends
the tautological generator to the tautological generator. Both routes consequently
evaluate at the same generalized parameter. The direct-image units and counits
are those defining pushParameterApp and pushSquareApp. Uniqueness of transposes
proves equality as derived arrows before any homology is taken. -/
theorem parameter_and_base_change (X : Scheme.{u}) (P : Profinite.{u}) :
    (∀ (P' : Profinite.{u}) (j : P' ⟶ P) (N : DerivedCategory (PointModules R)),
      (pointPullD R X).map ((pointParameterMap R j).app N) ≫ comparisonApp R X P' N =
      comparisonApp R X P N ≫
        (CondensedRing.moduleObjectDerivedPushforward R.X (projection X P)).map
          ((pointComposition R (projection X P)).inv.app N) ≫
        pushParameterApp R X P P' (testSchemeMap X j)
          (MorphismProperty.Over.w ((profiniteToProEtOf X).map j))
          ((pointPullD R X).obj N) ≫
        (CondensedRing.moduleObjectDerivedPushforward R.X (projection X P')).map
          ((pointComposition R (projection X P')).hom.app N)) ∧
    ∀ (Y : Scheme.{u}) (g : Y ⟶ X) [WeaklyEtale g]
      (N : DerivedCategory (PointModules R)),
      (CondensedRing.upperStar R.X g).mapDerivedCategory.map (comparisonApp R X P N) ≫
        pushSquareApp R g P P (parameterBaseMap g P) (pullback.lift_snd _ _ _)
          ((pointPullD R (testScheme X P)).obj N) ≫
        (CondensedRing.moduleObjectDerivedPushforward R.X (projection Y P)).map
          ((pointComposition R (parameterBaseMap g P)).hom.app N) =
      (pointComposition R g).hom.app ((functions R P).obj N) ≫ comparisonApp R Y P N := by
  sorry

/-- In degree zero the map is the exponential-law evaluation on the universal generator.
Source: Stacks 08J7, node proof step 3
(blueprint: lem-sfb-free-parameter-evaluation-coherence).
Proof: choose a nonnegative injective resolution of N. The degree-zero kernel of
internal Hom is ordinary internal Hom and that of direct image is ordinary direct
image. Exact point inverse image preserves these kernels. The defining derived-unit
maps give precisely sourceZero and targetZero. Their evaluation at every test and
generalized generator is f([t]), the underived evaluationApp in the displayed adjunct. -/
theorem degree_zero (X : Scheme.{u}) (P : Profinite.{u}) (N : PointModules R) :
    (DerivedCategory.homologyFunctor (Modules R X) 0).map
      (comparisonApp R X P ((DerivedCategory.singleFunctor (PointModules R) 0).obj N)) ≫
        (targetZero R X P N).hom =
    (sourceZero R X P N).hom ≫
      (CondensedRing.upperStarLowerStarAdjunction R.X (projection X P)).homEquiv _ _
        ((pointComp R (projection X P)).hom.app ((ihom (freeParameter R P)).obj N) ≫
          evaluationApp R X P N) := by
  sorry

section Scalars
variable (S : Profinite.CondensedRing.{u}) [IsCommMonObj S.X]
  (φ : R.X ⟶ S.X) [IsMonHom φ]

/-- Coefficient coherence and its conditional inverse square, without any flatness,
exact-extension, or comparison-isomorphism assumption in the forward identity.
Source: Stacks 07A6, 08J7; node proof steps 9--12
(blueprint: lem-sfb-free-parameter-evaluation-coherence).
Proof: transpose the square first by scalar extension and then by the projection
adjunction. Substitute the definitions of scalarHomPoint and scalarPushMap.
Both transposes apply the scalar transpose of n after evaluating at the same
universal generator: freeScalarMap sends [t] to [t], and scalarPullComparison
sends x to 1 tensor x. Tensor naturality and the two triangle identities identify
the transposes. Their injectivity proves the forward equality. If both c maps
are isomorphisms, multiply by their inverses to obtain the inverse equality. -/
theorem coefficient_square (X : Scheme.{u}) (P : Profinite.{u})
    (N : DerivedCategory (PointModules R)) (N' : DerivedCategory (PointModules S))
    (n : N ⟶ (restrictPoint R S φ).mapDerivedCategory.obj N') :
    (comparisonApp R X P N ≫ scalarPushMap R S φ X P N N' n =
      scalarHomMap R S φ X P N N' n ≫
        (restrictScheme R S φ X).mapDerivedCategory.map (comparisonApp S X P N')) ∧
    ∀ (_ : IsIso (comparisonApp R X P N)) (_ : IsIso (comparisonApp S X P N')),
      inv (comparisonApp R X P N) ≫ scalarHomMap R S φ X P N N' n =
        scalarPushMap R S φ X P N N' n ≫
          (restrictScheme R S φ X).mapDerivedCategory.map
            (inv (comparisonApp S X P N')) := by
  sorry

end Scalars

/-- In checking bases the beta-conjugated F-action is the actual matrix-vector
formula: the ith coordinate is sum_j m_ij f_j(a(t')). The entries are local
sections, expressed by their actions on the regular module, and the statement
allows every checking basis. The intrinsic F-action contains no checking basis.
Source: Stacks 08J7, node proof step 8
(blueprint: lem-sfb-free-parameter-evaluation-coherence).
Proof: insert the finite-biproduct identity between the local map and evaluation.
Precomposition sends the generalized parameter t' to a(t'), and postcomposition
by the regular-module endomorphism m_ij multiplies the jth value by that section.
Linearity of evaluation gives the displayed sum. Cancel beta with its inverse in
the independently defined action. This proves the formula including non-point
entries and empty ranks. Since it holds for every e,e', changing bases changes
only the coordinates of the same intrinsic action, proving basis independence. -/
theorem finite_free_matrix (V : Scheme.{u}) (P P' : Profinite.{u})
    (G : ProfiniteFreeSlice.Comparison R.X V P)
    (G' : ProfiniteFreeSlice.Comparison R.X V P')
    (a : testScheme V P' ⟶ testScheme V P)
    (ha : a ≫ projection V P = projection V P') (r s : ℕ)
    (e : (pointPull R V).obj (finiteFreePoint R r) ≅ finiteFreeLocal R V r)
    (e' : (pointPull R V).obj (finiteFreePoint R s) ≅ finiteFreeLocal R V s)
    (v : (pointPull R V).obj (finiteFreePoint R r) ⟶
      (pointPull R V).obj (finiteFreePoint R s))
    [IsIso (beta R V P
      ((DerivedCategory.singleFunctor (PointModules R) 0).obj (finiteFreePoint R r)))]
    [IsIso (beta R V P'
      ((DerivedCategory.singleFunctor (PointModules R) 0).obj (finiteFreePoint R s)))]
    (i : Fin s) :
    conjugatedAction R V P P' G G' a ha _ _ (localCoefficientMap R V r s v) ≫
      beta R V P' _ ≫ (schemeFunctions R V P').map (coordinate R V s e' i) =
    ∑ j : Fin r, beta R V P _ ≫
      (schemeFunctions R V P).map (coordinate R V r e j) ≫
      (schemeParameterMap R V P P' G G' a ha).app
        ((DerivedCategory.singleFunctor (Modules R V) 0).obj (𝟙_ (Modules R V))) ≫
      (schemeFunctions R V P').map
        ((DerivedCategory.singleFunctor (Modules R V) 0).map
          (localMatrix R V e e' v i j)) := by
  sorry

/-- The matrices in the preceding evaluation formula multiply as matrices of local
sections, including the empty middle rank. Combined with finite_free_matrix this
is multiplication of the beta-conjugated coordinate vectors by those matrices.
Source: Stacks 08J7, node proof step 8
(blueprint: lem-sfb-free-parameter-evaluation-coherence).
Proof: expand the entries of the two matrices. Matrix multiplication sums over
middle basis indices. Insert the biproduct identity in the middle module and
cancel its basis isomorphism with its inverse. Each remaining entry is the entry
of w after v, with multiplication in End given by composition in that order. -/
theorem finite_free_matrix_multiplication (V : Scheme.{u}) {r s t : ℕ}
    {M M' M'' : Modules R V}
    (e : M ≅ finiteFreeLocal R V r) (e' : M' ≅ finiteFreeLocal R V s)
    (e'' : M'' ≅ finiteFreeLocal R V t) (v : M ⟶ M') (w : M' ⟶ M'') :
    localMatrix R V e e'' (v ≫ w) =
      localMatrix R V e' e'' w * localMatrix R V e e' v := by
  sorry

/-- Whole-family substitution over X[Q] persists under every further restriction
functor and under any composite of successive slice restrictions.
Source: Stacks 08JB and 07A7 (blueprint: lem-sfb-free-parameter-evaluation-coherence).
Proof: apply whole_family on V=X[Q] to the specified relative map. Its free map
sends every generalized [q,t'] to [q,alpha(q,t')]. Apply E to the resulting derived
equality. For a composite restriction this is functoriality twice; the canonical
pullback composition comparisons and mate-pasting identify the same equality
on the composite localized site, with no need to test equality only on points. -/
theorem restricted_whole_family (X : Scheme.{u}) (Q P P' : Profinite.{u})
    (G : ProfiniteFreeSlice.Comparison R.X (testScheme X Q) P)
    (G' : ProfiniteFreeSlice.Comparison R.X (testScheme X Q) P')
    (α : Q ⨯ P' ⟶ P)
    (K K' : DerivedCategory (Modules R (testScheme X Q))) (v : K ⟶ K')
    {D : Type w} [Category.{v} D]
    (E : DerivedCategory (Modules R (testScheme X Q)) ⥤ D) :
    E.map ((schemeParameterMap R (testScheme X Q) P P' G G'
        (familyParameterMap X Q P P' α) (pullback.lift_snd _ _ _)).app K ≫
      (schemeFunctions R (testScheme X Q) P').map v ≫ G'.gamma.hom.app K') =
    E.map (G.gamma.hom.app K ≫
      pushParameterApp R (testScheme X Q) P P' (familyParameterMap X Q P P' α)
        (pullback.lift_snd _ _ _) K ≫
      (CondensedRing.moduleObjectDerivedPushforward R.X (projection (testScheme X Q) P')).map
        ((CondensedRing.upperStar R.X (projection (testScheme X Q) P')).mapDerivedCategory.map
          v)) := by
  sorry

end AlgebraicGeometry.ProEtale.FreeParameterEvaluation
