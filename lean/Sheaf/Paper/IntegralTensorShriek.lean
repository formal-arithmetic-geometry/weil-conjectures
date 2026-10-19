/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q82
-/
module

public import Sheaf.Paper.ModuleObjects
public import Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.Paper.IntegralModelSurjectiveClosedReflection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.AlgebraicGeometry.ProEtaleOpenExtensionProducts
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Sheaf.Paper.DerivedNakayamaResolution
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Paper.CondensedConstantConstructibility
import WeilConjectures.ConstructibleSheaf.Pullback
import Sheaf.Paper.CondensedSurjectiveClosedEquivalence
import Sheaf.Paper.ProEtaleSurjectiveClosedCoverRefinement
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.Paper.CoefficientHeartCommonStratification
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Sites.Precoverage
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
import Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison
import Sheaf.Paper.CartesianCoefficients
import Sheaf.SixFunctors.ProEtale.DerivedCompletion

/-!
# Integral constructibility under immersions and generation by strata

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-int-tensor,
`det-lem-int-tensor-shriek.md` and its proof; Stacks Project, Tags 09AA, 09BM, 09BP
(blueprint: det-lem-int-tensor-shriek).

The coefficient ring is the existing continuous condensed valuation ring. Local complex
models are pulled back from finite free complexes on the point, so their differentials
are scalar matrices over the valuation ring, rather than arbitrary sheaf morphisms.
Generation is expressed by membership in every isomorphism-closed full subcategory
satisfying all three two-out-of-three conditions and containing the specified generators.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Pull a bounded finite free complex on the coefficient point to a scheme, term by
term. This is the model P tensor O_{E,X}: maps between finite copies of the regular
module on the point are scalar matrices over O_E.
Source: blueprint det-lem-int-tensor-shriek, clause (2)
(blueprint: det-lem-int-tensor-shriek). -/
noncomputable def integralTensorShriek_pointComplex
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (Q : CochainComplex (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      (integralModelCondensedCoefficients l E).X) ℤ) :
    CochainComplex
      (pulledBackModuleObjects (integralModelCondensedCoefficients l E).X X) ℤ :=
  letI : pointUpperStar.{u}.IsLeftAdjoint := pointUpperStarLowerStarAdjunction.isLeftAdjoint
  letI : (upperStarFromPoint X).IsLeftAdjoint :=
    inferInstanceAs ((pointUpperStar ⋙ upperStar Ab.{u + 1} (toSpecZ X)).IsLeftAdjoint)
  (Functor.mapHomologicalComplex
    ((upperStarFromPoint X).mapMod (integralModelCondensedCoefficients l E).X)
    (ComplexShape.up ℤ)).obj Q

/-- Open extension by zero, closed direct image, and their locally closed composites
preserve integral bounded constructibility.
Source: blueprint det-lem-int-tensor-shriek, clause (1)
(blueprint: det-lem-int-tensor-shriek).

Proof (DAG steps 1--6):
1. Cartesian coefficients identify restrictions of O_E with O_E. Noetherianity makes the
open immersions and complementary opens quasi-compact. The reduced-induced-closed
subscheme and pro-etale ringed open/closed lemmas give exactness and the four restriction
identities. Exact functors act termwise on derived categories.
2. Open extension preserves products and derived limits by
 det-sf-open-closed-extension-zero-limits. Closed direct image preserves products by its
right adjunction. Exact countable pro-etale products and derived-limit-products-core
identify derived products termwise. Apply the functors to the Roos triangle to preserve
sequential derived limits, with the natural strict product-and-cone comparisons.
3. The uniformizer resolution of det-pe-derived-nakayama-resolution represents reduction
modulo its nth power by a cone. Exact coefficient-linear functors preserve this cone;
the transition chain maps have components pi_E and 1, so the comparisons respect the
entire reduction tower and its map from the original complex.
4. These comparisons carry the completion isomorphism to the completion map of the image.
The integral criterion in sk-lem-integral-models (2) supplies completeness of the input
and constructibility of its residue reduction; its preservation clause (3) is not used.
5. Extend a finite stratification of the source by the complementary stratum. Restriction
of the image is the original module on its strata and zero on the complement. This gives
constructibility at the finite residue level, including torsion modules and the zero module.
6. Exactness commutes with homology and preserves bounds. The finite coefficient
constructible comparison and the integral criterion now give the assertion for j_! and
i_*. Apply them successively to i_* u_! for the locally closed case. -/
theorem integralTensorShriek_preserves
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (_hp : 0 < p) (_hpl : p ≠ l)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsNoetherian X]
    : (∀ (U : Scheme.{u}) (j : U ⟶ X) [IsOpenImmersion j]
        (M : DerivedCategory (pulledBackModuleObjects (integralModelCondensedCoefficients l E).X
          U)),
        boundedConstructible (condensedRingObj (integralModelCondensedCoefficients l E).X U) M →
          boundedConstructible (condensedRingObj (integralModelCondensedCoefficients l E).X X)
            ((CondensedRing.openImmersionLowerShriek (integralModelCondensedCoefficients l E).X
              j).mapDerivedCategory.obj M)) ∧
      (∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i]
        (M : DerivedCategory (pulledBackModuleObjects (integralModelCondensedCoefficients l E).X
          Z)),
        boundedConstructible (condensedRingObj (integralModelCondensedCoefficients l E).X Z) M →
          boundedConstructible (condensedRingObj (integralModelCondensedCoefficients l E).X X)
            ((CondensedRing.lowerStar (integralModelCondensedCoefficients l E).X
              i).rightDerivedFunctor.obj M)) ∧
      (∀ (S Z : Scheme.{u}) (v : S ⟶ Z) (i : Z ⟶ X)
        [IsOpenImmersion v] [IsClosedImmersion i]
        (M : DerivedCategory (pulledBackModuleObjects (integralModelCondensedCoefficients l E).X
          S)),
        boundedConstructible (condensedRingObj (integralModelCondensedCoefficients l E).X S) M →
          boundedConstructible (condensedRingObj (integralModelCondensedCoefficients l E).X X)
            (((CondensedRing.openImmersionLowerShriek (integralModelCondensedCoefficients l E).X
              v).mapDerivedCategory ⋙
              (CondensedRing.lowerStar (integralModelCondensedCoefficients l E).X
                i).rightDerivedFunctor).obj M)) := by
  sorry

/-- Every integral bounded constructible complex is generated by extensions, with the
source's explicit two-out-of-three meaning, and isomorphisms from extensions by zero of
stratum complexes locally obtained from bounded finite free scalar complexes.
Source: blueprint det-lem-int-tensor-shriek, clause (2)
(blueprint: det-lem-int-tensor-shriek).

Proof (DAG steps 7--13, using steps 1--6 above):
7. Cartesian coefficients and exact homology comparison preserve bounded constructibility
under restriction to locally closed subschemes. Pull back the finite stratification and its
model covers; weakly-etale and fpqc base change verify that they remain pro-etale covers.
8. det-lem-int-integral-heart-local-model gives whole-complex bounded finite free scalar
models on strata. Pullback preserves their finite free terms and scalar differentials,
and the model covers pull back by the same geometric base-change results.
9. For refinements changing scheme structures, form T times_X S. Its map to T is a
surjective closed immersion, without assuming that point-set containment gives a scheme
factorization. The condensed-surjective-closed equivalence and cover-refinement lemmas
lift the model isomorphisms by fullness and faithfulness, also on derived categories.
10. The coefficient-independent topological clause of
 det-lem-coefficient-heart-common-stratification orders a finite refinement so that prefixes
are open. Realize their closed complements with reduced induced structures. The successive
closed maps factor scheme-theoretically: initially the ideal is zero, subsequently inclusion
of closed subsets reverses inclusion of the radical ideals. Thus nonreduced X is included.
11. The ringed open/closed short exact sequence termwise and complex-ses-triangle give the
localization triangle e_! M -> K|Y -> h_* K|Y' -> e_! M[1], with ordinary inverse image.
12. Push it to X. Exact closed direct image preserves distinguished triangles, and the
canonical lower-star composition comparison identifies successive vertices with
Q_r = c_{r,*}(K|Y_r). The first vertex is precisely the indicated stratum generator.
13. The last closed complement is empty, so Q_m is zero. The zero complex is itself an
allowed generator (use the one-stratum identity stratification and its zero finite free
model). Descend through the finite localization triangles by two-out-of-three to Q_0,
which is isomorphic to K. Isomorphism closure proves membership in every such full
subcategory, which is exactly membership in the smallest one. -/
theorem integralTensorShriek_generated
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (_hp : 0 < p) (_hpl : p ≠ l)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsNoetherian X]
    (K : DerivedCategory (pulledBackModuleObjects (integralModelCondensedCoefficients l E).X X))
    (hK : boundedConstructible (condensedRingObj (integralModelCondensedCoefficients l E).X X) K)
    (P : ObjectProperty (DerivedCategory (pulledBackModuleObjects
      (integralModelCondensedCoefficients l E).X X)))
    [P.IsClosedUnderIsomorphisms]
    [P.IsTriangulatedClosed₁] [P.IsTriangulatedClosed₂] [P.IsTriangulatedClosed₃]
    (hgen : ∀ (T : X.FiniteLocallyClosedStratification) (a : Fin T.n)
      (Z : Scheme.{u}) (v : T.domain a ⟶ Z) (i : Z ⟶ X)
      [IsOpenImmersion v] [IsClosedImmersion i],
      v ≫ i = T.immersion a →
      ∀ M : DerivedCategory (pulledBackModuleObjects (integralModelCondensedCoefficients l E).X
        (T.domain a)),
        boundedConstructible (condensedRingObj (integralModelCondensedCoefficients l E).X
          (T.domain a)) M →
        (∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage (T.domain a), ∀ b : C.I₀,
          ∃ Q : CochainComplex
            (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
              (integralModelCondensedCoefficients l E).X) ℤ,
            (∃ r s : ℤ, ∀ n : ℤ, n < r ∨ s < n → IsZero (Q.X n)) ∧
            (∀ n : ℤ, Mod.IsFree (integralModelCondensedCoefficients l E).X (Q.X n)) ∧
            Nonempty
              ((CondensedRing.upperStar (integralModelCondensedCoefficients l E).X (C.f
                b)).mapDerivedCategory.obj M ≅
                DerivedCategory.Q.obj
                  (integralTensorShriek_pointComplex l E (C.X b) Q))) →
        P (((CondensedRing.openImmersionLowerShriek (integralModelCondensedCoefficients l E).X
          v).mapDerivedCategory ⋙
          (CondensedRing.lowerStar (integralModelCondensedCoefficients l E).X
            i).rightDerivedFunctor).obj M)) :
    P K := by
  sorry

end AlgebraicGeometry.ProEtale
