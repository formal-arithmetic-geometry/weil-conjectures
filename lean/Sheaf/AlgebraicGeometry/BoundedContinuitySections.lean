/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.AlgebraicGeometry.ProEtale.HypercoverComplex
public import Sheaf.AlgebraicGeometry.ProEtale.HypercoverExistence
public import Sheaf.AlgebraicGeometry.ProEtaleWContractibleSectionsDerived
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Topology.Defs.Filter
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.AlgebraicGeometry.ProperHeartContinuitySections
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
# Bounded-below continuity of hypercover sections

Source: blueprint main-20261015, sec-proetale-coefficients/sk-cor-pe-bounded-continuity/
sk-lem-bounded-continuity-sections.md and its proof
(blueprint: det-lem-bounded-continuity-sections).

The first statement is the general categorical assertion in clause (1). The second
collects evaluation continuity, the natural derived and cohomological hypercover
comparisons, finite effective diagonals, and the canonical comparison of clause (3).
-/

@[expose] public section

set_option autoImplicit false

universe t u v wA wB s uC uD vC vD

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory

/-- Exact additive functors preserving arbitrary direct sums preserve all small colimits.
Source: blueprint main-20261015, sk-lem-bounded-continuity-sections.md, clause (1)
(blueprint: det-lem-bounded-continuity-sections).

Proof: for a small diagram D form P, the coproduct of its objects, and Q, the
coproduct over its arrows of their sources. The map Q → P has component
ι_source - D(arrow) ≫ ι_target. Its cokernel represents cocones, including for an
empty diagram, by def-weil-pbc-category-colimit. Grothendieck abelian categories
have these coproducts and cokernels. Exactness preserves the cokernel by
lem-sp-exact-functor-preserves-homology. Coproduct preservation and additivity
identify the image presentation with the presentation of the image diagram.
The resulting cocone is a colimit cocone, so every small colimit is preserved. -/
theorem preservesColimitsOfSize_of_exact_additive_coproducts
    (C : Type uC) (D : Type uD) [Category.{vC} C] [Category.{vD} D]
    [Abelian C] [Abelian D]
    [IsGrothendieckAbelian.{s} C] [IsGrothendieckAbelian.{s} D]
    (Φ : C ⥤ D) [Φ.Additive] (hΦ : exactFunctor C D Φ)
    [∀ I : Type s, PreservesColimitsOfShape (Discrete I) Φ] :
    PreservesColimitsOfSize.{s, s} Φ := by
  sorry

end CategoryTheory

namespace AlgebraicGeometry.Scheme.ProEt

/-- Hypercohomology on a qcqs scheme is computed by the given affine weakly
contractible hypercover and commutes with uniformly bounded-below filtered colimits.
The finite diagonal uses exactly pairs (n,m) with n ≥ 0, m ≥ a, n+m=q. The
cohomology is that of the unbounded right derived functor of abelian sections;
`Plus` restricts its inputs to complexes with an integer strict lower bound.
Source: blueprint main-20261015, sk-lem-bounded-continuity-sections.md, clauses (1)-(3)
(blueprint: det-lem-bounded-continuity-sections).

Proof:
1. The preceding cokernel-presentation argument proves the general assertion of
   (1). Apply det-proper-heart-continuity-sections separately to each affine
   weakly contractible W_n. Evaluation is exact and preserves all colimits,
   hence the filtered colimits in the first conclusion below.
2. Apply det-pe-hypercover-complex to this given W, with U the identity object
   of Y.ProEt and coefficients R. It gives the natural derived isomorphism
   below. Apply the derived homology functor and its factorization through Q
   to obtain the cohomology comparison in every integer degree.
3. For K vanishing below a, only m=q-n ≥ a and n ≥ 0 contribute. Thus
   0 ≤ n ≤ q-a, a finite interval; for q<a it is empty. Remove zero summands
   from the coproduct total to get the displayed finite coproduct. For negative
   a this is the same first-quadrant total after reindexing m by m-a; the
   differential remains delta + (-1)^n d_K, without an extra shift sign.
4. Form the complex colimit degreewise. Below a its terms are colimits of
   zero objects, hence zero. Evaluation comparisons identify its sections
   with the colimits of the sections, compatibly with every face restriction
   and coefficient differential. Interchanging coproducts with colimits gives
   an isomorphism from the colimit of the totals to the total of the colimit.
5. By lem-weil-pbc-filtered-colimit-abelian-groups-exact, filtered colimits
   preserve the exact sequences of cycles, boundaries and cohomology. The
   kernel of the outgoing differential is the colimit of cycles, the image
   of the incoming differential is the colimit of boundaries, and their
   quotient is the colimit of cohomology.
6. Naturality of det-pe-hypercover-complex identifies each cocone leg with
   the hypercohomology map of the original complex colimit leg. Uniqueness
   in def-weil-pbc-category-colimit identifies the composite with colimit.post,
   proving that the actual canonical comparison is invertible. -/
theorem boundedContinuitySections
    (Y : Scheme.{t}) [CompactSpace Y] [QuasiSeparatedSpace Y]
    (R : Sheaf (topology Y) RingCat.{u})
    (W : SimplicialObject (Over (ProEt.mk (𝟙 Y))))
    [HasDerivedCategory.{wA} (ringedSiteModules.{max u v (t + 1)} R)]
    [HasDerivedCategory.{wB} AddCommGrpCat.{max u v (t + 1)}]
    (haff : ∀ n : ℕ, IsAffine (W _⦋n⦌).left.left)
    (hqc : ∀ n : ℕ, CompactSpace (W _⦋n⦌).left.left)
    (hweak : ∀ n : ℕ,
      (topology Y).IsWeaklyContractible.{max u v (t + 1)} (W _⦋n⦌).left)
    (hzero : Presieve.singleton (W _⦋0⦌).hom ∈ (precoverage Y) (ProEt.mk (𝟙 Y)))
    (hmatching : ∀ n : ℕ,
      ∃ (c : Cone (SimplicialObject.properFaceDiagram W (n + 1)))
        (μ : W _⦋n + 1⦌ ⟶ c.pt),
        Nonempty (IsLimit c) ∧ Presieve.singleton μ.left ∈ (precoverage Y) c.pt.left ∧
          ∀ b : SimplicialObject.ProperFaceCategory (n + 1),
            μ ≫ c.π.app (op b) = W.map b.obj.hom.op) :
    (∀ n : ℕ, PreservesFilteredColimitsOfSize.{max u v (t + 1), max u v (t + 1)}
      (hypercoverAbelianEvaluation.{t, u, v} Y R (W _⦋n⦌).left)) ∧
    Nonempty
      (CochainComplex.Plus.ι (ringedSiteModules.{max u v (t + 1)} R) ⋙ DerivedCategory.Q ⋙
          (Functor.rightDerivedFunctorOfQuasiIsoResolutions
            (hypercoverAbelianEvaluation.{t, u, v} Y R (ProEt.mk (𝟙 Y))))
            (moduleQuasiIsoKInjectiveResolutions.{t, u, v} Y R) ≅
        CochainComplex.Plus.ι (ringedSiteModules.{max u v (t + 1)} R) ⋙
          hypercoverAbelianTotal.{t, u, v} Y R (ProEt.mk (𝟙 Y)) W ⋙ DerivedCategory.Q) ∧
    (∀ q : ℤ, Nonempty
      (CochainComplex.Plus.ι (ringedSiteModules.{max u v (t + 1)} R) ⋙ DerivedCategory.Q ⋙
          (Functor.rightDerivedFunctorOfQuasiIsoResolutions
            (hypercoverAbelianEvaluation.{t, u, v} Y R (ProEt.mk (𝟙 Y))))
            (moduleQuasiIsoKInjectiveResolutions.{t, u, v} Y R) ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{max u v (t + 1)} q ≅
        CochainComplex.Plus.ι (ringedSiteModules.{max u v (t + 1)} R) ⋙
          hypercoverAbelianTotal.{t, u, v} Y R (ProEt.mk (𝟙 Y)) W ⋙
          HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v (t + 1)} (.up ℤ) q)) ∧
    (∀ (K : CochainComplex (ringedSiteModules.{max u v (t + 1)} R) ℤ)
      (a : ℤ), (∀ m : ℤ, m < a → IsZero (K.X m)) → ∀ q : ℤ,
      Finite {p : ℕ × ℤ // a ≤ p.2 ∧ (p.1 : ℤ) + p.2 = q} ∧
      Nonempty
        (((hypercoverAbelianTotal.{t, u, v} Y R (ProEt.mk (𝟙 Y)) W).obj K).X q ≅
          ∐ (fun p : {p : ℕ × ℤ // a ≤ p.2 ∧ (p.1 : ℤ) + p.2 = q} ↦
            (hypercoverAbelianEvaluation.{t, u, v} Y R (W _⦋p.val.1⦌).left).obj (K.X p.val.2)))) ∧
    (∀ (I : Type (max u v (t + 1))) [SmallCategory I] [IsFiltered I]
      (K : I ⥤ CochainComplex (ringedSiteModules.{max u v (t + 1)} R) ℤ)
      (a : ℤ), (∀ (i : I) (m : ℤ), m < a → IsZero ((K.obj i).X m)) → ∀ q : ℤ,
      IsIso (colimit.post K
        (DerivedCategory.Q ⋙
          (Functor.rightDerivedFunctorOfQuasiIsoResolutions
            (hypercoverAbelianEvaluation.{t, u, v} Y R (ProEt.mk (𝟙 Y))))
            (moduleQuasiIsoKInjectiveResolutions.{t, u, v} Y R) ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{max u v (t + 1)} q))) := by
  sorry

end AlgebraicGeometry.Scheme.ProEt
