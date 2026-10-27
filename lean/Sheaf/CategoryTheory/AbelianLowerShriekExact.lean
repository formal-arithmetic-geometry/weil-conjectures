/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q133
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.CategoryTheory.SpecialCocontinuousCoverings
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.CategoryTheory.SiteContinuousPushforwardSheaf
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Exactness of abelian lower shriek without terminal objects

Source: Stacks Project, Modules on Sites, Tag 04BH, lemma-exactness-lower-shriek
(blueprint: lem-sfb-abelian-lower-shriek-exact).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- Every left adjoint to abelian sheaf precomposition is additive and exact.

Source: Stacks Project, Modules on Sites, Tag 04BH, hypotheses (a)-(c)
(blueprint: lem-sfb-abelian-lower-shriek-exact).

The cover-image condition and preservation of pullbacks express Stacks continuity
(00WV). The existential continuity witness records the consequence needed to type
Mathlib's precomposition functor. The existential additivity witness allows the
standard `ShortComplex.map` to use its induced preservation of zero morphisms.
Neither witness imposes an additional hypothesis. The coefficient universe contains
both small sites and an arbitrary further universe. No terminal object or local
slice equivalence is required.

Proof:
1. Continuity makes precomposition preserve abelian sheaves
   [lem-weil-pbc-site-continuous-pushforward-sheaf]. The sheafified left Kan
   extension B is its left adjoint
   [lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction]. At V its presheaf
   part P is the colimit over J_V = I_V.op, where I_V consists of pairs
   (U, V ⟶ F(U)). This category is small since both sites are small.
2. A common-source span in J_V reverses to a cospan in I_V. Take its pullback
   in C. Preservation of this pullback supplies the unique arrow V ⟶ F(Q),
   giving a commuting cocone in J_V.
3. A parallel pair in J_V reverses to a parallel pair in I_V. Its equalizer
   in C and preservation of that equalizer give an arrow V ⟶ F(E), hence a
   coequalizing arrow in J_V. Neither construction requires J_V to be nonempty.
4. By [lem-sfb-almost-filtered-abelian-colimits], these two conditions make
   colimits of abelian groups additive and finite-limit-preserving, even for
   the empty category. Presheaf limits are objectwise
   [lem-weil-pbc-presheaf-finite-limits-objectwise], so P preserves finite
   limits. The comparisons commute with restriction, which replaces
   (U, phi) by (U, phi composed with the restriction arrow). Sectionwise
   additivity of the colimit functors makes P additive.
5. Inclusion preserves limits and sheafification preserves finite limits and
   colimits [lem-weil-pbc-sheafification-exact]. Thus B preserves kernels.
   Sheafification preserves zero objects and finite biproduct diagrams, hence
   addition, expressed by diagonal, biproduct and codiagonal. Inclusion is
   additive sectionwise. Consequently B is additive.
6. The two adjunctions identify Hom(A(M), N) with Hom(B(M), N), naturally.
   The identity maps give mutually inverse maps A(M) ≅ B(M); naturality makes
   them a natural isomorphism. Conjugation transports additivity and kernel
   preservation from B to A.
7. For a short exact sequence with maps i and q, kernel preservation makes
   A(i) the kernel of A(q). For h with A(i) followed by h equal to zero,
   transpose h under the adjunction. Naturality and additivity of
   precomposition make its transpose vanish after i. It factors uniquely
   through q. Transpose back to see that A(q) is the cokernel of A(i).
   Therefore the image sequence is short exact. -/
theorem abelianLowerShriek_additive_shortExact
    {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
    (J : Precoverage C) (K : Precoverage D)
    (hJ : J.IsSiteForCoverings) (hK : K.IsSiteForCoverings)
    (F : C ⥤ D) [F.IsCocontinuous J.toGrothendieck K.toGrothendieck]
    (hcover : ∀ (X : C) (R : Presieve X), R ∈ J X → R.map F ∈ K (F.obj X))
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan F]
    [PreservesLimitsOfShape WalkingParallelPair F] :
    ∃ hcontinuous : F.IsContinuous J.toGrothendieck K.toGrothendieck,
      ∀ A : Sheaf J.toGrothendieck AddCommGrpCat.{max u w} ⥤
          Sheaf K.toGrothendieck AddCommGrpCat.{max u w},
        (A ⊣ @sheafPushforwardContinuous C _ D _ F AddCommGrpCat.{max u w} _
          J.toGrothendieck K.toGrothendieck hcontinuous) →
        ∃ _ : A.Additive,
          ∀ S : ShortComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max u w}),
            S.ShortExact → (S.map A).ShortExact := by
  sorry

end CategoryTheory.Functor
