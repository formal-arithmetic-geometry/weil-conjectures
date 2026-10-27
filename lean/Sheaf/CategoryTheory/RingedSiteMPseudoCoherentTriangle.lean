module

public import Sheaf.Algebra.Homology.RingedSitePseudoCoherent
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.Algebra.Homology.StrictPerfectLocalActual
import Sheaf.Algebra.Homology.RingedSiteStrictPerfectLocalLift
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Degreewise pseudo-coherence in ringed-site triangles

Source: Stacks Project, sites-cohomology.tex, Tag 08FV (lemma-cone-pseudo-coherent),
parts (1), (2), and (3) (blueprint: lem-sfb-ringed-site-m-pseudocoherent-triangle).
-/

@[expose] public section

set_option autoImplicit false

universe c v r w w'

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace SheafOfModules

/-- The three shifted two-out-of-three assertions for local strictly perfect approximation.
Source: Stacks Project, Tag 08FV (lemma-cone-pseudo-coherent), parts (1)--(3)
(blueprint: lem-sfb-ringed-site-m-pseudocoherent-triangle).

Proof:
1. Fix an arbitrary site object and restrict the distinguished triangle to successive
   covering slices. Exact restriction commutes with cohomology and induces a triangulated
   derived functor (lem-pur-site-restriction-module-adjunction-exact,
   lem-weil-pbc-exact-functor-derived-factorization,
   lem-weil-pbc-exact-functor-complex-cohomology). Choose strictly perfect approximations
   P to K through m+1 and Q to L through m on a common covering.
2. Replace P by its stupid truncation in degrees at least m+1. It remains strictly
   perfect, with cohomology unchanged above m+1 and surjecting in degree m+1, because
   removing incoming boundaries leaves the cycles unchanged.
3. Represent L by a complex F. After refining the covering, realize both approximation
   arrows to L by actual chain maps to F using lem-sfb-ringed-site-strict-perfect-local-actual.
   Apply lem-sfb-ringed-site-strict-perfect-local-lift to lift the map from P through
   Q to F up to homotopy. The support bound on P and the cohomology bounds on Q give
   its hypotheses. Localization identifies homotopic maps, giving the commutative square.
4. The mapping cone of P to Q has terms Q in degree j plus P in degree j+1, hence is
   bounded with finite-free-summand terms. TR3 completes the square to a morphism from
   its distinguished cone triangle to the given triangle (def-weil-triangulated-category).
5. The natural long exact cohomology sequences give a cohomology ladder
   (lem-sf-derived-homology-long-exact, lem-weil-pbc-derived-cohomology-ladder).
   Above m, the five lemma gives an isomorphism on the cone comparison, with the
   first vertical arrow epic, the second and fourth invertible, and the fifth monic
   (lem-weil-pbc-five-lemma). At m, the epi four lemma gives an epimorphism, using the
   first and third vertical arrows epic and the fourth monic (lem-pc-four-lemma-epi).
6. Compose the successive covers. This constructs the required local strictly perfect
   approximation to M on a cover of every object, proving (1).
7. Reindexing complexes gives: X shifted by s is a-pseudo-coherent exactly when X is
   (a+s)-pseudo-coherent. Inverse rotation gives M[-1] to K to L, so (1) proves (2).
   Rotation gives L to M to K[1], so (1) and the shift formula prove (3). Rotation
   signs do not change the cohomology isomorphism or epimorphism conditions.
-/
theorem mPseudoCoherent_distinguishedTriangle
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    [HasDerivedCategory.{w}
      (ringedSiteModules.{max c v r} (scalarPerfectRingUnderlying.{c, v, max c v r} J R))]
    [∀ U : C, HasDerivedCategory.{w'}
      (ringedSiteModules.{max c v r} ((scalarPerfectRingUnderlying.{c, v, max c v r} J R).over U))]
    (m : ℤ)
    (T : Triangle (DerivedCategory
      (ringedSiteModules.{max c v r}
        (scalarPerfectRingUnderlying.{c, v, max c v r} J R))))
    (hT : T ∈ distTriang _) :
    (IsMPseudoCoherentOnRingedSite.{c, v, r, w, w'} R (m + 1) T.obj₁ →
      IsMPseudoCoherentOnRingedSite.{c, v, r, w, w'} R m T.obj₂ →
      IsMPseudoCoherentOnRingedSite.{c, v, r, w, w'} R m T.obj₃) ∧
    (IsMPseudoCoherentOnRingedSite.{c, v, r, w, w'} R m T.obj₁ →
      IsMPseudoCoherentOnRingedSite.{c, v, r, w, w'} R m T.obj₃ →
      IsMPseudoCoherentOnRingedSite.{c, v, r, w, w'} R m T.obj₂) ∧
    (IsMPseudoCoherentOnRingedSite.{c, v, r, w, w'} R (m + 1) T.obj₂ →
      IsMPseudoCoherentOnRingedSite.{c, v, r, w, w'} R m T.obj₃ →
      IsMPseudoCoherentOnRingedSite.{c, v, r, w, w'} R (m + 1) T.obj₁) := by
  sorry

end SheafOfModules
