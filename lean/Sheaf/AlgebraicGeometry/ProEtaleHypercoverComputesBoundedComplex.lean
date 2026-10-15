/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleAffineAcyclicHypercover
public import Sheaf.AlgebraicGeometry.ProEtaleHypercoverTotal
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.Algebra.Homology.BoundedBelowInjectiveResolution
import Sheaf.CategoryTheory.DoubleComplexTotal
import Sheaf.Algebra.Homology.FirstQuadrantTotalComparison
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Sheaf.CategoryTheory.RingedHypercoverInjectiveAugmentation
import Sheaf.CategoryTheory.RingedSiteModules

/-!
# Bounded-below derived evaluation by weakly contractible hypercovers

Source: Stacks Project, proetale.tex, Tag 09A2, lemma-compute-cohomology;
sites-cohomology.tex, Tag 0946, lemma-w-contractible
(blueprint: lem-weil-pbc-proetale-hypercover-computes-bounded-complex).
-/

@[expose] public section

universe w u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace AlgebraicGeometry.Scheme.ProEt

/-- A weakly contractible hypercover computes bounded-below derived evaluation.
Source: Stacks Project, Tags 09A2 and 0946, with ringed-module coefficients
(blueprint: lem-weil-pbc-proetale-hypercover-computes-bounded-complex).

The first conjunct gives a comparison for every bounded-below complex and every
bounded-below termwise-injective chain resolution. Its target is precisely the
resolution definition of derived evaluation in the node. The comparisons are
natural under coefficient chain maps and resolution maps commuting up to homotopy.
Taking an identity coefficient map gives independence of the resolution. The
second conjunct is invariance of total sections under bounded-below quasi-isomorphisms.
`CochainComplex.Plus` imposes strict boundedness of terms, not just of cohomology.
No affineness or qcqs hypothesis is imposed on the given hypercover or its base.

Proof for stage 3:
1. `hypercoverTotal` forms the commuting section bicomplex and its coproduct total.
   All face restrictions are linear over `R(W)`. Simplicial identities give delta
   squared zero, and naturality of the coefficient differential gives commutation.
   Mathlib's total signs are delta plus `(-1)^p` times that differential. A lower
   bound N leaves at most r-N+1 nonzero summands in degree r, none below N.
2. At each weakly contractible term, evaluation is exact: kernels are sectionwise;
   module epimorphisms are locally surjective by the abelian- and set-sheaf
   epimorphism criteria. Weak contractibility provides sectionwise lifts.
3. Apply lem-sc-bounded-below-injective-resolution on the chosen small skeleton
   to obtain a bounded-below termwise-injective K-injective resolution. For a
   comparison of two complexes choose a common lower bound M and relabel q=t+M.
4. Apply lem-sc-first-quadrant-total-column-comparison to the transposed
   section bicomplex map of a resolution. The signed interchange `(-1)^(pt)`
   identifies the two total conventions. Thus T(E) to T(J) is a quasi-isomorphism.
5. Apply lem-weil-pbc-ringed-hypercover-injective-augmentation in each coefficient
   degree of J. This uses injectivity as module sheaves, without claiming that
   the underlying abelian sheaves are injective. Each augmented row is acyclic.
6. Apply the other first-quadrant comparison to the augmentation J(W) to T(J).
   It is a quasi-isomorphism. Invert it after localization and compose with
   Q(T(E) to T(J)) to obtain the comparison to Q(J(W)).
7. The K-injective localization-Hom bijection represents every derived resolution
   map by a chain map, uniquely up to homotopy. A coefficient homotopy h gives
   total homotopy `(-1)^p h(U_p)`: horizontal terms cancel and vertical terms are
   dh+hd. Augmentation is strictly natural. These facts give the displayed
   naturality equation, independence of resolutions and composition compatibility.
8. A bounded-below coefficient quasi-isomorphism is a quasi-isomorphism at each
   weakly contractible term by step 2. Repeat step 4 with a common lower bound to
   prove the final chain-level quasi-isomorphism assertion. -/
theorem hypercover_computes_boundedBelow_complex (X : Scheme.{u})
    (R : Sheaf (topology X) CommRingCat.{u + 1}) (W : X.ProEt)
    (U : SimplicialObject (Over W))
    [HasDerivedCategory.{w} (ModuleCat.{u + 1}
      (((sheafCompose (topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj.obj (op W)))]
    (hweak : ∀ (n : ℕ) (F G : Sheaf (topology X) (Type (u + 1))) (f : F ⟶ G),
      Epi f → Function.Surjective (f.hom.app (op (U _⦋n⦌).left)))
    (hzero : Epi ((topology X).yoneda.map (U _⦋0⦌).hom))
    (hone : ∃ c : Fan (fun _ : Fin 2 ↦ U _⦋0⦌), Nonempty (IsLimit c) ∧
      ∃ μ : U _⦋1⦌ ⟶ c.pt,
        (∀ i : Fin 2, μ ≫ c.proj i = U.δ i) ∧
        Epi ((topology X).yoneda.map μ.left))
    (hhigher : ∀ n : ℕ,
      ∃ c : Cone (SimplicialObject.matchingBoundaryIndex U n).multicospan,
        Nonempty (IsLimit c) ∧ ∃ μ : U _⦋n + 2⦌ ⟶ c.pt,
          (∀ i : Fin (n + 3), μ ≫ c.π.app (WalkingMulticospan.left i) = U.δ i) ∧
          Epi ((topology X).yoneda.map μ.left)) :
    (∃ c : ∀ (E J : CochainComplex.Plus (ringedSiteModules.{u + 1}
          ((sheafCompose (topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))),
      (∀ n : ℤ, Injective (J.obj.X n)) →
      (i : E.obj ⟶ J.obj) → QuasiIso i →
      (DerivedCategory.Q.obj ((hypercoverTotal X R W U).obj E.obj) ≅
        DerivedCategory.Q.obj (((SheafOfModules.evaluation _ (op W)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj J.obj)),
      ∀ (E F J L : CochainComplex.Plus (ringedSiteModules.{u + 1}
          ((sheafCompose (topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)))
        (hJ : ∀ n : ℤ, Injective (J.obj.X n))
        (hL : ∀ n : ℤ, Injective (L.obj.X n))
        (i : E.obj ⟶ J.obj) (j : F.obj ⟶ L.obj)
        (hi : QuasiIso i) (hj : QuasiIso j) (f : E ⟶ F) (a : J ⟶ L),
        Nonempty (Homotopy (i ≫ a.hom) (f.hom ≫ j)) →
        DerivedCategory.Q.map ((hypercoverTotal X R W U).map f.hom) ≫
            (c F L hL j hj).hom =
          (c E J hJ i hi).hom ≫ DerivedCategory.Q.map
            (((SheafOfModules.evaluation _ (op W)).mapHomologicalComplex
              (ComplexShape.up ℤ)).map a.hom)) ∧
    (∀ (E F : CochainComplex.Plus (ringedSiteModules.{u + 1}
          ((sheafCompose (topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))) (f : E ⟶ F),
      QuasiIso f.hom → QuasiIso ((hypercoverTotal X R W U).map f.hom)) := by
  sorry

end AlgebraicGeometry.Scheme.ProEt
