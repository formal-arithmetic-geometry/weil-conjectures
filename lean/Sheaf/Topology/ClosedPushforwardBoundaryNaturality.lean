/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.Sheaves.Functors
public import Sheaf.Topology.AbelianCohomologyDeltaFunctor
import Sheaf.CategoryTheory.DeltaFunctor
import Sheaf.CategoryTheory.EffaceableDeltaFunctorUniversal
import Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor
import Sheaf.Topology.ClosedImmersionPushforwardCohomology
import Sheaf.Topology.ClosedImmersionPushforwardExact

/-!
# Closed-pushforward cohomology comparison and boundaries

Source: Stacks Project, Cohomology of Sheaves, Lemma 02UV and naturality of
cohomological delta-functors (blueprint: lem-sc-closed-pushforward-boundary-naturality).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

namespace TopCat.Sheaf

/-- The canonical closed-immersion comparison is the unique morphism of delta-functors
extending the identity on global sections. Its components are isomorphisms, commute
with boundaries, and carry the boundary of one to the boundary of one in the pulled-back
constant-quotient sequence.
Source: Stacks Project, Lemma 02UV
(blueprint: lem-sc-closed-pushforward-boundary-naturality).

Proof:
1. Exactness of closed direct image gives every image short exact sequence
(lem-sc-closed-immersion-pushforward-exact).
2. Compose the canonical cohomology delta-functor on X with this exact direct image.
The resulting delta-functor T has the image-sequence boundaries and in degree zero
identifies with global sections on Z (def-sc-topological-abelian-cohomology).
3. The source is universal by lem-weil-pbc-right-derived-universal-delta-functor.
The target is effaceable: embed a sheaf in an injective on Z; positive cohomology of its
direct image vanishes by lem-sc-cohomology-closed-immersion-pushforward. Thus T is
universal by lem-weil-pbc-effaceable-delta-functor-universal.
4. The two universal properties give the unique extension of the degree-zero identity
and its inverse. Consequently every component is an isomorphism.
5. The defining equation for a delta-functor morphism gives compatibility with boundaries
(def-weil-pbc-delta-functor). For the constant quotient, the restriction map sends one
to one. The pullback square and exactness identify the kernel map φ.τ₁ with the canonical
kernel isomorphism. Naturality of the boundary transports its boundary of one along
φ.τ₁ to the image-sequence boundary, hence to the compared boundary on Z. -/
theorem closed_pushforward_boundary_naturality
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    ∃ hex : ∀ (S : ShortComplex ((Z : TopCat).Sheaf AddCommGrpCat.{u})),
        S.ShortExact →
          (S.map (pushforward AddCommGrpCat.{u} (Scheme.forgetToTop.map i))).ShortExact,
    ∃ T : CohomologicalDeltaFunctor ((Z : TopCat).Sheaf AddCommGrpCat.{u})
        AddCommGrpCat.{u + 1},
    ∃ e : ∀ n : ℕ, T.F n ≅
        pushforward AddCommGrpCat.{u} (Scheme.forgetToTop.map i) ⋙
          abelianCohomologyFunctor (X : TopCat) n,
      (∀ (S : ShortComplex ((Z : TopCat).Sheaf AddCommGrpCat.{u}))
        (hS : S.ShortExact) (n : ℕ),
        T.delta S hS n ≫ (e (n + 1)).hom.app S.X₁ =
          (e n).hom.app S.X₃ ≫ abelianCohomologyBoundary (X : TopCat)
            (S.map (pushforward AddCommGrpCat.{u} (Scheme.forgetToTop.map i)))
            (hex S hS) n) ∧
      ∃ t : CohomologicalDeltaFunctor.Hom (abelianCohomologyDeltaFunctor (Z : TopCat)) T,
        (∀ (D : (Z : TopCat).Sheaf AddCommGrpCat.{u})
          (c : (abelianCohomologyFunctor (Z : TopCat) 0).obj D),
          abelianCohomologySection (X : TopCat)
            ((pushforward AddCommGrpCat.{u} (Scheme.forgetToTop.map i)).obj D)
            ((e 0).hom.app D ((t.app 0).app D c)) =
          abelianCohomologySection (Z : TopCat) D c) ∧
        (∀ t' : CohomologicalDeltaFunctor.Hom
            (abelianCohomologyDeltaFunctor (Z : TopCat)) T,
          (∀ (D : (Z : TopCat).Sheaf AddCommGrpCat.{u})
            (c : (abelianCohomologyFunctor (Z : TopCat) 0).obj D),
            abelianCohomologySection (X : TopCat)
              ((pushforward AddCommGrpCat.{u} (Scheme.forgetToTop.map i)).obj D)
              ((e 0).hom.app D ((t'.app 0).app D c)) =
            abelianCohomologySection (Z : TopCat) D c) → t' = t) ∧
        (∀ n : ℕ, IsIso (t.app n)) ∧
        (∀ (S : ShortComplex ((Z : TopCat).Sheaf AddCommGrpCat.{u}))
          (hS : S.ShortExact) (c : (abelianCohomologyFunctor (Z : TopCat) 0).obj S.X₃),
          (e 1).hom.app S.X₁
              ((t.app 1).app S.X₁ (abelianCohomologyBoundary (Z : TopCat) S hS 0 c)) =
            abelianCohomologyBoundary (X : TopCat)
              (S.map (pushforward AddCommGrpCat.{u} (Scheme.forgetToTop.map i))) (hex S hS) 0
              ((e 0).hom.app S.X₃ ((t.app 0).app S.X₃ c))) ∧
        (∀ (S : ShortComplex ((Z : TopCat).Sheaf AddCommGrpCat.{u})) (hS : S.ShortExact)
          (a : S.X₃ ≅ (constantSheaf (Opens.grothendieckTopology Z)
            AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))
          (P : ShortComplex ((X : TopCat).Sheaf AddCommGrpCat.{u})) (hP : P.ShortExact)
          (b : P.X₃ ≅ (constantSheaf (Opens.grothendieckTopology X)
            AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))
          (φ : P ⟶ S.map (pushforward AddCommGrpCat.{u} (Scheme.forgetToTop.map i)))
          (hpb : IsPullback φ.τ₂ P.g
            ((S.map (pushforward AddCommGrpCat.{u} (Scheme.forgetToTop.map i))).g) φ.τ₃)
          (cZ : (abelianCohomologyFunctor (Z : TopCat) 0).obj S.X₃)
          (cX : (abelianCohomologyFunctor (X : TopCat) 0).obj P.X₃)
          (hcZ : a.hom.hom.app (op ⊤) (abelianCohomologySection (Z : TopCat) S.X₃ cZ) =
            ((constantSheafAdj (Opens.grothendieckTopology Z) AddCommGrpCat.{u}
              isTerminalTop).unit.app (AddCommGrpCat.of (ULift.{u} ℤ))) (ULift.up 1))
          (hcX : b.hom.hom.app (op ⊤) (abelianCohomologySection (X : TopCat) P.X₃ cX) =
            ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
              isTerminalTop).unit.app (AddCommGrpCat.of (ULift.{u} ℤ))) (ULift.up 1))
          (hu : φ.τ₃.hom.app (op ⊤) (abelianCohomologySection (X : TopCat) P.X₃ cX) =
            abelianCohomologySection (Z : TopCat) S.X₃ cZ),
          (abelianCohomologyFunctor (X : TopCat) 1).map φ.τ₁
              (abelianCohomologyBoundary (X : TopCat) P hP 0 cX) =
            (e 1).hom.app S.X₁ ((t.app 1).app S.X₁
              (abelianCohomologyBoundary (Z : TopCat) S hS 0 cZ))) := by
  sorry

end TopCat.Sheaf
