/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.Paper.ProfiniteTestObjectFunctor
public import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.Spectral.Basic
import Sheaf.AlgebraicGeometry.CoproductCopiesMorphismsClopen

/-!
# Maps to relative profinite test schemes

Source: Bhatt–Scholze, Section 4.2, Lemma 4.2.13(1), finite-quotient argument;
RefactorInstruction, Section 4, proof of Lemma point-eval
(blueprint: lem-weil-pbc-proetale-point-components-maps).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProEtale

/-- The component quotient of an affine weakly contractible pro-etale object is profinite.
Maps to `X[S]` are naturally continuous maps from this quotient to `S`.
Weak contractibility means surjectivity on sections of every epimorphism of set sheaves;
the sheaf values live in the larger universe of the small-site convention.
The single family `e` is covariant in profinite targets and contravariant in these objects.

Source: Bhatt–Scholze, Section 4.2, Lemma 4.2.13(1), with the finite-quotient argument;
RefactorInstruction, Section 4, proof of Lemma point-eval
(blueprint: lem-weil-pbc-proetale-point-components-maps).

Proof for stage 3:
1. An affine scheme is compact and quasi-separated, hence spectral by
   lem-weil-pbc-qcqs-scheme-spectral and def-weil-spectral-space. By
   lem-weil-pbc-quasicompact-components-clopen-intersection, distinct components are
   separated by clopens. Clopens are saturated for the component quotient, giving
   Hausdorffness and total disconnectedness. Compactness descends along the quotient.
2. For a finite discrete target, lem-weil-pbc-profinite-test-object-functor identifies
   the test scheme with a coproduct of copies of X. Use
   lem-galois-coproduct-copies-morphisms-clopen to identify its maps with continuous
   finite-valued functions. Such functions factor uniquely through the component
   quotient, and the quotient topology gives continuity of that factor.
3. Present S by its finite quotients. The limit clause of
   lem-weil-pbc-profinite-test-object-functor identifies scheme maps with compatible
   families of finite-stage maps, hence with compatible continuous finite-stage functions.
4. The topological inverse-limit property identifies these families with continuous
   maps to S. Basic opens give continuity. Empty targets give no maps from a nonempty
   source and a unique map from an empty source; singleton targets give a unique map.
5. Precomposition pulls back finite-stage clopen fibres and induces the usual map on
   component quotients. For a target map, compose with any finite quotient of its target
   and factor this finite-valued function through a finite quotient of its source.
   The test-object functor respects these maps. Equality at every finite quotient proves
   both naturality identities. -/
theorem proEtale_point_components_maps (X : Scheme.{u}) :
    (∀ (U : X.ProEt), IsAffine U.left →
      (∀ (F G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) (f : F ⟶ G),
        Epi f → Function.Surjective (f.hom.app (op U))) →
      CompactSpace (ConnectedComponents U.left) ∧
        T2Space (ConnectedComponents U.left) ∧
        TotallyDisconnectedSpace (ConnectedComponents U.left)) ∧
    ∃ e : ∀ (U : X.ProEt), IsAffine U.left →
        (∀ (F G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) (f : F ⟶ G),
          Epi f → Function.Surjective (f.hom.app (op U))) →
        ∀ S : Profinite.{u},
          (U ⟶ (profiniteToProEtOf X).obj S) ≃ C(ConnectedComponents U.left, S),
      (∀ (U : X.ProEt) (hU : IsAffine U.left)
        (wU : ∀ (F G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) (f : F ⟶ G),
          Epi f → Function.Surjective (f.hom.app (op U)))
        (S T : Profinite.{u}) (b : S ⟶ T) (f : U ⟶ (profiniteToProEtOf X).obj S),
        e U hU wU T (f ≫ (profiniteToProEtOf X).map b) =
          b.hom.hom.comp (e U hU wU S f)) ∧
      (∀ (U V : X.ProEt) (hU : IsAffine U.left) (hV : IsAffine V.left)
        (wU : ∀ (F G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) (f : F ⟶ G),
          Epi f → Function.Surjective (f.hom.app (op U)))
        (wV : ∀ (F G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) (f : F ⟶ G),
          Epi f → Function.Surjective (f.hom.app (op V)))
        (a : V ⟶ U) (S : Profinite.{u}) (f : U ⟶ (profiniteToProEtOf X).obj S),
        e V hV wV S (a ≫ f) = (e U hU wU S f).comp
          ⟨a.left.continuous.connectedComponentsMap,
            a.left.continuous.connectedComponentsMap_continuous⟩) := by
  sorry

end AlgebraicGeometry.ProEtale
