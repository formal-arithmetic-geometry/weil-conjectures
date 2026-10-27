/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q99
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.FinitePushforwardCoherent
import WeilConjectures.AlgebraicGeometry.CoherentModuleLocalOnOpenCover
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
import WeilConjectures.AlgebraicGeometry.AffineMorphismCohomologyEdge
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerCharProper

/-!
# Finite-map locally free projection and coherent Euler comparison

Source: Stacks Project, Cohomology, Tag 01E8, degree zero and its final proof
paragraph; Cohomology of Schemes, Tags 089W, 01XZ and 01Y6; Varieties, Tag 0BEJ
(blueprint: lem-sfb-finite-map-locally-free-euler-comparison).

The projection isomorphism is specified by its action on tensor sections. The edge
map is the recorded identity h-map, and its field linearity is expressed using the
actual structure maps to global functions. Finiteness uses restriction of scalars
on the recorded module-valued cohomology, while Euler characteristics use the
existing `eulerChar`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- Finite locally free pullback, coherent projection, and Euler comparison for a
finite morphism of proper locally Noetherian schemes over a field.
Source: Stacks 01E8 (degree zero), 01C8, 01XZ, 01Y6, 089W and 0BEJ
(blueprint: lem-sfb-finite-map-locally-free-euler-comparison).

Proof:
1. Trivialize E on opens U_i, with finite ranks r_i allowed to vary. On f⁻¹U_i,
its pullback has basis 1 tensor e_ij: the inverse sends a tensor sum b_j e_ij to
(a f-sharp(b_j))_j. These maps respect restrictions and balancing, hence descend
through inverse image and tensor sheafification. Rank one gives invertibility.
2. Finite free modules are quasi-coherent and finite type in these charts.
`pqf-lem-coherent-ft-locnoeth` makes E and its pullback coherent.
`lem-weil-pbc-finite-pushforward-coherent` gives coherence of f_*N.
3. In the same charts each tensor product is a finite sum of the coherent factor.
Use `lem-weil-pbc-coherent-module-local-on-open-cover` and
`lem-weil-pbc-coherent-modules-kernel-cokernel-sum` for coherence of both tensor
products, and finite pushforward coherence for the direct image of the first.
4. The section rule e tensor n maps to eta(e) tensor n is balanced by linearity
of the pullback unit, and respects restriction. Sheafification gives the global
projection map. On every subopen of U_i it is the identity on tuples N(f⁻¹W)^r_i.
5. Apply `lem-sc-module-hom-local-bijective-iso` to these local bijections. The
local inverses agree on overlaps since they invert the same global map. Its
isomorphism is therefore specified by the displayed rule on tensor sections.
6. N and the pulled-back tensor product are quasi-coherent by step 3 and the
locally Noetherian criterion. The finite morphism is affine; apply
`lem-weil-pbc-affine-morphism-cohomology-edge` to the recorded edge maps.
Their global-function linearity restricts to k-linearity because f is over k.
7. `lem-pc-euler-characteristic-well-defined` gives finite dimensions and eventual
vanishing for these coherent modules on X and Y. The edge isomorphisms and the
projection isomorphism give equal dimensions in each degree. Choose a common
vanishing bound and sum with signs (-1)^q using `def-pc-euler-characteristic`.
-/
theorem finite_map_locally_free_euler_comparison
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] [IsProper (Y ↘ Spec (.of k))]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsFinite f]
    (E : Y.Modules) [SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    (N : X.Modules) (hN : RingedSpace.IsCoherent X.toRingedSpace N) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} ((tensorPullback f).obj E) ∧
    (E.IsInvertible → ((tensorPullback f).obj E).IsInvertible) ∧
    RingedSpace.IsCoherent Y.toRingedSpace E ∧
    RingedSpace.IsCoherent X.toRingedSpace ((tensorPullback f).obj E) ∧
    RingedSpace.IsCoherent Y.toRingedSpace ((pushforward f).obj N) ∧
    RingedSpace.IsCoherent X.toRingedSpace ((tensorPullback f).obj E ⊗ N) ∧
    RingedSpace.IsCoherent Y.toRingedSpace
      ((pushforward f).obj ((tensorPullback f).obj E ⊗ N)) ∧
    RingedSpace.IsCoherent Y.toRingedSpace (E ⊗ (pushforward f).obj N) ∧
    (∃ α : E ⊗ (pushforward f).obj N ≅
        (pushforward f).obj ((tensorPullback f).obj E ⊗ N),
      ∀ (U : Y.Opens) (e : Γ(E, U)) (n : Γ(N, f ⁻¹ᵁ U)),
        α.hom.app U (tmulSection (M := E) (N := (pushforward f).obj N) e n) =
          tmulSection (M := (tensorPullback f).obj E) (N := N)
            (((tensorPullbackSectionAdjunction f).unit.app E).app U e) n) ∧
    (∀ (G : X.Modules), G = N ∨ G = (tensorPullback f).obj E ⊗ N →
      ∀ (q : ℕ), IsIso (moduleCohomologyEdgeMap f G q) ∧
        ∀ (a : k)
          (x : (RingedSpace.moduleCohomology Y.toRingedSpace q).obj
            ((pushforward f).obj G)),
          moduleCohomologyEdgeMap f G q
              (Scheme.globalSectionsRingHom k (X := Y) a • x) =
            Scheme.globalSectionsRingHom k (X := X) a •
              @id ((RingedSpace.moduleCohomology X.toRingedSpace q).obj G)
                (moduleCohomologyEdgeMap f G q x)) ∧
    (∀ (G : X.Modules), G = N ∨ G = (tensorPullback f).obj E ⊗ N →
      (∀ q : ℕ, FiniteDimensional k
        ((ModuleCat.restrictScalars (Scheme.globalSectionsRingHom k (X := X))).obj
          ((RingedSpace.moduleCohomology X.toRingedSpace q).obj G))) ∧
      ∃ b : ℕ, ∀ q : ℕ, b < q →
        Subsingleton ((RingedSpace.moduleCohomology X.toRingedSpace q).obj G)) ∧
    (∀ (G : Y.Modules), G = (pushforward f).obj N ∨
        G = (pushforward f).obj ((tensorPullback f).obj E ⊗ N) ∨
        G = E ⊗ (pushforward f).obj N →
      (∀ q : ℕ, FiniteDimensional k
        ((ModuleCat.restrictScalars (Scheme.globalSectionsRingHom k (X := Y))).obj
          ((RingedSpace.moduleCohomology Y.toRingedSpace q).obj G))) ∧
      ∃ b : ℕ, ∀ q : ℕ, b < q →
        Subsingleton ((RingedSpace.moduleCohomology Y.toRingedSpace q).obj G)) ∧
    N.eulerChar k = ((pushforward f).obj N).eulerChar k ∧
    ((tensorPullback f).obj E ⊗ N).eulerChar k =
      (E ⊗ (pushforward f).obj N).eulerChar k := by
  sorry

end AlgebraicGeometry.Scheme.Modules
