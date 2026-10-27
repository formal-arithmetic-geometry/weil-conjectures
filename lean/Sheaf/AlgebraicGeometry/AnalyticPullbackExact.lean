/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.AlgebraicGeometry.SmoothAnalytificationCotangent
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.RingTheory.FlatnessFaithfullyFlatExtension
import WeilConjectures.Topology.AbelianSheafShortExactStalkwise
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.RingHom.Flat

/-! # Exactness of analytic pullback for arbitrary algebraic module sheaves

Source: Serre, GAGA, no. 9, Proposition 10, and no. 6, Proposition 3 and its corollary.
(blueprint: lem-sfb-analytic-pullback-exact).

The analytic objects are `SmoothAnalytic.analytify`. Their morphisms are the actual
inverse-image maps followed by extension of scalars, rather than chosen comparison maps.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.SmoothAnalytic

/-- Analytification of a module morphism: inverse image followed by the sheafified
sectionwise map `id ⊗ a`, over the canonical analytification ring map.
Source: Serre, GAGA, no. 9, Definition 2 and Proposition 10
(blueprint: lem-sfb-analytic-pullback-exact). -/
noncomputable def analytifyMap {X : Scheme.{u}} {f : X ⟶ Spec (.of (ULift.{u} ℂ))}
    (D : Data f) {F G : X.Modules} (a : F ⟶ G) : analytify D F ⟶ analytify D G :=
  SheafOfModules.changeOfRingsHom.{u, u, u}
    (CochainComplex.tensorPullbackRingMap D.pi.hom.base D.space.sheaf X.sheaf ⟨D.pi.hom.c⟩)
    (TopCat.Sheaf.inverseImageModule D.pi.hom.base X.sheaf F)
    (TopCat.Sheaf.inverseImageModuleMap D.pi.hom.base X.sheaf F a)

/-- Analytification carries every short exact sequence of algebraic module sheaves to a
short exact sequence of analytic module sheaves. No finite-generation, quasi-coherence
or coherence assumption is imposed.

Source: Serre, GAGA, no. 9, Proposition 10; no. 6, Proposition 3 and its corollary.
(blueprint: lem-sfb-analytic-pullback-exact).

Proof plan, following the five steps of the DAG:
1. At a point a of D.space put x = pi(a), A = O_X,x and B = O_M,a. The canonical
   local-completion comparison (lem-sfb-analytic-local-completion-comparison) gives
   Noetherian local rings and an A-algebra isomorphism of their completions, compatible
   with the actual local ring map A to B.
2. Noetherian local completion is faithfully flat
   (lem-weil-pbc-local-completion-faithfully-flat). The completion of B is flat over A
   through the comparison. Apply lem-trf-flatness-faithfully-flat-extension to A to B
   to the completion of B and the B-module B. The isomorphism C tensor_B B = C shows
   that B is flat over A.
3. Forgetting module structure preserves and reflects exactness: kernels are computed
   sectionwise and cokernels by sheafification (def-weil-sheaf-of-modules-category).
   Apply lem-sc-abelian-sheaf-short-exact-stalkwise to get the short exact stalk sequence
   at x, and use the same criterion on the analytic space.
4. The ringed-topos pullback-stalk comparison (lem-sfb-ringed-topos-pullback-stalk)
   identifies the analytic stalk of F with F_x tensor_A B. Its naturality identifies
   both analytic morphisms with the original stalk morphisms tensored with B.
5. Tensor right exactness (lem-weil-pbc-tensor-right-exact) and flatness of B
   (def-weil-pbc-flat-ring-map) make the tensored stalk sequence short exact. The
   stalk criterion gives the claimed short exact analytic sequence, for arbitrary
   modules, including zero modules and infinite modules. -/
theorem analytify_shortExact {X : Scheme.{u}}
    (f : X ⟶ Spec (.of (ULift.{u} ℂ))) [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [Smooth f] (D : Data f) (S : ShortComplex X.Modules)
    (hS : S.ShortExact) :
    ∃ h : analytifyMap D S.f ≫ analytifyMap D S.g = 0,
      (ShortComplex.mk (analytifyMap D S.f) (analytifyMap D S.g) h).ShortExact := by
  sorry

end AlgebraicGeometry.SmoothAnalytic
