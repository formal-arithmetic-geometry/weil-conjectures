/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q57
-/
module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.FinitePushforwardFiniteType
import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks
import Sheaf.AlgebraicGeometry.FiniteTypeFlatEtaleNeighborhood
import WeilConjectures.RingTheory.HenselianEtaleRetraction
import WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChange
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Module.Projective
import Sheaf.RingTheory.ProjectiveOverLocalFree

/-!
# Free affine neighbourhood at a flat point over a henselian local base

Source: Stacks Project, flat.tex, Tag 05MF,
lemma-flat-finite-type-affine-neighbourhood-projective; henselian specialization
as used in Tag 05U7, lemma-flat-finite-type-local-colimit-free.
(blueprint: lem-sfb-henselian-flat-point-free-affine-neighbourhood).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- A finite-type quasi-coherent sheaf flat at a closed-fibre point has an affine
neighbourhood whose sections are free over the henselian local base, in arbitrary rank.
Source: Stacks Project, flat.tex, Tags 05MF and 05U7.
(blueprint: lem-sfb-henselian-flat-point-free-affine-neighbourhood).

Proof:
1. Choose an affine finite-type chart through x and embed it as a closed subscheme
   i of finite-dimensional affine space P over A, by choosing algebra generators.
   The morphism P to Spec A is finitely presented.
2. The closed pushforward G of F on this chart is quasi-coherent and finite type
   by finite pushforward. Its stalk at i(x) is the original stalk, compatibly with
   the A-action, so it is A-flat. It suffices to find the desired open for G.
3. Apply the finite-type flat-at-a-point theorem (05I5) to P, G, i(x), obtaining
   an elementary etale base neighbourhood and an open over its marked local ring
   on which the pullback of G is finitely presented and relatively flat.
4. The henselian etale retraction (04GG) gives a section through the marked point
   of each affine elementary etale neighbourhood. This section is open and closed
   (024T): the affine morphism is separated because its diagonal comes from the
   surjective multiplication map. Hence its marked local ring is A. The open of
   step 3 is therefore an open in the original P, with the original G.
5. Choose a basic affine open Z inside this open through i(x). Its ring has the
   finite presentation A[t_1,...,t_n,u]/(hu-1). Apply 05ME to Z and G restricted
   to Z to get an affine open W after an elementary etale base change, containing
   the marked point, with sections Q projective over that etale base ring D.
6. Pull W back along the henselian section Spec A to Spec D from step 4. The
   resulting H is affine, open in Z and contains i(x). Quasi-coherent affine
   base change identifies its sections with A tensor_D Q. Pullback composition
   identifies the sheaf with the original restriction of G to H.
7. Tensor split maps exhibiting Q as a summand of a free D-module with A. The
   tensor of the free module is the free A-module on the same basis, so these
   sections are projective over A; no flatness of the retraction is needed.
8. Every projective module over the local ring A is free, with no finite-rank
   restriction (0593). The inverse image U of H under i is affine, open and
   contains x. The direct-image section formula identifies its sections of F
   with the sections of G on H, as A-modules, and transports the free basis. -/
theorem exists_free_affine_neighbourhood_of_henselian_flat_point
    (A : Type u) [CommRing A] [HenselianLocalRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [LocallyOfFiniteType f]
    (F : X.Modules) (hF : Scheme.Modules.IsQuasiCoherentFiniteType F)
    (x : X) (hx : f x = IsLocalRing.closedPoint A)
    (hflat : @Module.Flat A
      (PresheafOfModules.stalkObj X.ringCatSheaf.obj x F.val) _ _
      (Module.compHom _ (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop ≫
        X.presheaf.germ ⊤ x (by trivial)).hom))) :
    ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧
      @Module.Free A Γ(F, U) _ _
        (Module.compHom _ (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop ≫
          X.presheaf.map ((homOfLE le_top : U ⟶ ⊤)).op).hom)) := by
  sorry

end AlgebraicGeometry
