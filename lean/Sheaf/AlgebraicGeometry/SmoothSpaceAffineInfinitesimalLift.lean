/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O2
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Thickening
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.CategoryTheory.Sites.Torsor
import WeilConjectures.AlgebraicGeometry.EtaleAffineQcoherentULift

/-! # Affine infinitesimal lifting for smooth morphisms of algebraic spaces

Source: Stacks Project, More on Morphisms of Spaces, Tag 04AM (smooth implies
formally smooth), with Tag 060G and definition-formally-smooth-etale-unramified
(blueprint: lem-sfb-smooth-space-affine-infinitesimal-lift).

Smoothness is the existing compatible étale chart test applied to scheme smoothness.
Maps from test schemes are natural transformations of presheaves on schemes over `S`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- Smooth algebraic-space morphisms lift affine square-zero test diagrams globally.
There is no separatedness or quasi-compactness assumption on the space morphism.
Source: Stacks Project, Tag 04AM, implication (1) to (2), and Tag 060G
(blueprint: lem-sfb-smooth-space-affine-infinitesimal-lift).

Proof:
1. Smoothness implies local finite presentation by
   lem-sfb-stack-chartwise-smooth-etale-calculus. Apply
   lem-sfb-space-infinitesimal-lift-pseudotorsor to obtain the sheaf of specified lifts
   and its simply transitive action by a quasi-coherent translation module, wherever
   lifts exist. This step does not assert existence of a lift.
2. Form Z = X ×_Y T and the map T₀ → Z given by (a₀,j), using
   lem-trf-space-fibre-products-etale-covers. Base change preserves smoothness by
   lem-sfb-stack-chartwise-smooth-etale-calculus. Choose a surjective étale scheme
   atlas U → Z using def-trf-algebraic-space. Its composite U → T is smooth by the
   same calculus and hence formally smooth as a scheme map (def-sbc-smooth-morphisms).
3. Pull the atlas back to T₀, obtaining a surjective étale scheme W₀ → T₀ and a map
   W₀ → U. By sbc-lem-thickening-etale-site this étale cover lifts to W → T, with
   W ×_T T₀ identified with W₀ and W → T still surjective. Cover W by affine opens Wᵢ.
4. Each Wᵢ ×_T T₀ → Wᵢ is an affine first order thickening: its ideal is generated
   by the original square-zero ideal, so its square is zero
   (def-sbc-first-order-thickening). Scheme formal smoothness
   (def-sbc-smooth-morphisms) lifts Wᵢ ×_T T₀ → U to Wᵢ → U over T. Composing with
   U → Z → X gives sections of the sheaf of specified lifts over the covering Wᵢ → T.
5. Local nonemptiness and the action from lem-sfb-space-infinitesimal-lift-pseudotorsor
   make that sheaf a torsor (def-sc-gm-torsor). Its quasi-coherent translation module
   has vanishing first étale cohomology on affine T by lem-sc-etale-affine-qcoherent.
   By lem-sc-torsor-h1 the torsor is trivial. Its global zero section gives the required
   S-morphism a, whose defining conditions are exactly a ≫ f = b and j ≫ a = a₀.
   Neither separatedness nor quasi-compactness was used. -/
theorem smooth_affine_infinitesimal_lift {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (hf : MapIsLocally (@Smooth) f)
    (T₀ T : Over S) [IsAffine T₀.left] [IsAffine T.left] (j : T₀ ⟶ T)
    (hj : IsFirstOrderThickening j.left)
    (a₀ : yoneda.obj T₀ ⟶ X.obj.obj) (b : yoneda.obj T ⟶ Y.obj.obj)
    (hcomm : a₀ ≫ f.hom.hom = yoneda.map j ≫ b) :
    ∃ a : yoneda.obj T ⟶ X.obj.obj,
      a ≫ f.hom.hom = b ∧ yoneda.map j ≫ a = a₀ := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
