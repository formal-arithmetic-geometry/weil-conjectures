/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O4
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Mathlib.AlgebraicGeometry.OpenImmersion

import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentPushforward
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleFpDirectedApproximation
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Extending a finite-type submodule from an open algebraic subspace

Source: Stacks Project, Limits of Algebraic Spaces, Tag 0853 (lemma-extend)
(blueprint: lem-sfb-space-finite-type-submodule-extension).

The canonical tensor pullback along the open immersion is restriction to the small
étale site of the open. The existing normalized étale-restriction comparison identifies
it with precomposition, retaining the given inclusion into the ambient module.
Submodules are represented by monomorphisms, and equality of the restricted submodules
is expressed by an isomorphism commuting with their inclusions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- A finite-type quasi-coherent submodule on a quasi-compact open extends inside
its given ambient quasi-coherent module on a qcqs algebraic space.
Source: Stacks Project, Limits of Algebraic Spaces, Tag 0853 (lemma-extend)
(blueprint: lem-sfb-space-finite-type-submodule-extension).

Proof:
1. The point and atlas notions of quasi-compactness agree. Quasi-separatedness of X
   and quasi-compactness of W make j quasi-compact. Its diagonal is the identity,
   hence a closed immersion, so j is separated. Direct images of G and F restricted
   to W are therefore quasi-coherent; restriction preserves local presentations.
2. With i the direct image of the prescribed inclusion and r the adjunction unit,
   take H = ker(i - r : j_*G ⊕ F → j_*(F restricted to W)). Kernels and finite sums
   preserve quasi-coherence. The map i is injective on chart sections, so projection
   p : H → F is injective. On charts over W, direct image restricts to the original
   sections; thus H restricted to W is G, with p the prescribed inclusion.
3. Write H as a small filtered colimit of finitely presented quasi-coherent modules
   E_a. Choose an affine surjective étale atlas T of W. Affine-chart calculus computes
   H(T) as the filtered colimit of E_a(T), and identifies it with the finitely
   generated module G(T).
4. Lift a finite generating family to finitely many stages and choose a common
   receiving stage a. For an empty generating family choose any stage of the
   nonempty filtered category. Then E_a(T) → H(T) is surjective. Its quasi-coherent
   cokernel vanishes on T, hence on W by descent, so E_a restricted to W surjects
   onto G.
5. Take G' to be the image of E_a → H → F. Images are quasi-coherent. On affine
   charts the images of finitely many generators generate the image, making G'
   finite type. Over W the image of the surjection onto G followed by its prescribed
   inclusion is precisely G. These sectionwise image equalities commute with
   restrictions, giving the displayed isomorphism compatible with both inclusions. -/
theorem exists_finiteType_submodule_extension
    {S : Scheme.{u}} (X W : AlgebraicSpace S) (j : W ⟶ X)
    (hXqc : ∃ (T : Over S) (a : yoneda.obj T ⟶ X.obj.obj),
      CompactSpace T.left ∧ IsEtale a ∧ IsSurjective a)
    (hXqs : IsAbsolutelyQuasiSeparated X)
    (hj : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) j.hom.hom)
    (hWqc : ∃ (T : Over S) (a : yoneda.obj T ⟶ W.obj.obj),
      CompactSpace T.left ∧ IsEtale a ∧ IsSurjective a)
    (F : X.Modules) [F.IsQuasicoherent]
    (G : W.Modules) [G.IsQuasicoherent] [G.IsFiniteType]
    (ι : G ⟶ (moduleTensorPullback j).obj F) [Mono ι] :
    ∃ (G' : X.Modules), G'.IsQuasicoherent ∧ G'.IsFiniteType ∧
      ∃ (ι' : G' ⟶ F), Mono ι' ∧
        ∃ (e : (moduleTensorPullback j).obj G' ≅ G),
          (moduleTensorPullback j).map ι' = e.hom ≫ ι := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
