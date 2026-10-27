/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalSymmetricGradedAlgebra
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Fiber

/-!
# Lifting a fibre isomorphism as a morphism near the base point

Source: Stacks Project, coherent.tex, lemma-perfect-direct-image and
remark-explain-perfect-direct-image; limits.tex, lemma-descend-invertible-modules.
EGA II, Remark 4.2.7 announces the related projective-bundle classification.
(blueprint: lem-sfb-projective-bundle-fiber-hom-lift)
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.ProjectiveBundlePicardClassification
open Scheme.Modules

/-- A fibre isomorphism of lines lifts as a sheaf morphism above some base open,
whose pullback to the fibre is invertible. Invertibility away from that fibre is
not asserted: the proper shrinking argument is performed by the consumer.

Source: Stacks Project, coherent.tex, lemma-perfect-direct-image and
remark-explain-perfect-direct-image; limits.tex, lemma-descend-invertible-modules.
EGA II, Remark 4.2.7 announces the projective-bundle classification.
(blueprint: lem-sfb-projective-bundle-fiber-hom-lift)

Proof: Restrict to an affine frame neighbourhood for E. For a Noetherian base let
F be the line M dual tensor N. Its fibre is trivial, hence has vanishing first
cohomology by the projective-space structure-sheaf calculation. The projection is
proper and flat by its polynomial charts, and the invertible F is flat over the
base. Apply proper flat fibre-section lifting to the generator defined by the
fibre isomorphism. Tensor-Hom duality turns the lifted section of F into a morphism
M to N over the inverse image of a base open. Its fibre is the original invertible
map, so its pullback along the restricted projection's fibre inclusion is an
isomorphism. No shrinking of the non-invertibility locus is used here.
For an arbitrary affine ring A write it as the directed union of its finite-type
integer subalgebras. The associated projective spaces have affine transition
morphisms and limit the original projective space. Invertible affine-limit descent
places M and N at a common Noetherian stage. The residue-field fibres also form a
limit by residue-field continuity and compatibility of limits with fibre products.
Finite-presentation isomorphism descent places the fibre isomorphism at a later
stage. Lift it as a morphism by the Noetherian argument, and pull the morphism and
its base open back. Pullback preserves isomorphisms and identifies the restricted
fibre with the original fibre, giving the required final condition. Finally view
the open inside the original S via the initial affine frame neighbourhood. There
is no point s on an empty base; no reducedness or global compactness of S is used.
-/
theorem projective_bundle_fiber_hom_lift (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (hr : 2 ≤ r)
    (M N : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj.Modules)
    (hM : M.IsInvertible) (hN : N.IsInvertible) (s : S)
    (e : Nonempty
      ((tensorPullback
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom.fiberι s)).obj M ≅
        (tensorPullback
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom.fiberι s)).obj N)) :
    ∃ (U : S.Opens) (hs : s ∈ U)
      (φ : (tensorPullback
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U).ι).obj M ⟶
        (tensorPullback
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U).ι).obj N),
      IsIso ((tensorPullback
        (((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ∣_ U).fiberι
          (⟨s, hs⟩ : U.toScheme))).map φ) := by
  sorry

end AlgebraicGeometry.ProjectiveBundlePicardClassification
