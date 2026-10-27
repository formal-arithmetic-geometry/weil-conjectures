/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.IsLimit
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Eventual properness over qcqs scheme bases

Source: Stacks Project, Limits of Spaces, Tag 08K1 in Situation 084W;
Morphisms of Spaces, Tag 04WP
(blueprint: lem-sfb-space-qcqs-base-eventually-proper).

The base is Spec Z in the chosen universe. A cone in its over-category records the
scheme inverse limit, since Spec Z is terminal. The stage schemes need not be affine.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Properness at the limit of qcqs scheme bases with affine transitions implies
properness at every sufficiently late stage for a finitely presented algebraic space.
The two base-change morphisms below are the actual first projections of sheaf
fibre products, with the base scheme in the first factor.
Source: Stacks Project, Limits of Spaces, Tag 08K1, Situation 084W;
Morphisms of Spaces, Tag 04WP
(blueprint: lem-sfb-space-qcqs-base-eventually-proper).

Proof:
1. Choose a finite affine open cover of the distinguished qc scheme using
   lem-pqf-finite-affine-cover-qc-open. Pull it back to each later stage and the limit.
   The restrictions are open by lem-weil-pbc-open-immersion-base-change and still cover.
   They are affine by lem-weil-pbc-affine-morphism-permanence. The restriction of the
   limit is the limit of these affine schemes by lem-weil-pbc-limit-affine-transition.
   The upper tail is nonempty and directed, with the distinguished stage least.
2. On each covering affine open restrict the finitely presented space. Finite
   presentation and limiting properness persist by the separate base-change clauses
   of lem-sfb-space-flat-proper-fp-locality. The universal property of sheaf pullbacks
   from lem-trf-space-fibre-products-etale-covers identifies this restricted system
   with the restrictions of the original stage and limit spaces: on test schemes
   both describe a section of the original space and of the affine open with matching
   images in the distinguished base. Forgetting the redundant coordinates is invertible.
3. Apply lem-sfb-space-eventually-proper to each of these affine-base systems.
   Directedness gives a common bound for their finitely many bounds and the original
   distinguished stage, successively taking binary upper bounds. If the cover is
   empty use the distinguished stage. Every chart pullback is proper at every later stage.
4. The covering open immersions are flat and locally finitely presented: on an affine
   neighbourhood inside the open, the ring and stalk maps are identities. The ring
   presentation has zero generators and relations (def-sbc-locally-finite-presentation),
   and the stalk module is free of rank one (def-weil-flat-morphism). Together with
   joint surjectivity this is an fppf covering (def-pc-fppf-site, def-weil-open-immersion).
   Descend properness by lem-sfb-space-flat-proper-fp-locality at every later stage.
   An empty cover forces an empty base and imposes no local conditions. -/
theorem eventually_proper_over_qcqs_scheme_limit
    {J : Type u} [Preorder J] [Nonempty J] [IsDirected J (· ≤ ·)]
    (D : Jᵒᵖ ⥤ Over (Spec (.of (ULift.{u} ℤ)))) (c : Cone D) (hc : IsLimit c)
    (hqc : ∀ j : J, CompactSpace (D.obj (op j)).left)
    (hqs : ∀ j : J, QuasiSeparatedSpace (D.obj (op j)).left)
    (haff : ∀ (i j : J) (h : i ≤ j), IsAffineHom (D.map (homOfLE h).op).left)
    (j₀ : J) (Z₀ : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
    (f₀ : Z₀ ⟶ schemeSpace (D.obj (op j₀)))
    (hlfp : MapIsLocallyOfFinitePresentation f₀)
    (hfqc : MapIsQuasiCompact f₀.hom.hom)
    (hfqs : MapIsQuasiCompact (pullback.diagonal f₀.hom.hom))
    (hproper : MapIsProper (enlargedFibreProductFst
      (ObjectProperty.homMk
        ((Scheme.fppfTopology.over (Spec (.of (ULift.{u} ℤ)))).yoneda.map
          (c.π.app (op j₀))) : schemeSpace c.pt ⟶ schemeSpace (D.obj (op j₀))) f₀)) :
    ∃ j : J, ∃ hj : j₀ ≤ j, ∀ (k : J) (hk : j ≤ k),
      MapIsProper (enlargedFibreProductFst
        (ObjectProperty.homMk
          ((Scheme.fppfTopology.over (Spec (.of (ULift.{u} ℤ)))).yoneda.map
            (D.map (homOfLE (hj.trans hk)).op)) :
          schemeSpace (D.obj (op k)) ⟶ schemeSpace (D.obj (op j₀))) f₀) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
