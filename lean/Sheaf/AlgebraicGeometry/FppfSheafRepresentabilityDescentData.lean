/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.AlgebraicGeometry.SchemeCoverDescentDatum
public import Mathlib.CategoryTheory.Sites.Limits
import Sheaf.AlgebraicGeometry.FppfAffineRefinement
import Sheaf.CategoryTheory.SetSheafCoverDescent
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Sheaf.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum

/-! # Locally representable fppf sheaves and scheme descent data

Source: Stacks Project, Descent, Tag 02W5, including clauses (1) and (2)
(blueprint: lem-trf-fppf-sheaf-representability-descent-data).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- An equivalence between scheme descent data and locally representable fppf sheaves,
compatible with all local schemes and transitions, and with geometric effectivity.
Source: Stacks Project, Descent, Tag 02W5, including clauses (1) and (2)
(blueprint: lem-trf-fppf-sheaf-representability-descent-data).

The natural isomorphism of functors identifies the entire given local descent datum with
restriction of the global sheaf, so fixes the overlap maps as well as the local objects.
The second clause explicitly identifies the schemes representing `h_{U_i} × H`.
The last clause uses geometric effectivity, defined using Cartesian scheme squares.

Proof, following the nine steps of the node:
1. Every fppf covering is fpqc. Flatness is part of def-pc-fppf-site; after restricting to
   an affine open, lem-pc-fppf-affine-refinement gives the finitely many affine opens
   required by def-weil-pbc-fpqc-covering (Stacks Tags 022C and 021P).
2. Representable presheaves over every base are fppf sheaves by
   lem-weil-pbc-fpqc-representable-descent. The glued map remains over the base by
   uniqueness applied to the base scheme. This is the sheaf axiom of
   def-weil-pbc-sites-and-cohomology.
3. A representation of h_{U_i} × H induces X_i → U_i by lem-pc-yoneda. Fibres over each
   W → U_i give the representing bijection for H restricted to the slice. Conversely,
   separating maps by their composite to U_i gives the product representation. These
   identifications commute with restrictions (def-pur-localized-ringed-site).
4. By def-pc-fibre-product, both overlap schemes represent h_{U_i} × H × h_{U_j}.
   Lem-pc-representable-unique gives their comparison, preserving both base coordinates.
   Both triple-overlap composites preserve these coordinates and the H coordinate;
   lem-pc-yoneda gives their equality. The same argument defines local maps for sheaf
   maps and proves identities and composition, giving the functor to scheme data.
5. Conversely the local schemes represent sheaves on the slices. The scheme transition
   isomorphisms give compatible sheaf isomorphisms on double slices and satisfy the
   cocycle. Apply lem-pe-set-sheaf-cover-descent (Tags 04TR and 04TQ), with fibre products
   and terminal object T, in def-weil-size-convention's universes, to glue a sheaf H_D.
6. The local representing bijections assemble over all W → U_i into the representation
   of h_{U_i} × H_D by X_i. The gluing equality on double slices identifies the resulting
   transition with the specified one; lem-pc-yoneda gives the full datum isomorphism.
7. Compatible scheme maps induce compatible maps of the local represented sheaves.
   The morphism clause of lem-pe-set-sheaf-cover-descent glues them uniquely. Uniqueness
   gives identities and composition and makes the datum comparison natural.
8. Starting with H, the local identifications glue to G(R(H)) ≅ H. Glue their inverses
   too; uniqueness makes the composites identities. Naturality follows by checking on
   slices and using the same uniqueness. Together with step 7 this gives the equivalence
   and the natural comparison of its restriction with the given descent datum.
9. If H is represented by X, def-pc-fibre-product represents each local product by
   X ×_T U_i; lem-pc-representable-unique identifies its transitions with the canonical
   ones, so the datum is effective in the sense of def-pd-descent-datum. Conversely a
   geometric realization supplies compatible local isomorphisms h_X ≅ H. By step 2
   h_X is a sheaf; lem-pe-set-sheaf-cover-descent glues these maps and their inverses,
   and uniqueness proves that they are inverse. Thus H is representable. -/
theorem fppfSheafRepresentabilityDescentData
    {I : Type (u + 1)} (T : Scheme.{u}) (U : I → Scheme.{u})
    (f : ∀ i, U i ⟶ T)
    (hcov : Presieve.ofArrows U f ∈ Scheme.fppfPrecoverage T) :
    ∃ e : SchemeCoverDescent f ≌ (IsLocallyRepresentableFppfSheaf f).FullSubcategory,
      Nonempty
        (e.functor ⋙ (IsLocallyRepresentableFppfSheaf f).ι ⋙
            (Scheme.fppfTopology.pseudofunctorOver (Type (u + 1))).toDescentData f ≅
          schemeCoverDescentForget f) ∧
      (∀ (D : SchemeCoverDescent f) (i : I),
        Nonempty
          ((Limits.prod (uliftYoneda.{u + 1}.obj (Over.mk (f i)))
            (e.functor.obj D).obj.obj).RepresentableBy
              ((Over.map (f i)).obj (D.localScheme i)))) ∧
      (∀ D : SchemeCoverDescent f,
        (e.functor.obj D).obj.obj.IsRepresentable ↔ D.IsEffective) := by
  sorry

end AlgebraicGeometry
