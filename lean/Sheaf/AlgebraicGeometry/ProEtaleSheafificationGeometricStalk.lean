/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.RingTheory.IndPrincipalZariski
import Sheaf.RingTheory.WeaklyEtaleField
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Localization

/-! # Sheafification preserves pro-etale geometric stalks

Source: Stacks Project, Tags 0F6B, 0F6C, the paragraph before 0993, and 00Y8(3)
(blueprint: lem-cbc-proetale-sheafification-geometric-stalk).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The colimit of the abelian sheafification unit on pointed weakly etale neighbourhoods
is an isomorphism, naturally in the presheaf.
Source: Stacks Project, Tags 0F6B, 0F6C, paragraph before 0993, and 00Y8(3)
(blueprint: lem-cbc-proetale-sheafification-geometric-stalk).

Proof:
1. Use `def-weil-proetale-geometric-stalk` and `def-weil-size-convention` to form the
   filtered colimits. Every class is represented by one section, and equality is equality
   on a common pointed refinement, equalizing parallel arrows if necessary.
2. A cover of a pointed neighbourhood admits a lift of the fixed geometric point to a
   member (Tag 0F6C). Base change the fpqc cover to Spec Ω using
   `lem-galois-fpqc-covering-base-change`, choose a nonempty fibre and an affine open,
   and use `lem-weil-pbc-weakly-etale-composition-base-change` and
   `lem-weil-pbc-weakly-etale-source-locality`. By `def-weil-pbc-ind-etale-algebra` and
   `lem-weil-pbc-weak-etale-field` its residue field is separable algebraic over Ω.
   `lem-weil-pbc-separable-extension-embeds-separably-closed` embeds it into Ω.
   This supplies a pointed refinement with the original field, transported to the skeleton.
3. The adjunction `def-weil-pbc-sheafification` makes the sheafified unit an isomorphism.
   `lem-weil-pbc-site-sheafification-iso-locally-bijective` therefore gives local lifts of
   sections and local equality for sections with the same image, in abelian presheaves.
4. Represent a target class by a section, lift it locally by step 3, and choose a pointed
   member by step 2. This proves surjectivity of the colimit homomorphism.
5. A class mapping to zero has image zero on a pointed refinement by step 1. Step 3
   makes its representative locally zero; step 2 gives a pointed member where it is zero.
   The kernel is zero. Together with step 4 this proves the asserted isomorphism.
6. For `a : P ⟶ Q`, both paths in the naturality square send a representative `s` to
   the class of `θ_Q(a(s))`, by naturality of the sheafification unit. Since representatives
   generate the colimits, the square commutes; its inverse square commutes as well.
-/
theorem proEtaleGeometricStalk_sheafification
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (P : X.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    IsIso (colim.map (Functor.whiskerLeft (proEtaleGeometricNeighbourhoodForget x).op
      (toSheafify (ProEt.topology X) P))) ∧
    ∀ (Q : X.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (a : P ⟶ Q),
      colim.map (Functor.whiskerLeft (proEtaleGeometricNeighbourhoodForget x).op a) ≫
        colim.map (Functor.whiskerLeft (proEtaleGeometricNeighbourhoodForget x).op
          (toSheafify (ProEt.topology X) Q)) =
      colim.map (Functor.whiskerLeft (proEtaleGeometricNeighbourhoodForget x).op
        (toSheafify (ProEt.topology X) P)) ≫
        colim.map (Functor.whiskerLeft (proEtaleGeometricNeighbourhoodForget x).op
          (sheafifyMap (ProEt.topology X) a)) := by
  sorry

end AlgebraicGeometry.Scheme
