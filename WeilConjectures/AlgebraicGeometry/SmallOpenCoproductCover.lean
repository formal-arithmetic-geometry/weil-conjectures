/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty

/-!
# Small covering subfamilies of open sheaf coproducts

Source: Stacks Project, Spaces, Tag 02WR, first and third proof paragraphs; Tags 02WO
and 0F15 for the partition of a scheme mapping into a sheaf coproduct
(blueprint: lem-trf-small-open-coproduct-cover).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- An epimorphic open family whose coproduct has a scheme atlas has a small subfamily
with the same coproduct, and that subfamily covers the target fppf locally.
No representable diagonal of any summand is assumed.

Source: Stacks Project, Spaces, Tag 02WR, first and third proof paragraphs, including
its explicit set-theoretic coproduct hypothesis; Tags 02WO and 0F15
(blueprint: lem-trf-small-open-coproduct-cover).

Proof:
1. Choose a surjective etale scheme atlas U of H. Its sheaf map is epimorphic:
   each scheme test has a surjective etale pullback, whose singleton fppf cover
   supplies a local lift. Let K be the indices i for which F_i has a section on
   some nonempty scheme. If i is outside K, F_i is initial: it has no sections on
   nonempty schemes, and exactly one on empty schemes by the empty-cover axiom.
2. Let B be the fppf sheaf of continuous maps to the discrete two-point space.
   For each i in K, the coproduct universal property gives a map H to B which is
   constantly one on F_i and constantly zero on every other summand. Restrict
   these maps to U. Distinct indices give distinct maps U to B: equality after
   the epimorphic atlas implies equality on H, and evaluation on a section of
   F_i over a nonempty scheme distinguishes the constants one and zero.
   Yoneda identifies maps U to B with continuous maps from U to the two-point
   space, a u-small set. Thus K is u-small. Shrink K to J in Type u, with label
   map k. Omitting the initial summands preserves the coproduct universal
   property, proving the first assertion. This detector argument supplies the
   universe reduction before using any small-index coproduct-partition theorem.
3. On a test T to F, represent its pullback to each retained F_i by an open V_i.
   Their union defines a natural map from F to the sheaf of opens: pullback of
   these opens is prescribed by their representing property, and inverse image
   commutes with arbitrary unions. This map agrees with the constant full-open
   map on every retained summand, since that summand's own open is full. The
   coproduct universal property implies agreement after q; Epi q implies global
   agreement. The union is therefore T. The sheaf of opens is the sheaf of
   continuous maps to the Sierpinski space; fpqc descent of continuous maps
   supplies its fppf sheaf condition, also after restriction to schemes over S.
4. Choose for each point of T one V_(k j) containing it. These neighbourhoods
   form a u-small Zariski cover, hence an fppf cover. On each neighbourhood the
   universal section of the represented open pullback gives the displayed lift.
   Empty schemes and empty index types use the empty cover; repeated labels and
   initial summands cause no change. No summand diagonal is used. -/
theorem small_open_coproduct_cover {S : Scheme.{u}}
    (F : Sheaf (Scheme.fppfTopology.over S) (Type u)) (I : Type w)
    (Fi : I → Sheaf (Scheme.fppfTopology.over S) (Type u))
    (H : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (j : ∀ i : I, Fi i ⟶ H) (hcol : IsColimit (Cofan.mk H j))
    (ι : ∀ i : I, Fi i ⟶ F) (q : H ⟶ F)
    (hfac : ∀ i : I, j i ≫ q = ι i) (hmono : ∀ i : I, Mono (ι i))
    (hopen : ∀ i : I, AlgebraicSpace.IsRepresentableWith
      (fun _ _ p ↦ IsOpenImmersion p.left) (ι i).hom)
    (hq : Epi q) (hcop : AlgebraicSpace.IsAlgebraicSpace H) :
    ∃ (J : Type u) (k : J → I),
      Nonempty (IsColimit (Cofan.mk H (fun r ↦ j (k r)))) ∧
      ∀ (T : Over S) (a : F.obj.obj (op T)),
        ∃ (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage T.left) (l : 𝒰.I₀ → J),
          ∀ r : 𝒰.I₀,
            F.obj.map (Over.homMk (𝒰.f r) rfl : Over.mk (𝒰.f r ≫ T.hom) ⟶ T).op a ∈
              Set.range ((ι (k (l r))).hom.app (op (Over.mk (𝒰.f r ≫ T.hom)))) := by sorry

end AlgebraicGeometry
