/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.FpqcSingletonFullyFaithful

/-!
# Canonical comparisons of pullback functors on scheme descent data

Source: Stacks Project, Descent, Tags 02VS(3) and 023Y(1)--(2)
(blueprint: lem-galois-fpqc-pullback-canonical-iso).
-/

@[expose] public section

universe v

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

/-- Canonical comparisons of pullback of descent data over a fixed scheme.
Source: Stacks Project, Descent, Tags 023Y(1)--(2) and 02VS(3)
(blueprint: lem-galois-fpqc-pullback-canonical-iso).

The functors are specified by their fibre-product projections `q`, the universal property
`IsPullback`, the pulled-back datum `IsBaseChange`, and the equation for their maps.
The two-map comparison is specified by transporting the universal point of the first
pullback along the pair of maps to `X`. The composition comparison preserves the projection
back to the original scheme; together with being over `U`, this specifies the canonical
associativity isomorphism uniquely.

Proof: (1) The pair `(r₀,r₁)` defines a map to `X ×_S X` by the universal property
[def-pc-fibre-product]. Pull back the descent isomorphism [def-pd-descent-datum] along this
pair to obtain the comparison; compatibility of morphisms of descent data gives naturality.
(2) On `T ×_S T`, the required descent-morphism equation follows by applying the cocycle
identity twice on `X ×_S X ×_S X`; inverse transport gives the inverse morphism.
(3) For composable maps, the universal property [def-pc-fibre-product] identifies the
iterated and direct pullbacks preserving both projections. Functoriality identifies their
descent data and morphisms, giving the natural associativity comparison. -/
theorem descent_pullback_canonical_iso (S : Scheme.{v}) :
    ∃ (pull : ∀ ⦃X T : Scheme.{v}⦄ (a : X ⟶ S) (b : T ⟶ S)
        (r : T ⟶ X) (hr : r ≫ a = b), Over.DescentDataCategory a ⥤ Over.DescentDataCategory b)
      (q : ∀ ⦃X T : Scheme.{v}⦄ (a : X ⟶ S) (b : T ⟶ S)
        (r : T ⟶ X) (hr : r ≫ a = b) (D : Over.DescentDataCategory a),
          ((pull a b r hr).obj D).V.left ⟶ D.V.left)
      (hq : ∀ ⦃X T : Scheme.{v}⦄ (a : X ⟶ S) (b : T ⟶ S)
        (r : T ⟶ X) (hr : r ≫ a = b) (D : Over.DescentDataCategory a),
          q a b r hr D ≫ D.V.hom = ((pull a b r hr).obj D).V.hom ≫ r),
      (∀ ⦃X T : Scheme.{v}⦄ (a : X ⟶ S) (b : T ⟶ S)
          (r : T ⟶ X) (hr : r ≫ a = b) (D : Over.DescentDataCategory a),
        IsPullback (q a b r hr D) ((pull a b r hr).obj D).V.hom D.V.hom r ∧
          Over.DescentDatum.IsBaseChange (hr) (hq a b r hr D) D.datum
            ((pull a b r hr).obj D).datum) ∧
      (∀ ⦃X T : Scheme.{v}⦄ (a : X ⟶ S) (b : T ⟶ S)
          (r : T ⟶ X) (hr : r ≫ a = b)
          (D E : Over.DescentDataCategory a) (m : D ⟶ E),
        ((pull a b r hr).map m).hom.left ≫ q a b r hr E =
          q a b r hr D ≫ m.hom.left) ∧
      (∀ ⦃X T : Scheme.{v}⦄ (a : X ⟶ S) (b : T ⟶ S)
          (r₀ r₁ : T ⟶ X) (h₀ : r₀ ≫ a = b) (h₁ : r₁ ≫ a = b),
        ∃ e : pull a b r₀ h₀ ≅ pull a b r₁ h₁,
          ∀ D : Over.DescentDataCategory a,
            (e.hom.app D).hom.left ≫ q a b r₁ h₁ D =
              (D.datum.transport
                (((pull a b r₀ h₀).obj D).V.hom ≫ r₀)
                (((pull a b r₀ h₀).obj D).V.hom ≫ r₁)
                (by rw [Category.assoc, Category.assoc, h₀, h₁])
                (Over.homMk (q a b r₀ h₀ D) (hq a b r₀ h₀ D))).left) ∧
      (∀ ⦃X T U : Scheme.{v}⦄ (a : X ⟶ S) (b : T ⟶ S) (c : U ⟶ S)
          (r : T ⟶ X) (t : U ⟶ T) (hr : r ≫ a = b) (ht : t ≫ b = c)
          (hrt : (t ≫ r) ≫ a = c),
        ∃ e : pull a c (t ≫ r) hrt ≅ pull a b r hr ⋙ pull b c t ht,
          ∀ D : Over.DescentDataCategory a,
            (e.hom.app D).hom.left ≫ q b c t ht ((pull a b r hr).obj D) ≫
              q a b r hr D = q a c (t ≫ r) hrt D) := by
  sorry

end AlgebraicGeometry
