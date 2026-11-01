/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PrincipalTorsorComparisons.PrincipalTorsorSignTypes
/-! Independent comparison result for the principal torsor sign calculation. -/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite HomologicalComplex
namespace AlgebraicGeometry.Etale
/-- Normalized supported-Hom comparison commutes with the coefficient Yoneda boundary.
Source: Stacks Tag 06XU and the coefficient-boundary step of the principal-torsor node.
Proof: construct the comparison by the closed-cone lift on Hom(Q,I). Applying Hom(Q,-)
to the supplied degreewise split resolution sequence gives a short exact complex sequence.
The closed-cone lifts commute with coefficient maps, hence form a morphism to the relative
short exact sequence. Homology-boundary naturality intertwines their connecting maps.
The injective-resolution derived connecting theorem identifies the source boundary with
postcomposition by the extension class. Every normalized comparison agrees with this one
on all extMk cocycles, and extMk is surjective, so the identity holds for the given C.
(blueprint: lem-pur-principal-torsor-connecting-comparison). -/
theorem principalTorsorConnectingComparison
    (C : PrincipalTorsorComparisons.{u}) (hC : C.Normalized)
    (T Z : Scheme.{u}) (i : Z ⟶ T) [IsClosedImmersion i] (W : T.Opens)
    (h : Set.range i.base = (Set.range W.ι.base)ᶜ)
    (S : ShortComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hS : S.ShortExact) (I : InjectiveResolution S.X₁) (J : InjectiveResolution S.X₂)
    (L : InjectiveResolution S.X₃)
    (α : I.cocomplex ⟶ J.cocomplex) (β : J.cocomplex ⟶ L.cocomplex)
    (hαβ : α ≫ β = 0)
    (hα : I.ι ≫ α = (CochainComplex.single₀ _).map S.f ≫ J.ι)
    (hβ : J.ι ≫ β = (CochainComplex.single₀ _).map S.g ≫ L.ι)
    (hs : ∀ n : ℕ, Nonempty (((ShortComplex.mk α β hαβ).map
      (HomologicalComplex.eval _ (.up ℕ) n)).Splitting))
    (x : Ext (principalTorsorLocalization i W h).X₃ S.X₃ 1) :
    C.relative T Z i W h S.X₁ I 1 (x.comp hS.extClass rfl) =
      relativeConnecting T (Scheme.Etale.mk W.ι) (ShortComplex.mk α β hαβ) hs 1
        (C.relative T Z i W h S.X₃ L 0 x) := by sorry
end AlgebraicGeometry.Etale
