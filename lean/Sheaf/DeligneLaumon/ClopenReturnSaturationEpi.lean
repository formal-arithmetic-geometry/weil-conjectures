/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Sheaf.DeligneLaumon.FrobeniusSaturation
public import Sheaf.DeligneLaumon.PoweredPullbackCarrier
public import WeilConjectures.WeilSheaf.BaseChangeField.Geometric
public import WeilConjectures.SixFunctors.ProEtale.Adic.OpenImmersion
import Sheaf.DeligneLaumon.ClopenNonreturnVanishing
import Sheaf.DeligneLaumon.ClopenReturnTranslateFactor

/-! # The saturation has no extra image on the distinguished return sheet

Source: the cyclic Frobenius-orbit calculation in `sk-i-dl-general-real`.
(blueprint: lem-zl-clopen-return-saturation-epi).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Endofunctor
open scoped AlgebraicGeometry.ProEtale
namespace CategoryTheory.Endofunctor.IsoAlgebra

private theorem epi_saturationUnit_of_factors
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    (F : A ⥤ A) [F.IsEquivalence] [F.Additive]
    [HasColimitsOfShape (Discrete ℤ) A]
    (L : B ⥤ A) (P : A ⥤ B) (adj : L ⊣ P)
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesColimitsOfShape (Discrete ℤ) P]
    (V : IsoAlgebra F) (M : B) (s : M ⟶ P.obj V.carrier)
    (hf : ∀ n : ℤ, ∃ a : P.obj (Free.obj F (L.obj M) n) ⟶ M,
      P.map (Free.hom V ((adj.homEquiv M V.carrier).symm s) n) = a ≫ s) :
    Epi (saturationUnit F L P adj V M s) := by
  let f := saturationMap F L P adj V M s
  let q := factorThruImage f
  let j := saturationι F L P adj V M s
  let a := saturationUnit F L P adj V M s
  have hfac : q.hom.f ≫ j.hom.f = f.hom.f :=
    congrArg (fun g ↦ g.hom.f) (image.fac f)
  have hzero : a ≫ P.map j.hom.f = s := saturationUnit_comp_map_ι F L P adj V M s
  have : Epi q.hom.f := (forget F).map_epi q
  have : Mono j.hom.f := (forget F).map_mono j
  have hn (n : ℤ) : ∃ b : P.obj (Free.obj F (L.obj M) n) ⟶ M,
      P.map (Sigma.ι (Free.obj F (L.obj M)) n ≫ q.hom.f) = b ≫ a := by
    obtain ⟨b, hb⟩ := hf n
    refine ⟨b, (cancel_mono (P.map j.hom.f)).1 ?_⟩
    rw [← P.map_comp, Category.assoc, hfac, Category.assoc, hzero]
    rw [← hb]
    congr 1
    exact Sigma.ι_desc _ _
  constructor
  intro T b₁ b₂ h
  apply (cancel_epi (P.map q.hom.f)).1
  apply (isColimitOfPreserves P (coproductIsCoproduct (Free.obj F (L.obj M)))).hom_ext
  rintro ⟨n⟩
  change P.map (Sigma.ι (Free.obj F (L.obj M)) n) ≫ P.map q.hom.f ≫ b₁ =
    P.map (Sigma.ι (Free.obj F (L.obj M)) n) ≫ P.map q.hom.f ≫ b₂
  rw [← P.map_comp_assoc, ← P.map_comp_assoc]
  obtain ⟨b, hb⟩ := hn n
  rw [hb, Category.assoc, Category.assoc, h]

end CategoryTheory.Endofunctor.IsoAlgebra

namespace AlgebraicGeometry.WeilSheaf

/-- The zero-th generator surjects onto the saturation restricted to its own return sheet.
Source: the cyclic Frobenius-orbit calculation of
`lem-zl-clopen-return-subobject` in `sk-i-dl-general-real`.

Proof: put `q = #k₀`. The equality `#k₁ = q^r` identifies `r` with the extension
degree; in particular `r > 0`. The base change of `C` from `k₀` to its algebraic
closure is the disjoint union of `r` copies of `Cbar`, indexed by the embeddings
of `k₁`. The two projection equations identify `v` with the distinguished copy
followed by the base change of the monomorphism `c`. The `k₀`-Frobenius permutes
these copies cyclically. Thus, after restricting to `v`, the translate numbered
`n` of extension by zero from `v` is zero unless `r` divides `n`.
For `n = rm`, its map into the restricted ambient carrier has the same image
as the original map: equivariance of `i` for powered pullback identifies it
with the original map precomposed with the `m`-th invertible Weil structure of
`G`. This holds for negative as well as positive `m`, by inverting that
structure. Consequently every summand of the restricted free-algebra map has
image contained in the zero-th summand. Exact pullback preserves the image
factorization. The zero-th summand therefore surjects onto its image, which is
the restriction of the saturation. The adjunction unit identifies that
summand with `G.carrier`, and its map is precisely `saturationUnit`. This proves
it is epi. Neither injectivity of `i` nor lissity, finite ranks, smoothness or
constructibility is used. For `i = 0`, both this image and its restriction are
zero, so the asserted epimorphism is still valid.
(blueprint: lem-zl-clopen-return-saturation-epi). -/
theorem epi_clopen_return_saturationUnit
    {k₀ k₁ : Type u} [Field k₀] [Finite k₀] [Field k₁] [Finite k₁]
    [Algebra k₀ k₁] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] [Fact (ringChar k₁ ≠ l)]
    {X C : Scheme.{u}} [X.Over (Spec (.of k₀))] [C.Over (Spec (.of k₁))]
    (c : C ⟶ X) [Mono c]
    (hc : c ≫ (X ↘ Spec (.of k₀)) =
      (C ↘ Spec (.of k₁)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁)))
    (r : ℕ) (hr : Nat.card k₁ = Nat.card k₀ ^ r)
    (v : (C ↘ Spec (.of k₁)).geometricFiber ⟶ (X ↘ Spec (.of k₀)).geometricFiber)
    [IsOpenImmersion v]
    (hp : v ≫ (X ↘ Spec (.of k₀)).geometricFiberProj =
      (C ↘ Spec (.of k₁)).geometricFiberProj ≫ c)
    (hb : v ≫ (X ↘ Spec (.of k₀)).geometricFiberToAlgebraicClosure =
      (C ↘ Spec (.of k₁)).geometricFiberToAlgebraicClosure ≫
        Spec.map (CommRingCat.ofHom (algebraicClosureAlgEquiv k₀ k₁).symm.toRingHom))
    (hv : (C ↘ Spec (.of k₁)).geometricGaloisFrobenius.hom ≫ v =
      v ≫ ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ r).hom)
    (V : ProEtaleWeilSheaf k₀ l X) (G : ProEtaleWeilSheaf k₁ l C)
    (i : G ⟶ (poweredGeometricPullbackAll v r hv).obj V) :
    Epi (IsoAlgebra.saturationUnit (frobeniusPullback k₀ l X) (v)_!ᵃ[l] (v)^*ᵃ[l]
      (ProEtale.adicOpenImmersionLowerShriekAdjunction l v) V G.carrier
      (i.hom.f ≫ (poweredPullbackAllCarrierIso v r hv).hom.app V)) := by
  have _hmodel := hc
  classical
  have : (v)^*ᵃ[l].IsLeftAdjoint :=
    (ProEtale.adicUpperStarLowerStarAdjunction l v).isLeftAdjoint
  apply IsoAlgebra.epi_saturationUnit_of_factors
  intro n
  by_cases hn : (r : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := hn
    exact clopen_return_freeHom_factor v r hv V G i m
  · refine ⟨0, ?_⟩
    exact (isZero_clopen_nonreturn_freeObj c r hr v hp hb G.carrier n hn).eq_of_src _ _

end AlgebraicGeometry.WeilSheaf
