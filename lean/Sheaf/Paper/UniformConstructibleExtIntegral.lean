/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.Paper.UniformConstructibleExtTorsion

import Sheaf.Paper.SupportedLatticeHomReductionTower
import Sheaf.Paper.LatticeSupportedHomFiniteComparison

/-!
# The integral stratum Ext bound

Source: blueprint main-20261015, sec-six-functors-basics,
sk-lem-uniform-constructible-ext/sk-lem-uniform-constructible-ext-integral.md
(blueprint: det-uniform-constructible-ext-integral).

The Ext group is the morphism group from the degree-zero source to the shifted
degree-zero target in the unbounded derived category of integral coefficient modules.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The adjacent integral degrees both exceed the torsion cutoff.
Source: the final degree computation in Integral targets
(blueprint: det-uniform-constructible-ext-integral). -/
private theorem roos_degrees (d : WithTop ℕ) (q : ℤ)
    (h : d + 2 < (q.toNat : WithTop ℕ)) :
    d + 1 < ((q - 1).toNat : WithTop ℕ) ∧ d + 1 < (q.toNat : WithTop ℕ) := by
  cases d using WithTop.recTopCoe with
  | top => simp at h
  | coe d =>
    have hn : d + 2 < q.toNat := WithTop.coe_lt_coe.mp h
    have hprev : d + 1 < (q - 1).toNat := by omega
    have hnext : d + 1 < q.toNat := by omega
    exact ⟨WithTop.coe_lt_coe.mpr hprev, WithTop.coe_lt_coe.mpr hnext⟩

/-- Shifts preserve products; their mapped projections detect every map to the product.
Source: the fiber-of-1-minus-shift argument in Integral targets
(blueprint: det-uniform-constructible-ext-integral). -/
private theorem hom_shift_product_zero
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (Q : DerivedCategory C) (K : ℕ → DerivedCategory C) [HasProduct K]
    (r : ℤ) (h : ∀ n, Subsingleton (Q ⟶ (K n) ⟦r⟧))
    (f : Q ⟶ (∏ᶜ K) ⟦r⟧) : f = 0 := by
  apply (isLimitOfPreserves (shiftFunctor (DerivedCategory C) r)
    (productIsProduct K)).hom_ext
  intro n
  exact (h n.as).elim _ _

/-- Vanishing in two adjacent degrees propagates from the levels to their Roos limit.
Source: the final paragraph of Integral targets, the derived-limit one-degree loss
(blueprint: det-uniform-constructible-ext-integral). -/
private theorem hom_roos_zero
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (Q N : DerivedCategory C) (K : ℕ → DerivedCategory C) [HasProduct K]
    (step : ∀ n, K (n + 1) ⟶ K n)
    (pN : N ⟶ ∏ᶜ K) (δ : ∏ᶜ K ⟶ N⟦(1 : ℤ)⟧)
    (hT : IsDerivedLimitTriangle step N pN δ) (q : ℤ)
    (hprev : ∀ n, Subsingleton (Q ⟶ (K n) ⟦q - 1⟧))
    (hnext : ∀ n, Subsingleton (Q ⟶ (K n) ⟦q⟧)) :
    Subsingleton (Q ⟶ N⟦q⟧) := by
  let T := CategoryTheory.Pretriangulated.Triangle.mk pN (towerTransitionEndomorphism step) δ
  have hT' : T ∈ CategoryTheory.Pretriangulated.distinguishedTriangles
      (C := DerivedCategory C) := hT
  let U := (shiftFunctor (CategoryTheory.Pretriangulated.Triangle (DerivedCategory C))
    (q - 1)).obj T
  have hU : U ∈ CategoryTheory.Pretriangulated.distinguishedTriangles (C := DerivedCategory C) :=
    CategoryTheory.Pretriangulated.Triangle.shift_distinguished T hT' (q - 1)
  let e := (shiftFunctorAdd' (DerivedCategory C) (q - 1) 1 q (by omega)).app N
  have hz (f : Q ⟶ N⟦q⟧) : f = 0 := by
    obtain ⟨g, hg⟩ := CategoryTheory.Pretriangulated.Triangle.coyoneda_exact₁ U hU
      (f ≫ e.hom) (by
        apply (cancel_mono
          ((shiftFunctorAdd' (DerivedCategory C) (q - 1) 1 q (by omega)).app (∏ᶜ K)).inv).1
        rw [zero_comp]
        exact hom_shift_product_zero Q K q hnext _)
    have hg0 : g = 0 := hom_shift_product_zero Q K (q - 1) hprev g
    apply (cancel_mono e.hom).1
    simpa only [hg0, zero_comp] using hg
  exact ⟨fun f g => (hz f).trans (hz g).symm⟩

/-- The integral stratum bound, with the same standing setting as the torsion bound.
Source: blueprint main-20261015, sec-six-functors-basics,
sk-lem-uniform-constructible-ext/sk-lem-uniform-constructible-ext-integral.md
(blueprint: det-uniform-constructible-ext-integral).

Proof:
1. Put Q = i_*u_!L₀, N = kb_*vb_!M₀ and let Kₙ be the positive reduction of N,
regarded as an integral object. The supported-lattice tower theorem supplies the
Roos triangle N → P → P → N[1], with P the product of the Kₙ and middle map 1-shift.
2. Apply the three additive Hom comparisons of the finite-comparison theorem to
kb_*vb_!(M₀/π^(n+1)). Scalar restriction commutes with shifts, and the canonical
restriction isomorphism identifies its integral object with Kₙ. Thus Hom(Q,Kₙ[r])
is the cohomology of the finite-coefficient torsion stratum complex. Clause (2) of
the torsion bound kills it for r > cd_ℓ(j)+cd_ℓ(S)+1, uniformly in n.
3. Write d = cd_ℓ(j)+cd_ℓ(S). If d is infinite the asserted range is empty.
Otherwise d+2 < q.toNat implies d+1 < (q-1).toNat and d+1 < q.toNat, so step 2
kills both adjacent level Hom groups. Shifts preserve products, and product
extensionality kills Hom(Q,P[q-1]) and Hom(Q,P[q]). Shift the Roos triangle by q-1.
Exactness of Hom(Q,-) makes every map Q → N[q] factor through P[q-1], since its
image in P[q] is zero. The factor is zero, giving the result. This is precisely
the fiber-of-1-minus-shift proof of the one-degree derived-limit bound; no
Mittag-Leffler hypothesis or chosen Milnor short exact sequence is required. -/
theorem uniformConstructibleExtIntegral
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    (S Z V X T B : Over (Spec (.of k)))
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    (u : S ⟶ Z) (i : Z ⟶ X) (j : V ⟶ X) (kb : B ⟶ X) (vb : T ⟶ B)
    [IsOpenImmersion u.left] [IsClosedImmersion i.left] [IsOpenImmersion j.left]
    [IsClosedImmersion kb.left] [IsOpenImmersion vb.left]
    (hij : Set.range i.left.base = (Set.range j.left.base)ᶜ)
    (L₀ : FormalSupportModules (DerivedNakayama.integerRing ℓ E) S.left)
    (M₀ : FormalSupportModules (DerivedNakayama.integerRing ℓ E) T.left)
    (hL₀ : IsLisseCoefficientModule (DerivedNakayama.integerRing ℓ E) L₀)
    (hM₀ : IsLisseCoefficientModule (DerivedNakayama.integerRing ℓ E) M₀)
    (q : ℤ)
    (hq : torsionStratumRelativeDimension ℓ k j + torsionStratumDimension ℓ k S + 2 <
      (q.toNat : WithTop ℕ)) :
    Subsingleton
      (((DerivedCategory.singleFunctor
          (FormalSupportModules (DerivedNakayama.integerRing ℓ E) X.left) 0).obj
        ((lowerStar (DerivedNakayama.integerRing ℓ E) i.left).obj
          ((openImmersionLowerShriek (DerivedNakayama.integerRing ℓ E) u.left).obj L₀))) ⟶
        ((DerivedCategory.singleFunctor
            (FormalSupportModules (DerivedNakayama.integerRing ℓ E) X.left) 0).obj
          ((lowerStar (DerivedNakayama.integerRing ℓ E) kb.left).obj
            ((openImmersionLowerShriek (DerivedNakayama.integerRing ℓ E) vb.left).obj
              M₀))) ⟦q⟧) := by
  let : S.left.Over (Spec (.of k)) := ⟨S.hom⟩
  let : Z.left.Over (Spec (.of k)) := ⟨Z.hom⟩
  let : V.left.Over (Spec (.of k)) := ⟨V.hom⟩
  let : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  have : LocallyOfFiniteType (S.left ↘ Spec (.of k)) := by
    change LocallyOfFiniteType S.hom
    infer_instance
  have : QuasiCompact (S.left ↘ Spec (.of k)) := by
    change QuasiCompact S.hom
    infer_instance
  have : IsSeparated (S.left ↘ Spec (.of k)) := by
    change IsSeparated S.hom
    infer_instance
  have : LocallyOfFiniteType (Z.left ↘ Spec (.of k)) := by
    change LocallyOfFiniteType Z.hom
    infer_instance
  have : QuasiCompact (Z.left ↘ Spec (.of k)) := by
    change QuasiCompact Z.hom
    infer_instance
  have : IsSeparated (Z.left ↘ Spec (.of k)) := by
    change IsSeparated Z.hom
    infer_instance
  have : LocallyOfFiniteType (V.left ↘ Spec (.of k)) := by
    change LocallyOfFiniteType V.hom
    infer_instance
  have : QuasiCompact (V.left ↘ Spec (.of k)) := by
    change QuasiCompact V.hom
    infer_instance
  have : IsSeparated (V.left ↘ Spec (.of k)) := by
    change IsSeparated V.hom
    infer_instance
  have : LocallyOfFiniteType (X.left ↘ Spec (.of k)) := by
    change LocallyOfFiniteType X.hom
    infer_instance
  have : QuasiCompact (X.left ↘ Spec (.of k)) := by
    change QuasiCompact X.hom
    infer_instance
  have : IsSeparated (X.left ↘ Spec (.of k)) := by
    change IsSeparated X.hom
    infer_instance
  have : i.left.IsOver (Spec (.of k)) := ⟨i.w⟩
  have : j.left.IsOver (Spec (.of k)) := ⟨j.w⟩
  have : u.left.IsOver (Spec (.of k)) := ⟨u.w⟩
  let Q := SupportedLatticeHom.target ℓ E i.left u.left L₀
  let N := SupportedLatticeHom.target ℓ E kb.left vb.left M₀
  let K := SupportedLatticeHom.level ℓ E kb.left vb.left M₀
  have hlevel (n : ℕ) (r : ℤ)
      (hr : torsionStratumRelativeDimension ℓ k j + torsionStratumDimension ℓ k S + 1 <
        (r.toNat : WithTop ℕ)) : Subsingleton (Q ⟶ (K n) ⟦r⟧) := by
    obtain ⟨c⟩ := latticeSupportedHomFiniteComparison ℓ E (n + 1)
      i.left j.left u.left L₀ (by omega) k p hpℓ hij hL₀
    obtain ⟨e₁, _, e₂, _, ⟨e₃⟩⟩ := c.groups r
    let A := SupportedLatticeHom.finiteDerivedExtension ℓ E kb.left vb.left M₀ n
    have hz := (uniformConstructibleExtTorsion ℓ E k p hpℓ S Z V X T B
      u i j kb vb hij L₀ M₀ hL₀ hM₀ (n + 1) (by omega)).2 r hr
    have hs : Subsingleton
        (Q ⟶ (AdicCompletion.restrict ℓ E X.left n).obj (A⟦r⟧)) :=
      AddCommGrpCat.subsingleton_of_isZero
        (hz.of_iso (e₁.app A ≪≫ e₂.app A ≪≫ e₃.app A))
    let e := ((AdicCompletion.restrict ℓ E X.left n).commShiftIso r).app A ≪≫
      (shiftFunctor _ r).mapIso
        (SupportedLatticeHom.levelRestrictionIso ℓ E kb.left vb.left M₀ n)
    refine ⟨fun f g => ?_⟩
    apply (cancel_mono e.inv).1
    exact hs.elim _ _
  have hA := SupportedLatticeHom.supported_lattice_hom_reduction_tower
    ℓ E k p hpℓ i.left j.left u.left kb.left vb.left hij L₀ M₀ hL₀ hM₀
  obtain ⟨hP, hF, hB, pN, δ, eF, eB, hT, _⟩ := hA.2.2.2
  have : HasProduct K := hP
  apply hom_roos_zero Q N K (SupportedLatticeHom.step ℓ E kb.left vb.left M₀)
    pN δ hT q
  · intro n
    exact hlevel n (q - 1) (roos_degrees _ q hq).1
  · intro n
    exact hlevel n q (roos_degrees _ q hq).2

end AlgebraicGeometry.ProEtale.CondensedRing
