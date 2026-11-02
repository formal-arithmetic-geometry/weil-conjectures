/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UniformConstructibleExtTorsion
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LatticeSupportedHomFiniteComparison
import WeilConjectures.AlgebraicGeometry.SupportedLatticeHom.SupportedLatticeHomReductionTower
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedPullbackTensorComparison

/-!
# The integral stratum bound

Source: latest blueprint, part-six-operations/sec-six-functors-basics/sec-compactness/
sec-a-uniform-bound-for-ext-between-constructible-sheaves/sk-lem-uniform-constructible-ext/,
`sk-lem-uniform-constructible-ext-integral.md`, its `.proof.md`, and
`sk-lem-uniform-constructible-ext.proof.md`, Integral targets; Stacks Tag 08TB
(blueprint: det-uniform-constructible-ext-integral).

Ext is Hom into an integer shift in the ordinary unbounded derived category of modules
for the pulled-back condensed integer ring. No finite-stage realization is involved.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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

/-- The integral stratum bound, uniformly in the target locally closed stratum and lattice.
Source: latest blueprint, sk-lem-uniform-constructible-ext-integral, and the Integral targets
paragraph of sk-lem-uniform-constructible-ext.proof; Stacks Tag 08TB
(blueprint: det-uniform-constructible-ext-integral).

Proof: Put Q = i_*u_!L₀, N = k_b,*v_b,!M₀ and
K_n = Res_(n+1)(k_b,*v_b,!(M₀ / π^(n+1))). The supported lattice reduction-tower
statement gives the Roos triangle N → P → P → N[1], where P is the product of the
K_n and the middle arrow is one minus the quotient-transition shift. Its canonical
levelRestrictionIso identifies the terms with the restricted finite supported quotients.
For each n, the finite-comparison theorem at exponent n+1, together with restriction's
shift comparison, identifies Hom(Q,K_n[r]) with the torsion stratum cohomology in degree r.
Torsion bound (2) kills it when cd_ℓ(j) + cd_ℓ(S) + 1 < r.toNat.
If either dimension is infinite, the degree hypothesis is impossible. Otherwise put
d = cd_ℓ(j) + cd_ℓ(S). The strict bound d+2 < q.toNat implies
d+1 < (q-1).toNat and d+1 < q.toNat. Thus both Hom(Q,K_n[q-1]) and
Hom(Q,K_n[q]) vanish for every n. Shifts preserve products, so product extensionality
kills Hom(Q,P[q-1]) and Hom(Q,P[q]). Shift the Roos triangle by q-1 and apply Hom(Q,-).
Exactness makes every map Q → N[q] factor through P[q-1], hence zero. This is the
fiber-of-one-minus-shift proof of the one-degree loss in Integral targets. -/
theorem uniformConstructibleExtIntegral
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (_hpℓ : p ≠ ℓ)
    (S Z V X T B : Over (Spec (.of k)))
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    (v : S ⟶ Z) (i : Z ⟶ X) (j : V ⟶ X) (kb : B ⟶ X) (vb : T ⟶ B)
    [IsOpenImmersion v.left] [IsClosedImmersion i.left] [IsOpenImmersion j.left]
    [IsClosedImmersion kb.left] [IsOpenImmersion vb.left]
    (_hij : Set.range i.left.base = (Set.range j.left.base)ᶜ)
    (L₀ : FormalSupportModules (DerivedNakayama.integerRing ℓ E) S.left)
    (M₀ : FormalSupportModules (DerivedNakayama.integerRing ℓ E) T.left)
    (_hL₀ : IsLisseCoefficientModule (DerivedNakayama.integerRing ℓ E) L₀)
    (_hM₀ : IsLisseCoefficientModule (DerivedNakayama.integerRing ℓ E) M₀)
    (q : ℤ)
    (_hq : torsionStratumRelativeDimension ℓ k j + torsionStratumDimension ℓ k S + 2 <
      (q.toNat : WithTop ℕ)) :
    Subsingleton
      (((DerivedCategory.singleFunctor
          (FormalSupportModules (DerivedNakayama.integerRing ℓ E) X.left) 0).obj
        ((lowerStar (DerivedNakayama.integerRing ℓ E) i.left).obj
          ((openImmersionLowerShriek (DerivedNakayama.integerRing ℓ E) v.left).obj L₀))) ⟶
      ((DerivedCategory.singleFunctor
          (FormalSupportModules (DerivedNakayama.integerRing ℓ E) X.left) 0).obj
        ((lowerStar (DerivedNakayama.integerRing ℓ E) kb.left).obj
          ((openImmersionLowerShriek (DerivedNakayama.integerRing ℓ E) vb.left).obj M₀))) ⟦q⟧) := by
  let : S.left.Over (Spec (.of k)) := ⟨S.hom⟩
  let : Z.left.Over (Spec (.of k)) := ⟨Z.hom⟩
  let : V.left.Over (Spec (.of k)) := ⟨V.hom⟩
  let : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  let : T.left.Over (Spec (.of k)) := ⟨T.hom⟩
  let : B.left.Over (Spec (.of k)) := ⟨B.hom⟩
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
  have : LocallyOfFiniteType (T.left ↘ Spec (.of k)) := by
    change LocallyOfFiniteType T.hom
    infer_instance
  have : QuasiCompact (T.left ↘ Spec (.of k)) := by
    change QuasiCompact T.hom
    infer_instance
  have : IsSeparated (T.left ↘ Spec (.of k)) := by
    change IsSeparated T.hom
    infer_instance
  have : LocallyOfFiniteType (B.left ↘ Spec (.of k)) := by
    change LocallyOfFiniteType B.hom
    infer_instance
  have : QuasiCompact (B.left ↘ Spec (.of k)) := by
    change QuasiCompact B.hom
    infer_instance
  have : IsSeparated (B.left ↘ Spec (.of k)) := by
    change IsSeparated B.hom
    infer_instance
  have : i.left.IsOver (Spec (.of k)) := ⟨i.w⟩
  have : j.left.IsOver (Spec (.of k)) := ⟨j.w⟩
  have : v.left.IsOver (Spec (.of k)) := ⟨v.w⟩
  have : kb.left.IsOver (Spec (.of k)) := ⟨kb.w⟩
  have : vb.left.IsOver (Spec (.of k)) := ⟨vb.w⟩
  let Q := SupportedLatticeHom.target ℓ E i.left v.left L₀
  let N := SupportedLatticeHom.target ℓ E kb.left vb.left M₀
  let K := SupportedLatticeHom.level ℓ E kb.left vb.left M₀
  have hlevel (n : ℕ) (r : ℤ)
      (hr : torsionStratumRelativeDimension ℓ k j + torsionStratumDimension ℓ k S + 1 <
        (r.toNat : WithTop ℕ)) : Subsingleton (Q ⟶ (K n) ⟦r⟧) := by
    obtain ⟨c⟩ := latticeSupportedHomFiniteComparison ℓ E (n + 1)
      i.left j.left v.left L₀ (by omega) k p _hpℓ _hij _hL₀
    obtain ⟨e₁, _, e₂, _, ⟨e₃⟩⟩ := c.groups r
    have hsupport : formalClosedSupport (DerivedNakayama.quotientRing ℓ E (n + 1))
        i.left j.left = closedSupport (DerivedNakayama.quotientRing ℓ E (n + 1))
        i.left j.left := rfl
    have hpull : formalSupportPullback (DerivedNakayama.quotientRing ℓ E (n + 1))
        v.left = supportPullback (DerivedNakayama.quotientRing ℓ E (n + 1)) v.left := rfl
    simp only [hsupport, hpull] at e₃
    let A := SupportedLatticeHom.finiteDerivedExtension ℓ E kb.left vb.left M₀ n
    have hz := (uniformConstructibleExtTorsion ℓ E k p _hpℓ S Z V X T B
      v i j kb vb _hij L₀ M₀ _hL₀ _hM₀ (n + 1) (by omega)).2 r hr
    let G := (closedSupport (DerivedNakayama.quotientRing ℓ E (n + 1))
      i.left j.left).rightDerivedFunctor ⋙
      (supportPullback (DerivedNakayama.quotientRing ℓ E (n + 1)) v.left).mapDerivedCategory ⋙
      (derivedTensor (DerivedNakayama.quotientRing ℓ E (n + 1)) S.left).obj
        ((DerivedCategory.singleFunctor
            (FormalSupportModules (DerivedNakayama.quotientRing ℓ E (n + 1)) S.left) 0).obj
          (torsionStratumReduction ℓ E
            ((ihom L₀).obj (MonoidalCategoryStruct.tensorUnit
              (FormalSupportModules (DerivedNakayama.integerRing ℓ E) S.left))) (n + 1))) ⋙
      (formalClosedSupportSections (DerivedNakayama.quotientRing ℓ E (n + 1))
        S.left).rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor Ab r
    let G' := (closedSupport (DerivedNakayama.quotientRing ℓ E (n + 1))
      i.left j.left).rightDerivedFunctor ⋙
      (upperStar (DerivedNakayama.quotientRing ℓ E (n + 1)) v.left).mapDerivedCategory ⋙
      (derivedTensor (DerivedNakayama.quotientRing ℓ E (n + 1)) S.left).obj
        ((DerivedCategory.singleFunctor
            (FormalSupportModules (DerivedNakayama.quotientRing ℓ E (n + 1)) S.left) 0).obj
          (torsionStratumReduction ℓ E
            ((ihom L₀).obj (MonoidalCategoryStruct.tensorUnit
              (FormalSupportModules (DerivedNakayama.integerRing ℓ E) S.left))) (n + 1))) ⋙
      (formalClosedSupportSections (DerivedNakayama.quotientRing ℓ E (n + 1))
        S.left).rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor Ab r
    have hz'' : IsZero (G'.obj A) := by
      simpa [G', A, SupportedLatticeHom.finiteDerivedExtension,
        SupportedLatticeHom.finiteExtension, SupportedLatticeHom.finiteQuotient,
        AdicCompletion.quotient, AdicCompletion.finiteRing,
        torsionStratumTwist, torsionStratumSupport, torsionStratumReduction,
        closedSupport, supportPullback, supportKernel, Mod.comapEquivalenceOfIsIso,
        coefficientMap, upperStar] using hz
    let ePull := Functor.mapDerivedCategoryNatIso
      (supportPullbackIsoUpperStar
        (DerivedNakayama.quotientRing ℓ E (n + 1)) v.left)
    let eG : G ≅ G' := Functor.isoWhiskerLeft
      (closedSupport (DerivedNakayama.quotientRing ℓ E (n + 1)) i.left j.left).rightDerivedFunctor
      (Functor.isoWhiskerRight ePull
        ((derivedTensor (DerivedNakayama.quotientRing ℓ E (n + 1)) S.left).obj
          ((DerivedCategory.singleFunctor
              (FormalSupportModules (DerivedNakayama.quotientRing ℓ E (n + 1)) S.left) 0).obj
            (torsionStratumReduction ℓ E
              ((ihom L₀).obj (MonoidalCategoryStruct.tensorUnit
                (FormalSupportModules (DerivedNakayama.integerRing ℓ E) S.left))) (n + 1))) ⋙
          (formalClosedSupportSections
            (DerivedNakayama.quotientRing ℓ E (n + 1)) S.left).rightDerivedFunctor ⋙
          DerivedCategory.homologyFunctor Ab r))
    have hz' : IsZero (G.obj A) := hz''.of_iso (eG.app A)
    have hs : Subsingleton
        (Q ⟶ (AdicCompletion.restrict ℓ E X.left n).obj (A⟦r⟧)) :=
      AddCommGrpCat.subsingleton_of_isZero
        (hz'.of_iso (e₁.app A ≪≫ e₂.app A ≪≫ e₃.app A))
    let e := ((AdicCompletion.restrict ℓ E X.left n).commShiftIso r).app A ≪≫
      (shiftFunctor _ r).mapIso
        (SupportedLatticeHom.levelRestrictionIso ℓ E kb.left vb.left M₀ n)
    refine ⟨fun f g => ?_⟩
    apply (cancel_mono e.inv).1
    exact hs.elim _ _
  have hA := SupportedLatticeHom.supported_lattice_hom_reduction_tower
    ℓ E k p _hpℓ i.left j.left v.left kb.left vb.left _hij L₀ M₀ _hL₀ _hM₀
  obtain ⟨hP, hF, hB, pN, δ, eF, eB, hT, _⟩ := hA.2.2.2
  have : HasProduct K := hP
  apply hom_roos_zero Q N K (SupportedLatticeHom.step ℓ E kb.left vb.left M₀)
    pN δ hT q
  · intro n
    exact hlevel n (q - 1) (roos_degrees _ q _hq).1
  · intro n
    exact hlevel n q (roos_degrees _ q _hq).2


end AlgebraicGeometry.ProEtale.CondensedRing
