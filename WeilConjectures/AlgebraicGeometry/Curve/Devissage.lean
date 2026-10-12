/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.AssertionsTransfer
public import WeilConjectures.ConstructibleSheaf.SubobjectNoetherian

/-!
# Dévissage for the eight curve assertions

Let `0 ⟶ F₁ ⟶ F ⟶ F₂ ⟶ 0` be a short exact sequence of étale sheaves of `Λ`-modules on a
curve `X` over a field `k`. If the eight curve assertions `C(X, F₁)` and `C(X, F₂)` hold, then
so does `C(X, F)`: the long exact cohomology sequences, together with their pullbacks along a
field extension or to an open subscheme, pass vanishing, finiteness and bijectivity to the
middle term, and the coefficient hypotheses of the assertions for `F` are inherited by `F₁`
and `F₂`.

## Main statements

- `AlgebraicGeometry.Etale.bijective_cohomologyMap_X₂_of_shortExact`: the five lemma for the
  pullback maps on the middle terms of the long exact cohomology sequences.
- `AlgebraicGeometry.IsCurve.Assertions.of_shortExact`: dévissage for the eight assertions.
-/

@[expose] public section

universe u

open CategoryTheory Limits Abelian

namespace AlgebraicGeometry

namespace Etale

section LongExact

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  {S : ShortComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})} (hS : S.ShortExact)

include hS in
/-- In a short exact sequence `0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` of abelian étale sheaves, if
`Hⁿ(S.X₁) = 0` and `Hⁿ(S.X₃) = 0`, then `Hⁿ(S.X₂) = 0`. -/
lemma subsingleton_H_X₂_of_shortExact (n : ℕ) [Subsingleton (Sheaf.H S.X₁ n)]
    [Subsingleton (Sheaf.H S.X₃ n)] : Subsingleton (Sheaf.H S.X₂ n) := by
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨a, ha⟩ := (Sheaf.H.exact_map_map hS n x).1 (Subsingleton.elim _ _)
  obtain ⟨b, hb⟩ := (Sheaf.H.exact_map_map hS n y).1 (Subsingleton.elim _ _)
  rw [← ha, ← hb, Subsingleton.elim a b]

include hS in
/-- In a short exact sequence `0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` of abelian étale sheaves, if
`Hⁿ(S.X₁)` and `Hⁿ(S.X₃)` are finite, so is `Hⁿ(S.X₂)`. -/
lemma finite_H_X₂_of_shortExact (n : ℕ) [Finite (Sheaf.H S.X₁ n)]
    [Finite (Sheaf.H S.X₃ n)] : Finite (Sheaf.H S.X₂ n) := by
  let K := (Sheaf.H.map S.f n).range
  have hK : Finite K := Set.finite_range _ |>.to_subtype
  have hker : (Sheaf.H.map S.g n).ker = K := by
    ext x
    exact Sheaf.H.exact_map_map hS n x
  have : Finite (Sheaf.H S.X₂ n ⧸ K) := by
    rw [← hker]
    exact Finite.of_injective _ (QuotientAddGroup.kerLift_injective (Sheaf.H.map S.g n))
  exact (finite_iff_addSubgroup_quotient K).2 ⟨hK, this⟩

include hS in
/-- **The five lemma for pullback maps on cohomology, middle term.** Let
`0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` be a short exact sequence of abelian étale sheaves on `Y` and
`f : X ⟶ Y` a morphism of schemes. If the pullback maps `Hⁿ(Y, S.Xᵢ) ⟶ Hⁿ(X, f^* S.Xᵢ)` are
bijective for `i = 1, 3` and every `n`, then so are those for `i = 2`. -/
lemma bijective_cohomologyMap_X₂_of_shortExact
    (h₁ : ∀ n, Function.Bijective (cohomologyMap f S.X₁ n))
    (h₃ : ∀ n, Function.Bijective (cohomologyMap f S.X₃ n)) (n : ℕ) :
    Function.Bijective (cohomologyMap f S.X₂ n) := by
  have hS' := shortExact_map_upperStar f hS
  have hc (m : ℕ) {A B : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : A ⟶ B) :
      (Sheaf.H.map ((f)^*[AddCommGrpCat.{u + 1}].map φ) m).comp (cohomologyMap f A m) =
        (cohomologyMap f B m).comp (Sheaf.H.map φ m) :=
    AddMonoidHom.ext fun x ↦ (cohomologyMap_map f m φ x).symm
  have hδ (m : ℕ) : (Sheaf.H.δSucc hS' m).comp (cohomologyMap f S.X₃ m) =
      (cohomologyMap f S.X₁ (m + 1)).comp (Sheaf.H.δSucc hS m) :=
    AddMonoidHom.ext fun x ↦ (cohomologyMap_δSucc f hS m x).symm
  have hsurj : Function.Surjective (cohomologyMap f S.X₂ n) :=
    AddMonoidHom.surjective_of_surjective_of_surjective_of_injective
      (Sheaf.H.map S.f n) (Sheaf.H.map S.g n) (Sheaf.H.δSucc hS n)
      (Sheaf.H.map ((f)^*[AddCommGrpCat.{u + 1}].map S.f) n)
      (Sheaf.H.map ((f)^*[AddCommGrpCat.{u + 1}].map S.g) n) (Sheaf.H.δSucc hS' n)
      (cohomologyMap f S.X₁ n) (cohomologyMap f S.X₂ n) (cohomologyMap f S.X₃ n)
      (cohomologyMap f S.X₁ (n + 1)) (hc n S.f) (hc n S.g) (hδ n)
      (Sheaf.H.exact_map_δSucc hS n) (Sheaf.H.exact_map_map hS' n)
      (Sheaf.H.exact_map_δSucc hS' n) (h₁ n).2 (h₃ n).2 (h₁ (n + 1)).1
  refine ⟨?_, hsurj⟩
  rcases n with _ | n
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (Sheaf.H.exact_map_map hS 0 x).1 <| (h₃ 0).1 <| by
      rw [map_zero, cohomologyMap_map, hx, map_zero]
    have : Mono ((f)^*[AddCommGrpCat.{u + 1}].map S.f) := hS'.mono_f
    have hinj : Function.Injective (Sheaf.H.map ((f)^*[AddCommGrpCat.{u + 1}].map S.f) 0) :=
      Ext.postcomp_mk₀_injective_of_mono _ _
    have hy : cohomologyMap f S.X₁ 0 y = 0 :=
      hinj (by rw [map_zero, ← cohomologyMap_map, hx])
    rw [(h₁ 0).1 (hy.trans (map_zero _).symm), map_zero]
  · exact AddMonoidHom.injective_of_surjective_of_injective_of_injective
      (Sheaf.H.δSucc hS n) (Sheaf.H.map S.f (n + 1)) (Sheaf.H.map S.g (n + 1))
      (Sheaf.H.δSucc hS' n) (Sheaf.H.map ((f)^*[AddCommGrpCat.{u + 1}].map S.f) (n + 1))
      (Sheaf.H.map ((f)^*[AddCommGrpCat.{u + 1}].map S.g) (n + 1))
      (cohomologyMap f S.X₃ n) (cohomologyMap f S.X₁ (n + 1)) (cohomologyMap f S.X₂ (n + 1))
      (cohomologyMap f S.X₃ (n + 1)) (hδ n) (hc (n + 1) S.f) (hc (n + 1) S.g)
      (Sheaf.H.exact_δSucc_map hS n) (Sheaf.H.exact_map_map hS (n + 1))
      (Sheaf.H.exact_δSucc_map hS' n) (h₃ n).2 (h₁ (n + 1)).1 (h₃ (n + 1)).1

end LongExact

end Etale

namespace Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

/-- The geometric stalks of a monomorphism of étale sheaves of `Λ`-modules are injective. -/
lemma injective_sheafFiber_map_of_mono {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (ι : F ⟶ G) [Mono ι] {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    Function.Injective ((pointSmallEtale s).sheafFiber.map ι) := by
  have : Mono ((pointSmallEtale s).sheafFiber.map ι) := inferInstance
  exact (ModuleCat.mono_iff_injective _).1 this

/-- The geometric stalks of an epimorphism of étale sheaves of `Λ`-modules are surjective. -/
lemma surjective_sheafFiber_map_of_epi {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (π : F ⟶ G) [Epi π] {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    Function.Surjective ((pointSmallEtale s).sheafFiber.map π) := by
  have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  have := ((pointSmallEtale s).skyscraperSheafAdjunction (A := ModuleCat.{u + 1} Λ)).isLeftAdjoint
  exact (ModuleCat.epi_iff_surjective _).1 inferInstance

/-- A subsheaf of a `p`-primary torsion sheaf is `p`-primary torsion. -/
lemma IsPrimaryTorsionSheaf.of_mono {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (ι : F ⟶ G) [Mono ι] {p : ℕ} (hG : IsPrimaryTorsionSheaf Λ G p) :
    IsPrimaryTorsionSheaf Λ F p := fun Ω _ _ s x ↦ by
  obtain ⟨n, hn⟩ := hG Ω s ((pointSmallEtale s).sheafFiber.map ι x)
  exact ⟨n, injective_sheafFiber_map_of_mono ι s (by rw [map_nsmul, hn, map_zero])⟩

/-- A quotient of a `p`-primary torsion sheaf is `p`-primary torsion. -/
lemma IsPrimaryTorsionSheaf.of_epi {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (π : F ⟶ G) [Epi π] {p : ℕ} (hF : IsPrimaryTorsionSheaf Λ F p) :
    IsPrimaryTorsionSheaf Λ G p := fun Ω _ _ s x ↦ by
  obtain ⟨y, rfl⟩ := surjective_sheafFiber_map_of_epi π s x
  obtain ⟨n, hn⟩ := hF Ω s y
  exact ⟨n, by rw [← map_nsmul, hn, map_zero]⟩

/-- A subsheaf of a sheaf which is torsion of orders invertible on `S` is torsion of orders
invertible on `S`. -/
lemma IsTorsionSheafOfInvertibleOrder.of_mono (S : Scheme.{u})
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (ι : F ⟶ G) [Mono ι]
    [IsTorsionSheafOfInvertibleOrder S G] : IsTorsionSheafOfInvertibleOrder S F where
  exists_isUnit_nsmul_eq_zero Ω _ _ s x := by
    obtain ⟨n, hn, hu, hx⟩ := IsTorsionSheafOfInvertibleOrder.exists_isUnit_nsmul_eq_zero
      (S := S) Ω s ((pointSmallEtale s).sheafFiber.map ι x)
    exact ⟨n, hn, hu, injective_sheafFiber_map_of_mono ι s (by rw [map_nsmul, hx, map_zero])⟩

/-- A quotient of a sheaf which is torsion of orders invertible on `S` is torsion of orders
invertible on `S`. -/
lemma IsTorsionSheafOfInvertibleOrder.of_epi (S : Scheme.{u})
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (π : F ⟶ G) [Epi π]
    [IsTorsionSheafOfInvertibleOrder S F] : IsTorsionSheafOfInvertibleOrder S G where
  exists_isUnit_nsmul_eq_zero Ω _ _ s x := by
    obtain ⟨y, rfl⟩ := surjective_sheafFiber_map_of_epi π s x
    obtain ⟨n, hn, hu, hy⟩ := IsTorsionSheafOfInvertibleOrder.exists_isUnit_nsmul_eq_zero
      (S := S) Ω s y
    exact ⟨n, hn, hu, by rw [← map_nsmul, hy, map_zero]⟩

end Scheme

namespace IsCurve

open Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **Short exact dévissage for the eight curve assertions.** Let `X` be a curve over `k` and
`0 ⟶ F₁ ⟶ F ⟶ F₂ ⟶ 0` a short exact sequence of étale sheaves of `Λ`-modules on `X`. If the
eight assertions `C(X, F₁)` and `C(X, F₂)` hold, then so does `C(X, F)`: the long exact
cohomology sequences (and their pullbacks along a field extension) pass vanishing, finiteness
and bijectivity to the middle term, the hypotheses of the assertions being inherited by
subsheaves and quotients, constructibility for subsheaves since `Λ` is noetherian; for `C₈` one
uses `H³(X, F₁) = 0`, i.e. `C₁(X, F₁)`.
(blueprint: `lemma-weil-pbc-eight-curve-devissage`) -/
theorem Assertions.of_shortExact [IsNoetherianRing Λ] {k : Type u} [Field k]
    {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f]
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hS : S.ShortExact)
    (h₁ : IsCurve.Assertions Λ f S.X₁) (h₃ : IsCurve.Assertions Λ f S.X₃) :
    IsCurve.Assertions Λ f S.X₂ := by
  set Φ := sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  have hT : (S.map Φ).ShortExact := shortExact_map_sheafCompose_forget₂ hS
  have := hS.mono_f
  have := hS.epi_g
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := {}
  have hcons (hc : Scheme.IsConstructibleSheaf S.X₂) :
      Scheme.IsConstructibleSheaf S.X₁ ∧ Scheme.IsConstructibleSheaf S.X₃ := by
    have h₁ : Scheme.IsConstructibleSheaf S.X₁ := Scheme.IsConstructibleSheaf.of_mono S.f
    have := Scheme.IsConstructibleSheaf.cokernel S.f
    let e : S.X₃ ≅ cokernel S.f :=
      hS.exact.gIsCokernel.coconePointUniqueUpToIso (colimit.isColimit _)
    exact ⟨h₁, Scheme.IsConstructibleSheaf.of_iso e.symm⟩
  have hsub (q : ℕ) (ha : Subsingleton (Sheaf.H (Φ.obj S.X₁) q))
      (hb : Subsingleton (Sheaf.H (Φ.obj S.X₃) q)) : Subsingleton (Sheaf.H (Φ.obj S.X₂) q) :=
    have : Subsingleton (Sheaf.H (S.map Φ).X₁ q) := ha
    have : Subsingleton (Sheaf.H (S.map Φ).X₃ q) := hb
    subsingleton_H_X₂_of_shortExact hT q
  have hfin (q : ℕ) (ha : Finite (Sheaf.H (Φ.obj S.X₁) q))
      (hb : Finite (Sheaf.H (Φ.obj S.X₃) q)) : Finite (Sheaf.H (Φ.obj S.X₂) q) :=
    have : Finite (Sheaf.H (S.map Φ).X₁ q) := ha
    have : Finite (Sheaf.H (S.map Φ).X₃ q) := hb
    finite_H_X₂_of_shortExact hT q
  refine ⟨fun q hq ↦ hsub q (h₁.subsingleton_of_two_lt q hq) (h₃.subsingleton_of_two_lt q hq),
    fun q hq ↦ hsub q (h₁.subsingleton_of_one_lt_of_isAffine q hq)
      (h₃.subsingleton_of_one_lt_of_isAffine q hq),
    fun p _ _ hp q hq ↦ hsub q
      (h₁.subsingleton_of_one_lt_of_isPrimaryTorsionSheaf p (hp.of_mono S.f) q hq)
      (h₃.subsingleton_of_one_lt_of_isPrimaryTorsionSheaf p (hp.of_epi S.g) q hq),
    fun q ↦ ?_, fun q ↦ ?_, fun k' _ _ X' ι f' ι' h q ↦ ?_, fun k' _ _ X' ι f' ι' h q ↦ ?_,
    fun {W} a _ ↦ ?_⟩
  · rename_i hc _
    obtain ⟨_, _⟩ := hcons hc
    have := Scheme.IsTorsionSheafOfInvertibleOrder.of_mono (Spec (.of k)) S.f
    have := Scheme.IsTorsionSheafOfInvertibleOrder.of_epi (Spec (.of k)) S.g
    exact hfin q (h₁.finite_of_isTorsionSheafOfInvertibleOrder q)
      (h₃.finite_of_isTorsionSheafOfInvertibleOrder q)
  · rename_i _ hc
    obtain ⟨_, _⟩ := hcons hc
    exact hfin q (h₁.finite_of_isProper q) (h₃.finite_of_isProper q)
  · have := Scheme.IsTorsionSheafOfInvertibleOrder.of_mono (Spec (.of k)) S.f
    have := Scheme.IsTorsionSheafOfInvertibleOrder.of_epi (Spec (.of k)) S.g
    exact bijective_cohomologyMap_X₂_of_shortExact ι' hT
      (h₁.bijective_cohomologyMap_of_isTorsionSheafOfInvertibleOrder k' h)
      (h₃.bijective_cohomologyMap_of_isTorsionSheafOfInvertibleOrder k' h) q
  · exact bijective_cohomologyMap_X₂_of_shortExact ι' hT
      (h₁.bijective_cohomologyMap_of_isProper k' h)
      (h₃.bijective_cohomologyMap_of_isProper k' h) q
  · -- `C₈`, following the long exact sequences on `X` and on `W`
    set T := S.map Φ
    have hT' := shortExact_map_upperStar a hT
    have : Subsingleton (Sheaf.H T.X₁ (2 + 1)) := h₁.subsingleton_of_two_lt 3 (by omega)
    have hs₁ : Function.Surjective (cohomologyMap a T.X₁ 2) :=
      h₁.surjective_cohomologyMap_of_isOpenImmersion a
    have hs₃ : Function.Surjective (cohomologyMap a T.X₃ 2) :=
      h₃.surjective_cohomologyMap_of_isOpenImmersion a
    change Function.Surjective (cohomologyMap a T.X₂ 2)
    intro c
    obtain ⟨x₂, hx₂⟩ := hs₃ (Sheaf.H.map (T.map (a)^*[AddCommGrpCat.{u + 1}]).g 2 c)
    obtain ⟨x, rfl⟩ := (Sheaf.H.exact_map_δSucc hT 2 x₂).1 (Subsingleton.elim _ _)
    obtain ⟨d₁, hd₁⟩ := (Sheaf.H.exact_map_map hT' 2 (c - cohomologyMap a T.X₂ 2 x)).1 <| by
      rw [map_sub, sub_eq_zero]
      exact hx₂.symm.trans (cohomologyMap_map a 2 T.g x)
    obtain ⟨y₁, hy₁⟩ := hs₁ d₁
    refine ⟨x + Sheaf.H.map T.f 2 y₁, ?_⟩
    rw [map_add, cohomologyMap_map]
    change _ + Sheaf.H.map (T.map (a)^*[AddCommGrpCat.{u + 1}]).f 2 (cohomologyMap a T.X₁ 2 y₁) = c
    rw [hy₁, hd₁, add_sub_cancel]

end IsCurve

end AlgebraicGeometry
