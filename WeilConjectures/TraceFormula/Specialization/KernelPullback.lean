/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Functor

/-!

# The specialized coefficient as a section of the kernel, abstractly

Let `c : C ⟶ X ×_S X` be a correspondence, `S_P`, `S_C` the nearby cycles on `X ×_S X` and `C`
(lax monoidal), `α_c : c_s^* S_P ⟶ S_C c^*` and `β_c : S_C c^! ⟶ c_s^! S_P` the pullback and
exceptional exchanges, and `t_c : c^* N ⊗ c^! M ⟶ c^!(N ⊗ M)` the projection-formula map. For
`A = p₂^* K`, `B = p₁^! K` and their specializations `A' = p₂ₛ^* K'`, `B' = p₁ₛ^! K'`, with
`a = α_{p₂} : A' ⟶ S_P A` and `b = β_{p₁} : S_P B ⟶ B'`, the map
`𝔥 : S_P RHom(A, B) ⟶ RHom(A', B')` is the mate of `S_P(ev) ∘ μ`, precomposed with `a` and
postcomposed with `b`, and `𝔥_c` is defined in the same way on `C`, with `α_{c₂} = α_c ∘ c_s^* a`
and `β_{c₁} = c_s^! b ∘ β_c` (the composition laws of the exchanges). The external duality
isomorphism of `c` is `λ_{c,K} = τ_c ∘ c^! λ_K` for the exceptional internal hom exchange
`τ_c : c^! RHom(A, B) ⟶ RHom(c^* A, c^! B)`, the mate of `c^!(ev) ∘ t_c`.

Blueprint `det-tf-sp-kernel-pullback` states

`𝔥_c S_C(λ_{c_η,K}) = λ_{c_s,K'} c_s^! ρ β_c(P_X)`,

given the first identity `𝔥 S(λ_K) = λ_{K'} ρ` of blueprint `det-tf-sp-universal-kernel`, and
deduces the section `k_{u_s}` of the specialized coefficient `u_s = β_{c₁} S_C(u) α_{c₂}`.
This file proves both for abstract monoidal categories and lax monoidal functors:

* `CategoryTheory.map_comp_exchangeHom_eq`: the exchange `τ` commutes with `𝔥` and `𝔥_c`,
  `S_C(τ_c) ≫ 𝔥_c = β_c ≫ c_s^!(𝔥) ≫ τ_{c_s}`, from the compatibility of `β_c` with the
  projection formula (blueprint `det-nearby-exceptional-tensor` (2));
* `CategoryTheory.map_externalDuality_comp_eq`: the displayed identity;
* `CategoryTheory.name_comp_eq_of_section`: the section of the specialized coefficient.

-/

@[expose] public section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal

namespace CategoryTheory

variable {CP CP' CC CC' : Type*} [Category CP] [Category CP'] [Category CC] [Category CC']
  [MonoidalCategory CP] [MonoidalCategory CP'] [MonoidalCategory CC] [MonoidalCategory CC']
  {SP : CP ⥤ CP'} {SC : CC ⥤ CC'} [SP.LaxMonoidal] [SC.LaxMonoidal]
  {U L : CP ⥤ CC} {U' L' : CP' ⥤ CC'}

/-- **The exceptional internal hom exchange commutes with `𝔥`** (the core of blueprint
`det-tf-sp-kernel-pullback`): let `ev : A ⊗ H ⟶ B` and `ev' : A' ⊗ H' ⟶ B'` be evaluations,
`h : S_P H ⟶ H'` the map adjoint to `(a ⊗ 1) ≫ μ ≫ S_P(ev) ≫ b`, `τ : U H ⟶ H_c` a map adjoint
to `t ≫ U(ev)` for `t : L A ⊗ U H ⟶ U (A ⊗ H)`, `τ'` the map adjoint to `t' ≫ U'(ev')`, and `h_c`
the map adjoint to `((L' a ≫ α) ⊗ 1) ≫ μ ≫ S_C(ev_c) ≫ β ≫ U'(b)`. If `β` is compatible with
the projection-formula maps `t`, `t'` (blueprint `det-nearby-exceptional-tensor` (2)) and `t'` is
natural, then `S_C(τ) ≫ h_c = β ≫ U'(h) ≫ τ'`. -/
theorem map_comp_exchangeHom_eq [MonoidalClosed CC']
    (α : SP ⋙ L' ⟶ L ⋙ SC) (β : U ⋙ SC ⟶ SP ⋙ U')
    {A B H : CP} {A' B' H' : CP'} (ev : A ⊗ H ⟶ B) (ev' : A' ⊗ H' ⟶ B') (a : A' ⟶ SP.obj A)
    (b : SP.obj B ⟶ B') (h : SP.obj H ⟶ H')
    (hh : A' ◁ h ≫ ev' = a ▷ SP.obj H ≫ μ SP A H ≫ SP.map ev ≫ b)
    {Hc : CC} (evc : L.obj A ⊗ Hc ⟶ U.obj B) (t : L.obj A ⊗ U.obj H ⟶ U.obj (A ⊗ H))
    (τ : U.obj H ⟶ Hc) (hτ : L.obj A ◁ τ ≫ evc = t ≫ U.map ev)
    (t' : ∀ N M : CP', L'.obj N ⊗ U'.obj M ⟶ U'.obj (N ⊗ M))
    (ht'₁ : L'.obj A' ◁ U'.map h ≫ t' A' H' = t' A' (SP.obj H) ≫ U'.map (A' ◁ h))
    (ht'₂ : L'.map a ▷ U'.obj (SP.obj H) ≫ t' (SP.obj A) (SP.obj H) =
      t' A' (SP.obj H) ≫ U'.map (a ▷ SP.obj H))
    (hβ : α.app A ▷ SC.obj (U.obj H) ≫ μ SC (L.obj A) (U.obj H) ≫ SC.map t ≫ β.app (A ⊗ H) =
      L'.obj (SP.obj A) ◁ β.app H ≫ t' (SP.obj A) (SP.obj H) ≫ U'.map (μ SP A H))
    (τ' : U'.obj H' ⟶ (ihom (L'.obj A')).obj (U'.obj B'))
    (hτ' : MonoidalClosed.uncurry τ' = t' A' H' ≫ U'.map ev')
    (hc : SC.obj Hc ⟶ (ihom (L'.obj A')).obj (U'.obj B'))
    (hhc : MonoidalClosed.uncurry hc = (L'.map a ≫ α.app A) ▷ SC.obj Hc ≫
      μ SC (L.obj A) Hc ≫ SC.map evc ≫ β.app B ≫ U'.map b) :
    SC.map τ ≫ hc = β.app H ≫ U'.map h ≫ τ' := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, hhc, MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_natural_left, hτ']
  have hn : SC.map (U.map ev) ≫ β.app B = β.app (A ⊗ H) ≫ U'.map (SP.map ev) := β.naturality ev
  calc L'.obj A' ◁ SC.map τ ≫ (L'.map a ≫ α.app A) ▷ SC.obj Hc ≫
        μ SC (L.obj A) Hc ≫ SC.map evc ≫ β.app B ≫ U'.map b
      = L'.map a ▷ SC.obj (U.obj H) ≫ (α.app A ▷ SC.obj (U.obj H) ≫
          μ SC (L.obj A) (U.obj H) ≫ SC.map t ≫ β.app (A ⊗ H)) ≫
          U'.map (SP.map ev) ≫ U'.map b := by
        rw [whisker_exchange_assoc]
        simp only [Functor.comp_obj]
        rw [μ_natural_right_assoc, ← SC.map_comp_assoc, hτ,
          SC.map_comp_assoc, reassoc_of% hn, comp_whiskerRight_assoc]
        simp only [Category.assoc]
    _ = L'.obj A' ◁ β.app H ≫ t' A' (SP.obj H) ≫
          U'.map (a ▷ SP.obj H ≫ μ SP A H ≫ SP.map ev ≫ b) := by
        rw [hβ]
        simp only [Category.assoc]
        rw [← whisker_exchange_assoc]
        simp only [Functor.comp_obj]
        rw [reassoc_of% ht'₂]
        simp only [Functor.map_comp]
    _ = L'.obj A' ◁ β.app H ≫ L'.obj A' ◁ U'.map h ≫ t' A' H' ≫ U'.map ev' := by
        rw [reassoc_of% ht'₁, ← U'.map_comp, hh]

omit [MonoidalCategory CP] [MonoidalCategory CP'] [MonoidalCategory CC] [MonoidalCategory CC']
  [SP.LaxMonoidal] [SC.LaxMonoidal] in
/-- **The specialized external duality** (blueprint `det-tf-sp-kernel-pullback`, the displayed
identity `𝔥_c S_C(λ_{c_η,K}) = λ_{c_s,K'} c_s^! ρ β_c(P_X)`): if `λ_c = τ ∘ U(λ_K)` and
`λ_{c_s} = τ' ∘ U'(λ_{K'})`, the exchange `τ` commutes with `𝔥` (`map_comp_exchangeHom_eq`) and
`𝔥 S(λ_K) = λ_{K'} ρ` (blueprint `det-tf-sp-universal-kernel`, first identity), then
`S_C(λ_c) ≫ 𝔥_c = β ≫ U'(ρ) ≫ λ_{c_s}`. -/
theorem map_externalDuality_comp_eq (β : U ⋙ SC ⟶ SP ⋙ U') {P H : CP} {P' H' : CP'} {Hc : CC}
    {Hc' : CC'} (h : SP.obj H ⟶ H') (τ : U.obj H ⟶ Hc) (τ' : U'.obj H' ⟶ Hc')
    (hc : SC.obj Hc ⟶ Hc') (hX : SC.map τ ≫ hc = β.app H ≫ U'.map h ≫ τ')
    (lamK : P ⟶ H) (lamK' : P' ⟶ H') (ρ : SP.obj P ⟶ P')
    (h₁ : SP.map lamK ≫ h = ρ ≫ lamK') :
    SC.map (U.map lamK ≫ τ) ≫ hc = β.app P ≫ U'.map ρ ≫ U'.map lamK' ≫ τ' := by
  have hn : SC.map (U.map lamK) ≫ β.app H = β.app P ≫ U'.map (SP.map lamK) := β.naturality lamK
  rw [SC.map_comp, Category.assoc, hX, reassoc_of% hn, ← U'.map_comp_assoc, h₁,
    U'.map_comp_assoc]

/-- **The name of the specialization of a morphism**: for a lax monoidal `F`, morphisms
`g : X' ⟶ F X`, `k : F Y ⟶ Y'` and the map `h_c : F RHom(X, Y) ⟶ RHom(X', Y')` adjoint to
`(g ⊗ 1) ≫ μ ≫ F(ev) ≫ k`, the name `𝟙 ⟶ RHom(X', Y')` of `g ≫ F(u) ≫ k` is
`ε ≫ F(name u) ≫ h_c`. -/
theorem unit_comp_map_curry_comp_eq [MonoidalClosed CC] [MonoidalClosed CC'] {F : CC ⥤ CC'}
    [F.LaxMonoidal] {X Y : CC} {X' Y' : CC'} (g : X' ⟶ F.obj X) (k : F.obj Y ⟶ Y')
    (hc : F.obj ((ihom X).obj Y) ⟶ (ihom X').obj Y')
    (hhc : MonoidalClosed.uncurry hc = g ▷ F.obj ((ihom X).obj Y) ≫
      μ F X ((ihom X).obj Y) ≫ F.map ((ihom.ev X).app Y) ≫ k) (u : X ⟶ Y) :
    ε F ≫ F.map (MonoidalClosed.curry ((ρ_ X).hom ≫ u)) ≫ hc =
      MonoidalClosed.curry ((ρ_ X').hom ≫ g ≫ F.map u ≫ k) := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_natural_left, hhc, whisker_exchange_assoc, whisker_exchange_assoc,
    μ_natural_right_assoc, ← F.map_comp_assoc, ← MonoidalClosed.uncurry_eq,
    MonoidalClosed.uncurry_curry, F.map_comp_assoc, reassoc_of% (right_unitality F X).symm,
    rightUnitor_naturality_assoc]

omit [MonoidalCategory CP] [MonoidalCategory CP'] [SP.LaxMonoidal] in
/-- **The section of the specialized coefficient** (blueprint `det-tf-sp-kernel-pullback`, second
part): if `u : c₂^* K ⟶ c₁^! K` corresponds to the section `k_u : 𝟙 ⟶ c^! P_X` (its name is
`λ_c ∘ k_u`), then the specialized coefficient `u_s = β_{c₁} ∘ S_C(u) ∘ α_{c₂}` corresponds to
`c_s^! ρ ∘ β_c ∘ S_C(k_u) ∘ σ_C`, for the unit `σ_C = ε` of `S_C`. -/
theorem curry_comp_eq_of_section [MonoidalClosed CC] [MonoidalClosed CC']
    (β : U ⋙ SC ⟶ SP ⋙ U') {P H : CP} {P' H' : CP'} {X Y : CC} {X' Y' : CC'}
    (h : SP.obj H ⟶ H') (τ : U.obj H ⟶ (ihom X).obj Y) (τ' : U'.obj H' ⟶ (ihom X').obj Y')
    (g : X' ⟶ SC.obj X) (k : SC.obj Y ⟶ Y') (hc : SC.obj ((ihom X).obj Y) ⟶ (ihom X').obj Y')
    (hhc : MonoidalClosed.uncurry hc = g ▷ SC.obj ((ihom X).obj Y) ≫
      μ SC X ((ihom X).obj Y) ≫ SC.map ((ihom.ev X).app Y) ≫ k)
    (hX : SC.map τ ≫ hc = β.app H ≫ U'.map h ≫ τ')
    (lamK : P ⟶ H) (lamK' : P' ⟶ H') (ρ : SP.obj P ⟶ P')
    (h₁ : SP.map lamK ≫ h = ρ ≫ lamK') (u : X ⟶ Y) (ku : 𝟙_ CC ⟶ U.obj P)
    (hk : ku ≫ U.map lamK ≫ τ = MonoidalClosed.curry ((ρ_ X).hom ≫ u)) :
    MonoidalClosed.curry ((ρ_ X').hom ≫ g ≫ SC.map u ≫ k) =
      ε SC ≫ SC.map ku ≫ β.app P ≫ U'.map ρ ≫ U'.map lamK' ≫ τ' := by
  rw [← unit_comp_map_curry_comp_eq g k hc hhc u, ← hk, SC.map_comp, Category.assoc,
    map_externalDuality_comp_eq β h τ τ' hc hX lamK lamK' ρ h₁]

end CategoryTheory
