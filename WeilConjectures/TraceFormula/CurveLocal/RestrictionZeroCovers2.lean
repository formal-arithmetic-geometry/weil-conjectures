/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.CurveLocal.RestrictionZeroLocalization2
public import WeilConjectures.AlgebraicGeometry.Sites.StrictLocalizationMap
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.TraceFormula.CurveLocal.BlowupRestriction
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic

/-! # Prime-to-`ℓ` covers separating graph and diagonal

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-trace-formula/
sec-tf-curve-local/sec-the-local-term-as-a-restriction-map/sk-lem-tf-curve-restriction-zero/
det-tf-restriction-zero-covers.md, clauses (i)--(iii), with the strict localization made
explicit as the finite base change `T' = T ×_{X ×_k Y} (X' ×_k Y')`
(blueprint: det-tf-restriction-zero-covers).

We work in the situation of `det-tf-restriction-zero-localization`
(`AlgebraicGeometry.Etale.CurveLocalModel.restrictionZeroLocalization`): the two strictly local
traits `X`, `Y` are identical copies of `strictLocalization M.y`, and `T` is the strict
localization of the curve square at `(y, y)`. The canonical maps `T ⟶ X ×_k Y` are the
functorial strict-localization maps of the two projections; the fibre product `T'` is the
Mathlib `pullback` (`def-pc-fibre-product`). The reduced inverse images `D' = G' ∪ V'`, `H'`,
`B'` are characterized as reduced closed subschemes of `T'` whose underlying sets are the
preimages of the corresponding curves of `T`; this determines them uniquely.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.CurveLocalModel

open Scheme

variable {k : Type u} [Field k] [IsAlgClosed k] (M : CurveLocalModel k)

/-- The structure morphism `X ⟶ Spec k` of the strictly local trait `X = Y` at `y`.
Source: clause (i), the traits `X`, `Y` (blueprint: det-tf-restriction-zero-covers). -/
abbrev traitToBase : strictLocalization M.y ⟶ Spec (.of k) :=
  strictLocalizationToBase M.y ≫ M.f

/-- The canonical first map `T ⟶ X`: the strict-localization map of the first projection.
Source: the statement, `T ⟶ X ×_k Y` (blueprint: det-tf-restriction-zero-covers). -/
def traitProjFst : M.T ⟶ strictLocalization M.y :=
  strictLocalizationMap (pullback.fst M.f M.f) M.diagPoint ≫
    eqToHom (congrArg strictLocalization (pullback.lift_fst M.y M.y rfl))

/-- The canonical second map `T ⟶ Y`: the strict-localization map of the second projection.
Source: the statement, `T ⟶ X ×_k Y` (blueprint: det-tf-restriction-zero-covers). -/
def traitProjSnd : M.T ⟶ strictLocalization M.y :=
  strictLocalizationMap (pullback.snd M.f M.f) M.diagPoint ≫
    eqToHom (congrArg strictLocalization (pullback.lift_snd M.y M.y rfl))

/-- The product `X ×_k Y` of the two strictly local traits.
Source: the statement (blueprint: det-tf-restriction-zero-covers). -/
abbrev traitProduct : Scheme.{u} :=
  pullback M.traitToBase M.traitToBase

/-- The canonical map `T ⟶ X ×_k Y` with components the two strict-localization maps.
Source: the statement, `T' = T ×_{X ×_k Y} (X' ×_k Y')`
(blueprint: det-tf-restriction-zero-covers). -/
def toTraitProduct : M.T ⟶ M.traitProduct :=
  pullback.lift M.traitProjFst M.traitProjSnd (by
    have transport {C : Scheme.{u}} {x y : Spec (.of k) ⟶ C} (h : x = y) :
        eqToHom (congrArg strictLocalization h) ≫ strictLocalizationToBase y =
          strictLocalizationToBase x := by
      cases h
      exact Category.id_comp _
    have h₁ : M.traitProjFst ≫ strictLocalizationToBase M.y =
        strictLocalizationToBase M.diagPoint ≫ pullback.fst M.f M.f := by
      unfold traitProjFst
      rw [Category.assoc, transport (pullback.lift_fst M.y M.y rfl)]
      exact strictLocalizationMap_comp_strictLocalizationToBase _ _
    have h₂ : M.traitProjSnd ≫ strictLocalizationToBase M.y =
        strictLocalizationToBase M.diagPoint ≫ pullback.snd M.f M.f := by
      unfold traitProjSnd
      rw [Category.assoc, transport (pullback.lift_snd M.y M.y rfl)]
      exact strictLocalizationMap_comp_strictLocalizationToBase _ _
    simp only [traitToBase, ← Category.assoc, h₁, h₂]
    simpa only [Category.assoc] using
      congrArg (fun a ↦ strictLocalizationToBase M.diagPoint ≫ a)
        (pullback.condition (f := M.f) (g := M.f)))

/-- The product `p ×_k q : X' ×_k Y' ⟶ X ×_k Y` of two covers of the trait.
Source: the statement (blueprint: det-tf-restriction-zero-covers). -/
def coverProduct {X' Y' : Scheme.{u}} (p : X' ⟶ strictLocalization M.y)
    (q : Y' ⟶ strictLocalization M.y) :
    pullback (p ≫ M.traitToBase) (q ≫ M.traitToBase) ⟶ M.traitProduct :=
  pullback.map _ _ _ _ p q (𝟙 _) (Category.comp_id _) (Category.comp_id _)

/-- The finite base change `T' = T ×_{X ×_k Y} (X' ×_k Y')`, with no localization added.
Source: the statement (blueprint: det-tf-restriction-zero-covers). -/
abbrev coverChart {X' Y' : Scheme.{u}} (p : X' ⟶ strictLocalization M.y)
    (q : Y' ⟶ strictLocalization M.y) : Scheme.{u} :=
  pullback M.toTraitProduct (M.coverProduct p q)

/-- The projection `T' ⟶ T`.
Source: the statement, clause (ii) (blueprint: det-tf-restriction-zero-covers). -/
abbrev coverChartMap {X' Y' : Scheme.{u}} (p : X' ⟶ strictLocalization M.y)
    (q : Y' ⟶ strictLocalization M.y) : M.coverChart p q ⟶ M.T :=
  pullback.fst _ _

/-- `p : X' ⟶ X` is a finite cover of degree `d`, generically étale, by a strictly local
regular trait: `X'` is the spectrum of a strictly henselian discrete valuation ring, `p` is
finite locally free of constant degree `d`, and `p` is étale over the punctured trait
`X - y`, which is the generic point of `X`.
Source: the statement, first sentence (blueprint: det-tf-restriction-zero-covers). -/
def IsStrictTraitCover {X' : Scheme.{u}} (p : X' ⟶ strictLocalization M.y) (d : ℕ) : Prop :=
  IsAffine X' ∧ (∃ _ : IsDomain Γ(X', ⊤), IsDiscreteValuationRing Γ(X', ⊤)) ∧
    IsStrictlyHenselianLocalRing Γ(X', ⊤) ∧ p.IsFiniteLocallyFreeOfDegree d ∧
    Etale (p ∣_ M.localizationPuncture)

end AlgebraicGeometry.Etale.CurveLocalModel

namespace AlgebraicGeometry.Etale

open Scheme

/-- `F` admits a bounded finite projective lisse model whose termwise monodromy factors
through finite `ℓ`-groups: a bounded complex representing `F` each of whose terms becomes
constant, with finite projective value, on a finite étale Galois cover with group a finite
`ℓ`-group.
Source: clause (i) (blueprint: det-tf-restriction-zero-covers). -/
def HasEllGroupLisseModel (ell : ℕ) {U : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    (F : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) : Prop :=
  ∃ (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) (a b : ℤ),
    P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧ Nonempty (F ≅ DerivedCategory.Q.obj P) ∧
    ∀ n : ℤ, ∃ (G : Type (u + 1)) (_ : Group G) (_ : Finite G) (_ : IsPGroup ell G)
      (c : Scheme.GaloisCover G U) (V : ModuleCat.{u + 1} Λ) (_ : Module.Finite Λ V)
      (_ : Module.Projective Λ V),
      Nonempty ((c.π)^*[ModuleCat.{u + 1} Λ].obj (P.X n) ≅
        (constantSheaf c.P.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj V)

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale.CurveLocalModel

open Scheme

local instance {S T : Scheme.{u}} (f : S ⟶ T)
    [SmoothOfRelativeDimension 1 f] : Smooth f :=
  SmoothOfRelativeDimension.smooth 1 f

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- **Prime-to-`ℓ` covers separating graph and diagonal.**

Source: clauses (i)--(iii) and their proof in
literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-trace-formula/
sec-tf-curve-local/sec-the-local-term-as-a-restriction-map/sk-lem-tf-curve-restriction-zero/
det-tf-restriction-zero-covers.md (blueprint: det-tf-restriction-zero-covers).

In the situation of `restrictionZeroLocalization`, there are covers `p : X' ⟶ X`,
`q : Y' ⟶ Y` of the same degree `d` prime to `ℓ` as in `IsStrictTraitCover`. With
`T' = T ×_{X ×_k Y} (X' ×_k Y')` (`coverChart`, projection `π = coverChartMap`):
(i) the pullbacks `N'`, `Q'` of `N`, `Q` to the punctured covering traits satisfy
`HasEllGroupLisseModel`; (ii) `T'` is the strict localization of a smooth `k`-surface at a
`k`-point, its completed local ring is `k[[ξ, η]]` over `k`, `π` is finite locally free of
degree `d²` and étale over `T - (H ∪ V)`; the reduced inverse image `B'` maps to `B`, and over
`B - y` (whose inverse image is `B' - y'`) this map is finite étale of degree `d²`; (iii) the
tangent cone of the reduced inverse image `D' = G' ∪ V'` meets those of `B'` and `H'` only at
the origin.

Proof plan, following the seven reviewed DAG steps: (1) `D_C K`, `K` are in `D^b_ctf`; flat
constructible models on the curve restrict to the generic point of the trait, giving a finite
family of finite projective local systems representing `N`, `Q`. (2) A simultaneous Sylow
cover of the field scheme `U = X - y` has degree `d` prime to `ℓ` and an `ℓ`-group torsor
trivializing all terms; normalizing the trait in the corresponding separable extension gives
`X'`, and the same cover on the second copy gives `Y'`, so both degrees are `d`; pulled-back
models keep their constant finite projective values. (3) The finite-trait-cover product lemma
and ind-étale strict-local invariance identify `T'` with the strict localization of a smooth
surface with completion `k[[ξ, η]]`; tensoring the two bases gives rank `d²`. (4) Over
`T - (H ∪ V)` the map is a composite of base changes of finite étale covers, hence étale;
`B` is the strict localization of the curve, `B - y` is a field scheme inside `T - (H ∪ V)`, so
its inverse image is reduced, finite étale of degree `d²`, and equals `B' - y'`. (5) By the
Frobenius factorization, `φ(v) = (Φ^m)^♯ u` has order `q^m ≥ 2`, and `u = aξ^d`, `v = bη^d`.
(6) `gr R' = k[Ξ, Η]`; the elements `u(u - φ(v))`, `u - v`, `v` of the radical ideals of `D'`,
`B'`, `H'` have initial forms `α²Ξ^{2d}`, `αΞ^d - βΗ^d`, `βΗ^d`. (7) Their zero loci meet
pairwise only at the origin, also when `p ∣ d`. -/
theorem restrictionZeroCovers
    {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k]
    (X : Over (Spec (.of k))) [QuasiCompact X.hom] [IsSeparated X.hom]
    [SmoothOfRelativeDimension 1 X.hom]
    {X₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k₀)} {p : X.left ⟶ X₀}
    {Φ : X ⟶ X}
    (hΦ : ProEtale.CondensedRing.IsModelFrobenius Φ f₀ p)
    (m : ℕ) (hm : 1 ≤ m)
    (y : ProEtale.CondensedRing.RationalPoint X)
    (hy : y ≫ ProEtale.CondensedRing.frobeniusIterate Φ m = y)
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (ell : ℕ) [Fact ell.Prime] (hell : (ell : k) ≠ 0)
    (hΛ : ∃ n : ℕ, (ell : Λ) ^ n = 0)
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hctf : DerivedCategory.boundedConstructibleFiniteTor Λ X.left K)
    (hK : IsZero (D((y.left)^*[ModuleCat.{u + 1} Λ]).obj K)) :
    let M := ofModelFrobenius hΦ hm y hy
    let L := (verdierDual Λ M.f).obj (op K)
    let c := strictLocalizationToBase M.y
    let j := M.localizationPuncture.ι
    let Kloc := D((c)^*[ModuleCat.{u + 1} Λ]).obj K
    let Lloc := D((c)^*[ModuleCat.{u + 1} Λ]).obj L
    let N := D((j)^*[ModuleCat.{u + 1} Λ]).obj Lloc
    let Q := D((j)^*[ModuleCat.{u + 1} Λ]).obj Kloc
    ∃ (X' Y' : Scheme.{u}) (pX : X' ⟶ strictLocalization M.y)
      (pY : Y' ⟶ strictLocalization M.y) (d : ℕ),
      ¬ ell ∣ d ∧ M.IsStrictTraitCover pX d ∧ M.IsStrictTraitCover pY d ∧
      HasEllGroupLisseModel ell
        (D((pX ∣_ M.localizationPuncture)^*[ModuleCat.{u + 1} Λ]).obj N) ∧
      HasEllGroupLisseModel ell
        (D((pY ∣_ M.localizationPuncture)^*[ModuleCat.{u + 1} Λ]).obj Q) ∧
      (∃ (S' : Scheme.{u}) (aS' : S' ⟶ Spec (.of k)) (_ : SmoothOfRelativeDimension 2 aS')
        (s' : Spec (.of k) ⟶ S') (_ : s' ≫ aS' = 𝟙 _)
        (e : M.coverChart pX pY ≅ strictLocalization s'),
        e.hom ≫ strictLocalizationToBase s' ≫ aS' =
          M.coverChartMap pX pY ≫ M.τ ≫ pullback.fst M.f M.f ≫ M.f ∧
        (∃ φ : MvPowerSeries (Fin 2) k ≃+*
            AdicCompletion (IsLocalRing.maximalIdeal (strictHenselization s'))
              (strictHenselization s'),
          ∀ a : k, φ (MvPowerSeries.C a) =
            algebraMap _ (AdicCompletion (IsLocalRing.maximalIdeal (strictHenselization s'))
              (strictHenselization s'))
              (((Scheme.ΓSpecIso (.of k)).inv ≫ (strictLocalizationToBase s' ≫ aS').appTop ≫
                (Scheme.ΓSpecIso (strictHenselization s')).hom).hom a)) ∧
        (M.coverChartMap pX pY).IsFiniteLocallyFreeOfDegree (d ^ 2) ∧
        Etale (M.coverChartMap pX pY ∣_ M.twoAxesOpen) ∧
        ∃ (D' H' B' : Scheme.{u}) (dD' : D' ⟶ M.coverChart pX pY)
          (dH' : H' ⟶ M.coverChart pX pY) (dB' : B' ⟶ M.coverChart pX pY)
          (_ : IsClosedImmersion dD') (_ : IsClosedImmersion dH') (_ : IsClosedImmersion dB')
          (_ : IsReduced D') (_ : IsReduced H') (_ : IsReduced B'),
          Set.range dD'.base = (M.coverChartMap pX pY).base ⁻¹'
            (Set.range M.a.base ∪ Set.range M.v.base) ∧
          Set.range dH'.base = (M.coverChartMap pX pY).base ⁻¹' Set.range M.hH.base ∧
          Set.range dB'.base = (M.coverChartMap pX pY).base ⁻¹' Set.range M.b.base ∧
          ∃ βB : B' ⟶ M.B, βB ≫ M.b = dB' ≫ M.coverChartMap pX pY ∧
            IsFinite (βB ∣_ M.yB.openComplement) ∧ Etale (βB ∣_ M.yB.openComplement) ∧
            (βB ∣_ M.yB.openComplement).IsFiniteLocallyFreeOfDegree (d ^ 2) ∧
            IsLocalRing.TangentConesMeetAtOrigin (strictHenselization s')
              (specIdeal (dD' ≫ e.hom)) (specIdeal (dB' ≫ e.hom)) ∧
            IsLocalRing.TangentConesMeetAtOrigin (strictHenselization s')
              (specIdeal (dD' ≫ e.hom)) (specIdeal (dH' ≫ e.hom))) := by
  sorry

end AlgebraicGeometry.Etale.CurveLocalModel
