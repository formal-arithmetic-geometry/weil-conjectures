/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.AlgebraicGeometry.SepFinType
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Finite-horizontal compact-support exchange and ordinary units

This is the statement node `lem-trf-finite-horizontal-shriek-mate-general`.  The coefficient
ring is used through the ordinary constant pro-etale module categories (the discrete condensed
ring has pullback `A_T = p_T^* A`).  The composition comparison is the normalized
ordinary finite-coefficient compact-support comparison of formula (C); its proof is postponed.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-trace-formula/
sec-frobenius-and-rf/sk-i-relative-frob/sk-i-relative-frob.proof.md, item (3),
“Since base change is compatible with these units”; Stacks Tags 0F7L and 0F7J.
Proof steps: expand the compactification into open and proper parts; identify the proper/open
comparison; compute the independent open/proper interchange; compose the proper direct images
with their canonical compositor; transport along finite-ring etale origin; apply naturality and
triangles; conclude by the hom-bijection characterization of the inverse square mate.
(blueprint: lem-trf-finite-horizontal-shriek-mate-general)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- The canonical open/proper interchange used by the compact-support composition comparison.
It is the mate of the specified derived open-extension base-change isomorphism, independently
of the compact-support exchange. It is the map `γ` of formula (C) and equation (O) of the
node proof.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-trace-formula/
sec-frobenius-and-rf/sk-i-relative-frob/sk-i-relative-frob.proof.md,
item (3), formula (C); Stacks Tags 0F7B (lemma-shriek-proper-and-open) and 0F7J
(identity-open proper normalization).
(blueprint: lem-trf-finite-horizontal-shriek-mate-general) -/
noncomputable def finiteHorizontalOpenProperGamma
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (k : Type u) [Field k] [IsAlgClosed k]
    {X Y X' Y' : SepFinType k}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (pmap : X' ⟶ X) (g : Y' ⟶ Y)
    (sq : IsPullback pmap.hom.left f'.hom.left f.hom.left g.hom.left)
    [AlgebraicGeometry.IsFinite g.hom.left]
    (c : Compactification f.hom.left) :
    R((pmap.hom.left)_*[ModuleCat.{u + 1} A]) ⋙
        D((c.i)_!open[ModuleCat.{u + 1} A]) ⟶
      D(((c.ofIsPullback sq).i)_!open[ModuleCat.{u + 1} A]) ⋙
        R((pullback.fst c.g g.hom.left)_*[ModuleCat.{u + 1} A]) := by
  let α := TwoSquare.mk _ _ _ _
    ((leftDerivedOpenImmersionLowerShriekBaseChangeIso
      (ModuleCat.{u + 1} A) (c.isPullback_i_ofIsPullback sq)).inv)
  exact (mateEquiv
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) pmap.hom.left)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
      (pullback.fst c.g g.hom.left)) α).natTrans

/-- The canonical finite-horizontal compact-support composition comparison. It is formula (C):
first apply the specified open/proper interchange, then compose the two proper direct images
using `rightDerivedLowerStarComp`; no exchange map is used to define it.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-trace-formula/
sec-frobenius-and-rf/sk-i-relative-frob/sk-i-relative-frob.proof.md,
item (3), formula (C); Stacks Tag 0F7J (lemma-shriek-composition), proper-input case.
(blueprint: lem-trf-finite-horizontal-shriek-mate-general) -/
noncomputable def finiteHorizontalShriekCompositionMap
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (k : Type u) [Field k] [IsAlgClosed k]
    {X Y X' Y' : SepFinType k}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (pmap : X' ⟶ X) (g : Y' ⟶ Y)
    (sq : IsPullback pmap.hom.left f'.hom.left f.hom.left g.hom.left)
    [AlgebraicGeometry.IsFinite g.hom.left]
    (c : Compactification f.hom.left) :
    R((pmap.hom.left)_*[ModuleCat.{u + 1} A]) ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⟶
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) (c.ofIsPullback sq) ⋙
        R((g.hom.left)_*[ModuleCat.{u + 1} A]) := by
  let γ := finiteHorizontalOpenProperGamma A k f f' pmap g sq c
  let γb := Functor.whiskerRight γ R((c.g)_*[ModuleCat.{u + 1} A])
  let hcomp := rightDerivedLowerStarComp (ModuleCat.{u + 1} A)
    (pullback.fst c.g g.hom.left) c.g
  let hcomp' := rightDerivedLowerStarComp (ModuleCat.{u + 1} A)
    (c.ofIsPullback sq).g g.hom.left
  exact
    (Functor.associator _ _ _).hom ≫ γb ≫
      Functor.whiskerLeft D(((c.ofIsPullback sq).i)_!open[ModuleCat.{u + 1} A])
        (hcomp.hom ≫
          (eqToIso (congrArg (fun h ↦ R((h)_*[ModuleCat.{u + 1} A]))
            (pullback.condition :
              pullback.fst c.g g.hom.left ≫ c.g =
                pullback.snd c.g g.hom.left ≫ g.hom.left))).hom ≫ hcomp'.inv) ≫
      (Functor.associator _ _ _).inv

/-- The open/proper comparison and the direct-image compositor in formula (C) are the
normalized compact-support composition isomorphism.  Its invertibility is the finite-level
compact-support composition assertion of `sk-thm-sf-comp-composition`; the proof is postponed.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-trace-formula/
sec-frobenius-and-rf/sk-i-relative-frob/sk-i-relative-frob.proof.md,
item (3), formula (C); Stacks Tags 0F7J and 0F7L.
(blueprint: lem-trf-finite-horizontal-shriek-mate-general) -/
theorem finiteHorizontalShriekCompositionMap_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (k : Type u) [Field k] [IsAlgClosed k]
    {X Y X' Y' : SepFinType k}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (pmap : X' ⟶ X) (g : Y' ⟶ Y)
    (sq : IsPullback pmap.hom.left f'.hom.left f.hom.left g.hom.left)
    [AlgebraicGeometry.IsFinite g.hom.left]
    (c : Compactification f.hom.left) :
    IsIso (finiteHorizontalShriekCompositionMap A k f f' pmap g sq c) := by
  sorry

/-- The canonical finite-horizontal compact-support composition isomorphism.  Its hom is the
open/proper interchange followed by the canonical direct-image compositor of formula (C), and
is defined independently of the compact-support exchange map.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-trace-formula/
sec-frobenius-and-rf/sk-i-relative-frob/sk-i-relative-frob.proof.md,
item (3), formula (C); Stacks Tag 0F7J.
(blueprint: lem-trf-finite-horizontal-shriek-mate-general) -/
noncomputable def finiteHorizontalShriekComposition
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (k : Type u) [Field k] [IsAlgClosed k]
    {X Y X' Y' : SepFinType k}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (pmap : X' ⟶ X) (g : Y' ⟶ Y)
    (sq : IsPullback pmap.hom.left f'.hom.left f.hom.left g.hom.left)
    [AlgebraicGeometry.IsFinite g.hom.left]
    (c : Compactification f.hom.left) :
    R((pmap.hom.left)_*[ModuleCat.{u + 1} A]) ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) (c.ofIsPullback sq) ⋙
        R((g.hom.left)_*[ModuleCat.{u + 1} A]) := by
  letI := finiteHorizontalShriekCompositionMap_isIso A k f f' pmap g sq c
  exact asIso (finiteHorizontalShriekCompositionMap A k f f' pmap g sq c)

/-- **Finite-horizontal compact-support exchange preserves ordinary units.** For a Cartesian
square of separated finite-type `k`-schemes with finite `g`, a compactification `c` of `f` and
`K ∈ Dctf(X, A)`, `Rg_*(Ex_!(K)) ∘ η_g = χ_{p^*K} ∘ Rf_!(η_p)`, with `χ` the canonical
compact-support composition comparison of formula (C).
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-trace-formula/
sec-frobenius-and-rf/sk-i-relative-frob/sk-i-relative-frob.proof.md,
proof of (3), "Since base change is compatible with these units"; Stacks Tags 0F7L
(lemma-base-change-shriek) and 0F7J.
(blueprint: lem-trf-finite-horizontal-shriek-mate-general)

Proof (steps of the node):
1. Write `c = (j, b)`, `c' = (j', b')`, `q : Z' ⟶ Z`; the open square `(j, j', q, p)` and the
   proper square `(b, b', g, q)` are Cartesian; `p`, `q` are finite, hence proper; all schemes
   are Noetherian and all arrows qcqs.
2. On `D⁺` of the étale site, `γ : j_! Rp_* ≅ Rq_* j'_!` is the normalized proper/open map of
   Stacks 0F7B (identity of the two proper-support subsheaves).
3. Finite direct image is exact (also on constant-`A` modules), so `γ` is computed termwise.
4. With `β : q^* j_! ≅ j'_! p^*`, sectionwise: `Rq_*(β_F) ∘ η_q = γ_{p^*F} ∘ j_!(η_p)` (O).
5. For the proper square, `E = ε_g ∘ g^*σ ∘ g^*Rb_*(η_q)` by mate pasting, hence
   `Rg_*(E_M) ∘ η_g = σ_{q^*M} ∘ Rb_*(η_q)` (P), `σ` the direct-image compositor.
6. `Ex_!^c = Rb'_*(β) ∘ E j_!` and `χ_N = σ_{j'_!N} ∘ Rb_*(γ_N)` (C), by the proper-input
   composition with identity-open compactifications of `p`, `g`.
7. Apply (P) at `M = j_! K`, naturality of `σ` at `β_K`, then (O) and (C): the identity holds on
   finite étale coefficients.
8. Choose étale origin `a : C_X L ≅ K` (finite `A` is Noetherian; finite-Tor comparison); the
   mate-unit identity transports the units `η_p`, `η_g` to the pro-étale units.
9. The open-site exchange and proper/open coefficient-mate lemmas, and transport-identifies-
   exchange, carry the étale `Ex_!` to the pro-étale `Ex_!^c`.
10. Finite-ring compact-support site coherence and tower pasting carry `χ^e` to `χ^p`, with
    identity-open normalization `e_1 = 1`.
11. Apply `C_Y` to the equality of Step 7; cancel the comparisons; conjugate along `a`.
12. Equivalently, `Ex_!` is the inverse square mate of `χ` (adjunction bijection). -/
theorem finiteHorizontalShriekMateGeneral
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime]
    (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
    (hℓp : ell ≠ p)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, ∀ a : A, (ell ^ n) • a = 0)
    {X Y X' Y' : SepFinType k}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (pmap : X' ⟶ X) (g : Y' ⟶ Y)
    (sq : IsPullback pmap.hom.left f'.hom.left f.hom.left g.hom.left)
    [AlgebraicGeometry.IsFinite g.hom.left]
    (c : Compactification f.hom.left)
    (K : Dctf(X.obj.left, ModuleCat.{u + 1} A)) :
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g.hom.left).unit.app
        ((rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} A) c).obj K.obj)) ≫
      R((g.hom.left)_*[ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerShriekOfCompactificationBaseChangeMap
          (ModuleCat.{u + 1} A) sq c).app K.obj) =
      (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) c).map
        ((derivedUpperStarLowerStarAdjunction
          (ModuleCat.{u + 1} A) pmap.hom.left).unit.app K.obj) ≫
      (finiteHorizontalShriekComposition A k f f' pmap g sq c).hom.app
        (L((pmap.hom.left)^*[ModuleCat.{u + 1} A]).obj K.obj) := by
  sorry

end AlgebraicGeometry.ProEtale
