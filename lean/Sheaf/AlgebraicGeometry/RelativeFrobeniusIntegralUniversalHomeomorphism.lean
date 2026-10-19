/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.SchemeCharacteristic
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Integral

import Sheaf.AlgebraicGeometry.AbsoluteFrobeniusUniversalHomeomorphism
import Sheaf.Paper.FiniteFieldFiber
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Field.ZMod
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism

/-!
# Relative Frobenius without finiteness hypotheses

Source: Stacks Project, Varieties, Tag 0CCB, lemma-relative-frobenius, and
Definition 33.36.4 (blueprint: lem-trf-relative-frobenius-universal-homeomorphism).

The two projection equations uniquely specify the canonical relative Frobenius.
The characteristic of the source is a conclusion, rather than an extra assumption.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- Absolute Frobenius is natural because ring homomorphisms preserve powers.
Source: Stacks Project, Tag 0CC7. -/
private theorem frobenius_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0)
    (hY : (p : Γ(Y, ⊤)) = 0) :
    X.iterateFrobenius hp hX 1 ≫ f = f ≫ Y.iterateFrobenius hp hY 1 := by
  apply Scheme.Hom.ext (by ext x; rfl)
  intro U
  simp only [Scheme.Hom.comp_app]
  change f.app U ≫ (X.iterateFrobenius hp hX 1).app (f ⁻¹ᵁ U) ≫
    X.presheaf.map (𝟙 _) =
      (Y.iterateFrobenius hp hY 1).app U ≫ f.app U
  rw [X.presheaf.map_id, Category.comp_id]
  ext s
  change ((f.app U).hom s) ^ p ^ 1 = (f.app U).hom (s ^ p ^ 1)
  exact (map_pow (f.app U).hom s _).symm

/-- Specialize the finite-field absolute Frobenius theorem to the prime field.
The global section map also constructs the structure morphism for the empty scheme.
Source: Stacks Project, Tag 0CC8. -/
private theorem frobenius_universal (p : ℕ) (T : Scheme.{u})
    (hT : T.IsCharacteristic p) :
    IsUniversalHomeomorphism (T.iterateFrobenius hT.1 (hT.2 ⊤) 1) := by
  classical
  let : Fact p.Prime := ⟨hT.1⟩
  let k₀ := ULift.{u} (ZMod p)
  let D : WeilConjectures.FiniteFieldDatum.{u} :=
    { p := p
      a := 1
      q := p
      prime := hT.1
      exponent_pos := le_rfl
      cardinality_eq := (pow_one p).symm
      k₀ := k₀
      card_base := by simp [k₀, Nat.card_eq_fintype_card]
      k := AlgebraicClosure k₀ }
  let φ : k₀ →+* Γ(T, ⊤) :=
    (ZMod.castHom (ringChar.dvd (hT.2 ⊤)) Γ(T, ⊤)).comp ULift.ringEquiv.toRingHom
  let : T.Over (Spec (CommRingCat.of D.k₀)) :=
    ⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)⟩
  exact D.absoluteFrobenius_isUniversalHomeomorphism T

/-- Relative Frobenius is integral and a universal homeomorphism for every morphism to a
scheme of prime characteristic. Its existence and uniqueness are specified by the two
projection equations, with the characteristic of the source supplied as part of the result.

Source: Stacks Project, Varieties, Tag 0CCB, lemma-relative-frobenius, with the construction
of Definition 33.36.4 (blueprint: lem-trf-relative-frobenius-universal-homeomorphism).

Proof, following the node's eight steps:

1. Pull back `p = 0` on global sections along `v` and restrict to all opens of `V`.
   Thus `V` has characteristic `p`, including when empty. Absolute Frobenius commutes
   with `v` because ring homomorphisms preserve p-th powers (Tag 0CC7). The fibre-product
   universal property gives the unique map `r` with these projections (Tag 0CC9).
2. Apply `lem-pur-absolute-frobenius-universal-homeomorphism` to `X` and `V`, taking the
   finite-field datum with `a = 1`, `q = p`, prime field `k₀ = F_p`, and an algebraic
   closure of `k₀` (`def-weil-finite-field-fiber`, `def-weil-finite-field-q-elements`,
   `def-weil-algebraic-closure`). Their canonical `k₀`-scheme structures come from the
   compatible maps from `F_p` to sections, glued on affine charts
   (`def-weil-scheme-over-base`). This makes both absolute Frobenii universal
   homeomorphisms (Tag 0CC8); neither scheme is extended to the algebraic closure.
3. By `lem-weil-pbc-universal-homeomorphism-base-change`, the projection
   `h = pullback.fst v F_X`, a base change of `F_X`, is a universal homeomorphism.
   In particular, `h` and `F_V` are homeomorphisms on points.
4. By `lem-trf-closed-embedding-affine`, `F_V` is affine. Its universal-homeomorphism
   property makes it universally closed (`def-weil-proper-morphism`). Thus
   `pqf-lem-integral-univclosed` shows that `F_V` is integral (Tags 04DE, 01WM).
5. Likewise `h` is affine, hence separated by clause (3) of
   `lem-weil-pbc-affine-morphism-permanence`. Since `r ≫ h = F_V` is integral,
   `lem-weil-pbc-integral-of-comp-separated` shows that `r` is integral (Tag 035D).
6. `F_V` is universally injective. If two field-valued points have equal composites
   with `r`, composing with `h` gives equal composites with `F_V`, so they agree.
   The field-valued-point criterion in `def-weil-radicial-morphism` therefore makes
   `r` universally injective (Tag 01S4).
7. For a point `y` of the twist, choose `x` with `F_V(x) = h(y)` using surjectivity
   of `F_V`. Then `h(r(x)) = h(y)`, and injectivity of `h` gives `r(x) = y`.
   This proves surjectivity (`def-weil-surjective-morphism`), also for the empty scheme.
8. Apply `lem-pc-integral-radicial-surjective-universal-homeomorphism` to the integral,
   universally injective, surjective `r` to get the topological universal-homeomorphism
   conclusion (Tag 04DF). No finiteness, reducedness, or perfection assumption is used. -/
theorem relativeFrobenius_integral_universalHomeomorphism
    (p : ℕ) (X V : Scheme.{u}) (hX : X.IsCharacteristic p) (v : V ⟶ X) :
    ∃ hV : V.IsCharacteristic p,
      ∃ r : V ⟶ pullback v (X.iterateFrobenius hX.1 (hX.2 ⊤) 1),
        r ≫ pullback.fst v (X.iterateFrobenius hX.1 (hX.2 ⊤) 1) =
            V.iterateFrobenius hV.1 (hV.2 ⊤) 1 ∧
        r ≫ pullback.snd v (X.iterateFrobenius hX.1 (hX.2 ⊤) 1) = v ∧
        IsIntegralHom r ∧ (topologically IsHomeomorph).universally r ∧
        ∀ s : V ⟶ pullback v (X.iterateFrobenius hX.1 (hX.2 ⊤) 1),
          s ≫ pullback.fst v (X.iterateFrobenius hX.1 (hX.2 ⊤) 1) =
              V.iterateFrobenius hV.1 (hV.2 ⊤) 1 →
          s ≫ pullback.snd v (X.iterateFrobenius hX.1 (hX.2 ⊤) 1) = v → s = r := by
  have hVt : (p : Γ(V, ⊤)) = 0 := by
    rw [← map_natCast v.appTop.hom, hX.2 ⊤, map_zero]
  let hV : V.IsCharacteristic p :=
    ⟨hX.1, natCast_eq_zero_of_natCast_top_eq_zero hVt⟩
  let F := X.iterateFrobenius hX.1 (hX.2 ⊤) 1
  let G := V.iterateFrobenius hV.1 (hV.2 ⊤) 1
  let r : V ⟶ pullback v F :=
    pullback.lift G v (frobenius_naturality v hX.1 (hV.2 ⊤) (hX.2 ⊤))
  have hr₁ : r ≫ pullback.fst v F = G := pullback.lift_fst _ _ _
  have hr₂ : r ≫ pullback.snd v F = v := pullback.lift_snd _ _ _
  have : IsUniversalHomeomorphism F := frobenius_universal p X hX
  have : IsUniversalHomeomorphism G := frobenius_universal p V hV
  have : IsUniversalHomeomorphism (r ≫ pullback.fst v F) :=
    hr₁.symm ▸ ‹IsUniversalHomeomorphism G›
  have : IsUniversalHomeomorphism r :=
    IsUniversalHomeomorphism.of_comp r (pullback.fst v F)
  refine ⟨hV, r, hr₁, hr₂, inferInstance,
    @isUniversalHomeomorphism_le_universally_isHomeomorph _ _ r ‹_›, ?_⟩
  intro s hs₁ hs₂
  exact pullback.hom_ext (hs₁.trans hr₁.symm) (hs₂.trans hr₂.symm)

end AlgebraicGeometry.Scheme
