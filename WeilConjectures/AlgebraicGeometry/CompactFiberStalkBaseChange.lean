/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CompactFiberStalk
public import WeilConjectures.AlgebraicGeometry.CompactFiberStalkBaseChangeData
import WeilConjectures.AlgebraicGeometry.CompactFiberStalkBaseChangeSquare_eq
import WeilConjectures.AlgebraicGeometry.CompactFiberStalkBaseChangeIndependent_eq
import WeilConjectures.AlgebraicGeometry.CompactFiberStalkBaseChangeThreeSquares_eq

/-!
# Naturality of compact-support stalk comparisons under base change

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/
 sk-prop-an/thm-pur-rank-one-thom.proof.md`, Step 3
(blueprint: lem-pur-cfiber-stalk-base-change).

The displayed comparison is the canonical compactification exchange evaluated at a
geometric point. Its naturality is the horizontal pasting law for the finite
compact-support exchange; the chosen compactification is transported by
`Compactification.ofIsPullback`, and derived inverse-image compositors identify
iterated and direct fibre products.

The helper definitions give the fibre identification, the unbounded two-square
and three-square equations after derived sections, and the compactification
independence equation. The parent theorem is assembled from three named
coherence obligations in companion modules.
-/

@[expose] public section

set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace WeilConjectures

/-- Naturality of the finite-coefficient compact-support stalk comparison.

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/
 sk-prop-an/thm-pur-rank-one-thom.proof.md`, Step 3
(blueprint: lem-pur-cfiber-stalk-base-change).

Step 1: choose the supplied compactification `c` and its two successive base
changes. Pullback pasting gives `compactFiberStalkFibreIso`, identifying the
iterated fibre with the direct fibre at `b' ≫ g`. The comparison of
lem-pur-cfiber-stalk is precisely the proper-base-change mate followed by the
inverse open-extension comparison, and then derived sections on Spec Ω.
Every étale cover of this point splits, so these sections compute the stalk.

Step 2: use the étale-origin witness of def-weil-pbc-etale-origin-witness.
By thm-cbc-finite-level-proetale, its proper/open and inverse-image comparison
isomorphisms transport this étale compactification exchange to the pro-étale
one. The identity, composition and square compatibility of
lem-weil-pbc-comparison-pullback conjugate the étale coherence diagrams to the
pro-étale diagrams. This justifies using the permitted finite étale model here.

Step 3: apply horizontal pasting of the finite exchange from
thm-cbc-finite-torsion to the squares for `g` and `b'`, retaining the
inverse-image compositors and the compactification comparison. Apply derived
sections to obtain the first equation. Compatibility with refinements gives
the second equation, comparing arbitrary `c` and `d` on both ends. Paste a
third square for `g₂` and `b''`; associativity of inverse-image compositors
and the compactification cocycle give the last equation, with all three
exchanges displayed. These are node proof Steps 1, 2 and 3 respectively.

In Lean, the three equations are the instances at the canonical pullback squares of
`compactFiberStalkBaseChangeSquare_eq`, `compactFiberStalkBaseChangeIndependent_eq`
and `compactFiberStalkBaseChangeThreeSquares_eq`, stated for arbitrary pullback
squares in their own modules. -/
theorem compactFiberStalk_baseChange
    (P : PurityFiniteSetting.{u})
    {X Y Y' : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [Y'.Over (Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y' ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (g : Y' ⟶ Y) [g.IsOver (Spec (.of P.field.k))]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (b' : Spec (.of Ω) ⟶ Y')
    (K : DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (_hK : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} P.Coefficient) X K) :
    (letI : Finite P.Coefficient :=
      letI : Finite P.Ring :=
        Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level
          P.level_pos
      inferInstanceAs (Finite (ULift.{u + 1} P.Ring))
     (∀ c : Compactification f,
       compactFiberStalkBaseChangeSquare P.Coefficient
         (IsPullback.of_hasPullback f g)
         (IsPullback.of_hasPullback (pullback.snd f g) b')
         (IsPullback.of_iso_pullback
           ((IsPullback.of_hasPullback (pullback.snd f g) b').paste_horiz
             (IsPullback.of_hasPullback f g)).toCommSq
           (compactFiberStalkFibreIso f g b')
           ((IsPullback.of_hasPullback (pullback.snd f g) b').paste_horiz
             (IsPullback.of_hasPullback f g)).isoPullback_hom_fst
           ((IsPullback.of_hasPullback (pullback.snd f g) b').paste_horiz
             (IsPullback.of_hasPullback f g)).isoPullback_hom_snd) c K) ∧
       (∀ c d : Compactification f,
         compactFiberStalkBaseChangeIndependent P.Coefficient
           (IsPullback.of_hasPullback f (b' ≫ g)) c d K) ∧
       (∀ {Y'' : Scheme.{u}} (g₂ : Y'' ⟶ Y') (b'' : Spec (.of Ω) ⟶ Y'')
          (c : Compactification f),
         compactFiberStalkBaseChangeThreeSquares P.Coefficient
           (IsPullback.of_hasPullback f g)
           (IsPullback.of_hasPullback (pullback.snd f g) g₂)
           (IsPullback.of_hasPullback (pullback.snd (pullback.snd f g) g₂) b'') c K)) := by
  let : Finite P.Coefficient := by
    change Finite (ULift.{u + 1} (Padic.coefficientExtensionRing
      P.coefficients.l P.extension P.level))
    exact Equiv.ulift.finite_iff.mpr
      (Padic.finite_coefficientExtensionRing _ _ _ P.level_pos)
  constructor
  · intro c
    exact compactFiberStalkBaseChangeSquare_eq P.Coefficient
      (IsPullback.of_hasPullback f g)
      (IsPullback.of_hasPullback (pullback.snd f g) b')
      (IsPullback.of_iso_pullback
        ((IsPullback.of_hasPullback (pullback.snd f g) b').paste_horiz
          (IsPullback.of_hasPullback f g)).toCommSq
        (compactFiberStalkFibreIso f g b')
        ((IsPullback.of_hasPullback (pullback.snd f g) b').paste_horiz
          (IsPullback.of_hasPullback f g)).isoPullback_hom_fst
        ((IsPullback.of_hasPullback (pullback.snd f g) b').paste_horiz
          (IsPullback.of_hasPullback f g)).isoPullback_hom_snd) c K
  constructor
  · intro c d
    exact compactFiberStalkBaseChangeIndependent_eq P.Coefficient
      (IsPullback.of_hasPullback f (b' ≫ g)) c d K
  · intro Y'' g₂ b'' c
    exact compactFiberStalkBaseChangeThreeSquares_eq P.Coefficient
      (IsPullback.of_hasPullback f g)
      (IsPullback.of_hasPullback (pullback.snd f g) g₂)
      (IsPullback.of_hasPullback (pullback.snd (pullback.snd f g) g₂) b'') c K

end WeilConjectures
