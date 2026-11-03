/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreier
public import WeilConjectures.AlgebraicGeometry.AffineCharacterTrace.AffineCharacterTrace

/-! # Nonzero linear character vanishing before coefficient sections

This is the nonconstant-character calculation of lem-fd-character-integral,
in the ordinary derived category of pulled-back condensed E-modules.
(blueprint: lem-wft-current-linear-character-vanishing).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CurrentLinearCharacter
open CondensedRing

/-- Compact direct image of a nontrivial linear character sheaf is zero.
Only positive ranks occur here; no trace or root-zero assertion is included.

Source: literature/blueprint/latest/blueprint/sec-fourier-transform/
sk-lem-wft-character-integral/lem-fd-character-integral.proof.md,
"A nontrivial character on the line", "All nonzero linear forms on the line",
"Higher dimension", and the arbitrary-base convention in lem-fd-character-integral.md.
(blueprint: lem-wft-current-linear-character-vanishing).

Proof in words: over the algebraic closure of the finite ground field, the
prime Artin--Schreier covering is finite etale. Its compact direct image is the
compact direct image of the constant module on the covering affine line.
Deck translations preserve the vector-bundle trace by smooth-trace transitivity,
so act as identity on this complex. The nontrivial character summand is the
image of its averaging projector. Character orthogonality makes the induced
projector zero, hence its image has zero compact direct image. The comparison
of degree-q and prime-cover character sheaves writes a nontrivial character as
Psi composed with Tr(a times -), with a nonzero. Scaling over the algebraic
closure of k gives vanishing of the standard coordinate line character there.
On the splitting cover the character image is the free rank-one module:
evaluation at a chosen root is inverted by the character-valued function.
Thus its degree-zero complex is bounded constructible with finite Tor amplitude;
the regular modules have the same properties. Use native compact-support
Kunneth over this algebraic closure to obtain vanishing of the exterior product
with the regular module on the remaining
coordinates. Thus the standard first-coordinate character vanishes in every
positive rank. Compact-support base change carries this calculation to any
algebraically closed Omega; no finite-type condition on the extension is needed.
Only then choose Omega-linear coordinates whose first coordinate is the given
nonzero linear form. Its inverse solves for a coordinate with nonzero coefficient.
Transport through this coordinate isomorphism and the canonical compactification
comparisons gives
the literal compactPush below. All modules and comparisons use condensed E;
no torsion coefficient system or unspecified trace datum is substituted. -/
theorem compactPush_isZero
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hpell : p ≠ ell)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (hroots : ∀ z : rootsOfUnity p (PadicAlgCl ell),
      ((z : (PadicAlgCl ell)ˣ) : PadicAlgCl ell) ∈ E.1)
    (k Ω : Type u) [Field k] [Fintype k] [CharP k p]
    [Algebra (ZMod p) k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
    (psi : AddChar k (MonObj.Γ (Profinite.continuousMapRingObj E))) (hpsi : psi ≠ 1)
    (r : ℕ) (a : Fin (r + 1) → Ω) (ha : a ≠ 0) :
    letI : (affineTraceTower (Spec (.of Ω)) (r + 1)).Over (Spec (.of k)) :=
      ⟨affineTraceProjection (Spec (.of Ω)) (r + 1) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k Ω))⟩
    IsZero ((AffineCharacterTrace.compactPush (Profinite.continuousMapRingObj E)
      (AffineCharacterTrace.baseCompactification (AffineCharacterTrace.baseMap k Ω)
        (r + 1))).obj
      ((DerivedCategory.singleFunctor _ 0).obj
        (condensedArtinSchreierSheafOf (Profinite.continuousMapRingObj E) k _ psi
          (∑ i : Fin (r + 1), (affineTraceProjection (Spec (.of Ω)) (r + 1)).appTop
            ((Scheme.ΓSpecIso (.of Ω)).inv.hom (a i)) *
              affineTraceCoordinate (Spec (.of Ω)) (r + 1) i)))) := by
  sorry

end AlgebraicGeometry.ProEtale.CurrentLinearCharacter
