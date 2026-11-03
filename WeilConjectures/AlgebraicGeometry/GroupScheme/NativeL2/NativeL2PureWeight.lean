/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.CondensedL2Norm
public import WeilConjectures.AlgebraicGeometry.AffineSpace.GeometricallyConnected

/-! Native L² purity rigidity.
Source: latest blueprint, lem-wf-l2-purity-rigidity.
(blueprint: lem-fd-native-l2-pure-weight).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.NativeL2

/-- A nonzero pure lisse native Weil module on a dense affine open has L² weight w.

Source: latest blueprint, lem-fd-l2-middle-extension.proof.md, opening paragraph,
applying lem-wf-l2-purity-rigidity (blueprint: lem-fd-native-l2-pure-weight).

Proof: the dense open of A¹ is a smooth, separated, geometrically connected affine curve.
For affineness, every open of Spec k₀[t] is basic since k₀[t] is a principal ideal ring.
Place M and its actual Frobenius isomorphism in degree zero by the single functor and
its exact-pullback comparison. Lissity gives constructibility, so this is a bounded
constructible strict Weil complex in the ordinary heart. The canonical H⁰ comparison
is Weil compatible; the other cohomology modules vanish. Exact point pullback and
sections identify its alternating local traces with the module traces, hence identify
both energies. Apply native degree-zero purity rigidity to this complex: normalize by
a constant twist B_b with |iota b|=q^(-w/2), choosing b as a root of the inverse of a
nonzero closed-point Frobenius eigenvalue. The twist is pure of weight zero and its
energy parameter is the original parameter minus w. Its real envelope is nonzero,
lisse, real and pure of weight zero, so the real Euler-product dictionary gives
parameter zero. Its trace is twice the real part of the twist's trace, giving energy
at most four times the twist's energy and therefore a lower bound zero for the twist.
The pure upper bound gives the reverse inequality. Thus the twist has parameter zero;
translate by w to recover parameter w. The logarithmic/supremum dictionary and the
single-complex trace identification give exactly the module parameter asserted here.
Nonvanishing excludes the empty-parameter value; finite translation handles both
extended-real endpoints without cancellation at infinity. -/
theorem l2Weight_eq_of_pure
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (iota : PadicAlgCl l →+* ℂ)
    (U₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    (j₀ : U₀ ⟶ Over.mk (affineLine D.k₀ ↘ Spec (.of D.k₀)))
    [IsOpenImmersion j₀.left] [IsDominant j₀.left]
    (M : WeilModule D l U₀)
    (_hlisse : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier)
    (_hne : ¬ IsZero M) (w : ℝ) (_hpure : Pure D l U₀ M iota w) :
    l2Weight D l U₀ iota M = (w : EReal) := by
  sorry

end WeilConjectures.NativeL2
