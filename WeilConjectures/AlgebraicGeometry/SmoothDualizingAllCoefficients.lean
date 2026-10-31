/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.TransportUnits
public import WeilConjectures.AlgebraicGeometry.LocalizingExceptionalAdjoint
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.InternalSignedTateTwist

/-! # The smooth dualizing complex for every admissible coefficient

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-cor-sp-all-coefficients/_section.md and its proof
(blueprint: sk-cor-sp-all-coefficients).

The exceptional inverse image is the restriction of a specified right adjoint on
Loc(Dctf). Coefficient rings, positive Tate lines, and the full Dctf subcategory
are the existing condensed module-object constructions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.PurityTransport

/-- The exceptional inverse image of the coefficient unit under a smooth structure
morphism of pure dimension `d` is the native Tate line shifted by `2d`, inside
Dctf. The compactification and its localizing right adjoint are specified, rather
than replaced by an arbitrary functor on the ambient derived category. The output
membership certificates introduce no additional hypotheses.

Source: latest blueprint, sk-cor-sp-all-coefficients, entire statement
(blueprint: sk-cor-sp-all-coefficients).

Proof in words. Apply sk-thm-purity-transport to the structure morphism and the
coefficient unit. The unit has the rank-one finite constant scalar model and Tor
amplitude [0,0], hence is in Dctf. The purity theorem restricts the specified
localizing right adjoint to Dctf and gives its canonical natural comparison with
twisted, shifted pullback. Evaluate this comparison at the unit. By clause (1) of
sk-prop-sfb-cartesian-coefficients the coefficient pullback is exact and its
canonical coefficient comparison identifies the pulled-back unit with the unit
on X. Tensoring by the native Tate line and shifting identifies the source with
Lambda_X(d)[2d]; this is also the existing sourceUnit isomorphism. The source
preservation assertion of purity proves that this shifted line lies in Dctf.
Invert the composite to obtain the displayed orientation. Since Dctf is full,
the ambient comparison and its inverse define the asserted isomorphism in Dctf.
Its naturality is inherited from the natural purity comparison and the canonical
pullback-unit and tensor-unit isomorphisms. This applies to every admissible
coefficient, including nonregular finite rings and the zero ring. -/
theorem smooth_dualizing_all_coefficients
    (ell : ℕ) [Fact ell.Prime] (D : WeilConjectures.FiniteFieldDatum.{u})
    (_hEll : ell ≠ D.p) (c : Coefficient ell)
    (X : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (cf : Compactification X.hom)
    (hL : ∀ K, localizing ell c X.left K → localizing ell c (Spec (.of D.k))
      ((rightDerivedLowerShriekOfCompactification (c.obj ell) cf).obj K))
    (G : (localizing ell c (Spec (.of D.k))).FullSubcategory ⥤
      (localizing ell c X.left).FullSubcategory)
    (_b : localizingLowerShriek (c.obj ell) cf hL ⊣ G) :
    ∃ hU : property ell c (Spec (.of D.k)) (unit ell c (Spec (.of D.k))),
    ∃ hG : ∀ K : c.ctf ell (Spec (.of D.k)),
      property ell c X.left (G.obj ((inclusion ell c (Spec (.of D.k))).obj K)).obj,
    ∃ hT : property ell c X.left (c.derivedLine ell X.left d),
      Nonempty ((exceptional ell c G hG).obj ⟨unit ell c (Spec (.of D.k)), hU⟩ ≅
        (⟨c.derivedLine ell X.left d, hT⟩ : c.ctf ell X.left)) := by
  sorry

end AlgebraicGeometry.ProEtale.PurityTransport
