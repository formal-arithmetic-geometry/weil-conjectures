/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeDifferentialsPullbackMap
public import WeilConjectures.AlgebraicGeometry.TensorPullbackSectionAdjunction

/-!
# Source-open comparison for differential transitivity

Source: Stacks Project, Morphisms, Tags 01US (`lemma-differentials-restrict-open`)
and 01UV (`lemma-functoriality-differentials`)
(blueprint: lem-a1-differential-transitivity-open).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Hom

/-- Restriction of the differential transitivity arrows to every source open, normalized
on actual pulled-back differential sections.
Source: Stacks Project, Morphisms, Tags 01US and 01UV
(blueprint: lem-a1-differential-transitivity-open).

Proof:
1. For the open inclusion j, compose the restriction adjunction with the normalized
   tensor-pullback adjunction for h, and compare it with the normalized adjunction for
   j ≫ h using the canonical pushforward composition isomorphism. Uniqueness of left
   adjoints gives e. Its unit identity sends each restricted tensor-unit section to the
   tensor-unit section for j ≫ h, so in particular it gives the displayed formula on db.
2. Regard the universal derivation relative to j ≫ h as relative to j ≫ (h ≫ g).
   The differential universal property constructs qO, with qO(da) = da. Apply the
   restriction adjunction and the differential universal Hom equivalence to the second
   square. On da, both routes give d(j-sharp(a)), using hq and the formula for qO.
   For the first square, apply the tensor and restriction adjunctions, followed by the
   universal Hom equivalence for the differentials on Y. The left-adjoint uniqueness
   identity changes the route through e into the tensor adjunction for j ≫ h. On db,
   both routes give d(j-sharp(h-sharp(b))), by the tensor-unit formula, the defining
   formula of the canonical first arrow, and the source-restriction derivation formula.
   Equality induction shows that the associativity congruence preserves differentials.
   Injectivity of these Hom equivalences proves both sheaf morphism equalities, also
   for empty opens. This uses def-pc-module-pullback, def-sc-relative-differential-sheaf,
   and def-a1-relative-differentials-pullback-map; it does not use exactness. -/
theorem relativeDifferentials_transitivity_open
    {X Y S : Scheme.{u}} (h : X ⟶ Y) (g : Y ⟶ S)
    (q : (h ≫ g).relativeDifferentials ⟶ h.relativeDifferentials)
    (hq : ∀ (O : X.Opens) (a : Γ(X, O)),
      q.app O ((h ≫ g).relativeDifferentialsDerivation.d (X := op O) a) =
        h.relativeDifferentialsDerivation.d (X := op O) a) :
      (∀ O : X.Opens,
        ∃ (e : ((Modules.tensorPullback h).obj g.relativeDifferentials).restrict O.ι ≅
              (Modules.tensorPullback (O.ι ≫ h)).obj g.relativeDifferentials)
          (qO : (O.ι ≫ (h ≫ g)).relativeDifferentials ⟶ (O.ι ≫ h).relativeDifferentials),
          (∀ (V : Y.Opens) (b : Γ(Y, V)),
            e.hom.app (O.ι ⁻¹ᵁ (h ⁻¹ᵁ V))
              (((Modules.tensorPullback h).obj g.relativeDifferentials).presheaf.map
                (homOfLE (O.ι.image_preimage_le (h ⁻¹ᵁ V))).op
                  (g.relativeDifferentialsPullbackGenerator h V b)) =
              g.relativeDifferentialsPullbackGenerator (O.ι ≫ h) V b) ∧
          (Modules.restrictFunctor O.ι).map (g.relativeDifferentialsPullbackMap h) ≫
              ((h ≫ g).relativeDifferentialsRestrictIso O.ι).hom =
            e.hom ≫ g.relativeDifferentialsPullbackMap (O.ι ≫ h) ≫
              (relativeDifferentialsCongr _ (Category.assoc O.ι h g)).hom ∧
          (Modules.restrictFunctor O.ι).map q ≫
              (h.relativeDifferentialsRestrictIso O.ι).hom =
            ((h ≫ g).relativeDifferentialsRestrictIso O.ι).hom ≫ qO ∧
          (∀ (T : O.toScheme.Opens) (a : Γ(O.toScheme, T)),
            qO.app T ((O.ι ≫ (h ≫ g)).relativeDifferentialsDerivation.d (X := op T) a) =
              (O.ι ≫ h).relativeDifferentialsDerivation.d (X := op T) a)) := by
  sorry

end AlgebraicGeometry.Scheme.Hom
