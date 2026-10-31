/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrdinaryCoefficientDualizingExchange
/-! # Cartesian-apex pasting at the ordinary coefficient unit

The fixed unit changes preserve the proved monoidal-unit Cartesian-apex formula.
(blueprint: new-lem-pur-ordinary-coefficient-cartesian-apex-formula).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- Coefficient-unit Cartesian exchange respects replacement of its apex by an
isomorphism. Source: dualizing_cartesian_apex_isomorphism, coefficient-unit clause.
(blueprint: new-lem-pur-ordinary-coefficient-cartesian-apex-formula).

Proof: substitute the specified equality of the top arrow. Conjugate the raw
Cartesian-apex formula by the fixed unit comparisons. Naturality of the inverse-image
compositor moves the source unit change through it. Functoriality combines the two
unit changes at the intermediate apex; their hom/inverse pair cancels. This yields
the stated formula without any smoothness, twist or integration hypothesis. The
same cancellation works for identity isomorphisms and empty schemes. -/
theorem ordinaryCoefficientDualizingExchange_apex (P : PurityFiniteSetting.{u})
    {X Y T Q Z : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian T]
    [IsNoetherian Q] [IsNoetherian Z]
    {f : X ⟶ Y} {v : T ⟶ Y} {p : Q ⟶ X} {r : Q ⟶ T}
    [IsSeparated f] [QuasiCompact f] [HasCompactification f]
    [IsSeparated r] [QuasiCompact r] [HasCompactification r]
    (q : ChosenCartesianSquare p r f v) (e : Z ≅ Q)
    [IsSeparated (e.hom ≫ r)] [QuasiCompact (e.hom ≫ r)]
    [HasCompactification (e.hom ≫ r)]
    (j : Z ⟶ X) (hj : j = e.hom ≫ p)
    (qj : IsPullback j (e.hom ≫ r) f v) :
    P.ordinaryCoefficientDualizingExchange qj =
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
        e.hom p j hj).hom.app (P.diagonalOrdinaryDualizing f) ≫
      (Etale.ordinaryFinitePullback P.Coefficient e.hom).map
        (P.ordinaryCoefficientDualizingExchange
          (IsPullback.of_iso_pullback q.toCommSq q.isoPullback q.hom_fst q.hom_snd)) ≫
      P.ordinaryCoefficientApexComparison e r := by
  subst j
  have hraw := (Etale.dualizing_cartesian_apex_isomorphism
    P.Coefficient q e qj).2.2
  have hn := (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
    e.hom p).hom.naturality (OrientationCounit.unitChange P f).inv
  dsimp only [Functor.comp_map] at hn
  unfold ordinaryCoefficientDualizingExchange ordinaryCoefficientApexComparison
  rw [hraw]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hn]
  simp only [← Functor.map_comp_assoc]
  simp only [Iso.hom_inv_id, Category.comp_id]
  simp only [Etale.ordinaryFinitePullback]

end WeilConjectures.PurityFiniteSetting
