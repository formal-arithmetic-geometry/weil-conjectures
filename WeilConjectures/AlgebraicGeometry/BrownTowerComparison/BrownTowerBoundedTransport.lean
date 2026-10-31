/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BrownTowerComparison.Site.BrownTowerSite

/-! # Bounded site transport of the Brown adjunction

Source: Zheng Lemmas 4.10 and 5.22 and the integral-adjunction Hom display
(blueprint: def-pur-brown-bounded-transport).

This interface specifies the actual maps and their normalizations, without existence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genCtorIdx false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
namespace BrownTowerComparison
variable {O : Type (u + 1)} [CommRing O] {t : O}
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}

/-- Bounded site transport with the actual counit and natural Brown Hom bijection.
Source: Zheng Lemmas 4.10 and 5.22; node proof Steps 7--12
(blueprint: def-pur-brown-bounded-transport). -/
structure TransportData (S : StrictEtaleCompactSupport O t c)
    (G : EtaleTowerBrownAdjunction S) (H : FiniteEvaluation S G) where
  [finite : ∀ n : ℕ, Finite (Ring O t n)]
  siteX : Site X O t S.PX
  siteY : Site Y O t S.PY
  compact : ProCompact S siteX siteY
  compactComparison : S.functor ⋙ siteY.inverse ⟶ siteX.inverse ⋙ compact.functor
  compactEvaluation : ∀ n,
    compact.functor ⋙ siteY.proEvaluation.evaluation n ⋙ (siteY.realization n).derived ≅
    siteX.proEvaluation.evaluation n ⋙ (siteX.realization n).derived ⋙
      FiniteCoefficientAdjoints.lower (Ring O t n) c
  evaluation : ∀ n,
    siteY.direct ⋙ G.right ⋙ siteX.inverse ⋙ siteX.proEvaluation.evaluation n ≅
    siteY.proEvaluation.evaluation n ⋙ finiteExceptional S G H siteX siteY n
  counit : ∀ (C : DerivedCategory (ProSystem Y O t)), siteY.Origin C →
    IsNormalizedCoefficientSystem.{u + 1, u, u + 1, u + 2}
      (J := Scheme.ProEt.topology Y) O t siteY.proEvaluation C →
    (∀ n, FiniteCoefficientAdjoints.ctf (Ring O t n) Y
      ((siteY.realization n).derived.obj ((siteY.proEvaluation.evaluation n).obj C))) →
    (∃ a : ℤ, ∀ n, ((finiteExceptional S G H siteX siteY n).obj
      ((siteY.proEvaluation.evaluation n).obj C)).IsGE a) →
    (compact.functor.obj (siteX.inverse.obj
      (G.right.obj (siteY.direct.obj C))) ⟶ C)
  hom : ∀ C (_hC : siteY.Origin C)
    (_hn : IsNormalizedCoefficientSystem.{u + 1, u, u + 1, u + 2}
      (J := Scheme.ProEt.topology Y) O t siteY.proEvaluation C)
    (_hc : ∀ n, FiniteCoefficientAdjoints.ctf (Ring O t n) Y
      ((siteY.realization n).derived.obj ((siteY.proEvaluation.evaluation n).obj C)))
    (_hb : ∃ a : ℤ, ∀ n, ((finiteExceptional S G H siteX siteY n).obj
      ((siteY.proEvaluation.evaluation n).obj C)).IsGE a)
    B (_hB : siteX.Origin B),
    (B ⟶ siteX.inverse.obj (G.right.obj (siteY.direct.obj C))) ≃ (compact.functor.obj B ⟶ C)

/-- The canonical equations and boundedness properties of transport data.
Source: Zheng Lemmas 4.10 and 5.22; node proof Steps 7--12
(blueprint: def-pur-brown-bounded-transport). -/
structure Transport (S : StrictEtaleCompactSupport O t c)
    (G : EtaleTowerBrownAdjunction S) (H : FiniteEvaluation S G)
    (D : TransportData S G H) [finite : ∀ n : ℕ, Finite (Ring O t n)] : Prop where
  realizationX : ∀ n, D.siteX.etaleRealization n = H.realizationX n
  realizationY : ∀ n, D.siteY.etaleRealization n = H.realizationY n
  compactComparison_evaluation : ∀ n K
      (hK : DerivedCategory.TStructure.t.plus
        ((H.realizationX n).derived.obj ((S.PX.evaluation n).obj K))),
    (D.siteY.realization n).derived.map
      ((D.siteY.proEvaluation.evaluation n).map (D.compactComparison.app K)) ≫
      (D.compactEvaluation n).hom.app (D.siteX.inverse.obj K) ≫
      (FiniteCoefficientAdjoints.lower (Ring O t n) c).map
        ((D.siteX.realization n).derived.map
          ((D.siteX.comparison.evaluation.inverseEvaluation n).hom.app K) ≫
          (D.siteX.inverseLevel n).hom.app ((S.PX.evaluation n).obj K)) =
    (D.siteY.realization n).derived.map
      ((D.siteY.comparison.evaluation.inverseEvaluation n).hom.app (S.functor.obj K)) ≫
      (D.siteY.inverseLevel n).hom.app ((S.PY.evaluation n).obj (S.functor.obj K)) ≫
      (FiniteCoefficientAdjoints.nu (Ring O t n) Y).map
        (eqToHom (congrArg
          (fun R ↦ R.derived.obj ((S.PY.evaluation n).obj (S.functor.obj K)))
          (realizationY n)) ≫
        (H.realizationY n).derived.map ((S.evaluation n).hom.app K) ≫
          (H.lower n).hom.app ((S.PX.evaluation n).obj K)) ≫
      (ProEtale.compactSupportSiteComparison (Ring O t n) c).inv.app
        ⟨(H.realizationX n).derived.obj ((S.PX.evaluation n).obj K), hK⟩ ≫
      (FiniteCoefficientAdjoints.lower (Ring O t n) c).map
        ((FiniteCoefficientAdjoints.nu (Ring O t n) X).map
          (eqToHom (congrArg
            (fun R ↦ R.derived.obj ((S.PX.evaluation n).obj K))
            (realizationX n).symm)))
  compact_iso : ∀ K, (∃ a : ℤ, K.IsGE a) → IsIso (D.compactComparison.app K)
  unit_iso_X : ∀ K, (∃ a : ℤ, K.IsGE a) → IsIso (D.siteX.adjunction.unit.app K)
  unit_iso_Y : ∀ K, (∃ a : ℤ, K.IsGE a) → IsIso (D.siteY.adjunction.unit.app K)
  counit_iso_X : ∀ K, D.siteX.Origin K → IsIso (D.siteX.adjunction.counit.app K)
  counit_iso_Y : ∀ K, D.siteY.Origin K → IsIso (D.siteY.adjunction.counit.app K)
  fullyFaithful_X : ∀ K L, (∃ a : ℤ, K.IsGE a) → (∃ a : ℤ, L.IsGE a) →
    Function.Bijective (D.siteX.inverse.map : (K ⟶ L) → _)
  fullyFaithful_Y : ∀ K L, (∃ a : ℤ, K.IsGE a) → (∃ a : ℤ, L.IsGE a) →
    Function.Bijective (D.siteY.inverse.map : (K ⟶ L) → _)
  compact_bound : ∀ K a, K.IsGE a → (D.compact.functor.obj K).IsGE a
  bound : ∀ (C : DerivedCategory (ProSystem Y O t)), D.siteY.Origin C →
    IsNormalizedCoefficientSystem.{u + 1, u, u + 1, u + 2}
      (J := Scheme.ProEt.topology Y) O t D.siteY.proEvaluation C →
    (∀ n, FiniteCoefficientAdjoints.ctf (Ring O t n) Y
      ((D.siteY.realization n).derived.obj ((D.siteY.proEvaluation.evaluation n).obj C))) →
    ∀ a : ℤ,
    (∀ n, ((finiteExceptional S G H D.siteX D.siteY n).obj
      ((D.siteY.proEvaluation.evaluation n).obj C)).IsGE a) →
    (G.right.obj (D.siteY.direct.obj C)).IsGE a ∧
    (D.siteX.inverse.obj (G.right.obj (D.siteY.direct.obj C))).IsGE a ∧
    IsNormalizedCoefficientSystem.{u + 1, u, u + 1, u + 2}
      (J := Scheme.ProEt.topology X) O t D.siteX.proEvaluation
      (D.siteX.inverse.obj (G.right.obj (D.siteY.direct.obj C)))
  evaluation_def : ∀ n C,
    (D.evaluation n).hom.app C =
    (D.siteX.comparison.evaluation.inverseEvaluation n).hom.app
      (G.right.obj (D.siteY.direct.obj C)) ≫
    (D.siteX.comparison.evaluation.level n).inverse.map
      ((H.evaluation n).hom.app (D.siteY.direct.obj C)) ≫
    (D.siteX.comparison.evaluation.level n).inverse.map
      ((H.right n).map ((D.siteY.comparison.evaluation.directEvaluation n).hom.app C))
  counit_formula : ∀ C hC hn hc hb,
    D.compactComparison.app (G.right.obj (D.siteY.direct.obj C)) ≫ D.counit C hC hn hc hb =
    D.siteY.inverse.map (G.adjunction.counit.app (D.siteY.direct.obj C)) ≫
      D.siteY.adjunction.counit.app C
  hom_formula : ∀ C hC hn hc hb B hB a,
    D.hom C hC hn hc hb B hB a = D.compact.functor.map a ≫ D.counit C hC hn hc hb
  hom_brown : ∀ C hC hn hc hb B hB a b,
    D.siteX.adjunction.counit.app B ≫ a = D.siteX.inverse.map b →
    D.compactComparison.app (D.siteX.direct.obj B) ≫
      D.compact.functor.map (D.siteX.adjunction.counit.app B) ≫ D.hom C hC hn hc hb B hB a =
    D.siteY.inverse.map ((G.adjunction.homEquiv _ _).symm b) ≫ D.siteY.adjunction.counit.app C
  hom_natural_left : ∀ C hC hn hc hb B hB B' hB' (b : B' ⟶ B) a,
    D.hom C hC hn hc hb B' hB' (b ≫ a) =
      D.compact.functor.map b ≫ D.hom C hC hn hc hb B hB a
  hom_natural_right : ∀ C hC hn hc hb C' hC' hn' hc' hb' (b : C ⟶ C') B hB a,
    D.hom C' hC' hn' hc' hb' B hB
      (a ≫ D.siteX.inverse.map (G.right.map (D.siteY.direct.map b))) =
      D.hom C hC hn hc hb B hB a ≫ b
  hom_additive : ∀ C hC hn hc hb B hB a b,
    D.hom C hC hn hc hb B hB (a + b) =
      D.hom C hC hn hc hb B hB a + D.hom C hC hn hc hb B hB b
  hom_linear : ∀ C hC hn hc hb B hB a r (ar : C ⟶ C),
    D.siteY.adjunction.counit.app C ≫ ar =
      D.siteY.inverse.map ((G.scalarY.derived r).app (D.siteY.direct.obj C)) ≫
        D.siteY.adjunction.counit.app C →
    D.hom C hC hn hc hb B hB
      (a ≫ D.siteX.inverse.map ((G.scalarX.derived r).app (G.right.obj (D.siteY.direct.obj C)))) =
    D.hom C hC hn hc hb B hB a ≫ ar

end BrownTowerComparison
end AlgebraicGeometry
