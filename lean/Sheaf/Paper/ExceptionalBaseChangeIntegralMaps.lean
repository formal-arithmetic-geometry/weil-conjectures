module

public import Sheaf.Paper.ExceptionalBaseChangeIntegralComparisons
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Exceptional base change for strict towers and integral coefficients

Source: latest blueprint, sk-prop-sp-purity-bc-tower, clauses (1)--(3)
(blueprint: def-sp-exceptional-bc-integral-maps).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme WeilConjectures Opposite
namespace AlgebraicGeometry.ProEtale.SpExceptionalBaseChange
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)
variable {X' X Y' Y : Scheme.{u}} {u' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {v : Y' ⟶ Y} {sq : IsPullback u' f' f v} {c : Compactification f}
  (a : SpTowerMate.Data l E b o q sq c)

section Integral
variable [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  [∀ x : X', Invertible (l : X'.residueField x)]
  [∀ y : Y', Invertible (l : Y'.residueField y)]
  (s : IntegralData l E b o q a)

/-- The source whole-tower identification, using completed-pullback reconstruction.
Source: clause (3), a_K (blueprint: def-sp-exceptional-bc-integral-maps). -/
@[irreducible] def source (K : sfIntegralConstructibleCategory l E Y) :
    (red l E b q s.rX').obj
        ((constructibleIntegralPullback l E u').obj (s.right.obj K)) ≅
      (SpTowerMate.U l E b o q a).obj (a.right.obj ((red l E b q s.rY).obj K)) :=
  s.pullComparison.app (s.right.obj K) ≪≫
    (SpTowerMate.U l E b o q a).mapIso (s.exceptionalComparison.app K)

/-- The target whole-tower identification, using completed-pullback reconstruction.
Source: clause (3), b_K (blueprint: def-sp-exceptional-bc-integral-maps). -/
@[irreducible] def target (K : sfIntegralConstructibleCategory l E Y) :
    (red l E b q s.rX').obj
        (s.right'.obj ((constructibleIntegralPullback l E v).obj K)) ≅
      a.right'.obj ((SpTowerMate.V l E b o q a).obj ((red l E b q s.rY).obj K)) :=
  s.exceptionalComparison'.app ((constructibleIntegralPullback l E v).obj K) ≪≫
    a.right'.mapIso (s.pullComparison'.app K)

/-- The reduction of integral compact-support exchange. All factors are the specified
compact-support and completed-pullback comparisons and the actual tower exchange.
Source: clause (3), coefficient transport of beta
(blueprint: def-sp-exceptional-bc-integral-maps). -/
@[irreducible] def exchangeReduction (x : SpTowerShriek.OpenExchange l E b o)
    (M : sfIntegralConstructibleCategory l E X) :
    (red l E b q s.rY').obj ((constructibleIntegralPullback l E v).obj
        ((SpIntegralAdjunction.support l E c s.support_closed).obj M)) ⟶
      (red l E b q s.rY').obj
        ((SpIntegralAdjunction.support l E (c.ofIsPullback sq) s.support_closed').obj
          ((constructibleIntegralPullback l E u').obj M)) :=
  s.pullComparison'.hom.app ((SpIntegralAdjunction.support l E c s.support_closed).obj M) ≫
    (SpTowerMate.V l E b o q a).map (s.supportComparison.hom.app M) ≫
    (SpTowerMate.beta l E b o q a x).app ((red l E b q s.rX).obj M) ≫
    (SpTowerGluing.support l E b o q (c.ofIsPullback sq) a.support_closed').map
      (s.pullComparison.inv.app M) ≫
    s.supportComparison'.inv.app ((constructibleIntegralPullback l E u').obj M)

/-- Reconstruct the actual tower mate by the inverse on Hom sets of reduction.
Source: clause (3), iota_D inverse, L(b inverse e a), iota_C
(blueprint: def-sp-exceptional-bc-integral-maps). -/
@[irreducible] def reconstructed (x : SpTowerShriek.OpenExchange l E b o)
    (hb : IsIso (SpTowerMate.beta l E b o q a x))
    (K : sfIntegralConstructibleCategory l E Y) :
    (constructibleIntegralPullback l E u').obj (s.right.obj K) ⟶
      s.right'.obj ((constructibleIntegralPullback l E v).obj K) :=
  s.rX'.fullyFaithful.preimage
    ((source l E b o q a s K).hom ≫
      (SpTowerMate.mate l E b o q a x hb).app ((red l E b q s.rY).obj K) ≫
      (target l E b o q a s K).inv)

/-- The integral counit transpose for the specified compact-support exchange.
Source: clause (3), displayed transpose (blueprint: def-sp-exceptional-bc-integral-maps). -/
@[irreducible] def integralTranspose
    (beta : SpIntegralAdjunction.support l E c s.support_closed ⋙
        constructibleIntegralPullback l E v ≅
      constructibleIntegralPullback l E u' ⋙
        SpIntegralAdjunction.support l E (c.ofIsPullback sq) s.support_closed')
    (K : sfIntegralConstructibleCategory l E Y) :
    (constructibleIntegralPullback l E u').obj (s.right.obj K) ⟶
      s.right'.obj ((constructibleIntegralPullback l E v).obj K) :=
  s.adjunction'.homEquiv _ _ (beta.inv.app (s.right.obj K) ≫
    (constructibleIntegralPullback l E v).map (s.adjunction.counit.app K))


end Integral


end AlgebraicGeometry.ProEtale.SpExceptionalBaseChange
