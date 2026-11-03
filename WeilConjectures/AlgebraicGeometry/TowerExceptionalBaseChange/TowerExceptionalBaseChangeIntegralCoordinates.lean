/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TowerExceptionalBaseChange.TowerExceptionalBaseChangeData

/-! # Integral reduction coordinates for exceptional base change

Source: latest blueprint sk-prop-sp-purity-bc-tower.proof.md, clause (3).
(blueprint: stage3-sp-tower-exceptional-integral-current).
The coordinate construction is the existing remaining geometric obligation; the
exchange, counit-transpose and total-limit identities are proved by its consumer.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.TowerExceptionalBaseChange
open IntegralDirectImageTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)
  (ex : SpTowerShriek.OpenExchange l E b o) (laws : SpTowerShriek.Laws l E b o ex)

variable {X' X Y' Y : Scheme.{u}} {u' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {v : Y' ⟶ Y} {sq : IsPullback u' f' f v} {c : Compactification f}
  (a : SpTowerMate.Data l E b o q sq c)

/-- Construct the integral reduction coordinates before transporting the exchange.
Source: proof clause (3)
(blueprint: stage3-sp-tower-exceptional-integral-current).

Proof: finite type over the field makes all four vertices Noetherian. Reduction
and total inverse limit on each vertex give normalized constructible reductions,
fully faithful reduction, and invertible completion units. The integral direct-image
comparison gives the compactification support comparison, normalized by its actual
proper/open coefficient mate. The integral adjunction bijection identifies the total
inverse limit of the tower right adjoint with the integral right adjoint; its reduction
comparison is the actual reduction/limit counit and its adjunction counit reduces to
the specified tower counit. Apply these constructions to the compactification and
its Cartesian pullback using the same coefficient geometry. Derived scalar/pullback
compatibility gives both inverse-image comparisons, with their stated normalization.
These constructions yield IntegralData. Transporting exchange and its exceptional
mate is proved separately, and is not part of this remaining obligation.
-/
theorem tower_exceptional_base_change_integral_coordinates
    (k : Type u) [Field k] (_hk : Finite k ∨ IsAlgClosed k)
    (pchar : ℕ) (_hp : 0 < pchar) [CharP k pchar] (_hne : l ≠ pchar)
    (X Y X' Y' : Over (Spec (CommRingCat.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
    [IsSeparated Y'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
    (f : X ⟶ Y) (v : Y' ⟶ Y) (u' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback u'.left f'.left f.left v.left)
    (d : ℕ) [SmoothOfRelativeDimension d f.left] (c : Compactification f.left)
    (a : SpTowerMate.Data l E b o q sq c)
    (hb : IsIso (SpTowerMate.beta l E b o q a ex))
    (hfinite : ∀ (n : ℕ)
      (K : spFiniteConstructibleTorCategory Y.left (SpTowerShriek.R l E n)),
      IsIso ((SpTowerMate.finiteExchange l E b (sq := sq) (c := c) n).app
        ((a.levels.right n).obj K).obj))
    (hlaws : SpTowerMate.Laws l E b o q a ex hb hfinite)
    (hm : IsIso (SpTowerMate.mate l E b o q a ex hb))
    (hn : ∀ K : SpTowerCalculus.C l E b q Y.left,
      IsSpNormalizedTower l E Y.left (q.abelian Y.left) K.obj →
        IsSpNormalizedTower l E X'.left (q.abelian X'.left)
            (((SpTowerMate.U l E b o q a).obj (a.right.obj K)).obj) ∧
          IsSpNormalizedTower l E X'.left (q.abelian X'.left)
            ((a.right'.obj ((SpTowerMate.V l E b o q a).obj K)).obj)) :
    Module.finrank (Padic l) E = 1 → Nonempty (IntegralData l E b o q ex laws a) := by
  sorry

end AlgebraicGeometry.ProEtale.TowerExceptionalBaseChange
