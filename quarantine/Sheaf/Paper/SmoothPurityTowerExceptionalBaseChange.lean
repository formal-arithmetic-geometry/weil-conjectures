module

public import Sheaf.Paper.ExceptionalBaseChangeIntegralMaps
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Exceptional base change for strict towers and integral coefficients

Source: latest blueprint, sk-prop-sp-purity-bc-tower, clauses (1)--(3)
(blueprint: det-sp-tower-exceptional-bc).
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

/-- The total-limit realization equation, in adjunction form. Cancelling its invertible
unit is precisely the displayed unit/limit/inverse-unit formula.
Source: clause (3), R lim of e (blueprint: det-sp-tower-exceptional-bc). -/
@[irreducible] def IsLimitRealization (x : SpTowerShriek.OpenExchange l E b o)
    (hb : IsIso (SpTowerMate.beta l E b o q a x))
    (K : sfIntegralConstructibleCategory l E Y) : Prop :=
  HEq ((reconstructed l E b o q a s x hb K).hom ≫
      s.rX'.normalization.adjunction.unit.app
        (s.right'.obj ((constructibleIntegralPullback l E v).obj K)).obj)
    (s.rX'.normalization.adjunction.homEquiv _ _
      (((source l E b o q a s K).hom ≫
        (SpTowerMate.mate l E b o q a x hb).app ((red l E b q s.rY).obj K) ≫
        (target l E b o q a s K).inv).hom))

/-- Exact integral realization: beta is the unique reduction transport; the inverse
limit of the tower mate is invertible and is the specified integral counit transpose.
Source: clause (3) (blueprint: det-sp-tower-exceptional-bc). -/
@[irreducible] def IntegralConclusion (x : SpTowerShriek.OpenExchange l E b o)
    (hb : IsIso (SpTowerMate.beta l E b o q a x)) : Prop :=
  ∃ beta : SpIntegralAdjunction.support l E c s.support_closed ⋙
      constructibleIntegralPullback l E v ≅
    constructibleIntegralPullback l E u' ⋙
      SpIntegralAdjunction.support l E (c.ofIsPullback sq) s.support_closed',
    (∀ M : sfIntegralConstructibleCategory l E X,
      (red l E b q s.rY').map (beta.hom.app M) = exchangeReduction l E b o q a s x M) ∧
    (∀ beta' : SpIntegralAdjunction.support l E c s.support_closed ⋙
        constructibleIntegralPullback l E v ≅
      constructibleIntegralPullback l E u' ⋙
        SpIntegralAdjunction.support l E (c.ofIsPullback sq) s.support_closed',
      (∀ M : sfIntegralConstructibleCategory l E X,
        (red l E b q s.rY').map (beta'.hom.app M) =
          exchangeReduction l E b o q a s x M) → beta' = beta) ∧
    ∀ K : sfIntegralConstructibleCategory l E Y,
      IsIso (reconstructed l E b o q a s x hb K) ∧
      IsLimitRealization l E b o q a s x hb K ∧
      HEq (reconstructed l E b o q a s x hb K)
        (integralTranspose l E b o q a s beta K)
end Integral

/-- Compact-support exchange and its exceptional counit mate are isomorphisms on
uniformly bounded constructible finite-Tor towers. The evaluations and all reductions
are the specified finite mates. Normalized inputs remain normalized. In the integral
case the reconstructed map is exactly the counit transpose of transported exchange.
Source: latest blueprint, sk-prop-sp-purity-bc-tower.md, clauses (1)--(3)
(blueprint: det-sp-tower-exceptional-bc).

Proof:
1. lem-sp-ctf-tower-pullback-reconstruction preserves the uniform ctf bounds and
normalization. Pull back c using def-cbc-compact-support-square; relative dimension
is preserved by lem-sbc-smooth-relative-dimension-permanence.
2. det-sp-tower-shriek-levels supplies the actual compactification exchange.
lem-sp-tower-mate-evaluation-reduction restricts it and gives the tower adjunctions
of det-sp-tower-gluing, together with exchange evaluation.
3. Transpose beta inverse followed by the pulled-back counit. The same evaluation
lemma identifies every level with the finite exceptional transpose. Apply
lem-pur-smb-extraordinary at the finite quotient, using ell = unit times pi^e.
Evaluation conservativity in det-sp-tower-shriek-levels makes the tower mate invertible.
4. The reduction equations in lem-sp-tower-mate-evaluation-reduction include the
input transition for each quotient. det-sp-tower-gamma(3) and pullback normalization
normalize the source; invertibility and the reduction square normalize the target.
5. For E=Ql use lem-sp-integral-exceptional-mate-transport. Integral adjoints identify
counit-preservingly with H from det-sp-integral-adjunction-bijection. The equivalence
of det-sp-normalized-equivalence transports beta uniquely. Its inverse on Hom sets
is unit, total limit of the conjugated tower map, inverse unit. This sends the
constructed tower mate to its integral transpose; it preserves inverses and proves
invertibility. These are entire-tower identities, not statements only on evaluations.
-/
theorem tower_exceptional_base_change
    (k : FiniteFieldDatum.{u}) (_hne : l ≠ k.p)
    (x : SpTowerShriek.OpenExchange l E b o)
    (X Y X' Y' : Over (Spec (CommRingCat.of k.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
    [IsSeparated Y'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
    (f : X ⟶ Y) (v : Y' ⟶ Y) (u' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback u'.left f'.left f.left v.left)
    (d : ℕ) [SmoothOfRelativeDimension d f.left] (c : Compactification f.left) :
    ∃ a : SpTowerMate.Data l E b o q sq c,
    ∃ hb : IsIso (SpTowerMate.beta l E b o q a x),
    ∃ hfinite : ∀ (n : ℕ)
      (K : spFiniteConstructibleTorCategory Y.left (SpTowerShriek.R l E n)),
      IsIso ((SpTowerMate.finiteExchange l E b (sq := sq) (c := c) n).app
        ((a.levels.right n).obj K).obj),
      SpTowerMate.Laws l E b o q a x hb hfinite ∧
      IsIso (SpTowerMate.mate l E b o q a x hb) ∧
      (∀ K : SpTowerCalculus.C l E b q Y.left,
        IsSpNormalizedTower l E Y.left (q.abelian Y.left) K.obj →
          IsSpNormalizedTower l E X'.left (q.abelian X'.left)
              (((SpTowerMate.U l E b o q a).obj (a.right.obj K)).obj) ∧
            IsSpNormalizedTower l E X'.left (q.abelian X'.left)
              ((a.right'.obj ((SpTowerMate.V l E b o q a).obj K)).obj)) ∧
      (Module.finrank (Padic l) E = 1 →
        ∀ [∀ z : X.left, Invertible (l : X.left.residueField z)]
          [∀ z : Y.left, Invertible (l : Y.left.residueField z)]
          [∀ z : X'.left, Invertible (l : X'.left.residueField z)]
          [∀ z : Y'.left, Invertible (l : Y'.left.residueField z)],
        ∃ s : IntegralData l E b o q a, IntegralConclusion l E b o q a s x hb) := by
  sorry

end AlgebraicGeometry.ProEtale.SpExceptionalBaseChange
