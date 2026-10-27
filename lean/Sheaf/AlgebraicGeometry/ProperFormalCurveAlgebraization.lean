module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import WeilConjectures.AlgebraicGeometry.QuotientBaseChangeIdeal
import Sheaf.AlgebraicGeometry.ExistsAmpleOfDimLEOne
import Sheaf.AlgebraicGeometry.PicardLift
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import WeilConjectures.RingTheory.Flat.FlatModulePowers
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.PowerSeries.Inverse

/-! # Algebraization of proper flat formal curves

Source: Stacks Project, spaces-more-morphisms.tex, Tag 0E7R,
`lemma-formal-algebraic-space-proper-reldim-1`, with properness explicit;
more-morphisms.tex, Tag 0D4G, for flatness.
(blueprint: lem-sfb-proper-formal-curve-algebraization).

The natural index `n` denotes the paper's positive index `n + 1`.
The auxiliary definitions are the actual quotient spectra and their canonical maps.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The base `Spec(k[[t]]/(t^(n+1)))` of the positive infinitesimal stage `n + 1`.
Source: Stacks Project, Tag 0E7R, `lemma-formal-algebraic-space-proper-reldim-1`.
(blueprint: lem-sfb-proper-formal-curve-algebraization). -/
noncomputable def formalCurveBase (k : Type u) [Field k] (n : ℕ) : Scheme.{u} :=
  Spec (.of (PowerSeries k ⧸ (Ideal.span {(PowerSeries.X : PowerSeries k)}) ^ (n + 1)))

/-- The canonical quotient closed immersion of an infinitesimal power-series base.
Source: Stacks Project, Tag 0E7R, `lemma-formal-algebraic-space-proper-reldim-1`.
(blueprint: lem-sfb-proper-formal-curve-algebraization). -/
noncomputable def formalCurveBaseι (k : Type u) [Field k] (n : ℕ) :
    formalCurveBase k n ⟶ Spec (.of (PowerSeries k)) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
    ((Ideal.span {(PowerSeries.X : PowerSeries k)}) ^ (n + 1))))

/-- The adjacent transition induced by `k[[t]]/(t^(n+2)) → k[[t]]/(t^(n+1))`.
Source: Stacks Project, Tag 0E7R, `lemma-formal-algebraic-space-proper-reldim-1`.
(blueprint: lem-sfb-proper-formal-curve-algebraization). -/
noncomputable def formalCurveBaseStep (k : Type u) [Field k] (n : ℕ) :
    formalCurveBase k n ⟶ formalCurveBase k (n + 1) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (I := Ideal.span {(PowerSeries.X : PowerSeries k)})
      (Nat.le_succ (n + 1)))))

/-- A proper flat finitely presented formal curve over `k[[t]]` is algebraizable by
an H-projective flat finitely presented scheme, compatibly over every quotient base.
Source: Stacks Project, Tag 0E7R, `lemma-formal-algebraic-space-proper-reldim-1`;
Tag 0D4G, `lemma-check-flatness-on-infinitesimal-nbhds`.
(blueprint: lem-sfb-proper-formal-curve-algebraization).

Proof plan (the eight steps of the DAG node):
1. Power-series-field completeness and regularity make k[[t]] complete local Noetherian;
   its quotients are Noetherian, and finite type over them makes each X_n Noetherian.
2. Quotient base change makes each transition the nilpotent closed immersion defined
   by t^(n+1). Thus it is a homeomorphism and all X_n have dimension at most one.
3. The dimension-one ample-invertible theorem gives an ample line bundle on X_0.
   Picard lifting through each closed immersion gives compatible invertible lifts;
   compose adjacent pullback isomorphisms to obtain the cocycle identifications.
4. Polarized formal algebraization (Stacks 089A) gives Y, a finite projective-space
   embedding, and compatible isomorphisms over all the quotient bases.
5. Properness gives finite type, quasi-compactness and separatedness; the diagonal is
   quasi-compact, so the morphism is quasi-separated. Over the Noetherian base it is
   locally of finite presentation, hence of finite presentation. Y is Noetherian too.
6. On an affine open Spec B of Y, quotient base change identifies the reductions with
   Spec(B/t^(n+1)B). The given flatness and the affine flatness criterion make these
   flat over k[[t]]/(t^(n+1)).
7. Flat-module-powers (Stacks 0523) makes B_q flat over k[[t]] at every prime containing
   t. Affine-stalk localization identifies this with stalkwise flatness on the closed fibre.
8. Every nonzero power series is t^r times a unit, by the constant-coefficient unit
   criterion. Thus the only other base prime is (0), whose local ring is the fraction
   field. Modules over that field are flat, so Y is flat everywhere.

Compatibility is expressed on the maps X_n → Y obtained from the inverse isomorphisms.
Together with the explicitly required quotient-base equations, this is exactly
compatibility with the canonical base-change transitions (their two projections agree).
-/
theorem proper_formal_curve_algebraization
    (k : Type u) [Field k] (X : ℕ → Scheme.{u})
    (f : ∀ n : ℕ, X n ⟶ formalCurveBase k n)
    [∀ n : ℕ, IsProper (f n)] [∀ n : ℕ, Flat (f n)]
    [∀ n : ℕ, LocallyOfFinitePresentation (f n)]
    [∀ n : ℕ, QuasiCompact (f n)] [∀ n : ℕ, QuasiSeparated (f n)]
    (i : ∀ n : ℕ, X n ⟶ X (n + 1))
    (hcart : ∀ n : ℕ, IsPullback (i n) (f n) (f (n + 1)) (formalCurveBaseStep k n))
    (hdim : topologicalKrullDim (X 0) ≤ (1 : WithBot ℕ∞)) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of (PowerSeries k))),
      Flat g ∧ LocallyOfFinitePresentation g ∧ QuasiCompact g ∧ QuasiSeparated g ∧
        IsHProjective g ∧
        ∃ e : ∀ n : ℕ, pullback g (formalCurveBaseι k n) ≅ X n,
          (∀ n : ℕ, (e n).hom ≫ f n = pullback.snd g (formalCurveBaseι k n)) ∧
          (∀ n : ℕ, (e n).inv ≫ pullback.fst g (formalCurveBaseι k n) =
            i n ≫ (e (n + 1)).inv ≫ pullback.fst g (formalCurveBaseι k (n + 1))) := by
  sorry

end AlgebraicGeometry
