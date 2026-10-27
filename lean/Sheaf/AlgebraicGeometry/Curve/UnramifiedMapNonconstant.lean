module

public import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
public import Sheaf.AlgebraicGeometry.UnramifiedMorphism
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.AlgebraicGeometry.Dimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.UnramifiedFibrePointIsolated
import Mathlib.Topology.KrullDimension

/-! # Unramified morphisms of integral curves are nonconstant

Source: Stacks Project, Curves, Tag 0C1C (`lemma-generically-etale`), the nonconstancy
check in (3) implies (4) before Tag 0CCK (`lemma-flat`); Morphisms, Tag 02G7.
(blueprint: lem-a1-unramified-curve-map-nonconstant).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An unramified morphism of integral curves has two distinct image points. The same holds
on every nonempty open source, which is itself an integral curve over the base field.

Source: Stacks Project, Curves, Tag 0C1C, omitted nonconstancy check in (3) implies (4)
before Tag 0CCK; Morphisms, Tag 02G7(2).
(blueprint: lem-a1-unramified-curve-map-nonconstant).

Proof:
1. A nonempty open `V` of `X` is integral (`def-pc-integral-scheme`). Its diagonal is the
   restriction of the closed diagonal of `X` to the open fibre product
   (`lem-weil-pbc-open-fibre-product`), hence is closed. This gives separatedness
   (`def-weil-proper-morphism`).
2. The spectrum of a field is Noetherian, so finite type makes `X` Noetherian
   (`lem-weil-pbc-finite-type-over-noetherian`). Its open immersion `V.ι` is quasi-compact
   (`lem-sfb-noetherian-open-immersion-qc`) and therefore finite type
   (`lem-weil-pbc-qc-open-immersion-finite-type`). Composition then makes `V` finite type
   over the field (`lem-sfb-finite-type-composition-base-change`, clause (1)).
3. Convert local-ring dimension to topological dimension using
   `lem-pc-scheme-dimension-local-rings`. The nonempty open has the same dimension as `X`
   by `lem-sc-integral-locally-algebraic-opens-dimension`. Thus `V` is a curve
   (`def-pc-curve`).
4. Apply the following to either `(X, h)` or `(V, V.ι ≫ h)`. An integral curve is nonempty
   and irreducible. If its image has fewer than two points, its unique nonempty fibre
   is the entire source. Unramifiedness includes local finite type
   (`def-weil-unramified-morphism`), and `lem-weil-pbc-unramified-fibre-point-isolated`
   makes every singleton open in this fibre. The source is therefore discrete. An
   irreducible discrete nonempty space has just one point, and its topological Krull
   dimension is zero (`def-kun-topological-krull-dimension`), contradicting dimension one
   (`lem-pc-scheme-dimension-local-rings`). This works for both closed and generic images.
-/
theorem unramified_curve_map_nonconstant {k : Type u} [Field k] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [IsIntegralCurve pX] [IsIntegralCurve pY] (h : X ⟶ Y) (h_over : h ≫ pY = pX) :
    (IsUnramified h → ∃ x₁ x₂ : X, h x₁ ≠ h x₂) ∧
      (∀ V : X.Opens, Nonempty V → IsUnramified (V.ι ≫ h) →
        IsIntegralCurve (V.ι ≫ pX) ∧
          ∃ v₁ v₂ : V.toScheme, (V.ι ≫ h) v₁ ≠ (V.ι ≫ h) v₂) := by
  sorry

end AlgebraicGeometry
