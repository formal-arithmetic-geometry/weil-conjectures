/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Blowup.FlatBaseChange
public import WeilConjectures.Compactification.StrictTransform
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import Sheaf.AlgebraicGeometry.IsRegularScheme
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.LocalRing.Module
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.RingTheory.RegularLocalQuotientKernelParameters
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import Sheaf.AlgebraicGeometry.CoordinateSubspaceBlowupCharts

/-! # Smooth pullbacks of coordinate-subspace blowups

Source: Stacks Project, Tags 0H1H, 0FUT, 0805, 01VB, 01VA and 056S;
ILO VIII Lemma 4.2.9, printed p.121
(blueprint: lem-sfb-smooth-coordinate-blowup-charts).

The auxiliary definitions specialize ideal sheaves to the coordinate functions and package
exactly the intersection and parameter assertions used on the original scheme and its charts.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.SmoothCoordinateBlowup

/-- The pulled-back affine coordinates, indexed from zero instead of one.
Source: Stacks, Tag 0H1H (blueprint: lem-sfb-smooth-coordinate-blowup-charts). -/
def coordinates {F : Type u} [Field F] {n : ℕ} {V : Scheme.{u}}
    (c : V ⟶ AffineSpace (ULift.{u} (Fin n)) (Spec (.of F))) : Fin n → Γ(V, ⊤) :=
  fun a ↦ c.appTop (AffineSpace.coord (Spec (.of F)) (ULift.up a))

/-- The scheme-theoretic coordinate intersection ideal, including the zero ideal for no
coordinates. Source: Stacks, Tags 01VB and 0H1H
(blueprint: lem-sfb-smooth-coordinate-blowup-charts). -/
def intersection {V : Scheme.{u}} {n : ℕ} (z : Fin n → Γ(V, ⊤))
    (A : Finset (Fin n)) : V.IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (Ideal.span (z '' (A : Set (Fin n))))

/-- The principal ideal of a global equation. Source: ILO VIII Lemma 4.2.9, p.121
(blueprint: lem-sfb-smooth-coordinate-blowup-charts). -/
def equation {V : Scheme.{u}} (f : Γ(V, ⊤)) : V.IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (Ideal.span {f})

/-- The product coordinate equation; the empty product defines the empty divisor.
Source: ILO VIII Lemma 4.2.9, p.121
(blueprint: lem-sfb-smooth-coordinate-blowup-charts). -/
def boundary {V : Scheme.{u}} {n : ℕ} (z : Fin n → Γ(V, ⊤))
    (A : Finset (Fin n)) : V.IdealSheafData :=
  equation (∏ a ∈ A, z a)

/-- The intersection, pure codimension, and local parameter assertions for a coordinate list.
Pure codimension is the dimension of the ambient local ring at each component's generic
point. Vanishing means membership of the coordinate germ in the maximal ideal; an injection
into the positions of a regular parameter list expresses that the vanishing coordinates
are distinct members of that list. No ordering of the vanishing indices is imposed.
Source: Stacks, Tags 01VB, 01VA, 056S, 00NR and 00KU
(blueprint: lem-sfb-smooth-coordinate-blowup-charts). -/
def CoordinateGeometry {F : Type u} [Field F] {V : Scheme.{u}} {n : ℕ}
    (p : V ⟶ Spec (.of F)) (z : Fin n → Γ(V, ⊤)) : Prop :=
  (∀ A : Finset (Fin n),
    Smooth ((intersection z A).subschemeι ≫ p) ∧
    IsReduced (intersection z A).subscheme ∧
    IsRegularScheme (intersection z A).subscheme ∧
    ∀ Z ∈ irreducibleComponents (intersection z A).subscheme,
      ∀ η : (intersection z A).subscheme, IsGenericPoint η Z →
        ringKrullDim (V.presheaf.stalk ((intersection z A).subschemeι η)) =
          (A.card : WithBot ℕ∞)) ∧
  IsIso (intersection z ∅).subschemeι ∧
  ∀ x : V, ∃ (hR : IsNoetherianRing (V.presheaf.stalk x))
      (t : List (V.presheaf.stalk x)),
    @IsLocalRing.IsRegularSystemOfParameters (V.presheaf.stalk x) _ _ hR t ∧
    ∃ f : {a : Fin n // (V.presheaf.germ ⊤ x trivial).hom (z a) ∈
        IsLocalRing.maximalIdeal (V.presheaf.stalk x)} → Fin t.length,
      Function.Injective f ∧
      ∀ a, t.get (f a) = (V.presheaf.germ ⊤ x trivial).hom (z a.val)

/-- Smooth coordinate intersections and the complete coordinate blowup calculation.
Source: Stacks, Tags 0H1H, 0FUT and 0805; ILO VIII Lemma 4.2.9, p.121
(blueprint: lem-sfb-smooth-coordinate-blowup-charts).

Proof:
1. Each coordinate intersection is a smooth base change of `c` followed by the smooth
   affine-space projection (lem-pc-proper-base-change, sbc-lem-affine-space-smooth,
   lem-trf-smooth-composition). Smooth schemes over a field are regular, hence reduced
   (lem-weil-pbc-smooth-scheme-over-field-regular, lem-sc-regular-local-domain).
2. Distinct variables form a regular sequence in the polynomial ring. Localization and
   flat tensoring preserve the successive multiplication injections
   (lem-exc-weakly-regular-sequence-localization, lem-weil-pbc-flat-tensor-exact,
   lem-pc-smooth-flat). The final quotient is nonzero at a point where they vanish.
3. The quotient is regular. Its dimension is the ambient dimension minus the sequence
   length (lem-trf-regular-sequence-dimension-formula). The quotient kernel is generated
   by a parameter prefix (lem-weil-pbc-regular-local-quotient-kernel-parameters).
   The supplied coordinate classes are independent modulo the square of the maximal
   ideal; extend them to a basis and lift it. Nakayama gives a parameter system
   (lem-weil-pbc-nakayama-local-generators). At generic points of the intersections the
   quotient local ring is a field, giving the asserted pure codimension.
4. Individual parameter ideals are prime, since their quotients are regular local
   domains (lem-weil-pbc-regular-local-generators-regular-sequence,
   lem-sc-regular-local-domain). Their pairwise distinct generators are not in one
   another's ideals. The intersection of these prime ideals is their product.
   This proves that the product boundary ideals are radical and effective Cartier.
5. The center ideal is pulled back from affine space. The canonical comparison is an
   isomorphism by thm-nagata-blowup-flat-base-change. Pull back the polynomial charts
   of lem-trf-coordinate-subspace-blowup-charts; they remain smooth over their affine
   models. Apply steps 1--3 to the chart coordinates.
6. On the j-chart the center ideal becomes `(z_j)`. Substitution in the boundary
   product gives `z_j^|S|` times the ratio product times the unchanged product.
   Taking its radical removes the excess power of `z_j`; step 4 shows the displayed
   reduced product is already radical.
7. On the complement of the center, `z_j` is invertible and the strict transform has
   the ratio-product equation. The kernel defining schematic closure is the saturation
   of that product ideal by `z_j`. Primality of the distinct parameter ideals shows
   the product ideal is already saturated, so the equation holds scheme-theoretically
   (def-nagata-strict-transform, def-nagata-scheme-theoretic-image).
8. For a singleton center list there are no ratio coordinates: the model chart map is
   the identity and the strict equation is the empty product, namely 1. Empty charts
   and intersections impose no local conditions; for n=0 there is no nonempty S.
   Every argument is local, with no perfection or global finiteness assumption.
-/
theorem smooth_coordinate_blowup_charts (F : Type u) [Field F] (n : ℕ)
    (V : Scheme.{u}) (c : V ⟶ AffineSpace (ULift.{u} (Fin n)) (Spec (.of F)))
    [Smooth c] :
    CoordinateGeometry (c ≫ (AffineSpace.over _ _).hom) (coordinates c) ∧
    ∀ S T : Finset (Fin n), S.Nonempty → S ⊆ T →
      (boundary (coordinates c) T).IsInvertible ∧
      IsReduced (boundary (coordinates c) T).subscheme ∧
      (boundary (coordinates c) S).IsInvertible ∧
      IsReduced (boundary (coordinates c) S).subscheme ∧
      (∃ h : intersection (coordinates c) S =
          (intersection (coordinates (𝟙 (AffineSpace (ULift.{u} (Fin n))
            (Spec (.of F))))) S).comap c,
        IsIso (eqToHom (congrArg Scheme.IdealSheafData.blowup h) ≫
          (intersection (coordinates (𝟙 (AffineSpace (ULift.{u} (Fin n))
            (Spec (.of F))))) S).blowupFlatBaseChange c)) ∧
      (∃ (W : S → Scheme.{u})
          (ι : ∀ j, W j ⟶ (intersection (coordinates c) S).blowup)
          (q : ∀ j, W j ⟶ AffineSpace (ULift.{u} (Fin n)) (Spec (.of F))),
        (∀ j, IsOpenImmersion (ι j)) ∧
        (∀ x : (intersection (coordinates c) S).blowup,
          ∃ (j : S) (w : W j), ι j w = x) ∧
        ∀ j, Smooth (q j) ∧
          q j ≫ (AffineSpace.over _ _).hom =
            ι j ≫ (intersection (coordinates c) S).blowupMap ≫ c ≫
              (AffineSpace.over _ _).hom ∧
          (∀ a : Fin n, a = j.val ∨ a ∉ S →
            (coordinates (q j)) a =
              (ι j ≫ (intersection (coordinates c) S).blowupMap).appTop (coordinates c a)) ∧
          (∀ a ∈ S.erase j.val,
            (ι j ≫ (intersection (coordinates c) S).blowupMap).appTop (coordinates c a) =
              coordinates (q j) j.val * coordinates (q j) a) ∧
          (intersection (coordinates c) S).comap
              (ι j ≫ (intersection (coordinates c) S).blowupMap) =
            equation (coordinates (q j) j.val) ∧
          (((boundary (coordinates c) T).comap
              (intersection (coordinates c) S).blowupMap).radical).comap (ι j) =
            boundary (coordinates (q j)) T ∧
          (AlgebraicGeometry.strictTransformMap (boundary (coordinates c) S).subschemeι
              (intersection (coordinates c) S).blowupMap
              (intersection (coordinates c) S).support.compl).ker.comap (ι j) =
            boundary (coordinates (q j)) (S.erase j.val) ∧
          CoordinateGeometry (q j ≫ (AffineSpace.over _ _).hom) (coordinates (q j))) ∧
      (S.card = 1 → IsIso (intersection (coordinates c) S).blowupMap ∧
        IsEmpty ((intersection (coordinates c) S).strictTransform
          (boundary (coordinates c) S).subschemeι)) := by
  sorry

end AlgebraicGeometry.SmoothCoordinateBlowup
