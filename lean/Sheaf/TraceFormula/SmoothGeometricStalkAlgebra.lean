/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap
public import Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility
public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap

import Sheaf.AlgebraicGeometry.AffineStrictLocalRingComparison
import WeilConjectures.RingTheory.StrictHenselizationNoetherian
import Sheaf.Paper.StrictHenselizationFunctoriality
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.SmallStrictHenselizationIndEtale
import Sheaf.AlgebraicGeometry.IndEtaleStrictLocalInvariance
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.RingTheory.StrictHenselizationFaithfullyFlat
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedImmersionCartesian
import Sheaf.RingTheory.SmoothOverFieldRegularLocal
import WeilConjectures.RingTheory.StrictHenselizationRegular
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.RingTheory.PolynomialOriginRegularLocal
import WeilConjectures.RingTheory.StrictHenselizationDimension
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Flat.Stability
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Smooth geometric stalk algebras

Source: literature/stacks-project/algebra.tex, more-algebra.tex, morphisms.tex
(Morphisms Tags 01VF and 01VB; Algebra Tags 05WS and 00OR; More on Algebra
Tags 06LN and 06LK; blueprint: lem-trf-smooth-geometric-stalk-algebra).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

/-- The local-ring structure canonically supplied by strict henselization.
Source: Stacks Project, Tags 04HX and 06LJ (blueprint: lem-trf-smooth-geometric-stalk-algebra). -/
noncomputable instance strictHenselizationLocalRing
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) : IsLocalRing (Scheme.strictHenselizationRing s) :=
  Classical.choose (strictHenselizationLocalStructure s)

/-- The ring map induced by the canonical strict-henselization scheme map.
Source: Stacks Project, Tags 04HX, 03PS and 04GU
(blueprint: lem-trf-smooth-geometric-stalk-algebra). -/
noncomputable def strictHenselizationRingMap
    {S V : Scheme.{u}} (f : V ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (v : Spec (.of Ω) ⟶ V) :
    (Scheme.strictHenselizationRing (v ≫ f) : Type u) →+*
      (Scheme.strictHenselizationRing v : Type u) :=
  ((Scheme.ΓSpecIso (Scheme.strictHenselizationRing v)).hom.hom).comp
    (((Scheme.Hom.appTop (Scheme.strictHenselizationMap f v)).hom).comp
      (Scheme.ΓSpecIso (Scheme.strictHenselizationRing (v ≫ f))).inv.hom)

/-- Transport the canonical ring map along a displayed compatibility of points.
Source: Stacks Project, Tags 04HX, 03PS and 04GU
(blueprint: lem-trf-smooth-geometric-stalk-algebra). -/
noncomputable def strictHenselizationRingMapAlong
    {S V : Scheme.{u}} (f : V ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (v : Spec (.of Ω) ⟶ V) (hv : v ≫ f = s) :
    (Scheme.strictHenselizationRing s : Type u) →+*
      (Scheme.strictHenselizationRing v : Type u) :=
  hv ▸ strictHenselizationRingMap f v

/-- The affine-space coordinate in a strict geometric stalk.
Source: Stacks Project, Tag 00OR (blueprint: lem-trf-smooth-geometric-stalk-algebra). -/
noncomputable def strictHenselizationAffineCoordinate
    {S V : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (v : Spec (.of Ω) ⟶ V) (r : ℕ)
    (e : V ≅ 𝔸(ULift.{u} (Fin r); S)) (i : ULift.{u} (Fin r)) :
    (Scheme.strictHenselizationRing v : Type u) :=
  (Scheme.ΓSpecIso (Scheme.strictHenselizationRing v)).hom.hom
    ((Scheme.Hom.appTop
      (Scheme.strictHenselizationStructuralMap v ≫ e.hom)).hom
      (AffineSpace.coord S i))

/--
For a smooth morphism, strict local rings at compatible geometric points are
Noetherian local rings, the canonical map is flat and local, and its closed fibre
is regular.  Quotients by ideals below the maximal ideal retain these properties.
In the relative affine-space case the canonical coordinate sections cut regular
fibres and satisfy the dimension formula.

Source: Morphisms Tags 01VF and 01VB, Algebra Tags 05WS and 00OR, More on
Algebra Tags 06LN and 06LK (blueprint: lem-trf-smooth-geometric-stalk-algebra).

Proof plan, following the eight steps in the node:
1. Choose Noetherian affine neighbourhoods. The affine stalk-localization comparison and
   Noetherian localization identify their local rings; the affine strict-local comparison
   and Noetherian strict-henselization theorem make both strict local rings Noetherian.
   The comparison also identifies maximal-ideal membership with zero geometric evaluation.
2. Base change `V` to the strict localization of `S`. Functoriality lifts the common geometric
   point. The affine-chart structural map is ind-etale, so ind-etale strict-local invariance
   identifies the resulting strict local ring with `B`. Functorial uniqueness identifies
   its map from `A` with the canonical map used here.
3. Smooth-flatness makes the ordinary local map flat. Faithful flatness of its strict
   henselization and transitivity give flatness of the canonical map. Functoriality gives
   locality.
4. Base change to the residue field of `A`. The cartesian closed-immersion strict-localization
   theorem identifies its strict local ring with `B / mA B`. Smoothness over a field and
   preservation of regularity under strict henselization give regularity.
5. Flat quotient base change gives flatness over `A / I`. The quotient-local-structure
   theorem gives locality because `I` lies below `mA`. The inclusion `IB ≤ mA B` identifies
   the two displayed fibre quotients by the map fixing every quotient class.
6. Setting the selected coordinates to zero gives affine space in the remaining variables.
   Geometric evaluation makes the point factor through this closed subscheme. The cartesian
   strict-localization theorem identifies its ring with the coordinate quotient. Repeat
   steps 2--3 for its smooth projection, then apply quotient base change and quotient-local
   structure. Noetherianity descends from `B`.
7. On the closed fibre write `P` for the polynomial ring over the residue field of `A`,
   `q` for the geometric-point prime, and `L` for the selected-variable ideal. The affine
   comparison identifies the two fibre rings with strict henselizations of `P_q` and
   `(P/L)_(q/L)`. Polynomial regularity and strict-henselization regularity apply to both.
8. The subring `D` in the selected variables contracts `q` to its origin ideal `n`.
   The polynomial map `D → P` is smooth and flat. The flat height formula expresses
   `dim P_q` as `dim D_n + dim (P/L)_(q/L)`. The polynomial-origin dimension is `K.card`;
   preservation of dimension under strict henselization gives the displayed formula.
   This includes empty and full coordinate subsets and does not assume `q` maximal.
-/
theorem smooth_geometric_stalk_algebra
    {S V : Scheme.{u}} (f : V ⟶ S) [IsLocallyNoetherian S] [IsLocallyNoetherian V]
    [Smooth f] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (v : Spec (.of Ω) ⟶ V)
    (hv : v ≫ f = s) :
    IsNoetherianRing (Scheme.strictHenselizationRing s) ∧ IsNoetherianRing
          (Scheme.strictHenselizationRing v) ∧
      IsLocalRing (Scheme.strictHenselizationRing s) ∧ IsLocalRing (Scheme.strictHenselizationRing
          v) ∧
      RingHom.Flat (strictHenselizationRingMapAlong f s v hv) ∧ IsLocalHom
          (strictHenselizationRingMapAlong f s v hv) ∧
      IsRegularRing ((Scheme.strictHenselizationRing v) ⧸ Ideal.map
          (strictHenselizationRingMapAlong f s v hv) (IsLocalRing.maximalIdeal
          (Scheme.strictHenselizationRing s))) ∧
      (∀ (I : Ideal (Scheme.strictHenselizationRing s)), ∀ _hI : I ≤ (IsLocalRing.maximalIdeal
          (Scheme.strictHenselizationRing s)),
        RingHom.Flat (Ideal.quotientMap (Ideal.map (strictHenselizationRingMapAlong f s v hv) I)
          (strictHenselizationRingMapAlong f s v hv) Ideal.le_comap_map) ∧
          IsLocalHom (Ideal.quotientMap (Ideal.map (strictHenselizationRingMapAlong f s v hv) I)
          (strictHenselizationRingMapAlong f s v hv) Ideal.le_comap_map) ∧
          (∃ E : ((Scheme.strictHenselizationRing v) ⧸ (Ideal.map (strictHenselizationRingMapAlong
          f s v hv) I ⊔ Ideal.map (strictHenselizationRingMapAlong f s v hv)
          (IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing s)))) ≃+*
            ((Scheme.strictHenselizationRing v) ⧸ Ideal.map (strictHenselizationRingMapAlong f s v
          hv) (IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing s))), ∀ b :
          (Scheme.strictHenselizationRing v),
              E (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk _ b)) ∧
      (∀ (r : ℕ) (e : V ≅ 𝔸(ULift.{u} (Fin r); S))
        (_he : e.hom ≫ (𝔸(ULift.{u} (Fin r); S) ↘ S) = f)
        (K : Finset (ULift.{u} (Fin r)))
        (_hK : ∀ i, i ∈ K → strictHenselizationAffineCoordinate v r e i ∈
          (IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing v)))
        (I : Ideal (Scheme.strictHenselizationRing s)), ∀ _hI : I ≤ (IsLocalRing.maximalIdeal
          (Scheme.strictHenselizationRing s)),
        IsNoetherianRing
          ((Scheme.strictHenselizationRing v) ⧸ (Ideal.map (strictHenselizationRingMapAlong f s v
          hv) I ⊔ Ideal.span (Set.range
            (fun i : K ↦ strictHenselizationAffineCoordinate v r e i.1)))) ∧
        IsLocalRing
          ((Scheme.strictHenselizationRing v) ⧸ (Ideal.map (strictHenselizationRingMapAlong f s v
          hv) I ⊔ Ideal.span (Set.range
            (fun i : K ↦ strictHenselizationAffineCoordinate v r e i.1)))) ∧
        RingHom.Flat (Ideal.quotientMap
          (Ideal.map (strictHenselizationRingMapAlong f s v hv) I ⊔ Ideal.span (Set.range
            (fun i : K ↦ strictHenselizationAffineCoordinate v r e i.1)))
          (strictHenselizationRingMapAlong f s v hv)
          (Ideal.le_comap_map.trans (Ideal.comap_mono le_sup_left))) ∧
        IsRegularRing
          ((Scheme.strictHenselizationRing v) ⧸ (Ideal.map (strictHenselizationRingMapAlong f s v
          hv) (IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing s)) ⊔ Ideal.span
          (Set.range
            (fun i : K ↦ strictHenselizationAffineCoordinate v r e i.1)))) ∧
        (∃ E :
          ((Scheme.strictHenselizationRing v) ⧸ ((Ideal.map (strictHenselizationRingMapAlong f s v
          hv) I ⊔ Ideal.span (Set.range
            (fun i : K ↦ strictHenselizationAffineCoordinate v r e i.1))) ⊔ Ideal.map
          (strictHenselizationRingMapAlong f s v hv) (IsLocalRing.maximalIdeal
          (Scheme.strictHenselizationRing s)))) ≃+*
          ((Scheme.strictHenselizationRing v) ⧸ (Ideal.map (strictHenselizationRingMapAlong f s v
          hv) (IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing s)) ⊔ Ideal.span
          (Set.range
            (fun i : K ↦ strictHenselizationAffineCoordinate v r e i.1)))),
          ∀ b : (Scheme.strictHenselizationRing v), E (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk
          _ b) ∧
        ringKrullDim ((Scheme.strictHenselizationRing v) ⧸ Ideal.map
          (strictHenselizationRingMapAlong f s v hv) (IsLocalRing.maximalIdeal
          (Scheme.strictHenselizationRing s))) =
          ringKrullDim
            ((Scheme.strictHenselizationRing v) ⧸ (Ideal.map (strictHenselizationRingMapAlong f s
          v hv) (IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing s)) ⊔ Ideal.span
          (Set.range
              (fun i : K ↦ strictHenselizationAffineCoordinate v r e i.1)))) + K.card) := by
  sorry

end AlgebraicGeometry
