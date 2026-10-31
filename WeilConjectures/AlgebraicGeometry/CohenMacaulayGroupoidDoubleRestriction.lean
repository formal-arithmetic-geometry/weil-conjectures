/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupoidScheme
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.RingTheory.Depth
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.CohenMacaulayFieldExtension
import WeilConjectures.AlgebraicGeometry.FlatOfFpqcCover
import WeilConjectures.AlgebraicGeometry.LocallyOfFinitePresentationFpqcDescent

/-! # Cohen-Macaulay saturation after two groupoid restrictions

Source: Stacks Project, Tags 04MW and 04MX, applied to Cohen-Macaulay locally finitely
presented morphisms as in the final paragraph of Tag 04MZ. Target locality is Tag 045V.
(blueprint: lem-sfb-cm-groupoid-double-restriction).

The four auxiliary maps spell out the canonical projections in the statement.
Cohen-Macaulayness is expressed inline using flatness and Noetherian fibre stalks
whose depth equals their Krull dimension.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The saturation morphism `B ×[U] R → U`, using target for the pullback and source
for the outgoing map. Source: Stacks Project, Tag 04MX, notation `h`
(blueprint: lem-sfb-cm-groupoid-double-restriction). -/
noncomputable def groupoidSaturationMap {U R B : Scheme.{u}}
    (s t : R ⟶ U) (g : B ⟶ U) : pullback g t ⟶ U :=
  pullback.snd g t ≫ s

/-- The last projection `R_B = (B ×[U] R) ×[U] B → B`, the source of the restricted
groupoid. Source: Stacks Project, Tags 04MW and 04MX, notation `s'`
(blueprint: lem-sfb-cm-groupoid-double-restriction). -/
noncomputable def groupoidRestrictionSource {U R B : Scheme.{u}}
    (s t : R ⟶ U) (g : B ⟶ U) : pullback (groupoidSaturationMap s t g) g ⟶ B :=
  pullback.snd (groupoidSaturationMap s t g) g

/-- The first projection `R_B = (B ×[U] R) ×[U] B → B`, the target of the restricted
groupoid. Source: Stacks Project, Tags 04MW and 04MX, notation `t'`
(blueprint: lem-sfb-cm-groupoid-double-restriction). -/
noncomputable def groupoidRestrictionTarget {U R B : Scheme.{u}}
    (s t : R ⟶ U) (g : B ⟶ U) : pullback (groupoidSaturationMap s t g) g ⟶ B :=
  pullback.fst (groupoidSaturationMap s t g) g ≫ pullback.fst g t

/-- The second saturation `C ×[B] R_B → B`, using the two canonical restricted
projections. Source: Stacks Project, Tag 04MX, notation `h'`
(blueprint: lem-sfb-cm-groupoid-double-restriction). -/
noncomputable def groupoidSecondSaturationMap {U R B C : Scheme.{u}}
    (s t : R ⟶ U) (g : B ⟶ U) (j : C ⟶ B) :
    pullback j (groupoidRestrictionTarget s t g) ⟶ B :=
  pullback.snd j (groupoidRestrictionTarget s t g) ≫ groupoidRestrictionSource s t g

/-- Two successive restrictions whose saturation morphisms are Cohen-Macaulay and
locally of finite presentation have a Cohen-Macaulay locally finitely presented
composite saturation. Source: Stacks Project, Tags 04MW, 04MX and 045V, used in 04MZ
(blueprint: lem-sfb-cm-groupoid-double-restriction).

The maps `p,q` and equations `hs,ht` express the relative base. The groupoid laws
then make `e,i,c` morphisms over that base as well. The schemes `B,C` have structure
maps `g ≫ p` and `j ≫ g ≫ p`. The fibre conditions range over all points of every
scheme-theoretic fibre; via `Scheme.Hom.fiberHomeo` these are exactly the fibre
stalks at all source points. No surjectivity onto `U` is required.

Proof, following the six steps of the node:
1. Write W = B ×[U] R, Z = C ×[U] R, D = C ×[B] R_B and E = W ×[U] Z.
   The two squares of 04MW identify E → W with the base change of D → B along
   W → B. On test points the isomorphism sends ((b,r0),(z,r1)) to
   ((b,r0),(z,(j(z),c(r1,i(r0)),b))). Its inverse sends
   ((b,r0),(z,(j(z),a,b))) to ((b,r0),(z,c(a,r0))). The groupoid inverse, unit
   and associativity laws show that these are inverse scheme morphisms.
2. Flatness and local finite presentation make the image V of W → U open
   (lem-weil-pbc-flat-lfp-open). The corestriction W → V is surjective, flat
   and locally finitely presented: its stalk maps and affine finite presentations
   are unchanged (lem-weil-pbc-lfp-affine-opens-finite-presentation).
   It is an fppf and hence fpqc cover (lem-trf-fppf-covering-is-fpqc).
   The map (z,r) ↦ (j(z),r) from Z to W shows that Z → U factors through V.
3. By flat base change and lfp permanence (lem-weil-pbc-flat-morphism-base-change,
   lem-weil-pbc-qcqs-morphism-permanence), E → W is flat and lfp.
   Its fibres are field extensions of the fibres of D → B. A finite-presentation
   affine chart stays finitely generated after tensoring with the residue field
   (lem-weil-pbc-fibre-product-affine-spectra), so these fibres are locally of
   finite type over fields. Their Noetherian CM stalks ascend under arbitrary
   field extension (lem-pur-cohen-macaulay-field-extension, first assertion).
4. Identify E with W ×[V] Z and apply fpqc descent of flatness and lfp to obtain
   both properties for Z → V (lem-weil-pbc-fpqc-descend-flat and
   lem-weil-pbc-fpqc-descend-locally-finite-presentation).
5. Lift any point of Z to E using surjective base change
   (lem-weil-pbc-surjective-base-change). The fibre of E → W there is a field
   extension of the corresponding fibre of Z → V. The latter is locally of
   finite type by step 4 and the same affine calculation. The reverse direction
   of lem-pur-cohen-macaulay-field-extension gives depth equal to dimension at
   the original fibre point; the locally finite type fibre is locally Noetherian.
6. Composing Z → V with the open inclusion V → U preserves its target local
   rings, residue fields, fibre stalks and local finite presentations. Thus Z → U
   has all the claimed properties. If V is empty, Z is empty and the pointwise
   conditions hold vacuously. No Noetherian hypothesis on U or S is used. -/
theorem cm_groupoid_double_restriction
    {S U R B C : Scheme.{u}} (p : U ⟶ S) (q : R ⟶ S)
    (s t : R ⟶ U) (e : U ⟶ R) (i : R ⟶ R) (c : pullback s t ⟶ R)
    (hG : IsGroupoidScheme s t e i c) (hs : s ≫ p = q) (ht : t ≫ p = q)
    (g : B ⟶ U) (j : C ⟶ B)
    [Flat (groupoidSaturationMap s t g)]
    [LocallyOfFinitePresentation (groupoidSaturationMap s t g)]
    (hcmB : ∀ (y : U) (x : (groupoidSaturationMap s t g).fiber y),
      IsNoetherianRing (((groupoidSaturationMap s t g).fiber y).presheaf.stalk x) ∧
      (IsLocalRing.depth
        (R := ((groupoidSaturationMap s t g).fiber y).presheaf.stalk x)
        (((groupoidSaturationMap s t g).fiber y).presheaf.stalk x) : WithBot ℕ∞) =
          ringKrullDim (((groupoidSaturationMap s t g).fiber y).presheaf.stalk x))
    [Flat (groupoidSecondSaturationMap s t g j)]
    [LocallyOfFinitePresentation (groupoidSecondSaturationMap s t g j)]
    (hcmCB : ∀ (y : B) (x : (groupoidSecondSaturationMap s t g j).fiber y),
      IsNoetherianRing (((groupoidSecondSaturationMap s t g j).fiber y).presheaf.stalk x) ∧
      (IsLocalRing.depth
        (R := ((groupoidSecondSaturationMap s t g j).fiber y).presheaf.stalk x)
        (((groupoidSecondSaturationMap s t g j).fiber y).presheaf.stalk x) : WithBot ℕ∞) =
          ringKrullDim (((groupoidSecondSaturationMap s t g j).fiber y).presheaf.stalk x)) :
    Flat (groupoidSaturationMap s t (j ≫ g)) ∧
    LocallyOfFinitePresentation (groupoidSaturationMap s t (j ≫ g)) ∧
    ∀ (y : U) (x : (groupoidSaturationMap s t (j ≫ g)).fiber y),
      IsNoetherianRing (((groupoidSaturationMap s t (j ≫ g)).fiber y).presheaf.stalk x) ∧
      (IsLocalRing.depth
        (R := ((groupoidSaturationMap s t (j ≫ g)).fiber y).presheaf.stalk x)
        (((groupoidSaturationMap s t (j ≫ g)).fiber y).presheaf.stalk x) : WithBot ℕ∞) =
          ringKrullDim (((groupoidSaturationMap s t (j ≫ g)).fiber y).presheaf.stalk x) := by
  sorry

end AlgebraicGeometry
