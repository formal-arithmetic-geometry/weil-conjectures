/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q08
-/
module

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Relative rational maps and strict birational laws

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, 2.5 p.55, 5.1 pp.112--113,
5.2 Definition 1 p.115 (blueprint: def-sfb-relative-birational-law).

Open subschemes are represented by open immersions, retaining their domains rather than
choosing an isomorphic image. Products in `Over S` are scheme-theoretic fibre products.
The two translations have images V and W; being open immersions gives precisely the
isomorphisms onto those images. The common dense associativity chart expresses equality
as relative rational maps. All base-change data use `Over.pullback` and its product comparison.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

noncomputable section

variable {S T : Scheme.{u}}

/-- Fibrewise density of an open subset, BLR 2.5 p.55.
Source: BLR 2.5 (blueprint: def-sfb-relative-birational-law). -/
def Scheme.Hom.IsFiberwiseDenseOpen {X B : Scheme.{u}} (f : X ⟶ B) (U : X.Opens) : Prop :=
  ∀ b : B, Dense ((f.fiberι b) ⁻¹' (U : Set X))

/-- An open chart is dense relative to a structure map when its image is dense in each fibre.
The open-immersion requirement is separate, allowing this predicate on raw chart data.
Source: BLR 2.5 p.55 (blueprint: def-sfb-relative-birational-law). -/
def Scheme.Hom.IsFiberwiseDenseRange {D X B : Scheme.{u}} (i : D ⟶ X)
    (f : X ⟶ B) : Prop :=
  ∀ b : B, Dense ((f.fiberι b) ⁻¹' Set.range i)

/-- Raw data for a relative rational-map representative. The domain becomes an open subscheme
when `IsRational` holds; `Over S` supplies all structure-map compatibilities.
Source: BLR 2.5 p.55 (blueprint: def-sfb-relative-birational-law). -/
structure RelativeRationalChart (X Y : Over S) where
  /-- The scheme of definition, over the base. -/
  domain : Over S
  /-- Inclusion of the domain into the source. -/
  inclusion : domain ⟶ X
  /-- The morphism on the domain. -/
  hom : domain ⟶ Y

/-- A representative has a fibrewise dense open domain.
Source: BLR 2.5 p.55 (blueprint: def-sfb-relative-birational-law). -/
def RelativeRationalChart.IsRational {X Y : Over S} (r : RelativeRationalChart X Y) : Prop :=
  IsOpenImmersion r.inclusion.left ∧ r.inclusion.left.IsFiberwiseDenseRange X.hom

/-- Agreement on a fibrewise dense common open; open immersions may have different domains.
Source: BLR 2.5 p.55 (blueprint: def-sfb-relative-birational-law). -/
def RelativeRationalChart.Agrees {X Y : Over S} (r q : RelativeRationalChart X Y) : Prop :=
  ∃ (E : Over S) (i : E ⟶ X), IsOpenImmersion i.left ∧
    i.left.IsFiberwiseDenseRange X.hom ∧
    ∃ (a : E ⟶ r.domain) (b : E ⟶ q.domain),
      a ≫ r.inclusion = i ∧ b ≫ q.inclusion = i ∧ a ≫ r.hom = b ≫ q.hom

/-- Relative rational maps are representatives modulo agreement on a relative dense common
open. `Quot` forms the equivalence closure; the displayed agreement relation is itself an
equivalence relation by intersecting dense opens, as in BLR.
Source: BLR 2.5 p.55 (blueprint: def-sfb-relative-birational-law). -/
def RelativeRationalMap (X Y : Over S) : Type (u + 1) :=
  Quot (fun r q : {r : RelativeRationalChart X Y // r.IsRational} ↦ r.val.Agrees q.val)

/-- A relative birational representative is an isomorphism between relative dense opens.
Its map to the target is an open immersion, hence an isomorphism onto its open image.
Source: BLR 2.5 p.55 (blueprint: def-sfb-relative-birational-law). -/
def RelativeRationalChart.IsBirational {X Y : Over S} (r : RelativeRationalChart X Y) : Prop :=
  r.IsRational ∧ IsOpenImmersion r.hom.left ∧ r.hom.left.IsFiberwiseDenseRange Y.hom

/-- Canonical base change of raw representatives: pull back their actual domains and maps.
Source: BLR 2.5 p.55; Stacks 01JX (blueprint: def-sfb-relative-birational-law). -/
def RelativeRationalChart.baseChange {X Y : Over S} (r : RelativeRationalChart X Y)
    (g : T ⟶ S) :
    RelativeRationalChart ((Over.pullback g).obj X) ((Over.pullback g).obj Y) where
  domain := (Over.pullback g).obj r.domain
  inclusion := (Over.pullback g).map r.inclusion
  hom := (Over.pullback g).map r.hom

/-- The universal left translation `(x,y) ↦ (x,m(x,y))` on the chosen domain D.
Source: BLR 5.1 Definition 1(a) p.112 (blueprint: def-sfb-relative-birational-law). -/
def RelativeRationalChart.leftTranslation {Y : Over S} (m : RelativeRationalChart (Y ⨯ Y) Y) :
    m.domain ⟶ Y ⨯ Y :=
  prod.lift (m.inclusion ≫ prod.fst) m.hom

/-- The universal right translation `(x,y) ↦ (m(x,y),y)` on the chosen domain D.
Source: BLR 5.1 Definition 1(a) p.112 (blueprint: def-sfb-relative-birational-law). -/
def RelativeRationalChart.rightTranslation {Y : Over S} (m : RelativeRationalChart (Y ⨯ Y) Y) :
    m.domain ⟶ Y ⨯ Y :=
  prod.lift m.hom (m.inclusion ≫ prod.snd)

/-- Associativity as equality of relative rational maps: a relative dense open of triples
supports both inner and both outer products, and the resulting two morphisms agree there.
The equations specify `(x,y)`, `(y,z)`, `(xy,z)` and `(x,yz)` without choosing any product maps.
Source: BLR 5.1 Definition 1(b) p.112 (blueprint: def-sfb-relative-birational-law). -/
def RelativeRationalChart.IsAssociative {Y : Over S}
    (m : RelativeRationalChart (Y ⨯ Y) Y) : Prop :=
  ∃ (A : Over S) (i : A ⟶ (Y ⨯ Y) ⨯ Y), IsOpenImmersion i.left ∧
    i.left.IsFiberwiseDenseRange ((Y ⨯ Y) ⨯ Y).hom ∧
    ∃ (a b c d : A ⟶ m.domain),
      a ≫ m.inclusion = i ≫ prod.fst ∧
      b ≫ m.inclusion = prod.lift (i ≫ prod.fst ≫ prod.snd) (i ≫ prod.snd) ∧
      c ≫ m.inclusion = prod.lift (a ≫ m.hom) (i ≫ prod.snd) ∧
      d ≫ m.inclusion = prod.lift (i ≫ prod.fst ≫ prod.fst) (b ≫ m.hom) ∧
      c ≫ m.hom = d ≫ m.hom

/-- A chosen strict-law chart: D, V and W are open and dense for both projections, and
multiplication is associative as a relative rational map. V and W are the images of the
translations, whose open immersions supply the required isomorphisms from D.
The ambient smooth, separated, finite-type and nonempty-fibre assumptions are external.
Source: BLR 5.2 Definition 1 p.115 (blueprint: def-sfb-relative-birational-law). -/
def RelativeRationalChart.IsStrictLaw {Y : Over S}
    (m : RelativeRationalChart (Y ⨯ Y) Y) : Prop :=
  m.IsRational ∧ m.IsAssociative ∧
    IsOpenImmersion m.leftTranslation.left ∧ IsOpenImmersion m.rightTranslation.left ∧
    m.inclusion.left.IsFiberwiseDenseRange (prod.fst : Y ⨯ Y ⟶ Y).left ∧
    m.inclusion.left.IsFiberwiseDenseRange (prod.snd : Y ⨯ Y ⟶ Y).left ∧
    m.leftTranslation.left.IsFiberwiseDenseRange (prod.fst : Y ⨯ Y ⟶ Y).left ∧
    m.leftTranslation.left.IsFiberwiseDenseRange (prod.snd : Y ⨯ Y ⟶ Y).left ∧
    m.rightTranslation.left.IsFiberwiseDenseRange (prod.fst : Y ⨯ Y ⟶ Y).left ∧
    m.rightTranslation.left.IsFiberwiseDenseRange (prod.snd : Y ⨯ Y ⟶ Y).left

/-- Canonical base change of multiplication, using the canonical comparison
`(Y ×_S Y)_T ≅ Y_T ×_T Y_T`. The domain is exactly D_T, not an unspecified new chart.
Source: BLR 5.1 p.113 and 5.2 Definition 1 (blueprint: def-sfb-relative-birational-law). -/
def RelativeRationalChart.lawBaseChange {Y : Over S}
    (m : RelativeRationalChart (Y ⨯ Y) Y) (g : T ⟶ S) :
    RelativeRationalChart ((Over.pullback g).obj Y ⨯ (Over.pullback g).obj Y)
      ((Over.pullback g).obj Y) where
  domain := (Over.pullback g).obj m.domain
  inclusion := (Over.pullback g).map m.inclusion ≫ prodComparison (Over.pullback g) Y Y
  hom := (Over.pullback g).map m.hom

end

end AlgebraicGeometry
