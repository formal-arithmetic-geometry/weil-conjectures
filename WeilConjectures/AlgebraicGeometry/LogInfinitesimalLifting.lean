/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LogIdealChartPresentation
public import WeilConjectures.AlgebraicGeometry.Thickening

/-!
# Strict logarithmic infinitesimal lifting conditions

Source: Kato, Logarithmic structures of Fontaine--Illusie, 1.3--1.4 and 3.1--3.3,
printed pp.192--193 and 200--201; ILO VI 1.1 and X Proposition 1.2
(blueprint: def-sfb-log-infinitesimal-lifting-properties).

The tests are arbitrary schemes equipped with the existing `EtaleLogStructure.IsFine`.
In particular neither local Noetherianness nor saturation is imposed on test objects.
Strictness uses the actual unit-pushout congruence of `IsStalkChart`. The stalk map is
normalized on every relative pointed etale diagram by the given log morphism.
Pointwise etale-local existence specifies a jointly surjective family by taking all
of the witnessed neighbourhoods; it includes the empty covering of an empty scheme.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Equality of two composites of arbitrary log morphisms. The shared composite is
specified by the existing `CompEq`, including its scheme map and all section maps.
Source: Kato 1.1 and 3.2
(blueprint: def-sfb-log-infinitesimal-lifting-properties). -/
def EtaleLogMap.CompositesEq {T X X' Y : Scheme.{u}}
    {L : EtaleLogStructure T} {M : EtaleLogStructure X}
    {M' : EtaleLogStructure X'} {N : EtaleLogStructure Y}
    (a : EtaleLogMap L M) (f : EtaleLogMap M N)
    (i : EtaleLogMap L M') (b : EtaleLogMap M' N) : Prop :=
  ∃ d : EtaleLogMap L N, a.CompEq f d ∧ i.CompEq b d

/-- Strictness for arbitrary log schemes: the canonical morphism from the associated
inverse-image log structure is an isomorphism. At a geometric point its source is
`M_stalk ⊕_{β⁻¹(Oˣ)} Oˣ`; `IsStalkChart` says that the product map onto the source log
stalk is surjective with exactly this unit-pushout congruence as kernel. The last
clause fixes the stalk map on every section representative, so no arbitrary isomorphism
or uncharacterized map is substituted for the canonical map. Geometric stalks commute
with inverse image, sheafification and this pushout, and detect sheaf isomorphisms.
Source: Kato 1.3--1.4 and 3.1; ILO VI 1.1
(blueprint: def-sfb-log-infinitesimal-lifting-properties). -/
def EtaleLogMap.IsStrict {Y X : Scheme.{u}}
    {N : EtaleLogStructure Y} {M : EtaleLogStructure X}
    (f : EtaleLogMap N M) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Y),
    ∃ φ : M.toEtalePrelogStructure.stalk (t ≫ f.base) →*
        N.toEtalePrelogStructure.stalk t,
      N.IsStalkChart t φ ∧
        ∀ (W : X.Etale) (V : Y.Etale) (k : V.left ⟶ W.left)
          (hk : k ≫ W.hom = V.hom ≫ f.base)
          (w : (Scheme.pointSmallEtale (t ≫ f.base)).fiber.obj W)
          (v : (Scheme.pointSmallEtale t).fiber.obj V),
          v.left ≫ k = w.left →
            ∀ s : M.monoidSheaf.obj.obj (op W),
              φ (M.toEtalePrelogStructure.germ (t ≫ f.base) W w s) =
                N.toEtalePrelogStructure.germ t V v (f.sectionMap W V k hk s)

/-- Existence of log lifts etale locally for every strict square-zero fine test square.
The log structures on the etale neighbourhood and on the scheme fibre product are
identified by strict etale maps with the prescribed pullbacks. The map `j` is the
restriction of the original test immersion: its base is the second projection and
its log map is fixed by its commuting square with the strict etale map `v`.
Source: Kato 3.2--3.3, printed pp.200--201
(blueprint: def-sfb-log-infinitesimal-lifting-properties). -/
def EtaleLogMap.HasEtaleLocalInfinitesimalLifts {X Y : Scheme.{u}}
    {M : EtaleLogStructure X} {N : EtaleLogStructure Y}
    (f : EtaleLogMap M N) : Prop :=
  ∀ (T₀ T : Scheme.{u}) (L₀ : EtaleLogStructure T₀) (L : EtaleLogStructure T),
    L₀.IsFine → L.IsFine →
      ∀ (i : EtaleLogMap L₀ L) (a : EtaleLogMap L₀ M) (b : EtaleLogMap L N),
        IsFirstOrderThickening i.base → i.IsStrict → a.CompositesEq f i b →
          ∀ t : T,
            ∃ (V : T.Etale) (L' : EtaleLogStructure V.left)
              (v : EtaleLogMap L' L) (c : EtaleLogMap L' M)
              (L₀' : EtaleLogStructure (pullback i.base V.hom))
              (v₀ : EtaleLogMap L₀' L₀) (j : EtaleLogMap L₀' L'),
              t ∈ Set.range V.hom ∧
                v.base = V.hom ∧ v.IsStrictEtale ∧
                v₀.base = pullback.fst i.base V.hom ∧ v₀.IsStrictEtale ∧
                j.base = pullback.snd i.base V.hom ∧
                j.CompositesEq v v₀ i ∧ c.CompositesEq f v b ∧ j.CompositesEq c v₀ a

/-- Exactly one global log lift for every strict square-zero fine test square.
The uniqueness quantifier ranges over log morphisms, including their underlying
scheme maps and monoid-sheaf maps. Source: Kato 3.2--3.3, printed pp.200--201
(blueprint: def-sfb-log-infinitesimal-lifting-properties). -/
def EtaleLogMap.HasUniqueInfinitesimalLifts {X Y : Scheme.{u}}
    {M : EtaleLogStructure X} {N : EtaleLogStructure Y}
    (f : EtaleLogMap M N) : Prop :=
  ∀ (T₀ T : Scheme.{u}) (L₀ : EtaleLogStructure T₀) (L : EtaleLogStructure T),
    L₀.IsFine → L.IsFine →
      ∀ (i : EtaleLogMap L₀ L) (a : EtaleLogMap L₀ M) (b : EtaleLogMap L N),
        IsFirstOrderThickening i.base → i.IsStrict → a.CompositesEq f i b →
          ∃! c : EtaleLogMap L M, c.CompEq f b ∧ i.CompEq c a

end AlgebraicGeometry
