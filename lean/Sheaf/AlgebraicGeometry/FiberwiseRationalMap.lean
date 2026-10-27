module

public import Mathlib.AlgebraicGeometry.Fiber

/-! # Fibrewise rational maps

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, §2.5, printed pp.55--56.
(blueprint: def-sfb-fibrewise-rational-map).

Unlike ordinary rational maps, these representatives have domains dense in every fibre.
The quotient uses the relation of agreement on a fibrewise dense common open.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An open is base-dense when its inverse image in each scheme-theoretic fibre is dense.
Source: BLR §2.5, p.55 (blueprint: def-sfb-fibrewise-rational-map). -/
def Scheme.Hom.IsFiberwiseDense {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens) : Prop :=
  ∀ s : S, Dense (f.fiberι s ⁻¹' (U : Set X))

/-- A representative of a relative rational map, including its specified structure maps.
Source: BLR §2.5, p.55 (blueprint: def-sfb-fibrewise-rational-map). -/
structure Scheme.FiberwisePartialMap {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) where
  domain : X.Opens
  dense : f.IsFiberwiseDense domain
  hom : domain.toScheme ⟶ Y
  over : hom ≫ g = domain.ι ≫ f

/-- Agreement on a fibrewise dense common open is the relation defining relative rational maps.
Source: BLR §2.5, p.55 (blueprint: def-sfb-fibrewise-rational-map). -/
def Scheme.FiberwisePartialMap.Equiv {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (a b : Scheme.FiberwisePartialMap f g) : Prop :=
  ∃ (U : X.Opens) (ha : U ≤ a.domain) (hb : U ≤ b.domain),
    f.IsFiberwiseDense U ∧ X.homOfLE ha ≫ a.hom = X.homOfLE hb ≫ b.hom

/-- Relative rational maps are classes of morphisms on fibrewise dense opens.
`Quot` takes the generated equivalence relation; the displayed relation is already an
 equivalence relation since finite intersections of dense opens in each fibre are dense.
Source: BLR §2.5, p.55 (blueprint: def-sfb-fibrewise-rational-map). -/
def Scheme.FiberwiseRationalMap {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) : Type u :=
  Quot (Scheme.FiberwisePartialMap.Equiv (f := f) (g := g))

/-- An isomorphism of fibrewise dense opens represents a relative birational map.
Source: BLR §2.5, pp.55--56 (blueprint: def-sfb-fibrewise-rational-map). -/
structure Scheme.FiberwisePartialIso {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) where
  domain : X.Opens
  target : Y.Opens
  dense_domain : f.IsFiberwiseDense domain
  dense_target : g.IsFiberwiseDense target
  iso : domain.toScheme ≅ target.toScheme
  over : iso.hom ≫ target.ι ≫ g = domain.ι ≫ f

/-- Forget the open image of a birational representative.
Source: BLR §2.5, pp.55--56 (blueprint: def-sfb-fibrewise-rational-map). -/
def Scheme.FiberwisePartialIso.toPartialMap {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (e : Scheme.FiberwisePartialIso f g) : Scheme.FiberwisePartialMap f g where
  domain := e.domain
  dense := e.dense_domain
  hom := e.iso.hom ≫ e.target.ι
  over := (Category.assoc _ _ _).trans e.over

/-- A relative rational map is birational if an isomorphism of base-dense opens represents it.
Source: BLR §2.5, pp.55--56 (blueprint: def-sfb-fibrewise-rational-map). -/
def Scheme.FiberwiseRationalMap.IsBirational {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (q : Scheme.FiberwiseRationalMap f g) : Prop :=
  ∃ e : Scheme.FiberwisePartialIso f g, Quot.mk _ e.toPartialMap = q

end AlgebraicGeometry
