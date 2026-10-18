/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Relative logarithmic differentials at a geometric point

Source: ILO, Exposé XVI Proposition 3.6.3, p.252, and Exposé X Proposition 1.2,
pp.136--138 (blueprint: def-per-log-differential-stalk).

The free module on ordinary and logarithmic symbols is divided by the differential
relations. Base relations range over all relative pointed étale neighbourhoods;
by the geometric stalk colimit this kills precisely the base ring and log stalk.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry
namespace EtaleLogHom

variable {X Y : FineSaturatedLogScheme.{u}} (f : EtaleLogHom X Y)
variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme)

/-- The relation submodule on symbols `da` and `dlog m`. Base sections are killed on
all relative étale neighbourhoods, equivalently at the base geometric stalk.
Source: ILO X 1.2, XVI 3.6.3 (blueprint: def-per-log-differential-stalk). -/
noncomputable def logDifferentialRelations :
    Submodule (strictLocalRing X.scheme t)
      (Sum (strictLocalRing X.scheme t) (X.logStructure.stalk t) →₀
        strictLocalRing X.scheme t) :=
  let d := fun a : strictLocalRing X.scheme t ↦
    Finsupp.single (Sum.inl a : Sum _ (X.logStructure.stalk t))
      (1 : strictLocalRing X.scheme t)
  let l := fun m : X.logStructure.stalk t ↦
    Finsupp.single (Sum.inr m : Sum (strictLocalRing X.scheme t) _)
      (1 : strictLocalRing X.scheme t)
  Submodule.span (strictLocalRing X.scheme t) {s |
    (∃ a b, s = d (a + b) - d a - d b) ∨
    (∃ a b, s = d (a * b) - a • d b - b • d a) ∨
    (∃ m m', s = l (m * m') - l m - l m') ∨
    (∃ m, s = d (X.logStructure.stalkAlpha t m) -
      X.logStructure.stalkAlpha t m • l m) ∨
    (∃ (W : Y.scheme.Etale) (V : X.scheme.Etale)
      (v : (Scheme.pointSmallEtale t).fiber.obj V) (k : V.left ⟶ W.left)
      (_hk : k ≫ W.hom = V.hom ≫ f.base) (c : Γ(W.left, ⊤)),
      s = d (strictLocalGerm X.scheme t V v (k.appTop c))) ∨
    (∃ (W : Y.scheme.Etale) (V : X.scheme.Etale)
      (v : (Scheme.pointSmallEtale t).fiber.obj V) (k : V.left ⟶ W.left)
      (hk : k ≫ W.hom = V.hom ≫ f.base)
      (b : Y.logStructure.monoidSheaf.obj.obj (op W)),
      s = l (X.logStructure.germ t V v (f.sectionMap W V k hk b)))}

/-- The actual quotient module of relative logarithmic differentials.
Source: ILO X 1.2, XVI 3.6.3 (blueprint: def-per-log-differential-stalk). -/
noncomputable abbrev LogDifferential :=
  (Sum (strictLocalRing X.scheme t) (X.logStructure.stalk t) →₀
    strictLocalRing X.scheme t) ⧸ f.logDifferentialRelations t

/-- The logarithmic differential of a log-stalk element, represented by its symbol.
Source: ILO XVI 3.6.3 (blueprint: def-per-log-differential-stalk). -/
noncomputable def logDLog (m : X.logStructure.stalk t) : f.LogDifferential t :=
  (f.logDifferentialRelations t).mkQ (Finsupp.single (Sum.inr m) 1)

/-- The ordinary differential, represented by its symbol.
Source: ILO X 1.2 (blueprint: def-per-log-differential-stalk). -/
noncomputable def logD (a : strictLocalRing X.scheme t) : f.LogDifferential t :=
  (f.logDifferentialRelations t).mkQ (Finsupp.single (Sum.inl a) 1)

/-- The canonical image of a global base chart in the source log stalk. This is
section pullback followed by the geometric germ, with no chosen comparison map.
Source: ILO XVI 3.6.3 (blueprint: def-per-log-differential-stalk). -/
noncomputable def baseChartGerm {Q : Type u} [CommMonoid Q]
    (β : Q →* Y.logStructure.monoidSheaf.obj.obj
      (op (Scheme.Etale.mk (𝟙 Y.scheme)))) : Q →* X.logStructure.stalk t :=
  (X.logStructure.germ t (Scheme.Etale.mk (𝟙 X.scheme))
    (Over.homMk t)).hom.comp
      ((f.sectionMap (Scheme.Etale.mk (𝟙 Y.scheme)) (Scheme.Etale.mk (𝟙 X.scheme))
        f.base ((Category.comp_id f.base).trans (Category.id_comp f.base).symm)).comp β)

end EtaleLogHom
end AlgebraicGeometry
