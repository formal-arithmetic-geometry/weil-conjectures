/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Mathlib.CategoryTheory.Endomorphism

/-!
# Group actions and invariant quotients of fs log schemes

Source: ILO, Exposé VI 3.1--3.5, especially the identification after 3.5 of the
quotient log structure with the invariant direct image
(blueprint: def-per-fs-log-group-action).

The action laws use relative étale test objects, exactly as `EtaleLogHom` does.
Quotient sections are tested on the canonical scheme fibre product. Thus the log
structure is specified by invariant sections, rather than chosen independently.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A group action by log automorphisms. The reversed order in `mul` is the convention
of `CategoryTheory.Aut`: `(g * h).hom = h.hom ≫ g.hom`. The identity condition is
restriction on all étale test morphisms. Source: ILO VI 3.1
(blueprint: def-per-fs-log-group-action). -/
structure FSLogGroupAction (H : Type v) [Group H] (X : FineSaturatedLogScheme.{u}) where
  baseAction : H →* Aut X.scheme
  logMap : H → EtaleLogHom X X
  base_eq : ∀ g : H, (logMap g).base = (baseAction g).hom
  one : ∀ (U V : X.scheme.Etale) (j : V ⟶ U)
    (hj : j.left ≫ U.hom = V.hom ≫ (logMap 1).base),
    (logMap 1).sectionMap U V j.left hj = (X.logStructure.monoidSheaf.obj.map j.op).hom
  mul : ∀ g h : H, (logMap h).CompEq (logMap g) (logMap (g * h))

/-- Tameness uses geometric stabilizers, not the whole group or stabilizers of ordinary
points. Being a unit in the geometric residue field includes characteristic zero.
Source: ILO VI 3.1 (blueprint: def-per-fs-log-group-action). -/
noncomputable def FSLogGroupAction.IsTame {H : Type v} [Group H]
    {X : FineSaturatedLogScheme.{u}} (a : FSLogGroupAction H X) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme),
    IsUnit (Nat.card {g : H // t ≫ (a.baseAction g).hom = t} : Ω)

/-- Freeness on a dense invariant open, tested on geometric points.
Source: ILO VI 3.2 and X 1.1 (blueprint: def-per-fs-log-group-action). -/
def FSLogGroupAction.IsGenericallyFree {H : Type v} [Group H]
    {X : FineSaturatedLogScheme.{u}} (a : FSLogGroupAction H X) : Prop :=
  ∃ U : X.scheme.Opens, Dense (U : Set X.scheme) ∧
    (∀ (g : H) (x : X.scheme), (a.baseAction g).hom x ∈ U ↔ x ∈ U) ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (.of Ω) ⟶ X.scheme) (g : H),
      t default ∈ U → t ≫ (a.baseAction g).hom = t → g = 1

/-- Equivariance of a log morphism is equality of its two composites for every group
member. The common composite is specified by both `CompEq` conditions, so no extra
map is being substituted for either composite. Source: ILO X 1.1
(blueprint: def-per-fs-log-group-action). -/
def FSLogGroupAction.IsEquivariant {H : Type v} [Group H]
    {X Y : FineSaturatedLogScheme.{u}} (a : FSLogGroupAction H X)
    (b : FSLogGroupAction H Y) (f : EtaleLogHom X Y) : Prop :=
  ∀ g : H, ∃ c : EtaleLogHom X Y,
    (a.logMap g).CompEq f c ∧ f.CompEq (b.logMap g) c

/-- The canonical pullback of an étale quotient test object to the source.
Source: ILO VI, paragraph after 3.5 (blueprint: def-per-fs-log-group-action). -/
noncomputable abbrev logQuotientTest {X Y : FineSaturatedLogScheme.{u}}
    (q : EtaleLogHom X Y) (E : Y.scheme.Etale) : X.scheme.Etale :=
  Scheme.Etale.mk (pullback.snd E.hom q.base)

/-- Invariant log sections on a quotient test object. The maps quantified here are
exactly the unique lifts of each group member fixing the first pullback projection.
Source: ILO VI, paragraph after 3.5 (blueprint: def-per-fs-log-group-action). -/
def FSLogGroupAction.IsInvariantLogSection {H : Type v} [Group H]
    {X Y : FineSaturatedLogScheme.{u}} (a : FSLogGroupAction H X)
    (q : EtaleLogHom X Y) (E : Y.scheme.Etale)
    (s : X.logStructure.monoidSheaf.obj.obj (op (logQuotientTest q E))) : Prop :=
  ∀ (g : H) (k : (logQuotientTest q E).left ⟶ (logQuotientTest q E).left)
    (hk : k ≫ (logQuotientTest q E).hom =
      (logQuotientTest q E).hom ≫ (a.logMap g).base),
    k ≫ pullback.fst E.hom q.base = pullback.fst E.hom q.base →
      (a.logMap g).sectionMap (logQuotientTest q E) (logQuotientTest q E) k hk s = s

/-- A categorical geometric scheme quotient, affine locally given by invariant rings,
with precisely the invariant direct-image log structure. Log descent is tested on every
étale quotient object; scheme descent on every affine quotient open. No log regularity,
log smoothness, or very-tame hypothesis is part of this definition.
Source: ILO VI 3.2--3.5 and the paragraph after 3.5
(blueprint: def-per-fs-log-group-action). -/
structure FSLogGroupAction.IsQuotient {H : Type v} [Group H]
    {X Y : FineSaturatedLogScheme.{u}} (a : FSLogGroupAction H X)
    (q : EtaleLogHom X Y) : Prop where
  invariant : ∀ g : H, (a.logMap g).CompEq q q
  topology : Topology.IsQuotientMap q.base
  orbits : ∀ x y : X.scheme, q.base x = q.base y ↔
    ∃ g : H, (a.baseAction g).hom x = y
  categorical : ∀ (Z : Scheme.{u}) (f : X.scheme ⟶ Z),
    (∀ g : H, (a.baseAction g).hom ≫ f = f) →
      ∃! r : Y.scheme ⟶ Z, q.base ≫ r = f
  affine_invariants : ∀ U : Y.scheme.Opens, IsAffineOpen U →
    IsAffineOpen (q.base ⁻¹ᵁ U) ∧ Function.Injective (q.base.app U) ∧
    ∀ s : Γ(X.scheme, q.base ⁻¹ᵁ U),
      (∀ g : H, (a.logMap g).base.app (q.base ⁻¹ᵁ U) s =
        X.scheme.presheaf.map
          (eqToHom (congrArg (fun f : X.scheme ⟶ Y.scheme ↦ f ⁻¹ᵁ U)
            (invariant g).1)).op s) ↔
              ∃ t : Γ(Y.scheme, U), q.base.app U t = s
  log_injective : ∀ E : Y.scheme.Etale,
    Function.Injective (q.sectionMap E (logQuotientTest q E)
      (pullback.fst E.hom q.base) pullback.condition)
  log_invariants : ∀ (E : Y.scheme.Etale)
    (s : X.logStructure.monoidSheaf.obj.obj (op (logQuotientTest q E))),
    a.IsInvariantLogSection q E s ↔
      ∃ t : Y.logStructure.monoidSheaf.obj.obj (op E),
        q.sectionMap E (logQuotientTest q E)
          (pullback.fst E.hom q.base) pullback.condition t = s

end AlgebraicGeometry
