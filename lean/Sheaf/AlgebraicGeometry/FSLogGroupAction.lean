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
The raw `InvariantDirectImage` interface does not assume fs on the quotient; it
can therefore be used to establish fs by constructing charts.

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

/-- Pullback of an étale test object of a scheme quotient.
Source: ILO VI after 3.5 (blueprint: def-per-fs-log-group-action). -/
noncomputable abbrev logInvariantTest {X Y : Scheme.{u}} (f : X ⟶ Y) (E : Y.Etale) : X.Etale :=
  Scheme.Etale.mk (pullback.snd E.hom f)

/-- The invariant submonoid on a quotient test object. The equations use all
lifts of each prescribed group automorphism fixing the quotient projection.
Source: ILO VI after 3.5 (blueprint: def-per-fs-log-group-action). -/
def FSLogGroupAction.invariantLogSections {X : FineSaturatedLogScheme.{u}}
    {H : Type v} [Group H] (action : FSLogGroupAction H X)
    {Y : Scheme.{u}} (f : X.scheme ⟶ Y) (E : Y.Etale) :
    Submonoid (X.logStructure.monoidSheaf.obj.obj (op (logInvariantTest f E))) where
  carrier := {s | ∀ (h : H) (k : (logInvariantTest f E).left ⟶
      (logInvariantTest f E).left)
      (hk : k ≫ (logInvariantTest f E).hom =
        (logInvariantTest f E).hom ≫ (action.logMap h).base),
      k ≫ pullback.fst E.hom f = pullback.fst E.hom f →
      (action.logMap h).sectionMap _ _ k hk s = s}
  one_mem' := by intro h k hk he; exact map_one _
  mul_mem' := by
    intro s t hs ht h k hk he
    rw [map_mul, hs h k hk he, ht h k hk he]

/-- The canonical pullback of an étale quotient test object to the source.
Source: ILO VI, paragraph after 3.5 (blueprint: def-per-fs-log-group-action). -/
noncomputable abbrev logQuotientTest {X Y : FineSaturatedLogScheme.{u}}
    (q : EtaleLogHom X Y) (E : Y.scheme.Etale) : X.scheme.Etale :=
  logInvariantTest q.base E

/-- Invariant log sections on a quotient test object. The maps quantified here are
exactly the unique lifts of each group member fixing the first pullback projection.
Source: ILO VI, paragraph after 3.5 (blueprint: def-per-fs-log-group-action). -/
def FSLogGroupAction.IsInvariantLogSection {H : Type v} [Group H]
    {X Y : FineSaturatedLogScheme.{u}} (a : FSLogGroupAction H X)
    (q : EtaleLogHom X Y) (E : Y.scheme.Etale)
    (s : X.logStructure.monoidSheaf.obj.obj (op (logQuotientTest q E))) : Prop :=
  s ∈ a.invariantLogSections q.base E

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

/-- A presentation of the actual invariant direct-image log sheaf, without
assuming that this sheaf is fs. `pullbackMap` is a sheaf map on relative tests;
its image is exactly the invariant submonoid, and its structural map is the
prescribed pullback of regular functions. This characterizes the log sheaf
uniquely, and does not choose it from an existence theorem.
Source: ILO VI after 3.5 and 3.7(b)
(blueprint: def-per-fs-log-group-action). -/
structure FSLogGroupAction.InvariantDirectImage {X : FineSaturatedLogScheme.{u}}
    {H : Type v} [Group H] (action : FSLogGroupAction H X)
    {Y : Scheme.{u}} (f : X.scheme ⟶ Y) (N : EtaleLogStructure Y) where
  pullbackMap : ∀ E : Y.Etale, N.monoidSheaf.obj.obj (op E) →*
    X.logStructure.monoidSheaf.obj.obj (op (logInvariantTest f E))
  injective : ∀ E : Y.Etale, Function.Injective (pullbackMap E)
  image : ∀ (E : Y.Etale)
    (s : X.logStructure.monoidSheaf.obj.obj (op (logInvariantTest f E))),
    s ∈ FSLogGroupAction.invariantLogSections action f E ↔ ∃ t, pullbackMap E t = s
  naturality : ∀ (E F : Y.Etale) (j : E ⟶ F)
    (k : logInvariantTest f E ⟶ logInvariantTest f F),
    k.left ≫ pullback.fst F.hom f = pullback.fst E.hom f ≫ j.left →
    (X.logStructure.monoidSheaf.obj.map k.op).hom.comp (pullbackMap F) =
      (pullbackMap E).comp (N.monoidSheaf.obj.map j.op).hom
  compatibility : ∀ (E : Y.Etale) (s : N.monoidSheaf.obj.obj (op E)),
    X.logStructure.alpha.app (op (logInvariantTest f E)) (pullbackMap E s) =
      (pullback.fst E.hom f).appTop (N.alpha.app (op E) s)

end AlgebraicGeometry
