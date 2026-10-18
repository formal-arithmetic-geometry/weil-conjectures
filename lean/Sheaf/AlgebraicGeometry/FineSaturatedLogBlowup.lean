/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.LogRegularPair
public import Sheaf.AlgebraicGeometry.PointedEtaleStalk

/-!
# Fine saturated log schemes and saturated log blowups

Source: ILO, Exposé VI 1.1--1.2 and 1.4; Exposé VIII 3.3.7--3.3.9
(blueprint: def-trf-fs-log-blowup).

## Main definitions

* `EtaleLogStructure`: a monoid sheaf with the log unit condition.
* `FineSaturatedLogScheme`: a locally Noetherian scheme with fs charts.
* `IsLogRegular`: regular stratum quotients and the characteristic-rank dimension formula.
* `EtaleLogHom`: log morphisms, presented on relative étale test objects.
* `IsSaturatedLogBlowup`: the universal property in the fs category.
* `SaturatedLogBlowupTower`: finite towers, including length zero.

Morphisms are given by their maps on sections on every relative étale test diagram.
This is the adjoint form of `f⁻¹ M → N`; naturality in both test objects is required.
Ideal generation is sheaf-local, implemented by membership at all geometric stalks.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A prelog sheaf and its structural map. Source: ILO VI 1.1
(blueprint: def-trf-fs-log-blowup). -/
structure EtalePrelogStructure (X : Scheme.{u}) where
  monoidSheaf : Sheaf X.smallEtaleTopology CommMonCat.{u}
  alpha : monoidSheaf.obj ⟶ X.etaleStructurePresheaf ⋙ forget₂ CommRingCat CommMonCat

/-- The monoid-valued geometric stalk: the same pointed-neighbourhood colimit as
`Point.sheafFiber`, without its unnecessary all-colimits assumption on `CommMonCat`.
Source: ILO VI 1.1--1.2 (blueprint: def-trf-fs-log-blowup). -/
noncomputable def EtalePrelogStructure.stalk {X : Scheme.{u}} (M : EtalePrelogStructure X)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X) : CommMonCat.{u} :=
  pointedEtaleStalk M.monoidSheaf t

/-- Germ of a section in its actual monoid colimit. Source: ILO VI 1.2
(blueprint: def-trf-fs-log-blowup). -/
noncomputable def EtalePrelogStructure.germ {X : Scheme.{u}} (M : EtalePrelogStructure X)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X)
    (W : X.Etale) (w : (Scheme.pointSmallEtale t).fiber.obj W) :
    M.monoidSheaf.obj.obj (op W) ⟶ M.stalk t :=
  pointedEtaleGerm M.monoidSheaf t W w

/-- Structural map on stalks, induced by the prescribed ring germs. Source: ILO VI 1.2
(blueprint: def-trf-fs-log-blowup). -/
noncomputable def EtalePrelogStructure.stalkAlpha {X : Scheme.{u}}
    (M : EtalePrelogStructure X) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ X) : M.stalk t →* strictLocalRing X t :=
  (colimit.desc
    (pointedEtaleStalkDiagram M.monoidSheaf t)
    { pt := CommMonCat.of (strictLocalRing X t)
      ι :=
        { app := fun W ↦ M.alpha.app (op W.unop.1) ≫
            CommMonCat.ofHom (strictLocalGerm X t W.unop.1 W.unop.2).hom.toMonoidHom
          naturality := by
            intro W V f
            change M.monoidSheaf.obj.map f.unop.val.op ≫
                (M.alpha.app (op V.unop.1) ≫ _) = _ ≫ 𝟙 _
            rw [Category.comp_id, ← Category.assoc, M.alpha.naturality, Category.assoc]
            congr 1
            ext s
            have he := (Scheme.pointSmallEtale t).toPresheafFiber_w
              f.unop.val V.unop.2 X.etaleStructurePresheaf
            rw [f.unop.property] at he
            exact congrArg (fun k : Γ(W.unop.1.left, ⊤) ⟶ strictLocalRing X t ↦ k s) he
        } }).hom

/-- The log unit condition: reflection of units and bijectivity on unit groups.
Together these say exactly that `α⁻¹(Oˣ) → Oˣ` is an isomorphism; checking it on
geometric stalks is equivalent to the sheaf condition on that map.
Source: ILO VI 1.1 (blueprint: def-trf-fs-log-blowup). -/
structure EtaleLogStructure (X : Scheme.{u}) extends EtalePrelogStructure X where
  reflectsUnits : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ X) (m : toEtalePrelogStructure.stalk t),
    IsUnit (toEtalePrelogStructure.stalkAlpha t m) → IsUnit m
  unitsBijective : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ X),
    Function.Bijective (Units.map (toEtalePrelogStructure.stalkAlpha t))

/-- The inverse identification of ring units with log units. Source: ILO VI 1.1
(blueprint: def-trf-fs-log-blowup). -/
noncomputable def EtaleLogStructure.unitsIn {X : Scheme.{u}} (M : EtaleLogStructure X)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X) :
    (strictLocalRing X t)ˣ →* M.toEtalePrelogStructure.stalk t :=
  (Units.coeHom _).comp
    (MulEquiv.ofBijective (Units.map (M.toEtalePrelogStructure.stalkAlpha t))
      (M.unitsBijective Ω t)).symm.toMonoidHom

/-- A stalk chart: its product with units is surjective with exactly the pushout
congruence as kernel. Thus the induced map from the actual quotient pushout is an
isomorphism. The existing divisorial congruence depends only on the ring-valued
chart map, so its range restriction also covers noninjective structural maps.
Source: ILO VI 1.1 (blueprint: def-trf-fs-log-blowup). -/
def EtaleLogStructure.IsStalkChart {X : Scheme.{u}} (M : EtaleLogStructure X)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X)
    {P : Type u} [CommMonoid P] (β : P →* M.toEtalePrelogStructure.stalk t) : Prop :=
  Function.Surjective (β.coprod (M.unitsIn t)) ∧
    Con.ker (β.coprod (M.unitsIn t)) =
      divisorialChartCongruence (A := strictLocalRing X t) (P := P)
        (L := MonoidHom.mrange ((M.toEtalePrelogStructure.stalkAlpha t).comp β))
        ((M.toEtalePrelogStructure.stalkAlpha t).comp β).mrangeRestrict

/-- A chart on an étale neighbourhood, tested at all of its geometric points.
Source: ILO VI 1.1 (blueprint: def-trf-fs-log-blowup). -/
def EtaleLogStructure.IsChart {X : Scheme.{u}} (M : EtaleLogStructure X)
    (W : X.Etale) {P : Type u} [CommMonoid P]
    (β : P →* M.monoidSheaf.obj.obj (op W)) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X)
    (w : (Scheme.pointSmallEtale t).fiber.obj W),
    M.IsStalkChart t ((M.toEtalePrelogStructure.germ t W w).hom.comp β)

/-- Étale-local fs charts. Source: ILO VI 1.1
(blueprint: def-trf-fs-log-blowup). -/
def EtaleLogStructure.IsFineSaturated {X : Scheme.{u}} (M : EtaleLogStructure X) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X),
    ∃ (W : X.Etale) (_w : (Scheme.pointSmallEtale t).fiber.obj W)
      (P : Type u) (_ : CommMonoid P) (β : P →* M.monoidSheaf.obj.obj (op W)),
      IsFineSaturatedMonoid P ∧ M.IsChart W β

/-- Locally Noetherian fs log schemes, as stipulated throughout ILO VI 1.1.
Source: ILO VI 1.1 (blueprint: def-trf-fs-log-blowup). -/
structure FineSaturatedLogScheme where
  scheme : Scheme.{u}
  locallyNoetherian : IsLocallyNoetherian scheme
  logStructure : EtaleLogStructure scheme
  fineSaturated : logStructure.IsFineSaturated

/-- The characteristic monoid is the quotient by log units, identified with ring units
by the log condition. Source: ILO VI 1.1 (blueprint: def-trf-fs-log-blowup). -/
noncomputable def EtaleLogStructure.characteristic {X : Scheme.{u}} (M : EtaleLogStructure X)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X) : CommMonCat.{u} :=
  CommMonCat.of (Associates (M.toEtalePrelogStructure.stalk t))

/-- The triviality locus in the underlying scheme. Source: ILO VI 1.1, 1.4
(blueprint: def-trf-fs-log-blowup). -/
def EtaleLogStructure.trivialityLocus {X : Scheme.{u}} (M : EtaleLogStructure X) : Set X :=
  {x | ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X),
    (Scheme.SpecToEquivOfField Ω X t).1 = x → Subsingleton (M.characteristic t)}

/-- The rank is the actual rational dimension of the characteristic group completion.
Source: ILO VI 1.2 (blueprint: def-trf-fs-log-blowup). -/
noncomputable def EtaleLogStructure.characteristicRank {X : Scheme.{u}}
    (M : EtaleLogStructure X) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ X) : ℕ∞ :=
  Cardinal.toENat (Module.rank ℚ
    (TensorProduct ℤ ℚ (Additive (Algebra.GrothendieckGroup (M.characteristic t)))))

/-- The ring ideal generated by the images of log nonunits. Source: ILO VI 1.2
(blueprint: def-trf-fs-log-blowup). -/
noncomputable def EtaleLogStructure.nonunitIdeal {X : Scheme.{u}} (M : EtaleLogStructure X)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X) :
    Ideal (strictLocalRing X t) :=
  Ideal.span {a | ∃ m : M.toEtalePrelogStructure.stalk t,
    ¬ IsUnit m ∧ M.toEtalePrelogStructure.stalkAlpha t m = a}

/-- Regular stratum quotients and the dimension formula at every geometric point.
Source: ILO VI 1.2 (blueprint: def-trf-fs-log-blowup). -/
def FineSaturatedLogScheme.IsLogRegular (X : FineSaturatedLogScheme.{u}) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme),
    IsRegularRing (strictLocalRing X.scheme t ⧸ X.logStructure.nonunitIdeal t) ∧
      ringKrullDim (strictLocalRing X.scheme t) =
        ringKrullDim (strictLocalRing X.scheme t ⧸ X.logStructure.nonunitIdeal t) +
          (X.logStructure.characteristicRank t : WithBot ℕ∞)

/-- A log morphism, in the relative-test-object presentation of `f⁻¹ M → N`.
The square condition imposes naturality in both étale objects; compatibility is with
pullback of actual regular functions. Source: ILO VI 1.1, VIII 3.3.8--3.3.9
(blueprint: def-trf-fs-log-blowup). -/
structure EtaleLogHom (Y X : FineSaturatedLogScheme.{u}) where
  base : Y.scheme ⟶ X.scheme
  sectionMap : ∀ (W : X.scheme.Etale) (V : Y.scheme.Etale)
    (k : V.left ⟶ W.left) (_hk : k ≫ W.hom = V.hom ≫ base),
    X.logStructure.monoidSheaf.obj.obj (op W) →*
      Y.logStructure.monoidSheaf.obj.obj (op V)
  naturality : ∀ (W₁ W₂ : X.scheme.Etale) (V₁ V₂ : Y.scheme.Etale)
    (a : W₁ ⟶ W₂) (c : V₁ ⟶ V₂) (k₁ : V₁.left ⟶ W₁.left)
    (k₂ : V₂.left ⟶ W₂.left)
    (h₁ : k₁ ≫ W₁.hom = V₁.hom ≫ base) (h₂ : k₂ ≫ W₂.hom = V₂.hom ≫ base),
    c.left ≫ k₂ = k₁ ≫ a.left →
      (Y.logStructure.monoidSheaf.obj.map c.op).hom.comp (sectionMap W₂ V₂ k₂ h₂) =
        (sectionMap W₁ V₁ k₁ h₁).comp (X.logStructure.monoidSheaf.obj.map a.op).hom
  compatibility : ∀ (W : X.scheme.Etale) (V : Y.scheme.Etale)
    (k : V.left ⟶ W.left) (hk : k ≫ W.hom = V.hom ≫ base)
    (s : X.logStructure.monoidSheaf.obj.obj (op W)),
    Y.logStructure.alpha.app (op V) (sectionMap W V k hk s) =
      k.appTop (X.logStructure.alpha.app (op W) s)

/-- Equality with a composite, tested on all relative étale triangles. Every test
map to `X` factors through the pullback of its target along `b`, so these equations
are precisely `b ∘ h = f`, including equality of the underlying scheme maps.
Source: ILO VIII 3.3.8--3.3.9 (blueprint: def-trf-fs-log-blowup). -/
def EtaleLogHom.CompEq {Z Y X : FineSaturatedLogScheme.{u}}
    (h : EtaleLogHom Z Y) (b : EtaleLogHom Y X) (f : EtaleLogHom Z X) : Prop :=
  h.base ≫ b.base = f.base ∧
    ∀ (W : X.scheme.Etale) (V : Y.scheme.Etale) (T : Z.scheme.Etale)
      (k : V.left ⟶ W.left) (l : T.left ⟶ V.left) (m : T.left ⟶ W.left)
      (hk : k ≫ W.hom = V.hom ≫ b.base)
      (hl : l ≫ V.hom = T.hom ≫ h.base) (hm : m ≫ W.hom = T.hom ≫ f.base),
      l ≫ k = m → (h.sectionMap V T l hl).comp (b.sectionMap W V k hk) =
        f.sectionMap W T m hm

/-- A family of subsets of log sections; the subsheaf and ideal axioms are expressed
by `IsIdeal`. Source: ILO VIII 3.3.7 (blueprint: def-trf-fs-log-blowup). -/
def EtaleLogStructure.IdealFamily {X : Scheme.{u}} (M : EtaleLogStructure X) :=
  ∀ W : X.Etale, Set (M.monoidSheaf.obj.obj (op W))

/-- Germs belonging to a family of log subsets. Source: ILO VIII 3.3.7
(blueprint: def-trf-fs-log-blowup). -/
def EtaleLogStructure.idealStalk {X : Scheme.{u}} (M : EtaleLogStructure X)
    (I : M.IdealFamily) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ X) : Set (M.toEtalePrelogStructure.stalk t) :=
  {m | ∃ (W : X.Etale) (w : (Scheme.pointSmallEtale t).fiber.obj W)
    (s : M.monoidSheaf.obj.obj (op W)), s ∈ I W ∧
      M.toEtalePrelogStructure.germ t W w s = m}

/-- A subsheaf stable under multiplication by all log sections. Local membership is
checked at every geometric point, making this a subsheaf rather than a subpresheaf.
Source: ILO VIII 3.3.7 (blueprint: def-trf-fs-log-blowup). -/
def EtaleLogStructure.IsIdeal {X : Scheme.{u}} (M : EtaleLogStructure X)
    (I : M.IdealFamily) : Prop :=
  (∀ (W : X.Etale) (a b : M.monoidSheaf.obj.obj (op W)), a ∈ I W → a * b ∈ I W) ∧
    (∀ (V W : X.Etale) (f : V ⟶ W) (s : M.monoidSheaf.obj.obj (op W)),
      s ∈ I W → M.monoidSheaf.obj.map f.op s ∈ I V) ∧
    ∀ (W : X.Etale) (s : M.monoidSheaf.obj.obj (op W)),
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X)
        (w : (Scheme.pointSmallEtale t).fiber.obj W),
        M.toEtalePrelogStructure.germ t W w s ∈ M.idealStalk I t) → s ∈ I W

/-- Nonempty coherent log ideals: étale locally a nonempty finite set in an fs chart
generates the ideal. The equality is tested on every geometric stalk in the chart.
Source: ILO VIII 3.3.7 (blueprint: def-trf-fs-log-blowup). -/
def EtaleLogStructure.IsNonemptyCoherentIdeal {X : Scheme.{u}} (M : EtaleLogStructure X)
    (I : M.IdealFamily) : Prop :=
  M.IsIdeal I ∧ ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X),
    ∃ (W : X.Etale) (_w : (Scheme.pointSmallEtale t).fiber.obj W)
      (P : Type u) (_ : CommMonoid P) (β : P →* M.monoidSheaf.obj.obj (op W))
      (E : Finset P), IsFineSaturatedMonoid P ∧ M.IsChart W β ∧ E.Nonempty ∧
        ∀ (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω'] (t' : Spec (.of Ω') ⟶ X)
          (w' : (Scheme.pointSmallEtale t').fiber.obj W),
          M.idealStalk I t' = {m | ∃ p ∈ E, ∃ n : M.toEtalePrelogStructure.stalk t',
            M.toEtalePrelogStructure.germ t' W w' (β p) * n = m}

/-- The ideal of a target log stalk generated by images of source ideal sections on
all relative pointed étale neighbourhoods. Source: ILO VIII 3.3.7--3.3.9
(blueprint: def-trf-fs-log-blowup). -/
def EtaleLogHom.pulledIdealStalk {Y X : FineSaturatedLogScheme.{u}} (f : EtaleLogHom Y X)
    (I : X.logStructure.IdealFamily) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ Y.scheme) : Set (Y.logStructure.toEtalePrelogStructure.stalk t) :=
  {m | ∃ (W : X.scheme.Etale) (V : Y.scheme.Etale)
    (v : (Scheme.pointSmallEtale t).fiber.obj V) (k : V.left ⟶ W.left)
    (hk : k ≫ W.hom = V.hom ≫ f.base)
    (s : X.logStructure.monoidSheaf.obj.obj (op W))
    (n : Y.logStructure.toEtalePrelogStructure.stalk t), s ∈ I W ∧
      Y.logStructure.toEtalePrelogStructure.germ t V v (f.sectionMap W V k hk s) * n = m}

/-- Pullback ideal, with sheaf-local generation rather than only sectionwise generation.
Source: ILO VIII 3.3.7--3.3.9 (blueprint: def-trf-fs-log-blowup). -/
def EtaleLogHom.pullbackIdeal {Y X : FineSaturatedLogScheme.{u}} (f : EtaleLogHom Y X)
    (I : X.logStructure.IdealFamily) : Y.logStructure.IdealFamily :=
  fun W ↦ {s | ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Y.scheme)
    (w : (Scheme.pointSmallEtale t).fiber.obj W),
    Y.logStructure.toEtalePrelogStructure.germ t W w s ∈ f.pulledIdealStalk I t}

/-- Invertibility means étale-local generation by one log section, with no nonzero
condition on its ring image. Source: ILO VIII 3.3.8
(blueprint: def-trf-fs-log-blowup). -/
def EtaleLogStructure.IsInvertibleIdeal {X : Scheme.{u}} (M : EtaleLogStructure X)
    (I : M.IdealFamily) : Prop :=
  M.IsIdeal I ∧ ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X),
    ∃ (W : X.Etale) (_w : (Scheme.pointSmallEtale t).fiber.obj W)
      (a : M.monoidSheaf.obj.obj (op W)),
      ∀ (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω'] (t' : Spec (.of Ω') ⟶ X)
        (w' : (Scheme.pointSmallEtale t').fiber.obj W),
        M.idealStalk I t' = {m | ∃ n : M.toEtalePrelogStructure.stalk t',
          M.toEtalePrelogStructure.germ t' W w' a * n = m}

/-- The saturated log blowup universal property in the fs category. No existence is
asserted or chosen. Source: ILO VIII 3.3.8--3.3.9
(blueprint: def-trf-fs-log-blowup). -/
def IsSaturatedLogBlowup {X X' : FineSaturatedLogScheme.{u}}
    (b : EtaleLogHom X' X) (I : X.logStructure.IdealFamily) : Prop :=
  X.logStructure.IsNonemptyCoherentIdeal I ∧
    X'.logStructure.IsInvertibleIdeal (b.pullbackIdeal I) ∧
      ∀ (Y : FineSaturatedLogScheme.{u}) (f : EtaleLogHom Y X),
        Y.logStructure.IsInvertibleIdeal (f.pullbackIdeal I) →
          ∃! h : EtaleLogHom Y X', h.CompEq b f

/-- A finite sequence of saturated log blowups, with its centers and universal
properties. `length = 0` has one level and no arrows or centers.
Source: ILO VIII 3.3.9 (blueprint: def-trf-fs-log-blowup). -/
structure SaturatedLogBlowupTower where
  length : ℕ
  level : Fin (length + 1) → FineSaturatedLogScheme.{u}
  arrow : ∀ i : Fin length, EtaleLogHom (level i.succ) (level i.castSucc)
  center : ∀ i : Fin length, (level i.castSucc).logStructure.IdealFamily
  isBlowup : ∀ i : Fin length, IsSaturatedLogBlowup (arrow i) (center i)

end AlgebraicGeometry
