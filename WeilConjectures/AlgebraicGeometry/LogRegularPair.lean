/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.GroupWithZero.Associated
public import Mathlib.GroupTheory.Congruence.Basic
public import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.SetTheory.Cardinal.ENat
public import WeilConjectures.AlgebraicGeometry.Sites.Gm

/-!
# Divisorial fine saturated log regular pairs

Source: Illusie--Laszlo--Orgogozo, Exposé VI, §§1.1--1.4, printed pp. 69--70
(blueprint: def-trf-log-regular-pair).

The divisorial sections and all restrictions are prescribed constructions. Geometric
stalks are formed inside the ring-valued point fibre of the étale structure sheaf.
Charts use the congruence presentation of the pushout of commutative monoids; its
relations identify precisely the chart elements mapping to ring units with those units.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The regular functions becoming units on `W ×[V] U`, with multiplication and
inclusion into the regular functions. Source: ILO VI 1.4 (blueprint: def-trf-log-regular-pair). -/
noncomputable def divisorialSections {V U : Scheme.{u}} (j : U ⟶ V) (W : V.Etale) :
    Submonoid Γ(W.left, ⊤) :=
  (IsUnit.submonoid Γ(pullback W.hom j, ⊤)).comap
    (pullback.fst W.hom j).appTop.hom.toMonoidHom

/-- Canonical restriction of divisorial functions along an étale-site morphism.
Source: ILO VI 1.1, 1.4 (blueprint: def-trf-log-regular-pair). -/
noncomputable def divisorialRestriction {V U : Scheme.{u}} (j : U ⟶ V)
    {W₁ W₂ : V.Etale} (f : W₁ ⟶ W₂) :
    divisorialSections j W₂ →* divisorialSections j W₁ where
  toFun x := ⟨f.left.appTop x.1, by
    let k : pullback W₁.hom j ⟶ pullback W₂.hom j :=
      pullback.lift (pullback.fst W₁.hom j ≫ f.left) (pullback.snd W₁.hom j)
        (by rw [Category.assoc, MorphismProperty.Over.w f, pullback.condition])
    have hk : k ≫ pullback.fst W₂.hom j = pullback.fst W₁.hom j ≫ f.left :=
      pullback.lift_fst _ _ _
    change IsUnit ((pullback.fst W₁.hom j).appTop.hom (f.left.appTop.hom x.1))
    have he := congrArg (fun z : pullback W₁.hom j ⟶ W₂.left ↦ z.appTop.hom x.1) hk
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at he
    exact he ▸ x.2.map k.appTop.hom⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x.1 y.1)

/-- The prescribed multiplicative divisorial presheaf. The sheaf condition is included
in the log-regular-pair predicate below, so no descent proof is hidden in its data.
Source: ILO VI 1.1, 1.4 (blueprint: def-trf-log-regular-pair). -/
noncomputable def divisorialLogPresheaf {V U : Scheme.{u}} (j : U ⟶ V) :
    V.Etaleᵒᵖ ⥤ CommMonCat.{u} where
  obj W := CommMonCat.of (divisorialSections j W.unop)
  map f := CommMonCat.ofHom (divisorialRestriction j f.unop)
  map_id W := by
    ext x
    change (𝟙 W.unop.left : W.unop.left ⟶ W.unop.left).appTop.hom x.1 = x.1
    rw [Scheme.Hom.id_appTop]
    rfl
  map_comp f g := by
    ext x
    change (g.unop.left ≫ f.unop.left).appTop.hom x.1 =
      g.unop.left.appTop.hom (f.unop.left.appTop.hom x.1)
    rw [Scheme.Hom.comp_appTop]
    rfl

/-- Structural inclusion of divisorial functions into the étale structure presheaf.
Naturality forces its restrictions to be exactly pullback of regular functions.
Source: ILO VI 1.1, 1.4 (blueprint: def-trf-log-regular-pair). -/
noncomputable def divisorialStructuralMap {V U : Scheme.{u}} (j : U ⟶ V) :
    divisorialLogPresheaf j ⟶
      V.etaleStructurePresheaf ⋙ forget₂ CommRingCat CommMonCat where
  app W := CommMonCat.ofHom (divisorialSections j W.unop).subtype
  naturality _ _ f := by ext x; rfl

/-- The divisorial sheaf, with exactly the prescribed sections and restrictions.
The argument is only its descent proof; no section or map is chosen from that proof.
Source: ILO VI 1.1, 1.4 (blueprint: def-trf-log-regular-pair). -/
noncomputable def divisorialLogSheaf {V U : Scheme.{u}} (j : U ⟶ V)
    (h : Presheaf.IsSheaf V.smallEtaleTopology (divisorialLogPresheaf j)) :
    Sheaf V.smallEtaleTopology CommMonCat.{u} :=
  ⟨divisorialLogPresheaf j, h⟩

/-- The strict local ring: the ring-valued point fibre, equivalently the colimit over
pointed étale neighbourhoods. Source: ILO VI 1.2 and the blueprint geometric-stalk definition
(blueprint: def-trf-log-regular-pair). -/
noncomputable def strictLocalRing (V : Scheme.{u}) {Ω : Type u} [Field Ω]
    [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ V) : CommRingCat.{u} :=
  ((Scheme.pointSmallEtale t).presheafFiber (A := CommRingCat)).obj V.etaleStructurePresheaf

/-- The canonical ring germ from a pointed étale neighbourhood.
Source: ILO VI 1.2 (blueprint: def-trf-log-regular-pair). -/
noncomputable def strictLocalGerm (V : Scheme.{u}) {Ω : Type u} [Field Ω]
    [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ V) (W : V.Etale)
    (w : (Scheme.pointSmallEtale t).fiber.obj W) : Γ(W.left, ⊤) ⟶ strictLocalRing V t :=
  (Scheme.pointSmallEtale t).toPresheafFiber W w V.etaleStructurePresheaf

/-- The divisorial geometric stalk as a submonoid of the strict local ring. It is the
union of the images of divisorial sections on pointed étale neighbourhoods: the supremum
has that meaning since the neighbourhood category is cofiltered. This avoids any choice
of a strict henselization or any replacement by a Zariski stalk.
Source: ILO VI 1.2, 1.4 (blueprint: def-trf-log-regular-pair). -/
noncomputable def divisorialStalk {V U : Scheme.{u}} (j : U ⟶ V) {Ω : Type u} [Field Ω]
    [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ V) : Submonoid (strictLocalRing V t) :=
  ⨆ (W : V.Etale) (w : (Scheme.pointSmallEtale t).fiber.obj W),
    (divisorialSections j W).map (strictLocalGerm V t W w).hom.toMonoidHom

/-- Canonical germ of a divisorial section in the divisorial geometric stalk.
Source: ILO VI 1.2, 1.4 (blueprint: def-trf-log-regular-pair). -/
noncomputable def divisorialGerm {V U : Scheme.{u}} (j : U ⟶ V) {Ω : Type u} [Field Ω]
    [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ V) (W : V.Etale)
    (w : (Scheme.pointSmallEtale t).fiber.obj W) :
    divisorialSections j W →* divisorialStalk j t where
  toFun f := ⟨(strictLocalGerm V t W w).hom f.1,
    Submonoid.mem_iSup_of_mem W (Submonoid.mem_iSup_of_mem w ⟨f.1, f.2, rfl⟩)⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' f g := Subtype.ext (map_mul _ f.1 g.1)

/-- Fine saturation using the canonical group completion, rather than an embedding of
underlying sets into an unrelated group. Source: ILO VI 1.1, the fine saturated monoids
of Kato (blueprint: def-trf-log-regular-pair). -/
def IsFineSaturatedMonoid (P : Type u) [CommMonoid P] : Prop :=
  (∃ S : Finset P, Submonoid.closure (S : Set P) = ⊤) ∧
    Function.Injective (Algebra.GrothendieckGroup.of (M := P)) ∧
    ∀ (g : Algebra.GrothendieckGroup P) (n : ℕ), 0 < n →
      (∃ p : P, Algebra.GrothendieckGroup.of p = g ^ n) →
        ∃ p : P, Algebra.GrothendieckGroup.of p = g

/-- Inclusion of strict-local units into a log submonoid containing all of them.
Source: ILO VI 1.1 (blueprint: def-trf-log-regular-pair). -/
def divisorialUnitsIn {A : Type u} [CommRing A] (L : Submonoid A)
    (h : IsUnit.submonoid A ≤ L) : Aˣ →* L where
  toFun a := ⟨a.1, h a.isUnit⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The congruence presenting `P ⊕_{α⁻¹(Aˣ)} Aˣ`: identify `(p,1)` with `(1,a)`
exactly when the structural image of `p` is the ring unit `a`.
Source: the chart condition of ILO VI 1.1 (blueprint: def-trf-log-regular-pair). -/
def divisorialChartCongruence {A P : Type u} [CommRing A] [CommMonoid P]
    {L : Submonoid A} (β : P →* L) : Con (P × Aˣ) :=
  conGen (fun x y ↦ ∃ (p : P) (a : Aˣ), (β p).1 = a.1 ∧ x = (p, 1) ∧ y = (1, a))

/-- The chart pushout as a real quotient of the coproduct `P × Aˣ` by the
relations identifying the inverse image of units with those units. Its commutative
monoid structure is Mathlib's structure on congruence quotients.
Source: ILO VI 1.1 (blueprint: def-trf-log-regular-pair). -/
def divisorialChartPushout {A P : Type u} [CommRing A] [CommMonoid P]
    {L : Submonoid A} (β : P →* L) : CommMonCat.{u} :=
  CommMonCat.of (divisorialChartCongruence β).Quotient

/-- A chart generates the log stalk after adjoining ring units, and the kernel of
that product map is exactly the displayed pushout congruence. These two clauses say
that the induced map from the actual pushout quotient is an isomorphism.
Source: ILO VI 1.1 (blueprint: def-trf-log-regular-pair). -/
def IsDivisorialStalkChart {A P : Type u} [CommRing A] [CommMonoid P]
    (L : Submonoid A) (h : IsUnit.submonoid A ≤ L) (β : P →* L) : Prop :=
  Function.Surjective (β.coprod (divisorialUnitsIn L h)) ∧
    Con.ker (β.coprod (divisorialUnitsIn L h)) = divisorialChartCongruence β

/-- Étale-local fine saturated charts: every geometric point admits a pointed étale
neighbourhood and a monoid map into its divisorial sections which is a chart at every
geometric point of that neighbourhood. Each germ map is the prescribed one.
Source: ILO VI 1.1 (blueprint: def-trf-log-regular-pair). -/
def HasDivisorialFineSaturatedCharts {V U : Scheme.{u}} (j : U ⟶ V)
    (h : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ V),
      IsUnit.submonoid (strictLocalRing V t) ≤ divisorialStalk j t) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ V),
    ∃ (W : V.Etale) (_w : (Scheme.pointSmallEtale t).fiber.obj W)
      (P : Type u) (_ : CommMonoid P),
      IsFineSaturatedMonoid P ∧ ∃ β : P →* divisorialSections j W,
        ∀ (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω'] (t' : Spec (.of Ω') ⟶ V)
          (w' : (Scheme.pointSmallEtale t').fiber.obj W),
          IsDivisorialStalkChart (divisorialStalk j t') (h Ω' t')
            ((divisorialGerm j t' W w').comp β)

/-- The characteristic monoid is `Associates L = L / Lˣ`; the log unit condition
identifies `Lˣ` with `Aˣ`. Its group completion is tensored with `ℚ` over `ℤ`, and
its actual vector-space dimension is used (infinite dimensions map to `∞`).
Source: ILO VI 1.1--1.2 (blueprint: def-trf-log-regular-pair). -/
noncomputable def divisorialCharacteristicRank {A : Type u} [CommRing A]
    (L : Submonoid A) : ℕ∞ :=
  Cardinal.toENat (Module.rank ℚ
    (TensorProduct ℤ ℚ (Additive (Algebra.GrothendieckGroup (Associates L)))))

/-- The ideal generated by the structural images of log nonunits in the strict local
ring. Source: ILO VI 1.2 (blueprint: def-trf-log-regular-pair). -/
def divisorialNonunitIdeal {A : Type u} [CommRing A] (L : Submonoid A) : Ideal A :=
  Ideal.span {a : A | ∃ m : L, ¬ IsUnit (m : A) ∧ (m : A) = a}

/-- The divisorial pair `(V,Z)`, with `Z` the closed complement of the dense open
immersion `j`, is fine saturated and log regular. The canonical divisorial presheaf
is a sheaf, its structural map identifies the inverse image of units with ring units,
it admits étale-local
fine saturated charts, its triviality locus is exactly `U`, and every strict-local
stratum quotient is regular with the actual characteristic-group rank dimension formula.
Source: ILO VI 1.1--1.4, printed pp. 69--70 (blueprint: def-trf-log-regular-pair). -/
def IsDivisorialFineSaturatedLogRegularPair
    (V U : Scheme.{u}) (j : U ⟶ V) [IsOpenImmersion j]
    [IsLocallyNoetherian V] (_hU : DenseRange j) : Prop :=
  Presheaf.IsSheaf V.smallEtaleTopology (divisorialLogPresheaf j) ∧
    ∃ h : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ V),
      IsUnit.submonoid (strictLocalRing V t) ≤ divisorialStalk j t,
      HasDivisorialFineSaturatedCharts j h ∧
        ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ V),
          (divisorialStalk j t = IsUnit.submonoid (strictLocalRing V t) ↔
            (Scheme.SpecToEquivOfField Ω V t).1 ∈ Set.range j) ∧
          IsRegularRing (strictLocalRing V t ⧸ divisorialNonunitIdeal (divisorialStalk j t)) ∧
          ringKrullDim (strictLocalRing V t) =
            ringKrullDim (strictLocalRing V t ⧸ divisorialNonunitIdeal (divisorialStalk j t)) +
              (divisorialCharacteristicRank (divisorialStalk j t) : WithBot ℕ∞)

end AlgebraicGeometry
