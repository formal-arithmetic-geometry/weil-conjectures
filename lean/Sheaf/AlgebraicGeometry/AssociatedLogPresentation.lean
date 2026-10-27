/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Associated-log quotient presheaf and presentation

Source: ILO, Exposé VI 1.1, printed p. 69, with its reference to Kato (1988), §1;
Stacks, Tags 00YR, 00WK, 03PQ, 03PT and 03PU
(blueprint: lem-trf-associated-log-universal-stalks).
(blueprint: def-per-associated-log-presentation).

The presheaf below uses the existing `divisorialChartPushout` for an arbitrary
ring-valued monoid map, by its range restriction. The existence theorem specifies
its associated log structure by the sheafification universal property, its value
on pairs, and all comparison normalizations. No log structure is chosen from an
unconstrained existence assertion.
-/

@[expose] public section

universe u v

set_option linter.style.longLine false
set_option linter.checkUnivs false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Restriction of a global prelog chart to an étale object. Source: ILO VI 1.1
(blueprint: lem-trf-associated-log-universal-stalks). -/
noncomputable def associatedLogBeta {X : Scheme.{max u v}} {R : Type v} [CommMonoid R]
    (β : R →* Γ(X, ⊤)) (W : X.Etale) : R →* Γ(W.left, ⊤) :=
  W.hom.appTop.hom.toMonoidHom.comp β

/-- The canonical monoid isomorphism `ULift R → R` (the down map), transporting the
coefficient monoid `R : Type v` into the common site universe `max u v` required by the
log-structure interface. Source: ILO VI 1.1, the monoid `P` of a chart, here in the
universe of the étale site (blueprint: lem-trf-associated-log-universal-stalks). -/
noncomputable def associatedLogDown {R : Type v} [CommMonoid R] : ULift.{u, v} R →* R where
  toFun := ULift.down
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The restricted prelog map `β_U` precomposed with the canonical down map from
`ULift R`. Source: ILO VI 1.1 (blueprint: lem-trf-associated-log-universal-stalks). -/
noncomputable def associatedLogBetaLift {X : Scheme.{max u v}} {R : Type v} [CommMonoid R]
    (β : R →* Γ(X, ⊤)) (W : X.Etale) : ULift.{u, v} R →* Γ(W.left, ⊤) :=
  (associatedLogBeta β W).comp
    (associatedLogDown)

/-- The global prelog map `β` on the transported coefficient monoid `ULift R`, the
target of the compatibility condition `α_K ∘ v = β`. Source: ILO VI 1.1
(blueprint: lem-trf-associated-log-universal-stalks). -/
noncomputable def associatedLogDownChart {X : Scheme.{max u v}} {R : Type v}
    [CommMonoid R] (β : R →* Γ(X, ⊤)) : ULift.{u, v} R →* Γ(X, ⊤) :=
  β.comp associatedLogDown

/-- Pullback on pairs, keeping the chart element and restricting the unit.
Source: ILO VI 1.1 (blueprint: lem-trf-associated-log-universal-stalks). -/
noncomputable def associatedLogPairRestriction {X : Scheme.{max u v}} (R : Type v)
    [CommMonoid R] {V W : X.Etale} (f : V ⟶ W) :
    ULift.{u, v} R × Γ(W.left, ⊤)ˣ →* ULift.{u, v} R × Γ(V.left, ⊤)ˣ :=
  (MonoidHom.id (ULift.{u, v} R)).prodMap (Units.map f.left.appTop.hom.toMonoidHom)

/-- Restriction respects the generated pushout congruence. Source: ILO VI 1.1.
Proof: each generator identifies a chart element with its unit image. Pullback
preserves that equality and units, and `f` commutes with the maps to `X`, so the
image is a generator of the target congruence. Closure under equivalence and
multiplication gives the kernel inclusion, as in Step 1 of the node's proof.
(blueprint: lem-trf-associated-log-universal-stalks). -/
theorem associatedLogRestriction_wellDefined {X : Scheme.{max u v}} {R : Type v}
    [CommMonoid R] (β : R →* Γ(X, ⊤)) {V W : X.Etale} (f : V ⟶ W) :
    divisorialChartCongruence (P := ULift.{u, v} R) (associatedLogBetaLift β W).mrangeRestrict ≤
      Con.ker (((divisorialChartCongruence (P := ULift.{u, v} R)
        (associatedLogBetaLift β V).mrangeRestrict).mk').comp
          (associatedLogPairRestriction R f)) := by
  apply Con.conGen_le.mpr
  rintro x y ⟨r, a, ha, rfl, rfl⟩
  change (divisorialChartCongruence (associatedLogBetaLift β V).mrangeRestrict).mk'
      (r, Units.map f.left.appTop.hom.toMonoidHom 1) =
    (divisorialChartCongruence (associatedLogBetaLift β V).mrangeRestrict).mk'
      (1, Units.map f.left.appTop.hom.toMonoidHom a)
  rw [map_one]
  apply (Con.eq _).mpr
  apply Con.le_conGen
  refine ⟨r, Units.map f.left.appTop.hom.toMonoidHom a, ?_, rfl, rfl⟩
  change associatedLogBetaLift β V r = f.left.appTop.hom a.val
  rw [← ha]
  change V.hom.appTop.hom (β r.down) =
    f.left.appTop.hom (W.hom.appTop.hom (β r.down))
  have hw : f.left ≫ W.hom = V.hom := f.w
  rw [← hw, Scheme.Hom.comp_appTop]
  rfl

/-- The induced restriction of the actual quotient pushouts. Source: ILO VI 1.1
(blueprint: lem-trf-associated-log-universal-stalks). -/
noncomputable def associatedLogRestriction {X : Scheme.{max u v}} {R : Type v}
    [CommMonoid R] (β : R →* Γ(X, ⊤)) {V W : X.Etale} (f : V ⟶ W) :
    divisorialChartPushout (P := ULift.{u, v} R) (associatedLogBetaLift β W).mrangeRestrict ⟶
      divisorialChartPushout (P := ULift.{u, v} R) (associatedLogBetaLift β V).mrangeRestrict :=
  CommMonCat.ofHom ((divisorialChartCongruence
    (associatedLogBetaLift β W).mrangeRestrict).lift
      (((divisorialChartCongruence (P := ULift.{u, v} R)
        (associatedLogBetaLift β V).mrangeRestrict).mk').comp
          (associatedLogPairRestriction R f))
        (associatedLogRestriction_wellDefined β f))

/-- Identity restriction on the quotient. Source: ILO VI 1.1.
Proof (node Step 1): every quotient class has a pair representative and identity
pullback fixes that representative.
(blueprint: lem-trf-associated-log-universal-stalks). -/
theorem associatedLogRestriction_id {X : Scheme.{max u v}} {R : Type v} [CommMonoid R]
    (β : R →* Γ(X, ⊤)) (W : X.Etale) :
    associatedLogRestriction β (𝟙 W) = 𝟙 _ := by
  ext z
  induction z using Con.induction_on with
  | H p =>
    rcases p with ⟨r, a⟩
    change (divisorialChartCongruence (associatedLogBetaLift β W).mrangeRestrict).mk'
        (r, Units.map (𝟙 W : W ⟶ W).left.appTop.hom.toMonoidHom a) =
      (divisorialChartCongruence (associatedLogBetaLift β W).mrangeRestrict).mk' (r, a)
    apply congrArg
      (divisorialChartCongruence (associatedLogBetaLift β W).mrangeRestrict).mk'
    apply Prod.ext rfl
    apply Units.ext
    change (𝟙 W.left : W.left ⟶ W.left).appTop.hom a.val = a.val
    simp

/-- Composition of restrictions on the quotient. Source: ILO VI 1.1.
Proof (node Step 1): on a representative `(r,a)` this is functoriality of pullback
of regular functions, and hence of their units. Pair representatives exhaust the quotient.
(blueprint: lem-trf-associated-log-universal-stalks). -/
theorem associatedLogRestriction_comp {X : Scheme.{max u v}} {R : Type v} [CommMonoid R]
    (β : R →* Γ(X, ⊤)) {U V W : X.Etale} (f : U ⟶ V) (g : V ⟶ W) :
    associatedLogRestriction β (f ≫ g) =
      associatedLogRestriction β g ≫ associatedLogRestriction β f := by
  ext z
  induction z using Con.induction_on with
  | H p =>
    rcases p with ⟨r, a⟩
    change (divisorialChartCongruence (associatedLogBetaLift β U).mrangeRestrict).mk'
        (r, Units.map (f ≫ g).left.appTop.hom.toMonoidHom a) =
      (divisorialChartCongruence (associatedLogBetaLift β U).mrangeRestrict).mk'
        (r, Units.map f.left.appTop.hom.toMonoidHom
          (Units.map g.left.appTop.hom.toMonoidHom a))
    rfl

/-- The presheaf `U ↦ R ⊕_{β_U⁻¹(B_Uˣ)} B_Uˣ`, with its prescribed restrictions.
Source: ILO VI 1.1 (blueprint: lem-trf-associated-log-universal-stalks). -/
noncomputable def associatedLogPresheaf {X : Scheme.{max u v}} {R : Type v} [CommMonoid R]
    (β : R →* Γ(X, ⊤)) : X.Etaleᵒᵖ ⥤ CommMonCat.{max u v} where
  obj W :=
    divisorialChartPushout (P := ULift.{u, v} R)
      (associatedLogBetaLift β W.unop).mrangeRestrict
  map f := associatedLogRestriction β f.unop
  map_id W := associatedLogRestriction_id β W.unop
  map_comp f g := associatedLogRestriction_comp β g.unop f.unop

/-- The canonical chart map obtained by sheafifying `[r,1]` at the terminal object.
Source: ILO VI 1.1 (blueprint: lem-trf-associated-log-universal-stalks). -/
noncomputable def associatedLogIota {X : Scheme.{max u v}} {R : Type v} [CommMonoid R]
    (β : R →* Γ(X, ⊤)) (L : EtaleLogStructure.{max u v} X)
    (η : associatedLogPresheaf β ⟶ L.monoidSheaf.obj) :
    ULift.{u, v} R →* L.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 X))) :=
  ((η.app (op (Scheme.Etale.mk (𝟙 X)))).hom.comp
    (divisorialChartCongruence (P := ULift.{u, v} R)
      (associatedLogBetaLift β (Scheme.Etale.mk (𝟙 X))).mrangeRestrict).mk').comp
    (MonoidHom.inl (ULift.{u, v} R) Γ((Scheme.Etale.mk (𝟙 X)).left, ⊤)ˣ)

/-- A log morphism over the identity is a monoid-sheaf map commuting with the
structure maps. Fixing the canonical unit copy follows from the log axiom and is
not an additional hypothesis. Source: ILO VI 1.1
(blueprint: lem-trf-associated-log-universal-stalks). -/
def EtaleLogStructure.HomOverIdentity {X : Scheme.{max u v}}
    (L K : EtaleLogStructure.{max u v} X) :=
  {f : L.monoidSheaf ⟶ K.monoidSheaf // f.hom ≫ K.alpha = L.alpha}

/-- Composition of a global chart with a log morphism over the identity.
Source: ILO VI 1.1 (blueprint: lem-trf-associated-log-universal-stalks). -/
def EtaleLogStructure.composeGlobalChart {X : Scheme.{max u v}} {R : Type v} [CommMonoid R]
    {L K : EtaleLogStructure.{max u v} X}
    (c : ULift.{u, v} R →* L.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 X))))
    (f : EtaleLogStructure.HomOverIdentity.{max u v} L K) :
    ULift.{u, v} R →* K.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 X))) :=
  (f.val.hom.app (op (Scheme.Etale.mk (𝟙 X)))).hom.comp c

/-- The specialized associated-log presentation: the universal monoid sheafification
and the structural formula `α(η([r,a])) = β_U(r)a`. This uses exactly the universal
property of `presheafToSheaf`, without requiring a chosen sheafification functor
on all monoid presheaves. Source: ILO VI 1.1; Stacks Tag 00YR
(blueprint: lem-trf-associated-log-universal-stalks). -/
def IsAssociatedLogPresentation {X : Scheme.{max u v}} {R : Type v} [CommMonoid R]
    (β : R →* Γ(X, ⊤)) (L : EtaleLogStructure.{max u v} X)
    (η : associatedLogPresheaf β ⟶ L.monoidSheaf.obj) : Prop :=
  (∀ H : Sheaf X.smallEtaleTopology CommMonCat.{max u v},
    Function.Bijective (fun f : L.monoidSheaf ⟶ H ↦ η ≫ f.hom)) ∧
  ∀ (W : X.Etale) (r : R) (a : Γ(W.left, ⊤)ˣ),
    L.alpha.app (op W)
      (η.app (op W) ((divisorialChartCongruence (P := ULift.{u, v} R)
        (associatedLogBetaLift β W).mrangeRestrict).mk' (ULift.up r, a))) =
          associatedLogBetaLift β W (ULift.up r) * a.val

/-- The global prelog map at a geometric point, formed with the actual ring germ.
Source: ILO VI 1.1--1.2 (blueprint: lem-trf-associated-log-universal-stalks). -/
noncomputable def associatedLogStalkBeta {X : Scheme.{max u v}} {R : Type v} [CommMonoid R]
    (β : R →* Γ(X, ⊤)) {Ω : Type (max u v)} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ X) : ULift.{u, v} R →* strictLocalRing X t :=
  (strictLocalGerm X t (Scheme.Etale.mk (𝟙 X)) (Over.homMk t)).hom.toMonoidHom.comp
    (β.comp associatedLogDown)

/-- The global charts `v : R → N(X)` compatible with `β`, i.e. with `α_N ∘ v = β`:
the target set of the universal-property bijection. Source: ILO VI 1.1
(blueprint: lem-trf-associated-log-universal-stalks). -/
def associatedLogCompatibleRange {X : Scheme.{max u v}} {R : Type v} [CommMonoid R]
    (N : EtaleLogStructure.{max u v} X) (β : R →* Γ(X, ⊤)) :
    Set (ULift.{u, v} R →* N.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 X)))) :=
  {v | (N.alpha.app (op (Scheme.Etale.mk (𝟙 X)))).hom.comp v = associatedLogDownChart β}

end AlgebraicGeometry
