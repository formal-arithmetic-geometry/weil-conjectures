/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingMap

/-!
# Finite coefficients and small continuous-function carriers

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-scalar-six/_section.md, coefficient list (1)--(3), and the encoding bridge
in proof steps 1--6 of the DAG node.
(blueprint: lem-sfb-finite-coefficient-small-carrier-comparison).

The two endpoints are the actual `cartesianFinitePointRing` and
`Profinite.continuousMapRingObj`. The comparison postcomposes by a ring equivalence;
canonical universe lifts let the recorded postcomposition API handle both endpoints.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory Opposite
open AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Bundle the actual finite-coefficient sheaf, with its fixed bottom topology and
canonical commutative ring-object structure. This introduces no new coefficient model.
Source: CartesianCoefficients.lean, `cartesianFinitePointRing`, and node statement D_u(A).
(blueprint: lem-sfb-finite-coefficient-small-carrier-comparison). -/
abbrev finiteCoefficientComparisonSource (A : Type u) [CommRing A] :
    CommMon (Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}) := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := discreteTopology_bot A
  exact CommMon.mk (cartesianFinitePointRing A)

/-- Bundle the recorded continuous-function sheaf and its canonical commutative structure.
Source: ContinuousMapCondensedRing.lean and node statement C_u(T).
(blueprint: lem-sfb-finite-coefficient-small-carrier-comparison). -/
abbrev finiteCoefficientComparisonTarget (T : Type) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] :
    CommMon (Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}) :=
  CommMon.mk (Profinite.continuousMapRingObj T)

/-- Postcompose finite-coefficient sections by the carrier ring equivalence.
The existing universe-polymorphic postcomposition first lands in `ULift T`; lowering
that auxiliary carrier gives sections in the actual small-carrier endpoint. The
forgetful `sheafCompose` and its `IsMonHom` instance retain multiplication and unit.
Source: node proof step 3, using def-sfb-continuous-map-condensed-ring-map.
(blueprint: lem-sfb-finite-coefficient-small-carrier-comparison). -/
def finiteCoefficientComparisonHom (A : Type u) [CommRing A]
    (T : Type) [CommRing T] [TopologicalSpace T] [DiscreteTopology T] (r : A ≃+* T) :
    finiteCoefficientComparisonSource A ⟶ finiteCoefficientComparisonTarget T := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := discreteTopology_bot A
  let rUp : A →+* ULift.{u} T := ULift.ringEquiv.symm.toRingHom.comp r.toRingHom
  let k := Profinite.continuousMapRingSheafMapOfUniverse.{u, u} rUp
    continuous_of_discreteTopology
  let g : Profinite.continuousCoefficientRingSheaf A ⟶
      Profinite.continuousMapRingSheaf T :=
    ⟨{ app := fun S ↦ RingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
          ((ULift.ringEquiv.toRingHom.compLeftContinuous _ continuous_uliftDown).comp
            (ULift.ringEquiv.toRingHom.comp (k.hom.app S).hom)))
       naturality := fun _ _ _ ↦ rfl }⟩
  let m : cartesianFinitePointRing A ⟶ Profinite.continuousMapRingObj T :=
    (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map g
  letI : IsMonHom m := Sheaf.isMonHom_sheafCompose_map
    (coherentTopology Profinite.{u}) g
  exact CommMon.homMk (Mon.Hom.mk m)

/-- Postcompose small-carrier sections by the inverse carrier ring equivalence.
Lift the auxiliary coefficient carrier before applying the recorded postcomposition
map, then forget to abelian sheaves with its canonical `IsMonHom` compatibility.
Source: node proof step 3, using def-sfb-continuous-map-condensed-ring-map.
(blueprint: lem-sfb-finite-coefficient-small-carrier-comparison). -/
def finiteCoefficientComparisonInv (A : Type u) [CommRing A]
    (T : Type) [CommRing T] [TopologicalSpace T] [DiscreteTopology T] (r : A ≃+* T) :
    finiteCoefficientComparisonTarget T ⟶ finiteCoefficientComparisonSource A := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := discreteTopology_bot A
  let rDown : ULift.{u} T →+* A := r.symm.toRingHom.comp ULift.ringEquiv.toRingHom
  let k := Profinite.continuousMapRingSheafMapOfUniverse.{u, u} rDown
    continuous_of_discreteTopology
  let g : Profinite.continuousMapRingSheaf T ⟶
      Profinite.continuousCoefficientRingSheaf A :=
    ⟨{ app := fun S ↦ RingCat.ofHom ((k.hom.app S).hom.comp
          (ULift.ringEquiv.symm.toRingHom.comp
            (((ULift.ringEquiv : ULift.{u} T ≃+* T).symm.toRingHom.compLeftContinuous _
              continuous_uliftUp).comp
              ULift.ringEquiv.toRingHom)))
       naturality := fun _ _ _ ↦ rfl }⟩
  let m : Profinite.continuousMapRingObj T ⟶ cartesianFinitePointRing A :=
    (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map g
  letI : IsMonHom m := Sheaf.isMonHom_sheafCompose_map
    (coherentTopology Profinite.{u}) g
  exact CommMon.homMk (Mon.Hom.mk m)

/-- The recorded postcomposition map on the actual small continuous-function endpoints,
bundled as a morphism of commutative condensed ring objects.
Source: node proof steps 5--6 and def-sfb-continuous-map-condensed-ring-map.
(blueprint: lem-sfb-finite-coefficient-small-carrier-comparison). -/
def finiteCoefficientComparisonMap {T T' : Type} [CommRing T] [CommRing T']
    [TopologicalSpace T] [IsTopologicalRing T]
    [TopologicalSpace T'] [IsTopologicalRing T']
    (f : T →+* T') (hf : Continuous f) :
    finiteCoefficientComparisonTarget.{u} T ⟶ finiteCoefficientComparisonTarget T' := by
  let m : Profinite.continuousMapRingObj T ⟶ Profinite.continuousMapRingObj T' :=
    Profinite.continuousMapRingObjMapOfUniverse.{u, 0} f hf
  letI : IsMonHom m := Sheaf.isMonHom_sheafCompose_map
    (coherentTopology Profinite.{u}) (Profinite.continuousMapRingSheafMapOfUniverse.{u, 0} f hf)
  exact CommMon.homMk (Mon.Hom.mk m)

/-- Postcomposition by r composed with a continuous map into the finite carrier.
The finite target A has the fixed bottom topology, with no topology assumption on T.
Source: node statement mixed-source clause and proof step 6.
(blueprint: lem-sfb-finite-coefficient-small-carrier-comparison). -/
def finiteCoefficientComparisonMixedMap (A : Type u) [CommRing A]
    (A₀ : Type) [CommRing A₀] [TopologicalSpace A₀] [DiscreteTopology A₀]
    (r : A ≃+* A₀) {T : Type} [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    (ψ : T →+* A) (hψ : @Continuous T A _ ⊥ ψ) :
    finiteCoefficientComparisonTarget.{u} T ⟶ finiteCoefficientComparisonTarget A₀ := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := discreteTopology_bot A
  have hr : Continuous (r : A → A₀) := continuous_of_discreteTopology
  exact finiteCoefficientComparisonMap (r.toRingHom.comp ψ) (hr.comp hψ)

/-- The forward and inverse postcomposition maps compose to the identity on D_u(A).
Source: node proof step 4. On a section s, the composite has value
r.symm (r (s x)) = s x. Extensionality of functions, continuous maps, lifted sections,
sheaf maps and bundled ring-object maps proves the identity, including empty S.
(blueprint: lem-sfb-finite-coefficient-small-carrier-comparison). -/
theorem finiteCoefficientComparison_hom_inv_id (A : Type u) [CommRing A]
    (A₀ : Type) [CommRing A₀] [TopologicalSpace A₀] [DiscreteTopology A₀]
    (r : A ≃+* A₀) :
    finiteCoefficientComparisonHom A A₀ r ≫ finiteCoefficientComparisonInv A A₀ r = 𝟙 _ := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := discreteTopology_bot A
  ext S s
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  change r.symm (r (s.down x)) = s.down x
  exact r.symm_apply_apply _

/-- The inverse and forward postcomposition maps compose to the identity on C_u(A₀).
Source: node proof step 4. On a section t, the composite has value
r (r.symm (t x)) = t x. The same sectionwise and bundled-map extensionality proves
this identity. No nonzero-ring hypothesis is used.
(blueprint: lem-sfb-finite-coefficient-small-carrier-comparison). -/
theorem finiteCoefficientComparison_inv_hom_id (A : Type u) [CommRing A]
    (A₀ : Type) [CommRing A₀] [TopologicalSpace A₀] [DiscreteTopology A₀]
    (r : A ≃+* A₀) :
    finiteCoefficientComparisonInv A A₀ r ≫ finiteCoefficientComparisonHom A A₀ r = 𝟙 _ := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := discreteTopology_bot A
  ext S s
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  change r (r.symm (s.down x)) = s.down x
  exact r.apply_symm_apply _

/-- The canonical carrier comparison, with the explicitly constructed postcomposition
maps as its forward and inverse data; the inverse identities are
`finiteCoefficientComparison_hom_inv_id` and `finiteCoefficientComparison_inv_hom_id`.
Source: node proof steps 3--4.
(blueprint: lem-sfb-finite-coefficient-small-carrier-comparison). -/
def finiteCoefficientCarrierIso (A : Type u) [CommRing A]
    (A₀ : Type) [CommRing A₀] [TopologicalSpace A₀] [DiscreteTopology A₀]
    (r : A ≃+* A₀) :
    finiteCoefficientComparisonSource A ≅ finiteCoefficientComparisonTarget.{u} A₀ where
  hom := finiteCoefficientComparisonHom A A₀ r
  inv := finiteCoefficientComparisonInv A A₀ r
  hom_inv_id := finiteCoefficientComparison_hom_inv_id A A₀ r
  inv_hom_id := finiteCoefficientComparison_inv_hom_id A A₀ r

/-- Every finite commutative ring has a small discrete presentation. For every choice,
the constructed isomorphism has precisely the two postcomposition component formulas
and intertwines finite maps and continuous maps from arbitrary small topological rings.
The component formulas are expressed pointwise on the underlying continuous functions;
by extensionality these are exactly the stated equalities of lifted sections.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-scalar-six/_section.md, coefficient list (1)--(3), and DAG proof steps 1--6.

Proof:
1. Enumerate A by Fin n and transport zero, one, addition, multiplication and negation
along the enumeration. Ring axioms follow after applying its injective inverse;
this gives a finite small ring and a ring equivalence, also for the zero ring.
2. Put the bottom topology on this small carrier. All operations and the equivalence
and its inverse are continuous because their sources are discrete. Then fix any
allowed presentation, not just this enumeration.
3. Both endpoint sheaves have sections ULift C(S,-), with restrictions by
precomposition. Postcomposition by r and r.symm gives their actual ring-sheaf maps.
The recorded def-sfb-continuous-map-condensed-ring and
def-sfb-continuous-map-condensed-ring-map supply the canonical ring-object structures
and IsMonHom after sheafCompose forget₂; the auxiliary lifts add no data.
4. On every section, r.symm (r (s x)) = s x and r (r.symm (t x)) = t x.
Extensionality gives both inverse identities and the displayed component formulas.
5. For a finite ring map φ and a acting sectionwise by φ, both sides of the asserted
square take s at x to r_B (φ (s x)). The conjugated map is continuous because its
source is discrete. Extensionality gives equality of the actual bundled maps.
6. For continuous ψ from any small topological ring, both sides of the mixed equation
take s at x to r_A (ψ (s x)). Continuity follows by composition; extensionality
again gives equality, with no discreteness assumption on the mixed source.
(blueprint: lem-sfb-finite-coefficient-small-carrier-comparison). -/
theorem finiteCoefficientSmallCarrierComparison :
    (∀ (A : Type u) [CommRing A] [Finite A],
      ∃ (A₀ : Type) (_ : CommRing A₀), Finite A₀ ∧ Nonempty (A ≃+* A₀)) ∧
    (∀ (A : Type u) [CommRing A] [Finite A]
      (A₀ : Type) [CommRing A₀] [Finite A₀] [TopologicalSpace A₀] [DiscreteTopology A₀]
      (r_A : A ≃+* A₀),
      (∀ (S : Profinite.{u}) (s : (cartesianFinitePointRing A).obj.obj (op S)) (x : S),
        (((finiteCoefficientCarrierIso A A₀ r_A).hom.hom.hom.hom.app (op S)) s).down x =
          r_A (s.down x)) ∧
      (∀ (S : Profinite.{u})
        (t : (Profinite.continuousMapRingObj A₀).obj.obj (op S)) (x : S),
        (((finiteCoefficientCarrierIso A A₀ r_A).inv.hom.hom.hom.app (op S)) t).down x =
          r_A.symm (t.down x)) ∧
      (∀ (B : Type u) [CommRing B] [Finite B]
        (B₀ : Type) [CommRing B₀] [Finite B₀] [TopologicalSpace B₀] [DiscreteTopology B₀]
        (r_B : B ≃+* B₀)
        (e_B : finiteCoefficientComparisonSource B ≅ finiteCoefficientComparisonTarget.{u} B₀)
        (he_B : ∀ (S : Profinite.{u}) (s : (cartesianFinitePointRing B).obj.obj (op S))
          (x : S), ((e_B.hom.hom.hom.hom.app (op S)) s).down x = r_B (s.down x))
        (φ : A →+* B)
        (a : finiteCoefficientComparisonSource A ⟶ finiteCoefficientComparisonSource B),
        (∀ (S : Profinite.{u}) (s : (cartesianFinitePointRing A).obj.obj (op S)) (x : S),
          ((a.hom.hom.hom.app (op S)) s).down x = φ (s.down x)) →
        a ≫ e_B.hom =
          (finiteCoefficientCarrierIso A A₀ r_A).hom ≫
            finiteCoefficientComparisonMap (r_B.toRingHom.comp (φ.comp r_A.symm.toRingHom))
              continuous_of_discreteTopology) ∧
      (∀ (T : Type) [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
        (ψ : T →+* A) (hψ : @Continuous T A _ ⊥ ψ)
        (b : finiteCoefficientComparisonTarget.{u} T ⟶ finiteCoefficientComparisonSource A),
        (∀ (S : Profinite.{u}) (s : (Profinite.continuousMapRingObj T).obj.obj (op S)) (x : S),
          ((b.hom.hom.hom.app (op S)) s).down x = ψ (s.down x)) →
        b ≫ (finiteCoefficientCarrierIso A A₀ r_A).hom =
          finiteCoefficientComparisonMixedMap A A₀ r_A ψ hψ)) := by
  classical
  constructor
  · intro A _ _
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin A
    letI : CommRing (Fin n) := e.symm.commRing
    let f : A →+* Fin n :=
      { toFun := e
        map_one' := by rfl
        map_mul' := by
          intro x y
          rw [Equiv.mul_def]
          simp
        map_zero' := by
          rw [Equiv.zero_def]
          simp
        map_add' := by
          intro x y
          rw [Equiv.add_def]
          simp }
    exact ⟨Fin n, inferInstance, inferInstance, ⟨RingEquiv.ofBijective f e.bijective⟩⟩
  · intro A _ _ A₀ _ _ _ _ r_A
    constructor
    · intro S s x
      rfl
    · constructor
      · intro S t x
        rfl
      · constructor
        · intro B _ _ B₀ _ _ _ _ r_B e_B he_B φ a
          intro ha
          ext S s
          apply ULift.ext
          apply ContinuousMap.ext
          intro x
          change ((e_B.hom.hom.hom.hom.app S) ((a.hom.hom.hom.app S) s)).down x = _
          rw [he_B S.unop ((a.hom.hom.hom.app S) s) x, ha S.unop s x]
          change r_B (φ (s.down x)) =
            r_B (φ (r_A.symm (r_A (s.down x))))
          rw [r_A.symm_apply_apply]
        · intro T _ _ _ ψ hψ b
          intro hb
          ext S s
          apply ULift.ext
          apply ContinuousMap.ext
          intro x
          change (((finiteCoefficientCarrierIso A A₀ r_A).hom.hom.hom.hom.app S)
              ((b.hom.hom.hom.app S) s)).down x = _
          have hb' : ((b.hom.hom.hom.app S) s).down x = ψ (s.down x) := by
            simpa using hb S.unop s x
          change r_A (((b.hom.hom.hom.app S) s).down x) = _
          rw [hb']
          change r_A (ψ (s.down x)) = r_A (ψ (s.down x))
          rfl

end AlgebraicGeometry.ProEtale.CondensedRing
