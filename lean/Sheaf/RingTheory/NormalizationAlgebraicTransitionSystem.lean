module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Normalization over finite algebraic stages

Source: Stacks, More on Algebra, Tag 09II, `proposition-epp-essentially-finite-type`,
filtered-normalization paragraph; Algebra, Tag 09IG; More on Algebra, Tag 0AUW.
(blueprint: lem-sfb-normalization-algebraic-transition-system)

The auxiliary constructions below give the actual reduced tensor rings, integral
closures, tensor rings, inclusion maps, diagrams, and their canonical cocones.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v w x y

namespace Algebra
namespace NormalizationTransition

variable (K : Type w) (L : Type x) [Field K] [Field L] [Algebra K L]

/-- The reduced tensor ring of Tag 09II's normalization diagram.
(blueprint: lem-sfb-normalization-algebraic-transition-system) -/
abbrev reducedTensor (Q : Type y) [CommRing Q] [Algebra K Q] :=
  (L ⊗[K] Q) ⧸ nilradical (L ⊗[K] Q)

variable {K L}

/-- The reduced tensor transition induced by a field inclusion (Tag 09II).
Nilpotent elements map to nilpotent elements, so the quotient map is defined.
(blueprint: lem-sfb-normalization-algebraic-transition-system) -/
def reducedMap {Q Q' : Type y} [CommRing Q] [CommRing Q']
    [Algebra K Q] [Algebra K Q'] (f : Q →ₐ[K] Q') :
    reducedTensor K L Q →ₐ[L] reducedTensor K L Q' :=
  Ideal.quotientMapₐ _ (Algebra.TensorProduct.map (AlgHom.id L L) f)
    (fun _ h ↦ mem_nilradical.mpr
      ((mem_nilradical.mp h).map (Algebra.TensorProduct.map (AlgHom.id L L) f)))

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B]
variable [Algebra A K] [Algebra A B] [Algebra B L] [Algebra A L]
variable [IsScalarTower A K L] [IsScalarTower A B L]

/-- The closure transition is the restriction of the given inclusion (Tag 09II).
(blueprint: lem-sfb-normalization-algebraic-transition-system) -/
def closureMap {Q Q' : Type y} [CommRing Q] [CommRing Q']
    [Algebra K Q] [Algebra K Q'] [Algebra A Q] [Algebra A Q']
    [IsScalarTower A K Q] [IsScalarTower A K Q'] (f : Q →ₐ[K] Q') :
    integralClosure A Q →ₐ[A] integralClosure A Q' :=
  (f.restrictScalars A).mapIntegralClosure

/-- The closure over B transition is induced by the reduced tensor map (Tag 09II).
(blueprint: lem-sfb-normalization-algebraic-transition-system) -/
def secondClosureMap {Q Q' : Type y} [CommRing Q] [CommRing Q']
    [Algebra K Q] [Algebra K Q'] (f : Q →ₐ[K] Q') :
    integralClosure B (reducedTensor K L Q) →ₐ[B]
      integralClosure B (reducedTensor K L Q') :=
  ((reducedMap (L := L) f).restrictScalars B).mapIntegralClosure

/-- Tensor transitions are the identity on B and the closure inclusion on the right (Tag 09II).
(blueprint: lem-sfb-normalization-algebraic-transition-system) -/
def tensorMap {Q Q' : Type y} [CommRing Q] [CommRing Q']
    [Algebra K Q] [Algebra K Q'] [Algebra A Q] [Algebra A Q']
    [IsScalarTower A K Q] [IsScalarTower A K Q'] (f : Q →ₐ[K] Q') :
    B ⊗[A] integralClosure A Q →ₐ[B] B ⊗[A] integralClosure A Q' :=
  Algebra.TensorProduct.map (AlgHom.id B B) (closureMap A f)

variable (P : Type y) [Field P] [Algebra K P] [Algebra A P] [IsScalarTower A K P]

/-- Finite intermediate fields, ordered by inclusion, in the Tag 09II diagram.
(blueprint: lem-sfb-normalization-algebraic-transition-system) -/
abbrev finiteStages := {F : IntermediateField K P // FiniteDimensional K F}

/-- The first ring transition in Tag 09II, with its prescribed inclusion formula.
(blueprint: lem-sfb-normalization-algebraic-transition-system) -/
def firstTransition (F G : finiteStages (K := K) P) (h : F ≤ G) :
    integralClosure A F.1 →+* integralClosure A G.1 :=
  (closureMap A (IntermediateField.inclusion h)).toRingHom

/-- The first ring inclusion into the algebraic-extension apex (Tag 09II).
(blueprint: lem-sfb-normalization-algebraic-transition-system) -/
def firstToApex (F : finiteStages (K := K) P) :
    integralClosure A F.1 →+* integralClosure A P :=
  (closureMap A F.1.val).toRingHom

/-- Identity, composition and apex compatibility for the first system (Tag 09II).
Proof: inclusions compose literally. Restriction to integral elements, quotienting by
nilpotents, and tensoring preserve these formulas. Check on integral elements, on
quotient representatives, or on pure tensors, respectively. This is the identity and
composition assertion in Step 2 of the node's proof.
(blueprint: lem-sfb-normalization-algebraic-transition-system) -/
theorem firstLaws :
    (∀ F : finiteStages (K := K) P,
      firstTransition (K := K) A P F F le_rfl = RingHom.id _) ∧
    (∀ (F G H : finiteStages (K := K) P) (h : F ≤ G) (k : G ≤ H),
      firstTransition (K := K) A P F H (h.trans k) =
        (firstTransition (K := K) A P G H k).comp (firstTransition (K := K) A P F G h)) ∧
    (∀ (F G : finiteStages (K := K) P) (h : F ≤ G),
      (firstToApex (K := K) A P G).comp (firstTransition (K := K) A P F G h) =
        firstToApex (K := K) A P F) :=
  sorry

/-- The first ring diagram of finite normalizations (Tag 09II).
(blueprint: lem-sfb-normalization-algebraic-transition-system) -/
def firstDiagram : finiteStages (K := K) P ⥤ CommRingCat where
  obj F := CommRingCat.of (integralClosure A F.1)
  map {F G} h := CommRingCat.ofHom (firstTransition (K := K) A P F G (leOfHom h))
  map_id F := congrArg CommRingCat.ofHom ((firstLaws (K := K) A P).1 F)
  map_comp h k := congrArg CommRingCat.ofHom
    ((firstLaws (K := K) A P).2.1 _ _ _ (leOfHom h) (leOfHom k))

/-- The canonical first cocone with its actual inclusion legs (Tag 09II).
(blueprint: lem-sfb-normalization-algebraic-transition-system) -/
def firstCocone : Cocone (firstDiagram (K := K) A P) where
  pt := CommRingCat.of (integralClosure A P)
  ι := { app := fun F ↦ CommRingCat.ofHom (firstToApex (K := K) A P F)
         naturality := fun _ _ h ↦ congrArg CommRingCat.ofHom
           ((firstLaws (K := K) A P).2.2 _ _ (leOfHom h)) }

/-- The second ring transition in Tag 09II, with its prescribed inclusion formula.
(blueprint: lem-sfb-normalization-algebraic-transition-system) -/
def secondTransition (F G : finiteStages (K := K) P) (h : F ≤ G) :
    integralClosure B (reducedTensor K L F.1) →+* integralClosure B (reducedTensor K L G.1) :=
  (secondClosureMap (L := L) B (IntermediateField.inclusion h)).toRingHom

/-- The second ring inclusion into the algebraic-extension apex (Tag 09II).
(blueprint: lem-sfb-normalization-algebraic-transition-system) -/
def secondToApex (F : finiteStages (K := K) P) :
    integralClosure B (reducedTensor K L F.1) →+* integralClosure B (reducedTensor K L P) :=
  (secondClosureMap (L := L) B F.1.val).toRingHom

/-- Identity, composition and apex compatibility for the second system (Tag 09II).
Proof: inclusions compose literally. Restriction to integral elements, quotienting by
nilpotents, and tensoring preserve these formulas. Check on integral elements, on
quotient representatives, or on pure tensors, respectively. This is the identity and
composition assertion in Step 2 of the node's proof.
(blueprint: lem-sfb-normalization-algebraic-transition-system) -/
theorem secondLaws :
    (∀ F : finiteStages (K := K) P,
      secondTransition (K := K) (L := L) B P F F le_rfl = RingHom.id _) ∧
    (∀ (F G H : finiteStages (K := K) P) (h : F ≤ G) (k : G ≤ H),
      secondTransition (K := K) (L := L) B P F H (h.trans k) =
        (secondTransition (K := K) (L := L) B P G H k).comp
          (secondTransition (K := K) (L := L) B P F G h)) ∧
    (∀ (F G : finiteStages (K := K) P) (h : F ≤ G),
      (secondToApex (K := K) (L := L) B P G).comp (secondTransition (K := K) (L := L) B P F G h) =
        secondToApex (K := K) (L := L) B P F) :=
  sorry

/-- The second ring diagram of finite normalizations (Tag 09II).
(blueprint: lem-sfb-normalization-algebraic-transition-system) -/
def secondDiagram : finiteStages (K := K) P ⥤ CommRingCat where
  obj F := CommRingCat.of (integralClosure B (reducedTensor K L F.1))
  map {F G} h := CommRingCat.ofHom (secondTransition (K := K) (L := L) B P F G (leOfHom h))
  map_id F := congrArg CommRingCat.ofHom ((secondLaws (K := K) (L := L) B P).1 F)
  map_comp h k := congrArg CommRingCat.ofHom
    ((secondLaws (K := K) (L := L) B P).2.1 _ _ _ (leOfHom h) (leOfHom k))

/-- The canonical second cocone with its actual inclusion legs (Tag 09II).
(blueprint: lem-sfb-normalization-algebraic-transition-system) -/
def secondCocone : Cocone (secondDiagram (K := K) (L := L) B P) where
  pt := CommRingCat.of (integralClosure B (reducedTensor K L P))
  ι := { app := fun F ↦ CommRingCat.ofHom (secondToApex (K := K) (L := L) B P F)
         naturality := fun _ _ h ↦ congrArg CommRingCat.ofHom
           ((secondLaws (K := K) (L := L) B P).2.2 _ _ (leOfHom h)) }

/-- The tensor ring transition in Tag 09II, with its prescribed inclusion formula.
(blueprint: lem-sfb-normalization-algebraic-transition-system) -/
def tensorTransition (F G : finiteStages (K := K) P) (h : F ≤ G) :
    B ⊗[A] integralClosure A F.1 →+* B ⊗[A] integralClosure A G.1 :=
  (tensorMap A B (IntermediateField.inclusion h)).toRingHom

/-- The tensor ring inclusion into the algebraic-extension apex (Tag 09II).
(blueprint: lem-sfb-normalization-algebraic-transition-system) -/
def tensorToApex (F : finiteStages (K := K) P) :
    B ⊗[A] integralClosure A F.1 →+* B ⊗[A] integralClosure A P :=
  (tensorMap A B F.1.val).toRingHom

/-- Identity, composition and apex compatibility for the tensor system (Tag 09II).
Proof: inclusions compose literally. Restriction to integral elements, quotienting by
nilpotents, and tensoring preserve these formulas. Check on integral elements, on
quotient representatives, or on pure tensors, respectively. This is the identity and
composition assertion in Step 2 of the node's proof.
(blueprint: lem-sfb-normalization-algebraic-transition-system) -/
theorem tensorLaws :
    (∀ F : finiteStages (K := K) P,
      tensorTransition (K := K) A B P F F le_rfl = RingHom.id _) ∧
    (∀ (F G H : finiteStages (K := K) P) (h : F ≤ G) (k : G ≤ H),
      tensorTransition (K := K) A B P F H (h.trans k) =
        (tensorTransition (K := K) A B P G H k).comp (tensorTransition (K := K) A B P F G h)) ∧
    (∀ (F G : finiteStages (K := K) P) (h : F ≤ G),
      (tensorToApex (K := K) A B P G).comp (tensorTransition (K := K) A B P F G h) =
        tensorToApex (K := K) A B P F) :=
  sorry

/-- The tensor ring diagram of finite normalizations (Tag 09II).
(blueprint: lem-sfb-normalization-algebraic-transition-system) -/
def tensorDiagram : finiteStages (K := K) P ⥤ CommRingCat where
  obj F := CommRingCat.of (B ⊗[A] integralClosure A F.1)
  map {F G} h := CommRingCat.ofHom (tensorTransition (K := K) A B P F G (leOfHom h))
  map_id F := congrArg CommRingCat.ofHom ((tensorLaws (K := K) A B P).1 F)
  map_comp h k := congrArg CommRingCat.ofHom
    ((tensorLaws (K := K) A B P).2.1 _ _ _ (leOfHom h) (leOfHom k))

/-- The canonical tensor cocone with its actual inclusion legs (Tag 09II).
(blueprint: lem-sfb-normalization-algebraic-transition-system) -/
def tensorCocone : Cocone (tensorDiagram (K := K) A B P) where
  pt := CommRingCat.of (B ⊗[A] integralClosure A P)
  ι := { app := fun F ↦ CommRingCat.ofHom (tensorToApex (K := K) A B P F)
         naturality := fun _ _ h ↦ congrArg CommRingCat.ofHom
           ((tensorLaws (K := K) A B P).2.2 _ _ (leOfHom h)) }

/-- The actual multiplication map from the tensor of the first normalization to
its reduced generic tensor (Tag 09II). It sends b ⊗ r to the class of b ⊗ r.
(blueprint: lem-sfb-normalization-algebraic-transition-system) -/
def multiplicationMap (Q : Type y) [CommRing Q] [Algebra K Q]
    [Algebra A Q] [IsScalarTower A K Q] :
    B ⊗[A] integralClosure A Q →ₐ[A] reducedTensor K L Q :=
  Algebra.TensorProduct.productMap
    (IsScalarTower.toAlgHom A B (reducedTensor K L Q))
    ((((Ideal.Quotient.mkₐ K (nilradical (L ⊗[K] Q))).comp
      (Algebra.TensorProduct.includeRight : Q →ₐ[K] L ⊗[K] Q)).restrictScalars A).comp
        (integralClosure A Q).val)

/-- Every element in the image of the multiplication map is integral over B
(Stacks Tag 09II normalization diagram, Algebra Tags 00GI and 00GO).
Proof: the image of r in the first closure satisfies its monic equation over A,
whose image over B is still monic and vanishes. Elements from B are integral.
The integral elements form a subring, so sums of products of these images remain
integral. Pure tensors generate the tensor product, giving the assertion for z.
This is the map-construction part of Step 10 of the node's proof.
(blueprint: lem-sfb-normalization-algebraic-transition-system) -/
theorem multiplication_mem_closure (Q : Type y) [CommRing Q] [Algebra K Q]
    [Algebra A Q] [IsScalarTower A K Q] (z : B ⊗[A] integralClosure A Q) :
    multiplicationMap (K := K) (L := L) A B Q z ∈
      integralClosure B (reducedTensor K L Q) :=
  sorry

/-- The canonical multiplication map into the second normalization (Tag 09II).
Its underlying map into the reduced tensor is multiplicationMap, with codomain
restricted to integral elements; no arbitrary map or choice is involved.
(blueprint: lem-sfb-normalization-algebraic-transition-system) -/
def multiplicationToClosure (Q : Type y) [CommRing Q] [Algebra K Q]
    [Algebra A Q] [IsScalarTower A K Q] :
    B ⊗[A] integralClosure A Q →ₐ[A] integralClosure B (reducedTensor K L Q) :=
  (multiplicationMap (K := K) (L := L) A B Q).codRestrict
    ((integralClosure B (reducedTensor K L Q)).restrictScalars A)
    (multiplication_mem_closure (K := K) (L := L) A B Q)

/-- Injective normalization systems and faithful flatness over every finite stage.
Source: Stacks, More on Algebra Tag 09II, filtered-normalization paragraph, with
its algebraic transition-system refinement; Tag 0AUW(1) for faithful flatness.

Proof, following the node's ten steps:
1. K is a finite stage. Finitely many algebraic generators generate a finite
extension (lem-weil-pbc-algebraic-generators-finite-extension), so finite stages
are directed and cover P.
2. Tensor associativity (lem-weil-pbc-algebra-tensor-pushout-universal-property)
identifies raw transitions with field scalar extension. They are injective
(lem-sfb-field-extension-tensor-injective). If an image is nilpotent, injectivity
shows the source was nilpotent; reduced transitions are injective. Restricting
injections gives both closure injections. Their formulas preserve compositions.
3. Every integral element of P occurs in a finite stage, and its monic equation
descends along the inclusion. Hence R_P is the union of the R_F. A compatible
family of ring maps glues uniquely by evaluation in any common finite stage.
4. Finite tensor supports descend every element of E_P to some E_F. A monic
equation over B descends through the injective reduced transition. Thus C_P is
the directed union of C_F, with the same unique gluing of compatible ring maps.
5. A compatible family of maps from T_F has a common restriction from B and a
restriction from R_P by Step 3. These agree over A. The tensor pushout universal
property constructs the unique map from T_P. This is the third ring colimit.
6. A is a one-dimensional Noetherian domain: each ideal is principal, and the
unit-times-uniformizer-power description leaves only zero and the maximal ideal
as primes (lem-weil-pbc-dvr-unit-times-uniformizer-power). Krull--Akizuki gives
Dedekind finite normalizations (lem-sc-integral-closure-dedekind-surjective-fibres).
7. R_P is torsion-free over R_F inside P, hence flat by
lem-sfb-dedekind-torsionfree-module-flat. It is integral over R_F since it is
integral over A. Integral injective lying-over gives spectrum surjectivity
(lem-weil-pbc-integral-injective-lying-over); flatness plus surjectivity gives
faithful flatness (lem-weil-pbc-flat-surjective-spectrum-faithfully-flat).
8. A[1/a]=K by the unit-times-power description. Clear denominators in a monic
equation for x in F: for sufficiently large N, a^N x is integral over A. Thus
F is the localization of R_F away from a; its inclusion into F is injective.
9. B[1/b]=L likewise. Locality and injectivity give a=u b^e in B with e positive,
so a is invertible after inverting b. Write each tensor as a sum of terms with
coefficients v/b^m and r/a^n. The corresponding sum in T_F[1/b] maps to it,
proving surjectivity even when the raw tensor has nilpotents. The localization
universal property uniquely specifies the displayed map by its restriction.
10. The multiplication map lands in C_Q by multiplication_mem_closure. A monic
equation for c over B becomes a monic equation over T_Q by sending v to v ⊗ 1.
It still vanishes, proving integrality for every finite Q and for P.

Nonempty IsColimit states that the fixed cocone is colimiting; equivalently its
canonical comparison from a chosen colimit is an isomorphism. IsLocalization.Away
states the canonical first localization isomorphism with the field F itself.
(blueprint: lem-sfb-normalization-algebraic-transition-system) -/
theorem normalization_algebraic_transition_system
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsFractionRing A K] [IsFractionRing B L] [Algebra.IsAlgebraic K P]
    [IsLocalHom (algebraMap A B)] (hinj : Function.Injective (algebraMap A B)) :
    Nonempty (finiteStages (K := K) P) ∧
    (∀ F G : finiteStages (K := K) P, ∃ H : finiteStages (K := K) P, F ≤ H ∧ G ≤ H) ∧
    (∀ (F G : finiteStages (K := K) P) (h : F ≤ G),
      Function.Injective (reducedMap (L := L) (IntermediateField.inclusion h)) ∧
      Function.Injective (firstTransition A P F G h) ∧
      Function.Injective (secondTransition (L := L) B P F G h)) ∧
    (∀ F : finiteStages (K := K) P,
      Function.Injective (reducedMap (L := L) F.1.val) ∧
      Function.Injective (firstToApex A P F) ∧
      Function.Injective (secondToApex (L := L) B P F)) ∧
    Nonempty (IsColimit (firstCocone (K := K) A P)) ∧
    Nonempty (IsColimit (secondCocone (K := K) (L := L) B P)) ∧
    Nonempty (IsColimit (tensorCocone (K := K) A B P)) ∧
    (∀ F : finiteStages (K := K) P, (firstToApex A P F).FaithfullyFlat) ∧
    (∀ (a : A) (b : B), IsLocalRing.maximalIdeal A = Ideal.span {a} →
      IsLocalRing.maximalIdeal B = Ideal.span {b} →
      ∀ F : finiteStages (K := K) P,
        IsLocalization.Away (algebraMap A (integralClosure A F.1) a) F.1 ∧
        ∃ m : Localization.Away (algebraMap B (B ⊗[A] integralClosure A F.1) b) →+*
            reducedTensor K L F.1,
          m.comp (algebraMap (B ⊗[A] integralClosure A F.1)
            (Localization.Away (algebraMap B (B ⊗[A] integralClosure A F.1) b))) =
              (multiplicationMap (K := K) (L := L) A B F.1).toRingHom ∧
          Function.Surjective m) ∧
    (∀ F : finiteStages (K := K) P,
      (multiplicationToClosure (K := K) (L := L) A B F.1).toRingHom.IsIntegral) ∧
    (multiplicationToClosure (K := K) (L := L) A B P).toRingHom.IsIntegral :=
  sorry

end NormalizationTransition
end Algebra
