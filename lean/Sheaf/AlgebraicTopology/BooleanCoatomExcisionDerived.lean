/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q54
-/
module

public import Sheaf.AlgebraicTopology.AugmentedPosetChains
public import Sheaf.AlgebraicTopology.AugmentedPosetChainPrism
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.CochainComplexOpposite

/-! # Derived Boolean coatom excision

Source: the agent-written finite combinatorial extraction below paragraph (3) of
`latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`'s direct-images proof;
that paragraph supplies context only, not the combinatorial assertion
(blueprint: lem-sfb-boolean-coatom-excision-derived).

The quotient is the categorical cokernel of the chain-basis inclusion. Cokernels of
complexes of modules are computed degreewise, so this is the degreewise quotient.
The comparison is constructed by descending the signed last-vertex deletion map.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u w

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicTopology.AugmentedPosetChains.BooleanCoatom

variable {E : Type u} [DecidableEq E]

/-- Nonempty proper subsets, with their induced inclusion order.
Source: node statement, definition of P_F
(blueprint: lem-sfb-boolean-coatom-excision-derived). -/
abbrev Proper (F : Finset E) := {S : Finset E // S.Nonempty ∧ S ⊂ F}

/-- B_F is the recorded augmented strict-chain complex, without a second chain construction.
Source: node statement, definition of B_F
(blueprint: lem-sfb-boolean-coatom-excision-derived). -/
abbrev booleanComplex (F : Finset E) := complex ℚ (Proper F)

variable [Fintype E]

/-- The chosen coatom E minus {a}.
Source: node statement, v = E minus {a}
(blueprint: lem-sfb-boolean-coatom-excision-derived). -/
def coatom (a : E) : Finset E := Finset.univ.erase a

/-- The proper subset poset with the chosen coatom removed, with induced order.
Source: node statement, definition of D
(blueprint: lem-sfb-boolean-coatom-excision-derived). -/
abbrev Deleted (a : E) := {S : Proper (Finset.univ : Finset E) // S.val ≠ coatom a}

/-- The order-preserving inclusion of the deleted poset.
Source: node proof step 3 (blueprint: lem-sfb-boolean-coatom-excision-derived). -/
def inclusionOrder (a : E) : Deleted a →o Proper (Finset.univ : Finset E) where
  toFun := Subtype.val
  monotone' := fun _ _ h ↦ h

/-- The actual chain-basis inclusion, using the recorded monotone-chain-map construction.
Source: node proof step 3 (blueprint: lem-sfb-boolean-coatom-excision-derived). -/
def inclusion (a : E) : complex ℚ (Deleted a) ⟶ booleanComplex (Finset.univ : Finset E) :=
  map ℚ (inclusionOrder a)

/-- The degreewise quotient, constructed as the cokernel in complexes of modules.
Source: node statement and proof step 3
(blueprint: lem-sfb-boolean-coatom-excision-derived). -/
def quotientComplex (a : E) : ChainComplex (ModuleCat.{u} ℚ) ℤ :=
  cokernel (inclusion a)

/-- The canonical quotient chain map, not an arbitrary morphism to the quotient.
Source: node statement, p (blueprint: lem-sfb-boolean-coatom-excision-derived). -/
def projection (a : E) : booleanComplex (Finset.univ : Finset E) ⟶ quotientComplex a :=
  cokernel.π (inclusion a)

/-- The suspension has term K_(n-1) and differential -d_K.
Source: node statement, suspension convention
(blueprint: lem-sfb-boolean-coatom-excision-derived). -/
def suspension (K : ChainComplex (ModuleCat.{u} ℚ) ℤ) :
    ChainComplex (ModuleCat.{u} ℚ) ℤ where
  X n := K.X (n - 1)
  d i j := -K.d (i - 1) (j - 1)
  shape i j hij := by
    rw [K.shape, neg_zero]
    simp only [ComplexShape.down_Rel] at hij ⊢
    omega
  d_comp_d' i j k _ _ := by simp

/-- Retain vertices that belong to P_v. On a surviving quotient chain, this is exactly
its prefix before the final vertex v; it is only applied to the list with that vertex removed.
Source: node proof steps 3 and 4
(blueprint: lem-sfb-boolean-coatom-excision-derived). -/
def smallerVertices (a : E) (l : List (Proper (Finset.univ : Finset E))) :
    List (Proper (coatom a)) :=
  l.filterMap fun S ↦ if h : S.val.Nonempty ∧ S.val ⊂ coatom a then some ⟨S.val, h⟩ else none

/-- The signed drop-last rule on the full chain basis, zero on chains avoiding v.
In degree zero the list after deletion is empty and the coefficient is 1.
Source: node statement, theta_n, and proof step 4
(blueprint: lem-sfb-boolean-coatom-excision-derived). -/
def signedDeletion (a : E) (n : ℤ) :
    (booleanComplex (Finset.univ : Finset E)).X n ⟶
      (suspension (booleanComplex (coatom a))).X n :=
  ModuleCat.ofHom (Finsupp.linearCombination ℚ fun c ↦
    if c.val.getLast?.map Subtype.val = some (coatom a) then
      (-1 : ℚ) ^ n.toNat • bracket ℚ (n - 1) (smallerVertices a c.val.dropLast)
    else 0)

/-- The signed deletion rule commutes with the suspension differential.
Source: node proof steps 3 and 4
(blueprint: lem-sfb-boolean-coatom-excision-derived).

Proof: a strict chain containing the coatom ends there. If it avoids the coatom,
so does every face and both sides vanish. Otherwise write it as [c<v]. The face
deleting v vanishes. All remaining faces give the deletion differential of c;
the two sides have coefficients (-1)^(n-1) and -(-1)^n, which agree. For n=1
this uses the vertex-to-empty augmentation. In degree zero both outgoing maps
vanish, and in negative degrees signedDeletion is zero. Extend by linearity. -/
theorem signedDeletion_comm (a : E) (hcard : 2 ≤ Fintype.card E) (i j : ℤ) :
    signedDeletion a i ≫ (suspension (booleanComplex (coatom a))).d i j =
      (booleanComplex (Finset.univ : Finset E)).d i j ≫ signedDeletion a j := by
  sorry

/-- Signed deletion as a chain map, before descending to the quotient.
Source: node proof step 4 (blueprint: lem-sfb-boolean-coatom-excision-derived). -/
def deletionMap (a : E) (hcard : 2 ≤ Fintype.card E) :
    booleanComplex (Finset.univ : Finset E) ⟶ suspension (booleanComplex (coatom a)) where
  f := signedDeletion a
  comm' := fun i j _ ↦ signedDeletion_comm a hcard i j

/-- Signed deletion annihilates the included subcomplex.
Source: node proof steps 3 and 4
(blueprint: lem-sfb-boolean-coatom-excision-derived).

Proof: on every strict-chain generator from D, no vertex is v. In particular
its last vertex is not v and signedDeletion is zero. The empty list has no last
vertex and is also killed. Extend by linearity in each degree. -/
theorem inclusion_deletionMap (a : E) (hcard : 2 ≤ Fintype.card E) :
    inclusion a ≫ deletionMap a hcard = 0 := by
  classical
  ext n : 1
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro c r
  have hlast : (c.val.map (inclusionOrder a)).getLast?.map Subtype.val ≠
      some (coatom a) := by
    rw [List.getLast?_map, Option.map_map]
    cases h : c.val.getLast? with
    | none => simp
    | some S => simpa [inclusionOrder] using S.property
  let δ := Finsupp.linearCombination ℚ
    (fun c : Simplex (Proper (Finset.univ : Finset E)) n ↦
      if c.val.getLast?.map Subtype.val = some (coatom a) then
        (-1 : ℚ) ^ n.toNat • bracket ℚ (n - 1) (smallerVertices a c.val.dropLast)
      else 0)
  change δ (Finsupp.linearCombination ℚ
    (fun c : Simplex (Deleted a) n ↦ bracket ℚ n (c.val.map (inclusionOrder a)))
      (Finsupp.single c r)) = 0
  rw [Finsupp.linearCombination_single, map_smul]
  suffices δ (bracket ℚ n (c.val.map (inclusionOrder a))) = 0 by
    rw [this, smul_zero]
  unfold bracket
  split
  · simp only [δ, Finsupp.linearCombination_single, if_neg hlast, smul_zero]
  · exact map_zero _

/-- The prescribed theta map, descended along the canonical cokernel projection.
Source: node statement, theta, and proof step 4
(blueprint: lem-sfb-boolean-coatom-excision-derived). -/
def thetaMap (a : E) (hcard : 2 ≤ Fintype.card E) :
    quotientComplex a ⟶ suspension (booleanComplex (coatom a)) :=
  cokernel.desc (inclusion a) (deletionMap a hcard) (inclusion_deletionMap a hcard)

/-- The prescribed comparison has an inverse; this assertion determines that inverse uniquely.
Source: node proof steps 3 and 4
(blueprint: lem-sfb-boolean-coatom-excision-derived).

Proof: the included basis consists exactly of chains avoiding v. The quotient
basis therefore consists of chains ending in v. Deleting the final v identifies
these with the strict-chain basis of P_v one degree lower, including the empty
prefix in degree zero. The inverse appends v and multiplies by (-1)^n. Both
composites multiply generators by (-1)^(2n)=1. In negative degrees the inclusion
is an isomorphism and both quotient and suspension are zero. Thus thetaMap is
degreewise invertible, hence an isomorphism of chain complexes. -/
theorem thetaMap_isIso (a : E) (hcard : 2 ≤ Fintype.card E) :
    IsIso (thetaMap a hcard) := by
  sorry

/-- The signed chain isomorphism, with its uniquely determined inverse.
Source: node statement, theta (blueprint: lem-sfb-boolean-coatom-excision-derived). -/
def theta (a : E) (hcard : 2 ≤ Fintype.card E) :
    quotientComplex a ≅ suspension (booleanComplex (coatom a)) :=
  @asIso _ _ _ _ (thetaMap a hcard) (thetaMap_isIso a hcard)

/-- The grading reversal q ↦ -q from chain to cochain grading: restriction along Mathlib's
embedding `ComplexShape.embeddingUpIntDownInt`, i.e. the functor of Mathlib's
`ChainComplex.cochainComplexEquivalence`.
Source: node statement, check K (blueprint: lem-sfb-boolean-coatom-excision-derived). -/
def reversal : ChainComplex (ModuleCat.{u} ℚ) ℤ ⥤ CochainComplex (ModuleCat.{u} ℚ) ℤ :=
  ComplexShape.embeddingUpIntDownInt.restrictionFunctor (ModuleCat.{u} ℚ)

/-- The identity after the equality -q-1 = -(q+1), without a change of sign.
Source: node proof step 6 (blueprint: lem-sfb-boolean-coatom-excision-derived). -/
def reversalSuspensionComponent (K : ChainComplex (ModuleCat.{u} ℚ) ℤ) (q : ℤ) :
    (reversal.obj (suspension K)).X q ≅ (reversal.obj K)⟦(1 : ℤ)⟧.X q :=
  K.XIsoOfEq (p := -q - 1) (q := -(q + 1)) (by omega)

/-- The identity comparison from reversed suspension to cochain shift is a chain map.
Source: node proof step 6 (blueprint: lem-sfb-boolean-coatom-excision-derived).

Proof: both terms are K_(-q-1). Both differentials are -d_K: one from the
specified chain suspension, the other from Mathlib's cochain shift by 1. The
component equalities only reassociate integer indices, so the square commutes. -/
theorem reversalSuspension_comm (K : ChainComplex (ModuleCat.{u} ℚ) ℤ)
    (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    (reversalSuspensionComponent K i).hom ≫ (reversal.obj K)⟦(1 : ℤ)⟧.d i j =
      (reversal.obj (suspension K)).d i j ≫ (reversalSuspensionComponent K j).hom := by
  obtain rfl : i + 1 = j := hij
  rw [CochainComplex.shiftFunctor_obj_d']
  dsimp only [reversalSuspensionComponent, reversal, suspension,
    ComplexShape.Embedding.restrictionFunctor, HomologicalComplex.restriction,
    ComplexShape.embeddingUpIntDownInt]
  simp

/-- The canonical identification of reversed suspension with cochain shift by 1.
Source: node proof step 6 (blueprint: lem-sfb-boolean-coatom-excision-derived). -/
def reversalSuspensionIso (K : ChainComplex (ModuleCat.{u} ℚ) ℤ) :
    reversal.obj (suspension K) ≅ (reversal.obj K)⟦(1 : ℤ)⟧ :=
  HomologicalComplex.Hom.isoOfComponents (reversalSuspensionComponent K)
    (reversalSuspension_comm K)

/-- The exact derived arrow in the node, including Q's canonical commutation with shift.
Source: node statement, Q(check theta composed with check p), and proof step 6
(blueprint: lem-sfb-boolean-coatom-excision-derived). -/
def derivedComparison [HasDerivedCategory.{w} (ModuleCat.{u} ℚ)]
    (a : E) (hcard : 2 ≤ Fintype.card E) :
    DerivedCategory.Q.obj (reversal.obj (booleanComplex (Finset.univ : Finset E))) ⟶
      (DerivedCategory.Q.obj (reversal.obj (booleanComplex (coatom a))))⟦(1 : ℤ)⟧ :=
  DerivedCategory.Q.map
    (reversal.map (projection a ≫ (theta a hcard).hom) ≫
      (reversalSuspensionIso (booleanComplex (coatom a))).hom) ≫
    ((DerivedCategory.Q (C := ModuleCat.{u} ℚ)).commShiftIso (1 : ℤ)).hom.app
      (reversal.obj (booleanComplex (coatom a)))

/-- All clauses of derived Boolean coatom excision, with the specified chain representative.
Source: agent-written extraction from direct-images paragraph (3), context only,
node proof steps 1--6 (blueprint: lem-sfb-boolean-coatom-excision-derived).

Proof: (1) Put e={a}, u(S)=S union {a}. The singleton is proper since |E|>=2.
If u(S)=E then S=v or E, both excluded. Thus u stays in D, is monotone, and
is pointwise above the identity and e. (2) Apply lem-sfb-poset-augmented-chain-prism
to id<=u and const_e<=u. Subtract the prisms and add t_(-1)[empty]=[e]. The
result satisfies dt+td=id in every degree, including 0 and -1. Cycles are
boundaries, so the homology objects of C(D) vanish. (3) Chains avoiding v are
a deletion-closed subset of the basis. Inclusion is injective and fixes the empty
generator. The quotient is free on chains ending in v and zero in negative degrees.
(4) Signed deletion descends to theta: the quotient differential drops all vertices
except v; its signs become (-1)^(n-1)d, equal to -(-1)^n d in the suspension.
The inverse appends v and uses the same sign. (5) The short exact sequence of
complexes and lem-weil-pbc-complex-ses-homology-long-exact imply that p is a
quasi-isomorphism after reversal, since C(D) is acyclic. (6) Reversed suspension
is exactly cochain shift by 1. Compose check p with check theta, apply Q, and use
Q's canonical shift isomorphism. Localization inverts that quasi-isomorphism,
which is the claimed derivedComparison. The bracket formula includes all basis
vectors, the vertex [v], and the empty and negative degrees. -/
theorem excision [HasDerivedCategory.{w} (ModuleCat.{u} ℚ)]
    (a : E) (hcard : 2 ≤ Fintype.card E) :
    (∃ (e : Deleted a) (f : Deleted a →o Deleted a),
      e.val.val = {a} ∧
      (∀ S : Deleted a, (f S).val.val = insert a S.val.val) ∧
      (∀ S : Deleted a, S ≤ f S ∧ e ≤ f S)) ∧
    (∀ n : ℤ, IsZero ((complex ℚ (Deleted a)).homology n)) ∧
    (∀ n : ℤ, Function.Injective ((inclusion a).f n)) ∧
    ((inclusion a).f (-1) (bracket ℚ (-1) ([] : List (Deleted a))) =
      bracket ℚ (-1) ([] : List (Proper (Finset.univ : Finset E)))) ∧
    (∀ n : ℤ, n < 0 → IsZero ((quotientComplex a).X n) ∧
      IsZero ((suspension (booleanComplex (coatom a))).X n)) ∧
    (∀ (n : ℤ) (c : Simplex (Proper (Finset.univ : Finset E)) n),
      (theta a hcard).hom.f n ((projection a).f n (Finsupp.single c 1)) =
        signedDeletion a n (Finsupp.single c 1)) ∧
    IsIso (derivedComparison a hcard) := by
  sorry

end AlgebraicTopology.AugmentedPosetChains.BooleanCoatom
