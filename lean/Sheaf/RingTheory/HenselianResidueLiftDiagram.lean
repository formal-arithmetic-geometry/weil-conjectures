/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.FieldTheory.Galois.GaloisClosure
public import Mathlib.Algebra.Category.CommAlgCat.Basic

import Sheaf.RingTheory.HenselianFiniteEtaleFieldLift
import Sheaf.RingTheory.HenselianFiniteEtaleMapBijective
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Coherent finite étale lifts of residue subfields

Source: Stacks Project, Algebra, Tags 0BSL and 04GK; Fields, Tags 09DT and 0EXM;
Categories, Tag 002F (blueprint: lem-wf-henselian-residue-lift-diagram).

A surjective ring map with kernel `m B` and the specified scalar equation is exactly
an identification `B / m B ≃ₐ[k] e`. We use this quotient-map presentation throughout.
The indexing subtype is small by its type, and separability of every intermediate field
follows from the specified separable closure. Functor laws give identity and composition.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace Algebra

/-- Finite residue subfields admit finite étale local lifts and unique compatible arrows.
Source: Stacks Project, Algebra, Tags 0BSL and 04GK
(blueprint: lem-wf-henselian-residue-lift-diagram).

Proof, steps 1--4 of the node: identify `k ⊗[H] B` with `B / m B` by sending
`h̄ ⊗ b` to `hb` and `b` to `1 ⊗ b`. Apply
`lem-weil-pbc-henselian-finite-etale-field-lift` to every finite subfield, and choose
these lifts over the set of intermediate fields. The finite-algebra radical lemma
`lem-weil-pbc-finite-algebra-local-radical` puts every maximal ideal over `m`; since
the specified quotient is a field, `m B` is the unique maximal ideal. Its contraction
is `m`, so the structural map is local. Full faithfulness
`lem-weil-pbc-henselian-finite-etale-map-bijective` lifts every inclusion uniquely.
The inclusion of residue fields is injective, making each lift local. Identities
and composites reduce to the corresponding inclusions; injectivity of reduction gives
the functor laws. Uniqueness here is among all algebra maps, with no locality assumption. -/
theorem exists_henselian_residue_lift_diagram
    (H K : Type u) [CommRing H] [HenselianLocalRing H] [Field K]
    [Algebra (IsLocalRing.ResidueField H) K]
    [IsSepClosure (IsLocalRing.ResidueField H) K] :
    ∃ D : {e : IntermediateField (IsLocalRing.ResidueField H) K //
        FiniteDimensional (IsLocalRing.ResidueField H) e} ⥤ CommAlgCat.{u} H,
      ∃ q : ∀ e, D.obj e →+* e.val,
        (∀ e, Module.Finite H (D.obj e)) ∧
        (∀ e, Algebra.Etale H (D.obj e)) ∧
        (∀ e, Function.Surjective (q e)) ∧
        (∀ e, RingHom.ker (q e) =
          (IsLocalRing.maximalIdeal H).map (algebraMap H (D.obj e))) ∧
        (∀ e h, q e (algebraMap H (D.obj e) h) =
          algebraMap (IsLocalRing.ResidueField H) e.val (IsLocalRing.residue H h)) ∧
        (∃ loc : ∀ e, IsLocalRing (D.obj e),
          (∀ e, @IsLocalRing.maximalIdeal (D.obj e) _ (loc e) =
            (IsLocalRing.maximalIdeal H).map (algebraMap H (D.obj e))) ∧
          (∀ e, IsLocalHom (algebraMap H (D.obj e)))) ∧
        (∀ {e f} (t : e ⟶ f) b,
          (q f ((D.map t).hom b) : K) = (q e b : K)) ∧
        (∀ {e f} (t : e ⟶ f), IsLocalHom (D.map t).hom.toRingHom) ∧
        (∀ {e f} (t : e ⟶ f) (g : D.obj e →ₐ[H] D.obj f),
          (∀ b, (q f (g b) : K) = (q e b : K)) → g = (D.map t).hom) := by
  sorry

/-- Any two identified finite étale lifts have exactly one compatible algebra isomorphism.
Source: Stacks Project, Algebra, Tag 04GK, full faithfulness, and Tag 0BSL
(blueprint: lem-wf-henselian-residue-lift-diagram).

Proof, step 4: the two quotient maps identify the fibres with the same subfield `e`.
By `lem-weil-pbc-henselian-finite-etale-map-bijective`, lift the identity on `e`
in both directions. Each composite reduces to the identity, so injectivity of
reduction makes both composites identities. Thus the lifted map is an isomorphism,
and the same injectivity gives uniqueness among all residue-compatible isomorphisms.
No local-ring hypothesis is imposed on the lifts: it follows from their finite
module structure and field quotients as in step 2. -/
theorem henselian_residue_lift_unique
    (H K : Type u) [CommRing H] [HenselianLocalRing H] [Field K]
    [Algebra (IsLocalRing.ResidueField H) K]
    [IsSepClosure (IsLocalRing.ResidueField H) K]
    (e : IntermediateField (IsLocalRing.ResidueField H) K)
    [FiniteDimensional (IsLocalRing.ResidueField H) e]
    (B C : Type u) [CommRing B] [CommRing C] [Algebra H B] [Algebra H C]
    [Module.Finite H B] [Module.Finite H C] [Algebra.Etale H B] [Algebra.Etale H C]
    (qB : B →+* e) (qC : C →+* e)
    (hB : Function.Surjective qB) (hC : Function.Surjective qC)
    (hkerB : RingHom.ker qB = (IsLocalRing.maximalIdeal H).map (algebraMap H B))
    (hkerC : RingHom.ker qC = (IsLocalRing.maximalIdeal H).map (algebraMap H C))
    (hscalarB : ∀ h, qB (algebraMap H B h) =
      algebraMap (IsLocalRing.ResidueField H) e (IsLocalRing.residue H h))
    (hscalarC : ∀ h, qC (algebraMap H C h) =
      algebraMap (IsLocalRing.ResidueField H) e (IsLocalRing.residue H h)) :
    ∃! i : B ≃ₐ[H] C, ∀ b, qC (i b) = qB b := by
  sorry

/-- Finite Galois subfields are a directed cofinal full subposet of the finite subfields.
Source: Stacks Project, Fields, Tags 09DT, 0BMG and 0EXM
(blueprint: lem-wf-henselian-residue-lift-diagram).

Proof, step 5: the chosen separable closure is Galois by
`lem-weil-pbc-separable-closure-exists-galois`. Apply
`lem-weil-pbc-finite-set-in-finite-galois-subextension` to the union of bases of two
finite subfields to enclose both in a finite Galois subfield of the specified `K`.
The base field is an object, so both posets are nonempty and directed. Taking the
second subfield to be the base proves cofinality. The same enclosure argument shows
that every upper subposet of Galois overfields is directed, not just nonempty.
`Normal` means algebraicity and splitting of every minimal polynomial; separability
is inherited from `K`, so this is precisely the Galois subposet of the node. -/
theorem henselian_residue_lift_galois_cofinal
    (H K : Type u) [CommRing H] [HenselianLocalRing H] [Field K]
    [Algebra (IsLocalRing.ResidueField H) K]
    [IsSepClosure (IsLocalRing.ResidueField H) K] :
    IsFiltered {e : IntermediateField (IsLocalRing.ResidueField H) K //
      FiniteDimensional (IsLocalRing.ResidueField H) e} ∧
    IsFiltered (ObjectProperty.FullSubcategory
      (fun e : {e : IntermediateField (IsLocalRing.ResidueField H) K //
          FiniteDimensional (IsLocalRing.ResidueField H) e} ↦
        Normal (IsLocalRing.ResidueField H) e.val)) ∧
    (∀ e : {e : IntermediateField (IsLocalRing.ResidueField H) K //
        FiniteDimensional (IsLocalRing.ResidueField H) e},
      ∃ f : {e : IntermediateField (IsLocalRing.ResidueField H) K //
          FiniteDimensional (IsLocalRing.ResidueField H) e},
        Normal (IsLocalRing.ResidueField H) f.val ∧ e ≤ f) := by
  sorry

/-- Restricting any chosen lift diagram to its Galois subfields preserves cocones and colimits.
Source: Stacks Project, Algebra, Tag 0BSL; Fields, Tags 09DT and 0EXM;
Categories, Tag 002F (blueprint: lem-wf-henselian-residue-lift-diagram).

Proof, steps 6--7: given a compatible family on Galois subfields with vertex `T`,
extend its leg at `e` by composing the leg at a Galois overfield `g` with `u_eg`.
For another choice `g'`, put both in a common Galois overfield and use compatibility
and the functor composition law. Thus extension is well defined, compatible, and
inverse to restriction. This proves the asserted bijection for each vertex.
By `lem-weil-pbc-commutative-algebras-colimits-exist`, choose an algebra colimit `c`.
The cocone bijection makes its restriction a colimit too. Uniqueness of colimits
produces the unique comparison with every other restricted colimit, characterized
on all legs. The maps `B_e → e → K` form a compatible cocone by the residue equation;
its induced map `ρ` commutes with the comparison, by checking this on the Galois legs.
All comparison arrows belong to `CommAlgCat H`, so they preserve the `H` structure. -/
theorem henselian_residue_lift_galois_cocones
    (H K : Type u) [CommRing H] [HenselianLocalRing H] [Field K]
    [Algebra (IsLocalRing.ResidueField H) K]
    [IsSepClosure (IsLocalRing.ResidueField H) K]
    (D : {e : IntermediateField (IsLocalRing.ResidueField H) K //
      FiniteDimensional (IsLocalRing.ResidueField H) e} ⥤ CommAlgCat.{u} H)
    (q : ∀ e, D.obj e →+* e.val)
    (hfinite : ∀ e, Module.Finite H (D.obj e))
    (hetale : ∀ e, Algebra.Etale H (D.obj e))
    (hsurj : ∀ e, Function.Surjective (q e))
    (hker : ∀ e, RingHom.ker (q e) =
      (IsLocalRing.maximalIdeal H).map (algebraMap H (D.obj e)))
    (hscalar : ∀ e h, q e (algebraMap H (D.obj e) h) =
      algebraMap (IsLocalRing.ResidueField H) e.val (IsLocalRing.residue H h))
    (hcompat : ∀ {e f} (t : e ⟶ f) b,
      (q f ((D.map t).hom b) : K) = (q e b : K)) :
    (∀ T : CommAlgCat.{u} H,
      Function.Bijective (fun a : D ⟶ (Functor.const _).obj T ↦
        Functor.whiskerLeft (ObjectProperty.ι
          (fun e : {e : IntermediateField (IsLocalRing.ResidueField H) K //
            FiniteDimensional (IsLocalRing.ResidueField H) e} ↦
          Normal (IsLocalRing.ResidueField H) e.val)) a)) ∧
    ∃ c : Cocone D, Nonempty (IsColimit c) ∧
      Nonempty (IsColimit (c.whisker (ObjectProperty.ι
        (fun e : {e : IntermediateField (IsLocalRing.ResidueField H) K //
            FiniteDimensional (IsLocalRing.ResidueField H) e} ↦
          Normal (IsLocalRing.ResidueField H) e.val)))) ∧
      ∃ ρ : c.pt →+* K,
        (∀ e b, ρ ((c.ι.app e).hom b) = (q e b : K)) ∧
        ∀ c' : Cocone ((ObjectProperty.ι
            (fun e : {e : IntermediateField (IsLocalRing.ResidueField H) K //
            FiniteDimensional (IsLocalRing.ResidueField H) e} ↦
          Normal (IsLocalRing.ResidueField H) e.val)) ⋙ D),
          IsColimit c' → ∃! i : c'.pt ≅ c.pt,
            (∀ g, c'.ι.app g ≫ i.hom = c.ι.app g.obj) ∧
            (∀ ρ' : c'.pt →+* K,
              (∀ g b, ρ' ((c'.ι.app g).hom b) = (q g.obj b : K)) →
              ρ.comp i.hom.hom.toRingHom = ρ') := by
  sorry

end Algebra
