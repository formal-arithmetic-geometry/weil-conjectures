/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q138
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.Topology.JacobsonSpace
import Sheaf.AlgebraicGeometry.UnramifiedMorphism
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Sheaf.AlgebraicGeometry.UnramifiedMaximalIdealResidueCriterion
import Sheaf.TraceFormula.FiniteResiduePointClosedInFibre
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Localization.Submodule
import Sheaf.RingTheory.FlatLocalCompletionIso

/-!
# Étale invariance of completed local rings at rational points

Source: Stacks Project, Morphisms, Tags 02GL and 01TE; More on Algebra, Tag 0AGX;
Étale Morphisms, Tag 039M and the following remark; Curves, proof of Tag 0C57
(blueprint: lem-trf-etale-completed-local-ring-iso).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An étale morphism over an algebraically closed field preserves the residue field and
completed local ring whenever either structural residue-field map is an isomorphism;
both points are then closed. The completed map is specified on every residue class at
every power of the maximal ideal, so the existential map is uniquely determined.

Source: Stacks Project, Morphisms, Tags 02GL, 02GF and 01TE; More on Algebra, Tag 0AGX;
Étale Morphisms, Tag 039M and its following remark; Curves, proof of Tag 0C57.
(blueprint: lem-trf-etale-completed-local-ring-iso).

Proof:
1. Put A = O_{C,e(y)} and B = O_{D,y}. Étaleness gives flatness, unramifiedness and
   local finite type. The actual stalk map is a flat local homomorphism
   (def-weil-etale-morphism, def-weil-unramified-morphism, def-weil-flat-morphism).
2. Apply lem-trf-unramified-maximal-ideal-residue-criterion with the whole source D
   as neighbourhood: m_A B = m_B and the actual residue extension is finite separable.
3. Let i : k -> kappa(e(y)), j : k -> kappa(y), and alpha be the induced residue map.
   Functoriality gives j = alpha i (def-weil-residue-field). If i is bijective, the finite
   extension is algebraic over k, so lem-weil-pbc-algebraic-over-algebraically-closed-subfield
   makes j and alpha surjective. All field maps are injective. If instead j is bijective,
   for a in kappa(e(y)) choose c with j(c) = alpha(a); injectivity of alpha gives i(c) = a.
   Thus both structural maps and alpha are bijective in either case.
4. Apply lem-trf-finite-residue-point-closed-in-fibre to C -> Spec k: e(y) is closed in
   its fibre. Spec k has one point (def-weil-affine-spectrum), and its fibre is homeomorphic
   to C (def-pc-scheme-fibre), so e(y) is closed in C.
5. Apply the same closed-fibre lemma to e at y. Its residue extension is finite. The fibre
   is homeomorphic to e^{-1}({e(y)}) (def-pc-scheme-fibre), a closed subspace of D by step 4.
   Hence y is closed in D.
6. A field is Noetherian. By pqf-def-locnoeth and pqf-lem-locnoeth-lft, first C and then D
   are locally Noetherian. Choose affine Noetherian neighbourhoods; their stalks are
   localizations by lem-weil-pbc-affine-open-stalk-localization. Applying
   lem-weil-pbc-localization-noetherian shows A and B are Noetherian local rings.
7. Apply lem-weil-pbc-flat-local-completion-iso to the actual stalk map. Step 1 gives
   flatness and locality, step 2 the maximal-ideal equality, step 3 the residue isomorphism,
   and step 6 Noetherianity. The theorem supplies a bijective completed map with exactly
   the displayed coordinate formula, which uniquely specifies the induced map. -/
theorem etale_completedLocalRing_iso
    {k : Type u} [Field k] [IsAlgClosed k]
    {C D : Scheme.{u}} (f : C ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (e : D ⟶ C) [Etale e] (y : D)
    (hres :
      Function.Bijective
        (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ C.Γevaluation (e y)).hom) ∨
      Function.Bijective
        (((Scheme.ΓSpecIso (.of k)).inv ≫ (e ≫ f).appTop ≫ D.Γevaluation y).hom)) :
    e y ∈ closedPoints C ∧ y ∈ closedPoints D ∧
      IsIso (e.residueFieldMap y) ∧
      ∃ (ehat :
          AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk (e y)))
              (C.presheaf.stalk (e y)) →+*
            AdicCompletion (IsLocalRing.maximalIdeal (D.presheaf.stalk y))
              (D.presheaf.stalk y)),
        (∀ (n : ℕ)
          (z : AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk (e y)))
            (C.presheaf.stalk (e y))) (a : C.presheaf.stalk (e y)),
          AdicCompletion.evalₐ (IsLocalRing.maximalIdeal (C.presheaf.stalk (e y))) n z =
              Ideal.Quotient.mk (IsLocalRing.maximalIdeal (C.presheaf.stalk (e y)) ^ n) a →
          AdicCompletion.evalₐ (IsLocalRing.maximalIdeal (D.presheaf.stalk y)) n (ehat z) =
              Ideal.Quotient.mk (IsLocalRing.maximalIdeal (D.presheaf.stalk y) ^ n)
                ((e.stalkMap y).hom a)) ∧
        Function.Bijective ehat := by
  sorry

end AlgebraicGeometry
