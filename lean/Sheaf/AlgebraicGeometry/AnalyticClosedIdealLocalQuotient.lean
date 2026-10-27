/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q44
-/
module

public import Sheaf.AlgebraicGeometry.SmoothAnalytificationCotangent
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
import Sheaf.AlgebraicGeometry.ConormalSequenceSmoothImmersion
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.StalkTensor
import WeilConjectures.Topology.InverseImageStalk
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-! # The analytic local quotient of a smooth closed algebraic subvariety

Source: Serre, GAGA, no. 6, Proposition 4, pp. 10--11, and no. 10, Proposition 11,
p. 18 (blueprint: lem-sfb-analytic-closed-ideal-local-quotient).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.SmoothAnalytic

/-- Extend the algebraic defining ideal to the ambient analytic stalk. The stalk
congruence only identifies the two names for the ambient algebraic point.
Source: Serre, GAGA, no. 6, Proposition 4
(blueprint: lem-sfb-analytic-closed-ideal-local-quotient). -/
noncomputable def closedIdeal {X Y : Scheme.{u}}
    {f : X ⟶ Spec (.of (ULift.{u} ℂ))} {g : Y ⟶ Spec (.of (ULift.{u} ℂ))}
    (D : Data f) (E : Data g) (i : Over.mk f ⟶ Over.mk g)
    (j : D.space ⟶ E.space)
    (hπ : ∀ x : D.space, i.left (D.pi.hom.base x) = E.pi.hom.base (j.hom.base x))
    (x : D.space) : Ideal (E.space.presheaf.stalk (j.hom.base x)) :=
  Ideal.map (E.pi.hom.stalkMap (j.hom.base x)).hom
    (Ideal.map (Y.presheaf.stalkCongr (.of_eq (hπ x))).hom.hom
      (RingHom.ker (i.left.stalkMap (D.pi.hom.base x)).hom))

/-- The analytic restriction along a smooth closed algebraic immersion is surjective
on stalks, and its kernel is the extended algebraic defining ideal. The ring equivalence
is characterized on every quotient class; consequently it is an equivalence of algebras
over the ambient analytic stalk, with the action on the target given by restriction.
The analytic morphism is specified by its complex-point map and by pullback of functions.

Source: Serre, GAGA, no. 6, Proposition 4, pp. 10--11, and no. 10, Proposition 11,
p. 18 (blueprint: lem-sfb-analytic-closed-ideal-local-quotient).

Proof plan (the node's six steps):
1. Use lem-sfb-smooth-analytification-cotangent to obtain the holomorphic embedding.
   Pullback of functions constructs j, with the displayed evaluation formula and
   compatibility of the scheme points. Restriction commutes with the algebraic maps,
   so the extended ideal lies in the analytic kernel. Complex-point residue fields
   are C. Use lem-pc-ringed-space-module-stalk-tensor and
   lem-weil-pbc-topological-inverse-image-stalk to identify analytified cotangent
   fibres with analytic cotangent spaces, compatibly with regular differentials.
2. Apply lem-pur-conormal-sequence-smooth-immersion to choose algebraic ideal elements
   whose differentials form a basis of the normal cotangent space.
3. Complete these to ambient coordinates, using constant linear combinations of chart
   coordinates. Apply lem-sfb-complex-analytic-function-operations,
   lem-sfb-complex-analytic-derivative-rules and lem-sfb-complex-analytic-inverse-toolkit
   on both source and ambient manifolds to obtain normal and tangential coordinates.
4. Shrink the coordinate neighbourhoods. The embedding has expression t maps to (0,t):
   normal coordinates vanish and tangential coordinates identify the source. Its image
   on a smaller product neighbourhood is exactly the coordinate slice.
5. Extend a source holomorphic germ independently of the normal coordinates to prove
   surjectivity. Apply lem-sfb-holomorphic-coordinate-division to a germ vanishing on
   the slice, and compose with the ambient coordinates to express it as a sum of the
   selected algebraic equations times holomorphic germs. This proves kernel equality.
6. Factor restriction through the quotient. Kernel equality gives injectivity and
   surjectivity gives surjectivity of the factor, hence the stated ring equivalence.
   Its formula on quotient classes makes it linear over the ambient stalk. Empty
   source, zero normal dimension and zero tangential dimension are all allowed. -/
theorem exists_analyticClosedIdealLocalQuotient {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of (ULift.{u} ℂ))) (g : Y ⟶ Spec (.of (ULift.{u} ℂ)))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [Smooth f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] [Smooth g]
    (D : Data f) (E : Data g) (i : Over.mk f ⟶ Over.mk g) [IsClosedImmersion i.left] :
    ∃ (j : D.space ⟶ E.space)
      (hπ : ∀ x : D.space, i.left (D.pi.hom.base x) = E.pi.hom.base (j.hom.base x)),
      (∀ x : D.space, j.hom.base x = mapPoints D E i x) ∧
      (∀ (U : Opens E.space) (a : E.space.presheaf.obj (op U))
        (x : (Opens.map j.hom.base).obj U),
        D.functions.eval _ (j.hom.c.app (op U) a) x =
          E.functions.eval U a ⟨j.hom.base x.val, x.property⟩) ∧
      ∀ x : D.space,
        Function.Surjective (j.hom.stalkMap x).hom ∧
        RingHom.ker (j.hom.stalkMap x).hom = closedIdeal D E i j hπ x ∧
        ∃ e : (E.space.presheaf.stalk (j.hom.base x)) ⧸ closedIdeal D E i j hπ x ≃+*
            D.space.presheaf.stalk x,
          ∀ b : E.space.presheaf.stalk (j.hom.base x),
            e (Ideal.Quotient.mk (closedIdeal D E i j hπ x) b) = j.hom.stalkMap x b := by
  sorry

end AlgebraicGeometry.SmoothAnalytic
