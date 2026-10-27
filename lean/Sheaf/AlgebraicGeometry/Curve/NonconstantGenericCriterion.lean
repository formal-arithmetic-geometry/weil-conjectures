module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.Sober
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback
public import WeilConjectures.ZetaSeries

import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.ClosedPointField
import WeilConjectures.AlgebraicGeometry.RationalFunctionsGenericStalks
import WeilConjectures.Topology.PresheafModuleStalkFunctor

/-!
# Nonconstancy detected at the generic point of a curve

Source: Stacks Project, Curves, Tag 0BY1 (theorem-curves-rational-maps),
the paragraph defining constant morphisms and the third proof paragraph
(blueprint: lem-sfb-curve-nonconstant-generic-criterion).

The source scheme is any integral scheme over the base field. The constant case includes
its singleton closed image, the canonical residue-field identification, and factorization
through a rational point. The nonconstant case uses the existing generic stalk map and
specifies both compatibility with constants and the pullback formula on all germs.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A morphism from an integral scheme to a smooth integral dimension-one curve over an
algebraically closed field is nonconstant exactly when it preserves generic points.

Source: Stacks Project, Curves, Tag 0BY1 (theorem-curves-rational-maps),
the paragraph defining constant morphisms and the third proof paragraph;
Morphisms, Tags 01TF and 01RV; Schemes, Tag 0356
(blueprint: lem-sfb-curve-nonconstant-generic-criterion).

Proof plan, following the five steps of the node:
1. Every point of T specializes from its generic point. Continuity puts the whole image
   in the closure of y = u(eta_T). If y is not generic, a further distinct specialization
   would give a chain of irreducible closed subsets of C of length two, contradicting
   dimension one (def-sc-generic-point, lem-sc-scheme-sober,
   def-kun-topological-krull-dimension). Thus the image is the closed singleton {y}.
2. Finite type over the algebraically closed field identifies the residue field at y
   with k (lem-weil-pbc-closed-point-residue-field-base). The residue-field point is a
   closed immersion, locally the quotient by the maximal ideal. Transporting it along
   the structural residue-field isomorphism gives a section c of sC.
3. Integrality makes T reduced. Apply
   lem-weil-pbc-reduced-source-factors-through-closed-subscheme to factor u through c.
   Composing with sC identifies the factor T to Spec k with sT.
4. Conversely, a factorization through a k-point makes the residue extension at its image
   equal to k. The closed-point criterion lem-kun-closed-point-field makes this image
   closed. A closed generic point would make C a singleton of dimension zero, so the
   generic image is not generic. This proves the equivalence.
5. If u preserves generic points, its actual stalk map is a unital map between fields
   (lem-sc-rational-functions-generic-stalks, def-sc-function-field), hence injective.
   The equation u followed by sC equals sT gives compatibility with the canonical maps
   from k. Functoriality of germs gives the displayed formula on every local section
   (def-weil-pbc-module-stalk). -/
theorem curve_nonconstant_generic_criterion
    (k : Type u) [Field k] [IsAlgClosed k]
    (T C : Scheme.{u}) (sT : T ⟶ Spec (.of k)) (sC : C ⟶ Spec (.of k))
    [IsIntegral T] [IsIntegral C] [IsCurve sC] [Smooth sC]
    (hCdim : topologicalKrullDim C = 1) (u : T ⟶ C) (hu : u ≫ sC = sT) :
    (u (genericPoint T) = genericPoint C ↔
      ¬ ∃ c : Spec (.of k) ⟶ C, c ≫ sC = 𝟙 _ ∧ sT ≫ c = u) ∧
    (u (genericPoint T) ≠ genericPoint C →
      IsClosed ({u (genericPoint T)} : Set C) ∧
      Set.range u = {u (genericPoint T)} ∧
      Function.Bijective (sC.residueFieldAlgebraMap (u (genericPoint T))) ∧
      ∃ c : Spec (.of k) ⟶ C, c ≫ sC = 𝟙 _ ∧ sT ≫ c = u) ∧
    (∀ h : u (genericPoint T) = genericPoint C,
      Function.Injective (u.functionFieldMap h).hom ∧
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sC.appTop ≫
        C.presheaf.germ ⊤ (genericPoint C) trivial ≫ u.functionFieldMap h) =
        ((Scheme.ΓSpecIso (.of k)).inv ≫ sT.appTop ≫
          T.presheaf.germ ⊤ (genericPoint T) trivial) ∧
      ∀ (U : C.Opens) (hU : genericPoint C ∈ U) (a : Γ(C, U)),
        u.functionFieldMap h (C.presheaf.germ U (genericPoint C) hU a) =
          T.presheaf.germ (u ⁻¹ᵁ U) (genericPoint T)
            (Eq.mpr (congrArg (fun x : C ↦ x ∈ U) h) hU) (u.app U a)) := by
  sorry

end AlgebraicGeometry
