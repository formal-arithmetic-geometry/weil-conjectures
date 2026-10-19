/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.AlgebraicGeometry.NormalScheme
public import Sheaf.AlgebraicGeometry.AdmissibleFiniteSchemeQuotient
public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback
public import Mathlib.FieldTheory.Galois.Basic
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
import Sheaf.AlgebraicGeometry.AffineGroupoidOrbitFibres
import Sheaf.AlgebraicGeometry.FiniteFlatAffineRelationQuotient
import WeilConjectures.AlgebraicGeometry.FpqcDescentEtale
import Sheaf.AlgebraicGeometry.UnramifiedMorphism
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree

/-!
# The free open locus of a finite scheme quotient

Source: ILO, Travaux de Gabber, Expose IX, 1.4, pp. 132--133, situation (*);
Stacks Project, Tags 03BL, 03BM, 07S7 and 09I3
(blueprint: lem-per-free-finite-action-torsor).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- The function-field clause for the given quotient and action. The algebra is required
to be the actual generic stalk map, and the Galois-group identification is required to be
pullback by the inverse of the given action. Quantifying over algebra structures with this
equality does not add data: the ring homomorphism always supplies its `toAlgebra` structure.
Source: ILO IX 1.4, situation (*); Stacks Project, Tag 09I3
(blueprint: lem-per-free-finite-action-torsor). -/
def Scheme.Hom.HasGaloisFunctionFieldAction {G : Type v} [Group G]
    {C Y : Scheme.{u}} [IsIntegral C] [IsIntegral Y]
    (a : G →* Aut C) (q : C ⟶ Y) : Prop :=
  ∃ hη : q (genericPoint C) = genericPoint Y,
    ∀ [Algebra Y.functionField C.functionField],
      algebraMap Y.functionField C.functionField = (q.functionFieldMap hη).hom →
      IsGalois Y.functionField C.functionField ∧
      FiniteDimensional Y.functionField C.functionField ∧
      ∃ ρ : G ≃* (C.functionField ≃ₐ[Y.functionField] C.functionField),
        ∀ g : G, ∃ hg : (a g⁻¹).hom (genericPoint C) = genericPoint C,
          (ρ g).toRingHom = ((a g⁻¹).hom.functionFieldMap hg).hom

/-- A finite quotient restricts on its geometric free locus to the given finite etale
G-torsor, with orbit quotient topology. The torsor identification respects the actual
inclusion and the original action. In the separated case its dense base has the stated
Galois function-field extension.
Source: ILO, Expose IX, 1.4, pp. 132--133, situation (*)
(blueprint: lem-per-free-finite-action-torsor).

Proof, following the ten steps of the node:
1. On an affine D in Y, finiteness makes q⁻¹D affine, say Spec B, and the invariant
   sheaf identifies D with Spec(B^G). The constant action groupoid has source and target
   finite locally free: its algebra is a product of copies of B, with twisted target maps.
2. Apply lem-a1-affine-groupoid-orbit-fibres. Ordinary and geometric fibres are orbits,
   and q is surjective. Every fibre meeting the stable U is contained in U.
3. Finiteness makes q closed (lem-weil-pbc-finite-closed-map-finite-fibres). Thus q(U)
   is the complement of q(C minus U), hence open, and its inverse image is U. The
   open-subscheme universal property gives the displayed pullback square. Finiteness
   of the restriction follows from lem-weil-pbc-finite-morphism-permanence.
4. Geometric freeness implies freeness on every test scheme: on each clopen part where
   two group labels are constant, a point and an algebraic closure of its residue field
   detect equality of the labels. This also handles the empty test scheme. The action
   relation is consequently a monomorphism and an equivalence relation.
5. Apply lem-a1-finite-flat-affine-relation-quotient over each affine in q(U). Its
   invariant ring is the given base ring, so the restricted quotient is finite locally
   free and surjective, and G times U is its kernel pair. The comparison is the actual
   action and projection, so the local identifications glue uniquely.
6. This flat affine surjection is an fpqc covering. After pulling back along itself,
   the map is the disjoint union of identity maps indexed by G, hence etale. Apply
   lem-galois-fpqc-descend-etale to descend etaleness.
7. The kernel-pair identification gives simple transitivity on every geometric fibre.
   The finite surjection is closed, giving the quotient topology and ordinary orbit
   fibres. Restrict the invariant sheaf to q(U); the categorical quotient follows by
   descent. These data give GaloisCoverAction with its specified compatibility equations.
8. Every nonempty open of Y has nonempty open inverse image and therefore meets q(U).
   Each nonempty affine base ring is an invariant subring of a domain, so Y is integral.
9. By lem-sc-integral-function-field-affine-fraction, the generic stalks are the fraction
   fields of these affine rings. For an invariant fraction b/c, multiply its denominator
   by all its G-translates. The product is invariant and nonzero, and the resulting
   numerator is invariant too. Thus the fixed field is exactly the base function field.
10. Use inverse pullback for the left field action. An element acting trivially fixes
   the geometric generic point, which lies in U, so geometric freeness makes it 1.
   Apply lem-wf-finite-field-action-fixed-degree and
   lem-weil-pbc-finite-galois-fixed-field: the field extension is finite Galois and its
   automorphism group has order |G|. The faithful induced map from G is therefore an
   isomorphism, with the prescribed inverse-pullback formula. -/
theorem free_finite_action_torsor
    {G : Type v} [Group G] [Finite G]
    {C Y : Scheme.{u}} [IsIntegral C] [IsNoetherian C] [IsNoetherian Y]
    (a : G →* Aut C)
    (_hexc : ∀ W : C.affineOpens, IsExcellent Γ(C, W))
    (U : C.Opens) (_hdense : Dense (U : Set C))
    (_hstable : ∀ (g : G) (c : C), c ∈ U → (a g).hom c ∈ U)
    (_hfree : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (x : Spec (.of Ω) ⟶ U.toScheme) (g : G),
      x ≫ U.ι ≫ (a g).hom = x ≫ U.ι → g = 1)
    (q : C ⟶ Y) (_hquotient : IsAdmissibleFiniteSchemeQuotient a q) :
    ∃ V : Y.Opens, (V : Set Y) = q '' (U : Set C) ∧ q ⁻¹ᵁ V = U ∧
      ∃ p : U.toScheme ⟶ V.toScheme,
        IsPullback U.ι p q V.ι ∧ IsFinite p ∧ Etale p ∧
        ∃ aU : G →* Aut U.toScheme,
          (∀ g : G, (aU g).hom ≫ U.ι = U.ι ≫ (a g).hom) ∧
          IsAdmissibleFiniteSchemeQuotient aU p ∧
          ∃ (t : Scheme.GaloisCoverAction G V.toScheme) (e : t.Z ≅ U.toScheme),
            e.hom ≫ p = t.π ∧
            (∀ g : G, t.smul g ≫ e.hom = e.hom ≫ (aU g).hom) ∧
            (C.IsSeparated → Dense (V : Set Y) ∧
              ∃ hY : IsIntegral Y,
                @Scheme.Hom.HasGaloisFunctionFieldAction G _ C Y inferInstance hY a q) := by
  sorry

end AlgebraicGeometry
