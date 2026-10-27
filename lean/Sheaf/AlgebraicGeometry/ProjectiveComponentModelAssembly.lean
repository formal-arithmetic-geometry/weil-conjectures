/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Sober
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import Sheaf.AlgebraicGeometry.ProjectiveSpaceFunctorOfPoints
import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
import Sheaf.AlgebraicGeometry.ProjectiveMorphismChartPreimage
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso

/-!
# Assembly of projective component models and Cartier markings

Source: ILO, Travaux de Gabber, Expose X, 2.3, Step 1, printed p.150;
Stacks Project, Tags 01JB, 01JC, 01NE, 01NG, 01QO, 01WR and 01IS.
(blueprint: lem-sfb-projective-component-model-assembly)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

/-- Finitely many given projective normal geometrically reduced birational component models
assemble as a scheme coproduct, with the given Cartier ideals as restrictions of one Cartier
ideal. The coproduct embeds in projective space with the sum of the coordinate-block sizes,
and its induced map bijects component generic points and preserves their residue fields.

Source: ILO, Travaux de Gabber, Expose X, 2.3, Step 1, printed p.150; agent expansion
of the finite-component reconstruction using Stacks Tags 01JB, 01JC, 01NE, 01NG, 01QO,
01WR and 01IS (blueprint: lem-sfb-projective-component-model-assembly).

Proof:
1. Apply lem-weil-pbc-scheme-coproduct-family to obtain B and its disjoint clopen summands.
   The coproduct universal property assembles both structure maps and q, with the specified
   restrictions. Components cover T and each component map is surjective, so q is surjective.
2. Pull back O(1) along each given embedding. By lem-weil-pbc-projective-space-standard-charts
   its coordinate sections generate. Assemble these invertible modules componentwise on the
   disjoint open cover, and extend each coordinate section by zero on the other summands.
   The resulting sum of (m_i+1) sections generates. Use
   lem-weil-pbc-projective-space-functor-of-points and
   def-weil-pbc-morphism-to-projective-space-by-sections to obtain a map to P^M over e.
3. By lem-weil-pbc-projective-morphism-chart-preimage, the inverse image of a coordinate chart
   lies entirely in its own summand. Its ring map is the surjective map of the given embedding
   on that chart, sending all other coordinate blocks to zero. The affine closed-immersion
   criterion in def-weil-closed-immersion and target locality in
   lem-weil-pbc-closed-finite-etale-zariski-local show that the assembled map is closed.
4. Thus B is H-projective (def-kun-projective), so lem-kun-projective-implies-proper makes
   its structure map proper, and def-weil-proper-morphism makes it finite type.
5. For every field extension, lem-sc-etale-fibre-product-base-change-coproduct identifies
   the base change with the coproduct of the base-changed summands. Each local ring is that
   of one summand (def-weil-open-immersion), hence reduced. Apply def-pc-reduced-scheme and
   def-pc-geometrically-irreducible to get geometric reducedness of B.
6. Define J on an open U by the product of J_i(U intersect N_i), with componentwise
   restrictions and action. Sheaf gluing and quasi-coherence hold summandwise. On the affine
   covers inside the summands, the generators are the given non-zero-divisors, so J is an
   effective Cartier ideal (def-nagata-effective-cartier-ideal). Its restriction is each J_i;
   their supports give support J = q inverse C.
7. Integral summands and reduced components have unique generic points by
   lem-weil-pbc-scheme-sober. The dense opens in the birationality hypotheses contain them;
   their isomorphisms carry one generic point to the other. An irreducible subset of B meets
   only one clopen summand, so these summands are exactly its components. The component
   enumeration is bijective, giving the generic-point bijection. The dense-open isomorphisms
   and lem-weil-pbc-residue-field-point-naturality identify residue fields within each
   component. The component inclusions preserve residue fields by
   lem-weil-pbc-closed-immersion-residue-field-iso; the coprojections do so by the open case.
   Naturality identifies their composite with the actual residueFieldMap of q. -/
theorem exists_projective_component_model_assembly
    (e : Type u) [Field e] (T : Scheme.{u}) [T.Over (Spec (.of e))]
    [Nonempty T] [IsReduced T] [IsProper (T ↘ Spec (.of e))]
    (hfiniteType : LocallyOfFiniteType (T ↘ Spec (.of e)) ∧ QuasiCompact (T ↘ Spec (.of e)))
    (s : ℕ) (hs : 0 < s) (Ti : Fin s → Scheme.{u})
    [∀ i, (Ti i).Over (Spec (.of e))] [∀ i, IsReduced (Ti i)]
    (j : ∀ i, Ti i ⟶ T) [∀ i, IsClosedImmersion (j i)]
    [∀ i, (j i).IsOver (Spec (.of e))]
    (hcomponent : ∀ i, Set.range (j i) ∈ irreducibleComponents T)
    (henumeration : Function.Bijective
      (fun i ↦ (⟨Set.range (j i), hcomponent i⟩ : irreducibleComponents T)))
    (C : Set T) (hC : IsClosed C) (hCnd : interior C = ∅)
    (N : Fin s → Scheme.{u}) [∀ i, (N i).Over (Spec (.of e))]
    [∀ i, IsIntegral (N i)]
    (hnormal : ∀ (i : Fin s) (x : N i),
      IsDomain ((N i).presheaf.stalk x) ∧ IsIntegrallyClosed ((N i).presheaf.stalk x))
    [∀ i, GeometricallyReduced (N i ↘ Spec (.of e))]
    (m : Fin s → ℕ)
    (a : ∀ i, N i ⟶ ℙ(ULift.{u} (Fin (m i + 1)); Spec (.of e)))
    [∀ i, IsClosedImmersion (a i)] [∀ i, (a i).IsOver (Spec (.of e))]
    (qi : ∀ i, N i ⟶ Ti i) [∀ i, IsProper (qi i)] [∀ i, Surjective (qi i)]
    [∀ i, (qi i).IsOver (Spec (.of e))]
    (hbirational : ∀ i, ∃ (U : (N i).Opens) (V : (Ti i).Opens),
      Dense (U : Set (N i)) ∧ Dense (V : Set (Ti i)) ∧
      ∃ φ : U.toScheme ≅ V.toScheme, U.ι ≫ qi i = φ.hom ≫ V.ι)
    (Ji : ∀ i, (N i).IdealSheafData) (hJi : ∀ i, (Ji i).IsInvertible)
    (hsupport : ∀ i, ((Ji i).support : Set (N i)) = (qi i ≫ j i) ⁻¹' C) :
    ∃ (B : Scheme.{u}) (ι : ∀ i, N i ⟶ B) (b : B ⟶ Spec (.of e)) (q : B ⟶ T),
      Nonempty (IsColimit (Cofan.mk B ι)) ∧
      (∀ i, IsOpenImmersion (ι i) ∧ IsClosed (Set.range (ι i))) ∧
      (∀ i, ι i ≫ b = N i ↘ Spec (.of e)) ∧
      (∀ i, ι i ≫ q = qi i ≫ j i) ∧ q ≫ (T ↘ Spec (.of e)) = b ∧
      IsProper b ∧ LocallyOfFiniteType b ∧ QuasiCompact b ∧ GeometricallyReduced b ∧
      (∃ (M : ℕ) (A : B ⟶ ℙ(ULift.{u} (Fin (M + 1)); Spec (.of e))),
        M + 1 = ∑ i, (m i + 1) ∧ IsClosedImmersion A ∧
        A ≫ (ℙ(ULift.{u} (Fin (M + 1)); Spec (.of e)) ↘ Spec (.of e)) = b) ∧
      (∃ J : B.IdealSheafData, J.IsInvertible ∧
        (∀ i, J.comap (ι i) = Ji i) ∧ (J.support : Set B) = q ⁻¹' C) ∧
      Surjective q ∧
      (∀ (i : Fin s) (η : N i), IsGenericPoint η (Set.univ : Set (N i)) →
        IsGenericPoint (qi i η) (Set.univ : Set (Ti i)) ∧
        IsGenericPoint (q (ι i η)) (Set.range (j i)) ∧
        IsIso (q.residueFieldMap (ι i η))) ∧
      Set.BijOn q (genericPoints B) (genericPoints T) := by
  sorry

end AlgebraicGeometry
