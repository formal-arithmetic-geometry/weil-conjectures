/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q125
-/
module

public import Sheaf.AlgebraicGeometry.NodalLogCanonicalReconstruction
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Sheaf.AlgebraicGeometry.ProperReducedGlobalSectionsProduct
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import WeilConjectures.AlgebraicGeometry.Modules.Dual
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Sheaf.AlgebraicGeometry.CurveDegreeTensorAdditive
import Sheaf.TraceFormula.ReducedCurveNormalizationGenus
import Sheaf.AlgebraicGeometry.CurveSectionDegreePositivity
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Stable ten-canonical limits of balanced nodal traits

Source: Morrison, arXiv:0810.2340, Section 3.3, Proposition 10 and Corollary 11(1),
printed pp. 16--17; Stacks, Moduli of Curves, Tags 0E6R and 0E74
(blueprint: lem-sfb-balanced-nodal-trait-stable-canonical-limit).

Degrees are sums on canonical normalized components. Boundary points are counted in
intersections of complementary component unions. No Cartier-component or total-space
regularity condition occurs.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

namespace BalancedNodalTrait

/-- The geometric closed point induced by the residue-field inclusion.
Source: Morrison, Proposition 10, closed fibre over a trait
(blueprint: lem-sfb-balanced-nodal-trait-stable-canonical-limit). -/
def closedPoint (R Ω : Type u) [CommRing R] [IsLocalRing R] [Field Ω]
    [Algebra (IsLocalRing.ResidueField R) Ω] : Spec (.of Ω) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom
    ((algebraMap (IsLocalRing.ResidueField R) Ω).comp (IsLocalRing.residue R)))

/-- The actual geometric closed fibre, rather than a chosen isomorphic curve.
Source: Morrison, Proposition 10
(blueprint: lem-sfb-balanced-nodal-trait-stable-canonical-limit). -/
abbrev fiber {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) (Ω : Type u) [Field Ω]
    [Algebra (IsLocalRing.ResidueField R) Ω] : Scheme.{u} :=
  pullback f (closedPoint R Ω)

/-- Structural map of the geometric closed fibre.
Source: Morrison, Proposition 10
(blueprint: lem-sfb-balanced-nodal-trait-stable-canonical-limit). -/
abbrev projection {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) (Ω : Type u) [Field Ω]
    [Algebra (IsLocalRing.ResidueField R) Ω] : fiber f Ω ⟶ Spec (.of Ω) :=
  pullback.snd f (closedPoint R Ω)

/-- Restriction of a line to the actual geometric closed fibre.
Source: Morrison, Proposition 10; Stacks 0E6R for the dualizing line
(blueprint: lem-sfb-balanced-nodal-trait-stable-canonical-limit). -/
def line {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) (Ω : Type u) [Field Ω]
    [Algebra (IsLocalRing.ResidueField R) Ω] (L : X.Modules) : (fiber f Ω).Modules :=
  (Scheme.Modules.tensorPullback (pullback.fst f (closedPoint R Ω))).obj L

/-- Euler degree on the canonical normalization of a reduced component.
Source: Morrison, equation (6), normalized-component degree convention
(blueprint: lem-sfb-balanced-nodal-trait-stable-canonical-limit). -/
def componentDegree {Ω : Type u} [Field Ω] {C : Scheme.{u}}
    (p : C ⟶ Spec (.of Ω)) (L : C.Modules) (Z : irreducibleComponents C) : ℤ :=
  @Scheme.Modules.degree Ω _ (C.reducedNormalizationComponent Z).normalization
    ⟨C.normalizedComponentMap Z ≫ p⟩
    ((Scheme.Modules.tensorPullback (C.normalizedComponentMap Z)).obj L)

/-- Underlying set of a reduced component union; the empty union is allowed here.
Source: Morrison, equation (6)
(blueprint: lem-sfb-balanced-nodal-trait-stable-canonical-limit). -/
def componentUnion {C : Scheme.{u}} (S : Finset (irreducibleComponents C)) : Set C :=
  ⋃ Z ∈ S, Z.1

/-- Nodes between a component union and its complementary reduced union. Self-nodes
inside either union do not belong to this boundary.
Source: Morrison, equation (6)
(blueprint: lem-sfb-balanced-nodal-trait-stable-canonical-limit). -/
def boundary {C : Scheme.{u}} (S : Finset (irreducibleComponents C)) : Set C :=
  componentUnion S ∩ ⋃ Z : irreducibleComponents C, ⋃ (_ : Z ∉ S), Z.1

/-- Coordinate linear forms pulled back to the given embedding line. Bijectivity of
this actual map says the embedding is nondegenerate and uses the complete linear system.
Source: Morrison, Proposition 10 and Definition 7
(blueprint: lem-sfb-balanced-nodal-trait-stable-canonical-limit). -/
def coordinateSections {Ω : Type u} [Field Ω] {C : Scheme.{u}}
    (p : C ⟶ Spec (.of Ω)) {I : Type u} [Fintype I]
    (i : C ⟶ ℙ(I; Spec (.of Ω))) (L : C.Modules)
    (e : (Scheme.Modules.tensorPullback i).obj
      (ProjectiveSpace.twist I (Spec (.of Ω)) 1) ≅ L) (a : I → Ω) : Γ(L, ⊤) :=
  ∑ j : I, p.appTop.hom ((Scheme.ΓSpecIso (.of Ω)).inv (a j)) •
    e.hom.app ⊤
      (((Scheme.Modules.tensorPullbackSectionAdjunction i).unit.app
        (ProjectiveSpace.twist I (Spec (.of Ω)) 1)).app ⊤
          (ProjectiveSpace.twistOneSection I (Spec (.of Ω)) j))

end BalancedNodalTrait

/-- A balanced, potentially stable embedded closed fibre with generically tenth-canonical
polarization is itself stable and the same complete embedding is tenth-canonical.
Source: Morrison, Section 3.3, Proposition 10 and Corollary 11(1), pp. 16--17;
Stacks, Moduli of Curves, Tags 0E6R and 0E74
(blueprint: lem-sfb-balanced-nodal-trait-stable-canonical-limit).

Proof (the six DAG steps):
1. Projective base change and projective properness make the closed fibre proper.
   Finite type over the field makes it Noetherian. Proper reduced connected global
   sections are the field, and cohomology above dimension one vanishes. The Euler
   hypothesis therefore identifies its arithmetic genus with g.
2. A DVR is Noetherian. Nodal log canonical reconstruction with zero markings gives
   the canonical dualizing line and its generic and closed-fibre comparisons. For
   T = L tensor (omega dual)^10, invertible pullback/tensor and tensor duality give
   generic triviality; curve-degree tensor additivity gives deg_Y T = deg_Y L-10 deg_Y omega.
3. The nodal-trait twister extremal-degree theorem, which allows singular total spaces
   and persistent nodes, gives a proper nonempty Y with deg_Y T >= k_Y > 0 if T_C is
   nontrivial. Balance gives deg_Y T <= k_Y/2, a contradiction. Thus T_C is trivial and
   L_C is the tenth power of omega_C. This uses
   lem-sfb-nodal-trait-twister-extremal-degree.
4. On every canonical normalized component the embedding line has positive degree:
   choose a linear form vanishing at one geometric point but not another and apply
   curve-section-degree positivity. The reconstruction component formula reads
   0 < 10(2h-2+b). It forces b >= 3 for h=0 and b >= 1 for h=1, including self-nodes.
5. Repeat the component argument after every algebraically closed field extension.
   Relative dualizing base change preserves the line comparison and projective
   base change preserves the embedding. Flat cohomology base change preserves H1
   dimension, hence the genus at every geometric point of Spec Omega is g.
6. The empty labelled section family has vacuous marking conditions. The previous
   steps give exactly the recorded stable-pointed-curve and moduli-genus predicates.
   Composing the given hyperplane-line comparison with L_C = omega_C^10 identifies
   its coordinate sections, so the very same embedding is the complete ten-canonical one.
-/
theorem balanced_nodal_trait_stable_canonical_limit
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [IsProjective f] [Flat f] [LocallyOfFinitePresentation f]
    (hnodal : HasNodalGeometricFibres f)
    (hgeometric : ∀ (F : Type u) [Field F] [IsAlgClosed F] (t : Spec (.of F) ⟶ Spec (.of R)),
      IsReduced (pullback f t) ∧ (pullback f t).IsPureDimension 1)
    (omega : X.Modules) (dualizing : NodalDualizingDatum f omega)
    (L : X.Modules) [L.IsInvertible]
    (hgeneric : Nonempty
      ((Scheme.Modules.tensorPullback
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj L ≅
       (Scheme.Modules.tensorPullback
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj
          (omega.tensorPow 10)))
    (Ω : Type u) [Field Ω] [Algebra (IsLocalRing.ResidueField R) Ω]
    [IsAlgClosure (IsLocalRing.ResidueField R) Ω]
    (g : ℕ) (hg : 2 ≤ g)
    (hchi : @Scheme.Modules.eulerChar Ω _ (BalancedNodalTrait.fiber f Ω)
      ⟨BalancedNodalTrait.projection f Ω⟩
      (SheafOfModules.unit (BalancedNodalTrait.fiber f Ω).ringCatSheaf) = 1 - (g : ℤ))
    (I : Type u) [Fintype I]
    (i : BalancedNodalTrait.fiber f Ω ⟶ ℙ(I; Spec (.of Ω)))
    (hi : IsClosedImmersion i)
    (hover : i ≫ (ℙ(I; Spec (.of Ω)) ↘ Spec (.of Ω)) = BalancedNodalTrait.projection f Ω)
    (e : (Scheme.Modules.tensorPullback i).obj
      (ProjectiveSpace.twist I (Spec (.of Ω)) 1) ≅ BalancedNodalTrait.line f Ω L)
    (hcomplete : Function.Bijective
      (BalancedNodalTrait.coordinateSections (BalancedNodalTrait.projection f Ω) i _ e))
    (hrational : ∀ Z : irreducibleComponents (BalancedNodalTrait.fiber f Ω),
      (BalancedNodalTrait.fiber f Ω).normalizedComponentGenus
          (BalancedNodalTrait.projection f Ω) Z = 0 →
      2 ≤ ((BalancedNodalTrait.fiber f Ω).normalizedComponentMap Z ⁻¹'
        {x | x ∉ (BalancedNodalTrait.projection f Ω).smoothLocus}).encard)
    (htwopoint : ∀ Z : irreducibleComponents (BalancedNodalTrait.fiber f Ω),
      Smooth ((Scheme.IdealSheafData.vanishingIdeal
        ⟨Z.1, isClosed_of_mem_irreducibleComponents _ Z.2⟩).subschemeι ≫
          BalancedNodalTrait.projection f Ω) →
      (BalancedNodalTrait.fiber f Ω).normalizedComponentGenus
        (BalancedNodalTrait.projection f Ω) Z = 0 →
      (BalancedNodalTrait.boundary {Z}).ncard = 2 →
      BalancedNodalTrait.componentDegree (BalancedNodalTrait.projection f Ω)
        (BalancedNodalTrait.line f Ω L) Z = 1)
    (hbalanced : ∀ S : Finset (irreducibleComponents (BalancedNodalTrait.fiber f Ω)),
      S.Nonempty → BalancedNodalTrait.componentUnion S ≠ Set.univ →
      |((∑ Z ∈ S, BalancedNodalTrait.componentDegree (BalancedNodalTrait.projection f Ω)
          (BalancedNodalTrait.line f Ω L) Z : ℤ) : ℚ) -
        10 * ((∑ Z ∈ S, BalancedNodalTrait.componentDegree (BalancedNodalTrait.projection f Ω)
          (BalancedNodalTrait.line f Ω omega) Z : ℤ) : ℚ)| ≤
        ((BalancedNodalTrait.boundary S).ncard : ℚ) / 2) :
    ∃ c : BalancedNodalTrait.line f Ω L ≅ (BalancedNodalTrait.line f Ω omega).tensorPow 10,
      IsStablePointedCurve (BalancedNodalTrait.projection f Ω)
        (fun j : Fin 0 ↦ Fin.elim0 j) (fun j : Fin 0 ↦ Fin.elim0 j) ∧
      (∀ (F : Type u) [Field F] [IsAlgClosed F]
          (a : Spec (.of F) ⟶ Spec (.of Ω)),
        Module.finrank F
          ((ModuleCat.restrictScalars (((Scheme.ΓSpecIso (.of F)).inv ≫
            (pullback.snd (BalancedNodalTrait.projection f Ω) a).appTop).hom)).obj
            ((RingedSpace.moduleCohomology
              (pullback (BalancedNodalTrait.projection f Ω) a).toRingedSpace 1).obj
                (SheafOfModules.unit
                  (pullback (BalancedNodalTrait.projection f Ω) a).ringCatSheaf))) = g) ∧
      Function.Bijective (BalancedNodalTrait.coordinateSections
        (BalancedNodalTrait.projection f Ω) i _ (e ≪≫ c)) := by
  sorry

end AlgebraicGeometry
