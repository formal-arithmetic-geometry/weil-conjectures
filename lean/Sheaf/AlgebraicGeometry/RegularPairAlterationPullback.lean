/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q44
-/
module

public import Sheaf.AlgebraicGeometry.PrimeToEllAlterationTopology
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.RingTheory.GRing
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Topology.GDelta.Basic
import Sheaf.CategoryTheory.Sites.GrothendieckTopos
import Sheaf.RingTheory.RegularBaseChange
import Sheaf.RingTheory.RegularLocalMaximal
import WeilConjectures.RingTheory.RegularLocalOfFlatWithRegularClosedFiber
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import WeilConjectures.RingTheory.IsRegularSystemOfParameters
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.Flat.Localization
import Sheaf.RingTheory.FibreRingNoetherian
import Sheaf.RingTheory.RegularComposition
import Sheaf.AlgebraicGeometry.AlterationGeneratorsReducedBaseChange
import Sheaf.AlgebraicGeometry.SNCBoundaryParameterCriterion

/-!
# Regular pullback of alteration pairs

Source: ILO, Travaux de Gabber, Expose IX 1.3, printed p. 132, and II 2.3.4,
printed p. 28; Stacks Tags 031E, 07BZ, 07GH, 07QT and 0BIA
(blueprint: lem-per-regular-pair-alteration-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.PrimeToEllAlteration

/-- The identity object of `alt/S`. Source: ILO II 1.2.2
(blueprint: lem-per-regular-pair-alteration-pullback). -/
def baseObject (S : Scheme.{u}) [IsNoetherian S] [IsReduced S] : Alt S :=
  ⟨Over.mk (𝟙 S), (inferInstance : LocallyOfFiniteType (𝟙 S)),
    (inferInstance : QuasiCompact (𝟙 S)), (inferInstance : IsReduced S),
    fun t ht ↦ ⟨ht, by
      change ((𝟙 S : S ⟶ S).residueFieldMap t).hom.Finite
      rw [Scheme.residueFieldMap_id]
      exact RingHom.Finite.id (S.residueField t)⟩⟩

/-- The structural arrow to the identity object. Source: ILO II 1.2.2
(blueprint: lem-per-regular-pair-alteration-pullback). -/
def toBaseObject {S : Scheme.{u}} [IsNoetherian S] [IsReduced S] (T : Alt S) :
    T ⟶ baseObject S :=
  ObjectProperty.homMk (Over.homMk T.obj.hom)

/-- Regular pullback preserves a finite regular alteration covering and its boundary supports.
Source: ILO IX 1.3 and II 2.3.4; Stacks 031E and 0BIA
(blueprint: lem-per-regular-pair-alteration-pullback).

Proof: (1) On affine charts, regular base change (07C1) and localization (07C0)
give regular local projection maps. Flat ascent from a regular local ring with regular
closed fibre (031E) proves regularity of each ordinary fibre product.
(2) Regular fibres are reduced, so lem-per-alteration-generators-reduced-base-change
makes these ordinary products objects of alt/S' and preserves both generating covers.
(3) Image-covering sieves form a topology: maximality, pullback, and transitivity follow
from the corresponding sieve axioms and preservation of categorical pullbacks. Minimality
of the generated alteration topology therefore proves the covering assertion.
(4) At a boundary point choose parameters t_1,...,t_d with equation t_1...t_r.
Lift parameters of the regular closed fibre to u_1,...,u_e. Flatness gives generators
(t,u) of the target maximal ideal and the flat dimension formula gives dimension d+e.
Thus (t,u) is a regular system of parameters, including r=0.
(5) The inverse-image closed ideal is extended from the source, hence has equation
t_1...t_r in these parameters. The snc parameter criterion gives a strict normal crossings
boundary, even if components split. Its support is the exact inverse image by the
pullback square. The empty boundary is included. -/
theorem regular_pair_alteration_pullback
    {S S' : Scheme.{u}} [IsNoetherian S] [IsNoetherian S']
    [IsReduced S] [IsReduced S'] (g : S' ⟶ S) [Flat g]
    (hreg : ∀ (s : S) (L : Type u) [Field L]
      [Algebra (S.residueField s) L] [Module.Finite (S.residueField s) L],
      IsRegularScheme (pullback (g.fiberToSpecResidueField s)
        (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) L)))))
    (ell : ℕ) [Fact ell.Prime] (hinv : ∀ s : S, IsUnit (ell : S.presheaf.stalk s))
    {I : Type w} [Finite I] (R : I → Alt S)
    (hcover : IsCoveringFamily ell R (fun i ↦ toBaseObject (R i)))
    (hR : ∀ i, IsNoetherian (R i).obj.left ∧ IsRegularScheme (R i).obj.left)
    (hnoeth : ∀ i, IsNoetherian (pullback (R i).obj.hom g)) :
    (∀ i, IsRegularScheme (pullback (R i).obj.hom g)) ∧
    (∃ R' : I → Alt S',
      (∀ i, (R' i).obj = Over.mk (pullback.snd (R i).obj.hom g)) ∧
      IsCoveringFamily ell R' (fun i ↦ toBaseObject (R' i))) ∧
    ∀ (Z : TopologicalSpace.Closeds S), IsNowhereDense (Z : Set S) →
      (∀ i, ∃ H : (R i).obj.left.IdealSheafData,
        IsStrictNormalCrossingsBoundary H ∧
          (H.support : Set (R i).obj.left) = (R i).obj.hom ⁻¹' (Z : Set S)) →
      ∀ i, ∃ H' : (pullback (R i).obj.hom g).IdealSheafData,
        IsStrictNormalCrossingsBoundary H' ∧
          (H'.support : Set ↥(pullback (R i).obj.hom g)) =
            (pullback.snd (R i).obj.hom g) ⁻¹' (g ⁻¹' (Z : Set S)) := by
  sorry

end AlgebraicGeometry.PrimeToEllAlteration

namespace AlgebraicGeometry

/-- The completion map of an excellent local ring is regular. Source: ILO I 2.10,
IX 1.3; Stacks 07QT and 07GH (blueprint: lem-per-regular-pair-alteration-pullback).
Proof: excellence implies the G-ring condition. Apply that condition at the maximal
ideal and identify localization there with the local ring itself. Noetherianity of
completion is lem-weil-pbc-adic-completion-noetherian. -/
theorem excellent_local_completion_isRegular
    (A : Type u) [CommRing A] [IsLocalRing A] (hA : IsExcellent A) :
    RingHom.IsRegular (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) := by
  sorry

/-- Localization followed by excellent local completion is a regular scheme morphism.
Source: ILO IX 1.3; Stacks 07GH, 07QI
(blueprint: lem-per-regular-pair-alteration-pullback).
Proof: apply the preceding completion argument to the excellent stalk. The localization
map is flat and its fibres are empty or spectra of residue fields, hence geometrically
regular, including after every finite extension. The completion and fibre Noetherianity
lemmas allow regular composition (07QI). This gives flatness and geometric regularity of
the displayed composite, with no finite-type assumption on completion. -/
theorem excellent_stalk_completion_regular
    (S : Scheme.{u}) [IsNoetherian S]
    (hexc : ∀ U : S.affineOpens, IsExcellent Γ(S, U)) (s : S) :
    Flat (Spec.map (CommRingCat.ofHom
      (algebraMap (S.presheaf.stalk s)
        (AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk s))
          (S.presheaf.stalk s)))) ≫ S.fromSpecStalk s) ∧
    ∀ (t : S) (L : Type u) [Field L]
      [Algebra (S.residueField t) L] [Module.Finite (S.residueField t) L],
      IsRegularScheme (pullback
        ((Spec.map (CommRingCat.ofHom
          (algebraMap (S.presheaf.stalk s)
            (AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk s))
              (S.presheaf.stalk s)))) ≫ S.fromSpecStalk s).fiberToSpecResidueField t)
        (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField t) L)))) := by
  sorry

end AlgebraicGeometry
