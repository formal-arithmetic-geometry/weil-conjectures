/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q46
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.SpaceChangeBase
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.Paper.QuasiCompactH1Zero
import WeilConjectures.AlgebraicGeometry.EtaleZariskiQcohComparison
import Sheaf.AlgebraicGeometry.AlgebraicSpaceH1AffineBaseChange
import Sheaf.AlgebraicGeometry.AlgebraicSpaceUCSurjectionSeparation
import Sheaf.AlgebraicGeometry.StackUniversalInjectivityCriteria
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Geometry of the acyclic affinization map

Source: Stacks Project, Spaces Cohomology, Situation 07UY and Tags 07V4, 07V5;
Properties of Spaces, Tag 05Z1; Spaces, Tag 04SG
(blueprint: lem-sfb-space-acyclic-affinization-geometry).

Global functions are specified by their universal cone on the small etale charts.
The normalization of its projections specifies the identity on global functions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The absolute space obtained by the characterized change of base to Spec Z.
The chosen extension is specified on sections, restrictions, morphisms and charts
by `exists_spaceChangeBase`; its choice changes only the representative of the
canonical change of base. It retains the same small etale ringed site up to the
chart-normalized equivalence in that theorem.
Source: Stacks, Spaces, Tag 04SG
(blueprint: lem-sfb-space-acyclic-affinization-geometry). -/
def acyclicAffinizationAbsoluteSpace {S : Scheme.{u}} (X : AlgebraicSpace S) :
    AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ))) :=
  ((Classical.choose (exists_spaceChangeBase (specULiftZIsTerminal.from S))).obj X).left

/-- The canonical absolute affinization is unique, separated and universally injective.
A is the ring of global regular functions: its cone is limiting on the actual small
etale chart diagram. The displayed normalization says p induces the identity of A.
Separatedness is tested by closed immersions on all scheme tests of its diagonal;
universal injectivity uses every algebraic-space base change and field-point classes.
Source: Stacks, Spaces Cohomology, Situation 07UY and Tags 07V4, 07V5;
Properties of Spaces, Tag 05Z1; Spaces, Tag 04SG
(blueprint: lem-sfb-space-acyclic-affinization-geometry).

Proof:
1. Change base to Spec Z by lem-sfb-space-change-base-to-integers, retaining the
   charts, point topology and ringed small etale site. Use
   lem-sfb-space-affine-target-global-functions to construct the unique map p with
   the prescribed pullbacks on every chart.
2. For every field K over A, lem-sfb-space-h1-vanishing-affine-base-change gives a
   qcqs fibre with vanishing H1 and global ring K, including non-flat A -> K.
3. Regard that fibre as a space over K by lem-sfb-space-change-base-to-integers.
   Its rational points are closed and distinct points have distinct images by
   lem-sfb-qs-space-rational-point-topology. Two different points would be separated
   by a global function taking values 0 and 1, by
   lem-sfb-space-h1-separate-disjoint-closed. Both evaluations on Gamma = K are the
   identity, a contradiction. The field criterion
   lem-sfb-stack-universal-injectivity-criteria gives universal injectivity.
4. Choose the integral surjective scheme cover of
   lem-sfb-qcqs-space-integral-scheme-cover. It is affine over X and qcqs by
   lem-sfb-space-integral-qcqs-permanence; its quasi-coherent H1 vanishes by
   lem-sfb-space-h1-vanishing-affine-base-change.
5. Use lem-trf-scheme-zariski-etale-quasi-coherent-equivalence and
   lem-sc-etale-zariski-qcoh-comparison to transfer this vanishing to Zariski ideals.
   The scheme Serre criterion lem-pqf-quasicompact-h1-zero makes the cover affine.
6. Its absolute diagonal is closed by lem-weil-pbc-affine-source-morphism-separated
   and lem-weil-pbc-closed-immersion-base-change. The integral cover is universally
   closed by lem-sfb-space-integral-universally-closed; descend absolute separation
   by lem-sfb-space-uc-surjection-separation.
7. The relative diagonal over Spec A is a base change of the absolute diagonal.
   Every scheme test is therefore a closed immersion, as claimed. -/
theorem space_acyclic_affinization_geometry {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasSheafify X.etaleTopology AddCommGrpCat.{u}]
    [HasExt.{u + 1} (Sheaf X.etaleTopology AddCommGrpCat.{u})]
    (hqc : CompactSpace (Point X.obj.obj)) (hqs : IsAbsolutelyQuasiSeparated X)
    (hH : ∀ (F : X.Modules) (_ : F.IsQuasicoherent),
      Subsingleton (Sheaf.H ((SheafOfModules.toSheaf X.structureSheaf).obj F) 1)) :
    ∃ (A : CommRingCat.{u})
      (π : (Functor.const (acyclicAffinizationAbsoluteSpace X).EtaleSiteᵒᵖ).obj A ⟶
        (acyclicAffinizationAbsoluteSpace X).etaleForget.op ⋙ Scheme.Γ),
      Nonempty (IsLimit (Cone.mk A π)) ∧
      ∃ p : acyclicAffinizationAbsoluteSpace X ⟶
          schemeSpace (Over.mk (specULiftZIsTerminal.from (Spec A))),
        (∀ T : (acyclicAffinizationAbsoluteSpace X).EtaleSite,
          π.app (op T) = (Scheme.ΓSpecIso A).inv ≫
            (yoneda.preimage (T.obj.hom ≫ p.hom.hom)).left.appTop) ∧
        (∀ q : acyclicAffinizationAbsoluteSpace X ⟶
            schemeSpace (Over.mk (specULiftZIsTerminal.from (Spec A))),
          (∀ T : (acyclicAffinizationAbsoluteSpace X).EtaleSite,
            π.app (op T) = (Scheme.ΓSpecIso A).inv ≫
              (yoneda.preimage (T.obj.hom ≫ q.hom.hom)).left.appTop) → q = p) ∧
        IsRepresentableWith (fun _ _ f ↦ IsClosedImmersion f.left)
          (pullback.diagonal p.hom.hom) ∧
        ∀ (T : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ))))
          (g : T ⟶ schemeSpace (Over.mk (specULiftZIsTerminal.from (Spec A)))),
          Function.Injective (mapPoint (pullback.snd p.hom g.hom).hom) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
