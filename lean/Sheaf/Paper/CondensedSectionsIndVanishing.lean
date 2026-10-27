/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CondensedQcqsPushforwardContinuity
public import Mathlib.CategoryTheory.ObjectProperty.Ind
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# Filtered-colimit stability of ordinary module-section cohomology vanishing

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes, Lemma 5.3(1),
global-sections clause, applied to degree-zero complexes.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

set_option synthInstance.maxHeartbeats 100000 in
-- Colimit inference in the internal module category needs a larger search budget.
set_option synthInstance.maxSize 4096 in
/-- In a fixed degree, vanishing of ordinary derived module sections passes from an
object property to its small filtered-colimit hull. The diagram consists of modules;
no lift of its maps to presentations or to other complexes is required.

Source: Hemo--Richarz--Scholbach, Lemma 5.3(1), global-sections clause
(blueprint: lem-sfb-condensed-sections-ind-vanishing).
Proof: apply filtered continuity to the degree-zero complex diagram. These complexes
are strictly supported in degrees at least zero, so their good truncation at zero is
isomorphic to the original diagram. The single-complex functor preserves its colimit.
Thus the continuity target is the derived sections of the given colimit module.
Every group in the source diagram is zero; its colimit is zero. Transport along the
continuity isomorphism and the preceding identifications gives the assertion.
-/
theorem condensedModuleSections_ind_isZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (P : ObjectProperty
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (q : ℤ)
    (hP : ∀ M, P M → IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((condensedModuleSections Λ X).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj M))))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : P.ind.{u + 1} M) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((condensedModuleSections Λ X).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  obtain ⟨I, _, _, pres, hpres⟩ := hM
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let S := CochainComplex.singleFunctor A 0
  let D := pres.diag ⋙ S
  let T := DerivedCategory.Q ⋙ (condensedModuleSections Λ X).rightDerivedFunctor ⋙
    DerivedCategory.homologyFunctor Ab.{u + 1} q
  have hstrict (i : I) : (D.obj i).IsStrictlyGE 0 := by
    dsimp [D, S]
    infer_instance
  have : PreservesColimitsOfShape I S := by
    dsimp [S, CochainComplex.singleFunctor, CochainComplex.singleFunctors]
    infer_instance
  have ha (i : I) (n : ℤ) (hn : n < 0) : IsZero ((D.obj i).homology n) := by
    have := hstrict i
    exact (D.obj i).exactAt_of_isGE 0 n hn |>.isZero_homology
  have hc := condensed_qcqs_globalSections_continuity Λ X D 0 ha q
  let e : D ≅ D ⋙ (ComplexShape.embeddingUpIntGE 0).truncGEFunctor A :=
    NatIso.ofComponents (fun i ↦ by
      have := hstrict i
      exact asIso ((D.obj i).πTruncGE 0))
      (by intro i j f; exact ((D.obj i).πTruncGE_naturality (D.map f) 0).symm)
  let p := pres.map S
  let eM : (condensedContinuityCocone D 0).pt ≅ S.obj M :=
    (HasColimit.isoOfNatIso e).symm ≪≫ (colimit.isColimit D).coconePointUniqueUpToIso p.isColimit
  have hz : IsZero (colimit (D ⋙ T)) := by
    exact (colimit.isColimit (D ⋙ T)).isZero_pt
      ((D ⋙ T).isZero (fun i ↦ hP _ (hpres i)))
  exact (hz.of_iso (asIso (condensedContinuityComparison D 0 T)).symm).of_iso
    (T.mapIso eM).symm

end AlgebraicGeometry.ProEtale
