/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.CoherentFormalModule
import all Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import all Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import all WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex

/-! # Closed support of a proper coherent pushforward

This interface isolates the closedness part of the proper pushforward support theorem.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u
open CategoryTheory
namespace AlgebraicGeometry

set_option maxHeartbeats 600000 in
-- Coherent-generator presentation transport needs additional elaboration heartbeats.
private theorem fp_of_coh {X : Scheme.{u}} [IsLocallyNoetherian X] (F : X.Modules)
    (h : RingedSpace.IsCoherent X.toRingedSpace F) : F.IsFinitePresentation := by
  classical
  have : F.IsFiniteType := h.1
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData F
  have hfp (i : q.I) : (F.over (q.X i)).IsFinitePresentation := by
    have := hq.isFiniteType i
    let _ := Fintype.ofFinite (q.generators i).I
    let n := Fintype.card (q.generators i).I
    let e := (SheafOfModules.freeFunctor (R := X.ringCatSheaf.over (q.X i))).mapIso
      ((Equiv.ulift.trans (Fintype.equivFin (q.generators i).I).symm).toIso)
    let f := e.hom ≫ (q.generators i).π
    have : Epi f := inferInstanceAs (Epi (e.hom ≫ (q.generators i).π))
    let G := SheafOfModules.GeneratingSections.ofEpiFree f
    have : G.IsFiniteType := ⟨inferInstanceAs (Finite (ULift.{u} (Fin n)))⟩
    have : (Limits.kernel G.π).IsFiniteType := by
      simpa only [G, SheafOfModules.GeneratingSections.ofEpiFree_π]
        using h.2 (q.X i) n f
    exact Scheme.Modules.isFinitePresentation_of_generators_kernel.{u} (F.over (q.X i)) G
  exact @SheafOfModules.IsFinitePresentation.of_coversTop _ _ _ _ _ _ _ _
    F q.I q.X q.coversTop hfp

/-- The support of the pushforward of a coherent module along a proper map is closed.

Source: Stacks Project, Theorem 088E, support of H paragraph, using Proposition 02O5
and Lemma 056J. A proper morphism over a Noetherian scheme has coherent degree-zero
pushforward. On a Noetherian scheme, the support of a coherent module is closed. The
support is the set of points where the stalk is not subsingleton, so the resulting
closed subset has exactly the displayed underlying set. The proof must transport the
coherence statement for the zeroth higher direct image across the canonical
`rightDerivedZeroIsoSelf` isomorphism with ordinary pushforward, then apply the
finite-type support closedness theorem.
(blueprint: lem-weil-pbc-proper-pushforward-support-closed)
-/
theorem exists_pushforward_support_closed
    {Z Y : Scheme.{u}} [IsNoetherian Z]
    (q : Y ⟶ Z) [IsProper q] (F : CoherentModules Y) :
    ∃ D : TopologicalSpace.Closeds Z,
      (D : Set Z) =
        {x : Z | ¬ Subsingleton (((Scheme.Modules.pushforward q).obj F.obj).presheaf.stalk x)} := by
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  letI := Scheme.Modules.isGrothendieckAbelian Y
  have hqc := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType Y F.obj).mp F.property
  letI : F.obj.IsQuasicoherent := hqc.1
  letI : F.obj.IsFinitePresentation := fp_of_coh F.obj F.property
  have hfp := Scheme.Modules.isFinitePresentation_higherDirectImage q F.obj 0
  have hq := Scheme.Modules.isQuasicoherent_higherDirectImage q F.obj 0
  let e := (Scheme.Modules.pushforward q).rightDerivedZeroIsoSelf.app F.obj
  letI : ((Scheme.Modules.pushforward q).obj F.obj).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation Z.ringCatSheaf).prop_of_iso e hfp
  letI : ((Scheme.Modules.pushforward q).obj F.obj).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent Z.ringCatSheaf).prop_of_iso e hq
  refine ⟨⟨_, (Scheme.Modules.finite_type_module_support_closed Z
    ((Scheme.Modules.pushforward q).obj F.obj)).2.2.2⟩, rfl⟩

end AlgebraicGeometry
