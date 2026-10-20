/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentAffineSectionsFinite
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.ClosedSupportPushforwardSupport
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex

/-! # Closed support of a proper coherent pushforward

Source: Stacks Project, Theorem 088E, support of H paragraph, and Proposition 02O5.
The assertion isolates closedness and containment; properness over a further base
is proved separately in `ChowAlgebraizationSupport`.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- The support of a pushforward is closed and is contained in the image of the support.
Source: Stacks Project, Tag 088E, support paragraph (the closedness and stalk argument).
(blueprint: new-chow-pushforward-support-closed)

Proof: A proper morphism to the Noetherian Z is of finite type, hence Y is
Noetherian too. Tag 02O5 implies that q_*F is coherent. On a Noetherian scheme,
a coherent module is quasi-coherent of finite type (Tag 01XZ), so its support is
closed (Tag 056J). Give that support its closed-set structure D.
Because q is proper it is a closed map; thus q(C) is closed. For x outside q(C),
the open neighbourhood V = Z \ q(C) has inverse image disjoint from C. Every
stalk of F on q^{-1}(V) is zero by hC. Given two sections over any open inside
q^{-1}(V), equality of their germs supplies a neighbourhood of each point on
which they agree. Sheaf separatedness then makes the sections equal, including
on the empty open. Therefore q_*F has only one section over every open inside V.
Every germ at x is represented on an open neighbourhood; intersect that open
with V to conclude that the stalk of q_*F at x is zero. Taking the contrapositive
gives D ⊆ q(C). The construction also covers F = 0 and empty Y or Z.
-/
theorem pushforward_support_closed_subset
    {Z Y : Scheme.{u}} [IsNoetherian Z]
    (q : Y ⟶ Z) [IsProper q] (F : CoherentModules Y)
    (C : TopologicalSpace.Closeds Y)
    (hC : (C : Set Y) = {x : Y | ¬ Subsingleton (F.obj.presheaf.stalk x)}) :
    ∃ D : TopologicalSpace.Closeds Z,
      (D : Set Z) =
        {x : Z | ¬ Subsingleton (((Scheme.Modules.pushforward q).obj F.obj).presheaf.stalk x)} ∧
      (D : Set Z) ⊆ q '' (C : Set Y) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  have := Scheme.Modules.isGrothendieckAbelian Y
  have hq := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType Y F.obj).mp
    F.property
  have : F.obj.IsQuasicoherent := hq.1
  have : F.obj.IsFinitePresentation := by
    have hfp (V : Y.affineOpens) : (F.obj.over V.1).IsFinitePresentation := by
      have := IsLocallyNoetherian.component_noetherian V
      have := Scheme.Modules.coherent_affine_sections_finite Y F.obj F.property V.1 V.2
      have hp := Module.finitePresentation_of_finite Γ(Y, V.1) Γ(F.obj, V.1)
      exact (((Scheme.Modules.quasicoherent_finite_type_affine.{u, u} Y).2 F.obj hq.1).1
        V.1 V.2).2.mpr hp
    exact @SheafOfModules.IsFinitePresentation.of_coversTop _ _ _ _ _ _ _ _ F.obj
      Y.affineOpens (fun V ↦ V.1) (by
        rw [Opens.coversTop_iff]
        exact iSup_affineOpens_eq_top Y) hfp
  have hfp := Scheme.Modules.isFinitePresentation_higherDirectImage q F.obj 0
  have : ((Scheme.Modules.pushforward q).obj F.obj).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation Z.ringCatSheaf).prop_of_iso
      ((Scheme.Modules.pushforward q).rightDerivedZeroIsoSelf.app F.obj) hfp
  let D : TopologicalSpace.Closeds Z :=
    ⟨_, (Scheme.Modules.finite_type_module_support_closed Z
      ((Scheme.Modules.pushforward q).obj F.obj)).2.2.2⟩
  refine ⟨D, rfl, ?_⟩
  let T : TopologicalSpace.Closeds Z :=
    ⟨q.base '' (C : Set Y), q.isClosedMap _ C.isClosed⟩
  apply Scheme.Modules.pushforward_support_subset_of_closed_support q F.obj T
  intro y hy
  change q.base y ∈ (T : Set Z)
  exact ⟨y, by rw [hC]; exact hy, rfl⟩

end AlgebraicGeometry
