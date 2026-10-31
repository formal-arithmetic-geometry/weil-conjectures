/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.CoherentFiltrationIntegralSubschemes
import WeilConjectures.AlgebraicGeometry.CoherentPropertyIrreducible
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.FinitePushforwardCoherent
import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineVanishing

/-! # Devissage of coherent module properties

Source: Stacks Project, Cohomology of Schemes, Lemma 30.12.6, Tag 01YI.
(blueprint: lem-pc-coherent-property-devissage)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits ZeroObject AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- Devissage criterion for properties of coherent modules.
Source: Stacks Project, Cohomology of Schemes, Lemma 30.12.6 (Tag 01YI),
coherent.tex line 3270 (blueprint: lem-pc-coherent-property-devissage).
The residue-field action in hypothesis (2) is the quotient of the original
stalk-ring action. The point ξ is required to be generic in Z, as in 01YI.

Proof: two out of three and the zero hypothesis give invariance under isomorphism.
Induct on the closed subsets of X to show that P holds for every ideal pushforward
from an integral closed subscheme whose image is contained in the chosen closed set.
For i : Z → X, its image is irreducible closed and i(η_Z) is its generic point.
Every strictly smaller integral closed image is covered by the induction hypothesis.
Apply the irreducible-support criterion 01YH, with the witness from hypothesis (2),
to obtain P for i_*I. The ideal is coherent because Z is locally Noetherian and it
is a quasi-coherent submodule of the coherent structure sheaf; finite pushforward
preserves coherence. Its support is contained in i(Z), since stalks vanish off the
closed image. Finally use the integral-ideal filtration 01YF of any coherent F.
Each cokernel has P by the induction result and isomorphism invariance. Induction
on the finite chain, starting with its zero subobject, gives P for F. This includes
the length-zero filtration and an empty scheme.
-/
theorem coherent_property_devissage
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (P : X.Modules → Prop)
    (hP_zero : ∀ F : X.Modules, IsZero F → P F)
    (hP_seq : ∀ (S : ShortComplex X.Modules), S.ShortExact →
      RingedSpace.IsCoherent X.toRingedSpace S.X₁ →
      RingedSpace.IsCoherent X.toRingedSpace S.X₂ →
      RingedSpace.IsCoherent X.toRingedSpace S.X₃ →
      ((P S.X₁ ∧ P S.X₂) ∨ (P S.X₁ ∧ P S.X₃) ∨ (P S.X₂ ∧ P S.X₃)) →
      P S.X₁ ∧ P S.X₂ ∧ P S.X₃)
    (hP_integral : ∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsIntegral Z]
      [IsClosedImmersion i] (ξ : Z) (_hξ : IsGenericPoint ξ Set.univ),
      ∃ G : X.Modules,
        RingedSpace.IsCoherent X.toRingedSpace G ∧
        (∀ x : X, (¬ Subsingleton (G.presheaf.stalk x)) ↔
          x ∈ Set.range i.base) ∧
        (∀ (r : X.presheaf.stalk (i.base ξ)),
          r ∈ IsLocalRing.maximalIdeal _ →
            ∀ m : (PresheafOfModules.stalkObj X.ringCatSheaf.presheaf (i.base ξ) G.val),
              r • m = 0) ∧
        (∃ hκ : Module (X.residueField (i.base ξ))
            (PresheafOfModules.stalkObj X.ringCatSheaf.presheaf (i.base ξ) G.val),
          (∀ (r : X.presheaf.stalk (i.base ξ))
            (m : PresheafOfModules.stalkObj X.ringCatSheaf.presheaf (i.base ξ) G.val),
            r • m = (X.residue (i.base ξ)) r • m) ∧
          @Module.finrank _ _ _ _ hκ = 1) ∧
        P G)
    : ∀ F : X.Modules, RingedSpace.IsCoherent X.toRingedSpace F → P F := by
  classical
  have : IsNoetherian X := {}
  have hcoh := RingedSpace.coherent_kernel_cokernel_sum X.toRingedSpace
  have hzero := hcoh.2.2.2.1
  have hiso {F G : X.Modules} (e : F ≅ G)
      (hF : RingedSpace.IsCoherent X.toRingedSpace F) (hG : P G) : P F := by
    let S : ShortComplex X.Modules := ShortComplex.mk (0 : 0 ⟶ F) e.hom (by simp)
    have hs : S.ShortExact :=
      { exact := (S.exact_iff_mono rfl).mpr inferInstance }
    exact (hP_seq S hs hzero hF (hcoh.2.2.2.2 _ _ e hF)
      (Or.inr (Or.inl ⟨hP_zero _ (isZero_zero _), hG⟩))).2.1
  have hideal (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i]
      (I : Z.IdealSheafData) :
      RingedSpace.IsCoherent X.toRingedSpace ((pushforward i).obj I.toModules) := by
    have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
    have : (SheafOfModules.unit Z.ringCatSheaf).IsQuasicoherent :=
      SheafOfModules.isQuasicoherent_unit.{u, u, u}
    have : (SheafOfModules.unit I.subscheme.ringCatSheaf).IsQuasicoherent :=
      SheafOfModules.isQuasicoherent_unit.{u, u, u}
    have : ((SheafOfModules.pushforward I.subschemeι.toRingCatSheafHom).obj
        (SheafOfModules.unit I.subscheme.ringCatSheaf)).IsQuasicoherent :=
      isQuasicoherent_pushforward_of_isAffineHom I.subschemeι _
    have hIq : I.toModules.IsQuasicoherent := isQuasicoherent_kernel I.toPushforwardSubscheme
    have hIc := ((isCoherent_kernel_cokernel_biprod_and_submodule Z).2
      _ _ I.toModulesι (isCoherent_unit_of_finite_to_locallyNoetherian i)
      inferInstance hIq).1
    exact (isCoherent_pushforward_of_isFinite i I.toModules hIc).1
  have hsupport (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i]
      (I : Z.IdealSheafData) :
      {x : X | ¬ Subsingleton (((pushforward i).obj I.toModules).presheaf.stalk x)} ⊆
        Set.range i.base := by
    intro x hx
    by_contra hn
    exact hx ((closedImmersion_pushforward_stalks i i.isClosedEmbedding I.toModules).1 x hn)
  have hgood : ∀ T : TopologicalSpace.Closeds X,
      ∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z],
        Set.range i.base ⊆ (T : Set X) →
          ∀ I : Z.IdealSheafData, P ((pushforward i).obj I.toModules) := by
    intro T
    induction T using WellFoundedLT.induction with
    | ind T ih =>
      intro Z i hi hZ hrange I
      let ξ := i.base (genericPoint Z)
      have hξ : IsGenericPoint ξ (Set.range i.base) := by
        simpa only [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq]
          using (genericPoint_spec Z).image i.continuous
      have hirr : IsIrreducible (Set.range i.base) := hξ.isIrreducible
      apply coherent_property_irreducible X (Set.range i.base)
        i.isClosedEmbedding.isClosed_range hirr ξ hξ P
      · intro S hS h₁ h₂ h₃ _ _ _
        exact ⟨fun h ↦ (hP_seq S hS h₁ h₂ h₃ (Or.inl h)).2.2,
          fun h ↦ (hP_seq S hS h₁ h₂ h₃ (Or.inr (Or.inl h))).2.1,
          fun h ↦ (hP_seq S hS h₁ h₂ h₃ (Or.inr (Or.inr h))).1⟩
      · intro Z' j hj hZ' hsub J
        have := hj
        have := hZ'
        let T' : TopologicalSpace.Closeds X :=
          ⟨Set.range j.base, j.isClosedEmbedding.isClosed_range⟩
        exact ih T' (Set.ssubset_of_ssubset_of_subset hsub hrange) Z' j
          (by rfl) J
      · obtain ⟨G, hGc, hGs, hGk, hGr, hGP⟩ :=
          hP_integral Z i (genericPoint Z) (genericPoint_spec Z)
        exact ⟨G, hGc, Set.ext hGs, hGk, hGr, hGP⟩
      · exact hideal Z i I
      · exact hsupport Z i I
  intro F hF
  obtain ⟨m, c, hc, hbot, htop, hcc, hquot⟩ :=
    exists_coherent_filtration_integral_subschemes X F hF
  have hpieces (j : Fin m) :
      P (cokernel (Subobject.ofLE (c j.castSucc) (c j.succ) (hc j.castSucc_le_succ))) := by
    obtain ⟨Z, i, hi, hZ, I, _, _, ⟨e⟩⟩ := hquot j
    have := hi
    have := hZ
    have hq := (hcoh.1 _ _
      (Subobject.ofLE (c j.castSucc) (c j.succ) (hc j.castSucc_le_succ))
      (hcc j.castSucc) (hcc j.succ)).2
    exact hiso e hq (hgood ⊤ Z i (by simp) I)
  have hpc : ∀ j : Fin (m + 1), P (c j : X.Modules) := by
    intro j
    induction j using Fin.induction with
    | zero =>
      apply hP_zero
      exact (isZero_zero X.Modules).of_iso
        (Subobject.isoOfEq _ _ hbot ≪≫ Subobject.botCoeIsoZero)
    | succ j ih =>
      let f := Subobject.ofLE (c j.castSucc) (c j.succ) (hc j.castSucc_le_succ)
      let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
      have hs : S.ShortExact := { exact := ShortComplex.exact_cokernel f }
      exact (hP_seq S hs (hcc _) (hcc _) (hcoh.1 _ _ f (hcc _) (hcc _)).2
        (Or.inr (Or.inl ⟨ih, hpieces j⟩))).2.1
  exact hiso (Subobject.isoOfEq _ _ htop ≪≫ asIso (⊤ : Subobject F).arrow).symm hF
    (hpc _)

end AlgebraicGeometry
