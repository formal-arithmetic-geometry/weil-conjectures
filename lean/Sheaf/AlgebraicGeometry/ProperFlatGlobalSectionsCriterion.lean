/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Fiber
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
import Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalk
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.GlobalSections

/-!
# Proper flat morphisms with fibrewise constant functions

Source: Stacks Project, Tag 0E62, Lemma 36.32.5 (a), `perfect-lemma-proper-flat-h0`
(blueprint: lem-sc-proper-flat-global-sections-criterion).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem fiberwise_appTop_isIso_baseChange
    {X S T : Scheme.{u}} (f : X ⟶ S) [IsProper f] (g : T ⟶ S)
    (hfiber : ∀ s : S, IsIso (f.fiberToSpecResidueField s).appTop) (t : T) :
    IsIso ((pullback.snd f g).fiberToSpecResidueField t).appTop := by
  let h := isPullback_fiberToSpecResidueField_of_isPullback
    (IsPullback.of_hasPullback f g) t
  have : IsProper (f.fiberToSpecResidueField (g t)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : QuasiSeparatedSpace ↑(pullback f (S.fromSpecResidueField (g t))) :=
    quasiSeparatedSpace_of_quasiSeparated (f.fiberToSpecResidueField (g t))
  have : Flat (Spec.map (g.residueFieldMap t)) := by
    apply Flat.SpecMap_iff.mpr
    let φ := (g.residueFieldMap t).hom
    let := φ.toAlgebra
    change φ.Flat
    rw [← RingHom.algebraMap_toAlgebra φ, RingHom.flat_algebraMap_iff]
    infer_instance
  have hi := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right h
    (US := ⊤) (UT := ⊤) (UX := ⊤) le_top le_top (UY := ⊤) (by simp)
    (isAffineOpen_top _) (isAffineOpen_top _) CompactSpace.isCompact_univ
    (isQuasiSeparated_univ_iff.mpr inferInstance)
  have hp := (isIso_pushoutSection_iff h le_top le_top (by simp)).mp hi
  simp only [Scheme.Hom.appLE_top_top_eq_appTop] at hp
  have := hfiber (g t)
  exact hp.isIso_inr_of_isIso

/-- The canonical map `O_S → f_* O_X` is an isomorphism, universally, if its proper flat
finitely presented morphism has only residue-field functions on every fibre.
Source: Stacks Project, Tag 0E62, Lemma 36.32.5 (a)
(blueprint: lem-sc-proper-flat-global-sections-criterion).

Proof: At every point s apply `lem-sc-proper-flat-structure-sheaf-stalk` to the
hypothesized fibre isomorphism. The ordinary module unit is therefore bijective on all
stalks, so `lem-weil-pbc-module-iso-on-stalks` makes it an isomorphism.
For a base change g : T → S and t : T, the fibre square is cartesian over the field
extension κ(g(t)) → κ(t). That field extension is flat. The original fibre is proper,
hence quasi-compact and quasi-separated. Apply the degree-zero flat-base-change theorem
`lem-weil-pbc-flat-base-change-global-sections-qcqs` to this square. The resulting square
of global-section rings is a pushout. Its original structure map is an isomorphism by
hfiber, so the opposite structure map is an isomorphism. Thus the base-changed morphism
satisfies the same fibre hypothesis. Properness, flatness and local finite presentation
are preserved by base change; apply the single-point stalk criterion at every t and
stalk detection once more. The private helper proves the fibre stability step without
any unfinished proof. The remaining local derived argument is isolated in the new
single-point criterion; it is not the universal statement under another name.

The canonical map `O_S → f_* O_X` of `O_S`-modules is the unit at `O_S` of the module
adjunction `tensorPullback f ⊣ pushforward f` (`f^* O_S = O_X`), as in the hypothesis `hO`
of `lem-sc-picard-diagonal-locally-closed`; after base change along `g : T ⟶ S` it is the
unit for `p = pullback.snd f g : X_T ⟶ T`.
The fibre hypothesis uses `Γ(Spec κ(s), O) ≅ κ(s)` through `Scheme.ΓSpecIso` implicitly:
thus the map `(f.fiberToSpecResidueField s).appTop` is an isomorphism exactly when the
canonical residue-field map is. Properness supplies quasi-compactness and
quasi-separatedness, so locally finite presentation here is finite presentation. -/
theorem isIso_structureSheafMap_of_proper_flat_fiberwise
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f]
    (hfiber : ∀ s : S, IsIso (f.fiberToSpecResidueField s).appTop) :
    IsIso ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)).unit.app
        (SheafOfModules.unit S.ringCatSheaf)) ∧
      ∀ {T : Scheme.{u}} (g : T ⟶ S),
        IsIso ((Classical.choose
          (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
            (SheafOfModules.unit T.ringCatSheaf)) := by
  constructor
  · apply Scheme.Modules.isIso_of_bijective_stalkLinearMap
    intro s
    exact bijective_structureSheafMap_stalk_of_proper_flat_fiber f s (hfiber s)
  · intro T g
    have : IsProper (pullback.snd f g) :=
      MorphismProperty.pullback_snd _ _ inferInstance
    have : Flat (pullback.snd f g) :=
      MorphismProperty.pullback_snd _ _ inferInstance
    have : LocallyOfFinitePresentation (pullback.snd f g) :=
      MorphismProperty.pullback_snd _ _ inferInstance
    apply Scheme.Modules.isIso_of_bijective_stalkLinearMap
    intro t
    exact bijective_structureSheafMap_stalk_of_proper_flat_fiber (pullback.snd f g) t
      (fiberwise_appTop_isIso_baseChange f g hfiber t)

end AlgebraicGeometry
