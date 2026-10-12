/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Sheaf.AlgebraicGeometry.BaseChangeConventions
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
import Sheaf.AlgebraicGeometry.GlobalSectionsGeomConnected
import Sheaf.AlgebraicGeometry.ProperFlatGlobalSectionsCriterion

/-!
# Universal structure-sheaf pushforward for proper flat morphisms

Source: Stacks Project, Derived Categories of Schemes, Tag 0E0L
(blueprint: lem-sc-proper-flat-global-sections).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A proper flat morphism of finite presentation whose residue-field fibres are geometrically
reduced and geometrically connected has canonical map `𝒪_S → f_* 𝒪_X` an isomorphism,
universally. The canonical map `𝒪_T → p_* 𝒪_{X_T}` (for `p = pullback.snd f g`) is rendered as
the unit at `𝒪_T` of the module pullback/pushforward adjunction
`Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction p)`, i.e.
`𝒪_T → p_* p^* 𝒪_T` with `p^* 𝒪_T ≅ 𝒪_{X_T}`; this is the form of the hypothesis `hO` of
`lem-sc-picard-diagonal-locally-closed`. Locally of finite presentation together with
properness (quasi-compact, quasi-separated) is finite presentation.
Source: Stacks Project, Tag 0E0L (blueprint: lem-sc-proper-flat-global-sections).

Proof: apply the fibrewise criterion `lem-sc-proper-flat-global-sections-criterion` to `f`,
which is proper, flat and of finite presentation. For each `s`, its fibre is proper over
`κ(s)` by stability of properness under base change, and is geometrically reduced and
geometrically connected by hypothesis (`def-pc-geometrically-irreducible`). The field theorem
`lem-pc-h0-geom-connected` (Stacks, Tag 0BUG) therefore identifies the canonical map
`κ(s) → H⁰(X_s, 𝒪_{X_s})` as an isomorphism. The criterion gives `𝒪_S ≅ f_* 𝒪_X`, and its
universal clause gives the same conclusion after every morphism `T → S`. -/
theorem isIso_structureSheafMap_of_proper_flat_geometricallyReduced_connected_fibers
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f]
    (hred : ∀ s : S, GeometricallyReduced (f.fiberToSpecResidueField s))
    (hconn : ∀ s : S, GeometricallyConnected (f.fiberToSpecResidueField s)) :
    IsIso ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)).unit.app
        (SheafOfModules.unit S.ringCatSheaf)) ∧
      ∀ {T : Scheme.{u}} (g : T ⟶ S),
        IsIso ((Classical.choose
          (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
            (SheafOfModules.unit T.ringCatSheaf)) := by
  apply isIso_structureSheafMap_of_proper_flat_fiberwise f
  intro s
  let k : Type u := S.residueField s
  let F := f.fiberToSpecResidueField s
  let : (Scheme.Hom.fiber f s).Over (Spec (.of k)) :=
    f.fiberOverSpecResidueField s
  let : GeometricallyReduced ((Scheme.Hom.fiber f s) ↘ Spec (.of k)) := hred s
  have : IsProper ((Scheme.Hom.fiber f s) ↘ Spec (.of k)) := by
    change IsProper (pullback.snd f (S.fromSpecResidueField s))
    exact MorphismProperty.pullback_snd _ _ inferInstance
  have hbij : Function.Bijective (Scheme.globalSectionsRingHom k
      (X := Scheme.Hom.fiber f s)) :=
    (Scheme.globalSectionsRingHom_bijective_iff_geometricallyConnected k
      (Scheme.Hom.fiber f s)).2 (hconn s)
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ F.appTop) :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).2 hbij
  exact IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of k)).inv F.appTop

end AlgebraicGeometry
