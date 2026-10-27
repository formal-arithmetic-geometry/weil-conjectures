/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q57
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits

import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Coherent submodules exhaust a quasi-coherent module on a Noetherian algebraic space

Source: Stacks Project, Spaces Cohomology, Tags 07UV and 07UB
(blueprint: lem-sfb-space-coherent-filtered-union).

On a locally Noetherian algebraic space, coherent means quasi-coherent of finite
presentation, equivalently quasi-coherent of finite type (07UB). Thus the index below
uses the existing finite-presentation predicate. Its elements are subobjects of the
fixed module, rather than all coherent modules. Absolute quasi-separatedness is tested
on fibre products of pairs of affine scheme maps (Properties of Spaces, 0AHR).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The set of coherent submodules of a fixed module on a locally Noetherian space.
The finite-presentation predicate is equivalent to coherence under the Noetherian
hypothesis of the theorem (07UB); no new coherence predicate is introduced.
Source: Stacks, Spaces Cohomology, Tags 07UB and 07UV
(blueprint: lem-sfb-space-coherent-filtered-union). -/
abbrev CoherentSubobjects {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) :=
  {G : Subobject F // SheafOfModules.IsFinitePresentation (G : X.Modules)}

/-- The canonical diagram of coherent subobjects, with inclusion transition maps.
Source: Stacks, Spaces Cohomology, Tag 07UV
(blueprint: lem-sfb-space-coherent-filtered-union). -/
def coherentSubobjectDiagram {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) :
    CoherentSubobjects F ⥤ X.Modules :=
  (show Monotone (fun G : CoherentSubobjects F ↦ G.val) from fun _ _ h ↦ h).functor ⋙
    Subobject.underlying

/-- The cocone of actual submodule inclusions into the ambient module.
Source: Stacks, Spaces Cohomology, Tag 07UV
(blueprint: lem-sfb-space-coherent-filtered-union). -/
def coherentSubobjectCocone {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) :
    Cocone (coherentSubobjectDiagram F) where
  pt := F
  ι :=
    { app := fun G ↦ G.val.arrow
      naturality := fun _ _ f ↦ by
        dsimp [coherentSubobjectDiagram]
        rw [Category.comp_id]
        exact Subobject.underlying_arrow _ }

/-- A quasi-coherent module is the filtered colimit of its coherent submodules.
The colimit is asserted in all module sheaves. The displayed comparison is induced by
the canonical inclusion cocone, rather than an unspecified isomorphism.
Source: Stacks, Spaces Cohomology, Tag 07UV, lemma-directed-colimit-coherent
(blueprint: lem-sfb-space-coherent-filtered-union).

Proof:
1. Choose an affine surjective etale atlas U -> X. Its relation R = U x_X U consists
   of Noetherian schemes with flat, quasi-compact and quasi-separated projections.
2. Use the equivalence between quasi-coherent modules on X and on this groupoid.
   The flat Noetherian groupoid approximation theorem gives a small filtered
   coherent diagram with colimit F. Quasi-coherent colimits agree with module-sheaf
   colimits, so this cocone also has the universal property in all module sheaves.
3. The zero submodule is coherent. For two coherent submodules, the image of their
   direct sum in F is coherent and contains both. This proves nonemptiness and
   directedness of the poset of coherent subobjects.
4. The colimit of these inclusions maps monomorphically to F: sectionwise directed
   unions inject into F, and exact module sheafification preserves the zero kernel.
5. Every map from a coherent term of the diagram in step 2 factors through its
   coherent image, hence through the union. Monicity makes these factorizations
   compatible. The universal property in step 2 gives an inverse F -> union;
   uniqueness and cancellation show the two composites are identities. -/
theorem coherentSubobjects_filtered_colimit
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hln : ∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T))
    (hqc : CompactSpace (Point X.obj.obj))
    (hqs : ∀ (U V : Over S) (a : yoneda.obj U ⟶ X.obj.obj)
      (b : yoneda.obj V ⟶ X.obj.obj), IsAffine U.left → IsAffine V.left →
        CompactSpace (Point (Limits.pullback a b)))
    (F : X.Modules) [F.IsQuasicoherent] :
    Nonempty (CoherentSubobjects F) ∧
      IsDirected (CoherentSubobjects F) (· ≤ ·) ∧
      ∃ c : ColimitCocone (coherentSubobjectDiagram F),
        IsIso (c.isColimit.desc (coherentSubobjectCocone F)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
