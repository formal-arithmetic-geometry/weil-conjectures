/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Sheaf.AlgebraicGeometry.Coherent
import Sheaf.AlgebraicGeometry.ModuleFiniteTypeImageExtension
import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import Sheaf.AlgebraicGeometry.QuasiCoherentExtensionQcOpen
import Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine

/-!
# Extension of finite-type quasi-coherent submodules

Source: Stacks Project, Properties, Lemma 01PF.
(blueprint: lem-weil-pbc-module-finite-type-submodule-extension).
-/

@[expose] public section

universe u

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

/-- A finite-type quasi-coherent submodule on a quasi-compact open extends to the scheme.

Source: Stacks Project, Properties, Lemma 01PF.
(blueprint: lem-weil-pbc-module-finite-type-submodule-extension).

Proof:
1. Take a finite affine cover together with U and successively enlarge U
   (lem-weil-pbc-affine-opens-basis, lem-weil-pbc-affine-scheme-qcqs).
2. For one affine V, W intersect V is quasi-compact by spectrality
   (lem-weil-pbc-qcqs-scheme-spectral, def-weil-spectral-space). Use
   lem-weil-pbc-quasi-coherent-extension-qc-open and take the image of its extension
   map, quasi-coherent by lem-weil-pbc-quasi-coherent-module-cokernel-image.
   This image restricts to the prescribed submodule because its inclusion is injective.
3. On V = Spec R, identify that image with the tilde of its sections N using
   lem-weil-pbc-affine-tilde-gamma-adjunction. Cover W intersect V by finitely many
   principal opens where N localized is finite, using
   lem-weil-pbc-quasi-coherent-finite-type-affine and
   lem-weil-pbc-principal-localization-open-immersion.
4. Generate N' by the numerators of those finitely many local generators. The image of
   its tilde is quasi-coherent and finite type by lem-weil-pbc-spec-module-tilde-sections,
   lem-weil-pbc-quasi-coherent-finite-type-affine and
   lem-weil-pbc-module-finite-type-image-extension.
5. Its localization contains every selected generator, hence equals the original
   submodule on each principal open. The tilde counit makes these equalities equalities
   of sheaves; the sheaf property yields equality on W intersect V.
6. Glue the submodules on W and V by requiring both membership conditions on sections.
   Their common restriction makes the glued sheaf restrict to each one. Quasi-coherence
   and finite type are local, by pqf-def-coherent and
   def-weil-pbc-module-finite-type-presentation.
7. Induct along the finite affine cover to obtain the required submodule on X.
   All restriction identifications commute with the inclusions into F; this yields e. -/
theorem exists_quasicoherent_finiteType_submodule_extension
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (U : X.Opens) (hU : IsCompact (U : Set X))
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)) [F.IsQuasicoherent]
    (G : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
    [G.IsQuasicoherent] [G.IsFiniteType]
    (ι : G ⟶ F.over U) [Mono ι] :
    ∃ (G' : SheafOfModules.{u} (moduleRings X.toRingedSpace)),
      G'.IsQuasicoherent ∧ G'.IsFiniteType ∧
        ∃ (ι' : G' ⟶ F), Mono ι' ∧ ∃ (e : G'.over U ≅ G),
          (SheafOfModules.overFunctor (moduleRings X.toRingedSpace) U).map ι' = e.hom ≫ ι := by
  sorry

end AlgebraicGeometry.Scheme.Modules
