/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Topology.QuasiSeparated
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FinitePresentationRepresentatives
import Sheaf.AlgebraicGeometry.FinitePresentationBiprod
import Sheaf.AlgebraicGeometry.ModuleFinitePresentationCokernel
import Sheaf.AlgebraicGeometry.ModuleFinitePresentationExtension
import Sheaf.AlgebraicGeometry.ModuleFiniteTypeSubmoduleExtension
import Sheaf.AlgebraicGeometry.ModuleStalkFilteredColimit
import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage

/-!
# Quasi-coherent modules as filtered colimits of finitely presented modules

Source: Stacks Project, Properties, Lemma 01PJ
(blueprint: lem-weil-pbc-module-filtered-colimit-finite-presentation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- A quasi-coherent module on a quasi-compact quasi-separated scheme is a filtered colimit
of modules of finite presentation. Finite presentation is the local finite-free cokernel
condition of Stacks, Modules, Definition 01BN.
Source: Stacks Project, Properties, Lemma 01PJ
(blueprint: lem-weil-pbc-module-filtered-colimit-finite-presentation).

Proof:
1. Choose a set of representatives of pairs consisting of a finitely presented module and
   a map to `F` (lem-weil-pbc-module-finite-presentation-representatives, 01BC). Morphisms
   are module maps commuting with the maps to `F`.
2. The zero module gives an object. Finite direct sums give a common target for two objects
   (lem-weil-pbc-module-finite-presentation-direct-sum).
3. The cokernel of the difference of two parallel maps is finitely presented and its map
   to `F` factors uniquely, giving an equalizer to the right
   (lem-weil-pbc-module-finite-presentation-cokernel). The category is filtered.
4. The maps to `F` give a cocone and a comparison from the colimit. Its stalks are the
   comparison maps of filtered colimits of stalks (lem-weil-pbc-module-stalk-filtered-colimit,
   009E); isomorphisms are detected on stalks (lem-weil-pbc-module-iso-on-stalks).
5. A germ in a diagram term mapping to zero is represented on a quasi-compact open by a
   section mapping to zero. Its cyclic image is quasi-coherent
   (lem-weil-pbc-quasi-coherent-module-cokernel-image) and of finite type. Extend it to a
   finite-type quasi-coherent submodule of the kernel
   (lem-weil-pbc-module-finite-type-submodule-extension, 01PF). Quotient by this submodule;
   the quotient is finitely presented (lem-weil-pbc-module-finite-presentation-cokernel)
   and represents a later object killing the germ. Thus the stalk comparison is injective.
6. Represent a germ of `F` by a section on a quasi-compact neighbourhood. Extend the
   corresponding map from the structure sheaf to a map from a finitely presented module
   on `X` (lem-weil-pbc-module-finite-presentation-extension, 01PI). Its representative
   in the diagram supplies a preimage germ. Thus the stalk comparison is surjective.
7. The comparison is an isomorphism by stalkwise detection. Transporting the colimit
   cocone across it gives the stated colimit cocone with vertex `F`
   (def-weil-pbc-category-colimit). -/
theorem exists_filteredColimit_of_isQuasicoherent
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (F : X.Modules) [SheafOfModules.IsQuasicoherent.{u} (R := X.ringCatSheaf) F] :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I) (M : I ⥤ X.Modules),
      (∀ i : I, SheafOfModules.IsFinitePresentation.{u} (R := X.ringCatSheaf) (M.obj i)) ∧
        ∃ φ : M ⟶ (Functor.const I).obj F,
          Nonempty (IsColimit (Cocone.mk F φ)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
