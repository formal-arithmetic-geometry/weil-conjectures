/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.Directed
public import Mathlib.Topology.QuasiSeparated
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FinitePresentationHomColimit
import Sheaf.AlgebraicGeometry.QcqsSchemeCofinalFiniteCoverings
import Sheaf.CategoryTheory.ModuleDirectedColimitUnderlyingSets
import Sheaf.Topology.SheavesDirectedColimitSections
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom

/-!
# Maps from finitely presented module sheaves into directed colimits

Source: Stacks Project, Modules, Lemma 01BS, specialized to qcqs schemes
(blueprint: lem-weil-pbc-finite-presentation-hom-directed-colimit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Stacks Project, Modules, Lemma 01BS:
(blueprint: lem-weil-pbc-finite-presentation-hom-directed-colimit).
For a finitely presented module sheaf on a qcqs scheme, the canonical map from the directed
colimit of Hom sets is bijective, expressed by factorization and eventual equality.
Finite presentation means locally the cokernel of a map of finite free module sheaves (01BN).

Proof:
1. Form the sheaf Homs from `G` to the diagram terms and to `c.pt`
   (def-pur-sheaf-hom). Their global sections are the corresponding Hom sets, with
   postcomposition as transition maps and cocone maps.
2. Finite presentation identifies the colimit of these sheaf Homs with the sheaf Hom into
   `c.pt` (lem-weil-pbc-sheaf-hom-finite-presentation-colimit, Stacks 0GMV).
3. Finite affine open covers of a qcqs scheme are cofinal, and their pairwise intersections
   are quasi-compact (lem-weil-pbc-qcqs-scheme-cofinal-finite-coverings).
4. The underlying set sheaf of the module colimit is the colimit of underlying set sheaves
   (lem-weil-pbc-module-directed-colimit-underlying-sets). Global sections commute with this
   colimit by the covering condition (lem-weil-pbc-sheaves-directed-colimit-sections, 009F).
   Composing with the isomorphism of step 2 gives the canonical Hom-set bijection.
5. Surjectivity gives the first clause. In a directed colimit of sets, two representatives
   are equal exactly when they agree at a common later stage (def-weil-pbc-category-colimit),
   so injectivity gives the second clause. -/
theorem hom_directedColimit_of_isFinitePresentation
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (I : Type u) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ X.Modules) (c : Cocone D) (hc : IsColimit c)
    (G : X.Modules)
    [SheafOfModules.IsFinitePresentation.{u} (R := X.ringCatSheaf) G] :
    (∀ h : G ⟶ c.pt, ∃ (i : I) (g : G ⟶ D.obj i), g ≫ c.ι.app i = h) ∧
    (∀ (i j : I) (g : G ⟶ D.obj i) (g' : G ⟶ D.obj j),
      g ≫ c.ι.app i = g' ≫ c.ι.app j →
      ∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k),
        g ≫ D.map (homOfLE hik) = g' ≫ D.map (homOfLE hjk)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
