/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Connected.Basic
import Sheaf.AlgebraicGeometry.FundamentalGroup.OpenSubgroups
import Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence
import Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.Topology.NoetherianSpace

/-!
# Finite étale trivialization of a lisse sheaf

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-a1-kummer/
fin2-lem-lisse-trivialized-finite-etale.md, node fin2-lem-lisse-trivialized-finite-etale,
order 1904 (blueprint: fin2-lem-lisse-trivialized-finite-etale).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry Scheme

namespace AlgebraicGeometry

/-- A finite locally constant module sheaf on a finite-type scheme over a field is
trivialized by a finite étale surjective cover.  On each connected component of the
cover the pullback is constant with a finite module value; when the base is connected,
one common finite module value works on the whole cover.
Source: blueprint node `fin2-lem-lisse-trivialized-finite-etale`, order 1904
(blueprint: fin2-lem-lisse-trivialized-finite-etale).

Proof, following the node:
1. A field is Noetherian. Finite type over its spectrum makes X Noetherian by
   `lem-weil-pbc-finite-type-over-noetherian`. By
   `lem-sc-noetherian-closed-subset-finite-components`, X has finitely many irreducible
   components. Each is connected and lies in one connected component, so the connected
   components are finite unions of closed irreducible components. They are closed, and
   their complements are finite unions of closed components, hence they are also open.
   Work on these nonempty connected open-and-closed subschemes; for empty X use its identity.
2. Choose a geometric point of one component X₀. The lisse clause of
   `def-weil-pbc-constructible-complexes` gives a finite stalk M. The equivalences of
   `thm-galois-lc-etale` and `thm-galois-fundamental` identify the underlying sheaf with
   a finite continuous action of π₁(X₀). Preservation of products and faithfulness
   identify the stalks of the addition, zero and scalar operations with the module
   operations on M. Their equivariance makes each group element a module automorphism.
3. Let H be the subgroup fixing every element of M. Action identities give closure
   under products and inverses. Continuity of each orbit map to the finite discrete
   set M makes each point stabilizer open. Their finite intersection H is open.
4. The pointed clause of `cor-galois-open-subgroups` realizes H by a nonempty connected
   finite étale cover P₀ of X₀. The finite-étale base-change clause of
   `thm-galois-fundamental` identifies π₁(P₀) with H, and base-change compatibility in
   `thm-galois-lc-etale` identifies the pulled-back action with restriction to H.
   This action is trivial. The constant set sheaf of M is the finite coproduct of
   terminal sheaves, hence corresponds to the trivial action by preservation of finite
   colimits. Full faithfulness gives the sheaf isomorphism inducing the identity on M.
   Its compatibility with addition, zero and each scalar follows by faithfulness and
   preservation of products, so it is an isomorphism of module sheaves to the constant
   sheaf of `def-weil-pbc-constant-sheaf`. The module need not be free.
5. The degree clause of `cor-galois-open-subgroups` gives degree [G:H] ≥ 1. By
   `def-pc-finite-locally-free`, each fibre algebra has this positive dimension, so no
   fibre is empty and the cover is surjective. Form the coproduct of these covers by
   `lem-weil-pbc-scheme-coproduct-family`. Its restriction over each clopen component
   is the constructed finite cover; `lem-weil-pbc-finite-local-on-target` makes the
   union finite. The affine-local criterion in `def-weil-etale-morphism` makes it étale,
   since the source and target charts of the components cover the union. Surjectivity
   follows componentwise. The connected clopen summands are precisely its connected
   components and carry the finite constant module values. When X is connected there
   is only one base component and one common finite module value on all of P. -/
theorem exists_finite_etale_surjective_trivializing_lisse
    (k : Type u) [Field k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hL : Scheme.IsFiniteLocallyConstantSheaf L) :
    ∃ (P : Scheme.{u}) (p : P ⟶ X),
      IsFinite p ∧ Etale p ∧ Surjective p ∧
        (∀ (x : P),
          ∃ U : P.Opens, (U : Set P) = connectedComponent x ∧
            ∃ M : ModuleCat.{u + 1} Λ,
            Finite M ∧
              Nonempty
                ((Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj
                  ((Etale.upperStar (ModuleCat.{u + 1} Λ) p).obj L) ≅
                  (constantSheaf U.toScheme.smallEtaleTopology
                    (ModuleCat.{u + 1} Λ)).obj M)) ∧
        (ConnectedSpace X →
          ∃ (M : ModuleCat.{u + 1} Λ), Finite M ∧
            Nonempty
              ((Etale.upperStar (ModuleCat.{u + 1} Λ) p).obj L ≅
                (constantSheaf P.smallEtaleTopology
                  (ModuleCat.{u + 1} Λ)).obj M)) := by
  sorry

end AlgebraicGeometry
