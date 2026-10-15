/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.ConstructibleSheaf.Defs
public import Sheaf.Paper.ProEtaleFixedModuleLocalConstancy
public import Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.CategoryTheory.SiteConstantModuleIsomSheaf
import Sheaf.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import Sheaf.AlgebraicGeometry.FpqcOpenSubschemeDescent
import Sheaf.AlgebraicGeometry.ProEtaleConstantSheafStalk
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization

/-!
# Lisse pro-etale module sheaves have etale origin

Source: Stacks Project, Pro-etale Cohomology, Tag 099Y, lemma-compare-locally-constant;
Bhatt--Scholze, Corollary 5.1.5 (blueprint: lem-sf-proetale-locally-constant-origin).

Both clauses use the fixed-coefficient comparison adjunction. Local constancy uses
module-sheaf isomorphisms, and finiteness is tested at all bounded geometric points.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A fixed-coefficient pro-etale module sheaf is lisse when it is locally constant
and all geometric stalks are finite as sets. No freeness or constant rank is required.
Source: Stacks Project, Tag 099Y, specialized to a finite commutative coefficient ring
(blueprint: lem-sf-proetale-locally-constant-origin). -/
noncomputable def IsLisseProEtaleFixedModuleSheaf (X : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ]
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) : Prop :=
  IsLocallyConstantProEtaleFixedModuleSheaf X Λ F ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
      Finite (proEtaleGeometricFixedModuleStalk x Λ F)

/-- Inverse image preserves lisse module sheaves, and every lisse pro-etale module sheaf
is isomorphic to the inverse image of a lisse etale module sheaf.
Source: Stacks Project, Tag 099Y, lemma-compare-locally-constant; Bhatt--Scholze,
Corollary 5.1.5 (blueprint: lem-sf-proetale-locally-constant-origin).

Proof:
1. The comparison inverse image sends constant modules to constant modules, by the
constant-presheaf unit and sheafification (def-weil-pbc-constant-sheaf,
def-weil-pbc-sheafification, def-weil-pbc-site-comparison-morphism). This commutes with
restriction (lem-weil-pbc-comparison-pullback).
2. For an etale lisse sheaf choose a cover with finite constant module values
(lem-weil-pbc-finite-locally-constant-module-values). This is also a pro-etale cover.
Step 1 gives local constancy after inverse image. Lift each geometric point to a cover
member. Localization and the constant stalk computation give finite stalks
(lem-weil-proetale-weakly-etale-localization, lem-weil-proetale-constant-sheaf-stalk).
3. Conversely, take a pro-etale trivializing cover. At a geometric point of every
nonempty cover member its constant model is the finite stalk of the given sheaf.
Discard empty members. Every model is thus finite and, over the finite ring, finitely
presented (def-weil-proetale-geometric-stalk, lem-weil-proetale-constant-sheaf-stalk).
4. Distinct module types have empty double overlaps, by comparing their stalks.
The opens selecting one type agree on overlaps and descend by fpqc open descent
(lem-weil-pbc-open-subscheme-fpqc-descent, def-weil-pbc-proetale-site).
They give a disjoint open cover of X on each of which all models are one module M.
5. On each such open the sheaf of module-sheaf isomorphisms from the constant M to F
is a sheaf: compatible maps and their inverses glue sectionwise, with linearity and
naturality checked locally. It is locally the constant Aut(M) sheaf by finite
presentation (lem-sf-site-constant-module-isom-sheaf,
lem-weil-pbc-site-constant-restriction). Thus it is locally constant as a set sheaf.
6. Its sections on the pro-etale trivializing cover descend to sections on an etale
cover (lem-weil-pbc-proetale-locally-classical-etale-cover). Each section is a module
trivialization. Combining the disjoint opens gives an etale cover with finite models.
7. Put G = comparisonLowerStar F. On the etale cover the evaluation formula, step 1,
and the invertible comparison unit identify G with the constant finite models
(prop-weil-pbc-site-comparison-finite-level). Hence G is lisse. The counit from its
inverse image to F restricts to an isomorphism by the triangle identity and comparison
with restriction (lem-weil-pbc-comparison-pullback). Local inverses glue, giving the
required module-sheaf isomorphism. For the empty scheme take G = 0; the empty cover
and all stalk conditions are vacuous. -/
theorem proEtale_lisse_origin (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] :
    (∀ G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ),
      IsFiniteLocallyConstantSheaf G →
        IsLisseProEtaleFixedModuleSheaf X Λ
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj G)) ∧
    (∀ F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ),
      IsLisseProEtaleFixedModuleSheaf X Λ F →
        ∃ G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ),
          IsFiniteLocallyConstantSheaf G ∧
            Nonempty ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj G ≅ F)) := by
  sorry

end AlgebraicGeometry.Scheme
