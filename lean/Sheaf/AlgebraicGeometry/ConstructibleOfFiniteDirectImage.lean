/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import Sheaf.AlgebraicGeometry.ConstructibleSubsheafNoetherian
import WeilConjectures.SixFunctors.Finite.Stalk
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.ConstructibleSheaf.KernelCokernel

/-!
# Finite direct image reflects constructibility

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc`, lemma
`lem-fin-finite-reflects-constructibility`
(blueprint: lem-fin-finite-reflects-constructibility).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A module sheaf over a finite commutative ring on a Noetherian scheme is constructible
if its direct image along a finite morphism to a Noetherian scheme is constructible.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc`, lemma
`lem-fin-finite-reflects-constructibility`; Stacks Project, Tags 095G, 03QP, 03PT,
03PU, 09BH and 03RZ (blueprint: lem-fin-finite-reflects-constructibility).

Proof:
1. Put G = p_*F. Pull back its finite constructible stratification and its module
   trivializations to see that H = p^{-1}G is constructible
   (`prop-constructible-pullback`, `def-constructible-constant`,
   `lem-pur-scheme-constructible-preimage`).
2. The inverse-image stalk identification, its compatibility with germs and the
   adjunction triangle identity identify the counit H → F on each geometric stalk
   with the finite-fibre product projection. It is surjective, without requiring p
   to be surjective (`lem-weil-pbc-inverse-image-stalk-germ`,
   `lem-weil-pbc-finite-stalk-formula-restriction`).
3. Exact geometric stalks make the cokernel of the counit have zero stalks.
   Conservativity applied to its map to zero shows that it is zero, so the counit
   is epic (`prop-weil-pbc-geometric-stalks-exact`,
   `lemma-weil-pbc-geometric-stalk-conservative`). These maps preserve the module action.
4. Its kernel is constructible by `lem-weil-pbc-constructible-subobjects-noetherian`.
   Its inclusion into H is a morphism between constructible module sheaves, hence
   has constructible cokernel by `thm-constructible-serre`. Since the counit is epic,
   this cokernel is isomorphic to F. Transport the stratification and trivializations
   across that isomorphism. -/
theorem isConstructibleEtaleModuleSheaf_of_finite_lowerStar
    {Z S : Scheme.{u}} [IsNoetherian Z] [IsNoetherian S]
    (p : Z ⟶ S) [IsFinite p] {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleEtaleModuleSheaf ((Etale.lowerStar (ModuleCat.{u + 1} Λ) p).obj F)) :
    IsConstructibleEtaleModuleSheaf F := by
  sorry

end AlgebraicGeometry.Scheme
