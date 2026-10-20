/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q98
-/
module

public import Sheaf.CategoryTheory.Sites.GrothendieckTopos
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Sheaf.CategoryTheory.ToposCompatibleGenerators
import Sheaf.CategoryTheory.SheafSubcategoryComparison

/-!
# Covering-family presentation of a sieve sheaf category

Source: Stacks Project, `literature/stacks-project/sites.tex`, Tags 03CI and 03A1,
with the arbitrary-sieve extension described in the node source
(blueprint: lem-trf-sieve-sheaves-covering-site).
-/

@[expose] public section

set_option autoImplicit false

universe w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/--
Source: Stacks Project, `literature/stacks-project/sites.tex`, Tags 03CI and 03A1,
with Tag 00ZM for sheafification (blueprint: lem-trf-sieve-sheaves-covering-site).

Proof: Apply the compatible finite-limit generator construction to the identity
functor of the given sheaf category. One resulting small category has a fully
faithful, finite-limit-preserving inclusion and contains the sheafified
representables. Its pullbacks map to pullbacks of sheaves. Apply the sieve-topology
subcategory presentation theorem to equip this small category with the epimorphic
precoverage and obtain the required equivalence. This argument uses the given
sieve topology directly and assumes no pullbacks in D.
-/
theorem exists_coveringSite_of_sieveTopology
    (D : Type w) [SmallCategory D] (J : GrothendieckTopology D) :
    ∃ (S : Type w) (_ : SmallCategory S) (K : Precoverage S),
      K.IsSiteForCoverings ∧
        Nonempty (Sheaf J (Type w) ≌ Sheaf K.toGrothendieck (Type w)) := by
  obtain ⟨S, T, hS, hT, hlimS, hlimT, F, G, v,
      hfull, hfaith, hlim, _, _, _, _, _, hrep, _⟩ :=
    topos_compatibleGenerators J J (𝟭 (Sheaf J (Type w)))
  have hpb : ∀ (A B X : S) (f : A ⟶ X) (g : B ⟶ X),
      ∃ (P : S) (p : P ⟶ A) (q : P ⟶ B),
        IsPullback (F.map p) (F.map q) (F.map f) (F.map g) := by
    intro A B X f g
    exact ⟨pullback f g, pullback.fst f g, pullback.snd f g,
      (IsPullback.of_hasPullback f g).map F⟩
  obtain ⟨K, hK, e⟩ := sheafSubcategory_sievePresentation J F hrep hpb
  exact ⟨S, hS, K, hK, e⟩

end CategoryTheory
