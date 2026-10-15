/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.Sheaf
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.GlobalSections
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Étale objects and cohomology over a separably closed field

Source: blueprint `sec-smooth-purity`, `sk-prop-sf-kunneth-ordinary`,
lemma `lem-kun-0ezp`; Stacks Project, Tags 02GL, 03QO and the field case of 0EZP
(blueprint: lem-kun-0ezp).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Every étale object over a separably closed field is a disjoint union of copies of its
spectrum, and every abelian étale sheaf has vanishing positive cohomology and positive
higher direct images along any morphism from that spectrum.
Source: blueprint lemma `lem-kun-0ezp`, Stacks Project Tags 02GL, 03QO and the field case
of 0EZP (blueprint: lem-kun-0ezp).

Proof:
1. Apply `lem-weil-pbc-etale-fibre-discrete-separable-points` at the unique point of
   `Spec L`. The fibre is the original étale scheme. Its open singleton components have
   finite separable residue fields over L, hence are copies of L by
   `def-kun-separably-closed`. They give the coproduct decomposition over `Spec L`.
2. Apply the abelian sheaf axiom to this component covering. Sections on a coproduct are
   the product of sections on its components; on the empty scheme they form the zero group.
3. By `lem-weil-pbc-abelian-sheaf-epi-locally-surjective`, a section of an epimorphic
   quotient lifts on a covering. A nonempty covering of `Spec L` has a component section,
   so the section lifts globally. Lift separately on every component and glue, obtaining
   objectwise surjectivity on every étale object, including the empty one.
4. Global sections are evaluation at the terminal object
   (`def-weil-pbc-global-sections-functor`). Sectionwise kernels and finite products
   (`lem-weil-pbc-sheafification-exact`) together with step 3 show this functor is exact.
5. For any f, base change takes an étale object over the target to one over `Spec L`
   (`lem-weil-pbc-etale-base-change-finite-limits`). The direct-image section formula of
   `def-weil-pbc-direct-image` and step 3 preserve epimorphisms; sectionwise kernels and
   products show that direct image is exact as well. No condition on f is required.
6. Choose a K-injective resolution of F in degree zero. Its positive cohomology vanishes.
   Apply `lem-weil-pbc-exact-functor-complex-cohomology` to each of the exact functors in
   steps 4 and 5. Both preserve zero, so their resolved complexes have zero positive
   cohomology. By `def-weil-pbc-etale-cohomology` and `def-weil-pbc-direct-image`, these
   are precisely the two asserted vanishings. -/
theorem sepClosedField_etale_decomposition_and_vanishing
    (L : Type u) [Field L] [IsSepClosed L] :
    (∀ V : (Spec (.of L)).Etale,
      ∃ (I : Type u) (ι : I → (Spec (.of L) ⟶ V.left)),
        (∀ i : I, ι i ≫ V.hom = 𝟙 (Spec (.of L))) ∧
          Nonempty (IsColimit (Cofan.mk V.left ι))) ∧
    (∀ (F : Sheaf (Spec (.of L)).smallEtaleTopology AddCommGrpCat.{u + 1})
      (q : ℤ), 0 < q →
        IsZero ((cohomology AddCommGrpCat.{u + 1} (Spec (.of L)) q).obj
          ((DerivedCategory.singleFunctor _ 0).obj F))) ∧
    (∀ (Y : Scheme.{u}) (f : Spec (.of L) ⟶ Y)
      (F : Sheaf (Spec (.of L)).smallEtaleTopology AddCommGrpCat.{u + 1})
      (q : ℤ), 0 < q →
        IsZero ((DerivedCategory.Plus.homologyFunctor
          (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
          ((lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))) := sorry

end AlgebraicGeometry.Etale
