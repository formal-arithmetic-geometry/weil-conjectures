/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q53
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.SixFunctors.ClassicalDefinition
public import Sheaf.AlgebraicGeometry.UnboundedDirectImageComparisonMap
public import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
public import Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.AlgebraicGeometry.ClassicalDerivedEquivalence
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules
import Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Bounded classical coproduct transport through etale origins

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-ctf-finite-proper-localizing.proof.md, Transfer; Stacks Tags 07D9 and 09A6
(blueprint: lem-sfb-finite-proper-classical-bounded-sums).

We use the ordinary fixed-ring module-sheaf presentation on both sites. On the
pro-etale site `finiteCoefficientRealization` identifies it with modules over the
recorded continuous-function coefficient sheaf. Classicality below is precisely the
recorded `IsClassicalModuleComplex` after this exact realization. No completion,
constructibility condition, or unbounded essential-image assertion is involved.

The last theorem quantifies over every bounded origin and its identifying isomorphism.
The comparison isomorphisms are pinned down by equality with the canonical derived
mate, and the transport isomorphism by its coprojections.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated

-- Reuse the existing construction of ambient derived coproducts.
attribute [local instance] CategoryTheory.derived_hasCoproducts

namespace AlgebraicGeometry.ProEtale

/-- Arbitrary ambient coproducts of classical complexes are classical.
Source: blueprint Transfer; Stacks Tag 07D9 and Bhatt--Scholze, Lemma 5.1.2
(blueprint: lem-sfb-finite-proper-classical-bounded-sums).

Proof: the module categories are Grothendieck by lem-weil-pbc-ring-sheaves-grothendieck.
Exact small sums are filtered colimits of finite partial sums. Termwise sums compute
ambient derived coproducts by lem-kun-grothendieck-derived-coproducts, including zero
for the empty family. Thus H^q of the sum is the sum of H^q. Each classical sheaf is
an exact comparison inverse image by det-pe-classical-sheaves-modules. That left
adjoint preserves sums, so the sum of these cohomology sheaves is again classical.
The exact coefficient realization gives the same assertion in the recorded encoding. -/
theorem finiteProperClassical_coproduct_closure
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] (T : Scheme.{u})
    (I : Type (u + 1))
    (L : I → DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
    (_hL : ∀ s : I, IsClassicalModuleComplex
      ((finiteCoefficientRealization T A).mapDerivedCategory.obj (L s))) :
    IsClassicalModuleComplex
      ((finiteCoefficientRealization T A).mapDerivedCategory.obj (∐ L)) := by
  sorry

/-- Both standard good truncations preserve classical cohomology.
Source: blueprint Transfer; Bhatt--Scholze, Definition 5.1.3; def-kun-truncations
(blueprint: lem-sfb-finite-proper-classical-bounded-sums).

Proof: good truncation retains each cohomology sheaf on its allowed side and gives
zero on the other side. Zero is the inverse image of zero under the exact comparison
functor. Hence both truncations are classical by sk-def-pe-classical-definition.
The exact realization commutes with cohomology and the standard t-structure. -/
theorem finiteProperClassical_truncation_closure
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] (T : Scheme.{u})
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
    (_hL : IsClassicalModuleComplex
      ((finiteCoefficientRealization T A).mapDerivedCategory.obj L)) (n : ℤ) :
    IsClassicalModuleComplex ((finiteCoefficientRealization T A).mapDerivedCategory.obj
      ((DerivedCategory.TStructure.t.truncLE n).obj L)) ∧
    IsClassicalModuleComplex ((finiteCoefficientRealization T A).mapDerivedCategory.obj
      ((DerivedCategory.TStructure.t.truncGE n).obj L)) := by
  sorry

/-- Cohomology and both good truncations commute naturally with ambient sums, with the
specified inclusion and quotient maps. Preservation gives the canonical natural sum
comparisons, rather than arbitrary object isomorphisms.
Source: blueprint Transfer, steps 1--2; Stacks Tag 07D9, clauses (1)--(2)
(blueprint: lem-sfb-finite-proper-classical-bounded-sums).

Proof: termwise coproducts represent ambient derived coproducts by
lem-kun-grothendieck-derived-coproducts. Exactness of sums identifies kernels, images,
and cokernels of the sum differential with sums of those objects. Their quotient is
the natural cohomology comparison. In the boundary degree good truncation uses just
these kernel or cokernel maps; elsewhere its comparison is the identity or the zero
map. These identifications commute with the truncation inclusion and quotient, and
are natural in the family. Localization retains the specified coprojections and maps.
The same computations apply to the empty family. -/
theorem finiteProperClassical_coproduct_cohomology_truncations
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] (T : Scheme.{u}) (I : Type (u + 1)) :
    (∀ q : ℤ, PreservesColimitsOfShape (Discrete I)
      (DerivedCategory.homologyFunctor
        (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) q)) ∧
    (∀ n : ℤ,
      PreservesColimitsOfShape (Discrete I)
        ((DerivedCategory.TStructure.t
          (C := Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))).truncLE n)) ∧
    (∀ n : ℤ,
      PreservesColimitsOfShape (Discrete I)
        ((DerivedCategory.TStructure.t
          (C := Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))).truncGE n)) ∧
    (∀ (L : I → DerivedCategory
        (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) (n : ℤ),
      sigmaComparison (DerivedCategory.TStructure.t.truncLE n) L ≫
          (DerivedCategory.TStructure.t.truncLEι n).app (∐ L) =
        Sigma.desc (fun s : I ↦
          (DerivedCategory.TStructure.t.truncLEι n).app (L s) ≫ Sigma.ι L s)) ∧
    (∀ (L : I → DerivedCategory
        (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) (n : ℤ),
      Sigma.desc (fun s : I ↦
          (DerivedCategory.TStructure.t.truncGEπ n).app (L s) ≫
            Sigma.ι (fun s : I ↦ (DerivedCategory.TStructure.t.truncGE n).obj (L s)) s) ≫
          sigmaComparison (DerivedCategory.TStructure.t.truncGE n) L =
        (DerivedCategory.TStructure.t.truncGEπ n).app (∐ L)) := by
  sorry

/-- Exact termwise comparison inverse image preserves all small ambient coproducts.
Source: blueprint Transfer, step 3; Bhatt--Scholze, Lemma 5.1.2; Stacks Tag 07D9
(blueprint: lem-sfb-finite-proper-classical-bounded-sums).

Proof: comparison inverse image is the exact left adjoint of
 det-pe-classical-sheaves-modules. Its adjunction identifies maps from the image of a
sum with families of maps from the images, including the empty sum. Apply this
preservation termwise to representative complexes, and use
lem-kun-grothendieck-derived-coproducts on both sites. This gives preservation of the
specified ambient coproduct, with its canonical comparison on coprojections. -/
theorem finiteProperClassical_comparison_preservesCoproducts
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] (T : Scheme.{u}) (I : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete I)
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory := by
  sorry

/-- A family in a common finite cohomological interval has etale origins in that same
interval. The family may be empty.
Source: blueprint Transfer, step 5; Bhatt--Scholze, Corollary 5.1.6
(blueprint: lem-sfb-finite-proper-classical-bounded-sums).

Proof: sk-prop-sf-comparison supplies the bounded-below derived unit. Apply
 det-pe-classical-derived-equivalence to every classical summand to obtain an etale
origin and its counit isomorphism. Exact inverse image commutes with cohomology by
lem-weil-pbc-exact-functor-bounded-below. Its full faithfulness on sheaves reflects
zero, so the origin has vanishing cohomology below a and above b. Choice assembles
these origins as a family; for the empty family there is nothing to choose. -/
theorem finiteProperClassical_bounded_origins
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] (X : Scheme.{u})
    (I : Type (u + 1)) (a b : ℤ) (_hab : a ≤ b)
    (L : I → DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (_hL : ∀ s : I, IsClassicalModuleComplex
      ((finiteCoefficientRealization X A).mapDerivedCategory.obj (L s)))
    (_hge : ∀ s : I, (L s).IsGE a) (_hle : ∀ s : I, (L s).IsLE b) :
    ∃ B : I → Etale.DerivedCategoryModule A X,
      (∀ s : I, (B s).IsGE a ∧ (B s).IsLE b) ∧
      Nonempty (∀ s : I,
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj (B s) ≅ L s) := by
  sorry

/-- For every bounded choice of etale origins, the actual pro-etale coproduct comparison
is the specified composite of the canonical derived mates, etale sum comparison, and
origin identifications. The displayed component equations uniquely determine `t` and
the mate isomorphisms, so the assertion applies to every such canonical choice.
Source: blueprint Transfer, steps 6--9; Stacks Tag 09A6
(blueprint: lem-sfb-finite-proper-classical-bounded-sums).

Proof:
1. Properness gives quasi-compactness and quasi-separatedness by
   def-weil-finite-type-morphism and lem-pc-separated-quasi-separated. Exact sums
   retain the common bounds [a,b], so B_s and their sum are bounded below.
2. Apply sk-thm-pe-direct-image-comparison to B_s and their sum. Its canonical
   natural transformation is the unbounded mate restricted to these inputs. The
   resulting isomorphisms are theta and Theta below; their hom equations fix them.
3. Inverse image preserves coproducts by step 3 of the node's proof. Transporting
   along the i_s gives the unique isomorphism t with the displayed coprojections.
   Its inverse is induced by F_X(iota_s) composed with i_s inverse. The Y-side
   canonical comparison is alpha_Y = sigmaComparison F_Y (E B_s).
4. The explicit etale preservation hypothesis makes sigmaComparison E B invertible.
   Thus every factor of the displayed composite is invertible.
5. Test the composite on its s-th coprojection. The definitions of sums of maps,
   alpha_Y and the etale comparison reduce it to
   G(i_s) inverse, theta_s inverse, F_Y(E iota_s), theta_sum, and G(t).
   Naturality of the canonical mate interchanges the middle three maps, leaving
   G(i_s inverse followed by F_X(iota_s) followed by t) = G(iota'_s).
6. The coproduct universal property identifies this composite with sigmaComparison
   G L, proving the factorization, invertibility, and the specified component law.
   For the empty family the sum of origins is zero and lies in every interval;
   the same argument uses the unique map out of the zero source. No unbounded
   classical essential-image equivalence is used. -/
theorem finiteProperClassical_bounded_sum_factorization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (_hE : ∀ J : Type (u + 1), PreservesColimitsOfShape (Discrete J)
      (Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor)
    (I : Type (u + 1)) (a b : ℤ) (_hab : a ≤ b)
    (L : I → DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (_hL : ∀ s : I, IsClassicalModuleComplex
      ((finiteCoefficientRealization X A).mapDerivedCategory.obj (L s)))
    (_hge : ∀ s : I, (L s).IsGE a) (_hle : ∀ s : I, (L s).IsLE b)
    (B : I → Etale.DerivedCategoryModule A X)
    (_hB : ∀ s : I, (B s).IsGE a ∧ (B s).IsLE b)
    (i : ∀ s : I,
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj (B s) ≅ L s) :
    ∃ (theta : ∀ s : I,
        (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
            ((Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj (B s)) ≅
          (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj
            ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj (B s)))
      (Theta :
        (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
            ((Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj (∐ B)) ≅
          (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj
            ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj (∐ B)))
      (t : (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj (∐ B) ≅
        ∐ L),
      (∀ s : I, (theta s).hom = unboundedDirectImageComparisonMap A f (B s)) ∧
      Theta.hom = unboundedDirectImageComparisonMap A f (∐ B) ∧
      (∀ s : I,
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map (Sigma.ι B s) ≫
            t.hom = (i s).hom ≫ Sigma.ι L s) ∧
      sigmaComparison (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor L =
        Sigma.desc (fun s : I ↦
          ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.mapIso (i s)).inv ≫
            (theta s).inv ≫
            Sigma.ι (fun s : I ↦
              (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
                ((Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj (B s))) s) ≫
          sigmaComparison (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory
            (fun s : I ↦
              (Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj (B s)) ≫
          (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
            (sigmaComparison (Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor B) ≫
          Theta.hom ≫ (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.map t.hom ∧
      IsIso (sigmaComparison (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor L) ∧
      (∀ s : I,
        Sigma.ι (fun s : I ↦
            (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj (L s)) s ≫
          sigmaComparison (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor L =
        (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.map (Sigma.ι L s)) := by
  sorry

end AlgebraicGeometry.ProEtale
