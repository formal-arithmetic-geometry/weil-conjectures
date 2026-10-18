/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.Algebra.Homology.BoundedFlatReplacement
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.CategoryTheory.TruncationTriangle
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Single
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.Algebra.Homology.FlatTruncationTower
import Sheaf.Algebra.Homology.FilteredColimitsTensor
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import Sheaf.Algebra.Homology.KFlat
import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.CategoryTheory.TruncationTriangle

/-!
# Cohomological bounds for derived extension of ring-sheaf scalars

Source: Stacks Project, sites-cohomology.tex, Tags 06YU and 077J; the bounds are the
agent consequence detailed in the DAG proof, not a verbatim assertion of either tag
(blueprint: lem-weil-pbc-ringed-tensor-cohomological-bounds).

`ringedDerivedScalarExtension` selects the existing universal derived-change-of-rings
functor. Its ordinary functor is fixed on both objects and maps by that dependency;
the derived universal property determines its value up to compatible isomorphism.
No new tensor product, module category, or cohomological-bound predicate is introduced.

`ringedTensorCohomologicalBounds` states both bounds. Higher Tor is written directly
as the negative-degree cohomology of scalar extension of a degree-zero module.
The module universe is independent of both site universes; essential smallness and
the sheafification instances express the size convention for the abelian module category.
-/

@[expose] public section

set_option autoImplicit false

universe w r u v

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- The universal derived scalar-extension functor from the recorded K-flat construction.
Source: Stacks Project, Tag 06YU, using the universal pair of Tag 06YY
(blueprint: lem-weil-pbc-ringed-tensor-cohomological-bounds).
The choice is from `derivedChangeOfRingsIndependentCoefficients`: the ordinary tensor
functor has its objects and maps specified, and the derived pair has the left-derived
universal property and its canonical counit is invertible on K-flat representatives.
Thus this selects a construction determined up to the isomorphism used by cohomology. -/
noncomputable def ringedDerivedScalarExtension
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify J AddCommGrpCat.{r}]
    {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J R))]
    [HasDerivedCategory.{w} (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J S))] :
    DerivedCategory (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J R)) ⥤
      DerivedCategory (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J S)) :=
  ((derivedChangeOfRingsIndependentCoefficients φ).choose_spec.choose_spec.choose_spec.choose_spec
    |>.2.2).choose

/-- Derived extension of scalars preserves an upper cohomological bound. It also preserves
any lower bound when the cohomology sheaves in the retained range have zero higher Tor.
Here `Tor_p(N,S)` is exactly `H^(-p)(F(Q(N[0])))`, and `IsLE` and `IsGE` are the standard
bounds, equivalent to cohomology vanishing above and below the stated integer.
Source: Stacks Project, sites-cohomology.tex, Tags 06YU and 077J, agent consequence
(blueprint: lem-weil-pbc-ringed-tensor-cohomological-bounds).

Proof:
1. For the upper bound, choose a good upper-truncated representative of M
(def-sbc-standard-tstructure-derived-category). Apply the same-bound flat replacement
(lem-pc-kflat-bounded-flat-replacement). The replacement is K-flat by
lem-pc-bounded-above-flat-kflat-site; its termwise scalar extension computes F(M) by
lem-pur-derived-change-of-rings. Terms and hence cohomology above a vanish.
2. For a sheaf N with vanishing positive Tor, the definition gives vanishing of F(N[0])
in negative degrees. Step 1 gives vanishing in positive degrees. Exactness and shift
compatibility of lem-pur-derived-change-of-rings show F(N[-q]) is concentrated in degree q,
with the shift convention of def-weil-abstract-derived-category.
3. For b < a, the good upper truncation of M at b is zero, since all its cohomology is
zero. Starting at b = a-1, induct using the successive-truncation triangle
(lem-weil-pbc-truncation-triangle). Its third term is H^b(M)[-b]. After applying F,
Step 2 concentrates this term in degree b >= a. The long exact cohomology sequence
(lem-sf-derived-homology-long-exact) and induction give the lower bound for every finite
upper truncation of M.
4. For a representative G, take compatible bounded-above flat resolutions E_n of its
good upper truncations, with maps into G (lem-pc-flat-truncation-tower). Their degreewise
colimit P maps to G. Exact filtered colimits (lem-pc-module-filtered-colimits-tensor)
preserve kernels, images and their quotients, so commute with cohomology. In any fixed
degree i the maps H^i(E_n) -> H^i(G) are compatible isomorphisms once n >= max(0,i).
Their colimit is an isomorphism. Thus P -> G is a quasi-isomorphism.
5. Each E_n is K-flat by lem-pc-bounded-above-flat-kflat-site. Tensor commutes with the
filtered colimit by lem-pc-module-filtered-colimits-tensor, and exactness of that colimit
preserves acyclicity. Therefore P is K-flat (def-pc-kflat-complex). If necessary, exchange
the tensor factors using the signed symmetry (-1)^(rs); the differential formula of
def-pc-tensor-complex-sheaves verifies this chain isomorphism and its inverse.
6. The K-flat computation (lem-pur-derived-change-of-rings) represents F(M) by P tensor S,
which is the degreewise colimit of E_n tensor S. Step 3 makes each of these acyclic below
a, so the exact-colimit cohomology calculation in Step 4 proves the same for F(M).
One may calculate after restricting scalars to R: the kernels and sheafified cokernels
are the same underlying abelian sheaves (def-weil-sheaf-of-modules-category), so vanishing
also holds as an S-module sheaf. This uses no upper bound for the second assertion and
no flatness, finite generation, boundedness beyond the stated bounds, or site points. -/
theorem ringedTensorCohomologicalBounds
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify J AddCommGrpCat.{r}]
    {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J R))]
    [HasDerivedCategory.{w} (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J S))]
    (a : ℤ) :
    (∀ M : DerivedCategory
      (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J R)),
      M.IsLE a → ((ringedDerivedScalarExtension φ).obj M).IsLE a) ∧
    (∀ M : DerivedCategory
      (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J R)),
      M.IsGE a →
      (∀ (q : ℤ), a ≤ q → ∀ (p : ℕ), 0 < p →
        IsZero ((DerivedCategory.homologyFunctor
          (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J S)) (-(p : ℤ))).obj
          ((ringedDerivedScalarExtension φ).obj
            (DerivedCategory.Q.obj
              ((CochainComplex.singleFunctor
                (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J R)) 0).obj
                ((DerivedCategory.homologyFunctor
                  (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J R)) q).obj
                    M)))))) →
      ((ringedDerivedScalarExtension φ).obj M).IsGE a) := by
  sorry

end SheafOfModules
