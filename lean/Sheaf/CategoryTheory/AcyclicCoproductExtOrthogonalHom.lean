/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.CategoryTheory.DoubleComplexTotal
import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
import Sheaf.CategoryTheory.FirstQuadrantRowCollapse

/-!
# Acyclic Hom from bounded-above sums of Ext-orthogonal module sheaves

Source: Stacks Project, Cohomology on Sites, Tag 07AA,
`example-hom-complex-into-sheaf`, and Tag 07AC,
`lemma-existence-derived-lower-shriek`
(blueprint: lem-trf-acyclic-coproduct-ext-orthogonal-hom).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- A bounded-above acyclic complex whose terms are small coproducts of modules
Ext-orthogonal to `F` has acyclic Hom into `F`.

Source: Stacks Project, Cohomology on Sites, Tags 07AA and 07AC
(blueprint: lem-trf-acyclic-coproduct-ext-orthogonal-hom).

The positive Ext groups are computed using the specified injective resolution `P`.
The functor `preadditiveCoyoneda.obj (op (E i))` is Hom(E_i,-), with values in
abelian groups. The target of `HomComplex` is the complex with `F` in degree zero.
Its degree-n group identifies canonically with Hom(K^(-n),F) by
`CochainComplex.HomComplex.Cochain.toSingleEquiv`. Under this identification,
`CochainComplex.HomComplex.Cochain.δ_toSingleMk` gives the differential
h ↦ (-1)^(n+1) (d_K^(-n-1) ≫ h), exactly the differential in the node.

Proof:
1. Module sheaves form a Grothendieck abelian category by
   lem-weil-pbc-ring-sheaves-grothendieck, so have enough injectives by
   lem-sp-grothendieck-enough-injectives. Fix the exact nonnegative injective
   resolution supplied by lem-weil-pbc-left-exact-injective-resolution-degree-zero.
   The resolution-independence theorem lem-sp-derived-well-defined identifies
   its positive Hom cohomology with that computed using P in the hypothesis.
2. Hom out of each coproduct is the product of the Hom complexes from its summands.
   Exactness of products in Ab (lem-pc-abelian-groups-exact-products), applied to
   the cycles/boundaries and boundaries/cycles/homology short exact sequences,
   shows that positive Ext vanishes for each term of K. This allows empty sums
   and arbitrary repetitions of summands.
3. Choose an upper bound b and form the first-quadrant commuting double complex
   D^(p,q) = Hom(K^(b-p),J^q), with horizontal precomposition and vertical
   postcomposition. Its total differential is d_I + (-1)^p d_II, as in
   def-sp-double-complex-total; each total diagonal is finite.
4. The columns have no positive cohomology by step 2. Their degree-zero
   cohomology is Hom(K^(b-p),F), by exactness of the injective augmentation;
   these identifications commute with the horizontal differential.
5. Every row is exact: a cocycle factors through the image of d_K by acyclicity
   of K and extends to K^(b-p+1) by injectivity of J^q. At p=0 the upper bound
   makes that image zero, so the endpoint is exact as well.
6. The second spectral sequence of thm-sp-double-complex-spectral-sequences
   has zero first page by step 5. Its finite filtration implies Tot D is acyclic.
7. The first spectral sequence has only its degree-zero row left after step 4.
   The edge isomorphism of lem-weil-pbc-first-quadrant-row-collapse, including
   degree zero, identifies the cohomology of C^p = Hom(K^(b-p),F) with that of
   Tot D. Thus C is acyclic.
8. Relabel T^(p-b) = C^p and multiply degree p by signs a_p, where a_0=1 and
   a_(p+1)=(-1)^(p-b+1)a_p. This is an isomorphism to HomComplex K (F[0])
   with the stated differential. The lower degrees are zero, proving acyclicity. -/
theorem acyclic_hom_of_coproduct_ext_orthogonal
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    (F : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    {I : Type w}
    (E : I → ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (P : InjectiveResolution F)
    (hExt : ∀ (i : I) (p : ℕ), 0 < p →
      IsZero ((((preadditiveCoyoneda.obj (op (E i))).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj P.cocomplex).homology p))
    (K : CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (hbounded : ∃ b : ℤ, ∀ n : ℤ, b < n → IsZero (K.X n))
    (hacyclic : K.Acyclic)
    (hterms : ∀ n : ℤ, ∃ (A : Type u) (i : A → I),
      Nonempty (K.X n ≅ ∐ (fun a : A ↦ E (i a)))) :
    (CochainComplex.HomComplex K ((CochainComplex.singleFunctor _ 0).obj F)).Acyclic := by
  sorry

end CategoryTheory
