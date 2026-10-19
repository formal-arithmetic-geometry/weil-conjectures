/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.YonedaDerivedExtComparison
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import WeilConjectures.CategoryTheory.PushoutShortExactSequence
import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import WeilConjectures.CategoryTheory.PushoutShortExactSequence

/-! # Disk, sphere and degreewise split extension calculations

Source: the agent-formulated disk/sphere calculation below proof paragraph 2 of
`prop-coef-integral-exceptional-adjoint`, using Stacks Project, Homology, Section 010I
(blueprint: lem-coef-complex-ext-disk-sphere).

The groups below are the actual Yoneda quotients. Their Baer group structures and
endpoint maps are those of the recorded `YonedaDerivedExtComparison`. Such comparison
data exist for every abelian category; `HasExt.standard` supplies the unrestricted
size convention. Disks use the existing `CochainComplex.doubleId`, and spheres use
`CochainComplex.singleFunctor`, without new copies of these constructions.
-/

@[expose] public section

universe u v w w'

namespace CategoryTheory

open Limits Abelian CochainComplex CochainComplex.HomComplex

/-- Endpoint pullback and pushout on degree-one Yoneda classes, expressed through
 the canonical recorded comparison with derived Ext.

Source: Stacks Project, Derived Categories, Tag 06XU, endpoint naturality, as used
in the disk/sphere calculation (blueprint: lem-coef-complex-ext-disk-sphere). -/
noncomputable def YonedaDerivedExtComparison.mapOne
    {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]
    (c : YonedaDerivedExtComparison A) {U V U' V' : A}
    (a : U' ⟶ U) (b : V ⟶ V') (e : YonedaExtension.Classes V U 1) :
    YonedaExtension.Classes V' U' 1 :=
  (@AddEquiv.toEquiv _ _ (c.classGroup V' U' 0).toAdd inferInstance
    (c.comparison V' U' 0)).symm
    (((Ext.mk₀ a).comp (c.comparison V U 0 e) (zero_add 1)).comp
      (Ext.mk₀ b) (add_zero 1))

/-- Regard a short exact sequence as a degree-one Yoneda extension with the same
 endpoints and maps.

Source: Stacks Project, Homology, Definition 010J, used in the degreewise-split
calculation (blueprint: lem-coef-complex-ext-disk-sphere). -/
def shortExactYonedaExtension {A : Type u} [Category.{v} A] [Abelian A]
    (S : ShortComplex A) (hS : S.ShortExact) : YonedaExtension A S.X₁ S.X₃ 1 where
  sequence := S.toComposableArrows
  leftIso := Iso.refl _
  rightIso := Iso.refl _
  exact := hS.exact.exact_toComposableArrows
  first_mono := hS.mono_f
  last_epi := hS.epi_g

/-- The six natural Baer-group isomorphisms of the disk/sphere calculation,
including the normalization by the off-diagonal differential under splittings.
The comparison parameters only supply the previously constructed Baer group laws.

Source: the agent-formulated tool below proof paragraph 2 of
`prop-coef-integral-exceptional-adjoint`, using Stacks Project, Homology, Section 010I
(blueprint: lem-coef-complex-ext-disk-sphere). -/
structure ComplexExtDiskSphere (A : Type u) [Category.{v} A] [Abelian A]
    [HasExt.{w} A] [HasExt.{w'} (CochainComplex A ℤ)]
    (cA : YonedaDerivedExtComparison A)
    (cC : YonedaDerivedExtComparison (CochainComplex A ℤ)) where
  /-- The disk left group isomorphism. -/
  disk_left (M : A) (Y : CochainComplex A ℤ) (n : ℤ) :
    @AddEquiv (YonedaExtension.Classes (Y) (doubleId M n) 1)
      (YonedaExtension.Classes (Y.X n) (M) 1)
      (cC.classGroup (Y) (doubleId M n) 0).toAdd
      (cA.classGroup (Y.X n) (M) 0).toAdd
  /-- The disk right group isomorphism. -/
  disk_right (X : CochainComplex A ℤ) (M : A) (n : ℤ) :
    @AddEquiv (YonedaExtension.Classes (doubleId M n) (X) 1)
      (YonedaExtension.Classes (M) (X.X (n + 1)) 1)
      (cC.classGroup (doubleId M n) (X) 0).toAdd
      (cA.classGroup (M) (X.X (n + 1)) 0).toAdd
  /-- The sphere left group isomorphism. -/
  sphere_left (M : A) (Y : CochainComplex A ℤ) (n : ℤ) (hY : Y.Acyclic) :
    @AddEquiv (YonedaExtension.Classes (Y) ((singleFunctor A n).obj M) 1)
      (YonedaExtension.Classes (Y.cycles n) (M) 1)
      (cC.classGroup (Y) ((singleFunctor A n).obj M) 0).toAdd
      (cA.classGroup (Y.cycles n) (M) 0).toAdd
  /-- The sphere right group isomorphism. -/
  sphere_right (X : CochainComplex A ℤ) (M : A) (n : ℤ) (hX : X.Acyclic) :
    @AddEquiv (YonedaExtension.Classes ((singleFunctor A n).obj M) (X) 1)
      (YonedaExtension.Classes (M) (X.cycles (n + 1)) 1)
      (cC.classGroup ((singleFunctor A n).obj M) (X) 0).toAdd
      (cA.classGroup (M) (X.cycles (n + 1)) 0).toAdd
  /-- Degreewise vanishing classifies extensions by first Hom cohomology. -/
  hom_complex (X Y : CochainComplex A ℤ)
      (h : ∀ k : ℤ, Subsingleton (YonedaExtension.Classes (Y.X k) (X.X k) 1)) :
    @AddEquiv (YonedaExtension.Classes Y X 1) (CohomologyClass X Y 1)
      (cC.classGroup Y X 0).toAdd inferInstance
  /-- The classification sends an extension to its off-diagonal differential. -/
  hom_complex_split (S : ShortComplex (CochainComplex A ℤ)) (hS : S.ShortExact)
      (h : ∀ k : ℤ, Subsingleton (YonedaExtension.Classes (S.X₁.X k) (S.X₃.X k) 1))
      (σ : ∀ k : ℤ, (S.map (HomologicalComplex.eval A (.up ℤ) k)).Splitting) :
    hom_complex S.X₃ S.X₁ h (shortExactYonedaExtension S hS).classOf =
      CohomologyClass.mk (cocycleOfDegreewiseSplit S σ)
  /-- The injective formula requires no acyclicity of the source. -/
  injective (X : CochainComplex A ℤ) (I : A) [Injective I] (n : ℤ) :
    @AddEquiv (YonedaExtension.Classes ((singleFunctor A n).obj I) X 1)
      (X.homology (n - 1) ⟶ I)
      (cC.classGroup ((singleFunctor A n).obj I) X 0).toAdd inferInstance
  /-- Naturality in both disk-left endpoints. -/
  disk_left_naturality {M M' : A} {Y Y' : CochainComplex A ℤ}
      (a : M' ⟶ M) (b : Y ⟶ Y') (n : ℤ)
      (e : YonedaExtension.Classes Y (doubleId M n) 1) :
    cA.mapOne a (b.f n) (disk_left M Y n e) =
      disk_left M' Y' n (cC.mapOne (doubleIdMap a n) b e)
  /-- Naturality in both disk-right endpoints. -/
  disk_right_naturality {X X' : CochainComplex A ℤ} {M M' : A}
      (a : X' ⟶ X) (b : M ⟶ M') (n : ℤ)
      (e : YonedaExtension.Classes (doubleId M n) X 1) :
    cA.mapOne (a.f (n + 1)) b (disk_right X M n e) =
      disk_right X' M' n (cC.mapOne a (doubleIdMap b n) e)
  /-- Naturality on the full subcategory of acyclic second arguments. -/
  sphere_left_naturality {M M' : A} {Y Y' : CochainComplex A ℤ}
      (a : M' ⟶ M) (b : Y ⟶ Y') (n : ℤ) (hY : Y.Acyclic) (hY' : Y'.Acyclic)
      (e : YonedaExtension.Classes Y ((singleFunctor A n).obj M) 1) :
    cA.mapOne a (HomologicalComplex.cyclesMap b n) (sphere_left M Y n hY e) =
      sphere_left M' Y' n hY' (cC.mapOne ((singleFunctor A n).map a) b e)
  /-- Naturality on the full subcategory of acyclic first arguments. -/
  sphere_right_naturality {X X' : CochainComplex A ℤ} {M M' : A}
      (a : X' ⟶ X) (b : M ⟶ M') (n : ℤ) (hX : X.Acyclic) (hX' : X'.Acyclic)
      (e : YonedaExtension.Classes ((singleFunctor A n).obj M) X 1) :
    cA.mapOne (HomologicalComplex.cyclesMap a (n + 1)) b (sphere_right X M n hX e) =
      sphere_right X' M' n hX' (cC.mapOne a ((singleFunctor A n).map b) e)
  /-- Naturality of the Hom classification, specified on every cocycle. -/
  hom_complex_naturality {X X' Y Y' : CochainComplex A ℤ}
      (a : X' ⟶ X) (b : Y ⟶ Y')
      (h : ∀ k : ℤ, Subsingleton (YonedaExtension.Classes (Y.X k) (X.X k) 1))
      (h' : ∀ k : ℤ, Subsingleton (YonedaExtension.Classes (Y'.X k) (X'.X k) 1))
      (z : Cocycle X Y 1) :
    hom_complex X' Y' h'
      (cC.mapOne a b
        ((@AddEquiv.toEquiv _ _ (cC.classGroup Y X 0).toAdd inferInstance
          (hom_complex X Y h)).symm (CohomologyClass.mk z))) =
        CohomologyClass.mk ((z.precomp a).postcomp b)
  /-- Naturality of the injective formula, including arbitrary source complexes. -/
  injective_naturality {X X' : CochainComplex A ℤ} {I I' : A}
      [Injective I] [Injective I'] (a : X' ⟶ X) (b : I ⟶ I') (n : ℤ)
      (e : YonedaExtension.Classes ((singleFunctor A n).obj I) X 1) :
    injective X' I' n (cC.mapOne a ((singleFunctor A n).map b) e) =
      HomologicalComplex.homologyMap a (n - 1) ≫ injective X I n e ≫ b

/-- The disk, sphere, degreewise-split and injective extension calculations exist,
with Baer addition, naturality and the off-diagonal normalization specified above.

Source: the agent-formulated tool below proof paragraph 2 of
`prop-coef-integral-exceptional-adjoint`, using Stacks Project, Homology, Section 010I
(blueprint: lem-coef-complex-ext-disk-sphere).

Proof:
1. Work with actual short exact sequences in the abelian category of complexes.
They are degreewise short exact (lem-weil-pbc-cochain-complexes-degreewise-exact).
Pushout preserves short exactness (lem-weil-pbc-pushout-short-exact-sequence), and
pullback does so by passage to the opposite category. An endpoint-fixed map of
extensions is an isomorphism by the snake lemma (lem-weil-pbc-snake-lemma-abelian).
Endpoint pullback and pushout commute by their universal properties and this test.
2. Evaluate a disk extension in degree n. Conversely push a component extension
out along the differential Yⁿ → Yⁿ⁺¹ and keep Y in all other degrees. The induced
differentials square to zero, and the quotient differential is the identity.
3. The canonical pushout comparison is an endpoint-fixed extension map and hence
an isomorphism, so these operations are inverse on classes.
4. Opposite-category degree reversal sends Dⁿ to D⁻ⁿ⁻¹ and gives the second disk
formula, with Xⁿ⁺¹ as its component.
5. For acyclic Y, cycles of an extension of SⁿM give an extension of M by ZⁿY.
Surjectivity on cycles follows by lifting through the epic differential onto
Zⁿ⁺¹Y and subtracting that lift (lem-sp-abelian-refinements).
6. Push an extension of M by ZⁿY out along ZⁿY → Yⁿ and use zero differential on
the new extension term. The comparison test shows this inverts the cycles map.
7. Opposite-category degree reversal gives the other sphere formula. Exactness
identifies coker d_X^(n-1) with Z^(n+1)X
(lem-weil-pbc-abelian-exact-epi-cokernel).
8. The zero Yoneda class is the split extension: the Baer construction with a
split summand is canonically the original extension. Degreewise vanishing thus
provides degreewise splittings by ordinary choice.
9. In these splittings the differential matrix has off-diagonal block t with
δt = 0. Changing the section by h changes t by δh. Conversely the square-zero
matrix built from any cocycle defines an extension, and a coboundary gives an
endpoint-fixed isomorphism. This proves the Hom classification and its stated
normalization by cocycleOfDegreewiseSplit.
10. Evaluation and cycles commute with the direct sums and endpoint operations
in Baer addition; the cycle-pushout comparison is an endpoint-fixed isomorphism.
The matrix off-diagonal of a Baer sum is t+t', and endpoint maps replace t by
bt or ta. Thus all displayed maps are additive and natural. The recorded Yoneda
comparison identifies these operations with mapOne.
11. If I is injective, every component extension into SⁿI splits. The degree-one
Hom cocycles are maps X^(n-1) → I killing d_X^(n-2), modulo maps factoring through
d_X^(n-1). Restriction to cycles descends to H^(n-1)X. Injectivity extends maps
from H^(n-1)X to the corresponding cokernel for surjectivity, and extends maps
from im d_X^(n-1) to Xⁿ for injectivity. Restriction is additive and natural in
X and in injective I (def-sp-injective-resolutions), without acyclicity of X.
-/
theorem exists_complexExtDiskSphere (A : Type u) [Category.{v} A] [Abelian A] :
    ∃ (cA : @YonedaDerivedExtComparison A _ _ (HasExt.standard A))
      (cC : @YonedaDerivedExtComparison (CochainComplex A ℤ) _ _
        (HasExt.standard (CochainComplex A ℤ))),
      Nonempty (@ComplexExtDiskSphere A _ _ (HasExt.standard A)
        (HasExt.standard (CochainComplex A ℤ)) cA cC) := by
  sorry

end CategoryTheory
