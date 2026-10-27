/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.ModuliChartNormalization
import Sheaf.AlgebraicGeometry.DMIsomSpaceUnramified
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import Sheaf.AlgebraicGeometry.EtaleSmoothAtlasFppfDescent
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite

/-! # Relative étale scheme atlases for Deligne--Mumford fibre products

Source: Stacks Project, algebraic.tex, Tags 04TF, 04T2, 045B and 045C;
stacks-morphisms.tex, Tags 06N3, 0CIM and 0CIN; spaces-morphisms.tex, Tag 05W3
(blueprint: lem-sfb-dm-etale-atlas-calculus).

## Main statements

- `dm_twoFiberProduct`: the 2-fibre product is DM, including its étale scheme atlas.
- `dm_etale_baseChange`, `dm_etale_comp`: étaleness and surjectivity permanence.
- `dm_relative_etale_chart`: the induced chart map is étale, without surjectivity.

Surjectivity is tested on the actual algebraic-space projections after scheme base change.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂ v₃ w₃

open AlgebraicGeometry

namespace CategoryTheory

/-- The 2-fibre product of DM stacks is DM and therefore has an étale scheme atlas.
Source: Stacks, algebraic.tex, Tags 04TF and 04T2, with étale atlases; Tag 06N3
(blueprint: lem-sfb-dm-etale-atlas-calculus).

Proof:
1. Descend the two objects of a triple separately, then glue its comparison arrow
   using the isomorphism-sheaf condition in the target. This gives stack descent.
   The Isom sheaf of two triples is the fibre product of the two source Isom spaces
   over the target Isom space, with maps u ↦ alpha' f(u) and v ↦ g(v) alpha.
   Use lem-sfb-dm-isom-space-unramified and lem-trf-space-fibre-products-etale-covers.
   The diagonal base change is this Isom sheaf: (c,i,j) maps to j i inverse,
   and k maps back to (a,id,k). Thus the diagonal is representable by spaces.
2. Choose scheme atlases U and V of the source stacks. Over U ×_S V the target
   Isom space R represents U ×_Z V, by the same triple description; its arrows
   fix both scheme maps and hence are unique. Use def-pc-fibre-product and
   lem-sfb-dm-isom-space-unramified; R need not be a scheme.
3. For a scheme T mapping to the product, R ×_P T is
   (U ×_X T) ×_T (V ×_Y T). Each factor is étale surjective over T, so the
   projection is étale surjective by lem-trf-space-chartwise-etale-permanence.
   Choose a scheme atlas W → R using def-trf-algebraic-space. Its composite to P
   remains étale surjective by the same permanence, giving the required atlas. -/
theorem dm_twoFiberProduct {S : Scheme.{u}}
    {X : BasedCategory.{v₁, w₁} (Over S)} {Y : BasedCategory.{v₂, w₂} (Over S)}
    {Z : BasedCategory.{v₃, w₃} (Over S)}
    (hX : IsDeligneMumfordModuliStack X) (hY : IsDeligneMumfordModuliStack Y)
    (hZ : IsDeligneMumfordModuliStack Z) (f : BasedFunctor X Z) (g : BasedFunctor Y Z) :
    IsDeligneMumfordModuliStack (moduliTwoFiberProduct f g) := by
  sorry

/-- Base change preserves representable étaleness and, when present, surjectivity.
Source: Stacks, algebraic.tex, Tag 045C; stacks-morphisms.tex, Tag 0CIN
(blueprint: lem-sfb-dm-etale-atlas-calculus).

Proof:
4. An étale scheme atlas is smooth by lem-weil-pbc-etale-smooth-zero-dimensional-fibres.
   Apply lem-sfb-etale-smooth-atlas-fppf-descent to regard each DM stack as an fppf
   algebraic stack, with unchanged diagonal and atlas. The result of steps 1--3
   applies to the fibre product too. Now lem-sfb-stack-chartwise-smooth-etale-calculus
   gives representable étale base change. Its surjectivity comparison identifies
   field-extension lifting with surjectivity on scheme charts. The latter is
   equivalent to SpaceMapIsSurjective for each actual space projection: an atlas
   point above a test point supplies the required chart point, and composing
   any chart through a surjective atlas preserves surjectivity. Apply its
   surjectivity base-change assertion and recover the displayed scheme-test condition. -/
theorem dm_etale_baseChange {S : Scheme.{u}}
    {X : BasedCategory.{v₁, w₁} (Over S)} {Y : BasedCategory.{v₂, w₂} (Over S)}
    {Z : BasedCategory.{v₃, w₃} (Over S)}
    (hX : IsDeligneMumfordModuliStack X) (hY : IsDeligneMumfordModuliStack Y)
    (hZ : IsDeligneMumfordModuliStack Z) (f : BasedFunctor X Z) (g : BasedFunctor Y Z)
    (hf : IsEtaleModuliMap f) :
    IsEtaleModuliMap (moduliTwoFiberFst g f) ∧
      ((∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) Z),
        ∃ (A : AlgebraicSpace S) (p : A.obj.obj ⟶ yoneda.obj T),
          HasSpaceBaseChange f T t A p ∧ SpaceMapIsSurjective A T p) →
        ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) Y),
          ∃ (A : AlgebraicSpace S) (p : A.obj.obj ⟶ yoneda.obj T),
            HasSpaceBaseChange (moduliTwoFiberFst g f) T t A p ∧
              SpaceMapIsSurjective A T p) := by
  sorry

/-- Composition preserves representable étaleness and, when present, surjectivity.
Source: Stacks, algebraic.tex, Tag 045B; stacks-morphisms.tex, Tag 0CIM
(blueprint: lem-sfb-dm-etale-atlas-calculus).

Proof:
4. As in the base-change clause, smoothness of the étale atlases and
   lem-sfb-etale-smooth-atlas-fppf-descent supply algebraic stacks with the same
   atlas and diagonal. Apply lem-sfb-stack-chartwise-smooth-etale-calculus to the
   two representable étale maps. It proves representability and étaleness of the
   composite by successive algebraic-space tests and space composition permanence.
   For surjectivity use its comparison with field-extension lifting, compose
   the two lifts (and their comparison isomorphisms), and translate back to the
   actual algebraic-space projections as in the base-change clause. -/
theorem dm_etale_comp {S : Scheme.{u}}
    {X : BasedCategory.{v₁, w₁} (Over S)} {Y : BasedCategory.{v₂, w₂} (Over S)}
    {Z : BasedCategory.{v₃, w₃} (Over S)}
    (hX : IsDeligneMumfordModuliStack X) (hY : IsDeligneMumfordModuliStack Y)
    (hZ : IsDeligneMumfordModuliStack Z) (f : BasedFunctor X Y) (g : BasedFunctor Y Z)
    (hf : IsEtaleModuliMap f) (hg : IsEtaleModuliMap g) :
    IsEtaleModuliMap (f.comp g) ∧
      ((∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) Y),
        ∃ (A : AlgebraicSpace S) (p : A.obj.obj ⟶ yoneda.obj T),
          HasSpaceBaseChange f T t A p ∧ SpaceMapIsSurjective A T p) →
        (∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) Z),
          ∃ (A : AlgebraicSpace S) (p : A.obj.obj ⟶ yoneda.obj T),
            HasSpaceBaseChange g T t A p ∧ SpaceMapIsSurjective A T p) →
        ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) Z),
          ∃ (A : AlgebraicSpace S) (p : A.obj.obj ⟶ yoneda.obj T),
            HasSpaceBaseChange (f.comp g) T t A p ∧ SpaceMapIsSurjective A T p) := by
  sorry

/-- The comparison from two compatible étale scheme charts is representable étale.
Neither chart is required to be surjective.
Source: Stacks, spaces-morphisms.tex, Tag 05W3 after scheme base change
(blueprint: lem-sfb-dm-etale-atlas-calculus).

Proof:
5. Put E = X ×_Y V and let h be the specified comparison. The scheme V is DM:
   def-trf-scheme-algebraic-space supplies its sheaf and representable diagonal,
   and its identity is an étale surjective atlas. Steps 1--3 show E is DM.
   By step 4, q : E → X is representable étale. For a scheme t : T → E put
   B = U ×_X T and D = E ×_X T. Both are spaces étale over T, so the induced
   map B → D is étale by lem-trf-space-chartwise-etale-permanence.
   The map t gives a section T → D. Pulling B → D back along this section gives
   U ×_E T: the extra comparison beta is forced to be q(gamma), where gamma
   is the comparison in E. Forgetting beta and recovering it this way are inverse
   on objects and arrows, and commute with restriction. Apply space fibre-product
   closure and étale base change. Every scheme test of h is therefore a space
   étale over T, without using surjectivity of either original chart. -/
theorem dm_relative_etale_chart {S : Scheme.{u}}
    {X : BasedCategory.{v₁, w₁} (Over S)} {Y : BasedCategory.{v₂, w₂} (Over S)}
    (hX : IsDeligneMumfordModuliStack X) (hY : IsDeligneMumfordModuliStack Y)
    (f : BasedFunctor X Y) (U V : Over S)
    (a : BasedFunctor (discreteModuli (yoneda.obj U)) X)
    (b : BasedFunctor (discreteModuli (yoneda.obj V)) Y) (p : U ⟶ V)
    (e : a.comp f ≅ (discreteModuliMap (yoneda.map p)).comp b)
    (ha : IsEtaleModuliMap a) (hb : IsEtaleModuliMap b) :
    IsEtaleModuliMap (moduliTwoFiberLift a (discreteModuliMap (yoneda.map p)) e) := by
  sorry

end CategoryTheory
