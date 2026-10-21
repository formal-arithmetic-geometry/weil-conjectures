/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows
import Sheaf.AlgebraicGeometry.VaryingRingOperations
import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
import Sheaf.Paper.SemilinearDerivedSections
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Pullback compatibility of the intrinsic semilinear alpha

Source: Stacks Project, Tag 0F7F, alpha-level open case, and the agent-written
extension to arbitrary strict semilinear systems
(blueprint: lem-sf-semilinear-alpha-pullback).

The ordinary system cube is stated first. Its exact localization is the derived
cube, prior to taking any proper direct-image mate. The auxiliary isomorphisms
only localize the dependency's specified ordinary comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.VaryingRing

variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)

/-- Exact localization of the specified unit-normalized open comparison.
Source: Stacks, Tags 09AE and 0F7F (blueprint: lem-sf-semilinear-alpha-pullback).
This is the actual ordinary moduleBeta localized, with the standard composition
isomorphisms; no derived comparison is selected independently. -/
def alphaPullbackBeta {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g)
    (hsq : IsPullback a j' j g) : J R φ j ⋙ G R φ g ≅ G R φ a ⋙ J R φ j' :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (moduleBeta R φ a j' j g h hsq) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- Exact localization of the specified inverse-image square compositor.
Source: Stacks, Tags 07A7 and 0F7F (blueprint: lem-sf-semilinear-alpha-pullback).
The square comparison is induced by moduleGComp, hence by the section-normalized
ordinary direct-image comparison, with its prescribed adjunction units. -/
def alphaPullbackSquareG {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    (h : k ≫ p = r ≫ i) : G R φ i ⋙ G R φ r ≅ G R φ p ⋙ G R φ k :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (moduleSquareG R φ k r p i h) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- The pullback cube already commutes on ordinary semilinear systems.
Source: Stacks, Tag 0F7F, alpha-level open case; agent-written semilinear extension
(blueprint: lem-sf-semilinear-alpha-pullback).
Proof (the node's seven steps):
1. Factor Q through T = V ×_Z W. The canonical lift s : U → T is clopen.
   Base change gives s₁ : U₁ → T₁, its clopen image, and its complementary open.
2. For an ordinary system M use the two cartesian open comparisons to write the
   common source as b₁! q₁* c* M. The open-adjunction Hom bijection reduces
   equality to equality after restriction along b₁.
3. Transpose the defining open unit for moduleBeta. The triangle identity says
   its restriction is identity under the open-unit identifications.
4. The clopen modulePi is the direct-image unit followed by the inverse of the
   open-to-direct-image comparison. Its restriction is the open unit. Therefore
   restriction of moduleAlpha along k is r* applied to the inverse unit for i.
5. Restrict both cube paths along k₁. By steps 3 and 4 both give r₁* c* applied
   to the inverse unit for i. The specified compositors agree: their right
   adjoints are the same identity-on-sections direct-image comparison.
6. On the complement of s₁ the common target is zero. On the image the two
   restrictions agree by step 5. Sheaf uniqueness on this disjoint open cover,
   coefficientwise and compatibly with the transitions, gives the ordinary
   system equality. The Hom bijection in step 2 removes the restriction.
7. Apply the ordinary transformations degreewise to unbounded complexes and
   localize at quasi-isomorphisms. Exactness preserves quasi-isomorphisms and
   the localization universal property preserves the equality and composition.
   This gives the derived equality before any proper direct-image mate is taken.
-/
theorem moduleAlpha_baseChange
    {U V W Z U₁ V₁ W₁ Z₁ : Scheme.{u}}
    (k : U ⟶ V) (i : W ⟶ Z) (r : U ⟶ W) (p : V ⟶ Z)
    (k₁ : U₁ ⟶ V₁) (i₁ : W₁ ⟶ Z₁) (r₁ : U₁ ⟶ W₁) (p₁ : V₁ ⟶ Z₁)
    (a : V₁ ⟶ V) (h : Z₁ ⟶ Z) (c : W₁ ⟶ W) (d : U₁ ⟶ U)
    [IsOpenImmersion k] [IsOpenImmersion i]
    [IsOpenImmersion k₁] [IsOpenImmersion i₁]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact k₁] [QuasiCompact i₁]
    [IsProper r] [IsProper p] [IsProper r₁] [IsProper p₁]
    (w : k ≫ p = r ≫ i) (w₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
    (wk : d ≫ k = k₁ ≫ a) (wi : c ≫ i = i₁ ≫ h)
    (wp : a ≫ p = p₁ ≫ h) (wr : d ≫ r = r₁ ≫ c)
    (sk : IsPullback d k₁ k a) (si : IsPullback c i₁ i h)
    (sp : IsPullback a p₁ p h) (sr : IsPullback d r₁ r c)
    (M : Modules R φ W) :
    (pull R φ p₁).map ((moduleBeta R φ c i₁ i h wi si).hom.app M) ≫
        (moduleAlpha R φ k₁ r₁ p₁ i₁ w₁).app ((pull R φ c).obj M) =
      (moduleSquareG R φ a p₁ p h wp).hom.app ((extension R φ i).obj M) ≫
        (pull R φ a).map ((moduleAlpha R φ k r p i w).app M) ≫
        (moduleBeta R φ d k₁ k a wk sk).hom.app ((pull R φ r).obj M) ≫
        (extension R φ k₁).map ((moduleSquareG R φ d r₁ r c wr).inv.app M) := by
  sorry

/-- The two displayed alpha cube paths agree after exact localization, on every
unbounded derived system, prior to taking any proper direct-image mate.
Source: Stacks, Tag 0F7F, alpha-level open case; agent-written semilinear extension
(blueprint: lem-sf-semilinear-alpha-pullback).
Proof (the node's seven steps):
1. Factor Q through T = V ×_Z W. The canonical lift s : U → T is clopen.
   Base change gives s₁ : U₁ → T₁, its clopen image, and its complementary open.
2. For an ordinary system M use the two cartesian open comparisons to write the
   common source as b₁! q₁* c* M. The open-adjunction Hom bijection reduces
   equality to equality after restriction along b₁.
3. Transpose the defining open unit for moduleBeta. The triangle identity says
   its restriction is identity under the open-unit identifications.
4. The clopen modulePi is the direct-image unit followed by the inverse of the
   open-to-direct-image comparison. Its restriction is the open unit. Therefore
   restriction of moduleAlpha along k is r* applied to the inverse unit for i.
5. Restrict both cube paths along k₁. By steps 3 and 4 both give r₁* c* applied
   to the inverse unit for i. The specified compositors agree: their right
   adjoints are the same identity-on-sections direct-image comparison.
6. On the complement of s₁ the common target is zero. On the image the two
   restrictions agree by step 5. Sheaf uniqueness on this disjoint open cover,
   coefficientwise and compatibly with the transitions, gives the ordinary
   system equality. The Hom bijection in step 2 removes the restriction.
7. Apply the ordinary transformations degreewise to unbounded complexes and
   localize at quasi-isomorphisms. Exactness preserves quasi-isomorphisms and
   the localization universal property preserves the equality and composition.
   This gives the derived equality before any proper direct-image mate is taken.
-/
theorem alpha_baseChange
    {U V W Z U₁ V₁ W₁ Z₁ : Scheme.{u}}
    (k : U ⟶ V) (i : W ⟶ Z) (r : U ⟶ W) (p : V ⟶ Z)
    (k₁ : U₁ ⟶ V₁) (i₁ : W₁ ⟶ Z₁) (r₁ : U₁ ⟶ W₁) (p₁ : V₁ ⟶ Z₁)
    (a : V₁ ⟶ V) (h : Z₁ ⟶ Z) (c : W₁ ⟶ W) (d : U₁ ⟶ U)
    [IsOpenImmersion k] [IsOpenImmersion i]
    [IsOpenImmersion k₁] [IsOpenImmersion i₁]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact k₁] [QuasiCompact i₁]
    [IsProper r] [IsProper p] [IsProper r₁] [IsProper p₁]
    (w : k ≫ p = r ≫ i) (w₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
    (wk : d ≫ k = k₁ ≫ a) (wi : c ≫ i = i₁ ≫ h)
    (wp : a ≫ p = p₁ ≫ h) (wr : d ≫ r = r₁ ≫ c)
    (sk : IsPullback d k₁ k a) (si : IsPullback c i₁ i h)
    (sp : IsPullback a p₁ p h) (sr : IsPullback d r₁ r c)
    (M : Derived R φ W) :
    (G R φ p₁).map ((alphaPullbackBeta R φ c i₁ i h wi si).hom.app M) ≫
        (alpha R φ k₁ r₁ p₁ i₁ w₁).app ((G R φ c).obj M) =
      (alphaPullbackSquareG R φ a p₁ p h wp).hom.app ((J R φ i).obj M) ≫
        (G R φ a).map ((alpha R φ k r p i w).app M) ≫
        (alphaPullbackBeta R φ d k₁ k a wk sk).hom.app ((G R φ r).obj M) ≫
        (J R φ k₁).map ((alphaPullbackSquareG R φ d r₁ r c wr).inv.app M) := by
  sorry

end AlgebraicGeometry.ProEtale.VaryingRing
