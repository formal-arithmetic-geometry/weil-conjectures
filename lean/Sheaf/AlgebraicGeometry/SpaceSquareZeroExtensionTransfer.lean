/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q94
-/
module

public import Sheaf.AlgebraicGeometry.SpaceFixedIdealExtensions
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.SpaceNaiveCotangentComplex
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModulePullbackQuasiCoherent
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! # Transfer of square-zero extensions under derived quasi-coherent tests

Source: Stacks Project, Deformation Theory, Tag 0D3Q and its preceding setup
(blueprint: lem-sfb-space-square-zero-extension-transfer).

The equivalent small ringed model is the existing one; arbitrary module sheaves,
not just quasi-coherent ones, are allowed as kernels. The prescribed inverse-image
base-ideal map is expressed by its adjoint f^*J → F. The existential pushout
functor is characterized by all its extension maps and their universal property.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Kernel pushout is an equivalence for extensions with a fixed base-ideal map.
Source: Stacks Project, Deformation Theory, Tags 0D3P and 0D3Q
(blueprint: lem-sfb-space-square-zero-extension-transfer).

Proof:
1. Identify B_et and B'_et by lem-sfb-space-first-order-ringed-description;
   its ideal J is quasi-coherent. The naive cotangent complex N of X → B'
   has quasi-coherent cohomology by lem-sfb-space-naive-cotangent-quasicoherent.
   Apply the Hom test to N[-i]. Moving shifts to the target gives bijections
   Ext^i(N,F) → Ext^i(N,G), in particular for i = 0,1.
2. By lem-sfb-etale-algebra-extension-ext, unrestricted algebra extensions
   are classified by Ext^1(N,-), and their automorphisms by Ext^0(N,-),
   naturally for kernel pushout. Every map fixing kernel and quotient is an
   isomorphism, by exactness. Degree-one surjectivity lifts objects. Degree-one
   injectivity detects when two lifts are isomorphic. After choosing one such
   isomorphism, the degree-zero bijection lifts uniquely all its translates by
   automorphisms. Thus unrestricted pushout is fully faithful and essentially
   surjective, including pairs with empty Hom sets. Kernel pushout itself is
   the sheafification of (E ⊕ G)/{(inclusion(m),-u(m))}; multiplication is
   (e,g)(e',g')=(ee',p(e)g'+p(e')g). The square-zero and scalar identities make
   multiplication descend. This gives the stated universal property and its
   natural arrows, with the specified inclusion of G and quotient to O_X.
3. P = f^*J is quasi-coherent by lem-sfb-space-module-pullback-quasicoherent.
   The Hom test at P[0], and lem-weil-pbc-derived-single-fully-faithful, make
   Hom(P,F) → Hom(P,G) injective. Scalar-extension adjunction identifies these
   maps with the f^{-1}O_B-linear maps f^{-1}J → F and → G: send a ⊗ j to
   a d(j), and restrict to 1 ⊗ j for the inverse. These formulas commute with u.
4. The universal pushout arrow sends inclusion(m) to inclusion(u(m)). Hence
   its induced base-ideal map is u c_E. Extension isomorphisms preserve this
   map because they preserve the base algebra action. The fixed-map categories
   are full subcategories, so full faithfulness restricts to them.
5. For a target extension D with base-ideal map u c, lift D to an unrestricted
   E with pushout isomorphic to D. Then u c_E = u c; the injectivity in step 3
   gives c_E = c. Thus essential surjectivity also restricts. Together with full
   faithfulness it proves equivalence, even when the fixed-map categories are
   empty. No quasi-coherence of F or G is used. -/
theorem exists_kernelPushout_isEquivalence
    {S : Scheme.{u}} {X B B' : AlgebraicSpace S}
    (i : B ⟶ B') (hi : IsSpaceFirstOrderThickening i)
    (T : ThickeningSiteModel i) (J : SquareZeroIdeal T)
    (f : X ⟶ B) [CompactSpace (Point X.obj.obj)] (hqs : IsAbsolutelyQuasiSeparated X)
    [HasDerivedCategory.{w} X.SmallModules]
    {F G : X.Modules} (u : F ⟶ G)
    (h : ∀ K : X.DerivedQCoh,
      Function.Bijective (fun a : K.obj ⟶
        (DerivedCategory.singleFunctor X.SmallModules 0).obj
          (X.smallModuleRestriction.obj F) ↦
        a ≫ (DerivedCategory.singleFunctor X.SmallModules 0).map
          (X.smallModuleRestriction.map u)))
    (c : (moduleTensorPullback f).obj J.obj ⟶ F) :
    ∃ P : FixedIdealExtensions T J f c ⥤ FixedIdealExtensions T J f (c ≫ u),
      Nonempty (IsKernelPushout u P) ∧ P.IsEquivalence := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
