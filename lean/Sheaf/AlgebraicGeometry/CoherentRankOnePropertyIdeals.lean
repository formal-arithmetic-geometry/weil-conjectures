/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q108
-/
module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.LinearAlgebra.Dimension.Finite
import WeilConjectures.AlgebraicGeometry.CoherentPushforwardIdeal
import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks
import WeilConjectures.AlgebraicGeometry.RankOneGenericIdealInclusion
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.AlgebraicGeometry.IntegralIdealsCommonGenericLattice

/-!
# Transfer from a generic rank-one witness to ideal pushforwards

Source: Stacks Project, coherent.tex, Tag 01YH, `lemma-property-irreducible`,
third and fourth proof paragraphs (blueprint: lem-pc-coherent-rank-one-property-ideals).
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace AlgebraicGeometry.Scheme.Modules

/-- A generic residue-field line with a two-out-of-three property gives that property
for every ideal pushforward from the integral closed subscheme, including the zero ideal.
Support is the set of points with nonsingleton stalk. The residue-field action in the
witness is required to induce its given stalk-ring action via the residue map.

Source: Stacks Project, coherent.tex, Tag 01YH, `lemma-property-irreducible`,
third and fourth proof paragraphs (blueprint: lem-pc-coherent-rank-one-property-ideals).

Proof:
1. For any ideal L, lem-pc-r2-coherent-pushforward-ideal gives coherence of i_*L.
   Its stalks vanish outside the image by lem-weil-pbc-closed-pushforward-stalks.
   For J = 0, pushforward is zero sectionwise; isomorphism invariance and P(0) finish.
2. Apply lem-pc-r2-rank-one-generic-ideal-inclusion to G to obtain a nonzero ideal I
   and a mono i_*I into G, invertible at the generic point. Its cokernel Q is coherent
   by lem-weil-pbc-coherent-kernel-cokernel-locnoeth. By lem-weil-pbc-module-stalk-exact,
   Q is supported in the image and has zero generic stalk. Thus P(Q) by hsmall,
   and two out of three with P(G) gives P(i_*I).
3. The generic stalk is nonzero, so i_*I is nonzero. For J nonzero apply
   lem-pc-r2-integral-ideals-common-generic-lattice to I and J, obtaining a coherent K
   with monomorphisms into both pushforwards, invertible at the generic point.
   Coherent cokernel closure and stalk exactness show that K and both cokernels are
   supported in the image, while both cokernels have zero generic stalk. Hence each
   cokernel has P by hsmall.
4. Two out of three in K → i_*I → Q_I gives P(K); in K → i_*J → Q_J it then gives
   P(i_*J). The coherence and support checks above justify both applications.
-/
theorem coherent_rank_one_property_ideals
    (X : Scheme.{u}) [IsNoetherian X]
    (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (P : X.Modules → Prop)
    (hiso : ∀ (F H : X.Modules),
      RingedSpace.IsCoherent X.toRingedSpace F →
      RingedSpace.IsCoherent X.toRingedSpace H →
      {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ⊆ Set.range i.base →
      {x : X | ¬ Subsingleton (H.presheaf.stalk x)} ⊆ Set.range i.base →
      ∀ (_ : F ≅ H), P F ↔ P H)
    (hzero : P (0 : X.Modules))
    (hshort : ∀ S : ShortComplex X.Modules, S.ShortExact →
      RingedSpace.IsCoherent X.toRingedSpace S.X₁ →
      RingedSpace.IsCoherent X.toRingedSpace S.X₂ →
      RingedSpace.IsCoherent X.toRingedSpace S.X₃ →
      {x : X | ¬ Subsingleton (S.X₁.presheaf.stalk x)} ⊆ Set.range i.base →
      {x : X | ¬ Subsingleton (S.X₂.presheaf.stalk x)} ⊆ Set.range i.base →
      {x : X | ¬ Subsingleton (S.X₃.presheaf.stalk x)} ⊆ Set.range i.base →
      ((P S.X₁ ∧ P S.X₂) → P S.X₃) ∧
      ((P S.X₁ ∧ P S.X₃) → P S.X₂) ∧
      ((P S.X₂ ∧ P S.X₃) → P S.X₁))
    (hsmall : ∀ Q : X.Modules, RingedSpace.IsCoherent X.toRingedSpace Q →
      {x : X | ¬ Subsingleton (Q.presheaf.stalk x)} ⊆ Set.range i.base →
      Subsingleton (Q.presheaf.stalk (i.base (genericPoint Z))) → P Q)
    (hG : ∃ G : X.Modules, RingedSpace.IsCoherent X.toRingedSpace G ∧
      {x : X | ¬ Subsingleton (G.presheaf.stalk x)} = Set.range i.base ∧
      P G ∧
      (∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i.base (genericPoint Z))),
        ∀ v : (RingedSpace.moduleStalkFunctor X.toRingedSpace
          (i.base (genericPoint Z))).obj G, a • v = 0) ∧
      (∃ inst : Module (X.residueField (i.base (genericPoint Z)))
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace (i.base (genericPoint Z))).obj G),
        (∀ (a : X.presheaf.stalk (i.base (genericPoint Z)))
          (v : (RingedSpace.moduleStalkFunctor X.toRingedSpace
            (i.base (genericPoint Z))).obj G),
          a • v = (X.residue (i.base (genericPoint Z))) a • v) ∧
        @Module.finrank (X.residueField (i.base (genericPoint Z)))
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace
            (i.base (genericPoint Z))).obj G) _ _ inst = 1)) :
    ∀ J : Z.IdealSheafData, P ((pushforward i).obj J.toModules) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
