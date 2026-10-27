/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O4
-/
module

public import Sheaf.AlgebraicGeometry.RigidifiedPicardRepresentation
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFppfCoveringCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers

/-! # The rigidified Picard space of an integral proper flat family

Source: Stacks Project, quot.tex, Tags 0D28, 0D2B, 0D2C; spaces-perfect.tex, Tag 0E0S;
moduli.tex, Tags 0DNI, 0DNJ (blueprint: lem-sfb-rigidified-space-picard).

The existing pointed-space, axis, and classification constructions apply to arbitrary
pointed families, without requiring a group law or algebraic triviality. Here the
classification includes ALL lines and ALL algebraic-space parameters. SmallModules
is the published equivalent small affine model of the same small etale module category.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.AlgebraicSpace

open Poincare

variable {S : Scheme.{u}}

/-- A proper flat finitely presented family with integral geometric fibres and a section
has its separated, locally finitely presented, rigidified Picard group space.
Source: Stacks 0D28, 0D2B, 0D2C, 0E0S, 0DNI, 0DNJ
(blueprint: lem-sfb-rigidified-space-picard).

Proof:
1. An integral geometric fibre is nonempty, reduced and connected. Apply
   lem-sfb-space-geometric-h0 to obtain UniversalStructureIso. Apply
   lem-sfb-space-picard-sheaf-representability to the fppf Picard sheaf. It is
   quasi-separated and locally finitely presented, by 0DNI.
2. In a local frame an automorphism of a line is multiplication by a unit. These
   functions glue; by step 1 the unit is pulled back uniquely from the base.
   Its section restriction is one when it preserves the rigidification, proving
   AllRigidifiedAutomorphisms. Normalize L by L tensor f-star (e-star L)-dual.
   This kills base pullbacks and recovers every already rigidified class.
3. Unique rigidified overlap isomorphisms satisfy the cocycle. Apply
   lem-sfb-space-fppf-covering-calculus, lem-sfb-space-fppf-qcoh-descent and
   lem-sfb-space-fppf-invertible-locality to descend lines and rigidifications.
   Lines are quasi-coherent by their local rank-one presentations. Normalization
   and forgetting are inverse between the Picard sheaf and rigidified classes.
   Tensor product gives the commutative group law, with the trivial line as zero.
4. For all valuation rings, two classes agreeing generically have a tensor
   difference trivial generically. Use lem-sfb-space-valuation-line-triviality
   and lem-sfb-space-flat-proper-fp-locality to trivialize it. Correct its
   section trivialization by a base unit. Then lem-sfb-space-valuative-separatedness
   and the quasi-compact diagonal prove separatedness (0DNJ).
5. Choose a scheme atlas of any parameter space. Scheme classification supplies
   lines on its charts and unique rigidified overlap isomorphisms. Descent as in
   step 3 gives classification and rigidity for all space parameters. At P the
   identity gives U. Zero gives its right-axis trivialization; normalization at
   the section gives its left axis, with the two agreeing at the intersection.
6. Under every scheme base change the parameter families and their rigidified
   lines agree. The actual pulled-back U therefore again classifies all lines.
   Uniqueness gives the unique normalized comparison with any other universal
   family, including identity and iterated comparisons. Taking an algebraically
   closed field as parameter gives the ordinary rigidified Picard functor of
   the geometric fibre, without a Noetherian restriction on a changed base. -/
theorem exists_rigidifiedSpacePicard [IsLocallyNoetherian S]
    (A : Pointed (groupSpaceBase S))
    (hp : MapIsProper A.p) (hf : MapIsFlat A.p)
    (hfp : MapIsLocallyOfFinitePresentation A.p ∧ MapIsQuasiCompact A.p.hom.hom ∧
      MapIsQuasiCompact (pullback.diagonal A.p.hom.hom))
    (hgeom : ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S),
      IrreducibleSpace (Point (product A.p (groupSchemeMap
        (Over.homMk (U := Over.mk s) (V := Over.mk (𝟙 S)) s (by simp)))).obj.obj) ∧
      ∀ V : (product A.p (groupSchemeMap
        (Over.homMk (U := Over.mk s) (V := Over.mk (𝟙 S)) s (by simp)))).EtaleSite,
        AlgebraicGeometry.IsReduced ((etaleForget _).obj V)) :
    UniversalStructureIso A ∧ AllRigidifiedAutomorphisms A ∧
      ∃ (P : AlgebraicSpace S) (G : CommutativeSpaceGroup P)
        (U : (product A.p (groupSpaceProjection P)).SmallModules)
        (rU : Axes A (pointedGroup P G) U),
        MapIsSeparated (groupSpaceProjection P) ∧
        MapIsLocallyOfFinitePresentation (groupSpaceProjection P) ∧
        RepresentsAllRigidifiedLines A (pointedGroup P G) U rU ∧
        PicardTensorLaw A P G U rU ∧
        AllRigidifiedPicardBaseChange A (pointedGroup P G) U rU := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
