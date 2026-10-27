/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Topology.Sober
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.AlgebraicGeometry.TensorPullbackFinitePresentation
import WeilConjectures.RingTheory.DimensionAtPointLocalRingTrdeg
import Mathlib.RingTheory.KrullDimension.Zero
import Sheaf.TraceFormula.FlatFibreFreeNeighbourhood
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Top-dimensional flatness and the clopen generic-rank decomposition

Source: Stacks Project, More on Flatness, Tag 05UE, `lemma-compare-H-F`, with
`equation-free-at-generic-points` and `equation-flat-dimension-n`
(blueprint: lem-sfb-smooth-top-dimension-rank-decomposition).

The two predicates below are exactly the objectwise conditions defining H_r and F_a.
The theorem supplies their subterminal Zariski sheaves and states the coproduct by its
universal property in the sheaf category, including the unique clopen partition on every
(possibly disconnected or empty) test scheme.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- The condition defining H_r(T): after tensor pullback, the module is free of rank r
on an ambient open neighbourhood of each fibre generic point. The open may depend on
both the base point and the generic point; no freeness on the whole fibre is required.
Source: Stacks Project, More on Flatness, `equation-free-at-generic-points`, Tag 05UE
(blueprint: lem-sfb-smooth-top-dimension-rank-decomposition). -/
def smoothGenericFreeRankCondition {X S : Scheme.{u}} (g : X ⟶ S)
    (E : X.Modules) (r : ℕ) (T : Over S) : Prop :=
  ∀ (t : T.left) (ξ : (pullback.snd g T.hom).fiber t),
    IsGenericPoint ξ Set.univ →
      ∃ W : (Limits.pullback g T.hom).Opens,
        (pullback.snd g T.hom).fiberι t ξ ∈ W ∧
        Nonempty (((tensorPullback (pullback.fst g T.hom)).obj E).over W ≅
          SheafOfModules.free (ULift.{u} (Fin r)))

/-- The condition defining F_a(T): flatness of the actual pulled-back stalk over the
base local ring at every point whose relative residue-field transcendence degree is
at least a. The algebra structure is induced by the canonical residue-field map.
Source: Stacks Project, More on Flatness, `equation-flat-dimension-n`, Tag 05UE
(blueprint: lem-sfb-smooth-top-dimension-rank-decomposition). -/
def smoothTopDimensionFlatCondition {X S : Scheme.{u}} (g : X ⟶ S)
    (E : X.Modules) (a : ℕ) (T : Over S) : Prop :=
  ∀ x : (Limits.pullback (C := Scheme.{u}) g T.hom),
    (a : Cardinal.{u}) ≤
      @Algebra.trdeg (T.left.residueField (pullback.snd g T.hom x))
        ((Limits.pullback g T.hom).residueField x) _ _
        ((pullback.snd g T.hom).residueFieldMap x).hom.toAlgebra →
    @Module.Flat (T.left.presheaf.stalk (pullback.snd g T.hom x))
      ((RingedSpace.moduleStalkFunctor (Limits.pullback g T.hom).toRingedSpace x).obj
        ((tensorPullback (pullback.fst g T.hom)).obj E)) _ _
      (Module.compHom _ ((pullback.snd g T.hom).stalkMap x).hom)

/-- A rank-labelled clopen decomposition of T into ranks 0 through c. Each piece
carries the original tensor-pullback generic-free condition for its own rank.
Source: Stacks Project, More on Flatness, Tag 05UE, sheaf-coproduct interpretation
(blueprint: lem-sfb-smooth-top-dimension-rank-decomposition). -/
def smoothGenericRankPartition {X S : Scheme.{u}} (g : X ⟶ S)
    (E : X.Modules) (c : ℕ) (T : Over S) (U : Fin (c + 1) → T.left.Opens) : Prop :=
  (∀ r, IsClosed (U r : Set T.left)) ∧
  Pairwise (fun r q ↦ Disjoint (U r) (U q)) ∧
  (⨆ r, U r) = ⊤ ∧
  ∀ r, smoothGenericFreeRankCondition g E r.val (Over.mk ((U r).ι ≫ T.hom))

/-- Top-dimensional flatness is the finite sheaf coproduct of generic free-rank loci.
Subsingleton sections together with the displayed nonemptiness equivalences specify
exactly singleton-or-empty values and uniquely specify all restriction maps. An initial
H_r is empty on every nonempty test scheme and has one section on the empty scheme.
The colimit is in Zariski sheaves on S-schemes, rather than objectwise sets.

Source: Stacks Project, More on Flatness, Tag 05UE, `lemma-compare-H-F`
(blueprint: lem-sfb-smooth-top-dimension-rank-decomposition).

Proof:
1. Use `lem-weil-pbc-finite-presentation-affine-sections` to obtain a finite generator
   bound c. By `lem-weil-pbc-affine-tilde-gamma-adjunction`, its generating map sheafifies
   to O_X^c onto E. Tensor pullback preserves this surjection. Residue-field dimensions
   then bound any occurring free rank by c. For empty tests H_r has its unique section.
2. Relative dimension survives base change by `lem-sbc-smooth-relative-dimension-permanence`.
   Apply `lem-pc-smooth-flat`, `lem-weil-pbc-morphism-affine-schemes-affine`,
   `lem-weil-pbc-affine-morphism-permanence`, and `lem-weil-pbc-qcqs-morphism-permanence`
   to get a flat finitely presented base-changed family. Its fibres are integral by
   `def-pc-geometrically-irreducible`, `sbc-lem-smooth-geometrically-reduced`, and
   `def-pc-integral-scheme`. The pulled-back module is finitely presented by
   `lem-pc-tensor-pullback-finite-presentation`. Tests need not be affine or Noetherian.
3. On each integral affine fibre the dimension formula
   `lem-weil-pbc-dimension-at-point-local-ring-trdeg` says that local-ring dimension
   plus residue-field transcendence degree is a. The generic point has local ring a
   field by `lem-weil-pbc-minimal-prime-reduced-localization-field`. Every other point
   has positive local-ring dimension, so the tested points are exactly generic points.
4. For F_a(T), the generic stalk is flat over the base, and its fibre stalk is flat
   over the fibre local field. Apply `lem-trf-flat-fibre-free-neighbourhood` to obtain
   a neighbourhood free of rank r, with r at most c by step 1, including r = 0.
5. Its image is open by `lem-weil-pbc-flat-lfp-open`. On every fibre meeting this
   neighbourhood, the nonempty open contains the generic point. Thus H_r holds over
   that image; freeness on the entire inverse image of the image is unnecessary.
6. Conversely H_r implies base flatness at generic points, since finite free modules
   over the flat structure stalk are base-flat. This implication is local on the base.
7. Tensor two free generic stalks with the residue field to see their ranks agree.
   The unions of the open rank-r neighbourhoods therefore give disjoint open pieces
   covering T. Each complement is the union of the other pieces, hence each is closed.
   Rank uniqueness forces any other labelled partition to agree with this one.
8. The H_r conditions are stable under tensor base change, as in
   `lem-sfb-smooth-generic-rank-locus-representability`, and satisfy the Zariski sheaf
   condition by locality. Steps 5--7 give base-change stability for F_a, whose stalk
   condition is also local. These give the specified subterminal sheaves. For any
   sheaf G, maps H_r to G glue uniquely on the canonical clopen partition. The
   partition pulls back to the unique such partition after every base change, so
   gluing is natural and gives exactly the sheaf-coproduct universal property.
   The empty overlaps have one section by `def-pc-zariski-sheaf-property`. -/
theorem exists_smoothTopDimension_rank_decomposition
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    (g : X ⟶ S) (a : ℕ) [SmoothOfRelativeDimension a g]
    [GeometricallyIrreducible g] (E : X.Modules)
    [E.IsQuasicoherent] [E.IsFinitePresentation] :
    ∃ (c : ℕ)
      (H : ℕ → Sheaf (Scheme.zariskiTopology.over S) (Type (u + 1)))
      (F : Sheaf (Scheme.zariskiTopology.over S) (Type (u + 1))),
      (∀ (r : ℕ) (T : Over S), Subsingleton ((H r).obj.obj (op T)) ∧
        (Nonempty ((H r).obj.obj (op T)) ↔ smoothGenericFreeRankCondition g E r T)) ∧
      (∀ T : Over S, Subsingleton (F.obj.obj (op T)) ∧
        (Nonempty (F.obj.obj (op T)) ↔ smoothTopDimensionFlatCondition g E a T)) ∧
      (∀ r : ℕ, c < r → Nonempty (IsInitial (H r))) ∧
      (∃ ι : ∀ r : Fin (c + 1), H r.val ⟶ F,
        Nonempty (IsColimit (Cofan.mk F ι))) ∧
      ∀ T : Over S, smoothTopDimensionFlatCondition g E a T ↔
        ∃! U : Fin (c + 1) → T.left.Opens, smoothGenericRankPartition g E c T U := by
  sorry

end AlgebraicGeometry.Scheme.Modules
