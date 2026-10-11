/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Topology.InverseImageModule
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct

/-!
# Pullback preserves K-flat complexes

Source: Stacks Project, Cohomology, Lemma 20.26.8, Tag 06YC
(blueprint: lem-pc-kflat-pullback-preservation).

The pulled-back complex has terms given by the topological module inverse image
followed by sheafified sectionwise change of rings along the adjoint structure map.
Its differentials are inverse images of the original differentials followed by
`changeOfRingsHom`. No comparison with an abstract module pullback is used.
-/

@[expose] public section

universe w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace CochainComplex

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : TopCat.{w}} (f : X ⟶ Y)
    (OX : Sheaf (Opens.grothendieckTopology X) CommRingCat.{w})
    (OY : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{w})
    (φ : OY ⟶ ((Opens.map f).sheafPushforwardContinuous CommRingCat.{w}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj OX)

/-- The ring map `f⁻¹ OY → OX` adjoint to the structure-sheaf map.
Source: Stacks, Tag 0095 (blueprint: lem-pc-kflat-pullback-preservation). -/
def tensorPullbackRingMap : TopCat.Sheaf.inverseImageRing f OY ⟶ OX :=
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map f) CommRingCat.{w} _ _).homEquiv OY OX).symm φ

variable (K : CochainComplex (SheafOfModules.{w}
    ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat.{w} RingCat.{w})).obj OY)) ℤ)

/-- The differential obtained by inverse image and the sectionwise tensor map.
Source: Stacks, Tags 0095 and 06YC (blueprint: lem-pc-kflat-pullback-preservation). -/
def tensorPullbackDifferential (i j : ℤ) :
    SheafOfModules.changeOfRings.{w, w, w} (tensorPullbackRingMap f OX OY φ)
      (TopCat.Sheaf.inverseImageModule f OY (K.X i)) ⟶
    SheafOfModules.changeOfRings.{w, w, w} (tensorPullbackRingMap f OX OY φ)
      (TopCat.Sheaf.inverseImageModule f OY (K.X j)) :=
  SheafOfModules.changeOfRingsHom.{w, w, w} (tensorPullbackRingMap f OX OY φ)
    (TopCat.Sheaf.inverseImageModule f OY (K.X i))
    (TopCat.Sheaf.inverseImageModuleMap f OY (K.X i) (K.d i j))

/-- The tensor pullback differential has cochain shape.
Source: Stacks, Tags 0095 and 06YC (blueprint: lem-pc-kflat-pullback-preservation).
Proof: outside the cochain shape the original differential is zero. The inverse-image
abelian-sheaf functor preserves zero maps, as do sectionwise extension of scalars and
module sheafification. Hence the displayed differential is zero. -/
theorem tensorPullbackDifferential_shape (i j : ℤ)
    (h : ¬ (ComplexShape.up ℤ).Rel i j) :
    tensorPullbackDifferential f OX OY φ K i j = 0 := by
  sorry

/-- Consecutive tensor pullback differentials compose to zero.
Source: Stacks, Tags 0095 and 06YC (blueprint: lem-pc-kflat-pullback-preservation).
Proof: the inverse-image abelian-sheaf functor preserves composition and zero maps;
the module maps have exactly those underlying abelian maps. Sectionwise extension of
scalars and sheafification preserve composition and zero maps as well. Apply these
facts to `K.d_comp_d i j k`. -/
theorem tensorPullbackDifferential_comp (i j k : ℤ) :
    tensorPullbackDifferential f OX OY φ K i j ≫
      tensorPullbackDifferential f OX OY φ K j k = 0 := by
  sorry

/-- The termwise formula `f⁻¹ K ⊗_{f⁻¹ OY} OX`, including its differentials.
Source: Stacks, Tags 0095 and 06YC (blueprint: lem-pc-kflat-pullback-preservation). -/
def tensorPullbackComplex : CochainComplex (SheafOfModules.{w}
    ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{w} RingCat.{w})).obj OX)) ℤ where
  X i := SheafOfModules.changeOfRings.{w, w, w} (tensorPullbackRingMap f OX OY φ)
    (TopCat.Sheaf.inverseImageModule f OY (K.X i))
  d := tensorPullbackDifferential f OX OY φ K
  shape := tensorPullbackDifferential_shape f OX OY φ K
  d_comp_d' i j k _ _ := tensorPullbackDifferential_comp f OX OY φ K i j k

/-- Pullback along a morphism of ringed spaces preserves K-flatness. Source: Stacks,
Tag 06YC (blueprint: lem-pc-kflat-pullback-preservation).

Proof:
1. At `x : X`, set `y = f x`, `A = OY_y`, and `B = OX_x`. The inverse-image stalk
   isomorphism (lem-weil-pbc-topological-inverse-image-stalk) and the change-of-rings
   tensor-stalk isomorphism (lem-weil-pbc-stalk-change-of-rings-tensor), natural in the
   differentials, identify the pullback stalk complex with `K_y ⊗_A B`.
2. The forward direction of lem-pc-kflat-stalk-criterion makes `K_y` K-flat over `A`.
3. For any acyclic `B`-complex `L`, restriction to `A` is acyclic, and associativity of
   tensor products and total-complex direct sums identifies
   `Tot(L ⊗_B (K_y ⊗_A B))` with `Tot(L ⊗_A K_y)`. The latter is acyclic by
   def-pc-kflat-complex and def-pc-tensor-complex-sheaves. Thus the pullback stalk is
   K-flat; this is Stacks Tag 06Y1 and requires no flatness of the ring map.
4. The reverse direction of lem-pc-kflat-stalk-criterion on `X` proves the conclusion.
-/
theorem isKFlat_pullback
    {X Y : TopCat.{w}} (f : X ⟶ Y)
    (OX : Sheaf (Opens.grothendieckTopology X) CommRingCat.{w})
    (OY : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{w})
    (φ : OY ⟶ ((Opens.map f).sheafPushforwardContinuous CommRingCat.{w}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj OX)
    (K : CochainComplex (SheafOfModules.{w}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat.{w} RingCat.{w})).obj OY)) ℤ)
    (hK : K.IsKFlat) :
    IsKFlat (R := OX) (tensorPullbackComplex f OX OY φ K) := by
  sorry

end
end CochainComplex
