/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeCompleteProjectionDescent.NativeProjectionDescentMaps
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionReductionSquare

/-! # Coherence of the native pullback reduction comparisons

Source: current Weil blueprint, sec-smooth-purity,
`sk-prop-sp-integral-adjunction-direct-image.proof.md`, paragraph (3)
(blueprint: lem-sp-complete-projection-reduction-square, proof step 1).

The descent data `DescentModels` fixes the pullback reduction comparisons `m.pull f`, the tensor
reduction comparisons `(m.tensor T).mu` and the system tensor pullbacks `(m.systemPull f).iso`
only through their values on flat K-flat representatives and on quotient unit sections. The
proof step "the tensor and pullback reduction models identify the whole-system comparisons with
the canonical scalar-extension comparisons" says that these comparisons are therefore the
canonical ones, and hence satisfy the two coherences of a monoidal pseudonatural transformation:

* `pull_tensor_coherence`: `m.pull g` is monoidal, for the oplax structure of `Lg^*`
  (`CondensedRing.monoidal_leftDerivedUpperStar`), the tensor comparisons `(m.tensor T).mu` and
  the system tensor pullback `(m.systemPull g).iso`;
* `pull_comp_coherence`: `m.pull` is compatible with composition, for
  `CondensedRing.leftDerivedUpperStarComp` and `VaryingRing.gComp`.

## Missing inputs

Both statements are left as `sorry`. Deriving them from the representative normalizations
in `DescentModels` needs inputs not available in the library:

1. every integral object is `DerivedCategory.Q.obj P` for a `FlatRepresentative` complex `P`
   (flat-term K-flat resolutions in the section presentation), and inverse images of
   `FlatRepresentative` complexes are `FlatRepresentative`;
2. a representative formula for the tensorator of `CondensedRing.monoidal_leftDerivedUpperStar`
   and for `CondensedRing.leftDerivedUpperStarComp` on such complexes, compatible with
   `pullComplexComparison`;
3. generation statements: morphisms out of `ordinaryReduction (f^* M)` and out of quotient
   reductions of signed total tensors are determined by their values on the quotient
   augmentation generators of unit sections, respectively of tensor generators (needed to
   compare the existential witnesses `ordinary` of `PullReductionModel`, the chain maps
   `TensorPresentation.chain` and `TensorComparisonModel.ordinary`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures WeilConjectures.SemilinearSections
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.NativeCompleteProjectionDescent

variable {l : ℕ} [Fact l.Prime] {E : Type u} [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The pullback reduction comparison is monoidal: under reduction, the tensorator of the
derived pullback `Lg^*` corresponds to the system tensor pullback.
Source: blueprint, sec-smooth-purity, paragraph (3)
(blueprint: lem-sp-complete-projection-reduction-square, proof step 1).

Missing input (see the module docstring): the representative identification of `m.pull g`,
`(m.tensor T).mu` and `(m.systemPull g).iso` with the canonical scalar-extension comparisons. -/
theorem pull_tensor_coherence (m : DescentModels l E) {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (A B : Integral l E Y) :
    (red l E m Z).map (Functor.OplaxMonoidal.δ (ringedPull l E g) A B) ≫
        (m.tensor Z).mu.hom.app ((ringedPull l E g).obj A, (ringedPull l E g).obj B) ≫
        (m.systems Z).closed.tensor.map
          (Prod.mkHom ((m.pull g).hom.app A) ((m.pull g).hom.app B)) =
      (m.pull g).hom.app (A ⊗ B) ≫
        (VaryingRing.G (rings l E) (transitions l E) g).map ((m.tensor Y).mu.hom.app (A, B)) ≫
        (m.systemPull g).iso.hom.app ((red l E m Y).obj A, (red l E m Y).obj B) := by
  sorry

/-- The pullback reduction comparison is compatible with composition of inverse images.
Source: blueprint, sec-smooth-purity, paragraph (3)
(blueprint: lem-sp-complete-projection-reduction-square, proof step 1).

Missing input (see the module docstring): the representative identification of `m.pull` with
the canonical scalar-extension comparisons. -/
theorem pull_comp_coherence (m : DescentModels l E) {X Z Y : Scheme.{u}} (i : X ⟶ Z)
    (g : Z ⟶ Y) (K : Integral l E Y) :
    (red l E m X).map
        ((CondensedRing.leftDerivedUpperStarComp (spIntegralCondensed l E) i g).inv.app K) ≫
        (m.pull (i ≫ g)).hom.app K =
      (m.pull i).hom.app ((ringedPull l E g).obj K) ≫
        (VaryingRing.G (rings l E) (transitions l E) i).map ((m.pull g).hom.app K) ≫
        (VaryingRing.gComp (rings l E) (transitions l E) i g).inv.app ((red l E m Y).obj K) := by
  sorry

/-- The reconstruction counit is the proper scalar exchange followed by the proper image of
the open scalar comparison: transpose the defining open/limit and proper/limit formulas and
use unit naturality and the triangle identity.
Source: blueprint, sec-smooth-purity, paragraph (3)
(blueprint: lem-sp-complete-projection-reduction-square, proof step 4). -/
theorem reconstruction_eq (m : DescentModels l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (AX : Limit l E X (m.abelian X) (m.red X))
    (AZ : Limit l E c.Z (m.abelian c.Z) (m.red c.Z))
    (AY : Limit l E Y (m.abelian Y) (m.red Y)) (N : Integral l E X) :
    reconstruction l E m c AX AZ AY N =
      (properScalar l E m c.g).app ((ringedOpen l E c.i).obj N) ≫
        (VaryingRing.P (rings l E) (transitions l E) c.g).map ((m.openScalar c.i).hom.app N) :=
  Adjunction.map_compactificationLimit_comp_counit (adj l E m X AX) (adj l E m c.Z AZ)
    (adj l E m Y AY) (m.openScalar c.i) (properScalar l E m c.g) N

/-- The pullback reduction comparison along `f` is the composite of those along the two halves
of a compactification, for any isomorphism equal to `leftDerivedUpperStarCompactificationIso`.
Source: blueprint, sec-smooth-purity, paragraph (3)
(blueprint: lem-sp-complete-projection-reduction-square, proof step 5). -/
theorem pull_compactification (m : DescentModels l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (K : Integral l E Y) (e : ringedPull l E f ≅ ringedPull l E c.g ⋙ ringedPull l E c.i)
    (he : e = CondensedRing.leftDerivedUpperStarCompactificationIso (spIntegralCondensed l E) c) :
    (red l E m X).map (e.inv.app K) ≫ (m.pull f).hom.app K =
      (m.pull c.i).hom.app ((ringedPull l E c.g).obj K) ≫
        (VaryingRing.G (rings l E) (transitions l E) c.i).map ((m.pull c.g).hom.app K) ≫
        (VaryingRing.gComp (rings l E) (transitions l E) c.i c.g).inv.app
          ((red l E m Y).obj K) ≫
        eqToHom (congrArg (fun g : X ⟶ Y ↦
          (VaryingRing.G (rings l E) (transitions l E) g).obj ((red l E m Y).obj K))
            c.comm.symm) :=
  Adjunction.map_inv_app_comp_hom_app_of_eq (L := ringedPull l E)
    (G := VaryingRing.G (rings l E) (transitions l E)) (r := red l E m X) (r' := red l E m Y)
    (m.pull (X := X) (Y := Y)) c.comm
    (CondensedRing.leftDerivedUpperStarComp (spIntegralCondensed l E) c.i c.g) e he K
    _ _ _ (pull_comp_coherence m c.i c.g K)

end AlgebraicGeometry.ProEtale.NativeCompleteProjectionDescent
