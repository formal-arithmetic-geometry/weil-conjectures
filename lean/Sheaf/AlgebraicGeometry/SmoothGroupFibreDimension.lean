/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.LocallyConstant.Basic
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import WeilConjectures.AlgebraicGeometry.DensePoints

/-! # Geometric fibre dimensions of smooth group algebraic spaces

Source: Stacks Project, Morphisms, Tag 02G1, and Groupoids, Tag 047M,
identity-section and translation argument
(blueprint: lem-sfb-smooth-group-fibre-dimension).

The group law is encoded by a group-valued functor with its underlying presheaf
identified with the given space. All scheme base changes are covered by the same
function on the original base: a geometric fibre over `t : T` has dimension `d (h t)`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The geometric fibre is the actual presheaf fibre product with the given field spectrum.
The final topology on its `Point` is the atlas topology, since this fibre product is an
algebraic space by `fibreProduct_isAlgebraicSpace`.
Source: Stacks, Morphisms of Spaces, Tag 04NS(1)
(blueprint: lem-sfb-smooth-group-fibre-dimension). -/
def groupGeometricFibre {B : Scheme.{u}} {H : AlgebraicSpace B}
    (p : H.obj.obj ⟶ yoneda.obj (Over.mk (𝟙 B)))
    {Ω : Type u} [Field Ω] (a : Spec (.of Ω) ⟶ B) : (Over B)ᵒᵖ ⥤ Type u :=
  Limits.pullback p (yoneda.map (Over.homMk
    (U := Over.mk a) (V := Over.mk (𝟙 B)) a))

/-- A smooth separated finitely presented group algebraic space has nonempty pure
finite-dimensional geometric fibres, with locally constant dimension on the base.
The assertion for every `T : Over B` says simultaneously that the original fibres have
this dimension (take `T = B`) and that the dimension function after any scheme base
change is `d ∘ T.hom`. Every algebraic closure is allowed.
Source: Stacks, Morphisms, Tag 02G1; Groupoids, Tag 047M
(blueprint: lem-sfb-smooth-group-fibre-dimension).

Proof:
1. Apply `lem-sfb-smooth-space-dimension-strata` to `p`. Restrict its locally constant
   relative-dimension function along the identity section. Continuity of that section
   on points is `lem-a1-space-point-open-calculus`, so the result `d` is locally constant.
2. Over an algebraically closed field, translation by a rational point and translation
   by its inverse are inverse automorphisms, by associativity, unit and inverse laws.
   They preserve etale charts and their dimensions, and take the identity to that point.
   Thus every rational point has the identity's dimension.
3. If a different dimension stratum were nonempty, an etale scheme chart of that open
   stratum would be a nonempty smooth scheme over the algebraically closed field.
   `lem-pc-rational-points-dense` supplies a rational point there, contradicting step 2.
4. The identity gives nonemptiness. The unique dimension stratum is the whole fibre;
   the pure-fibre clause of `lem-sfb-smooth-space-dimension-strata` gives dimension `d`
   for every irreducible component.
5. Repeat steps 2--4 over any algebraically closed field mapping to `B`. For a base
   change `T → B` and an algebraic closure of the residue field at `t`, associativity
   of sheaf fibre products identifies the new geometric fibre with the original space
   pulled back along `Spec Ω → T → B`. Its dimension is therefore `d (T.hom t)`.
   This also shows independence of the chosen algebraic closure. No flatness of the
   base change, commutativity, connectedness, properness or Noetherian base is used. -/
theorem exists_locallyConstant_geometricFibreDimension
    {B : Scheme.{u}} (H : AlgebraicSpace B)
    (F : (Over B)ᵒᵖ ⥤ GrpCat.{u}) (e : F ⋙ forget GrpCat ≅ H.obj.obj)
    (p : H.obj.obj ⟶ yoneda.obj (Over.mk (𝟙 B)))
    (hsm : MapToSchemeIsLocally (@Smooth) H (Over.mk (𝟙 B)) p)
    (hsep : MapToSchemeIsSeparated H (Over.mk (𝟙 B)) p)
    (hlfp : MapToSchemeIsLocally (@LocallyOfFinitePresentation) H (Over.mk (𝟙 B)) p)
    (hqc : MapIsQuasiCompact p)
    (hqs : MapIsQuasiCompact (pullback.diagonal p)) :
    ∃ d : B → ℕ, IsLocallyConstant d ∧
      ∀ (T : Over B) (t : T.left) (Ω : Type u) [Field Ω]
        [Algebra (T.left.residueField t) Ω] [IsAlgClosure (T.left.residueField t) Ω],
        Nonempty (Point (groupGeometricFibre p
          (Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField t) Ω)) ≫
            T.left.fromSpecResidueField t ≫ T.hom))) ∧
        ∀ Z ∈ irreducibleComponents (Point (groupGeometricFibre p
          (Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField t) Ω)) ≫
            T.left.fromSpecResidueField t ≫ T.hom))),
          topologicalKrullDim Z = (d (T.hom t) : WithBot ℕ∞) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
