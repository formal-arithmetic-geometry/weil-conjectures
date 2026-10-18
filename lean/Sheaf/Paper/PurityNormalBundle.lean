/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.AlgebraicGeometry.ConormalGradedAlgebra
public import Sheaf.AlgebraicGeometry.RegularImmersionPureCodimension
public import Sheaf.Paper.PurityVectorBundleZeroSection
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Sheaf.RingTheory.RegularSequenceConormal
import Sheaf.AlgebraicGeometry.IsFiniteLocallyFreeOfCoherentFreeStalks
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Sheaf.AlgebraicGeometry.AffineMorphismRelativeSpec
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Topology.Sheaves.Functors
import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.Topology.Sheaves.Stalks
import Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraCore

/-!
# The normal cone, its augmentation section, and the regular normal bundle

Source: blueprint `sec-smooth-purity/sk-def-purity-conv`, order 1894;
Stacks Project, Divisors, Tags 0636, 0637, 063M; Algebra, Tag 00LN
(blueprint: def-pur-normal-bundle).

The cone is the relative spectrum of the conormal algebra for the given immersion.
The regular case uses the conormal module itself, with no globally chosen frame.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace AlgebraicGeometry.PurityNormalBundle

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The conormal algebra as an object of the quasi-coherent algebra category.
Source: Stacks Tags 0630, 0636 (blueprint: def-pur-normal-bundle). -/
def algebraObject : ObjectProperty.FullSubcategory
    (fun A : Z.CommAlgebraSheaf ↦ A.toModule.IsQuasicoherent) :=
  ⟨(ConormalGradedAlgebra.presentation i).algebra,
    (ConormalGradedAlgebra.presentation i).quasicoherent⟩

/-- The normal cone as an affine scheme over `Z`, defined by relative spectrum of
`G = direct sum I^n/I^(n+1)`, with the actual conormal algebra of this immersion.
Source: Stacks Tag 0636 (blueprint: def-pur-normal-bundle). -/
def over : ObjectProperty.FullSubcategory (fun Y : Over Z ↦ IsAffineHom Y.hom) :=
  ((VectorBundleZeroSection.antiEquivalence Z).inverse.obj (algebraObject i)).unop

/-- The normal cone `Spec_Z G` for the given closed immersion.
Source: Stacks Tag 0636 (blueprint: def-pur-normal-bundle). -/
def normalCone : Scheme.{u} := (over i).obj.left

/-- The affine projection from the normal cone to the closed subscheme.
Source: Stacks Tag 0636 (blueprint: def-pur-normal-bundle). -/
def projection : normalCone i ⟶ Z := (over i).obj.hom

/-- The degree-zero augmentation, transported along the structure map to the algebra of
the identity scheme over `Z`. Both arrows are specified algebra morphisms.
Source: Stacks Tags 0636, 01LX (blueprint: def-pur-normal-bundle). -/
def augmentationToBase : (algebraObject i).obj ⟶
    ((VectorBundleZeroSection.antiEquivalence Z).functor.obj
      (op (VectorBundleZeroSection.baseObject Z))).obj :=
  ConormalGradedAlgebra.augmentation i ≫
    Under.homMk (((VectorBundleZeroSection.antiEquivalence Z).functor.obj
      (op (VectorBundleZeroSection.baseObject Z))).obj.hom) (Category.id_comp _)

/-- The canonical section induced contravariantly by projection to degree zero.
Source: Stacks Tags 0636, 01LX (blueprint: def-pur-normal-bundle). -/
def zeroSection : Z ⟶ normalCone i :=
  ((VectorBundleZeroSection.antiEquivalence Z).functor.preimage
    (((VectorBundleZeroSection.antiEquivalence Z).counitIso.app (algebraObject i)).hom ≫
      ObjectProperty.homMk (augmentationToBase i))).unop.hom.left

/-- The augmentation gives a closed section even when the immersion is not regular.
Source: Stacks Tags 0636, 01LX, 01QO (blueprint: def-pur-normal-bundle).

Proof: the nonnegative grading makes projection to degree zero multiplicative. Its
composite with the structural inclusion is the identity. Under the relative-spectrum
anti-equivalence (`lem-weil-pbc-affine-morphism-relative-spec`), this is precisely the
section identity. On an affine open W of Z, the section is Spec of G(W) → O_Z(W), a
surjection since it fixes constants. The affine-cover closed-immersion criterion
(`lem-weil-pbc-closed-immersion-affine-cover-criterion`) proves closedness. This is Steps
1--2 of the node, using `lem-pur-conormal-graded-algebra` for the augmentation. -/
theorem zeroSection_spec :
    zeroSection i ≫ projection i = 𝟙 Z ∧ IsClosedImmersion (zeroSection i) := by
  sorry

/-- A regular immersion has a conormal module of rank `c`, and the canonical graded map
from its symmetric algebra to its conormal algebra is invertible.
Source: Stacks Tags 063M, 0637; Algebra Tag 00LN
(blueprint: def-pur-normal-bundle).

Proof: these are Steps 3--5 of the node. Finite type over the field makes X and Z
Noetherian (`lem-weil-pbc-finite-type-over-noetherian`). At each z the defining regular
sequence of length c gives the basis of J_z/J_z^2
(`lem-weil-pbc-regular-sequence-conormal-free`). The conormal-algebra stalk comparison
identifies these with conormal stalks. Coherence and the coherent free-stalk criterion
(`lem-sc-coherent-free-stalks-locally-free`) give local freeness; residue-field dimension
computes its rank as c. For every degree, the chosen regular generators identify Sym(C_z)
with the polynomial algebra on their basis
(`lem-weil-pbc-symmetric-algebra-free-module-polynomial` and its universal property).
The canonical map sends variables to their degree-one classes, so it is precisely the
isomorphism of `lem-pur-regular-sequence-graded-polynomial`. The module stalk criterion
(`lem-weil-pbc-module-iso-on-stalks`) makes it an isomorphism globally. Its module inverse
is an algebra map by applying the injective comparison to every algebra identity. -/
theorem regular_spec (P : WeilConjectures.PurityFiniteSetting.{u})
    (hX : X ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated hX] [LocallyOfFiniteType hX] [QuasiCompact hX]
    [IsSeparated (i ≫ hX)] [LocallyOfFiniteType (i ≫ hX)] [QuasiCompact (i ≫ hX)]
    (c : ℕ) (hreg : IsRegularImmersionOfPureCodimension hX i c) :
    (ConormalGradedAlgebra.piece i 1).IsFiniteLocallyFreeOfRank c ∧
      IsIso (ConormalGradedAlgebra.symmetricComparison i) := by
  sorry

/-- The regular normal cone equipped with its canonical vector-bundle identification.
The isomorphism is contravariantly induced by the canonical symmetric-algebra comparison.
Source: Stacks Tags 0637, 01M2 (blueprint: def-pur-normal-bundle). -/
def vectorBundle (P : WeilConjectures.PurityFiniteSetting.{u})
    (hX : X ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated hX] [LocallyOfFiniteType hX] [QuasiCompact hX]
    [IsSeparated (i ≫ hX)] [LocallyOfFiniteType (i ≫ hX)] [QuasiCompact (i ≫ hX)]
    (c : ℕ) (hreg : IsRegularImmersionOfPureCodimension hX i c) :
    PurityVectorBundle P Z (i ≫ hX) c := by
  letI : (ConormalGradedAlgebra.piece i 1).IsFiniteLocallyFreeOfRank c :=
    (regular_spec i P hX c hreg).1
  letI : IsIso (ConormalGradedAlgebra.symmetricComparison i) :=
    (regular_spec i P hX c hreg).2
  let e : VectorBundleZeroSection.algebraObject Z c (ConormalGradedAlgebra.piece i 1) ≅
      algebraObject i :=
    ObjectProperty.isoMk _ (asIso (ConormalGradedAlgebra.symmetricComparison i))
  let eOver := (ObjectProperty.ι (fun Y : Over Z ↦ IsAffineHom Y.hom)).mapIso
    (((VectorBundleZeroSection.antiEquivalence Z).inverse.mapIso e).unop)
  exact {
    E := normalCone i
    p := projection i
    𝓔 := ConormalGradedAlgebra.piece i 1
    phi := (Over.forget Z).mapIso eOver
    over_commutes := Over.w eOver.hom }

/-- The canonical symmetric-algebra identification carries the degree-zero augmentation
section of the normal cone to the vector-bundle zero section.
Source: Stacks Tags 0637, 01M2 (blueprint: def-pur-normal-bundle).

Proof: Step 6 of the node. The symmetric-algebra augmentation fixes constants and kills
every degree-one generator (`def-pur-vector-bundle-zero-section`). The conormal
augmentation after the comparison has the same values, by preservation of degrees.
Uniqueness in `lem-weil-pbc-quasi-coherent-symmetric-algebra-core` identifies the algebra
maps. The contravariant relative-spectrum anti-equivalence then identifies their sections.
This uses the same chosen anti-equivalence and the exact canonical comparison used in
`vectorBundle`, so it is an equality of the displayed arrows. -/
theorem vectorBundle_zeroSection (P : WeilConjectures.PurityFiniteSetting.{u})
    (hX : X ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated hX] [LocallyOfFiniteType hX] [QuasiCompact hX]
    [IsSeparated (i ≫ hX)] [LocallyOfFiniteType (i ≫ hX)] [QuasiCompact (i ≫ hX)]
    (c : ℕ) (hreg : IsRegularImmersionOfPureCodimension hX i c) :
    (vectorBundle i P hX c hreg).zeroSection = zeroSection i := by
  sorry

end AlgebraicGeometry.PurityNormalBundle
