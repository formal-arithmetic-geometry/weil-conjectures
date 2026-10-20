/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Blowup.AdmissibleBlowup
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.Compactification.StrictTransform
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.FiniteStability
import Sheaf.AlgebraicGeometry.FinitePresentationKernelSurjectionFiniteType
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
import WeilConjectures.AlgebraicGeometry.Coherent
import WeilConjectures.Compactification.StrictTransformBlowup
import Sheaf.AlgebraicGeometry.CoherentFiniteType
import Sheaf.AlgebraicGeometry.FlatteningModuleByAdmissibleBlowup
import Sheaf.AlgebraicGeometry.ModuleStrictTransform
import Sheaf.AlgebraicGeometry.ModuleStrictTransformAffinePushforward
import Sheaf.AlgebraicGeometry.StrictTransformComposition

/-!
# Flattening by an admissible blowup

Source: Stacks Project, Tag 081R, `flat.tex`, Lemma `lemma-flat-after-blowing-up`;
Tag 080D, `divisors.tex`, Definition `definition-strict-transform`
(blueprint: lem-trf-flattening-by-admissible-blowup).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Raynaud--Gruson flattening for a finite type quasi-separated morphism over a qcqs base.
The strict transform uses the complement of the centre, which can be larger than `U`.
Source: Stacks Project, Tag 081R, Lemma `lemma-flat-after-blowing-up`, with strict transform
as in Tag 080D (blueprint: lem-trf-flattening-by-admissible-blowup).

Proof:
1. Quasi-compactness gives a finite affine cover of the source. Reduce to its affine pieces,
   using locality of flatness and local finite presentation.
2. Embed each affine piece into a finite-dimensional relative affine space, and choose a
   quasi-compact open neighbourhood in which the immersion is closed. Its structure sheaf
   pushed forward is quasi-coherent and finite type, since on affine charts it is cyclic.
3. Over `U`, finite presentation over the base and finite type of the ambient algebra imply
   finite presentation over that algebra. The finite-presentation surjection-kernel lemma
   supplies finitely many ideal generators, hence a finite module presentation. Flatness
   follows from the identical stalks on the closed image and zero stalks off that image.
4. Apply `lem-trf-flattening-module-by-admissible-blowup` to this pushed-forward module.
   The module strict transform becomes flat over the modified base and finitely presented.
5. Use `lem-trf-strict-transform-affine-pushforward` to identify this module transform with
   the pushforward of the structure sheaf of the scheme strict transform: the defining
   ideal consists of the sections supported on the exceptional inverse image.
6. The identical stalks on the closed image give flatness of the scheme strict transform.
   Finite presentation of the quotient module gives a finite type kernel by
   `lem-weil-pbc-finite-presentation-kernel-surjection-finite-type`. Thus the strict transform
   is locally cut out by finitely many equations in a locally finitely presented scheme,
   so its structural morphism is locally of finite presentation.
7. Take the product of the finitely many centre ideals. It is finite type and is the unit
   ideal over `U`. The product-ideal blowup comparison identifies its map to each individual
   blowup with a further admissible blowup. The support formula follows by separating the
   complement of the first centre, where its blowup is an isomorphism, from that centre.
8. Apply `lem-trf-strict-transform-composition`, using this factorization and support
   equality, to compare the single strict transform with the successive transforms.
9. A flat strict transform stays flat and locally finitely presented after further blowup:
   strict transform is the blowup of the extended centre, and flat base change of blowup
   identifies it with ordinary base change. No density assumption on `U` is needed.
10. The transforms of the affine pieces cover the global strict transform, so locality gives
    flatness and local finite presentation. Quasi-compactness and quasi-separatedness follow
    from base change of the original morphism and composition with the closed immersion of
    the strict transform. These are exactly the remaining finite-presentation conditions. -/
theorem exists_flat_finitePresentation_strictTransform_admissibleBlowup
    {T W : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    (U : T.Opens) (hU : IsCompact (U : Set T)) (g : W ⟶ T)
    [LocallyOfFiniteType g] [QuasiCompact g] [QuasiSeparated g]
    [Flat (g ∣_ U)] [LocallyOfFinitePresentation (g ∣_ U)] :
    ∃ B : IsAdmissible T U,
      Flat (strictTransformMap g B.I.blowupMap B.I.support.compl) ∧
      LocallyOfFinitePresentation (strictTransformMap g B.I.blowupMap B.I.support.compl) ∧
      QuasiCompact (strictTransformMap g B.I.blowupMap B.I.support.compl) ∧
      QuasiSeparated (strictTransformMap g B.I.blowupMap B.I.support.compl) := by
  sorry

end AlgebraicGeometry
