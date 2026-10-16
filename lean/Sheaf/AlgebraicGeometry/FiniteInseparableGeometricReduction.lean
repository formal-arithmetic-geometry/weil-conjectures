/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import Sheaf.AlgebraicGeometry.Morphisms.FiniteAffineTensorBaseChange
import Sheaf.Topology.PresheafModuleStalkFunctor
import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.FieldTheory.MakeSeparable
import WeilConjectures.FieldTheory.SeparableExtension
import WeilConjectures.FieldTheory.SeparablyGeneratedTensorReduced
import Sheaf.AlgebraicGeometry.GeometricReducednessFromGenericStalks
import Sheaf.RingTheory.PowerGeneratedSpectrumHomeomorphism

/-!
# Geometric reducedness after a finite purely inseparable extension

Source: Stacks Project, Varieties, Tag 04KT, lemma-finite-extension-geometrically-reduced
(blueprint: lem-pur-finite-inseparable-geometric-reduction).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A locally finite type scheme with finitely many irreducible components acquires a
geometrically reduced reduction after a finite purely inseparable extension of its base field.
Source: Stacks Project, Varieties, Tag 04KT, lemma-finite-extension-geometrically-reduced
(blueprint: lem-pur-finite-inseparable-geometric-reduction).

Proof:
1. Replace Z by its reduction. On affine charts, the nilradical generates a nilpotent-element
   ideal after field extension, so reducing before base change and reducing afterwards gives
   the same reduced scheme. Nilradicals commute with localization, hence these identifications
   glue. Use lem-sbc-finite-affine-tensor-base-change to describe the affine base changes.
2. List the finitely many generic points using lem-sc-scheme-sober. Their stalks are fields
   by lem-weil-pbc-minimal-prime-reduced-localization-field. Each is the fraction field of a
   minimal-prime quotient of a finite type affine chart, hence finitely generated over k.
3. A purely inseparable base change is a homeomorphism by
   lem-pur-power-generated-spectrum-homeomorphism. Its reduced generic stalks are the fields
   (K_i tensor_k l)_red: every tensor element has a characteristic power in K_i, and localization
   commutes with reduction and base change (lem-weil-pbc-localization-base-change).
4. Induct over the generic points, maintaining a finite purely inseparable tower and geometric
   reducedness of the generic fields already treated. Each remaining generic field is still
   finitely generated, since its extension of the original generic field is finite.
5. Apply lem-weil-pbc-make-separable to the next generic field. The tensor-product map to the
   separable extension has nilpotent kernel by the characteristic-power calculation. Thus its
   reduced quotient is a finitely generated subfield of that separable extension, hence
   separably generated. Apply lem-weil-pbc-separably-generated-tensor-reduced to every further
   field extension to obtain geometric reducedness of this new generic stalk.
6. Previously treated stalks remain geometrically reduced by tensor reassociation. Reduction
   commutes with successive base changes as in step 1; compose the finite purely inseparable
   extensions using lem-weil-pbc-finite-purely-inseparable-transitive.
7. Apply lem-pur-geometric-reducedness-from-generic-stalks to the final reduced base change.
   If Z is empty, the list is empty and the identity field extension suffices. -/
theorem exists_finite_purelyInseparable_geometricallyReduced_reduction
    (k : Type u) [Field k] (Z : Scheme.{u}) (f : Z ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [Finite (irreducibleComponents Z)] :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k'),
      Module.Finite k k' ∧ IsPurelyInseparable k k' ∧
        GeometricallyReduced
          ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k')))).nilradical.subschemeι ≫
            pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) := by
  sorry

end AlgebraicGeometry
