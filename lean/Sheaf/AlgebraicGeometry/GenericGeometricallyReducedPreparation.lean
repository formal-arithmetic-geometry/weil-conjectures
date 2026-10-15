/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Fiber

import Mathlib.RingTheory.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Sheaf.AlgebraicGeometry.GenericFlatFinitePresentation
import Sheaf.AlgebraicGeometry.FiniteInseparableGeometricReduction
import Sheaf.AlgebraicGeometry.GenericQuasiSeparatedness
import Sheaf.AlgebraicGeometry.ReductionGenericFibre
import Sheaf.RingTheory.PowerGeneratedSpectrumHomeomorphism

/-! # Preparing a geometrically reduced generic fibre

Source: Stacks Project, Tag 0550, lemma-make-generic-fibre-geometrically-reduced.
(blueprint: lem-pur-generic-geometrically-reduced-preparation)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite type family over an irreducible base admits, after shrinking and a finite
universal homeomorphism from an integral affine base, a reduced pullback that is flat,
finitely presented, and has geometrically reduced generic fibre.

Source: Stacks Project, Tag 0550, lemma-make-generic-fibre-geometrically-reduced.
(blueprint: lem-pur-generic-geometrically-reduced-preparation)

Proof:
1. Choose a nonempty affine open Spec A. Its nilradical is prime, and the generic fibre
is finite type over its residue field K. It is Noetherian by
lem-weil-pbc-finite-type-algebra-noetherian, with finitely many components by
lem-weil-pbc-noetherian-finite-components. Apply lem-pur-finite-inseparable-geometric-reduction
for a finite purely inseparable extension K'/K making its reduction geometrically reduced.
2. Scale finitely many field generators into elements whose p-power lies in A_red.
Their bounded monomials span a finite A-algebra A' inside K'. In characteristic zero use
A_red itself. This domain has fraction field K', so Spec A' is integral affine.
3. The kernel of A → A' is the nilradical. The power conditions on the generators give a
universal homeomorphism by lem-pur-power-generated-spectrum-homeomorphism; in characteristic
zero the quotient is surjective, so the same criterion applies with prime 2.
4. The reduction of the pullback is finite type, as seen on its finite affine cover.
By lem-pur-reduction-generic-fibre its generic fibre is the reduction of X over K', hence
geometrically reduced by step 1.
5. Apply lem-sbc-generic-flat-finite-presentation and lem-pur-generic-quasi-separatedness.
Intersect their nonempty opens in Spec A', and choose a principal open of Spec A whose
inverse image lies in that intersection, using the homeomorphism. Localize A' accordingly.
The resulting base remains integral affine and finite universally homeomorphic to this
nonempty open of the original base. Reduction commutes with localization, so flatness,
local finite presentation and quasi-separatedness restrict. The finite affine cover gives
quasi-compactness, hence finite presentation. The fraction field and generic fibre are
unchanged. The argument also allows an empty generic fibre or empty total pullback. -/
theorem exists_generic_geometricallyReduced_preparation {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] [IrreducibleSpace S] :
    ∃ U : S.Opens, (U : Set S).Nonempty ∧
      ∃ T : Scheme.{u}, IsIntegral T ∧ IsAffine T ∧
        ∃ q : T ⟶ U.toScheme, IsFinite q ∧
          (topologically IsHomeomorph).universally q ∧
          Flat ((pullback f (q ≫ U.ι)).nilradical.subschemeι ≫
            pullback.snd f (q ≫ U.ι)) ∧
          LocallyOfFinitePresentation ((pullback f (q ≫ U.ι)).nilradical.subschemeι ≫
            pullback.snd f (q ≫ U.ι)) ∧
          QuasiCompact ((pullback f (q ≫ U.ι)).nilradical.subschemeι ≫
            pullback.snd f (q ≫ U.ι)) ∧
          QuasiSeparated ((pullback f (q ≫ U.ι)).nilradical.subschemeι ≫
            pullback.snd f (q ≫ U.ι)) ∧
          ∀ η : T, IsGenericPoint η Set.univ →
            GeometricallyReduced
              (((pullback f (q ≫ U.ι)).nilradical.subschemeι ≫
                pullback.snd f (q ≫ U.ι)).fiberToSpecResidueField η) := by
  sorry

end AlgebraicGeometry
