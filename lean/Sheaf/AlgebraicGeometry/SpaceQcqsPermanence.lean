/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.SpaceChangeBase
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFiniteAffineSubatlas
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Quasi-compact and quasi-separated permanence for algebraic spaces

Source: Stacks Project, Morphisms of Spaces, Tag 073B, parts (1)-(2)
(blueprint: lem-sfb-space-qcqs-permanence).

Absolute quasi-separatedness uses the existing affine-test criterion, equivalent to
quasi-compactness of the diagonal over Spec Z. Morphism quasi-compactness uses the
existing point-space affine tests; relative quasi-separatedness tests the diagonal.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism from a quasi-compact space to a quasi-separated space is quasi-compact;
if the source is also quasi-separated, its relative diagonal is quasi-compact.
Source: Stacks Project, Morphisms of Spaces, Tag 073B(1)-(2)
(blueprint: lem-sfb-space-qcqs-permanence).

Proof:
1. By lem-sfb-space-change-base-to-integers view the spaces over Spec Z. This keeps
   scheme atlases, sheaf fibre products and the atlas topology on point classes.
   By lem-sfb-qc-space-affine-etale-atlas choose an affine surjective etale atlas W of X.
   For any affine T over Spec Z, W times T over Spec Z is a surjective etale atlas
   of X times T, by lem-trf-space-fibre-products-etale-covers.
2. By lem-weil-pbc-fibre-product-affine-spectra, this atlas is the spectrum of the
   tensor product of the two affine rings over Z. It is quasi-compact by
   lem-weil-pbc-affine-scheme-qcqs. The atlas consequence of
   lem-a1-space-finite-affine-subatlas makes X times T quasi-compact. Hence the
   absolute structure map of X is quasi-compact.
3. The absolute structure map of Y is quasi-separated by hypothesis. Apply
   lem-sfb-space-qc-cancellation to f followed by that map. This proves that f is
   quasi-compact over Spec Z. The fibre-product and point-topology identifications
   of lem-sfb-space-change-base-to-integers return the affine-test conclusion over S.
4. If X is also absolutely quasi-separated, put P = X times_Y X and Q = X times_Z X.
   An affine test T to P has two maps u,v to X satisfying f u = f v. Sections of
   X times_P T are precisely pairs (x,t) with x = u(t) = v(t), which also describe
   X times_Q T. The latter is quasi-compact by the absolute diagonal hypothesis on X.
   Thus every affine test of the relative diagonal is quasi-compact, proving the
   second clause. Change of base again returns this conclusion over S. -/
theorem qcqs_permanence {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hX : CompactSpace (Point X.obj.obj)) (hY : IsAbsolutelyQuasiSeparated Y) :
    MapIsQuasiCompact f.hom.hom ∧
      (IsAbsolutelyQuasiSeparated X → MapIsQuasiCompact (pullback.diagonal f.hom.hom)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
