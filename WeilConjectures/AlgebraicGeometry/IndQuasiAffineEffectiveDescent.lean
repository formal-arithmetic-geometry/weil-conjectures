/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import WeilConjectures.AlgebraicGeometry.IndQuasiAffineFpqcDescent

/-! # Effective descent for ind-quasi-affine schemes

Source: Stacks Project, More on Groupoids, Tag 0APK, lemma-ind-quasi-affine;
More on Morphisms, Tag 0AP6, definition-ind-quasi-affine
(blueprint: lem-sfb-ind-quasi-affine-effective-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory

namespace CategoryTheory.Over.DescentDatum

/-- A descent datum on an ind-quasi-affine scheme along a flat, surjective,
quasi-compact morphism is effective. The morphism `t` need not be quasi-compact or
locally of finite presentation.

Source: Stacks Project, Tag 0APK, lemma-ind-quasi-affine; Tag 0AP6 defines the
ind-quasi-affine condition appearing in `hT`.
(blueprint: lem-sfb-ind-quasi-affine-effective-descent)

`D` is the recorded transport form of the overlap isomorphism and its cocycle.
`D.IsEffective` gives an X-scheme and a Cartesian square identifying T with its
pullback to V; invariance of transport is exactly compatibility with the canonical
descent datum, hence the displayed conjugation identity in the node.

Proof:
1. The flat, surjective, quasi-compact map p is a singleton fpqc covering.
2. For an affine open B in V, identify T times_V B with the inverse-image open
   t inverse B using pullbackRestrictIsoRestrict.
3. A quasi-compact open K in the pullback has quasi-compact open image under this
   isomorphism. The hypothesis makes that image quasi-affine, and hence K is
   quasi-affine. Since B is affine, the morphism K to B is quasi-compact and
   therefore quasi-affine.
4. Apply isEffective_of_indQuasiAffine_fpqc with this translated hypothesis.
   This is the same Stacks 0APK argument, already implemented in the library. -/
theorem isEffective_of_indQuasiAffine_flat_surjective_quasiCompact
    {V X T : Scheme.{u}} (p : V ⟶ X) [Flat p] [Surjective p] [QuasiCompact p]
    (t : T ⟶ V)
    (hT : ∀ (B : V.Opens), IsAffineOpen B →
      ∀ (U : (t ⁻¹ᵁ B).toScheme.Opens),
        IsCompact (U : Set (t ⁻¹ᵁ B).toScheme) → U.toScheme.IsQuasiAffine)
    (D : Over.DescentDatum p (Over.mk t)) : D.IsEffective := by
  apply isEffective_of_indQuasiAffine_fpqc p p.singleton_mem_fpqcPrecoverage ?_ D
  intro B hB K hK
  let e := pullbackRestrictIsoRestrict t B
  have : (e.hom ''ᵁ K).toScheme.IsQuasiAffine :=
    hT B hB (e.hom ''ᵁ K) (hK.image e.hom.continuous)
  have : K.toScheme.IsQuasiAffine :=
    Scheme.IsQuasiAffine.of_isIso (e.hom.isoImage K).hom
  have : IsAffine B.toScheme := hB
  infer_instance

end CategoryTheory.Over.DescentDatum
