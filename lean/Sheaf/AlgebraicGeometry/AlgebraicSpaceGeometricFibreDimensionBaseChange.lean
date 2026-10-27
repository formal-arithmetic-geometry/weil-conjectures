/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import WeilConjectures.AlgebraicGeometry.DimensionAffineOpenCover
import WeilConjectures.AlgebraicGeometry.Dimension
import WeilConjectures.AlgebraicGeometry.DimensionPreservedFieldExtension
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.KrullDimension.Basic

/-!
# Geometric fibre dimension bounds after base change

Source: Stacks Project, Morphisms of Spaces, Tag 04NS(1),
`lemma-dimension-fibre-after-base-change` and `definition-relative-dimension`;
Decent Spaces, Tag 0A4J, `lemma-dimension-decent-space`
(blueprint: lem-sfb-space-fibre-dimension-base-change).

The structural map of `X : AlgebraicSpace B` is the morphism to the scheme `B`.
Products of presheaves on `Over B` are fibre products over this structural base.
They are the underlying presheaves of the corresponding sheaf fibre products.
The conclusion displays the geometric fibre as a pullback of the projection
`X ×_B B' → B'`, rather than replacing the space by a scheme chart.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A uniform bound on the dimensions of the chosen geometric fibres persists after
every scheme base change, for every choice of algebraic closure on the new base.
The family `K` specifies one algebraic closure of each residue field of `B`.
Quasi-separatedness is the scheme-test quasi-compactness of the representable diagonal.
Local finite type is tested on every representable étale scheme chart.
Dimension uses the existing atlas topology on point classes; empty fibres have dimension
`⊥`, and there is no equidimensionality hypothesis.

Source: Stacks Project, Morphisms of Spaces, Tag 04NS(1),
`lemma-dimension-fibre-after-base-change`; Decent Spaces, Tag 0A4J
(blueprint: lem-sfb-space-fibre-dimension-base-change).

Proof:
1. Fix `g : B' → B`, a point `b'`, and an algebraic closure `Ω` of its residue field.
   Let `b = g(b')`. The residue-field map embeds `κ(b)` into `Ω`. By
   `lem-weil-pbc-algebraic-extension-embeds-algebraically-closed`, extend it to an
   embedding `K b → Ω`. Associativity of sheaf fibre products identifies the new
   geometric fibre `G` with `F ×_(Spec (K b)) Spec Ω`, where `F` is the chosen old fibre
   (`def-weil-geometric-fibre`, `lem-trf-space-fibre-products-etale-covers`).
2. Choose a surjective étale scheme atlas `U → X`. Its pullbacks `V → F` and `W → G`
   remain surjective étale by `lem-trf-space-fibre-products-etale-covers`, and
   `W = V ×_(Spec (K b)) Spec Ω`. By
   `lem-sfb-space-etale-atlas-topological-dimension`, quasi-separatedness gives
   `dim V = dim F ≤ d` and `dim W = dim G`. That comparison works locally on the
   scheme test, without requiring the test scheme to be quasi-separated.
3. If `W` is empty, its dimension is `⊥` and the result follows. Otherwise `V` is
   nonempty. By `lem-weil-pbc-lft-base-change`, `V` is locally of finite type over
   `K b`. Cover it by affine opens `Spec Aᵢ` with `Aᵢ` finite type over `K b`.
   `lem-pc-dimension-affine-open-cover` and `lem-pc-scheme-dimension-local-rings`
   identify its dimension with the supremum of `dim Spec Aᵢ`; hence each is at most `d`.
4. By `lem-weil-pbc-open-fibre-product` the inverse images of these opens cover `W`.
   `lem-weil-pbc-fibre-product-affine-spectra` identifies them with
   `Spec (Aᵢ ⊗[K b] Ω)`. Tensor symmetry identifies this with
   `Spec (Ω ⊗[K b] Aᵢ)`, and `lem-weil-pbc-dimension-preserved-field-extension`
   makes its dimension equal to that of `Spec Aᵢ`, hence at most `d`.
5. The affine-cover and local-ring dimension formulas give `dim W ≤ d`.
   Step 2 gives `dim G ≤ d`. All base changes and closures were arbitrary.
   The empty case was separate, and no step assumes equidimensionality. -/
theorem geometricFibreDimension_le_baseChange {B : Scheme.{u}} (X : AlgebraicSpace B)
    (hqs : IsRepresentableWith (fun _ _ p ↦ QuasiCompact p.left)
      (Limits.prod.lift (𝟙 X.obj.obj) (𝟙 X.obj.obj)))
    (hft : ∀ (U : Over B) (a : yoneda.obj U ⟶ X.obj.obj),
      IsEtale a → LocallyOfFiniteType U.hom)
    (d : ℕ) (K : B → Type u) [∀ b : B, Field (K b)]
    [∀ b : B, Algebra (B.residueField b) (K b)]
    [∀ b : B, IsAlgClosure (B.residueField b) (K b)]
    (hbound : ∀ b : B,
      topologicalKrullDim (Point (Limits.prod X.obj.obj
        (yoneda.obj (Over.mk
          (Spec.map (CommRingCat.ofHom (algebraMap (B.residueField b) (K b))) ≫
            B.fromSpecResidueField b))))) ≤ (d : WithBot ℕ∞))
    (B' : Scheme.{u}) (g : B' ⟶ B) (b' : B')
    (Ω : Type u) [Field Ω] [Algebra (B'.residueField b') Ω]
    [IsAlgClosure (B'.residueField b') Ω] :
    topologicalKrullDim (Point (Limits.pullback
      (Limits.prod.snd : Limits.prod X.obj.obj (yoneda.obj (Over.mk g)) ⟶
        yoneda.obj (Over.mk g))
      (yoneda.map (Over.homMk
        (U := Over.mk ((Spec.map (CommRingCat.ofHom
          (algebraMap (B'.residueField b') Ω)) ≫ B'.fromSpecResidueField b') ≫ g))
        (V := Over.mk g)
        (Spec.map (CommRingCat.ofHom (algebraMap (B'.residueField b') Ω)) ≫
          B'.fromSpecResidueField b') rfl)))) ≤ (d : WithBot ℕ∞) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
