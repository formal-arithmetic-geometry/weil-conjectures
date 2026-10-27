/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q48
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineAtlasOpenCover
import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.RingTheory.Spectrum.Maximal.Basic
import Mathlib.RingTheory.Jacobson.Ring
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability

/-!
# Schemeness over an algebraic closure after a field extension

Source: Stacks Project, Spaces over Fields, Tag 0B84,
`lemma-when-scheme-after-base-change`, part (1)
(blueprint: lem-sfb-space-scheme-after-field-extension).

Restriction along `Over.map` expresses base change: on a scheme over the new field,
its structural map supplies the second projection of the fibre product. Thus its
sections are precisely sections of the original space on the same scheme over `k`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A space with quasi-compact relative diagonal that becomes a scheme over some field
extension becomes a scheme over any fixed algebraic closure. No quasi-compactness or
finite-type condition is imposed on the space itself.

Source: Stacks Project, Spaces over Fields, Tag 0B84, part (1)
(blueprint: lem-sfb-space-scheme-after-field-extension).

Proof:
1. The affine base is quasi-separated by [lem-weil-pbc-affine-scheme-qcqs]. The relative
   diagonal condition makes X absolutely quasi-separated by
   [lem-sfb-space-qcqs-source-products]. Choose a Zariski cover by opens V with affine
   surjective etale atlases using [lem-a1-space-affine-atlas-open-cover]. Each V is
   quasi-compact, and quasi-separated by [lem-sfb-space-integral-qcqs-permanence].
   Its base change V_K is an open subscheme of the scheme X_K, using
   [def-a1-space-open-subspace]. Work with one V at a time.
2. The finitely generated k-subalgebras A of K form a nonempty directed set, since k
   belongs to it and adjoining both finite lists gives an upper bound. Their union is
   K, since every element lies in k[a]. The spaces V_A are qcqs by
   [lem-sfb-qcqs-space-fibre-product] and [lem-weil-pbc-affine-scheme-qcqs]. The maps
   Spec B to Spec A are affine by [lem-weil-pbc-morphism-affine-schemes-affine], so
   their base changes V_B to V_A are affine by [lem-sfb-space-affine-locality].
3. Identify the sheaf limit with V_K on every test scheme T: a compatible section is
   a map T to V and compatible k-algebra maps A to the global functions of T, by
   [lem-weil-pbc-morphism-into-affine-scheme]. These maps glue uniquely to a map
   from K, since K is the union of the A. The bijections are natural in T and give
   the fibre product of [lem-trf-space-fibre-products-etale-covers].
4. Apply [lem-sfb-space-affine-limits-schematic-stages] to this small nonempty directed
   system with qcqs stages and affine transitions: V_A is a scheme for some A.
5. A is nontrivial as a subring of K. Choose a maximal ideal by
   [lem-weil-common-extension-fields-maximal-ideal]. Its residue field L is a finitely
   generated k-algebra, hence finite over k by [lem-weil-pbc-zariski-lemma]. Linear
   dependence of powers shows L/k is algebraic. Embed L into the fixed algebraic
   closure over k by [lem-weil-pbc-algebraic-extension-embeds-algebraically-closed].
   Compose A to L with this embedding. The scheme fibre product
   V_A times Spec Ω over Spec A, from [def-pc-fibre-product], represents V_Ω by its
   test-scheme universal property.
6. Repeat for every open V in step 1. The base-changed opens still cover, by
   [lem-trf-space-fibre-products-etale-covers], and their inclusions remain open
   immersions by [def-a1-space-open-subspace]. The fppf sheaf of
   [def-trf-algebraic-space] is a Zariski sheaf. Apply [lem-pc-schemes-criterion] to
   glue these schematic open subfunctors. An empty cover represents the empty scheme;
   no finite subcover of X or common A for the different opens is needed. -/
theorem scheme_over_algebraicClosure_of_exists_field_extension
    {k : Type u} [Field k] (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (X : AlgebraicSpace (Spec (.of k)))
    (hqs : IsRepresentableWith (fun _ _ p ↦ QuasiCompact p.left)
      (prod.lift (𝟙 X.obj.obj) (𝟙 X.obj.obj)))
    (hK : ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (Y : Over (Spec (.of K))),
      Nonempty
        (((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).op ⋙ X.obj.obj) ≅
          yoneda.obj Y)) :
    ∃ Y : Over (Spec (.of Ω)),
      Nonempty
        (((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).op ⋙ X.obj.obj) ≅
          yoneda.obj Y) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
