/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q98
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.RingTheory.HopkinsLevitzki
import WeilConjectures.AlgebraicGeometry.Thickening
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Sheaf.AlgebraicGeometry.AffineSmoothTrivializationLift

/-!
# Extending a deformation across a smooth affine open

Source: Stacks Project, Examples of Deformation Problems, Tags 0DZN and 0DYZ,
Situation `situation-glueing` and Example `example-schemes`
(blueprint: lem-sfb-smooth-open-deformation-lift).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A prescribed flat lift on one affine open extends across a smooth affine open
with smooth affine overlap, compatibly with the prescribed reduction isomorphism.
Empty opens are permitted.

Source: Stacks Project, Examples of Deformation Problems, Tag 0DZN,
`lemma-glueing-smooth`, second assertion with the first open smooth;
Tag 0DYZ, `lemma-glueing`
(blueprint: lem-sfb-smooth-open-deformation-lift).

`X`, `Y`, and `Z` are objects of the categories of schemes over their respective
bases. Thus `φ`, `e`, `α`, and `γ` are isomorphisms over the indicated bases.
The inverse-image equation `hYV` labels the open `YV` by `V` using the special
fibre marking `φ`. Reduction is a homeomorphism, so this characterizes exactly
the corresponding open without making any choice of a topological inverse.
Likewise the inverse-image equation in the conclusion characterizes `Y'V` by
reduction to `YV` through `α`; equivalently it is the open labelled by `V` under
the induced special-fibre marking. The final equation is the required equality
`e ∘ γ_A = α|Y_V`, written after the open inclusion into `Y`.

Proof:
1. Finite-dimensional algebras are Artinian by stabilization of dimensions of
   descending chains of ideals. Their maximal ideals are nilpotent by
   `lem-weil-pbc-artinian-local-noetherian-nilpotent`. Compatibility of the
   augmentations puts `ker q` in the maximal ideal of `A'`, so it too is
   nilpotent. By `def-sbc-first-order-thickening`, reduction is a homeomorphism
   on spaces. All labelled opens therefore exist uniquely. Restriction to
   opens preserves flatness by the local-ring criterion `def-weil-flat-morphism`.
2. Put `W = U ∩ V`. Apply `lem-sfb-affine-smooth-trivialization-lift` to `Y_U`
   over `A`, reducing by the augmentation ideal, and the specified marking.
   It yields `a : Y_U ≅ U_A` fixing the marking, and hence `a_W : Y_W ≅ W_A`.
3. Set `L = U_{A'}`. This is flat by smooth base change
   (`lem-pc-proper-base-change`, clause 2) and `lem-pc-smooth-flat`.
   The open `W_{A'}` in `L` and the open `E = Z_W` have reductions identified
   by `β₀ = a_W ∘ e|E_A`, using `lem-weil-pbc-open-immersion-base-change`.
4. Apply `lem-sfb-affine-smooth-trivialization-lift` to the smooth affine `W`
   and the flat deformation `E` over `A'`, modulo `ker q`. Obtain
   `b : E ≅ W_{A'}` reducing to `β₀`; use `b⁻¹` as the gluing identification.
5. By `lem-weil-pbc-glue-schemes`, glue `L` and `Z` along these opens. The
   inverse isomorphisms give all two-piece cocycle identities. Their structural
   maps agree and glue by `lem-weil-pbc-scheme-morphism-gluing`. The result
   `Y'` is flat because its local structural maps are those of `L` or `Z`.
6. Reduce this cover to `A` using `lem-weil-pbc-open-immersion-base-change`.
   The maps `a⁻¹` and `e` agree on the overlap since `b_A = a_W ∘ e|E_A`.
   Glue them by `lem-weil-pbc-scheme-morphism-gluing` to obtain `α` over `A`.
   The maps induced by `a` and `e⁻¹` glue in the other direction; uniqueness
   on the covers makes the composites identities and proves the base equations.
7. Reduction is a homeomorphism by `def-sbc-first-order-thickening`. The open
   copy of `Z` is exactly `Y'V` since `α` restricts there to `e`. Its inverse
   gives `γ`, and the same restriction equality gives the final equation.
   For empty `V` or `W` the formulas use empty schemes; for empty `U` use `Z`.
-/
theorem exists_smooth_open_deformation_lift
    (k A A' : Type u) [Field k] [CommRing A] [CommRing A']
    [Algebra k A] [Algebra k A'] [FiniteDimensional k A] [FiniteDimensional k A']
    [IsLocalRing A] [IsLocalRing A']
    (ε : A →ₐ[k] k) (ε' : A' →ₐ[k] k)
    (hε : RingHom.ker ε.toRingHom = IsLocalRing.maximalIdeal A)
    (hε' : RingHom.ker ε'.toRingHom = IsLocalRing.maximalIdeal A')
    (q : A' →ₐ[k] A) (hq : Function.Surjective q) (haug : ε.comp q = ε')
    (X : Over (Spec (CommRingCat.of k))) (U V : X.left.Opens)
    (hcover : U ⊔ V = ⊤) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : IsAffineOpen (U ⊓ V))
    (hsU : Smooth (U.ι ≫ X.hom)) (hsUV : Smooth ((U ⊓ V).ι ≫ X.hom))
    (Y : Over (Spec (CommRingCat.of A))) [Flat Y.hom]
    (φ : (Over.pullback (Spec.map (CommRingCat.ofHom ε.toRingHom))).obj Y ≅ X)
    (YV : Y.left.Opens)
    (hYV : pullback.fst Y.hom (Spec.map (CommRingCat.ofHom ε.toRingHom)) ⁻¹ᵁ YV =
      φ.hom.left ⁻¹ᵁ V)
    (Z : Over (Spec (CommRingCat.of A'))) [Flat Z.hom]
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom q.toRingHom))).obj Z ≅
      Over.mk (YV.ι ≫ Y.hom)) :
    ∃ Y' : Over (Spec (CommRingCat.of A')), Flat Y'.hom ∧
      ∃ α : (Over.pullback (Spec.map (CommRingCat.ofHom q.toRingHom))).obj Y' ≅ Y,
        ∃ Y'V : Y'.left.Opens,
          pullback.fst Y'.hom (Spec.map (CommRingCat.ofHom q.toRingHom)) ⁻¹ᵁ Y'V =
            α.hom.left ⁻¹ᵁ YV ∧
          ∃ γ : Over.mk (Y'V.ι ≫ Y'.hom) ≅ Z,
            ((Over.pullback (Spec.map (CommRingCat.ofHom q.toRingHom))).mapIso γ).hom ≫
                e.hom ≫ Over.homMk YV.ι =
              (Over.pullback (Spec.map (CommRingCat.ofHom q.toRingHom))).map
                  (Over.homMk Y'V.ι) ≫ α.hom := by
  sorry

end AlgebraicGeometry
