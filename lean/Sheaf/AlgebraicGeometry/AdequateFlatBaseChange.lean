/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q156
-/
module

public import Sheaf.AlgebraicGeometry.AdequateModuliSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.RelativeModuliInertia

import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Flat base change of adequate moduli spaces

Source: Alper, Adequate moduli spaces and geometrically reductive group schemes,
arXiv:1005.2398v3, Section 2 and Proposition 5.2.9(1), printed p.27
(blueprint: lem-sfb-adequate-flat-base-change).

The projection is the first projection from the actual 2-fibre product with the
base-change space first. Its adequacy tests all algebras on the new stack. The
diagonal of the stack over the base uses the landed structural functor
`moduliBaseStructure` (def-sfb-relative-moduli-inertia).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- Flat base change preserves adequate moduli spaces, with the quasi-compact and
separated diagonal conventions of the source. No finite-type hypothesis is imposed.
Source: Alper, Section 2 and Proposition 5.2.9(1), printed p.27
(blueprint: lem-sfb-adequate-flat-base-change).

Proof:
1. Regard the spaces as discrete algebraic stacks (def-sfb-algebraic-moduli-stack,
   def-trf-algebraic-space, lem-sfb-stack-chartwise-smooth-etale-calculus).
   Their 2-fibre products are algebraic by lem-sfb-algebraic-stack-fibre-products.
   Quasi-compactness and quasi-separatedness persist by
   lem-sfb-stack-etale-local-qcqs-homeomorphism. Choose affine etale charts U_i of Y
   and W_ij of T times_Y U_i, using lem-weil-pbc-affine-opens-basis,
   lem-weil-pbc-open-immersion-etale, lem-trf-space-fibre-products-etale-covers and
   lem-trf-space-chartwise-etale-permanence. Their composites cover T; reassociate
   the actual 2-fibre products, retaining the specified comparison isomorphisms.
2. By lem-sfb-adequate-moduli-etale-locality, X times_Y U_i is adequate over U_i.
   Its affine criterion gives the canonical structure-ring isomorphism and global
   power lifting. The latter is adequate affineness by
   lem-sfb-affine-target-adequacy-criterion.
3. Flatness of T over Y, etale implies flat, and composition make W_ij flat over U_i
   by lem-sfb-stack-chartwise-smooth-etale-calculus. The affine ring map is flat by
   lem-weil-pbc-flat-morphism-affine-criterion. No finite presentation is used.
4. Apply lem-sfb-adequately-affine-affine-target-base-change to obtain adequate
   affineness over W_ij. The affine-target criterion supplies power lifting for
   every surjection of quasi-coherent algebras on the new stack, without descent.
5. Apply lem-sfb-stack-flat-scalar-sections to the structure sheaf. Its restriction
   is the new structure sheaf by def-sfb-stack-quasi-coherent-algebra. The canonical
   comparison identifies its global ring with the scalar extension of the old one.
   The old structural isomorphism identifies this with the ring of W_ij; the
   normalization 1 tensor s maps to the pullback of s makes the resulting map the
   canonical structural map.
6. The affine criterion in lem-sfb-adequate-moduli-etale-locality gives adequacy on
   every W_ij, and etale locality gives adequacy over T. Only the structure sheaf
   used flat scalar extension; all power tests range over arbitrary new algebras. -/
theorem adequateModuliSpace_flat_baseChange {k : Type u} [Field k]
    (F : BasedCategory.{v, w} (Over (Spec (CommRingCat.of k))))
    (hF : IsAlgebraicModuliStack F)
    (Y T : AlgebraicSpace (Spec (CommRingCat.of k)))
    (hFdiag : ∀ (V : Over (Spec (CommRingCat.of k)))
        (t : BasedFunctor (discreteModuli (yoneda.obj V))
          (moduliTwoFiberProduct (moduliBaseStructure F) (moduliBaseStructure F))),
      ∃ (Z : AlgebraicSpace (Spec (CommRingCat.of k))) (p : Z.obj.obj ⟶ yoneda.obj V),
        HasSpaceBaseChange (moduliRelativeDiagonal (moduliBaseStructure F)) V t Z p ∧
          AlgebraicSpace.MapIsQuasiCompact p ∧ AlgebraicSpace.MapToSchemeIsSeparated Z V p)
    (hYdiag : AlgebraicSpace.MapIsQuasiCompact (prod.lift (𝟙 Y.obj.obj) (𝟙 Y.obj.obj)) ∧
      AlgebraicSpace.IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
        (pullback.diagonal (prod.lift (𝟙 Y.obj.obj) (𝟙 Y.obj.obj))))
    (hTdiag : AlgebraicSpace.MapIsQuasiCompact (prod.lift (𝟙 T.obj.obj) (𝟙 T.obj.obj)) ∧
      AlgebraicSpace.IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
        (pullback.diagonal (prod.lift (𝟙 T.obj.obj) (𝟙 T.obj.obj))))
    (φ : BasedFunctor F (discreteModuli Y.obj.obj))
    (hφ : IsAdequateModuliSpace F hF Y φ) (g : T ⟶ Y)
    (hg : AlgebraicSpace.MapIsFlat g) :
    ∃ hFT : IsAlgebraicModuliStack (moduliTwoFiberProduct (discreteModuliMap g.hom.hom) φ),
      IsAdequateModuliSpace (moduliTwoFiberProduct (discreteModuliMap g.hom.hom) φ) hFT T
        (moduliTwoFiberFst (discreteModuliMap g.hom.hom) φ) := by
  sorry

end CategoryTheory
