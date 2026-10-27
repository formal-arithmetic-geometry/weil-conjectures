/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q123
-/
module

public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism

import Sheaf.AlgebraicGeometry.DMIsomSpaceUnramified
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import WeilConjectures.AlgebraicGeometry.UnramifiedQuasiFinite

/-! # Relative diagonals of Deligne--Mumford stack morphisms

Source: Stacks Project, stacks-morphisms.tex, Tag 050N, parts (2) and (6)
(blueprint: lem-sfb-dm-relative-diagonal-quasifinite).

The conclusion includes representability by algebraic spaces and tests every
representable etale scheme chart of every scheme base change. No condition is
imposed on the morphism beyond its source and target being DM stacks.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open AlgebraicGeometry

namespace CategoryTheory

/-- The relative diagonal of any morphism of DM stacks is representable by algebraic
spaces and locally quasi-finite on every etale scheme chart of each scheme base change.
The scheme predicate includes local finite type, as in Stacks 01TD.
Source: Stacks Project, Tag 050N, parts (2) and (6)
(blueprint: lem-sfb-dm-relative-diagonal-quasifinite).

Proof:
1. A scheme test of the relative diagonal specifies two objects `x,y` of the source
   over `T` and an isomorphism `alpha : f(x) ≅ f(y)`. By
   lem-sfb-dm-isom-space-unramified, their Isom spaces `I` and `J` in the source
   and target are algebraic spaces unramified over `T`. Applying `f` gives
   `phi : I → J`, compatible with restriction, and `alpha` gives a section of `J`.
2. Regard `T` as an algebraic space by def-trf-scheme-algebraic-space and form
   `P = I ×_J T` by lem-trf-space-fibre-products-etale-covers. Its points are the
   isomorphisms `beta : x ≅ y` whose image is `alpha`. A triple `(z,a,b)` in the
   tested 2-pullback maps to `b a⁻¹`; its inverse sends `beta` to `(x,1,beta)`.
   Compatibility with the first arrow gives the unique arrows between triples.
   This natural equivalence over `T` proves representability of the diagonal.
3. The composite `I → J → T` is unramified. Unramified cancellation and base change
   from lem-sfb-space-unramified-permanence make `P → T` unramified, without any
   finite-type, separation or representability hypothesis on `f`.
4. Every representable etale chart `A → P` therefore has unramified composite
   `A → T`. Apply lem-weil-pbc-unramified-quasi-finite-at-points to obtain local
   quasi-finiteness, including finite type at every point. Charts need not be
   surjective. This proves exactly the algebraic-space test in the conclusion. -/
theorem dm_relativeDiagonal_locallyQuasiFinite {S : Scheme.{u}}
    (F : BasedCategory.{v₁, w₁} (Over S)) (G : BasedCategory.{v₂, w₂} (Over S))
    (hF : IsDeligneMumfordModuliStack F) (hG : IsDeligneMumfordModuliStack G)
    (f : BasedFunctor F G) :
    ModuliSpaceTest @Scheme.Hom.IsLocallyQuasiFinite (moduliRelativeDiagonal f) := by
  sorry

end CategoryTheory
