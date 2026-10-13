/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.HomComplexProjections
public import Sheaf.Paper.DerivedHomMayerVietoris
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomOver
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom

/-!
# Differential compatibility for the product comparison under open restriction

Source: Stacks Project, Cohomology, Tag 08DL, and Cohomology on Sites, Tag 0A8X.
(blueprint: lem-sc-hom-complex-restrict-open-differential).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace CategoryTheory

/-- A degreewise comparison satisfying the factorwise product projection equations
intertwines the Hom-complex differential. This statement supplies no degreewise
isomorphisms: those must already have been constructed.

Source: Stacks Project, Cohomology, Tag 08DL, construction of internal Hom;
Cohomology on Sites, Tag 0A8X, the displayed Hom-complex differential.

Proof: Fix adjacent degrees n and m and postcompose both sides with each chosen
product projection in degree m on the localized site. These projections are jointly
monic by the limit assertion in `homComplex_projections_exists`. Expand the localized
differential using the second assertion of that theorem. Distribute composition over
subtraction and multiplication by the integer unit n.negOnePow, and apply the assumed
projection equation to both summands, with indices (p,p+n) and (p+m-n,p+m).
On the other side use the projection equation in degree m, functoriality of
restriction, and the global differential formula. Restriction is additive, so it
preserves subtraction and this integer-unit multiplication. The two summands now
agree by naturality of `SheafOfModules.overHomObjIso` in both arguments: on an object
W over U, its forward map precomposes a local module morphism by
`Over.iteratedSliceForward W`. Precomposition preserves identity and composition,
so restricting the pre- and post-compositions gives precisely the pre- and
post-compositions of the restricted maps. Thus both summands, with the same sign,
agree after every product projection, proving the asserted equality. The argument
uses all integer-indexed factors, and applies unchanged to zero complexes, the
empty open, and unbounded complexes.
(blueprint: lem-sc-hom-complex-restrict-open-differential). -/
theorem homComplex_restrict_open_differential (X : RingedSpace.{u}) (U : Opens X)
    (L M : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ) :
    let F := SheafOfModules.overFunctor.{u} (moduleRings X) U
    let LF := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L
    let MF := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M
    let H := homComplex (R := X.sheaf) L M
    let K := homComplex (R := X.sheaf.over U) LF MF
    let π := Classical.choose (homComplex_projections_exists (R := X.sheaf))
    let τ := Classical.choose (homComplex_projections_exists (R := X.sheaf.over U))
    ∀ (e : ∀ n : ℤ, F.obj (H.X n) ≅ K.X n),
      (∀ (n p q : ℤ) (hpq : p + n = q),
        (e n).hom ≫ τ LF MF n p q hpq =
          F.map (π L M n p q hpq) ≫
            (SheafOfModules.overHomObjIso (L.X p) (M.X q) U).hom) →
      ∀ (n m : ℤ), n + 1 = m →
        (e n).hom ≫ K.d n m = F.map (H.d n m) ≫ (e m).hom := by sorry

end CategoryTheory
