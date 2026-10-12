/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
import Mathlib.CategoryTheory.Presentable.Directed
import Sheaf.AlgebraicGeometry.DescendFinite
import Sheaf.AlgebraicGeometry.DescendSurjective
import Sheaf.AlgebraicGeometry.EtaleInverseLimitDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-! # Descent of an unpointed finite Galois torsor

Source: Stacks Project, Tags 0BTV and 01ZM, used in the last paragraph of Tag 0EZJ.
(blueprint: lem-sbc-galois-cover-stage-descent)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- An unpointed finite torsor descends along affine inverse limits.

Source: Stacks Project, Tags 0BTV and 01ZM; Tag 0EZJ, final paragraph.
(blueprint: lem-sbc-galois-cover-stage-descent)

Proof:
Reindex the small cofiltered category by a coinitial directed poset. This preserves
its limit and the affine-transition and qcqs assumptions. Apply finite-presentation
approximation to the finite étale morphism `Z.π`. Descend finiteness and étaleness
at a later stage using Tags 01ZO and 07RP. The finite étale image is clopen.
Surjectivity descends by Tag 07RR. In this finite étale case one can also use
that the complementary clopen has empty pullback, and affine-transition
compactness makes the complement empty at some later stage.

Enumerate the finite group by a finite type. Descend the finitely many endomorphisms
`Z.smul g` as maps over the base using the morphism part of 01ZM. Its equality part
makes all unit and multiplication equations hold at a common later stage. Finite
coproducts and fibre products commute with base change. The canonical torsor comparison
map therefore has base change equal to the original comparison map. Descend the
inverse of the latter map and both inverse equations by 01ZM, at a common stage.
The descended map, action, and torsor comparison form `Z₀`; its comparison with `Z`
gives `χ` and the cartesian square. Transfer that stage back to the original category.
-/
theorem GaloisCover.exists_stage_of_affine_limits
    {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    (hDqc : ∀ i, CompactSpace (D.obj i)) (hDqs : ∀ i, QuasiSeparatedSpace (D.obj i))
    (hDa : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f))
    {X : Scheme.{u}} (κ : (Functor.const I).obj X ⟶ D)
    (hκ : IsLimit (Cone.mk X κ))
    (G : Type (u + 1)) [Group G] [Finite G] (Z : GaloisCover G X) :
    ∃ (i : I) (Z₀ : GaloisCover G (D.obj i)) (χ : Z.P ⟶ Z₀.P),
      IsPullback χ Z.π Z₀.π (κ.app i) := by sorry

end AlgebraicGeometry.Scheme
