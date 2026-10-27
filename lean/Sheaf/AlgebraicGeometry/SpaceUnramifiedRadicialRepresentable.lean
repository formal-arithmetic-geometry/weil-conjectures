/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.UnramifiedMorphism
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Sheaf.AlgebraicGeometry.SeparatedLocallyQuasiFiniteSpaceRepresentable

/-! # Unramified universally injective space morphisms are representable

Source: Stacks Project, Tag 05W6, spaces-more-morphisms.tex,
lemma-universally-injective-unramified, moreover clause under condition (2)
(blueprint: lem-sfb-space-unramified-radicial-representable).

The universal-injectivity hypothesis ranges over all algebraic-space base changes.
The conclusion is scheme-test representability of the given morphism.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- An unramified universally injective morphism of algebraic spaces is representable
by schemes. Unramifiedness uses the existing chart test, including local finite type.
Universal injectivity says that two field-valued representatives of `X ×_Y Y'` with the
same point class in `|Y'|` already have the same point class, for the point classes and
representative map of def-a1-space-point-topology.
Source: Stacks Project, Tag 05W6, lemma-universally-injective-unramified,
moreover clause under condition (2)
(blueprint: lem-sfb-space-unramified-radicial-representable).

Proof:
1. Fix an arbitrary scheme test `h_T → Y`, regard it as `schemeSpace T`
   [def-trf-scheme-algebraic-space], and form `E = X ×_Y h_T` with projection `g`.
   It is an algebraic space by [lem-trf-space-fibre-products-etale-covers].
   By [lem-sfb-space-unramified-permanence], `g` is unramified and hence locally
   of finite type on étale scheme charts.
2. Associativity of sheaf fibre products shows that `g` remains universally injective.
   In particular the projection `p : E ×_T E → E` is injective on point classes
   [def-a1-space-point-topology]. Its diagonal section `δ` satisfies `p δ = 1`.
   For every point `z`, injectivity applied to `p (δ (p z)) = p z` gives `δ (p z) = z`.
   Thus the diagonal is surjective on points. These identifications are sectionwise
   compatible-pair identities for [lem-trf-space-fibre-products-etale-covers].
3. By [lem-sfb-unramified-space-open-diagonal], the diagonal of `g` is a representable
   open immersion. The full-point-image criterion of [lem-a1-space-point-open-calculus]
   makes it an isomorphism. Consequently `g` is a monomorphism of sheaves:
   a pair of sections with the same image is a section of the fibre product,
   and the inverse diagonal expresses it as an equal pair.
4. Apply [lem-sfb-space-lft-monomorphism-separated-lqf] to obtain separatedness and
   chartwise local quasi-finiteness of `g`; no quasi-compactness is required.
5. By [lem-a1-separated-locally-qf-space-representable], `E` is represented by a scheme
   over `T`, with the representing isomorphism over `h_T`. This gives a representing
   scheme pullback square. Since the test was arbitrary, `f` is representable. -/
theorem isRepresentable_of_unramified_universallyInjective {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hunramified : MapIsLocally (@IsUnramified) f)
    (hinjective : ∀ (Y' : AlgebraicSpace S) (g : Y' ⟶ Y)
      (a b : PointRepresentative (Limits.pullback f.hom g.hom).obj),
      (Quot.mk _ (a.map (Limits.pullback.snd f.hom g.hom).hom) : Point Y'.obj.obj) =
          Quot.mk _ (b.map (Limits.pullback.snd f.hom g.hom).hom) →
        (Quot.mk _ a : Point (Limits.pullback f.hom g.hom).obj) = Quot.mk _ b) :
    IsRepresentable f.hom.hom := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
