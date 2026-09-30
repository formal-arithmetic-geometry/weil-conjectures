/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Over
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Coefficients
public import WeilConjectures.Mathlib.CategoryTheory.Sites.LeftExact
import WeilConjectures.CategoryTheory.Sites.TransfinitePlusSheaf
import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu

/-!

# Sheafification on essentially small sites

Sheafification exists for `A`-valued presheaves on any essentially small site, for a
Grothendieck abelian category `A` with `Hom`-types in the universe `u + 1`, one above the
universe `u` of the base schemes.

On a *small* site `(C, J)`, with `A` Grothendieck abelian with `Hom`-types in the universe of
`C` (`CategoryTheory.GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian`), the
sheafification functor is the transfinite plus construction
`CategoryTheory.GrothendieckTopology.transfinitePlusSheaf`, iterated along a regular cardinal
`κ` for which a separator of `A` is `κ`-presentable and `C` has fewer than `κ` arrows. It is
left exact because each plus step is and filtered colimits in `A` are exact. An essentially
small site is equivalent to a small one (`hasSheafify_of_essentiallySmall`), and the small
étale site, the small pro-étale site and their localizations `J.over V` are essentially small
in `u + 1`.

The localized instances are what lets the constructible-sheaf definitions of
`WeilConjectures.ConstructibleSheaf.Defs` restrict a sheaf to a member of an étale cover
without carrying `HasWeakSheafify` for the localized sites as a hypothesis.

-/

@[expose] public section

universe u' v u

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace CategoryTheory.GrothendieckTopology

/-- Sheafification for `A`-valued presheaves on a small site `(C, J)`, for a Grothendieck
abelian coefficient category `A` whose `Hom`-types live in the universe of `C`.

The sheafification functor is the transfinite plus construction
`CategoryTheory.GrothendieckTopology.transfinitePlusSheaf`, iterated along a regular cardinal
`κ` bounding the cardinalities of `Subobject G`, `G ⟶ G` for a separator `G` of `A` (so that
`G` is `κ`-presentable) and of `Arrow C`. -/
theorem hasSheafify_of_isGrothendieckAbelian {C : Type v} [SmallCategory C]
    (J : GrothendieckTopology C) (A : Type u') [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{v} A] :
    HasSheafify J A := by
  let G := separator A
  obtain ⟨κ, hκ, h⟩ := HasCardinalLT.exists_regular_cardinal.{v}
    (Subobject G ⊕ (G ⟶ G) ⊕ Arrow C)
  have : Fact κ.IsRegular := ⟨hκ⟩
  have := IsGrothendieckAbelian.isCardinalPresentable_of_isSeparator (isSeparator_separator A)
    (h.of_injective _ Sum.inl_injective)
    (h.of_injective _ (Sum.inr_injective.comp Sum.inl_injective))
  have hC : HasCardinalLT (Arrow C) κ :=
    h.of_injective _ (Sum.inr_injective.comp Sum.inr_injective)
  have : Nonempty κ.ord.ToType := by simpa using hκ.ne_zero
  have := WellFoundedLT.toOrderBot κ.ord.ToType
  exact HasSheafify.mk' J A (J.transfinitePlusAdjunction A κ (isSeparator_separator A) hC)

/-- Sheafification for `A`-valued presheaves on an essentially small site, for a
Grothendieck abelian coefficient category `A` with `Hom`-types in the universe `u + 1`: the
site is equivalent to a small one, to which
`CategoryTheory.GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian` applies.

All the other instances in this file are special cases. -/
instance (priority := high) hasSheafify_of_essentiallySmall (A : Type u')
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    {C : Type*} [Category* C] [EssentiallySmall.{u + 1} C] (J : GrothendieckTopology C) :
    HasSheafify J A :=
  have : HasSheafify ((equivSmallModel C).inverse.inducedTopology J) A :=
    hasSheafify_of_isGrothendieckAbelian _ A
  hasSheafifyEssentiallySmallSite J A

/-- Sheafification for `A`-valued presheaves on the small étale site of a scheme: the site
is essentially small in `u + 1`. -/
instance (priority := high) hasSheafify_smallEtaleTopology (A : Type u')
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A] (X : Scheme.{u}) :
    HasSheafify X.smallEtaleTopology A :=
  inferInstance

/-- Sheafification for `A`-valued presheaves on the localization of the small étale site
at an étale `U ⟶ X`: a slice of an essentially small site is again essentially small. This
is what lets a sheaf be restricted to a member of an étale cover without assuming
`HasWeakSheafify` for the localized site. -/
instance (priority := high) hasSheafify_over_smallEtaleTopology (A : Type u')
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A] (X : Scheme.{u})
    (U : X.Etale) :
    HasSheafify (X.smallEtaleTopology.over U) A :=
  inferInstance

/-- Sheafification for `A`-valued presheaves on the small pro-étale site of a scheme: the
site is essentially small in `u + 1`. -/
instance (priority := high) hasSheafify_proEtTopology (A : Type u')
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A] (X : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology X) A :=
  inferInstance

/-- Sheafification for `A`-valued presheaves on the localization of the small pro-étale
site at a weakly étale `U ⟶ X`: a slice of an essentially small site is again essentially
small. -/
instance (priority := high) hasSheafify_over_proEtTopology (A : Type u')
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A] (X : Scheme.{u})
    (U : X.ProEt) :
    HasSheafify ((Scheme.ProEt.topology X).over U) A :=
  inferInstance

/-- Sheafification for `A`-valued presheaves on the small `Q`-site of `P`-schemes over a
scheme `U`, for a coefficient category `A` with small-site sheafification: the site has
objects in `Type (u + 1)` and `Hom`-types in `Type u`, so it is essentially `u + 1`-small. -/
instance (priority := high) hasSheafify_smallGrothendieckTopology (A : Type u')
    [Category.{u + 1} A] [HasSmallSiteSheafify A] (P Q : MorphismProperty Scheme.{u})
    [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
    (U : Scheme.{u}) :
    HasSheafify (U.smallGrothendieckTopology Q (Q := P)) A :=
  HasSmallSiteSheafify.hasSheafify_of_essentiallySmall A _

/-- Sheafification for `A`-valued presheaves on the localization at `V` of the small
`Q`-site of `P`-schemes over `U`, for a coefficient category `A` with small-site
sheafification: the slice of the site at `V` again has objects in `Type (u + 1)` and
`Hom`-types in `Type u`. -/
instance (priority := high) hasSheafify_over_smallGrothendieckTopology (A : Type u')
    [Category.{u + 1} A] [HasSmallSiteSheafify A] (P Q : MorphismProperty Scheme.{u})
    [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
    (U : Scheme.{u}) (V : P.Over ⊤ U) :
    HasSheafify ((U.smallGrothendieckTopology Q (Q := P)).over V) A :=
  HasSmallSiteSheafify.hasSheafify_of_essentiallySmall A _

end CategoryTheory.GrothendieckTopology
