/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Sites.LocalSite
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.ConstructibleSheaf.Stratification
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs

/-!
# Constructible sheaves on the small pro-étale site

This is the pro-étale counterpart of `WeilConjectures.ConstructibleSheaf.Etale`, for
mathlib's pro-étale site `AlgebraicGeometry.Scheme.ProEt.topology`: the topology on the
category `X.ProEt` of weakly étale schemes over `X` whose covers are the pro-étale covers
of [Bhatt–Scholze, Definition 4.1.1], that is, the fpqc covers by weakly étale morphisms.
The two files share the site-independent `AlgebraicGeometry.Scheme.Stratification` of
`WeilConjectures.ConstructibleSheaf.Stratification`.

For a sheaf `F` on the small pro-étale site of `X` with values in a category `A` we define,
in exact parallel with the étale case:

- `F` is *locally constant* (`ProEtale.IsLocallyConstantSheaf`) if there is a pro-étale
  cover of `X` such that the restriction of `F` to each member is constant in the sense of
  `CategoryTheory.Sheaf.IsConstant`; the trivializing data is packaged in
  `ProEtale.LocallyConstantDatum`. A constant sheaf is locally constant, trivialized by the
  identity cover (`CategoryTheory.Sheaf.IsConstant.proEtaleIsLocallyConstantSheaf`).
- `F` is *finite* (`ProEtale.IsFiniteSheaf`) if the stalk of `F` at every geometric point of
  `X` is finite, the stalk being taken at the point `ProEtale.point` of the small pro-étale
  site.
- `F` is *finite locally constant* (`ProEtale.IsFiniteLocallyConstantSheaf`) if it is
  locally constant and finite.
- `F` is *constructible* (`ProEtale.IsConstructibleSheaf`) if there is a stratification of
  `X` such that the pullback of `F` to each stratum, along
  `AlgebraicGeometry.ProEtale.upperStar`, is finite locally constant.

The one real difference with the étale file is the *cover*: a pro-étale cover is a
quasi-compact jointly surjective family of weakly étale morphisms, a member of
`AlgebraicGeometry.Scheme.proetalePrecoverage`, and joint surjectivity alone does not
suffice. Consequently `Scheme.etalePrecoverage` is replaced by
`Scheme.proetalePrecoverage` throughout.

## Implementation notes

- The point `ProEtale.point` attached to a geometric point `s : Spec Ω ⟶ X` of `X`, with
  `Ω` separably closed, has fiber functor `V ↦ Hom_X(Spec Ω, V)`, exactly as
  `AlgebraicGeometry.Scheme.pointSmallEtale` does on the étale site. Its cofilteredness is
  proved — the small pro-étale site has finite limits and the fiber functor preserves them.
  Its other two axioms are sorried:
  * `initiallySmall` asks for a cofinal small subcategory of the category of elements.
    Mathlib's étale proof goes through the small *affine* étale site
    (`AlgebraicGeometry.Scheme.AffineEtale`), which has no pro-étale counterpart yet; one
    has to bound the weakly étale objects by a cardinal instead, as in
    [Bhatt–Scholze, §4.1].
  * `jointly_surjective` is the lifting property of weakly étale morphisms against a
    separably closed field along a covering family, the analogue of
    `AlgebraicGeometry.Scheme.exists_fac_of_etale_of_isSepClosed`.
- Sheafification on the localizations of the small pro-étale sites, needed to restrict a
  sheaf to a member of a pro-étale cover, is
  `CategoryTheory.GrothendieckTopology.hasSheafify_over_proEtTopology`; the left Kan
  extensions along base change needed by `ProEtale.upperStar` are
  `AlgebraicGeometry.ProEtale.hasLeftKanExtension_op_overPullback`. Both are cases of the
  sorried instances of `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify` and
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension`.
-/

@[expose] public section

universe u u'

open CategoryTheory Limits Opposite

noncomputable section

namespace AlgebraicGeometry

open Scheme

variable {X Y : Scheme.{u}}

section PullbackFunctor

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The pullback of pro-étale sheaves along `f : X ⟶ Y` sends constant sheaves to constant
sheaves: `constantSheaf ⋙ f^*` and `constantSheaf` are both left adjoint to global
sections of the pushforward, since base change preserves the terminal object of the
small pro-étale site (`X ×_Y Y ≅ X`). -/
def ProEtale.upperStarConstantSheafIso (f : X ⟶ Y) :
    constantSheaf (Scheme.ProEt.topology Y) A ⋙ ProEtale.upperStar A f ≅
      constantSheaf (Scheme.ProEt.topology X) A :=
  Adjunction.leftAdjointUniq
    (((constantSheafAdj (Scheme.ProEt.topology Y) A terminalIsTerminal).comp
        (ProEtale.upperStarLowerStarAdjunction A f)).ofNatIsoRight
      (NatIso.ofComponents
        (F := ProEtale.lowerStar A f ⋙
          (sheafSections (Scheme.ProEt.topology Y) A).obj (op (⊤_ Y.ProEt)))
        (G := (sheafSections (Scheme.ProEt.topology X) A).obj (op (⊤_ X.ProEt)))
        (fun H ↦ H.obj.mapIso
          (PreservesTerminal.iso (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f)).op.symm)
        (fun α ↦ (α.hom.naturality _).symm)))
    (constantSheafAdj (Scheme.ProEt.topology X) A terminalIsTerminal)

end PullbackFunctor

section Point

/-- The category of elements of the fiber functor `V ↦ Hom_X(Spec Ω, V)` of the small
pro-étale site is cofiltered: the site has finite limits and the fiber functor, being the
composite of the forgetful functor to `Over X` with a `coyoneda`, preserves them. -/
instance ProEtale.isCofiltered_elements {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X) :
    IsCofiltered (Scheme.ProEt.forget X ⋙ coyoneda.obj (op (Over.mk s))).Elements :=
  Functor.isCofiltered_elements _

set_option backward.isDefEq.respectTransparency.types false in
/-- The point of the small pro-étale site of `X` attached to a geometric point
`s : Spec Ω ⟶ X` with `Ω` separably closed: its fiber functor sends a weakly étale
`V ⟶ X` to the set of `X`-morphisms `Spec Ω ⟶ V`. This is the pro-étale analogue of
`AlgebraicGeometry.Scheme.pointSmallEtale`; the stalk of a sheaf at the geometric point is
the fiber `CategoryTheory.GrothendieckTopology.Point.sheafFiber` at this point.

Cofilteredness of the category of elements is `ProEtale.isCofiltered_elements`; the two
remaining axioms are sorried, see the module implementation notes. -/
def ProEtale.point {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    (Scheme.ProEt.topology X).Point where
  fiber := Scheme.ProEt.forget X ⋙ coyoneda.obj (op (Over.mk s))
  initiallySmall := sorry
  jointly_surjective := sorry

end Point

section LocallyConstant

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The object of the small pro-étale site of `X` given by a member of a pro-étale cover
of `X`. -/
abbrev Scheme.Cover.proetalePrecoverageToProEt (𝒰 : Cover.{u} proetalePrecoverage X)
    (i : 𝒰.I₀) : X.ProEt :=
  MorphismProperty.Over.mk ⊤ (𝒰.f i)
    (Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ 𝒰.mem₀ ⟨i⟩)

/-- The datum of a trivialization of a sheaf `F` on the small pro-étale site of `X`: a
pro-étale cover of `X` — a quasi-compact jointly surjective family of weakly étale maps, a
cover in `Scheme.proetalePrecoverage` — such that the restriction of `F` to the site
localized at each member of the cover is constant in the sense of
`CategoryTheory.Sheaf.IsConstant`. `F` is locally constant if such a datum exists, see
`ProEtale.IsLocallyConstantSheaf`. -/
structure ProEtale.LocallyConstantDatum (F : Sheaf (Scheme.ProEt.topology X) A) where
  /-- The trivializing pro-étale cover. -/
  cover : Cover.{u} proetalePrecoverage X
  /-- The restriction of `F` to the site localized at each member of the cover is
  constant. -/
  isConstant (i : cover.I₀) : (F.over (cover.proetalePrecoverageToProEt i)).IsConstant
    ((Scheme.ProEt.topology X).over (cover.proetalePrecoverageToProEt i))

/-- A sheaf `F` on the small pro-étale site of `X` is *locally constant* if there is a
pro-étale cover of `X` trivializing `F`, i.e. a `ProEtale.LocallyConstantDatum`. -/
class ProEtale.IsLocallyConstantSheaf (F : Sheaf (Scheme.ProEt.topology X) A) : Prop where
  nonempty_locallyConstantDatum : Nonempty (ProEtale.LocallyConstantDatum F)

/-- A constant sheaf on the small pro-étale site is locally constant, trivialized by the
identity cover. The right Kan extension hypothesis compares sheafification on the small
pro-étale site with sheafification on its localizations. -/
lemma _root_.CategoryTheory.Sheaf.IsConstant.proEtaleIsLocallyConstantSheaf
    [∀ (U : X.ProEt) (P : (Over U)ᵒᵖ ⥤ A), (Over.forget U).op.HasPointwiseRightKanExtension P]
    {F : Sheaf (Scheme.ProEt.topology X) A} (h : F.IsConstant (Scheme.ProEt.topology X)) :
    ProEtale.IsLocallyConstantSheaf F :=
  have := h
  ⟨⟨⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _), fun _ ↦ F.isConstant_over _⟩⟩⟩

end LocallyConstant

section FiniteSheaf

variable {A : Type u'} [Category.{u + 1} A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasColimitsOfSize.{u, u} A]

/-- A sheaf `F` on the small pro-étale site of `X` with values in a concrete category is
*finite* if the stalk of `F` at every geometric point of `X` is finite. A geometric point
`Spec Ω ⟶ X`, with `Ω` a separably closed field, induces the point `ProEtale.point` of the
small pro-étale site, and the stalk of `F` is its fiber
`CategoryTheory.GrothendieckTopology.Point.sheafFiber` at this point. -/
class ProEtale.IsFiniteSheaf (F : Sheaf (Scheme.ProEt.topology X) A) : Prop where
  finite_sheafFiber (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    Finite (ToType ((ProEtale.point s).sheafFiber.obj F))

end FiniteSheaf

section FiniteLocallyConstant

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

/-- A sheaf `F` on the small pro-étale site of `X` with values in a concrete category is
*finite locally constant* if it is locally constant and finite. -/
class ProEtale.IsFiniteLocallyConstantSheaf (F : Sheaf (Scheme.ProEt.topology X) A) : Prop
    extends ProEtale.IsLocallyConstantSheaf F, ProEtale.IsFiniteSheaf F

end FiniteLocallyConstant

section Constructible

variable {A : Type u'} [Category.{u + 1} A] [Abelian A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [IsGrothendieckAbelian.{u + 1} A]

/-- A sheaf `F` on the small pro-étale site of `X` with values in a concrete category is
*constructible* if there is a stratification of `X` such that the pullback of `F` to each
stratum is finite locally constant.

The stratification records a choice of scheme structure on each stratum via the immersion
`S.immersion i : S.domain i ⟶ X`; by topological invariance of the small pro-étale site the
condition does not depend on this choice.

In the `ℓ`-adic formalism it is applied with `A = ModuleCat Λ` for the finite ring
`Λ = ℤ/ℓⁿℤ`. -/
class ProEtale.IsConstructibleSheaf (F : Sheaf (Scheme.ProEt.topology X) A) : Prop where
  exists_stratification : ∃ S : Stratification X, ∀ i : Fin S.n,
    ProEtale.IsFiniteLocallyConstantSheaf ((ProEtale.upperStar A (S.immersion i)).obj F)

end Constructible

end AlgebraicGeometry
