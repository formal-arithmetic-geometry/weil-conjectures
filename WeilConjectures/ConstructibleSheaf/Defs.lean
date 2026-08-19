/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SixFunctors.UpperLowerStar.Etale
public import WeilConjectures.Topology.Stratification

/-!
# Constructible sheaves on the small étale site

Let `X` be a scheme and let `F` be a sheaf on the small étale site of `X` (see
`AlgebraicGeometry.Scheme.smallEtaleTopology`) with values in a category `A`. Following
[SGA 4, Exp. IX, §2] we define:

- `F` is *constant* if it is isomorphic to the sheafification of a constant presheaf;
  this is mathlib's `CategoryTheory.Sheaf.IsConstant`.
- `F` is *locally constant* (`IsLocallyConstantSheaf`) if there is an étale cover of `X`
  (a jointly surjective family of étale maps `Uᵢ ⟶ X`, a cover in
  `Scheme.etalePrecoverage`) such that the restriction of `F` to each `Uᵢ` is constant;
  the trivializing data is packaged in `LocallyConstantDatum`. A constant sheaf is
  locally constant, trivialized by the identity cover
  (`CategoryTheory.Sheaf.IsConstant.isLocallyConstantSheaf`).
- `F` is *finite* (`IsFiniteSheaf`) if the stalk of `F` at every geometric point of `X`
  (`Scheme.pointSmallEtale`) is finite.
- `F` is *finite locally constant* (`IsFiniteLocallyConstantSheaf`) if it is locally
  constant and finite.
- `F` is *constructible* (`IsConstructibleSheaf`) if there is a stratification of `X`
  (`Scheme.Stratification`: a stratification of the underlying topological space of `X` —
  a finite partition into locally closed subsets, `Topology.Stratification`, following
  [Stacks 09XZ] — together with schemes immersed in `X` realizing the strata) such that
  the pullback of `F` to each stratum is finite locally constant.

All four predicates are `Prop`-valued classes.

The notions involving finiteness require `A` to be a concrete category, and finiteness
refers to the underlying type `CategoryTheory.ToType`. This covers sheaves of sets
(`A = Type u`), of abelian groups (`A = Ab`) and of `Λ`-modules (`A = ModuleCat Λ`), the
case relevant for the `ℓ`-adic formalism, where `Λ` is the finite ring `Λₙ = ℤ/ℓⁿℤ`.

To restrict `F` to an étale `U ⟶ X` we use the localized site: `F.over U` is the sheaf
induced by `F` on the localization of the small étale site at `U`, which is equivalent to
the small étale site of `U`. To restrict `F` to a stratum we use the pullback
`AlgebraicGeometry.Etale.upperStar` of `WeilConjectures.SixFunctors.UpperLowerStar.Etale`
along an immersion, the left adjoint of the pushforward `AlgebraicGeometry.Etale.lowerStar`.

## Implementation notes

- The pullback `Etale.upperStar` is defined by left Kan extension along base change
  followed by sheafification, and the Kan extensions in question are not known to exist
  for an arbitrary `f` with current mathlib: the full small étale site is not known to be
  essentially small (only the small affine étale site
  `AlgebraicGeometry.Scheme.AffineEtale` is). Mathematically they always exist; they are
  provided by the sorried instance
  `CategoryTheory.GrothendieckTopology.hasLeftKanExtension_op_overPullback` of
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension`. What remains
  assumed as an instance hypothesis
  of `IsConstructibleSheaf` is `HasWeakSheafify` for the localizations of the small étale
  sites of all schemes, quantified because the stratification is existentially
  quantified; for concrete `A`, `HasWeakSheafify` for the (unlocalized) small étale sites
  already holds by mathlib's `HasSheafify` instance for `smallEtaleTopology`.
- Similarly, `CategoryTheory.Sheaf.IsConstant.isLocallyConstantSheaf` assumes the
  existence of the right Kan extensions along `(Over.forget U).op` needed to compare
  sheafification on the small étale site with sheafification on its localizations.
-/

@[expose] public section

universe v u u'

open CategoryTheory Limits Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

section PullbackFunctor

variable (A : Type u') [Category.{u} A] [Abelian A] [IsGrothendieckAbelian.{u} A]

/-- The pullback of étale sheaves along `f : X ⟶ Y` sends constant sheaves to constant
sheaves: `constantSheaf ⋙ f^*` and `constantSheaf` are both left adjoint to global
sections of the pushforward, since base change preserves the terminal object of the
small étale site (`X ×_Y Y ≅ X`). -/
def upperStarConstantSheafIso (f : X ⟶ Y) :
    constantSheaf Y.smallEtaleTopology A ⋙ Etale.upperStar A f ≅
      constantSheaf X.smallEtaleTopology A :=
  Adjunction.leftAdjointUniq
    (((constantSheafAdj Y.smallEtaleTopology A terminalIsTerminal).comp
        (Etale.upperStarLowerStarAdjunction A f)).ofNatIsoRight
      (NatIso.ofComponents
        (F := Etale.lowerStar A f ⋙
          (sheafSections Y.smallEtaleTopology A).obj (op (⊤_ Y.Etale)))
        (G := (sheafSections X.smallEtaleTopology A).obj (op (⊤_ X.Etale)))
        (fun H ↦ H.obj.mapIso (PreservesTerminal.iso f.Etale).op.symm)
        (fun α ↦ (α.hom.naturality _).symm)))
    (constantSheafAdj X.smallEtaleTopology A terminalIsTerminal)

end PullbackFunctor

section LocallyConstant

variable {A : Type u'} [Category.{v} A]
  [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) A]

/-- The object of the small étale site of `X` given by a member of an étale cover
of `X`. -/
abbrev Cover.etalePrecoverageToEtale (𝒰 : Cover.{u} etalePrecoverage X) (i : 𝒰.I₀) : X.Etale :=
  MorphismProperty.Over.mk ⊤ (𝒰.f i) (𝒰.map_prop i)

/-- The datum of a trivialization of a sheaf `F` on the small étale site of `X`: an étale
cover of `X` — a jointly surjective family of étale maps, a cover in
`Scheme.etalePrecoverage` — such that the restriction of `F` to the site localized at
each member of the cover is constant in the sense of `CategoryTheory.Sheaf.IsConstant`.
`F` is locally constant if such a datum exists, see `IsLocallyConstantSheaf`. -/
structure LocallyConstantDatum (F : Sheaf X.smallEtaleTopology A) where
  /-- The trivializing étale cover. -/
  cover : Cover.{u} etalePrecoverage X
  /-- The restriction of `F` to the site localized at each member of the cover is
  constant. -/
  isConstant (i : cover.I₀) : (F.over (cover.etalePrecoverageToEtale i)).IsConstant
    (X.smallEtaleTopology.over (cover.etalePrecoverageToEtale i))

/-- A sheaf `F` on the small étale site of `X` is *locally constant* if there is an étale
cover of `X` trivializing `F`, i.e. a `LocallyConstantDatum`. Applies to sheaves of sets
(`A = Type u`), abelian groups (`A = Ab`), modules, etc. -/
class IsLocallyConstantSheaf (F : Sheaf X.smallEtaleTopology A) : Prop where
  nonempty_locallyConstantDatum : Nonempty (LocallyConstantDatum F)

/-- A constant sheaf on the small étale site is locally constant, trivialized by the
identity cover. The right Kan extension hypothesis compares sheafification on the small
étale site with sheafification on its localizations; it always holds mathematically, see
the module implementation notes. -/
lemma _root_.CategoryTheory.Sheaf.IsConstant.isLocallyConstantSheaf
    [∀ (U : X.Etale) (P : (Over U)ᵒᵖ ⥤ A), (Over.forget U).op.HasPointwiseRightKanExtension P]
    {F : Sheaf X.smallEtaleTopology A} (h : F.IsConstant X.smallEtaleTopology) :
    IsLocallyConstantSheaf F :=
  have := h
  have : etalePrecoverage.{u}.HasIsos := inferInstanceAs (precoverage @Etale).HasIsos
  ⟨⟨⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _), fun _ ↦ F.isConstant_over _⟩⟩⟩

end LocallyConstant

section FiniteSheaf

variable {A : Type u'} [Category.{v} A]
  {FA : A → A → Type*} {CD : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CD X) (CD Y)] [ConcreteCategory A FA]
  [HasColimitsOfSize.{u, u} A]

/-- A sheaf `F` on the small étale site of `X` with values in a concrete category is
*finite* if the stalk of `F` at every geometric point of `X` is finite. A geometric
point `Spec Ω ⟶ X`, with `Ω` a separably closed field, induces a point of the small
étale site (`Scheme.pointSmallEtale`), and the stalk of `F` is its fiber
`CategoryTheory.GrothendieckTopology.Point.sheafFiber` at this point. -/
class IsFiniteSheaf (F : Sheaf X.smallEtaleTopology A) : Prop where
  finite_sheafFiber (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    Finite (ToType ((pointSmallEtale s).sheafFiber.obj F))

end FiniteSheaf

section FiniteLocallyConstant

variable {A : Type u'} [Category.{v} A]
  {FA : A → A → Type*} {CD : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CD X) (CD Y)] [ConcreteCategory A FA]
  [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) A]
  [HasColimitsOfSize.{u, u} A]

/-- A sheaf `F` on the small étale site of `X` with values in a concrete category is
*finite locally constant* if it is locally constant and finite. For sheaves of sets,
equivalently (not proved here), `F` is representable by a scheme finite étale over
`X`. -/
class IsFiniteLocallyConstantSheaf (F : Sheaf X.smallEtaleTopology A) : Prop
    extends IsLocallyConstantSheaf F, IsFiniteSheaf F

end FiniteLocallyConstant

section Stratification

/-- A *stratification* of a scheme `X`: a stratification of the underlying topological
space of `X` (`Topology.Stratification`: a finite partition into locally closed subsets
following [Stacks 09XZ]) together with, for each stratum, a scheme immersed in `X` with
set-theoretic image the stratum. A sheaf on the small étale site of `X` is constructible
if its pullbacks to the strata of some stratification are finite locally constant, see
`IsConstructibleSheaf`. -/
structure Stratification (X : Scheme.{u}) extends Topology.Stratification X where
  /-- The schemes underlying the strata. -/
  domain : Fin n → Scheme.{u}
  /-- The immersions of the strata into `X`. -/
  immersion : ∀ i, domain i ⟶ X
  isImmersion : ∀ i, IsImmersion (immersion i) := by infer_instance
  range_immersion : ∀ i, Set.range (immersion i) = stratum i

attribute [instance] Stratification.isImmersion

end Stratification

section Constructible

variable {A : Type u'} [Category.{u} A] [Abelian A]
  {FA : A → A → Type*} {CD : A → Type u}
  [∀ X Y, FunLike (FA X Y) (CD X) (CD Y)] [ConcreteCategory.{u} A FA]
  [IsGrothendieckAbelian.{u} A]
  [HasColimitsOfSize.{u, u} A]
  [∀ (T : Scheme.{u}) (U : T.Etale), HasWeakSheafify (T.smallEtaleTopology.over U) A]

/-- A sheaf `F` on the small étale site of `X` with values in a concrete category is
*constructible* if there is a stratification of `X` such that the pullback of `F` to each
stratum is finite locally constant.

The stratification records a choice of scheme structure on each stratum via the immersion
`S.immersion i : S.domain i ⟶ X`; by topological invariance of the small étale site the
condition does not depend on this choice.

The left Kan extensions along base change needed by the pullback `Etale.upperStar` are
provided by the sorried instance
`CategoryTheory.GrothendieckTopology.hasLeftKanExtension_op_overPullback` of
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension`. Stating
`IsFiniteLocallyConstantSheaf` needs sheafification for the localizations of the small
étale sites of the strata; since the
stratification is existentially quantified, this is a hypothesis of the definition,
quantified over all schemes. It always holds mathematically but is not known to hold
with current mathlib (see the module implementation notes).

For `X` quasi-compact and quasi-separated this global definition agrees with the
affine-local one of [Stacks 03RW]. In the `ℓ`-adic formalism it is applied with
`A = ModuleCat Λ` for the finite ring `Λ = ℤ/ℓⁿℤ`. -/
class IsConstructibleSheaf (F : Sheaf X.smallEtaleTopology A) : Prop where
  exists_stratification : ∃ S : Stratification X, ∀ i : Fin S.n,
    IsFiniteLocallyConstantSheaf ((Etale.upperStar A (S.immersion i)).obj F)

end Constructible

end Scheme

end AlgebraicGeometry
