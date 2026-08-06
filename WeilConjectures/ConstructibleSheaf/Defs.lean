/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib
public import WeilConjectures.SixFunctors.UpperLowerStar.Etale

/-!
# Constructible sheaves on the small étale site

Let `X` be a scheme and let `F` be a sheaf on the small étale site of `X` (see
`AlgebraicGeometry.Scheme.smallEtaleTopology`) with values in a category `A`. Following
[SGA 4, Exp. IX, §2] we define:

- `F` is *constant* if it is isomorphic to the sheafification of a constant presheaf;
  this is mathlib's `CategoryTheory.Sheaf.IsConstant`.
- `F` is *locally constant* (`IsLocallyConstantSheaf`) if there is an étale cover of `X`
  (a jointly surjective family of étale maps `Uᵢ ⟶ X`, a cover in
  `Scheme.etalePrecoverage`) such that the restriction of `F` to each `Uᵢ` is isomorphic
  to a constant sheaf; the trivializing data is packaged in `LocallyConstantDatum`.
- `F` is *finite* (`IsFiniteSheaf`) if the stalk of `F` at every geometric point of `X`
  (`Scheme.pointSmallEtale`) is finite.
- `F` is *finite locally constant* (`IsFiniteLocallyConstantSheaf`) if it is locally
  constant and finite.
- `F` is *constructible* (`IsConstructibleSheaf`) if there is a stratification of `X`
  (`Scheme.Stratification`: a finite family of schemes immersed in `X` with pairwise
  disjoint constructible images covering `X`) such that the pullback of `F` to each
  stratum is finite locally constant.

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
  `AlgebraicGeometry.Scheme.AffineEtale` is). Mathematically they always exist, so in
  `IsConstructibleSheaf` their existence, together with `HasWeakSheafify` for the small
  étale sites of the strata, is assumed as an instance hypothesis inside the
  quantification over strata; the definition is mathematically unchanged and the
  hypotheses become vacuous once essential smallness of the small étale site is
  formalized (for concrete `A`, `HasWeakSheafify` already holds by mathlib's
  `HasSheafify` instance for `smallEtaleTopology`).
-/

@[expose] public section

universe v u u'

-- Matches the project-wide option in `lakefile.toml`; needed (as in mathlib's own
-- étale site files) because `@Etale` and `MorphismProperty` differ in binder annotations.
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

section Functoriality

/-- The base change functor `Y.Etale ⥤ X.Etale` along a morphism `f : X ⟶ Y`, sending an
étale `V ⟶ Y` to the projection `V ×_Y X ⟶ X`. This is the functor along which the
pushforward `AlgebraicGeometry.Etale.lowerStar` and the pullback
`AlgebraicGeometry.Etale.upperStar` are defined. -/
def Hom.etaleBaseChange (f : X ⟶ Y) : Y.Etale ⥤ X.Etale :=
  MorphismProperty.Over.pullback @Etale ⊤ f

instance (f : X ⟶ Y) : PreservesFiniteLimits f.etaleBaseChange :=
  inferInstanceAs <| PreservesFiniteLimits (MorphismProperty.Over.pullback @Etale ⊤ f)

instance : HasFiniteLimits Y.Etale :=
  inferInstanceAs <| HasFiniteLimits (MorphismProperty.Over @Etale ⊤ Y)

end Functoriality

section PullbackFunctor

variable (A : Type u') [Category.{v} A]

/-- The pullback of étale sheaves along `f : X ⟶ Y` sends constant sheaves to constant
sheaves: `constantSheaf ⋙ f^*` and `constantSheaf` are both left adjoint to global
sections of the pushforward, since base change preserves the terminal object of the
small étale site (`X ×_Y Y ≅ X`). -/
def upperStarConstantSheafIso (f : X ⟶ Y)
    [∀ P : Y.Etaleᵒᵖ ⥤ A, (MorphismProperty.Over.pullback @Etale ⊤ f).op.HasLeftKanExtension P]
    [HasWeakSheafify Y.smallEtaleTopology A] [HasWeakSheafify X.smallEtaleTopology A] :
    constantSheaf Y.smallEtaleTopology A ⋙ Etale.upperStar A f ≅
      constantSheaf X.smallEtaleTopology A :=
  Adjunction.leftAdjointUniq
    (((constantSheafAdj Y.smallEtaleTopology A terminalIsTerminal).comp
        (Etale.upperStarLowerStarAdjunction A f)).ofNatIsoRight
      (NatIso.ofComponents
        (F := Etale.lowerStar A f ⋙
          (sheafSections Y.smallEtaleTopology A).obj (op (⊤_ Y.Etale)))
        (G := (sheafSections X.smallEtaleTopology A).obj (op (⊤_ X.Etale)))
        (fun H ↦ H.obj.mapIso (PreservesTerminal.iso f.etaleBaseChange).op.symm)
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
`Scheme.etalePrecoverage` — together with values and isomorphisms of the restriction of
`F` to the site localized at each member of the cover with the constant sheaf at the
corresponding value. `F` is locally constant if such a datum exists, see
`IsLocallyConstantSheaf`. -/
structure LocallyConstantDatum (F : Sheaf X.smallEtaleTopology A) where
  /-- The trivializing étale cover. -/
  cover : Cover.{u} etalePrecoverage X
  /-- The values of `F` on the members of the cover. -/
  val : cover.I₀ → A
  /-- The trivializing isomorphisms. -/
  iso (i : cover.I₀) : F.over (cover.etalePrecoverageToEtale i) ≅
    (constantSheaf (X.smallEtaleTopology.over (cover.etalePrecoverageToEtale i)) A).obj (val i)

/-- Given a trivializing datum for `F`, the restriction of `F` to the site localized at
each member of the trivializing cover is constant in the sense of
`CategoryTheory.Sheaf.IsConstant`. -/
lemma LocallyConstantDatum.isConstant {F : Sheaf X.smallEtaleTopology A}
    (D : LocallyConstantDatum F) (i : D.cover.I₀) :
    (F.over (D.cover.etalePrecoverageToEtale i)).IsConstant
      (X.smallEtaleTopology.over (D.cover.etalePrecoverageToEtale i)) :=
  Sheaf.isConstant_of_iso _ (D.iso i)

/-- A sheaf `F` on the small étale site of `X` is *locally constant* if there is an étale
cover of `X` trivializing `F`, i.e. a `LocallyConstantDatum`. Applies to sheaves of sets
(`A = Type u`), abelian groups (`A = Ab`), modules, etc. -/
def IsLocallyConstantSheaf (F : Sheaf X.smallEtaleTopology A) : Prop :=
  Nonempty (LocallyConstantDatum F)

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
def IsFiniteSheaf (F : Sheaf X.smallEtaleTopology A) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
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
def IsFiniteLocallyConstantSheaf (F : Sheaf X.smallEtaleTopology A) : Prop :=
  IsLocallyConstantSheaf F ∧ IsFiniteSheaf F

theorem IsFiniteLocallyConstantSheaf.isLocallyConstantSheaf
    {F : Sheaf X.smallEtaleTopology A} (hF : IsFiniteLocallyConstantSheaf F) :
    IsLocallyConstantSheaf F := hF.1

theorem IsFiniteLocallyConstantSheaf.isFiniteSheaf
    {F : Sheaf X.smallEtaleTopology A} (hF : IsFiniteLocallyConstantSheaf F) :
    IsFiniteSheaf F := hF.2

end FiniteLocallyConstant

section Stratification

/-- A *stratification* of a scheme `X`: a finite family of schemes immersed in `X` whose
set-theoretic images — the *strata* — are pairwise disjoint constructible subsets covering
`X`. The strata are automatically locally closed, see
`Stratification.isLocallyClosed_stratum`. A sheaf on the small étale site of `X` is
constructible if its pullbacks to the strata of some stratification are finite locally
constant, see `IsConstructibleSheaf`. -/
structure Stratification (X : Scheme.{u}) where
  /-- The number of strata. -/
  n : ℕ
  /-- The schemes underlying the strata. -/
  domain : Fin n → Scheme.{u}
  /-- The immersions of the strata into `X`. -/
  immersion : ∀ i, domain i ⟶ X
  isImmersion : ∀ i, IsImmersion (immersion i) := by infer_instance
  iUnion_range_eq_univ : (⋃ i, Set.range (immersion i)) = Set.univ
  pairwise_disjoint : Pairwise (Function.onFun Disjoint fun i ↦ Set.range (immersion i))
  isConstructible_range : ∀ i, Topology.IsConstructible (Set.range (immersion i))

attribute [instance] Stratification.isImmersion

/-- The underlying set of the `i`-th stratum of a stratification. -/
def Stratification.stratum (S : Stratification X) (i : Fin S.n) : Set X :=
  Set.range (S.immersion i)

lemma Stratification.isLocallyClosed_stratum (S : Stratification X) (i : Fin S.n) :
    IsLocallyClosed (S.stratum i) :=
  (S.immersion i).isLocallyClosed_range

end Stratification

section Constructible

variable {A : Type u'} [Category.{v} A]
  {FA : A → A → Type*} {CD : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CD X) (CD Y)] [ConcreteCategory A FA]
  [HasColimitsOfSize.{u, u} A]

/-- A sheaf `F` on the small étale site of `X` with values in a concrete category is
*constructible* if there is a stratification of `X` such that the pullback of `F` to each
stratum is finite locally constant.

The stratification records a choice of scheme structure on each stratum via the immersion
`S.immersion i : S.domain i ⟶ X`; by topological invariance of the small étale site the
condition does not depend on this choice.

The pullback `Etale.upperStar` needs left Kan extensions along base change by the
immersions, and stating `IsFiniteLocallyConstantSheaf` needs sheafification for the small
étale sites of the strata and their localizations; all are assumed as instance hypotheses
inside the quantification. The Kan extensions always exist mathematically but are not
known to exist with current mathlib (see the module implementation notes); the
sheafification hypothesis for `smallEtaleTopology` is discharged by mathlib's
`HasSheafify` instance whenever `A` is a suitable concrete category.

For `X` quasi-compact and quasi-separated this global definition agrees with the
affine-local one of [Stacks 03RW]. In the `ℓ`-adic formalism it is applied with
`A = ModuleCat Λ` for the finite ring `Λ = ℤ/ℓⁿℤ`. -/
def IsConstructibleSheaf (F : Sheaf X.smallEtaleTopology A) : Prop :=
  ∃ S : Stratification X, ∀ (i : Fin S.n)
    [∀ P : X.Etaleᵒᵖ ⥤ A,
        (MorphismProperty.Over.pullback @Etale ⊤ (S.immersion i)).op.HasLeftKanExtension P]
      [HasWeakSheafify (S.domain i).smallEtaleTopology A]
      [∀ U : (S.domain i).Etale, HasWeakSheafify ((S.domain i).smallEtaleTopology.over U) A],
        IsFiniteLocallyConstantSheaf ((Etale.upperStar A (S.immersion i)).obj F)

end Constructible

end Scheme

end AlgebraicGeometry
