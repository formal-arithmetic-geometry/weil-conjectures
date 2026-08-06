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
- `F` is *locally constant* (`IsLocallyConstantSheaf`) if there is a jointly surjective
  family of étale maps `Uᵢ ⟶ X` such that the restriction of `F` to each `Uᵢ` is
  isomorphic to the restriction of a constant sheaf.
- `F` is *finite locally constant* (`IsFiniteLocallyConstantSheaf`) if moreover the
  values of the trivializing constant sheaves are finite.
- `F` is *constructible* (`IsConstructibleSheaf`) if there is a stratification of `X`
  (`Scheme.Stratification`: a finite family of schemes immersed in `X` with pairwise
  disjoint constructible images covering `X`) such that the pullback of `F` to each
  stratum is finite locally constant.

The last two notions require a notion of finiteness for the values of `F`, so there `A` is
assumed to be a concrete category and finiteness refers to the underlying type
`CategoryTheory.ToType`. This covers sheaves of sets (`A = Type u`), of abelian groups
(`A = Ab`) and of `Λ`-modules (`A = ModuleCat Λ`), the case relevant for the `ℓ`-adic
formalism, where `Λ` is the finite ring `Λₙ = ℤ/ℓⁿℤ`.

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

variable {A : Type u'} [Category.{v} A] [HasWeakSheafify X.smallEtaleTopology A]

/-- A sheaf `F` on the small étale site of `X` is *constant with value `V` over an étale
`U ⟶ X`* if the restriction of `F` to the site localized at `U` is isomorphic to the
restriction of the constant sheaf with value `V`. -/
def IsConstantSheafOn (F : Sheaf X.smallEtaleTopology A) (V : A) (U : X.Etale) : Prop :=
  Nonempty (F.over U ≅ ((constantSheaf X.smallEtaleTopology A).obj V).over U)

/-- A sheaf `F` on the small étale site of `X` is *locally constant* if there is a
jointly surjective family of étale maps `Uᵢ ⟶ X` such that the restriction of `F` to
each `Uᵢ` is constant. Applies to sheaves of sets (`A = Type u`), abelian groups
(`A = Ab`), modules, etc. -/
def IsLocallyConstantSheaf (F : Sheaf X.smallEtaleTopology A) : Prop :=
  ∃ (ι : Type u) (U : ι → X.Etale) (V : ι → A),
    (⋃ i, Set.range (U i).hom : Set X) = Set.univ ∧
    ∀ i, IsConstantSheafOn F (V i) (U i)

end LocallyConstant

section FiniteLocallyConstant

variable {A : Type u'} [Category.{v} A]
  {FA : A → A → Type*} {CD : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CD X) (CD Y)] [ConcreteCategory A FA]
  [HasWeakSheafify X.smallEtaleTopology A]

/-- A sheaf `F` on the small étale site of `X` with values in a concrete category is
*finite locally constant* if there is a jointly surjective family of étale maps `Uᵢ ⟶ X`
trivializing `F` with finite objects as values. For sheaves of sets, equivalently (not
proved here), `F` is representable by a scheme finite étale over `X`. -/
def IsFiniteLocallyConstantSheaf (F : Sheaf X.smallEtaleTopology A) : Prop :=
  ∃ (ι : Type u) (U : ι → X.Etale) (V : ι → A),
    (⋃ i, Set.range (U i).hom : Set X) = Set.univ ∧
    (∀ i, Finite (ToType (V i))) ∧
    ∀ i, IsConstantSheafOn F (V i) (U i)

theorem IsFiniteLocallyConstantSheaf.isLocallyConstantSheaf
    {F : Sheaf X.smallEtaleTopology A} (hF : IsFiniteLocallyConstantSheaf F) :
    IsLocallyConstantSheaf F := by
  obtain ⟨ι, U, V, hcover, -, htriv⟩ := hF
  exact ⟨ι, U, V, hcover, htriv⟩

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

/-- A sheaf `F` on the small étale site of `X` with values in a concrete category is
*constructible* if there is a stratification of `X` such that the pullback of `F` to each
stratum is finite locally constant.

The stratification records a choice of scheme structure on each stratum via the immersion
`S.immersion i : S.domain i ⟶ X`; by topological invariance of the small étale site the
condition does not depend on this choice.

The pullback `Etale.upperStar` needs left Kan extensions along base change by the
immersions and a sheafification functor for the small étale sites of the strata; both are
assumed as instance hypotheses inside the quantification. The Kan extensions always exist
mathematically but are not known to exist with current mathlib (see the module
implementation notes); the sheafification hypothesis is discharged by mathlib's
`HasSheafify` instance for `smallEtaleTopology` whenever `A` is a suitable concrete
category.

For `X` quasi-compact and quasi-separated this global definition agrees with the
affine-local one of [Stacks 03RW]. In the `ℓ`-adic formalism it is applied with
`A = ModuleCat Λ` for the finite ring `Λ = ℤ/ℓⁿℤ`. -/
def IsConstructibleSheaf (F : Sheaf X.smallEtaleTopology A) : Prop :=
  ∃ S : Stratification X, ∀ (i : Fin S.n)
    [∀ P : X.Etaleᵒᵖ ⥤ A,
        (MorphismProperty.Over.pullback @Etale ⊤ (S.immersion i)).op.HasLeftKanExtension P]
      [HasWeakSheafify (S.domain i).smallEtaleTopology A],
        IsFiniteLocallyConstantSheaf ((Etale.upperStar A (S.immersion i)).obj F)

end Constructible

end Scheme

end AlgebraicGeometry
