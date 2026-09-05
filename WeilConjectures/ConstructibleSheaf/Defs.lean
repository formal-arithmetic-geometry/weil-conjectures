/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Sites.LocalSite
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SixFunctors.UpperLowerStar.Defs
public import WeilConjectures.Topology.Stratification

/-!
# Constructible sheaves on the small sites of schemes

Let `P` and `Q` be morphism properties of schemes with `Q ≤ P`, let `X` be a scheme and
let `F` be a sheaf on the small `Q`-site of `P`-schemes over `X`
(`AlgebraicGeometry.Scheme.smallGrothendieckTopology`) with values in a category `A`.
Following [SGA 4, Exp. IX, §2] we define:

- `F` is *constant* if it is isomorphic to the sheafification of a constant presheaf;
  this is mathlib's `CategoryTheory.Sheaf.IsConstant`.
- `F` is *locally constant* (`IsLocallyConstantSheaf`) if there is a `Q`-cover of `X`
  (a jointly surjective family of `Q`-maps `Uᵢ ⟶ X`, a cover in
  `Scheme.precoverage Q`) such that the restriction of `F` to each `Uᵢ` is constant;
  the trivializing data is packaged in `LocallyConstantDatum`. A constant sheaf is
  locally constant, trivialized by the identity cover
  (`CategoryTheory.Sheaf.IsConstant.isLocallyConstantSheaf`).
- `F` is *finite* (`IsFiniteSheaf`) if the stalk of `F` at every geometric point of `X`
  is finite. Which point of the site a geometric point determines is part of the input,
  recorded by the class `HasGeometricPoints`; for the étale site it is
  `Scheme.pointSmallEtale`.
- `F` is *finite locally constant* (`IsFiniteLocallyConstantSheaf`) if it is locally
  constant and finite.
- `F` is *constructible* (`IsConstructibleSheaf`) if there is a stratification of `X`
  (`Scheme.Stratification`: a stratification of the underlying topological space of `X` —
  a finite partition into locally closed subsets, `Topology.Stratification`, following
  [Stacks 09XZ] — together with schemes immersed in `X` realizing the strata) such that
  the pullback of `F` to each stratum is finite locally constant.

All four predicates are `Prop`-valued classes. The étale and pro-étale specializations are
in `WeilConjectures.ConstructibleSheaf.Etale` and
`WeilConjectures.ConstructibleSheaf.ProEt`; this file is stated once for `P` and `Q`, in
the same way as the pushforward and pullback of
`WeilConjectures.SixFunctors.UpperLowerStar.Defs`.

Following the convention of the `SixFunctors` folder, the coefficient category `A` is a
Grothendieck abelian category with `Hom`-types in the universe `u + 1`, one above the
universe `u` of the base schemes; this is what supplies the sheafification used to
restrict a sheaf to a member of a cover, see the implementation notes. The notions
involving finiteness require `A` to be moreover concrete, finiteness referring to the
underlying type `CategoryTheory.ToType`. This covers sheaves of abelian groups
(`A = Ab.{u + 1}`) and of `Λ`-modules (`A = ModuleCat.{u + 1} Λ`), the case relevant for
the `ℓ`-adic formalism, where `Λ` is the finite ring `Λₙ = ℤ/ℓⁿℤ`.

To restrict `F` to a `Q`-morphism `U ⟶ X` we use the localized site: `F.over U` is the
sheaf induced by `F` on the localization of the small site at `U`. To restrict `F` to a
stratum we use the pullback `CategoryTheory.GrothendieckTopology.upperStar` of
`WeilConjectures.SixFunctors.UpperLowerStar.Defs` along an immersion, the left adjoint of
the pushforward `CategoryTheory.GrothendieckTopology.lowerStar`.

## Implementation notes

- The pullback `upperStar` is defined by left Kan extension along base change followed by
  sheafification, and the Kan extensions in question are not known to exist for an
  arbitrary `f` with current mathlib. Mathematically they always exist; they are provided
  by the sorried instance
  `CategoryTheory.GrothendieckTopology.hasLeftKanExtension_op_overPullback` of
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension`.
- Sheafification is likewise not assumed here. Restricting a sheaf to a member of a cover
  needs it for the *localizations* of the small sites, and for a Grothendieck abelian `A`
  these are supplied by the sorried instance
  `CategoryTheory.GrothendieckTopology.hasSheafify_essentiallySmall` of
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`, a slice of an
  essentially small site being again essentially small. This replaces what used to be a
  `HasWeakSheafify` hypothesis quantified over all schemes and all `U`, the quantification
  being forced by the existential quantifier over stratifications.
- Similarly, `CategoryTheory.Sheaf.IsConstant.isLocallyConstantSheaf` assumes the
  existence of the right Kan extensions along `(Over.forget U).op` needed to compare
  sheafification on the small site with sheafification on its localizations.
-/

@[expose] public section

universe u u'

open CategoryTheory Limits Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

section PullbackFunctor

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  (P Q : MorphismProperty Scheme.{u})
  [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
  [Q.IsMultiplicative] [Q.IsStableUnderBaseChange] (hQP : Q ≤ P)

/-- The pullback of sheaves on the small sites along `f : X ⟶ Y` sends constant sheaves to
constant sheaves: `constantSheaf ⋙ f^*` and `constantSheaf` are both left adjoint to
global sections of the pushforward, since base change preserves the terminal object of the
small site (`X ×_Y Y ≅ X`). -/
def upperStarConstantSheafIso (f : X ⟶ Y) :
    constantSheaf (Y.smallGrothendieckTopology Q (Q := P)) A ⋙
        GrothendieckTopology.upperStar A P Q f ≅
      constantSheaf (X.smallGrothendieckTopology Q (Q := P)) A :=
  Adjunction.leftAdjointUniq
    (((constantSheafAdj (Y.smallGrothendieckTopology Q (Q := P)) A terminalIsTerminal).comp
        (GrothendieckTopology.upperStarLowerStarAdjunction A P Q hQP f)).ofNatIsoRight
      (NatIso.ofComponents
        (F := GrothendieckTopology.lowerStar A P Q hQP f ⋙
          (sheafSections (Y.smallGrothendieckTopology Q (Q := P)) A).obj
            (op (⊤_ (P.Over ⊤ Y))))
        (G := (sheafSections (X.smallGrothendieckTopology Q (Q := P)) A).obj
          (op (⊤_ (P.Over ⊤ X))))
        (fun H ↦ H.obj.mapIso
          (PreservesTerminal.iso (MorphismProperty.Over.pullback P ⊤ f)).op.symm)
        (fun α ↦ (α.hom.naturality _).symm)))
    (constantSheafAdj (X.smallGrothendieckTopology Q (Q := P)) A terminalIsTerminal)

end PullbackFunctor

section LocallyConstant

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  (P Q : MorphismProperty Scheme.{u})
  [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]

/-- The object of the small `Q`-site of `P`-schemes over `X` given by a member of a
`Q`-cover of `X`. -/
abbrev Cover.toOverProp (hQP : Q ≤ P) (𝒰 : Cover.{u} (precoverage Q) X) (i : 𝒰.I₀) :
    P.Over ⊤ X :=
  MorphismProperty.Over.mk ⊤ (𝒰.f i) (hQP _ (𝒰.map_prop i))

/-- The datum of a trivialization of a sheaf `F` on the small `Q`-site of `P`-schemes over
`X`: a `Q`-cover of `X` — a jointly surjective family of `Q`-maps, a cover in
`Scheme.precoverage Q` — such that the restriction of `F` to the site localized at each
member of the cover is constant in the sense of `CategoryTheory.Sheaf.IsConstant`. `F` is
locally constant if such a datum exists, see `IsLocallyConstantSheaf`. -/
structure LocallyConstantDatum (hQP : Q ≤ P)
    (F : Sheaf (X.smallGrothendieckTopology Q (Q := P)) A) where
  /-- The trivializing `Q`-cover. -/
  cover : Cover.{u} (precoverage Q) X
  /-- The restriction of `F` to the site localized at each member of the cover is
  constant. -/
  isConstant (i : cover.I₀) : (F.over (Cover.toOverProp P Q hQP cover i)).IsConstant
    ((X.smallGrothendieckTopology Q (Q := P)).over (Cover.toOverProp P Q hQP cover i))

/-- A sheaf `F` on the small `Q`-site of `P`-schemes over `X` is *locally constant* if
there is a `Q`-cover of `X` trivializing `F`, i.e. a `LocallyConstantDatum`. Applies to
sheaves of abelian groups (`A = Ab.{u + 1}`), of `Λ`-modules (`A = ModuleCat.{u + 1} Λ`),
etc. -/
class IsLocallyConstantSheaf (hQP : Q ≤ P)
    (F : Sheaf (X.smallGrothendieckTopology Q (Q := P)) A) : Prop where
  nonempty_locallyConstantDatum : Nonempty (LocallyConstantDatum P Q hQP F)

/-- A constant sheaf on a small site is locally constant, trivialized by the identity
cover. The right Kan extension hypothesis compares sheafification on the small site with
sheafification on its localizations; it always holds mathematically, see the module
implementation notes. -/
lemma _root_.CategoryTheory.Sheaf.IsConstant.isLocallyConstantSheaf (hQP : Q ≤ P)
    [(precoverage Q).HasIsos]
    [∀ (U : P.Over ⊤ X) (R : (Over U)ᵒᵖ ⥤ A), (Over.forget U).op.HasPointwiseRightKanExtension R]
    {F : Sheaf (X.smallGrothendieckTopology Q (Q := P)) A}
    (h : F.IsConstant (X.smallGrothendieckTopology Q (Q := P))) :
    IsLocallyConstantSheaf P Q hQP F :=
  have := h
  ⟨⟨⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _), fun _ ↦ F.isConstant_over _⟩⟩⟩

end LocallyConstant

section GeometricPoints

variable (P Q : MorphismProperty Scheme.{u})
  [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]

/-- The data of a point of the small `Q`-site of `P`-schemes over `X` attached to every
geometric point `Spec Ω ⟶ X` of every scheme `X`, with `Ω` a separably closed field.

For the small étale site this is `AlgebraicGeometry.Scheme.pointSmallEtale`: a geometric
point defines a point of the site whose fiber functor is
`V ↦ Hom_X(Spec Ω, V)`, and the stalk of a sheaf at the geometric point is the fiber of
the sheaf at that point of the site. Finiteness of a sheaf (`IsFiniteSheaf`) is finiteness
of all these stalks, so it depends on this choice. -/
class HasGeometricPoints where
  /-- The point of the small site attached to a geometric point of `X`. -/
  point {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    (X.smallGrothendieckTopology Q (Q := P)).Point

/-- The point of the small `Q`-site of `P`-schemes over `X` attached to a geometric point
`s : Spec Ω ⟶ X`, with `P` and `Q` explicit. -/
abbrev geometricPoint [HasGeometricPoints P Q] {X : Scheme.{u}} {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    (X.smallGrothendieckTopology Q (Q := P)).Point :=
  HasGeometricPoints.point (P := P) (Q := Q) s

end GeometricPoints

section FiniteSheaf

variable {A : Type u'} [Category.{u + 1} A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasColimitsOfSize.{u, u} A]
  (P Q : MorphismProperty Scheme.{u})
  [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
  [HasGeometricPoints P Q]

/-- A sheaf `F` on the small `Q`-site of `P`-schemes over `X` with values in a concrete
category is *finite* if the stalk of `F` at every geometric point of `X` is finite. A
geometric point `Spec Ω ⟶ X`, with `Ω` a separably closed field, induces a point of the
site via `HasGeometricPoints`, and the stalk of `F` is its fiber
`CategoryTheory.GrothendieckTopology.Point.sheafFiber` at this point. -/
class IsFiniteSheaf (F : Sheaf (X.smallGrothendieckTopology Q (Q := P)) A) : Prop where
  finite_sheafFiber (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    Finite (ToType ((geometricPoint P Q s).sheafFiber.obj F))

end FiniteSheaf

section FiniteLocallyConstant

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  (P Q : MorphismProperty Scheme.{u})
  [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
  [HasGeometricPoints P Q]

/-- A sheaf `F` on the small `Q`-site of `P`-schemes over `X` with values in a concrete
category is *finite locally constant* if it is locally constant and finite. For sheaves of
sets on the étale site, equivalently (not proved here), `F` is representable by a scheme
finite étale over `X`. -/
class IsFiniteLocallyConstantSheaf (hQP : Q ≤ P)
    (F : Sheaf (X.smallGrothendieckTopology Q (Q := P)) A) : Prop
    extends IsLocallyConstantSheaf P Q hQP F, IsFiniteSheaf P Q F

end FiniteLocallyConstant

section Stratification

/-- A *stratification* of a scheme `X`: a stratification of the underlying topological
space of `X` (`Topology.Stratification`: a finite partition into locally closed subsets
following [Stacks 09XZ]) together with, for each stratum, a scheme immersed in `X` with
set-theoretic image the stratum. A sheaf on a small site of `X` is constructible if its
pullbacks to the strata of some stratification are finite locally constant, see
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

variable {A : Type u'} [Category.{u + 1} A] [Abelian A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [IsGrothendieckAbelian.{u + 1} A]
  (P Q : MorphismProperty Scheme.{u})
  [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
  [Q.IsMultiplicative] [Q.IsStableUnderBaseChange]
  [HasGeometricPoints P Q]

/-- A sheaf `F` on the small `Q`-site of `P`-schemes over `X` with values in a concrete
category is *constructible* if there is a stratification of `X` such that the pullback of
`F` to each stratum is finite locally constant.

The stratification records a choice of scheme structure on each stratum via the immersion
`S.immersion i : S.domain i ⟶ X`; by topological invariance of the small étale site the
condition does not depend on this choice.

The left Kan extensions along base change needed by the pullback `upperStar` are provided
by the sorried instance
`CategoryTheory.GrothendieckTopology.hasLeftKanExtension_op_overPullback` of
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension`.

For `X` quasi-compact and quasi-separated and `P = Q = @Etale`, this global definition
agrees with the affine-local one of [Stacks 03RW]. In the `ℓ`-adic formalism it is applied
with `A = ModuleCat Λ` for the finite ring `Λ = ℤ/ℓⁿℤ`. -/
class IsConstructibleSheaf (hQP : Q ≤ P)
    (F : Sheaf (X.smallGrothendieckTopology Q (Q := P)) A) : Prop where
  exists_stratification : ∃ S : Stratification X, ∀ i : Fin S.n,
    IsFiniteLocallyConstantSheaf P Q hQP
      ((GrothendieckTopology.upperStar A P Q (S.immersion i)).obj F)

end Constructible

end Scheme

end AlgebraicGeometry
