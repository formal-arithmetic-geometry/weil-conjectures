/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib

/-!
# Constructible sheaves on the small étale site

Let `X` be a scheme and let `F` be a sheaf on the small étale site of `X` (see
`AlgebraicGeometry.Scheme.smallEtaleTopology`). Following [SGA 4, Exp. IX, §2] we define:

- `F` is *constant* if it is isomorphic to the sheafification of a constant presheaf;
  this is mathlib's `CategoryTheory.Sheaf.IsConstant`.
- `F` is *locally constant* (`IsLocallyConstantSheaf`) if there is a jointly surjective
  family of étale maps `Uᵢ ⟶ X` such that the restriction of `F` to each `Uᵢ` is
  isomorphic to the restriction of a constant sheaf.
- `F` is *finite locally constant* (`IsFiniteLocallyConstantSheaf`) if moreover the
  values of the trivializing constant sheaves are finite sets.
- `F` is *constructible* (`IsConstructibleSheaf`) if `X` admits a finite partition into
  constructible locally closed subsets such that the pullback of `F` to each stratum is
  finite locally constant.

To restrict `F` to an étale `U ⟶ X` we use the localized site: `F.over U` is the sheaf
induced by `F` on the localization of the small étale site at `U`, which is equivalent to
the small étale site of `U`. To restrict `F` to a stratum we use the pullback
`f.etalePullback` along an immersion, defined below as the left adjoint of the
pushforward `f.etalePushforward`.
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
étale `V ⟶ Y` to the projection `V ×_Y X ⟶ X`. -/
def Hom.etaleBaseChange (f : X ⟶ Y) : Y.Etale ⥤ X.Etale :=
  MorphismProperty.Over.pullback @Etale ⊤ f

instance (f : X ⟶ Y) : PreservesFiniteLimits f.etaleBaseChange :=
  inferInstanceAs <| PreservesFiniteLimits (MorphismProperty.Over.pullback @Etale ⊤ f)

instance : HasFiniteLimits Y.Etale :=
  inferInstanceAs <| HasFiniteLimits (MorphismProperty.Over @Etale ⊤ Y)

instance (f : X ⟶ Y) : RepresentablyFlat f.etaleBaseChange :=
  flat_of_preservesFiniteLimits _

/-- The set-theoretic image of the base change of a `V`-morphism `g : Z ⟶ V` of schemes
étale over `Y` along `f : X ⟶ Y` is the preimage of the image of `g` under the
projection `V ×_Y X ⟶ V`. -/
lemma range_etaleBaseChange_map_left (f : X ⟶ Y) {Z V : Y.Etale} (g : Z ⟶ V) :
    Set.range (f.etaleBaseChange.map g).left =
      pullback.fst V.hom f ⁻¹' Set.range g.left := by
  have h : (f.etaleBaseChange.map g).left =
      pullback.map Z.hom f V.hom f g.left (𝟙 X) (𝟙 Y)
        ((Category.comp_id _).trans (MorphismProperty.Over.w g).symm)
        ((Category.comp_id f).trans (Category.id_comp f).symm) := by
    apply pullback.hom_ext
    · simp only [Hom.etaleBaseChange, MorphismProperty.Over.pullback_map_left,
        pullback.lift_fst]
    · simp only [Hom.etaleBaseChange, MorphismProperty.Over.pullback_map_left,
        pullback.lift_snd, Category.comp_id]
  rw [h]
  haveI : Mono (𝟙 Y) := ⟨fun g h w ↦ by simpa using w⟩
  exact (Pullback.range_map Z.hom f V.hom f g.left (𝟙 X) (𝟙 Y) _ _).trans (by simp)

/-- Every point of `V` lies in the image of one of the arrows of an étale covering sieve
of `V`. -/
lemma exists_range_of_mem_smallEtaleTopology {V : Y.Etale} {S : Sieve V}
    (hS : S ∈ Y.smallEtaleTopology V) (v : V.left) :
    ∃ (Z : Y.Etale) (g : Z ⟶ V), S.arrows g ∧ v ∈ Set.range g.left := by
  obtain ⟨𝒰, h𝒰, hP, hle⟩ := (mem_smallGrothendieckTopology _ _).1 hS
  letI := h𝒰
  obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq v
  exact ⟨(𝒰.X i).asOverProp _ (hP i), (𝒰.f i).asOverProp _,
    hle _ _ (Presieve.ofArrows.mk i), y, rfl⟩

/-- Base change along `f : X ⟶ Y` sends étale covering sieves of `Y` to étale covering
sieves of `X`: étale covers are jointly surjective families, and joint surjectivity is
stable under base change. -/
lemma coverPreserving_etaleBaseChange (f : X ⟶ Y) :
    CoverPreserving Y.smallEtaleTopology X.smallEtaleTopology f.etaleBaseChange where
  cover_preserve {V S} hS := by
    refine X.smallEtaleTopology.superset_covering
      (Sieve.generate_le_iff _ _ |>.2 ?_)
      ((ofArrows_mem_smallEtaleTopology_iff
        (fun i : Σ Z : Y.Etale, { g : Z ⟶ V // S.arrows g } ↦
          f.etaleBaseChange.map i.2.1)).2 ?_)
    · rintro W h ⟨i⟩
      exact ⟨i.1, i.2.1, 𝟙 _, i.2.2, by simp⟩
    · rw [Set.eq_univ_iff_forall]
      intro pt
      obtain ⟨Z, g, hg, hv⟩ := exists_range_of_mem_smallEtaleTopology hS
        (pullback.fst V.hom f pt)
      exact Set.mem_iUnion.2 ⟨⟨Z, g, hg⟩, by
        rw [range_etaleBaseChange_map_left]; exact hv⟩

/-- Base change along `f : X ⟶ Y` is a continuous functor between the small étale
sites: it preserves covers and is representably flat. -/
instance (f : X ⟶ Y) :
    f.etaleBaseChange.IsContinuous Y.smallEtaleTopology X.smallEtaleTopology :=
  Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfFlat X.smallEtaleTopology f.etaleBaseChange)
    (coverPreserving_etaleBaseChange f)

variable (A : Type*) [Category.{v} A]

/-- The pushforward `f_*` of étale sheaves along a morphism `f : X ⟶ Y`, given on
sections by `(f_* F)(V) = F(V ×_Y X)` for `V` étale over `Y`. -/
def Hom.etalePushforward (f : X ⟶ Y) :
    Sheaf X.smallEtaleTopology A ⥤ Sheaf Y.smallEtaleTopology A :=
  f.etaleBaseChange.sheafPushforwardContinuous A
    Y.smallEtaleTopology X.smallEtaleTopology

end Functoriality

section AdjointExistence

/-- The restriction of the base change functor along `f : X ⟶ Y` to the small affine
étale site of `Y` is a continuous functor to the small étale site of `X`, as a
composition of two continuous functors. -/
instance (f : X ⟶ Y) :
    (AffineEtale.Spec Y ⋙ f.etaleBaseChange).IsContinuous
      (AffineEtale.topology Y) X.smallEtaleTopology :=
  Functor.isContinuous_comp _ _ _ Y.smallEtaleTopology _

/-- Left Kan extensions along the affine base change functor exist: the costructured
arrow categories are essentially small because the small affine étale site is, so the
pointwise Kan extension colimits exist. This is the place where essential smallness of
the affine étale site is used; the analogous statement for the base change functor on
the full small étale site is not accessible with current mathlib. -/
instance (f : X ⟶ Y) {A : Type u'} [Category.{u} A] [HasColimits A]
    (F : (Y.AffineEtale)ᵒᵖ ⥤ A) :
    (AffineEtale.Spec Y ⋙ f.etaleBaseChange).op.HasLeftKanExtension F := by
  haveI : ∀ V : (X.Etale)ᵒᵖ, HasColimitsOfShape
      (CostructuredArrow (AffineEtale.Spec Y ⋙ f.etaleBaseChange).op V) A :=
    fun V ↦ hasColimitsOfShape_of_essentiallySmall _ _
  infer_instance

variable {A : Type u'} [Category.{u} A]
  {FA : A → A → Type*} {CD : A → Type u}
  [∀ X Y, FunLike (FA X Y) (CD X) (CD Y)] [ConcreteCategory.{u} A FA]
  [PreservesLimits (CategoryTheory.forget A)] [HasColimits A] [HasLimits A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]

/-- The pushforward of étale sheaves admits a left adjoint, the inverse image functor.

The pushforward composed with the restriction equivalence to the small affine étale
site of `Y` is the pushforward along the affine base change functor
`Y.AffineEtale ⥤ X.Etale`, whose source is essentially small; the latter pushforward
has a left adjoint given by sheafified left Kan extension, and being a right adjoint
descends along the equivalence. -/
instance (f : X ⟶ Y) : (f.etalePushforward A).IsRightAdjoint := by
  rw [← Functor.isRightAdjoint_comp_iff_left (f.etalePushforward A)
    ((AffineEtale.Spec Y).sheafPushforwardContinuous A
      (AffineEtale.topology Y) Y.smallEtaleTopology)]
  exact inferInstanceAs
    ((AffineEtale.Spec Y ⋙ f.etaleBaseChange).sheafPushforwardContinuous A
      (AffineEtale.topology Y) X.smallEtaleTopology).IsRightAdjoint

end AdjointExistence

section PullbackFunctor

variable (A : Type*) [Category.{v} A]

/-- The pullback (inverse image) `f⁻¹` of étale sheaves along a morphism `f : X ⟶ Y`,
defined as the left adjoint of the pushforward `f.etalePushforward`. The adjoint exists
for sheaves valued in suitable concrete categories (`Type u`, `Ab`, modules, …), see the
instance above. -/
def Hom.etalePullback (f : X ⟶ Y) [(f.etalePushforward A).IsRightAdjoint] :
    Sheaf Y.smallEtaleTopology A ⥤ Sheaf X.smallEtaleTopology A :=
  (f.etalePushforward A).leftAdjoint

/-- The pullback/pushforward adjunction `f⁻¹ ⊣ f_*` for étale sheaves. -/
def Hom.etaleAdjunction (f : X ⟶ Y) [(f.etalePushforward A).IsRightAdjoint] :
    f.etalePullback A ⊣ f.etalePushforward A :=
  Adjunction.ofIsRightAdjoint (f.etalePushforward A)

/-- The pullback of étale sheaves along `f : X ⟶ Y` sends constant sheaves to constant
sheaves: `constantSheaf ⋙ f⁻¹` and `constantSheaf` are both left adjoint to global
sections of the pushforward, since base change preserves the terminal object of the
small étale site (`X ×_Y Y ≅ X`). -/
def etalePullbackConstantSheafIso (f : X ⟶ Y)
    [HasWeakSheafify Y.smallEtaleTopology A] [HasWeakSheafify X.smallEtaleTopology A]
    [(f.etalePushforward A).IsRightAdjoint] :
    constantSheaf Y.smallEtaleTopology A ⋙ f.etalePullback A ≅
      constantSheaf X.smallEtaleTopology A :=
  Adjunction.leftAdjointUniq
    (((constantSheafAdj Y.smallEtaleTopology A terminalIsTerminal).comp
        (f.etaleAdjunction A)).ofNatIsoRight
      (NatIso.ofComponents
        (F := f.etalePushforward A ⋙
          (sheafSections Y.smallEtaleTopology A).obj (op (⊤_ Y.Etale)))
        (G := (sheafSections X.smallEtaleTopology A).obj (op (⊤_ X.Etale)))
        (fun H ↦ H.obj.mapIso (PreservesTerminal.iso f.etaleBaseChange).op.symm)
        (fun α ↦ (α.hom.naturality _).symm)))
    (constantSheafAdj X.smallEtaleTopology A terminalIsTerminal)

end PullbackFunctor

/-- The structure morphism of an object of the small étale site of `X`, with its type
stated in the category of schemes (rather than of the underlying comma category), so that
it can be applied to points. -/
abbrev Etale.structMap (U : X.Etale) : U.left ⟶ X := U.hom

section LocallyConstant

variable {A : Type*} [Category.{v} A] [HasWeakSheafify X.smallEtaleTopology A]

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
    (⋃ i, Set.range (U i).structMap) = Set.univ ∧
    ∀ i, IsConstantSheafOn F (V i) (U i)

/-- A sheaf of sets `F` on the small étale site of `X` is *finite locally constant* if
there is a jointly surjective family of étale maps `Uᵢ ⟶ X` trivializing `F` with finite
sets as values. Equivalently (not proved here), `F` is representable by a scheme finite
étale over `X`. -/
def IsFiniteLocallyConstantSheaf (F : Sheaf X.smallEtaleTopology (Type u)) : Prop :=
  ∃ (ι : Type u) (U : ι → X.Etale) (V : ι → Type u),
    (⋃ i, Set.range (U i).structMap) = Set.univ ∧
    (∀ i, Finite (V i)) ∧
    ∀ i, IsConstantSheafOn F (V i) (U i)

theorem IsFiniteLocallyConstantSheaf.isLocallyConstantSheaf
    {F : Sheaf X.smallEtaleTopology (Type u)} (hF : IsFiniteLocallyConstantSheaf F) :
    IsLocallyConstantSheaf F := by
  obtain ⟨ι, U, V, hcover, -, htriv⟩ := hF
  exact ⟨ι, U, V, hcover, htriv⟩

end LocallyConstant

section Constructible

/-- A sheaf of sets `F` on the small étale site of `X` is *constructible* if `X` admits
a finite partition into constructible locally closed subsets `Zᵢ` such that the pullback
of `F` to each stratum is finite locally constant.

The restriction of `F` to the stratum `Zᵢ` is expressed by quantifying over all
immersions `g : T ⟶ X` with set-theoretic image `Zᵢ`; by topological invariance of the
small étale site this does not depend on the chosen scheme structure on `Zᵢ`.

For `X` quasi-compact and quasi-separated this global definition agrees with the
affine-local one of [Stacks 03RW]. -/
def IsConstructibleSheaf (F : Sheaf X.smallEtaleTopology (Type u)) : Prop :=
  ∃ (n : ℕ) (Z : Fin n → Set X),
    (⋃ i, Z i) = Set.univ ∧
    Pairwise (Function.onFun Disjoint Z) ∧
    (∀ i, IsLocallyClosed (Z i)) ∧
    (∀ i, Topology.IsConstructible (Z i)) ∧
    ∀ (i : Fin n) (T : Scheme.{u}) (g : T ⟶ X), IsImmersion g →
      Set.range g.base = Z i →
      IsFiniteLocallyConstantSheaf ((g.etalePullback (Type u)).obj F)

end Constructible

section ModuleSheaf

/-! ### Constructible sheaves of `Λ`-modules

The definitions of the previous sections, adapted to sheaves with values in the category
of modules over a ring `Λ`. In the `ℓ`-adic formalism, `Λ` is the finite ring
`Λₙ = ℤ/ℓⁿℤ`, where `ℓ` is a prime; for schemes in characteristic `p > 0` one takes
`ℓ` different from (hence coprime to) `p`. -/

variable {Λ : Type u} [Ring Λ]

/-- A sheaf of `Λ`-modules on the small étale site of `X` is *finite locally constant*
if there is a jointly surjective family of étale maps `Uᵢ ⟶ X` on which it becomes
constant with values finite `Λ`-modules. -/
def IsFiniteLocallyConstantModuleSheaf
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) : Prop :=
  ∃ (ι : Type u) (U : ι → X.Etale) (V : ι → ModuleCat.{u} Λ),
    (⋃ i, Set.range (U i).structMap) = Set.univ ∧
    (∀ i, Finite (V i)) ∧
    ∀ i, IsConstantSheafOn F (V i) (U i)

/-- A sheaf of `Λ`-modules on the small étale site of `X` is *constructible* if `X`
admits a finite partition into constructible locally closed subsets `Zᵢ` such that the
pullback of `F` to each stratum is a finite locally constant sheaf of `Λ`-modules;
compare `IsConstructibleSheaf`. -/
def IsConstructibleModuleSheaf (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) : Prop :=
  ∃ (m : ℕ) (Z : Fin m → Set X),
    (⋃ i, Z i) = Set.univ ∧
    Pairwise (Function.onFun Disjoint Z) ∧
    (∀ i, IsLocallyClosed (Z i)) ∧
    (∀ i, Topology.IsConstructible (Z i)) ∧
    ∀ (i : Fin m) (T : Scheme.{u}) (g : T ⟶ X), IsImmersion g →
      Set.range g.base = Z i →
      IsFiniteLocallyConstantModuleSheaf ((g.etalePullback (ModuleCat.{u} Λ)).obj F)

end ModuleSheaf

end Scheme

end AlgebraicGeometry
