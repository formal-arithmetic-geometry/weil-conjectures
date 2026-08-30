/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLimitsOfSize
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.SixFunctors.UpperLowerStar.Etale

/-!

# Stalks of a pullback, and of a pushforward along a closed immersion, of étale sheaves

For a morphism of schemes `f : X ⟶ Y`, pulling an étale sheaf back to `X` does not change
its stalks: the stalk of `f^* F` at a geometric point `s : Spec Ω ⟶ X` is the stalk of `F`
at the image point `s ≫ f`.

The pullback `(f)^*[A]` of `WeilConjectures.SixFunctors.UpperLowerStar.Etale` is the sheaf
pullback along base change `f.Etale`. Mathlib's
`CategoryTheory.GrothendieckTopology.Point.sheafFiberComapIso` computes the fibre functor on
sheaves of the point `Point.comap` of a representably flat, cover preserving functor as the
sheaf pullback followed by the fibre functor of the original point; and by
`AlgebraicGeometry.Scheme.pointSmallEtaleComapIso` the point obtained from `s` along base
change is the geometric point `s ≫ f`.

Dually, pushing forward along a *closed immersion* `i : Z ⟶ X` does not change stalks at
points of `Z`: the stalk of `i_* H` at `s ≫ i` is the stalk of `H` at `s`, for a geometric
point `s : Spec Ω ⟶ Z`. Here `(i)_*[A]` is restriction along base change `i.Etale`, so both
stalks are filtered colimits over categories of pointed étale neighbourhoods, and the
comparison is the initiality of
`AlgebraicGeometry.Scheme.pointSmallEtaleElementsBaseChange`, which sends a pointed étale
neighbourhood `(V, v)` of `s ≫ i` in `X` to `(V ×_X Z, (v, s))`.

## Main results

- `AlgebraicGeometry.Etale.upperStarCompSheafFiberIso`: the natural isomorphism
  `(f)^*[A] ⋙ (pointSmallEtale s).sheafFiber ≅ (pointSmallEtale (s ≫ f)).sheafFiber`,
  that is, `(f^* F)_s ≅ F_(s ≫ f)`, naturally in the sheaf `F`.
- `AlgebraicGeometry.Etale.upperStarCompUliftSheafFiberIso`: the same isomorphism for the
  universe-lifted points `CategoryTheory.GrothendieckTopology.Point.ulift`.
- `AlgebraicGeometry.Scheme.initial_pointSmallEtaleElementsBaseChange`: for a closed
  immersion `i`, base change is initial on pointed étale neighbourhoods.
- `AlgebraicGeometry.Etale.lowerStarCompSheafFiberIso` and
  `AlgebraicGeometry.Etale.lowerStarCompUliftSheafFiberIso`: the natural isomorphism
  `(i)_*[A] ⋙ (pointSmallEtale (s ≫ i)).sheafFiber ≅ (pointSmallEtale s).sheafFiber`,
  that is, `(i_* H)_(s ≫ i) ≅ H_s`, and its universe-lifted form.

## Implementation notes

Base change occurs under its two interchangeable names: `AlgebraicGeometry.Etale.upperStar`
and `AlgebraicGeometry.Etale.lowerStar` are defined along
`MorphismProperty.Over.pullback @Etale ⊤ f`, whereas the point API is applied to the
definitionally equal `AlgebraicGeometry.Scheme.Hom.Etale f`, whose stated type
`Y.Etale ⥤ X.Etale` is the one the geometric points of `X` and `Y` come with. Both names
appear below, each where its instances are available.

Initiality is obtained from `CategoryTheory.Functor.initial_of_exists_of_isCofiltered`, so
no connectedness argument is written by hand: the categories of elements of the fibre
functors of points are cofiltered, and only the two hypotheses of that criterion are proved
here. The first is `AlgebraicGeometry.Etale.exists_pullback_hom_of_isClosedImmersion`, the
local lifting of étale morphisms along a closed immersion. The second combines the open
agreement locus of `AlgebraicGeometry.FormallyUnramified.eqLocus` with the fact that
`V ×_X Z ⟶ V` is a closed immersion, hence inducing on the underlying spaces, so that the
agreement locus is the trace of an open of `V`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section BaseChange

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ X)

/-- All left Kan extensions of `A`-valued presheaves along the opposite of base change
`f.Etale` exist. This is the `P = @Etale` case of
`CategoryTheory.GrothendieckTopology.hasLeftKanExtension_op_overPullback`, restated for
`AlgebraicGeometry.Scheme.Hom.Etale`; it is what makes the sheaf pullback along `f.Etale`
available, hence also the fibre functor on sheaves of the point
`(pointSmallEtale s).comap f.Etale _`. -/
instance Etale.hasLeftKanExtension_op_etale (G : Y.Etaleᵒᵖ ⥤ A) :
    f.Etale.op.HasLeftKanExtension G :=
  GrothendieckTopology.hasLeftKanExtension_op_overPullback A @Etale f G

/-- The stalk of a pullback of étale sheaves is the stalk at the image point: for a morphism
of schemes `f : X ⟶ Y` and a geometric point `s : Spec Ω ⟶ X`, the stalk of `f^* F` at `s`
is the stalk of `F` at `s ≫ f`, naturally in the sheaf `F`.

The three steps are the comparison
`CategoryTheory.Functor.sheafPullbackConstruction.sheafPullbackIso` between `(f)^*[A]` and
the abstract sheaf pullback along base change, the isomorphism
`CategoryTheory.GrothendieckTopology.Point.sheafFiberComapIso` of the sheaf pullback with
the fibre functor of the point obtained from `s` by `Point.comap`, and the identification
`AlgebraicGeometry.Scheme.pointSmallEtaleComapIso` of that point with `s ≫ f`. -/
noncomputable def Etale.upperStarCompSheafFiberIso :
    (f)^*[A] ⋙ (pointSmallEtale s).sheafFiber ≅ (pointSmallEtale (s ≫ f)).sheafFiber :=
  Functor.isoWhiskerRight
      (Functor.sheafPullbackConstruction.sheafPullbackIso
        (MorphismProperty.Over.pullback @Etale ⊤ f) A _ _).symm _ ≪≫
    (GrothendieckTopology.Point.sheafFiberComapIso (pointSmallEtale s) f.Etale
      (Hom.coverPreserving_etale f) A).symm ≪≫
    GrothendieckTopology.Point.sheafFiberIso (pointSmallEtaleComapIso f s)

/-- The universe-lifted form of `AlgebraicGeometry.Etale.upperStarCompSheafFiberIso`: the
stalk of `f^* F` at the geometric point `s`, taken at the universe of the coefficients, is
the stalk of `F` at `s ≫ f`. This is the form in which the comparison is used, since the
coefficient categories of the six functor formalism are concrete over `Type (u + 1)` and the
fibre functor of `pointSmallEtale s` takes values in `Type u`. -/
noncomputable def Etale.upperStarCompUliftSheafFiberIso :
    (f)^*[A] ⋙ ((pointSmallEtale s).ulift.{u + 1}).sheafFiber ≅
      ((pointSmallEtale (s ≫ f)).ulift.{u + 1}).sheafFiber :=
  Functor.isoWhiskerLeft _ ((pointSmallEtale s).uliftSheafFiberIso A) ≪≫
    upperStarCompSheafFiberIso A f s ≪≫
    ((pointSmallEtale (s ≫ f)).uliftSheafFiberIso A).symm

end BaseChange

section ClosedImmersion

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Z)

/-- Every pointed étale neighbourhood of a geometric point `s` of `Z` is dominated by the
base change of a pointed étale neighbourhood of `s ≫ i` in `X`. This is the first hypothesis
of `CategoryTheory.Functor.initial_of_exists_of_isCofiltered`, and its content is
`AlgebraicGeometry.Etale.exists_pullback_hom_of_isClosedImmersion`. -/
private theorem exists_hom_pointSmallEtaleElementsBaseChange
    (d : (pointSmallEtale s).fiber.Elements) :
    ∃ c, Nonempty ((pointSmallEtaleElementsBaseChange i s).obj c ⟶ d) := by
  obtain ⟨W, w⟩ := d
  -- lift `W` locally along `i` to an étale `X`-scheme `q : V ⟶ X`, in a way compatible with
  -- the marked point `w` of `W`
  obtain ⟨V, q, hq, g, hg, t, ht⟩ :=
    Etale.exists_pullback_hom_of_isClosedImmersion i W.hom w.left
  have := hq
  have hts : t ≫ pullback.snd q i = s := by
    rw [← hg, ← Category.assoc, ht]
    exact CategoryTheory.Over.w w
  have hv : (t ≫ pullback.fst q i) ≫ q = s ≫ i := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hts]
  refine ⟨⟨Scheme.Etale.mk q, CategoryTheory.Over.homMk (t ≫ pullback.fst q i) hv⟩,
    ⟨CategoryOfElements.homMk _ _ (MorphismProperty.Over.homMk g hg) ?_⟩⟩
  -- the marked point of `V ×_X Z` is `t`, since its two components are those of `t`
  have hp : ((pointSmallEtaleFiberEtaleIso i s).inv.app (Scheme.Etale.mk q)
      (CategoryTheory.Over.homMk (t ≫ pullback.fst q i) hv)).left = t := by
    refine pullback.hom_ext ?_ ?_
    · rw [Scheme.pointSmallEtaleFiberEtaleIso_inv_app_left_fst]
      rfl
    · rw [Scheme.pointSmallEtaleFiberEtaleIso_inv_app_left_snd]
      exact hts.symm
  apply CategoryTheory.Over.OverMorphism.ext
  change ((pointSmallEtaleFiberEtaleIso i s).inv.app (Scheme.Etale.mk q)
    (CategoryTheory.Over.homMk (t ≫ pullback.fst q i) hv)).left ≫ g = w.left
  rw [hp, ht]

/-- Two morphisms out of the base change `V ×_X Z` of a pointed étale neighbourhood of
`s ≫ i` into an étale `Z`-scheme which agree over `Z` are equalised after shrinking `V`.
This is the second hypothesis of
`CategoryTheory.Functor.initial_of_exists_of_isCofiltered`.

The two morphisms agree on the open `AlgebraicGeometry.FormallyUnramified.eqLocus` of
`V ×_X Z`, which contains the marked point. Since `V ×_X Z ⟶ V` is a closed immersion it is
inducing on the underlying spaces, so that agreement locus is the trace of an open `V₀` of
`V`; and `V₀` is the required shrinking of `V`. -/
private theorem exists_map_comp_eq_pointSmallEtaleElementsBaseChange
    {d : (pointSmallEtale s).fiber.Elements}
    {c : (pointSmallEtale (s ≫ i)).fiber.Elements}
    (σ σ' : (pointSmallEtaleElementsBaseChange i s).obj c ⟶ d) :
    ∃ (c' : (pointSmallEtale (s ≫ i)).fiber.Elements) (τ : c' ⟶ c),
      (pointSmallEtaleElementsBaseChange i s).map τ ≫ σ =
        (pointSmallEtaleElementsBaseChange i s).map τ ≫ σ' := by
  obtain ⟨V, v⟩ := c
  obtain ⟨W, w⟩ := d
  -- `p` is the marked point of `V ×_X Z`; both `σ` and `σ'` send it to the marked point of `W`
  set p : Spec (.of Ω) ⟶ pullback V.hom i :=
    ((pointSmallEtaleFiberEtaleIso i s).inv.app V v).left
  have key : ∀ τ : (pointSmallEtaleElementsBaseChange i s).obj ⟨V, v⟩ ⟶ ⟨W, w⟩,
      p ≫ τ.val.left = w.left := fun τ ↦ congrArg CategoryTheory.Over.Hom.left τ.property
  have hab : σ.val.left ≫ W.hom = σ'.val.left ≫ W.hom := by
    rw [CategoryTheory.Over.w, CategoryTheory.Over.w]
  have hpab : p ≫ σ.val.left = p ≫ σ'.val.left := by rw [key σ, key σ']
  have hvfst : p ≫ pullback.fst V.hom i = v.left :=
    Scheme.pointSmallEtaleFiberEtaleIso_inv_app_left_fst i s V v
  -- the agreement locus of `σ` and `σ'` is the trace of an open `V₀` of `V`
  obtain ⟨S, hS, hSU⟩ :=
    (pullback.fst V.hom i).isClosedEmbedding.isInducing.isOpen_iff.1
      (FormallyUnramified.eqLocus W.hom σ.val.left σ'.val.left hab).2
  set V₀ : V.left.Opens := ⟨S, hS⟩
  -- `V₀` contains the marked point of `V`, which is the image of `p`
  have hVrange : Set.range v.left.base ⊆ Set.range V₀.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    have hx := FormallyUnramified.range_subset_eqLocus W.hom σ.val.left σ'.val.left hab p hpab
      (Set.mem_range_self x)
    have hx' : (pullback.fst V.hom i).base (p.base x) ∈ S := by
      rw [← Set.mem_preimage, hSU]
      exact hx
    rw [← hvfst]
    exact hx'
  set v₀ := IsOpenImmersion.lift V₀.ι v.left hVrange
  have hv₀ι : v₀ ≫ V₀.ι = v.left := IsOpenImmersion.lift_fac _ _ _
  set θ : Scheme.Etale.mk (V₀.ι ≫ V.hom) ⟶ V :=
    MorphismProperty.Over.homMk V₀.ι rfl with hθ
  have hmfst : (i.Etale.map θ).left ≫ pullback.fst V.hom i =
      pullback.fst (Scheme.Etale.mk (V₀.ι ≫ V.hom)).hom i ≫ V₀.ι := by
    simp [Scheme.Hom.Etale, hθ]
  refine ⟨⟨Scheme.Etale.mk (V₀.ι ≫ V.hom), CategoryTheory.Over.homMk v₀ ?_⟩,
    CategoryOfElements.homMk _ _ θ ?_, ?_⟩
  · change v₀ ≫ V₀.ι ≫ V.hom = s ≫ i
    rw [← Category.assoc, hv₀ι]
    exact CategoryTheory.Over.w v
  · apply CategoryTheory.Over.OverMorphism.ext
    change v₀ ≫ V₀.ι = v.left
    exact hv₀ι
  · -- `V₀ ×_X Z` lands in the agreement locus, so `σ` and `σ'` agree on it
    have hmr : Set.range (i.Etale.map θ).left.base ⊆
        Set.range (FormallyUnramified.eqLocus W.hom σ.val.left σ'.val.left hab).ι.base := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      have h₁ : (pullback.fst V.hom i) ((i.Etale.map θ).left x) =
          V₀.ι ((pullback.fst (Scheme.Etale.mk (V₀.ι ≫ V.hom)).hom i) x) :=
        congrArg (fun m ↦ m.base x) hmfst
      have hmem : (i.Etale.map θ).left.base x ∈ ⇑(pullback.fst V.hom i) ⁻¹' S := by
        change (pullback.fst V.hom i) ((i.Etale.map θ).left x) ∈ S
        rw [h₁]
        exact (Scheme.Opens.range_ι V₀).subset (Set.mem_range_self _)
      rw [hSU] at hmem
      exact hmem
    refine Subtype.ext (MorphismProperty.Over.Hom.ext ?_)
    change (i.Etale.map θ).left ≫ σ.val.left = (i.Etale.map θ).left ≫ σ'.val.left
    rw [← IsOpenImmersion.lift_fac
      (FormallyUnramified.eqLocus W.hom σ.val.left σ'.val.left hab).ι _ hmr,
      Category.assoc, Category.assoc, FormallyUnramified.eqLocus_ι_comp_eq]

/-- **Base change along a closed immersion is initial on pointed étale neighbourhoods.** For
a closed immersion `i : Z ⟶ X` and a geometric point `s` of `Z`, every pointed étale
neighbourhood of `s` in `Z` is dominated by one of the form `V ×_X Z`, and two maps out of
such a `V ×_X Z` are equalised after shrinking `V`; the categories of pointed étale
neighbourhoods being cofiltered, this is initiality by
`CategoryTheory.Functor.initial_of_exists_of_isCofiltered`. -/
theorem Scheme.initial_pointSmallEtaleElementsBaseChange :
    (pointSmallEtaleElementsBaseChange i s).Initial :=
  Functor.initial_of_exists_of_isCofiltered _
    (exists_hom_pointSmallEtaleElementsBaseChange i s)
    (fun σ σ' ↦ exists_map_comp_eq_pointSmallEtaleElementsBaseChange i s σ σ')

/-- The presheaf form of `AlgebraicGeometry.Etale.lowerStarCompSheafFiberIso`: restricting an
`A`-valued presheaf on the small étale site of `Z` along base change along a closed immersion
`i : Z ⟶ X` and taking the fibre at the geometric point `s ≫ i` of `X` gives the fibre at
`s`. Both sides are colimits over categories of pointed étale neighbourhoods, and the
comparison is `AlgebraicGeometry.Scheme.initial_pointSmallEtaleElementsBaseChange` read
through `CategoryTheory.Functor.Final.colimIso`. -/
noncomputable def Etale.lowerStarCompPresheafFiberIso :
    (Functor.whiskeringLeft _ _ A).obj i.Etale.op ⋙ (pointSmallEtale (s ≫ i)).presheafFiber ≅
      (pointSmallEtale s).presheafFiber :=
  have := Scheme.initial_pointSmallEtaleElementsBaseChange i s
  Functor.isoWhiskerLeft
    ((Functor.whiskeringLeft _ _ A).obj (CategoryOfElements.π (pointSmallEtale s).fiber).op)
    (Functor.Final.colimIso (pointSmallEtaleElementsBaseChange i s).op)

/-- The comparison `AlgebraicGeometry.Etale.lowerStarCompPresheafFiberIso` on the canonical
maps from the sections over a pointed étale neighbourhood: the section of `P` over
`V ×_X Z` attached to a point `y` of `V` above `s ≫ i` has the same image in the fibre of
`P` at `s` whether it is seen as a section of the restriction of `P` over `(V, y)` or as a
section of `P` over the pointed étale neighbourhood `(V ×_X Z, y)` of `s`. -/
lemma Etale.toPresheafFiber_lowerStarCompPresheafFiberIso_hom_app (P : Z.Etaleᵒᵖ ⥤ A)
    (V : X.Etale) (y : (pointSmallEtale (s ≫ i)).fiber.obj V) :
    (pointSmallEtale (s ≫ i)).toPresheafFiber V y (i.Etale.op ⋙ P) ≫
        (Etale.lowerStarCompPresheafFiberIso A i s).hom.app P =
      (pointSmallEtale s).toPresheafFiber (i.Etale.obj V)
        ((pointSmallEtaleFiberEtaleIso i s).inv.app V y) P :=
  have := Scheme.initial_pointSmallEtaleElementsBaseChange i s
  Functor.Final.ι_colimitIso_hom (pointSmallEtaleElementsBaseChange i s).op
    ((CategoryOfElements.π (pointSmallEtale s).fiber).op ⋙ P) (op ⟨V, y⟩)

/-- **The stalk of a pushforward along a closed immersion.** For a closed immersion
`i : Z ⟶ X` and a geometric point `s : Spec Ω ⟶ Z`, the stalk of `i_* H` at the geometric
point `s ≫ i` of `X` is the stalk of `H` at `s`, naturally in the sheaf `H`.

On underlying presheaves `(i)_*[A]` *is* restriction along base change, so this is
`AlgebraicGeometry.Etale.lowerStarCompPresheafFiberIso` restricted to sheaves. -/
noncomputable def Etale.lowerStarCompSheafFiberIso :
    (i)_*[A] ⋙ (pointSmallEtale (s ≫ i)).sheafFiber ≅ (pointSmallEtale s).sheafFiber :=
  Functor.isoWhiskerLeft (sheafToPresheaf _ A) (Etale.lowerStarCompPresheafFiberIso A i s)

/-- The universe-lifted form of `AlgebraicGeometry.Etale.lowerStarCompSheafFiberIso`: the
stalk of `i_* H` at the geometric point `s ≫ i`, taken at the universe of the coefficients,
is the stalk of `H` at `s`. This is the form in which the comparison is used, since the
coefficient categories of the six functor formalism are concrete over `Type (u + 1)` and the
fibre functor of `pointSmallEtale s` takes values in `Type u`. -/
noncomputable def Etale.lowerStarCompUliftSheafFiberIso :
    (i)_*[A] ⋙ ((pointSmallEtale (s ≫ i)).ulift.{u + 1}).sheafFiber ≅
      ((pointSmallEtale s).ulift.{u + 1}).sheafFiber :=
  Functor.isoWhiskerLeft _ ((pointSmallEtale (s ≫ i)).uliftSheafFiberIso A) ≪≫
    lowerStarCompSheafFiberIso A i s ≪≫
    ((pointSmallEtale s).uliftSheafFiberIso A).symm

end ClosedImmersion

end AlgebraicGeometry
