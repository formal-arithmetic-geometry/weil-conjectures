/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.SixFunctors.UpperLowerStar.TopologicalInvariance

/-!
# Descent of locally constant sheaves along universal homeomorphisms

Let `f : X ⟶ Y` be a universal homeomorphism. Pullback along `f` is an equivalence of the
categories of étale sheaves (`AlgebraicGeometry.Etale.isEquivalence_upperStar`, Stacks 03SI)
and carries constant sheaves to constant sheaves, so constancy descends along `f`. Base change
along `f` is moreover essentially surjective on étale schemes (Stacks 04DZ), so a trivialising
cover of `f^* G` comes from an étale cover of `Y`, and each base change of `f` is again a
universal homeomorphism; this makes local constancy descend as well.

Finiteness of the stalks is local for a jointly surjective family of morphisms which are
surjective on stalks: every geometric point of the base lifts to a member of the family
(`AlgebraicGeometry.Scheme.Hom.exists_comp_eq_of_mem_range`), and the stalk of the pullback at
a lift is the stalk of the sheaf. In particular finiteness descends along a surjective closed
immersion; this is the case needed for the independence of constructibility from the scheme
structures on the strata, see `WeilConjectures.ConstructibleSheaf.Refinement`.
(blueprint: `lemma:constructible-universal-homeomorphism-invariance`)

## Main results

- `AlgebraicGeometry.Scheme.isConstant_upperStar_iff`: a sheaf is constant if and only if its
  pullback along a universal homeomorphism is.
- `AlgebraicGeometry.Scheme.IsLocallyConstantSheaf.of_upperStar` and
  `AlgebraicGeometry.Scheme.isLocallyConstantSheaf_upperStar_iff`: a sheaf is locally constant
  if and only if its pullback along a universal homeomorphism is.
- `AlgebraicGeometry.Scheme.IsFiniteSheaf.of_jointly_surjective` and
  `AlgebraicGeometry.Scheme.IsFiniteSheaf.of_upperStar`: a sheaf is finite as soon as its
  pullbacks along a jointly surjective family of morphisms surjective on stalks are.
- `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.of_upperStar` and
  `AlgebraicGeometry.Scheme.isFiniteLocallyConstantSheaf_upperStar_iff`: a sheaf is finite
  locally constant if and only if its pullback along a universal homeomorphism which is
  surjective on stalks, for instance along a surjective closed immersion, is.

## TODO

Finiteness is descended only along morphisms surjective on stalks, not along an arbitrary
universal homeomorphism `f : X ⟶ Y`: a geometric point `Spec k ⟶ Y` with `k` separably closed
need not lift to `X`, the residue field extension being purely inseparable. The general case
is reachable: the residue field `k'` of a point of the fibre `X ×_Y Spec k` is purely
inseparable over `k`, hence again separably closed, so `Spec k' ⟶ X` is a geometric point of
`X`. What is missing is the invariance of the stalks of a sheaf under the universal
homeomorphism `Spec k' ⟶ Spec k`.
-/

@[expose] public section

universe u u'

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

section Constant

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsUniversalHomeomorphism f]

/-- **A sheaf is constant if and only if its pullback along a universal homeomorphism `f` is
constant.** (blueprint: `lemma:constructible-universal-homeomorphism-invariance`) -/
lemma isConstant_upperStar_iff (G : Sheaf Y.smallEtaleTopology A) :
    ((Etale.upperStar A f).obj G).IsConstant X.smallEtaleTopology ↔
      G.IsConstant Y.smallEtaleTopology :=
  have := Etale.isEquivalence_upperStar A f
  Sheaf.isConstant_iff_of_constantSheafIso (upperStarConstantSheafIso A f) G

end Constant

section LocallyConstant

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsUniversalHomeomorphism f]

attribute [local instance] Scheme.Hom.isEquivalence_etale

/-- **Local constancy descends along a universal homeomorphism** `f : X ⟶ Y`: if `f^* G` is
locally constant, then so is `G`.

The trivialising cover of `G` is descended from one of `f^* G` along the base-change squares

```
   V ×_Y X ──fst──→ V
      │             │
   snd│             │(V i).hom
      ↓             ↓
      X ─────f────→ Y
```

whose left-hand side is again a universal homeomorphism.
(blueprint: `lemma:constructible-universal-homeomorphism-invariance`) -/
theorem IsLocallyConstantSheaf.of_upperStar (G : Sheaf Y.smallEtaleTopology A)
    [IsLocallyConstantSheaf ((Etale.upperStar A f).obj G)] : IsLocallyConstantSheaf G := by
  obtain ⟨⟨𝒰, h𝒰⟩⟩ :=
    IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := (Etale.upperStar A f).obj G)
  let V (i : 𝒰.I₀) : Y.Etale := f.Etale.objPreimage (𝒰.etalePrecoverageToEtale i)
  let e (i : 𝒰.I₀) : f.Etale.obj (V i) ≅ 𝒰.etalePrecoverageToEtale i :=
    f.Etale.objObjPreimageIso _
  have hinv (i : 𝒰.I₀) : (e i).inv.left ≫ pullback.snd (V i).hom f = 𝒰.f i :=
    MorphismProperty.Over.w (e i).inv
  let 𝒱 : Cover.{u} etalePrecoverage Y :=
    { I₀ := 𝒰.I₀
      X i := (V i).left
      f i := (V i).hom
      mem₀ := by
        refine (presieve₀_mem_precoverage_iff _).mpr ⟨fun y ↦ ?_, fun i ↦ (V i).prop⟩
        obtain ⟨x, rfl⟩ := f.surjective y
        obtain ⟨i, x', rfl⟩ := 𝒰.exists_eq x
        refine ⟨i, (pullback.fst (V i).hom f) ((e i).inv.left x'), ?_⟩
        -- unfold `𝒱.f i` to `(V i).hom` and read both sides as applications of a composite
        change ((e i).inv.left ≫ pullback.fst (V i).hom f ≫ (V i).hom) x' = (𝒰.f i ≫ f) x'
        rw [pullback.condition, ← Category.assoc, hinv]
        rfl }
  refine ⟨⟨⟨𝒱, fun i ↦ ?_⟩⟩⟩
  rw [isConstant_over_iff_upperStar]
  -- unfold `𝒱.f i` to `(V i).hom`
  change ((Etale.upperStar A (V i).hom).obj G).IsConstant (V i).left.smallEtaleTopology
  refine (isConstant_upperStar_iff (pullback.fst (V i).hom f) _).mp ?_
  -- `hconst` and `hconst'` are never referred to by name: they are picked up by instance
  -- search, in `Sheaf.IsConstant.upperStar` and in the final `Sheaf.isConstant_congr`.
  have hconst : ((Etale.upperStar A (𝒰.f i)).obj ((Etale.upperStar A f).obj G)).IsConstant
      (𝒰.etalePrecoverageToEtale i).left.smallEtaleTopology :=
    (isConstant_over_iff_upperStar A (𝒰.etalePrecoverageToEtale i) _).mp (h𝒰 i)
  have hconst' : ((Etale.upperStar A (e i).hom.left).obj
      ((Etale.upperStar A (𝒰.f i)).obj ((Etale.upperStar A f).obj G))).IsConstant
        (pullback (V i).hom f).smallEtaleTopology :=
    Sheaf.IsConstant.upperStar A _ _
  have hsnd : pullback.snd (V i).hom f = (e i).hom.left ≫ 𝒰.f i :=
    (MorphismProperty.Over.w (e i).hom).symm
  let e' : (Etale.upperStar A (pullback.fst (V i).hom f)).obj
      ((Etale.upperStar A (V i).hom).obj G) ≅
      (Etale.upperStar A (e i).hom.left).obj
        ((Etale.upperStar A (𝒰.f i)).obj ((Etale.upperStar A f).obj G)) :=
    Etale.upperStarSquareIso A (h₁ := pullback.fst (V i).hom f) (h₂ := (V i).hom)
        (k₁ := (e i).hom.left) (k₂ := 𝒰.f i ≫ f)
        (by rw [pullback.condition, hsnd, Category.assoc]) G ≪≫
      (Etale.upperStar A (e i).hom.left).mapIso
        ((Etale.upperStarComp A (𝒰.f i) f (𝒰.f i ≫ f) rfl).app G)
  exact Sheaf.isConstant_congr _ e'.symm

/-- **A sheaf is locally constant if and only if its pullback along a universal homeomorphism
is locally constant.** (blueprint: `lemma:constructible-universal-homeomorphism-invariance`) -/
theorem isLocallyConstantSheaf_upperStar_iff (G : Sheaf Y.smallEtaleTopology A) :
    IsLocallyConstantSheaf ((Etale.upperStar A f).obj G) ↔ IsLocallyConstantSheaf G :=
  ⟨fun _ ↦ IsLocallyConstantSheaf.of_upperStar f G,
    fun _ ↦ IsLocallyConstantSheaf.upperStar f G⟩

end LocallyConstant

section Finite

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
variable {W Z : Scheme.{u}}

/-- **Finiteness is local for a jointly surjective family of morphisms surjective on
stalks**: if the pullbacks of `G` along the `f i` are finite, then `G` is finite.

Every geometric point `s : Spec Ω ⟶ Z` lifts to some `Y i`, and the stalk of `(f i)^* G` at
the lift is the stalk of `G` at `s`:

```
   Spec Ω ────s'───→ Y i
       ╲              │
      s ╲             │ f i
         ╲            ↓
          ──────────→ Z
```
-/
theorem IsFiniteSheaf.of_jointly_surjective {ι : Type*} {Y : ι → Scheme.{u}}
    (f : ∀ i, Y i ⟶ Z) [∀ i, SurjectiveOnStalks (f i)]
    (hf : ∀ z : Z, ∃ i, z ∈ Set.range (f i)) (G : Sheaf Z.smallEtaleTopology A)
    [∀ i, IsFiniteSheaf ((Etale.upperStar A (f i)).obj G)] : IsFiniteSheaf G where
  finite_sheafFiber Ω _ _ s := by
    obtain ⟨i, hi⟩ := hf (s (IsLocalRing.closedPoint _))
    obtain ⟨s', rfl⟩ := (f i).exists_comp_eq_of_mem_range s hi
    have := IsFiniteSheaf.finite_sheafFiber (FA := FA) (CA := CA)
      (F := (Etale.upperStar A (f i)).obj G) Ω s'
    exact Finite.of_equiv
      (ToType ((pointSmallEtale s').sheafFiber.obj ((Etale.upperStar A (f i)).obj G)))
      ((CategoryTheory.forget A).mapIso
        ((Etale.upperStarCompSheafFiberIso A (f i) s').app G)).toEquiv

variable (p : W ⟶ Z)

/-- **Finiteness descends along a surjective morphism which is surjective on stalks**, for
instance along a surjective closed immersion: this is the one-member case of
`AlgebraicGeometry.Scheme.IsFiniteSheaf.of_jointly_surjective`.
(blueprint: `lemma:constructible-universal-homeomorphism-invariance`) -/
theorem IsFiniteSheaf.of_upperStar [SurjectiveOnStalks p] [Surjective p]
    (G : Sheaf Z.smallEtaleTopology A) [IsFiniteSheaf ((Etale.upperStar A p).obj G)] :
    IsFiniteSheaf G :=
  IsFiniteSheaf.of_jointly_surjective (fun _ : Unit ↦ p) (fun z ↦ ⟨(), p.surjective z⟩) G

variable [IsUniversalHomeomorphism p] [SurjectiveOnStalks p]

/-- **Finite local constancy descends along a universal homeomorphism which is surjective on
stalks**, for instance along a surjective closed immersion.
(blueprint: `lemma:constructible-universal-homeomorphism-invariance`) -/
theorem IsFiniteLocallyConstantSheaf.of_upperStar (G : Sheaf Z.smallEtaleTopology A)
    [IsFiniteLocallyConstantSheaf ((Etale.upperStar A p).obj G)] :
    IsFiniteLocallyConstantSheaf G where
  toIsLocallyConstantSheaf := IsLocallyConstantSheaf.of_upperStar p G
  toIsFiniteSheaf := IsFiniteSheaf.of_upperStar p G

/-- **A sheaf is finite locally constant if and only if its pullback along a universal
homeomorphism which is surjective on stalks is**, for instance along a surjective closed
immersion. (blueprint: `lemma:constructible-universal-homeomorphism-invariance`) -/
theorem isFiniteLocallyConstantSheaf_upperStar_iff (G : Sheaf Z.smallEtaleTopology A) :
    IsFiniteLocallyConstantSheaf ((Etale.upperStar A p).obj G) ↔
      IsFiniteLocallyConstantSheaf G :=
  ⟨fun _ ↦ IsFiniteLocallyConstantSheaf.of_upperStar p G,
    fun _ ↦ IsFiniteLocallyConstantSheaf.upperStar p G⟩

end Finite

end AlgebraicGeometry.Scheme
