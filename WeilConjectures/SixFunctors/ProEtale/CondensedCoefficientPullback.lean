/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.Topology.LocallyConstant.Algebra
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteExtension.UpperLowerStar.Monoidal

/-!

# Coefficient rings pulled back from the pro-étale site of a point

Let `Λ` be a condensed ring, i.e. a ring object of abelian sheaves on the pro-étale site of a
point `*_proét = (Profinite, coherent topology)`, for instance the condensed rings
`T̲ = C(-, T)` of `WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap`. Following
Sections 4 and 5 of `WeilConjectures/RefactorInstruction.tex`, this file pulls `Λ` back to every
scheme `X`,
```
Λ_X := p_X^* Λ,
```
along the canonical morphism `p_X : X_proét ⟶ *_proét`, and constructs explicitly the
isomorphisms of ring objects
```
α_f : f^* Λ_Y ≅ Λ_X
```
for every morphism of schemes `f : X ⟶ Y`.

## The profinite test objects

For a profinite set `S`, the ring `LC(S, ℤ)` of locally constant functions `S → ℤ` is the
filtered colimit of the finite products `ℤ^{S_i}` over the finite quotients `S_i` of `S`, so
```
Spec LC(S, ℤ) = lim_i ∐_{S_i} Spec ℤ,
```
the profinite set `S` regarded as a pro-étale scheme over `Spec ℤ`
(`AlgebraicGeometry.ProEtale.profiniteToProEt`). For a scheme `X` with structure morphism
`π_X : X ⟶ Spec ℤ`, the base change
```
X[S] := Spec LC(S, ℤ) ×_{Spec ℤ} X = lim_i ∐_{S_i} X
```
is the pro-étale `X`-scheme of the notes (`AlgebraicGeometry.ProEtale.profiniteToProEtOf`). The
functor `S ↦ X[S]` is the composite of `S ↦ Spec LC(S, ℤ)` with the base change along `π_X`.

## The morphism `p_X` and the comparison `α_f`

Accordingly, the inverse image along `p_X` is the composite
```
p_X^* := π_X^* ∘ p^*,
```
where `p^* : Sheaf *_proét Ab ⥤ Sheaf (Spec ℤ)_proét Ab` is the inverse image along the
continuous functor `S ↦ Spec LC(S, ℤ)` (`AlgebraicGeometry.ProEtale.pointUpperStar`). For
`f : X ⟶ Y`, the structure morphisms satisfy `f ≫ π_Y = π_X`, `Spec ℤ` being terminal, and the
comparison
```
α_f : f^* p_Y^* = f^* π_Y^* p^* ≅ (f ≫ π_Y)^* p^* = π_X^* p^* = p_X^*
```
is the composition isomorphism `ProEtale.upperStarComp` of the pullbacks, which on the test
objects is the canonical isomorphism `X ×_Y Y[S] ≅ X[S]` of the notes
(`AlgebraicGeometry.ProEtale.upperStarFromPointComp`). Evaluated at `Λ`, it is the isomorphism
of ring objects `α_f : f^* Λ_Y ≅ Λ_X` (`AlgebraicGeometry.ProEtale.coefficientPullbackIso`).

## Main definitions

* `AlgebraicGeometry.ProEtale.profiniteToProEt`: the functor `S ↦ Spec LC(S, ℤ)` from
  profinite sets to the pro-étale site of `Spec ℤ`.
* `AlgebraicGeometry.ProEtale.pointUpperStar`: the inverse image `p^*` from condensed abelian
  groups to abelian sheaves on `(Spec ℤ)_proét`.
* `AlgebraicGeometry.ProEtale.upperStarFromPoint`: the inverse image `p_X^* = π_X^* ∘ p^*`.
* `AlgebraicGeometry.ProEtale.coefficientRing`: the ring object `Λ_X = p_X^* Λ`.
* `AlgebraicGeometry.ProEtale.upperStarFromPointComp`: the natural isomorphism
  `f^* ∘ p_Y^* ≅ p_X^*`.
* `AlgebraicGeometry.ProEtale.coefficientPullbackIso`: the isomorphism of ring objects
  `α_f : f^* Λ_Y ≅ Λ_X`.

## Sorried input

* `AlgebraicGeometry.ProEtale.weaklyEtale_toSpecZ_profiniteToScheme`: `Spec LC(S, ℤ) ⟶ Spec ℤ`
  is weakly étale, `LC(S, ℤ)` being ind-Zariski over `ℤ` (the filtered colimit of the finite
  products `ℤ^{S_i}`), and ind-Zariski algebras being weakly étale.
* `AlgebraicGeometry.ProEtale.preservesFiniteLimits_profiniteToProEt` and
  `AlgebraicGeometry.ProEtale.coverPreserving_profiniteToProEt`: the functor
  `S ↦ Spec LC(S, ℤ)` preserves finite limits (`LC(-, ℤ)` sends a fibre product of profinite
  sets to the tensor product, and the point to `ℤ`), and sends a finite jointly surjective
  family to a pro-étale covering (the map on underlying spaces of `Spec LC(S, ℤ)` is the
  projection `S × Spec ℤ → S`, so surjectivity is preserved, and the morphisms are weakly
  étale and affine). This is Lemma 4.2 of the notes.
* `AlgebraicGeometry.ProEtale.hasLeftKanExtension_op_profiniteToProEt`: the left Kan
  extensions along the opposite of `S ↦ Spec LC(S, ℤ)` exist, both sites being essentially
  small in `u + 1` and `Ab.{u + 1}` being cocomplete for `u + 1`-small diagrams, exactly as
  for `SmallSite.hasLeftKanExtension_op_overPullback`.
* `AlgebraicGeometry.ProEtale.isIso_η_pointUpperStar` and
  `AlgebraicGeometry.ProEtale.isIso_δ_pointUpperStar`: `p^*` is strong monoidal, being the
  sheafification of a left Kan extension along a finite limit preserving functor, which
  commutes with the objectwise tensor product (as for `ProEtale.isIso_δ_upperStar`).
* `AlgebraicGeometry.ProEtale.isMonoidal_upperStarFromPointComp`: the comparison
  `f^* ∘ p_Y^* ≅ p_X^*` is a monoidal natural isomorphism. It is the mate of the composition
  isomorphism of pushforwards, which is monoidal by `ProEtale.isMonoidal_lowerStarComp`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite Functor.LaxMonoidal Functor.OplaxMonoidal

namespace AlgebraicGeometry.ProEtale

open Scheme

/-! ### `Spec ℤ` and the structure morphisms -/

/-- The terminal scheme `Spec ℤ`, in the universe `u`. -/
noncomputable abbrev specZ : Scheme.{u} :=
  Spec (.of (ULift.{u} ℤ))

/-- The structure morphism `π_X : X ⟶ Spec ℤ`. -/
noncomputable abbrev toSpecZ (X : Scheme.{u}) : X ⟶ specZ :=
  specULiftZIsTerminal.from X

/-- The structure morphisms are compatible with every morphism of schemes, `Spec ℤ` being
terminal. -/
lemma comp_toSpecZ {X Y : Scheme.{u}} (f : X ⟶ Y) : f ≫ toSpecZ Y = toSpecZ X :=
  specULiftZIsTerminal.hom_ext _ _

/-! ### Profinite sets as pro-étale schemes over `Spec ℤ` -/

/-- The functor `S ↦ LC(S, ℤ)` sending a profinite set to its ring of locally constant
integer-valued functions, contravariantly by precomposition. -/
noncomputable def profiniteToCommRingCatOp : Profinite.{u} ⥤ CommRingCat.{u}ᵒᵖ where
  obj S := op (CommRingCat.of (LocallyConstant S ℤ))
  map f := (CommRingCat.ofHom (LocallyConstant.comapRingHom f.hom.hom)).op

/-- The functor `S ↦ Spec LC(S, ℤ) = lim_i ∐_{S_i} Spec ℤ`, the profinite set `S` regarded as a
scheme. -/
noncomputable def profiniteToScheme : Profinite.{u} ⥤ Scheme.{u} :=
  profiniteToCommRingCatOp ⋙ Scheme.Spec

/-- `Spec LC(S, ℤ) ⟶ Spec ℤ` is weakly étale. See the module docstring. -/
instance weaklyEtale_toSpecZ_profiniteToScheme (S : Profinite.{u}) :
    WeaklyEtale (toSpecZ (profiniteToScheme.obj S)) :=
  sorry

/-- The functor `S ↦ Spec LC(S, ℤ)` from profinite sets to the pro-étale site of `Spec ℤ`. -/
noncomputable def profiniteToProEt : Profinite.{u} ⥤ specZ.{u}.ProEt where
  obj S := ProEt.mk (toSpecZ (profiniteToScheme.obj S))
  map f := MorphismProperty.Over.homMk (profiniteToScheme.map f) (comp_toSpecZ _)
  map_id S := MorphismProperty.Over.Hom.ext (profiniteToScheme.map_id S)
  map_comp f g := MorphismProperty.Over.Hom.ext (profiniteToScheme.map_comp f g)

lemma profiniteToProEt_obj_left (S : Profinite.{u}) :
    (profiniteToProEt.obj S).left = Spec (.of (LocallyConstant S ℤ)) :=
  rfl

/-- The functor `S ↦ Spec LC(S, ℤ)` preserves finite limits. See the module docstring. -/
instance preservesFiniteLimits_profiniteToProEt : PreservesFiniteLimits profiniteToProEt.{u} :=
  sorry

instance : RepresentablyFlat profiniteToProEt.{u} :=
  flat_of_preservesFiniteLimits _

/-- The functor `S ↦ Spec LC(S, ℤ)` sends finite jointly surjective families to pro-étale
coverings. See the module docstring. -/
lemma coverPreserving_profiniteToProEt :
    CoverPreserving (coherentTopology Profinite.{u}) (ProEt.topology specZ) profiniteToProEt :=
  sorry

instance isContinuous_profiniteToProEt :
    profiniteToProEt.IsContinuous (coherentTopology Profinite.{u}) (ProEt.topology specZ) :=
  Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
    coverPreserving_profiniteToProEt

/-- The left Kan extensions along the opposite of `S ↦ Spec LC(S, ℤ)` exist. See the module
docstring. -/
instance hasLeftKanExtension_op_profiniteToProEt (F : Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}) :
    profiniteToProEt.op.HasLeftKanExtension F :=
  sorry

/-- The profinite test object `X[S] = Spec LC(S, ℤ) ×_{Spec ℤ} X = lim_i ∐_{S_i} X` over a
scheme `X`, as a functor from profinite sets to the pro-étale site of `X`. -/
noncomputable def profiniteToProEtOf (X : Scheme.{u}) : Profinite.{u} ⥤ X.ProEt :=
  profiniteToProEt ⋙
    MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)

/-! ### The inverse image `p^*` from the point -/

/-- The direct image `p_*` from abelian sheaves on `(Spec ℤ)_proét` to condensed abelian
groups, `(p_* G)(S) = G(Spec LC(S, ℤ))`. -/
noncomputable def pointLowerStar :
    Sheaf (ProEt.topology specZ.{u}) Ab.{u + 1} ⥤
      Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  profiniteToProEt.sheafPushforwardContinuous Ab.{u + 1} (coherentTopology Profinite.{u})
    (ProEt.topology specZ)

/-- The inverse image `p^*` from condensed abelian groups to abelian sheaves on
`(Spec ℤ)_proét`: left Kan extension along `S ↦ Spec LC(S, ℤ)` followed by sheafification. -/
noncomputable def pointUpperStar :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⥤
      Sheaf (ProEt.topology specZ.{u}) Ab.{u + 1} :=
  Functor.sheafPullbackConstruction.sheafPullback profiniteToProEt Ab.{u + 1}
    (coherentTopology Profinite.{u}) (ProEt.topology specZ)

/-- The adjunction `p^* ⊣ p_*`. -/
noncomputable def pointUpperStarLowerStarAdjunction : pointUpperStar.{u} ⊣ pointLowerStar :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous profiniteToProEt Ab.{u + 1}
    (coherentTopology Profinite.{u}) (ProEt.topology specZ)

/-- The direct image `p_*` is lax monoidal, being the pushforward along a continuous functor. -/
noncomputable instance laxMonoidal_pointLowerStar : pointLowerStar.{u}.LaxMonoidal := by
  unfold pointLowerStar
  infer_instance

/-- The inverse image `p^*` is oplax monoidal, being left adjoint to the lax monoidal `p_*`. -/
noncomputable instance oplaxMonoidal_pointUpperStar : pointUpperStar.{u}.OplaxMonoidal :=
  pointUpperStarLowerStarAdjunction.leftAdjointOplaxMonoidal

/-- The inverse image `p^*` preserves the unit. See the module docstring. -/
instance isIso_η_pointUpperStar : IsIso (η pointUpperStar.{u}) :=
  sorry

/-- The inverse image `p^*` commutes with the tensor product. See the module docstring. -/
instance isIso_δ_pointUpperStar (F G : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :
    IsIso (δ pointUpperStar F G) :=
  sorry

/-- The inverse image `p^*` is strong monoidal. -/
noncomputable instance monoidal_pointUpperStar : pointUpperStar.{u}.Monoidal :=
  Functor.Monoidal.ofOplaxMonoidal _

/-! ### The inverse image `p_X^*` and the coefficient rings `Λ_X` -/

/-- The inverse image `p_X^* = π_X^* ∘ p^*` from condensed abelian groups to abelian sheaves on
`X_proét`. On the test objects it is the inverse image along `S ↦ X[S]`. -/
noncomputable def upperStarFromPoint (X : Scheme.{u}) :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⥤ Sheaf (ProEt.topology X) Ab.{u + 1} :=
  pointUpperStar ⋙ (toSpecZ X)^*[Ab.{u + 1}]

/-- The inverse image `p_X^*` is strong monoidal. -/
noncomputable instance monoidal_upperStarFromPoint (X : Scheme.{u}) :
    (upperStarFromPoint X).Monoidal := by
  unfold upperStarFromPoint
  infer_instance

/-- The coefficient ring `Λ_X = p_X^* Λ` on `X_proét` of a condensed ring `Λ`. -/
noncomputable def coefficientRing (X : Scheme.{u})
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) :
    Mon (Sheaf (ProEt.topology X) Ab.{u + 1}) :=
  (upperStarFromPoint X).mapMon.obj Λ

lemma coefficientRing_X (X : Scheme.{u})
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) :
    (coefficientRing X Λ).X = (upperStarFromPoint X).obj Λ.X :=
  rfl

/-- The condensed ring `T̲ = C(-, T)` of continuous maps into a topological ring `T`, as a ring
object of condensed abelian groups. -/
noncomputable def continuousMapCondensedRing (T : Type) [TopologicalSpace T] [Ring T]
    [IsTopologicalRing T] : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
  Mon.mk ((sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
    (Profinite.continuousMapRingSheaf T))

/-! ### The comparison `α_f : f^* Λ_Y ≅ Λ_X` -/

section Comparison

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The natural isomorphism `f^* ∘ p_Y^* ≅ p_X^*`: the composition isomorphism
`f^* ∘ π_Y^* ≅ (f ≫ π_Y)^*` of the pullbacks, followed by `f ≫ π_Y = π_X`. On the test objects
it is the canonical isomorphism `X ×_Y Y[S] ≅ X[S]`. -/
noncomputable def upperStarFromPointComp :
    upperStarFromPoint Y ⋙ (f)^*[Ab.{u + 1}] ≅ upperStarFromPoint X :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft pointUpperStar
    ((upperStarComp Ab.{u + 1} f (toSpecZ Y)).symm ≪≫
      eqToIso (by rw [comp_toSpecZ]))

/-- The comparison `f^* ∘ p_Y^* ≅ p_X^*` is a monoidal natural isomorphism. See the module
docstring. -/
instance isMonoidal_upperStarFromPointComp :
    NatTrans.IsMonoidal (upperStarFromPointComp f).hom :=
  sorry

/-- The comparison `α_f : f^* Λ_Y ≅ Λ_X` of the coefficient rings pulled back from the point,
an isomorphism of ring objects of abelian sheaves on `X_proét`. -/
noncomputable def coefficientPullbackIso
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) :
    (f)^*[Ab.{u + 1}].mapMon.obj (coefficientRing Y Λ) ≅ coefficientRing X Λ :=
  (Functor.mapMonCompIso (F := upperStarFromPoint Y) (G := (f)^*[Ab.{u + 1}])).symm.app Λ ≪≫
    (Functor.mapMonNatIso (upperStarFromPointComp f)).app Λ

end Comparison

end AlgebraicGeometry.ProEtale
