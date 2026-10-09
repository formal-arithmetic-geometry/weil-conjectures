/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Coequalizer
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction

/-!
# Base change of finite étale schemes is exact

Let `f : X ⟶ Y` be a morphism of schemes. The base change functor
`AlgebraicGeometry.Scheme.FiniteEtale.pullback f : FÉt(Y) ⥤ FÉt(X)` preserves finite limits and
finite colimits (blueprint `lem-fet-finite-limits`).

The proof goes through geometric fibres:

* every fibre functor `F_s : FÉt(Y) ⥤ FintypeCat` preserves finite colimits, also over a
  disconnected base (`AlgebraicGeometry.Scheme.FiniteEtale.preservesFiniteColimits_fiber`): it
  preserves finite coproducts and quotients by finite monoids, and coequalizers are quotients by
  a finite monoid action;
* the fibre functors at the points of `X` jointly reflect isomorphisms
  (`AlgebraicGeometry.Scheme.FiniteEtale.isIso_of_forall_isIso_fiber_map`);
* the fibre of a base change at `s` is the fibre at `s ≫ f`
  (`AlgebraicGeometry.Scheme.FiniteEtale.pullbackFiberIso`).

## Main results

- `AlgebraicGeometry.Scheme.FiniteEtale.preservesFiniteLimits_pullback`
- `AlgebraicGeometry.Scheme.FiniteEtale.preservesFiniteColimits_pullback`
-/

@[expose] public section

universe u

open CategoryTheory Limits MorphismProperty

namespace CategoryTheory.Limits

universe w

variable {C : Type*} [Category* C] [HasBinaryCoproducts C] {Z P : C} {f g : Z ⟶ P}

/-- The quotient of `P ⨿ Z` by the action of `ParallelPairMonoid` given by a coequalizer of `f`
and `g` is a colimit. -/
noncomputable def isColimitCoconeOfCofork {t : Cofork f g} (ht : IsColimit t) :
    IsColimit (coconeOfCofork.{w} f g t) where
  desc s := ht.desc (coforkOfCocone f g s)
  fac s j := by
    obtain rfl : j = SingleObj.star _ := rfl
    have hl := s.w (j := SingleObj.star _) (j' := SingleObj.star _) ParallelPairMonoid.left
    simp only [parallelPairMonoidFunctor_map, parallelPairMonoidAct] at hl
    have hl' := coprod.inr ≫= hl
    simp only [coprod.inr_desc_assoc, Category.assoc] at hl'
    apply coprod.hom_ext
    · simp [coconeOfCofork, coforkOfCocone]
    · simp [coconeOfCofork, coforkOfCocone, hl']
  uniq s m hm := by
    apply Cofork.IsColimit.hom_ext ht
    rw [Cofork.IsColimit.π_desc]
    simpa [coconeOfCofork, coforkOfCocone] using coprod.inl ≫= hm (SingleObj.star _)

variable {D : Type*} [Category* D] (F : C ⥤ D)

/-- A functor preserving the coproduct `P ⨿ Z` and the quotient of `P ⨿ Z` by the action of
`ParallelPairMonoid` preserves coequalizers of `f` and `g`. -/
noncomputable def isColimitCoforkMapOfPreserves [PreservesColimit (pair P Z) F]
    [PreservesColimit (parallelPairMonoidFunctor.{w} f g) F] {W : C} {π : P ⟶ W}
    {w : f ≫ π = g ≫ π} (ht : IsColimit (Cofork.ofπ π w)) :
    IsColimit (Cofork.ofπ (F.map π) (by simp only [← F.map_comp, w]) :
      Cofork (F.map f) (F.map g)) := by
  have hq := isColimitOfPreserves F (isColimitCoconeOfCofork.{w} ht)
  have hcop := isColimitMapCoconeBinaryCofanEquiv F _ _
    (isColimitOfPreserves F (coprodIsCoprod P Z))
  let ℓ (s : Cofork (F.map f) (F.map g)) : F.obj (P ⨿ Z) ⟶ s.pt :=
    (BinaryCofan.IsColimit.desc' hcop s.π (F.map f ≫ s.π)).1
  have hℓ₁ (s : Cofork (F.map f) (F.map g)) : F.map coprod.inl ≫ ℓ s = s.π :=
    (BinaryCofan.IsColimit.desc' hcop s.π (F.map f ≫ s.π)).2.1
  have hℓ₂ (s : Cofork (F.map f) (F.map g)) : F.map coprod.inr ≫ ℓ s = F.map f ≫ s.π :=
    (BinaryCofan.IsColimit.desc' hcop s.π (F.map f ≫ s.π)).2.2
  let c (s : Cofork (F.map f) (F.map g)) : Cocone (parallelPairMonoidFunctor.{w} f g ⋙ F) :=
    { pt := s.pt
      ι :=
        { app _ := ℓ s
          naturality _ _ m := by
            refine (?_ : _ = ℓ s).trans (Category.comp_id _).symm
            rw [Functor.comp_map, parallelPairMonoidFunctor_map]
            refine BinaryCofan.IsColimit.hom_ext hcop ?_ ?_
            · rw [BinaryCofan.mk_inl, ← F.map_comp_assoc, inl_parallelPairMonoidAct]
            · rw [BinaryCofan.mk_inr, ← F.map_comp_assoc]
              cases m
              · rw [parallelPairMonoidAct, Category.comp_id]
              · rw [parallelPairMonoidAct, coprod.inr_desc, F.map_comp_assoc, hℓ₁, hℓ₂]
              · rw [parallelPairMonoidAct, coprod.inr_desc, F.map_comp_assoc, hℓ₁, hℓ₂,
                  s.condition] } }
  have hc (s : Cofork (F.map f) (F.map g)) :
      F.map (coprod.desc π (f ≫ π)) ≫ hq.desc (c s) = ℓ s :=
    hq.fac (c s) (SingleObj.star _)
  refine Cofork.IsColimit.mk _ (fun s ↦ hq.desc (c s)) (fun s ↦ ?_) (fun s m hm ↦ ?_)
  · rw [Cofork.π_ofπ, ← hℓ₁, ← hc, ← F.map_comp_assoc, coprod.inl_desc]
  · rw [Cofork.π_ofπ] at hm
    refine hq.hom_ext fun j ↦ ?_
    obtain rfl : j = SingleObj.star _ := rfl
    rw [hq.fac]
    refine BinaryCofan.IsColimit.hom_ext hcop ?_ ?_
    · rw [BinaryCofan.mk_inl, hℓ₁, ← hm, Functor.mapCocone_ι_app, ← F.map_comp_assoc]
      simp [coconeOfCofork]
    · rw [BinaryCofan.mk_inr, hℓ₂, ← hm, Functor.mapCocone_ι_app, ← F.map_comp_assoc]
      simp [coconeOfCofork]

/-- A functor preserving binary coproducts and quotients by the action of `ParallelPairMonoid`
preserves coequalizers. -/
lemma preservesColimitsOfShape_walkingParallelPair_of_singleObj [HasCoequalizers C]
    [PreservesColimitsOfShape (Discrete WalkingPair) F]
    [PreservesColimitsOfShape (SingleObj ParallelPairMonoid.{w}) F] :
    PreservesColimitsOfShape WalkingParallelPair F where
  preservesColimit {K} :=
    have (f g : K.obj .zero ⟶ K.obj .one) : PreservesColimit (parallelPair f g) F :=
      preservesColimit_of_preserves_colimit_cocone (coequalizerIsCoequalizer f g)
        ((isColimitMapCoconeCoforkEquiv F _).symm
          (isColimitCoforkMapOfPreserves.{w} F (coequalizerIsCoequalizer f g)))
    preservesColimit_of_iso_diagram F (diagramIsoParallelPair K).symm

end CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale

section FiberColimits

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)

/-- **The fibre functor preserves finite colimits** (blueprint `lem-fet-finite-limits`), over any
base: it preserves finite coproducts and quotients by finite monoids, and coequalizers are
quotients by an action of `ParallelPairMonoid`. -/
instance preservesFiniteColimits_fiber : PreservesFiniteColimits (fiber s) :=
  have := preservesColimitsOfShape_walkingParallelPair_of_singleObj.{u} (fiber s)
  preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts _

end FiberColimits

section Conservative

variable {Y : Scheme.{u}}

/-- A morphism of finite étale `Y`-schemes which is surjective on the geometric fibres at all
points of `Y` is surjective: the complement of its image is an open and closed subscheme with
empty geometric fibres, hence empty. -/
lemma surjective_of_forall_surjective_fiber {P Q : Y.FiniteEtale} (φ : P ⟶ Q)
    (h : ∀ y : Y, Function.Surjective ((fiber (Y.algClosurePoint y)).map φ)) :
    Function.Surjective φ.hom.left := by
  have hV : IsClosed (Set.range φ.hom.left) := φ.hom.left.isClosedMap.isClosed_range
  let W : Q.obj.left.Opens := ⟨(Set.range φ.hom.left)ᶜ, hV.isOpen_compl⟩
  have hW : IsClosed (W : Set Q.obj.left) :=
    isClosed_compl_iff.mpr φ.hom.left.isOpenMap.isOpen_range
  intro q
  by_contra hq
  let s := Y.algClosurePoint (Q.obj.hom q)
  have : IsFinite (ofIsClopen Q W hW).obj.hom := (ofIsClopen Q W hW).property
  have : Etale (ofIsClopen Q W hW).obj.hom := (ofIsClopen Q W hW).obj.prop
  obtain ⟨t, ht⟩ := (ofIsClopen Q W hW).obj.hom.exists_lift_of_isSepClosed s
    ⟨default, (⟨q, hq⟩ : (W : Set Q.obj.left)), (Y.algClosurePoint_base _ _).symm⟩
  let x : (fiber s).obj (ofIsClopen Q W hW) := Over.homMk t ht
  obtain ⟨z, hz⟩ := h (Q.obj.hom q) ((fiber s).map (ofIsClopenι Q W hW) x)
  have := congr_arg (fun y : (fiber s).obj Q ↦ (y.left : Spec (.of _) ⟶ Q.obj.left)
    (default : Spec (.of _))) hz
  simp only [fiber_map_left, Scheme.Hom.comp_apply] at this
  let w : (W : Set Q.obj.left) := x.left (default : Spec (.of _))
  exact w.2 ⟨_, this⟩

/-- A monomorphism of finite étale `Y`-schemes which is surjective on the geometric fibres at all
points of `Y` is an isomorphism: it is a surjective open immersion. -/
lemma isIso_of_mono_of_forall_surjective_fiber {P Q : Y.FiniteEtale} (i : P ⟶ Q) [Mono i]
    (h : ∀ y : Y, Function.Surjective ((fiber (Y.algClosurePoint y)).map i)) : IsIso i := by
  have : IsOpenImmersion i.hom.left := IsOpenImmersion.of_flat_of_mono _
  have : IsIso ((forgetScheme Y).map i) :=
    (isIso_iff_isOpenImmersion_and_surjective i.hom.left).mpr
      ⟨inferInstance, ⟨surjective_of_forall_surjective_fiber i h⟩⟩
  exact isIso_of_reflects_iso i (forgetScheme Y)

/-- If a morphism `f : P ⟶ Q` of finite étale `Y`-schemes is bijective on a geometric fibre, then
the diagonal `P ⟶ P ×_Q P` is surjective on that fibre. -/
lemma surjective_fiber_map_diagonal {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ Y) {P Q : Y.FiniteEtale} (f : P ⟶ Q) [IsIso ((fiber s).map f)] :
    Function.Surjective
      ((fiber s).map (Limits.pullback.lift (𝟙 P) (𝟙 P) rfl : P ⟶ Limits.pullback f f)) := by
  have hbij : Function.Bijective ((fiber s).map f) := ConcreteCategory.bijective_of_isIso _
  let δ : P ⟶ Limits.pullback f f := Limits.pullback.lift (𝟙 P) (𝟙 P) rfl
  intro e
  let hD := isLimitOfPreserves (fiber s ⋙ FintypeCat.incl) (pullbackIsPullback f f)
  have hfs : (fiber s).map f ((fiber s).map (Limits.pullback.fst f f) e) =
      (fiber s).map f ((fiber s).map (Limits.pullback.snd f f) e) := by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp, Limits.pullback.condition]
  have hab := hbij.1 hfs
  set a := (fiber s).map (Limits.pullback.fst f f) e
  have hfst : (fiber s).map (Limits.pullback.fst f f) ((fiber s).map δ a) = a := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, Limits.pullback.lift_fst,
      CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
  have hsnd : (fiber s).map (Limits.pullback.snd f f) ((fiber s).map δ a) = a := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, Limits.pullback.lift_snd,
      CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
  refine ⟨a, (Concrete.isLimit_ext _ hD _ _ ?_).symm⟩
  rintro (_ | _ | _)
  · change (fiber s).map (Limits.pullback.fst f f ≫ f) e =
      (fiber s).map (Limits.pullback.fst f f ≫ f) ((fiber s).map δ a)
    rw [Functor.map_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hfst]
  · change (fiber s).map (Limits.pullback.fst f f) e =
      (fiber s).map (Limits.pullback.fst f f) ((fiber s).map δ a)
    exact hfst.symm
  · change (fiber s).map (Limits.pullback.snd f f) e =
      (fiber s).map (Limits.pullback.snd f f) ((fiber s).map δ a)
    rw [hsnd]
    exact hab.symm

/-- **The fibre functors jointly reflect isomorphisms** (blueprint `lem-fet-finite-limits`): a
morphism of finite étale `Y`-schemes which is bijective on the geometric fibres at all points of
`Y` is an isomorphism. -/
lemma isIso_of_forall_isIso_fiber_map {P Q : Y.FiniteEtale} (f : P ⟶ Q)
    (h : ∀ y : Y, IsIso ((fiber (Y.algClosurePoint y)).map f)) : IsIso f := by
  let δ : P ⟶ Limits.pullback f f := Limits.pullback.lift (𝟙 P) (𝟙 P) rfl
  have : IsSplitMono δ := IsSplitMono.mk' ⟨Limits.pullback.fst f f, by simp [δ]⟩
  have : IsIso δ := isIso_of_mono_of_forall_surjective_fiber δ fun y ↦
    have := h y
    surjective_fiber_map_diagonal _ f
  have hfs : Limits.pullback.fst f f = Limits.pullback.snd f f := by
    rw [← cancel_epi δ, Limits.pullback.lift_fst, Limits.pullback.lift_snd]
  have : Mono f := ⟨fun g h hgh ↦ by
    rw [← Limits.pullback.lift_fst g h hgh, hfs, Limits.pullback.lift_snd]⟩
  exact isIso_of_mono_of_forall_surjective_fiber f fun y ↦
    (ConcreteCategory.bijective_of_isIso ((fiber (Y.algClosurePoint y)).map f)).2

end Conservative

section BaseChange

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Base change of finite étale schemes preserves limits of finite shape. -/
lemma preservesLimitsOfShape_pullback (J : Type) [SmallCategory J] [FinCategory J] :
    PreservesLimitsOfShape J (pullback f) where
  preservesLimit {K} := ⟨fun {c} hc ↦ ⟨by
    let d := limit.isLimit (K ⋙ pullback f)
    have : IsIso (d.lift ((pullback f).mapCone c)) := by
      refine isIso_of_forall_isIso_fiber_map _ fun x ↦ ?_
      let s := X.algClosurePoint x
      have : PreservesLimit K (pullback f ⋙ fiber s) :=
        preservesLimit_of_natIso K (pullbackFiberIso f s).symm
      let φ := (Cone.functoriality (K ⋙ pullback f) (fiber s)).map
        (d.liftConeMorphism ((pullback f).mapCone c))
      have : IsIso φ := IsLimit.hom_isIso
        (isLimitOfPreserves (pullback f ⋙ fiber s) hc) (isLimitOfPreserves (fiber s) d) φ
      exact (Cone.forget _).map_isIso φ
    exact IsLimit.ofPointIso d⟩⟩

/-- Base change of finite étale schemes preserves colimits of finite shape. -/
lemma preservesColimitsOfShape_pullback (J : Type) [SmallCategory J] [FinCategory J] :
    PreservesColimitsOfShape J (pullback f) where
  preservesColimit {K} := ⟨fun {c} hc ↦ ⟨by
    let d := colimit.isColimit (K ⋙ pullback f)
    have : IsIso (d.desc ((pullback f).mapCocone c)) := by
      refine isIso_of_forall_isIso_fiber_map _ fun x ↦ ?_
      let s := X.algClosurePoint x
      have : PreservesColimit K (pullback f ⋙ fiber s) :=
        preservesColimit_of_natIso K (pullbackFiberIso f s).symm
      let φ := (Cocone.functoriality (K ⋙ pullback f) (fiber s)).map
        (d.descCoconeMorphism ((pullback f).mapCocone c))
      have : IsIso φ := IsColimit.hom_isIso
        (isColimitOfPreserves (fiber s) d) (isColimitOfPreserves (pullback f ⋙ fiber s) hc) φ
      exact (Cocone.forget _).map_isIso φ
    exact IsColimit.ofPointIso d⟩⟩

/-- **Base change of finite étale schemes preserves finite limits** (blueprint
`lem-fet-finite-limits`). -/
instance preservesFiniteLimits_pullback : PreservesFiniteLimits (pullback f) :=
  ⟨fun J _ _ ↦ preservesLimitsOfShape_pullback f J⟩

/-- **Base change of finite étale schemes preserves finite colimits** (blueprint
`lem-fet-finite-limits`). -/
instance preservesFiniteColimits_pullback : PreservesFiniteColimits (pullback f) :=
  ⟨fun J _ _ ↦ preservesColimitsOfShape_pullback f J⟩

end BaseChange

end AlgebraicGeometry.Scheme.FiniteEtale
