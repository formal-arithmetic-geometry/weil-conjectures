/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldPointFactorsThroughClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Morphisms.FrobeniusExistence
public import WeilConjectures.TraceFormula.Main

/-!

# The trace formula is additive over open–closed decompositions of the model

Let `X = X₀ ×_{k₀} k` with its model Frobenius `Φ` and let `X₀ = U₀ ⊔ Z₀` be a decomposition into
an open subscheme `j₀ : U₀ ⟶ X₀` and a closed complement `i₀ : Z₀ ⟶ X₀`. This file proves that
the trace formula over `U₀` and over `Z₀` gives the trace formula over `X₀`
(`ProEtale.CondensedRing.modelTraceFormula_of_isCompl`, blueprint `sk-i-global-additivity`,
used in `sk-thm-trace-formula`):

* the base changes `U = U₀ ×_{X₀} X` and `Z = Z₀ ×_{X₀} X` are models of `U₀` and `Z₀` with
  Frobenii `Φ_U`, `Φ_Z` compatible with `Φ` (`ProEtale.CondensedRing.modelBaseChange`,
  `ProEtale.CondensedRing.IsModelFrobenius.baseChange`);
* the rational points of `X` fixed by `Φ_m` are the disjoint union of those of `U` and of `Z`
  (`ProEtale.CondensedRing.fixedPointSumEquiv`);
* the global operator of the restriction `K|_U` is, up to isomorphism of Weil objects, the
  compactly supported Frobenius of the restriction of the iterate `(K, φ_m)`
  (`ProEtale.CondensedRing.WeilBoundedConstructible.trace_globalOperator_weilUpperStar`);
* additivity of the compactly supported Frobenius
  (`ProEtale.CondensedRing.WeilBoundedConstructible.trace_compactFrobenius_eq_add`) and the
  identification of the stalks of `K|_U` with those of `K`
  (`ProEtale.CondensedRing.WeilBoundedConstructible.trace_stalkFrobenius_weilUpperStar`) then
  assemble the trace formulas.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Base change of a subscheme of the model -/

section BaseChange

variable {k : Type u} [Field k] {X₀ : Scheme.{u}} {X : Over (Spec (.of k))} (p : X.left ⟶ X₀)
  {W₀ : Scheme.{u}} (e₀ : W₀ ⟶ X₀)

/-- The base change `W = W₀ ×_{X₀} X` of a morphism `e₀ : W₀ ⟶ X₀` along `p : X ⟶ X₀`, a scheme
over `Spec k` through `X`. -/
noncomputable abbrev modelBaseChange : Over (Spec (.of k)) :=
  Over.mk (pullback.snd e₀ p ≫ X.hom)

/-- The projection `W = W₀ ×_{X₀} X ⟶ X`, the base change of `e₀`. -/
noncomputable abbrev modelBaseChangeHom : modelBaseChange p e₀ ⟶ X :=
  Over.homMk (pullback.snd e₀ p)

variable {Φ : X ⟶ X} {F₀ : X₀ ⟶ X₀} {FW : W₀ ⟶ W₀}

/-- The endomorphism `Φ_W = F_W × Φ` of the base change `W = W₀ ×_{X₀} X`, for endomorphisms
`F_W` of `W₀` and `Φ` of `X` compatible with an endomorphism `F₀` of `X₀`. -/
noncomputable def modelBaseChangeEndo (hp : Φ.left ≫ p = p ≫ F₀) (hFW : FW ≫ e₀ = e₀ ≫ F₀) :
    modelBaseChange p e₀ ⟶ modelBaseChange p e₀ :=
  Over.homMk (pullback.lift (pullback.fst e₀ p ≫ FW) (pullback.snd e₀ p ≫ Φ.left) (by
    rw [Category.assoc, hFW, pullback.condition_assoc, Category.assoc, hp]))
    (by
      dsimp
      rw [pullback.lift_snd_assoc, Category.assoc, Over.w Φ])

lemma modelBaseChangeEndo_comp (hp : Φ.left ≫ p = p ≫ F₀) (hFW : FW ≫ e₀ = e₀ ≫ F₀) :
    modelBaseChangeEndo p e₀ hp hFW ≫ modelBaseChangeHom p e₀ =
      modelBaseChangeHom p e₀ ≫ Φ :=
  Over.OverMorphism.ext (by simp [modelBaseChangeEndo])

lemma modelBaseChangeEndo_left_comp (hp : Φ.left ≫ p = p ≫ F₀) (hFW : FW ≫ e₀ = e₀ ≫ F₀) :
    (modelBaseChangeEndo p e₀ hp hFW).left ≫ pullback.fst e₀ p = pullback.fst e₀ p ≫ FW := by
  simp [modelBaseChangeEndo]

variable {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k] {f₀ : X₀ ⟶ Spec (.of k₀)}

omit [Finite k₀] in
/-- The base change `W = W₀ ×_{X₀} X` of a subscheme of the model is a model of `W₀`, with the
model Frobenius `Φ_W = F_W × Φ`. -/
lemma IsModelFrobenius.baseChange (hΦ : IsModelFrobenius Φ f₀ p) (hp : Φ.left ≫ p = p ≫ F₀)
    (hFW : FW ≫ e₀ = e₀ ≫ F₀)
    (hFW' : FW.IsFrobenius (Nat.card k₀)) :
    IsModelFrobenius (modelBaseChangeEndo p e₀ hp hFW) (e₀ ≫ f₀) (pullback.fst e₀ p) where
  isPullback := (IsPullback.of_hasPullback e₀ p).paste_vert hΦ.isPullback
  exists_isFrobenius := ⟨FW, hFW', modelBaseChangeEndo_left_comp p e₀ hp hFW⟩

end BaseChange

/-! ### Fixed points of a decomposition -/

section FixedPoints

variable {k : Type u} [Field k] {X U Z : Over (Spec (.of k))} {Φ : X ⟶ X} {ΦU : U ⟶ U}
  {ΦZ : Z ⟶ Z} (j : U ⟶ X) (i : Z ⟶ X)

lemma rationalPoint_ext_of_mono {Y : Over (Spec (.of k))} (e : Y ⟶ X) [Mono e.left]
    {y y' : RationalPoint Y} (h : y ≫ e = y' ≫ e) : y = y' :=
  Over.OverMorphism.ext ((cancel_mono e.left).1 (congrArg CommaMorphism.left h))

lemma fixedPoint_of_comp {Y : Over (Spec (.of k))} (e : Y ⟶ X) [Mono e.left] {ΦY : Y ⟶ Y}
    (he : ΦY ≫ e = e ≫ Φ) {m : ℕ} {y : RationalPoint Y}
    (hy : (y ≫ e) ≫ frobeniusIterate Φ m = y ≫ e) : y ≫ frobeniusIterate ΦY m = y :=
  rationalPoint_ext_of_mono e (by rw [Category.assoc, frobeniusIterate_comp_of_comp he,
    ← Category.assoc, hy])

/-- A rational point of `X` whose point lies in the image of an open immersion `j : U ⟶ X` lifts
to a rational point of `U`. -/
lemma exists_rationalPoint_comp_of_isOpenImmersion [IsOpenImmersion j.left] (x : RationalPoint X)
    (hx : x.left.base (default : Spec (.of k)) ∈ Set.range j.left.base) :
    ∃ y : RationalPoint U, y ≫ j = x := by
  have hr : Set.range x.left.base ⊆ Set.range j.left.base := by
    rintro _ ⟨w, rfl⟩
    obtain rfl : w = (default : Spec (.of k)) := Subsingleton.elim (α := ↥(Spec (.of k))) _ _
    exact hx
  refine ⟨Over.homMk (IsOpenImmersion.lift j.left x.left hr) ?_,
    Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)⟩
  rw [← Over.w j, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w x]

/-- A rational point of `X` whose point lies in the image of a closed immersion `i : Z ⟶ X`
lifts to a rational point of `Z`. -/
lemma exists_rationalPoint_comp_of_isClosedImmersion [IsClosedImmersion i.left]
    (x : RationalPoint X)
    (hx : x.left.base (default : Spec (.of k)) ∈ Set.range i.left.base) :
    ∃ z : RationalPoint Z, z ≫ i = x := by
  obtain ⟨z₀, hz₀⟩ := hx
  obtain ⟨⟨s, hs, -⟩, -⟩ :=
    field_point_factors_through_closed_immersion i.left x.left z₀ hz₀.symm
  refine ⟨Over.homMk s ?_, Over.OverMorphism.ext hs⟩
  rw [← Over.w i, ← Category.assoc, hs, Over.w x]

variable {j i}

/-- The map `Fix(Φ_{U,m}) ⊔ Fix(Φ_{Z,m}) ⟶ Fix(Φ_m)` induced by `j : U ⟶ X` and `i : Z ⟶ X`. -/
noncomputable def fixedPointSumMap (hj : ΦU ≫ j = j ≫ Φ) (hi : ΦZ ≫ i = i ≫ Φ) (m : ℕ) :
    FixedPoint ΦU m ⊕ FixedPoint ΦZ m → FixedPoint Φ m :=
  Sum.elim (fun y ↦ ⟨y.1 ≫ j, comp_comp_frobeniusIterate_of_comp hj y.2⟩)
    (fun z ↦ ⟨z.1 ≫ i, comp_comp_frobeniusIterate_of_comp hi z.2⟩)

variable [IsOpenImmersion j.left] [IsClosedImmersion i.left]

lemma fixedPointSumMap_injective
    (hcompl : IsCompl (Set.range j.left.base) (Set.range i.left.base)) (hj : ΦU ≫ j = j ≫ Φ)
    (hi : ΦZ ≫ i = i ≫ Φ) (m : ℕ) : Function.Injective (fixedPointSumMap hj hi m) := by
  have key (y : RationalPoint U) (z : RationalPoint Z) (h : y ≫ j = z ≫ i) : False := by
    refine Set.disjoint_iff.1 hcompl.disjoint
      ⟨⟨y.left.base (default : Spec (.of k)), rfl⟩, ⟨z.left.base (default : Spec (.of k)), ?_⟩⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, ← h, Over.comp_left, Scheme.Hom.comp_apply]
  rintro (y | z) (y' | z') h <;> have h' := congrArg Subtype.val h
  · exact congrArg Sum.inl (Subtype.ext (rationalPoint_ext_of_mono j h'))
  · exact (key y.1 z'.1 h').elim
  · exact (key y'.1 z.1 h'.symm).elim
  · exact congrArg Sum.inr (Subtype.ext (rationalPoint_ext_of_mono i h'))

lemma fixedPointSumMap_surjective
    (hcompl : IsCompl (Set.range j.left.base) (Set.range i.left.base)) (hj : ΦU ≫ j = j ≫ Φ)
    (hi : ΦZ ≫ i = i ≫ Φ) (m : ℕ) : Function.Surjective (fixedPointSumMap hj hi m) := by
  intro x
  by_cases hU : x.1.left.base (default : Spec (.of k)) ∈ Set.range j.left.base
  · obtain ⟨y, hy⟩ := exists_rationalPoint_comp_of_isOpenImmersion j x.1 hU
    exact ⟨Sum.inl ⟨y, fixedPoint_of_comp j hj (by rw [hy]; exact x.2)⟩, Subtype.ext hy⟩
  · have hZ : x.1.left.base (default : Spec (.of k)) ∈ Set.range i.left.base :=
      hcompl.compl_eq ▸ hU
    obtain ⟨z, hz⟩ := exists_rationalPoint_comp_of_isClosedImmersion i x.1 hZ
    exact ⟨Sum.inr ⟨z, fixedPoint_of_comp i hi (by rw [hz]; exact x.2)⟩, Subtype.ext hz⟩

/-- The rational points of `X` fixed by `Φ_m` are the disjoint union of those of an open
subscheme `j : U ⟶ X` and of its closed complement `i : Z ⟶ X`, both stable under the
Frobenius. -/
noncomputable def fixedPointSumEquiv
    (hcompl : IsCompl (Set.range j.left.base) (Set.range i.left.base)) (hj : ΦU ≫ j = j ≫ Φ)
    (hi : ΦZ ≫ i = i ≫ Φ) (m : ℕ) : FixedPoint ΦU m ⊕ FixedPoint ΦZ m ≃ FixedPoint Φ m :=
  Equiv.ofBijective (fixedPointSumMap hj hi m)
    ⟨fixedPointSumMap_injective hcompl hj hi m, fixedPointSumMap_surjective hcompl hj hi m⟩

end FixedPoints

/-! ### Traces of compactly supported Frobenii -/

namespace WeilBoundedConstructible

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

attribute [local instance] boundedConstructibleBraiding

/-- Isomorphic Weil objects have compactly supported Frobenii of the same trace. -/
lemma trace_compactFrobenius_eq_of_iso {Φ : X ⟶ X} [IsFinite Φ.left]
    [IsUniversalHomeomorphism Φ.left] {S T : WeilBoundedConstructible ℓ Φ} (e : S ≅ T)
    [HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        S.carrier)]
    [HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        T.carrier)] :
    trace S.compactFrobenius = trace T.compactFrobenius :=
  trace_eq_of_iso
    (X := (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
      S.carrier)
    (X' := (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
      T.carrier)
    ((IsoAlgebra.forget _).mapIso ((weilCompactCohomology ℓ Φ).mapIso e)) _ _
    (frobenius_hom_naturality ((weilCompactCohomology ℓ Φ).mapIso e).hom)


omit [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] in
/-- Conjugating an endomorphism by `eqToHom` and transporting it back. -/
lemma eqToHom_conj_comp {C : Type*} [Category* C] {A A' : C} (h : A = A') (h' : A' = A)
    (f : A' ⟶ A') : (eqToHom h ≫ f ≫ eqToHom h') ≫ eqToHom h = eqToHom h ≫ f := by
  subst h
  simp

/-- The global operator `F_{c,m}` of `(K, φ)` has the trace of the compactly supported Frobenius
of the iterate `(K, φ_m)`, for any choice of duals. -/
lemma trace_globalOperator_eq {Φ : X ⟶ X} (K : WeilBoundedConstructible ℓ Φ) (m : ℕ)
    [IsFinite (frobeniusIterate Φ m).left] [IsUniversalHomeomorphism (frobeniusIterate Φ m).left]
    [HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        K.carrier)]
    [HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        (K.iterate m).carrier)] :
    trace (K.globalOperator m) = trace (K.iterate m).compactFrobenius := by
  have e : (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
      K.carrier =
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        (K.iterate m).carrier := by
    rw [iterate_carrier]
  refine trace_eq_of_iso (eqToIso e) _ _ ?_
  rw [globalOperator, eqToIso.hom]
  exact eqToHom_conj_comp _ _ _


variable {U : Over (Spec (.of k))} [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
  [IsSeparated U.hom] {j : U ⟶ X}

omit [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] in
/-- The computation behind `weilUpperStarIterateIso`, for abstract functors: transporting the
pullback structure of the iterate along an equality `A' = A` of carriers. -/
lemma weilUpperStarIterateIso_aux {C D : Type*} [Category* C] [Category* D] {F : D ⥤ D}
    {F' : C ⥤ C} {L G₁ G₂ : C ⥤ D} (P : G₁ ≅ L ⋙ F) (Q : G₂ ≅ F' ⋙ L) {A A' : C} (hA : A' = A)
    (φ : F'.obj A ⟶ A) {S T T' : D} (e₁ : S = F.obj (L.obj A')) (e₂ : G₁.obj A' = G₂.obj A')
    (e₃ : L.obj (F'.obj A') = L.obj (F'.obj A)) (e₄ : L.obj A = T) (e₅ : S = F.obj (L.obj A))
    (e₆ : G₁.obj A = G₂.obj A) (e₇ : L.obj A = T') (e₈ : T' = T) :
    eqToHom e₁ ≫ P.inv.app A' ≫ eqToHom e₂ ≫ Q.hom.app A' ≫ eqToHom e₃ ≫ L.map φ ≫ eqToHom e₄ =
      eqToHom e₅ ≫ P.inv.app A ≫ eqToHom e₆ ≫ Q.hom.app A ≫ L.map φ ≫ eqToHom e₇ ≫
        eqToHom e₈ := by
  subst hA e₈ e₇ e₅
  simp

/-- The iterates of the restriction `K|_U` of a Weil object along `j : U ⟶ X` are the
restrictions of the iterates of `K`: an isomorphism of Weil objects for `Φ_{U,m}`. -/
noncomputable def weilUpperStarIterateIso {ΦU : U ⟶ U} {Φ : X ⟶ X} (hj : ΦU ≫ j = j ≫ Φ)
    (K : WeilBoundedConstructible ℓ Φ) (m : ℕ) :
    ((weilUpperStar ℓ ΦU Φ j hj).obj K).iterate m ≅
      (weilUpperStar ℓ (frobeniusIterate ΦU m) (frobeniusIterate Φ m) j
        (frobeniusIterate_comp_of_comp hj m)).obj (K.iterate m) :=
  IsoAlgebra.isoMk (eqToIso (by
    rw [iterate_carrier, weilUpperStar_obj_carrier, weilUpperStar_obj_carrier, iterate_carrier]))
    (by
      rw [← IsoAlgebra.str_hom, ← IsoAlgebra.str_hom, weilUpperStar_obj_str, iterate_str,
        iterate_str]
      simp only [Iso.trans_hom, Functor.mapIso_hom]
      rw [weilUpperStar_iterateStr_hom]
      simp only [weilUpperStarComparison, boundedConstructiblePullbackSquareComparison,
        Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, eqToIso.inv, eqToIso.hom,
        NatTrans.comp_app, eqToHom_app, Category.assoc, Iso.app_hom,
        Functor.map_comp, eqToHom_map]
      exact weilUpperStarIterateIso_aux
        (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ
          (frobeniusIterate ΦU m) j)
        (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ j
          (frobeniusIterate Φ m))
        (iterate_carrier K m) (K.iterateStr m).hom _ _ _ _ _ _ _ _)


end WeilBoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing
