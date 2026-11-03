/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SectionInvariant
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.DetPropSfCbc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompCompositionBaseChange

/-!
# Dualizing objects on the Cartesian self-product

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-orientation-from-the-diagonal/sk-prop-sp-orientation/
lem-pur-diagonal-base-change.md and its companion proof
(blueprint: lem-pur-diagonal-base-change).

All objects use the pulled-back condensed coefficient ring and the recorded restricted Brown
exceptional inverse image. The two projections and the diagonal are the actual scheme pullback
maps, regarded as morphisms over the fixed base field.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (D : WeilConjectures.FiniteFieldDatum.{u})
  (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
  (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ) (hn : 1 ≤ n)
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  (hcoeff :
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
      (Padic.coefficientExtensionRing ell E n))) ∨
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E)) ∨
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))

namespace DiagonalBaseChange

variable {D} {X Y : Over (Spec (.of D.k))} (f : X ⟶ Y)

/-- The compact-support exchange for supplied compactifications, followed by a supplied
comparison on the localizing domain. This is the literal proper/open formalism exchange;
there is no choice of a new exchange or of a comparison.
Source: def-pur-co-smoothness (3), specified compact-support base change
(blueprint: lem-pur-diagonal-base-change). -/
def compactExchangeComposite
    {A B A' B' : Scheme.{u}} {q : A ⟶ B} {q' : A' ⟶ B'}
    {t : A' ⟶ A} {v : B' ⟶ B}
    (c : Compactification q) (cp c₂ : Compactification q') (h : cp.Z ⟶ c.Z)
    (hi : IsPullback t cp.i c.i h) (hb : IsPullback h cp.g c.g v)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology A) Ab.{u + 1}) (condensedRingObj Λ A)))
    (hK : localizingClosureProEtale Λ A' ((moduleObjectDerivedPullback Λ t).obj K))
    (e : ((localizingClosureProEtale Λ A').ι ⋙
        rightDerivedLowerShriekOfCompactification Λ cp) ≅
      ((localizingClosureProEtale Λ A').ι ⋙
        rightDerivedLowerShriekOfCompactification Λ c₂)) :
      (moduleObjectDerivedPullback Λ v).obj
          ((rightDerivedLowerShriekOfCompactification Λ c).obj K) ⟶
        (rightDerivedLowerShriekOfCompactification Λ c₂).obj
          ((moduleObjectDerivedPullback Λ t).obj K) :=
  ((compactSupportCondensedFormalism Λ).shriekBaseChange c cp h hi hb).natTrans.app K ≫
    e.hom.app ⟨(moduleObjectDerivedPullback Λ t).obj K, hK⟩

private def nativeSquare {A B C T : Scheme.{u}} {t : A ⟶ B} {l : A ⟶ C}
    {r : B ⟶ T} {v : C ⟶ T} (sq : IsPullback t l r v) :
    ChosenCartesianSquare t l r v :=
  { toCommSq := sq.toCommSq
    isoPullback := sq.isoPullback
    hom_fst := sq.isoPullback_hom_fst
    hom_snd := sq.isoPullback_hom_snd }

private theorem properFactor_isIso (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hΛ : IsLocalizingAdmissibleCoefficient ell Λ)
    {A B A' B' : Over (Spec (.of k))}
    [LocallyOfFiniteType A.hom] [QuasiCompact A.hom] [IsSeparated A.hom]
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
    (q : A ⟶ B) (v : B' ⟶ B) (q' : A' ⟶ B')
    (c : Compactification q.left) (cp : Compactification q'.left)
    (h : cp.Z ⟶ c.Z) (hb : IsPullback h cp.g c.g v.left)
    (K : ConstantModelConstructibleFiniteTor Λ A.left) :
    IsIso ((condensedAmbientExchange Λ (nativeSquare hb)).app
      ((openImmersionLowerShriek Λ c.i).mapDerivedCategory.obj K.obj)) := by
  let : A.left.Over (Spec (.of k)) := ⟨A.hom⟩
  let : B.left.Over (Spec (.of k)) := ⟨B.hom⟩
  let : B'.left.Over (Spec (.of k)) := ⟨B'.hom⟩
  have : LocallyOfFiniteType (A.left ↘ Spec (.of k)) := by
    change LocallyOfFiniteType A.hom
    infer_instance
  have : QuasiCompact (A.left ↘ Spec (.of k)) := by
    change QuasiCompact A.hom
    infer_instance
  have : IsSeparated (A.left ↘ Spec (.of k)) := by
    change IsSeparated A.hom
    infer_instance
  have : LocallyOfFiniteType (B.left ↘ Spec (.of k)) := by
    change LocallyOfFiniteType B.hom
    infer_instance
  have : QuasiCompact (B.left ↘ Spec (.of k)) := by
    change QuasiCompact B.hom
    infer_instance
  have : IsSeparated (B.left ↘ Spec (.of k)) := by
    change IsSeparated B.hom
    infer_instance
  have : LocallyOfFiniteType (B'.left ↘ Spec (.of k)) := by
    change LocallyOfFiniteType B'.hom
    infer_instance
  have : QuasiCompact (B'.left ↘ Spec (.of k)) := by
    change QuasiCompact B'.hom
    infer_instance
  have : IsSeparated (B'.left ↘ Spec (.of k)) := by
    change IsSeparated B'.hom
    infer_instance
  let : c.Z.Over (Spec (.of k)) := ⟨c.g ≫ B.hom⟩
  have : LocallyOfFiniteType (c.Z ↘ Spec (.of k)) := by
    change LocallyOfFiniteType (c.g ≫ B.hom)
    infer_instance
  have : QuasiCompact (c.Z ↘ Spec (.of k)) := by
    change QuasiCompact (c.g ≫ B.hom)
    infer_instance
  have : IsSeparated (c.Z ↘ Spec (.of k)) := by
    change IsSeparated (c.g ≫ B.hom)
    infer_instance
  have : c.g.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : v.left.IsOver (Spec (.of k)) := ⟨v.w⟩
  have : c.i.IsOver (Spec (.of k)) := ⟨by
    change c.i ≫ (c.g ≫ B.hom) = A.hom
    rw [← Category.assoc, ← c.comm]
    exact q.w⟩
  have hopen := openImmersionLowerShriek_localizing ell k (ringChar k)
    (Nat.Prime.pos (Fact.out : (ringChar k).Prime))
    (Fact.out : ringChar k ≠ ell) Λ hΛ c.i
  have hJ : localizingClosureProEtale Λ c.Z
      ((openImmersionLowerShriek Λ c.i).mapDerivedCategory.obj K.obj) := by
    as_aux_lemma => exact fun _ _ hS ↦ hS _ (hopen.1 K)
  let : cp.Z.Over (Spec (.of k)) := ⟨cp.g ≫ B'.hom⟩
  have : LocallyOfFiniteType (cp.Z ↘ Spec (.of k)) := by
    change LocallyOfFiniteType (cp.g ≫ B'.hom)
    infer_instance
  have : QuasiCompact (cp.Z ↘ Spec (.of k)) := by
    change QuasiCompact (cp.g ≫ B'.hom)
    infer_instance
  have : IsSeparated (cp.Z ↘ Spec (.of k)) := by
    change IsSeparated (cp.g ≫ B'.hom)
    infer_instance
  have : cp.g.IsOver (Spec (.of k)) := ⟨rfl⟩
  have hqc (T : Scheme.{u}) [T.Over (Spec (.of k))]
      [QuasiCompact (T ↘ Spec (.of k))] : CompactSpace T :=
    QuasiCompact.compactSpace_of_compactSpace (T ↘ Spec (.of k))
  have hqs (T : Scheme.{u}) [T.Over (Spec (.of k))]
      [IsSeparated (T ↘ Spec (.of k))] : QuasiSeparatedSpace T :=
    quasiSeparatedSpace_of_quasiSeparated (T ↘ Spec (.of k))
  have := hqc c.Z
  have := hqc B.left
  have := hqc B'.left
  have := hqc cp.Z
  have := hqs c.Z
  have := hqs B.left
  have := hqs B'.left
  have := hqs cp.Z
  exact properExchange_admissible ell Λ hΛ k c.g v.left (nativeSquare hb)
    (by as_aux_lemma =>
      exact properLocalizingHypotheses_admissible ell Λ hΛ k cp.g)
    (by as_aux_lemma =>
      exact (pullback_of_constructible Λ v.left (pullback_constructible Λ v.left)).some)
    (by as_aux_lemma =>
      exact (pullback_of_constructible Λ h (pullback_constructible Λ h)).some) _ hJ

private theorem formalismSquare_inv (F : CompactSupportFormalism)
    {A B C T : Scheme.{u}} (t : A ⟶ B) (l : A ⟶ C) (r : B ⟶ T) (b : C ⟶ T)
    (sq : IsPullback t l r b) :
    (F.sqIso t l r b sq.w).inv =
      ((F.pbComp l b).symm ≪≫
        eqToIso (congrArg (fun h : A ⟶ T ↦ F.pb h) sq.w.symm) ≪≫
        F.pbComp t r).hom := by
  simp only [ExchangeFormalism.sqIso, ExchangeFormalism.pbComp',
    Iso.trans_inv, Iso.symm_inv, Iso.trans_hom, Iso.symm_hom,
    eqToIso.inv, eqToIso.hom, eqToHom_refl, Category.id_comp,
    Category.assoc]

private theorem formalismProperExchange_eq
    {A B C T : Scheme.{u}} (t : A ⟶ B) (l : A ⟶ C) (r : B ⟶ T) (b : C ⟶ T)
    (sq : IsPullback t l r b) :
    ((compactSupportCondensedFormalism Λ).pfBaseChange t l r b sq.w).natTrans =
      condensedAmbientExchange Λ (nativeSquare sq) := by
  unfold ExchangeFormalism.pfBaseChange condensedAmbientExchange
  rw [formalismSquare_inv (compactSupportCondensedFormalism Λ) t l r b sq]
  rfl

private theorem shriekComponent_isIso (F : CompactSupportFormalism) [F.HasBaseChange]
    {A B A' B' : Scheme.{u}} {q : A ⟶ B} {q' : A' ⟶ B'}
    {t : A' ⟶ A} {v : B' ⟶ B}
    (c : Compactification q) (cp : Compactification q') (h : cp.Z ⟶ c.Z)
    (hi : IsPullback t cp.i c.i h) (hb : IsPullback h cp.g c.g v) (K : F.obj A)
    (hp : IsIso ((F.pfBaseChange h cp.g c.g v hb.w).natTrans.app
      ((F.sh c.i).obj K))) :
    IsIso ((F.shriekBaseChange c cp h hi hb).natTrans.app K) := by
  have hopen := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F) hi
  rw [CompactSupportFormalism.shriekBaseChange, ExchangeFormalism.shriekBaseChange_app]
  exact IsIso.comp_isIso' hp (by infer_instance)

private theorem formalismIsIso_iff (S : Scheme.{u})
    {A B : (compactSupportCondensedFormalism Λ).obj S} (m : A ⟶ B) :
    @IsIso _ ((compactSupportCondensedFormalism Λ).category S) A B m ↔
      @IsIso (DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)))
        (instCategoryDerivedCategory _) A B m := by
  rfl

private theorem formalismSh_obj_eq {S T : Scheme.{u}} (j : S ⟶ T)
    [IsOpenImmersion j]
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))) :
    ((compactSupportCondensedFormalism Λ).sh j).obj K =
      (openImmersionLowerShriek Λ j).mapDerivedCategory.obj K := by
  rfl

private theorem properNative_isIso_iff
    {A B C T S : Scheme.{u}} (t : A ⟶ B) (l : A ⟶ C) (r : B ⟶ T) (b : C ⟶ T)
    (sq : IsPullback t l r b) (j : S ⟶ B) [IsOpenImmersion j]
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))) :
    IsIso (((compactSupportCondensedFormalism Λ).pfBaseChange t l r b sq.w).natTrans.app
      (((compactSupportCondensedFormalism Λ).sh j).obj K)) ↔
      IsIso ((condensedAmbientExchange Λ (nativeSquare sq)).app
        ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj K)) := by
  rw [formalismIsIso_iff Λ C, formalismProperExchange_eq Λ t l r b sq,
    formalismSh_obj_eq Λ j K]

private theorem nativeShriek_isIso
    {A B A' B' : Scheme.{u}} {q : A ⟶ B} {q' : A' ⟶ B'}
    {t : A' ⟶ A} {v : B' ⟶ B}
    (c : Compactification q) (cp : Compactification q') (h : cp.Z ⟶ c.Z)
    (hi : IsPullback t cp.i c.i h) (hb : IsPullback h cp.g c.g v)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology A) Ab.{u + 1}) (condensedRingObj Λ A)))
    (hp : IsIso ((condensedAmbientExchange Λ (nativeSquare hb)).app
      ((openImmersionLowerShriek Λ c.i).mapDerivedCategory.obj K))) :
    IsIso (show
      (moduleObjectDerivedPullback Λ v).obj
          ((rightDerivedLowerShriekOfCompactification Λ c).obj K) ⟶
        (rightDerivedLowerShriekOfCompactification Λ cp).obj
          ((moduleObjectDerivedPullback Λ t).obj K) from
      ((compactSupportCondensedFormalism Λ).shriekBaseChange c cp h hi hb).natTrans.app K) := by
  exact (formalismIsIso_iff Λ B' _).1
    (shriekComponent_isIso (compactSupportCondensedFormalism Λ) c cp h hi hb K
      ((properNative_isIso_iff Λ h cp.g c.g v hb c.i K).2 hp))

private theorem nativeComposite_isIso
    {A B A' B' : Scheme.{u}} {q : A ⟶ B} {q' : A' ⟶ B'}
    {t : A' ⟶ A} {v : B' ⟶ B}
    (c : Compactification q) (cp c₂ : Compactification q') (h : cp.Z ⟶ c.Z)
    (hi : IsPullback t cp.i c.i h) (hb : IsPullback h cp.g c.g v)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology A) Ab.{u + 1}) (condensedRingObj Λ A)))
    (hp : IsIso ((condensedAmbientExchange Λ (nativeSquare hb)).app
      ((openImmersionLowerShriek Λ c.i).mapDerivedCategory.obj K)))
    (hK : localizingClosureProEtale Λ A' ((moduleObjectDerivedPullback Λ t).obj K))
    (e : ((localizingClosureProEtale Λ A').ι ⋙
        rightDerivedLowerShriekOfCompactification Λ cp) ≅
      ((localizingClosureProEtale Λ A').ι ⋙
        rightDerivedLowerShriekOfCompactification Λ c₂)) :
    IsIso (compactExchangeComposite Λ c cp c₂ h hi hb K hK e) := by
  unfold compactExchangeComposite
  exact IsIso.comp_isIso'
    (nativeShriek_isIso Λ c cp h hi hb K hp) (by infer_instance)

private theorem geometricComposite_isIso (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hΛ : IsLocalizingAdmissibleCoefficient ell Λ)
    {A B A' B' : Over (Spec (.of k))}
    [LocallyOfFiniteType A.hom] [QuasiCompact A.hom] [IsSeparated A.hom]
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
    (q : A ⟶ B) (t : A' ⟶ A) (q' : A' ⟶ B') (v : B' ⟶ B)
    (c : Compactification q.left) (cp c₂ : Compactification q'.left)
    (h : cp.Z ⟶ c.Z) (hi : IsPullback t.left cp.i c.i h)
    (hb : IsPullback h cp.g c.g v.left)
    (K : ConstantModelConstructibleFiniteTor Λ A.left)
    (hK : localizingClosureProEtale Λ A'.left
      ((moduleObjectDerivedPullback Λ t.left).obj K.obj))
    (e : ((localizingClosureProEtale Λ A'.left).ι ⋙
        rightDerivedLowerShriekOfCompactification Λ cp) ≅
      ((localizingClosureProEtale Λ A'.left).ι ⋙
        rightDerivedLowerShriekOfCompactification Λ c₂)) :
    IsIso (compactExchangeComposite Λ c cp c₂ h hi hb K.obj hK e) := by
  exact nativeComposite_isIso Λ c cp c₂ h hi hb K.obj
    (properFactor_isIso Λ ell k hΛ q v q' c cp h hb K) hK e

/-- The chosen scheme self-product with its induced field structure.
Source: lem-pur-diagonal-base-change.md, `W = X ×_Y X`
(blueprint: lem-pur-diagonal-base-change). -/
abbrev selfProduct : Over (Spec (.of D.k)) :=
  Over.mk (pullback.fst f.left f.left ≫ X.hom)

/-- The first projection, with its field-compatibility equation.
Source: lem-pur-diagonal-base-change.md, the left projection in the square
(blueprint: lem-pur-diagonal-base-change). -/
abbrev first : selfProduct f ⟶ X :=
  Over.homMk (pullback.fst f.left f.left) rfl

/-- The second projection, with its field-compatibility equation.
Source: lem-pur-diagonal-base-change.md, the top projection in the square
(blueprint: lem-pur-diagonal-base-change). -/
abbrev second : selfProduct f ⟶ X :=
  Over.homMk (pullback.snd f.left f.left) (by
    change pullback.snd f.left f.left ≫ X.hom = pullback.fst f.left f.left ≫ X.hom
    calc
      pullback.snd f.left f.left ≫ X.hom =
          (pullback.snd f.left f.left ≫ f.left) ≫ Y.hom := by rw [Category.assoc, f.w]
      _ = (pullback.fst f.left f.left ≫ f.left) ≫ Y.hom := by rw [pullback.condition]
      _ = pullback.fst f.left f.left ≫ X.hom := by rw [Category.assoc, f.w])

/-- The actual diagonal, with its induced morphism over the field.
Source: lem-pur-diagonal-base-change.md, the section Delta
(blueprint: lem-pur-diagonal-base-change). -/
abbrev diagonal : X ⟶ selfProduct f :=
  Over.homMk (pullback.diagonal f.left) (by
    change pullback.diagonal f.left ≫ pullback.fst f.left f.left ≫ X.hom = X.hom
    simp)

/-- The self-product remains locally of finite type over the fixed field.
Source: lem-pur-diagonal-base-change.md, base-change geometry
(blueprint: lem-pur-diagonal-base-change). -/
instance selfProductLocallyOfFiniteType
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType f.left] :
    LocallyOfFiniteType (selfProduct f).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.fst f.left f.left ≫ X.hom))

/-- The self-product remains quasi-compact over the fixed field.
Source: lem-pur-diagonal-base-change.md, standing finite-type setting
(blueprint: lem-pur-diagonal-base-change). -/
instance selfProductQuasiCompact [QuasiCompact X.hom] [QuasiCompact f.left] :
    QuasiCompact (selfProduct f).hom :=
  inferInstanceAs (QuasiCompact (pullback.fst f.left f.left ≫ X.hom))

/-- The self-product remains separated over the fixed field.
Source: lem-pur-diagonal-base-change.md, standing separated setting
(blueprint: lem-pur-diagonal-base-change). -/
instance selfProductIsSeparated [IsSeparated X.hom] [IsSeparated f.left] :
    IsSeparated (selfProduct f).hom :=
  inferInstanceAs (IsSeparated (pullback.fst f.left f.left ≫ X.hom))

/-- The existing LocallyOfFiniteType base-change instance, exposed through the bundled projection.
Source: lem-pur-diagonal-base-change.md, projection geometry
(blueprint: lem-pur-diagonal-base-change). -/
instance firstLocallyOfFiniteType [LocallyOfFiniteType f.left] :
    LocallyOfFiniteType (first f).left :=
  inferInstanceAs (LocallyOfFiniteType (pullback.fst f.left f.left))

/-- The existing QuasiCompact base-change instance, exposed through the bundled projection.
Source: lem-pur-diagonal-base-change.md, projection geometry
(blueprint: lem-pur-diagonal-base-change). -/
instance firstQuasiCompact [QuasiCompact f.left] : QuasiCompact (first f).left :=
  inferInstanceAs (QuasiCompact (pullback.fst f.left f.left))

/-- The existing IsSeparated base-change instance, exposed through the bundled projection.
Source: lem-pur-diagonal-base-change.md, projection geometry
(blueprint: lem-pur-diagonal-base-change). -/
instance firstIsSeparated [IsSeparated f.left] : IsSeparated (first f).left :=
  inferInstanceAs (IsSeparated (pullback.fst f.left f.left))

/-- The existing LocallyOfFiniteType base-change instance, exposed through the bundled projection.
Source: lem-pur-diagonal-base-change.md, projection geometry
(blueprint: lem-pur-diagonal-base-change). -/
instance secondLocallyOfFiniteType [LocallyOfFiniteType f.left] :
    LocallyOfFiniteType (second f).left :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd f.left f.left))

/-- The existing QuasiCompact base-change instance, exposed through the bundled projection.
Source: lem-pur-diagonal-base-change.md, projection geometry
(blueprint: lem-pur-diagonal-base-change). -/
instance secondQuasiCompact [QuasiCompact f.left] : QuasiCompact (second f).left :=
  inferInstanceAs (QuasiCompact (pullback.snd f.left f.left))

/-- The existing IsSeparated base-change instance, exposed through the bundled projection.
Source: lem-pur-diagonal-base-change.md, projection geometry
(blueprint: lem-pur-diagonal-base-change). -/
instance secondIsSeparated [IsSeparated f.left] : IsSeparated (second f).left :=
  inferInstanceAs (IsSeparated (pullback.snd f.left f.left))

/-- Smoothness of the first projection is the existing smooth base-change instance.
Source: lem-pur-diagonal-base-change.md, the first projection is smooth
(blueprint: lem-pur-diagonal-base-change). -/
instance firstSmooth [Smooth f.left] : Smooth (first f).left :=
  inferInstanceAs (Smooth (pullback.fst f.left f.left))

/-- The diagonal is the existing closed diagonal of the separated morphism.
Source: lem-pur-diagonal-base-change.md, the closed section Delta
(blueprint: lem-pur-diagonal-base-change). -/
instance diagonalIsClosedImmersion [IsSeparated f.left] :
    IsClosedImmersion (diagonal f).left :=
  inferInstanceAs (IsClosedImmersion (pullback.diagonal f.left))

variable (D)

variable [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]

/-- The literal unit with the membership proof of the landed section invariant.
Source: def-pur-section-invariant, coefficient unit
(blueprint: lem-pur-diagonal-base-change). -/
abbrev unitCtf : ConstantModelConstructibleFiniteTor Λ Y.left :=
  ⟨sectionInvariantUnit Λ Y.left, sectionInvariantUnit_mem D ell hell E n hn Λ hcoeff Y⟩

/-- Evaluate the existing ctf exceptional inverse image on its existing literal unit.
This abbreviation makes no new choice of right adjoint.
Source: def-pur-co-smoothness, omega_f = Rf! Lambda_Y
(blueprint: lem-pur-diagonal-base-change). -/
abbrev omegaCtf : ConstantModelConstructibleFiniteTor Λ X.left :=
  letI : Fintype D.k₀ := Fintype.ofFinite D.k₀
  letI : Fact D.p.Prime := ⟨D.prime⟩
  letI : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans (D.card_base.trans D.cardinality_eq))
  letI : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  letI : Fact (ringChar D.k).Prime := ⟨(ringChar.eq D.k D.p).symm ▸ D.prime⟩
  letI : Fact (ringChar D.k ≠ ell) := ⟨(ringChar.eq D.k D.p).symm ▸ hell.symm⟩
  letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  (ctfExceptionalInverseImage Λ ell D.k (BaseFieldFiniteCD.of_isAlgClosed ell D.k) f
    (sectionInvariant_admissible D ell hell E n hn Λ hcoeff)).obj
      (unitCtf D ell hell E n hn Λ hcoeff (Y := Y))

/-- The ambient object of precisely the existing ctf exceptional image of the unit.
Source: lem-pur-diagonal-base-change, both projection dualizing objects
(blueprint: lem-pur-diagonal-base-change). -/
abbrev omega := (omegaCtf D ell hell E n hn Λ hcoeff f).obj

variable {X' Y' : Over (Spec (.of D.k))}
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]

/-- Pullback preserves the actual ctf object property, for the helper objects in the beta mate.
Proof (postponed): inverse image pulls the finite constructible stratification back to a finite
constructible stratification. Exact module pullback preserves flat modules, hence a bounded
flat representative with a given Tor interval keeps that same interval. Intersect these two
properties; this is the pullback-stability input to the base-change clause of cohomological
smoothness. No membership is assumed as extra data.
Source: def-pur-co-smoothness (3), def-weil-derived-pullback-tensor-hom
(blueprint: lem-pur-diagonal-base-change). -/
theorem pullback_mem (g' : X' ⟶ X)
    (K : ConstantModelConstructibleFiniteTor Λ X.left) :
    (constantModelBoundedConstructible Λ X'.left ⊓ DerivedCategory.finiteTorAmplitude _)
      ((moduleObjectDerivedPullback Λ g'.left).obj K.obj) := by
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : CompactSpace X'.left := QuasiCompact.compactSpace_of_compactSpace X'.hom
  let : QuasiSeparatedSpace X.left :=
    (quasiSeparated_iff_quasiSeparatedSpace X.hom).mp inferInstance
  let : QuasiSeparatedSpace X'.left :=
    (quasiSeparated_iff_quasiSeparatedSpace X'.hom).mp inferInstance
  exact ⟨pullback_bounded_constructible Λ g'.left
    (pullback_constructible Λ g'.left) K.obj K.property.1,
    pullback_tor Λ g'.left K.obj K.property.2⟩

/-- The specified compact-support exchange, followed by the canonical common-refinement
comparison from the base-changed compactification to the chosen compactification of f'.
The proper factor is the unit-square-counit mate; the open factor is its normalized inverse.
Source: def-pur-co-smoothness (3), beta is transposed from compact-support base change
(blueprint: lem-pur-diagonal-base-change). -/
def compactExchange (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [LocallyOfFiniteType f'.left] [QuasiCompact f'.left] [IsSeparated f'.left]
    (sq : IsPullback g'.left f'.left f.left g.left)
    (K : ConstantModelConstructibleFiniteTor Λ X.left) :
    (moduleObjectDerivedPullback Λ g.left).obj
        ((rightDerivedLowerShriekOfCompactification Λ (compactificationOverField f)).obj K.obj) ⟶
      (rightDerivedLowerShriekOfCompactification Λ (compactificationOverField f')).obj
        ((moduleObjectDerivedPullback Λ g'.left).obj K.obj) :=
  letI : Fintype D.k₀ := Fintype.ofFinite D.k₀
  letI : Fact D.p.Prime := ⟨D.prime⟩
  letI : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans (D.card_base.trans D.cardinality_eq))
  letI : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  letI : Fact (ringChar D.k).Prime := ⟨(ringChar.eq D.k D.p).symm ▸ D.prime⟩
  letI : Fact (ringChar D.k ≠ ell) := ⟨(ringChar.eq D.k D.p).symm ▸ hell.symm⟩
  letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  letI : Y'.left.Over (Spec (.of D.k)) := ⟨Y'.hom⟩
  letI : LocallyOfFiniteType (Y'.left ↘ Spec (.of D.k)) := ‹LocallyOfFiniteType Y'.hom›
  letI : QuasiCompact (Y'.left ↘ Spec (.of D.k)) := ‹QuasiCompact Y'.hom›
  letI : IsSeparated (Y'.left ↘ Spec (.of D.k)) := ‹IsSeparated Y'.hom›
  let c := compactificationOverField f
  let cp := c.ofIsPullback sq
  compactExchangeComposite Λ c cp (compactificationOverField f')
    (pullback.fst c.g g.left) (c.isPullback_i_ofIsPullback sq)
    (c.isPullback_g_ofIsPullback sq).flip K.obj
    (fun _ _ hS ↦ hS _ (pullback_mem D Λ g' K))
    (detSfCanonicalCompactificationComparison Λ ell
      (sectionInvariant_admissible D ell hell E n hn Λ hcoeff) D.k f'.left
      cp (compactificationOverField f'))

/-- The specified compact-support exchange is invertible on ctf objects.
Proof: extension by zero preserves ctf objects, so its value lies in the localizing closure.
The existing admissible proper-base-change theorem makes the proper factor invertible there.
That exchange is the formalism's proper mate, by their common pullback-square compositor.
The component formula for the formalism's shriek exchange then combines this
proper mate with its invertible open mate. Finally compose with the canonical comparison
from the pulled-back compactification to the chosen one. This proves invertibility of the
specified map.
Source: def-pur-co-smoothness (3), compact-support base-change mate
(blueprint: lem-pur-diagonal-base-change). -/
theorem compactExchange_isIso (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [LocallyOfFiniteType f'.left] [QuasiCompact f'.left] [IsSeparated f'.left]
    (sq : IsPullback g'.left f'.left f.left g.left)
    (K : ConstantModelConstructibleFiniteTor Λ X.left) :
    IsIso (compactExchange D ell hell E n hn Λ hcoeff f g' f' g sq K) := by
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans (D.card_base.trans D.cardinality_eq))
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  let : Fact (ringChar D.k).Prime := ⟨(ringChar.eq D.k D.p).symm ▸ D.prime⟩
  let : Fact (ringChar D.k ≠ ell) := ⟨(ringChar.eq D.k D.p).symm ▸ hell.symm⟩
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let hΛ := sectionInvariant_admissible D ell hell E n hn Λ hcoeff
  let : Y'.left.Over (Spec (.of D.k)) := ⟨Y'.hom⟩
  let : LocallyOfFiniteType (Y'.left ↘ Spec (.of D.k)) := ‹LocallyOfFiniteType Y'.hom›
  let : QuasiCompact (Y'.left ↘ Spec (.of D.k)) := ‹QuasiCompact Y'.hom›
  let : IsSeparated (Y'.left ↘ Spec (.of D.k)) := ‹IsSeparated Y'.hom›
  let c := compactificationOverField f
  let c₂ := compactificationOverField f'
  change IsIso (compactExchangeComposite Λ c (c.ofIsPullback sq) c₂
    (pullback.fst c.g g.left) (c.isPullback_i_ofIsPullback sq)
    (c.isPullback_g_ofIsPullback sq).flip K.obj
    (fun _ _ hS ↦ hS _ (pullback_mem D Λ g' K))
    (detSfCanonicalCompactificationComparison Λ ell hΛ D.k f'.left
      (c.ofIsPullback sq) c₂))
  exact geometricComposite_isIso Λ ell D.k hΛ f g' f' g c (c.ofIsPullback sq) c₂
    (pullback.fst c.g g.left) (c.isPullback_i_ofIsPullback sq)
    (c.isPullback_g_ofIsPullback sq).flip K
    (fun _ _ hS ↦ hS _ (pullback_mem D Λ g' K))
    (detSfCanonicalCompactificationComparison Λ ell hΛ D.k f'.left
      (c.ofIsPullback sq) c₂)

/-- The canonical beta: transpose the inverse compact-support exchange, the pulled-back ctf
counit for f, and the literal-unit pullback comparison under the ctf adjunction for f'.
All functors and both adjunctions are the existing CondensedSixOperations declarations.
Source: def-pur-co-smoothness (3), specified dualizing base-change map
(blueprint: lem-pur-diagonal-base-change). -/
def beta (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [LocallyOfFiniteType f'.left] [QuasiCompact f'.left] [IsSeparated f'.left]
    (sq : IsPullback g'.left f'.left f.left g.left) :
    (moduleObjectDerivedPullback Λ g'.left).obj (omega D ell hell E n hn Λ hcoeff f) ⟶
      omega D ell hell E n hn Λ hcoeff f' :=
  letI : Fintype D.k₀ := Fintype.ofFinite D.k₀
  letI : Fact D.p.Prime := ⟨D.prime⟩
  letI : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans (D.card_base.trans D.cardinality_eq))
  letI : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  letI : Fact (ringChar D.k).Prime := ⟨(ringChar.eq D.k D.p).symm ▸ D.prime⟩
  letI : Fact (ringChar D.k ≠ ell) := ⟨(ringChar.eq D.k D.p).symm ▸ hell.symm⟩
  letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let hΛ := sectionInvariant_admissible D ell hell E n hn Λ hcoeff
  let hcd := BaseFieldFiniteCD.of_isAlgClosed ell D.k
  let A : ConstantModelConstructibleFiniteTor Λ X'.left :=
    ⟨(moduleObjectDerivedPullback Λ g'.left).obj (omega D ell hell E n hn Λ hcoeff f),
      pullback_mem D Λ g' (omegaCtf D ell hell E n hn Λ hcoeff f)⟩
  letI := compactExchange_isIso D ell hell E n hn Λ hcoeff f g' f' g sq
    (omegaCtf D ell hell E n hn Λ hcoeff f)
  let a : (ctfLowerShriek Λ ell D.k hcd f' hΛ).obj A ⟶
      unitCtf D ell hell E n hn Λ hcoeff (Y := Y') :=
    ⟨inv (compactExchange D ell hell E n hn Λ hcoeff f g' f' g sq
        (omegaCtf D ell hell E n hn Λ hcoeff f)) ≫
      (moduleObjectDerivedPullback Λ g.left).map
        ((ctfExceptionalAdjunction Λ ell D.k hcd f hΛ).counit.app
          (unitCtf D ell hell E n hn Λ hcoeff (Y := Y))).hom ≫
      (leftDerivedUpperStarUnitIso Λ g.left).hom⟩
  ((ctfExceptionalAdjunction Λ ell D.k hcd f' hΛ).homEquiv A
    (unitCtf D ell hell E n hn Λ hcoeff (Y := Y')) a).hom

/-- The Cartesian square in the exact projection ordering of the blueprint.
Source: lem-pur-diagonal-base-change, displayed square
(blueprint: lem-pur-diagonal-base-change). -/
def square : IsPullback (second f).left (first f).left f.left f.left :=
  (IsPullback.of_hasPullback f.left f.left).flip

/-- Beta for the square, with target omega_p1.
Source: lem-pur-diagonal-base-change, first dualizing comparison
(blueprint: lem-pur-diagonal-base-change). -/
abbrev firstBeta := beta D ell hell E n hn Λ hcoeff f (second f) (first f) f (square D f)

/-- Beta for the flipped square, with target omega_p2.
Source: lem-pur-diagonal-base-change, symmetric dualizing comparison
(blueprint: lem-pur-diagonal-base-change). -/
abbrev secondBeta := beta D ell hell E n hn Λ hcoeff f (first f) (second f) f (square D f).flip

/-- The first displayed isomorphism is precisely the inverse of the specified beta.
Source: lem-pur-diagonal-base-change, omega_p1 congruent Lp2* omega_f
(blueprint: lem-pur-diagonal-base-change). -/
def firstProjectionIso (h : IsIso (firstBeta D ell hell E n hn Λ hcoeff f)) :
    omega D ell hell E n hn Λ hcoeff (first f) ≅
      (moduleObjectDerivedPullback Λ (second f).left).obj
        (omega D ell hell E n hn Λ hcoeff f) :=
  letI := h
  (asIso (firstBeta D ell hell E n hn Λ hcoeff f)).symm

/-- The symmetric displayed isomorphism is the inverse of the flipped beta.
Source: lem-pur-diagonal-base-change, omega_p2 congruent Lp1* omega_f
(blueprint: lem-pur-diagonal-base-change). -/
def secondProjectionIso (h : IsIso (secondBeta D ell hell E n hn Λ hcoeff f)) :
    omega D ell hell E n hn Λ hcoeff (second f) ≅
      (moduleObjectDerivedPullback Λ (first f).left).obj
        (omega D ell hell E n hn Λ hcoeff f) :=
  letI := h
  (asIso (secondBeta D ell hell E n hn Λ hcoeff f)).symm

variable [Smooth f.left]

/-- The final arrow is the inverse pullback compositor, transport along p2 Delta = id,
and the canonical identity-pullback comparison. No endpoint isomorphism is chosen.
Source: lem-pur-diagonal-base-change, last arrow of the final display
(blueprint: lem-pur-diagonal-base-change). -/
def diagonalIdentityIso :
    (moduleObjectDerivedPullback Λ (diagonal f).left).obj
        ((moduleObjectDerivedPullback Λ (second f).left).obj
          (omega D ell hell E n hn Λ hcoeff f)) ≅
      omega D ell hell E n hn Λ hcoeff f :=
  ((leftDerivedUpperStarComp Λ (diagonal f).left (second f).left).app
    (omega D ell hell E n hn Λ hcoeff f)).symm ≪≫
  eqToIso (congrArg (fun g => (moduleObjectDerivedPullback Λ g).obj
    (omega D ell hell E n hn Λ hcoeff f))
    (by simp [diagonal, second] : (diagonal f).left ≫ (second f).left = 𝟙 X.left)) ≪≫
  (leftDerivedUpperStarId Λ X.left).app (omega D ell hell E n hn Λ hcoeff f)

/-- The entire specified chain from the landed section invariant to omega_f.
Its first factor is literally mapIso of beta inverse; its remaining factors are the
canonical compositor inverse and identity comparison defined above.
Source: lem-pur-diagonal-base-change, final displayed chain
(blueprint: lem-pur-diagonal-base-change). -/
def diagonalSectionIso (h : IsIso (firstBeta D ell hell E n hn Λ hcoeff f)) :
    sectionInvariant D ell hell E n hn Λ hcoeff X (selfProduct f)
        (first f) (diagonal f) (by ext; simp [diagonal, first]) ≅
      omega D ell hell E n hn Λ hcoeff f :=
  (moduleObjectDerivedPullback Λ (diagonal f).left).mapIso
      (firstProjectionIso D ell hell E n hn Λ hcoeff f h) ≪≫
    diagonalIdentityIso D ell hell E n hn Λ hcoeff f

variable (d : ℕ) [SmoothOfRelativeDimension d f.left]

include d in
/-- The self-product geometry and invertibility of the two specified cohomological-smoothness
base-change maps, together with the specified diagonal composite.

Proof (postponed), following the six blueprint steps:
1. Use the actual pullback and its diagonal to get the Cartesian square and both section laws.
2. Smoothness, pure relative dimension d, separatedness and finite type survive base change.
3. Apply thm-pur-cohomological-smoothness (3) to this square and its flip. The maps asserted
   invertible are exactly beta, defined using the ctf counit and ctf exceptional adjunction.
4. Unfold the landed sectionInvariant; apply LDelta* to the inverse of beta for p1.
5. Compose with the inverse of leftDerivedUpperStarComp for Delta and p2.
6. Transport p2 Delta to the identity, then apply leftDerivedUpperStarId. These are the
   actual factors of diagonalSectionIso, so its hom has the displayed composite.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-orientation-from-the-diagonal/sk-prop-sp-orientation/
lem-pur-diagonal-base-change.md and its companion proof
(blueprint: lem-pur-diagonal-base-change). -/
theorem diagonal_base_change :
    IsPullback (pullback.snd f.left f.left) (pullback.fst f.left f.left) f.left f.left ∧
    Smooth (pullback.fst f.left f.left) ∧
    (diagonal f).left ≫ (second f).left = 𝟙 X.left ∧
    IsIso (firstBeta D ell hell E n hn Λ hcoeff f) ∧
    IsIso (secondBeta D ell hell E n hn Λ hcoeff f) ∧
    (sectionInvariant D ell hell E n hn Λ hcoeff X (selfProduct f)
        (first f) (diagonal f) (by ext; simp [diagonal, first]) =
      (moduleObjectDerivedPullback Λ (diagonal f).left).obj
        (omega D ell hell E n hn Λ hcoeff (first f))) ∧
    ∀ h : IsIso (firstBeta D ell hell E n hn Λ hcoeff f),
      (diagonalSectionIso D ell hell E n hn Λ hcoeff f h).hom =
        (moduleObjectDerivedPullback Λ (diagonal f).left).map
            (firstProjectionIso D ell hell E n hn Λ hcoeff f h).hom ≫
          (leftDerivedUpperStarComp Λ (diagonal f).left (second f).left).inv.app
            (omega D ell hell E n hn Λ hcoeff f) ≫
          eqToHom (congrArg (fun g => (moduleObjectDerivedPullback Λ g).obj
            (omega D ell hell E n hn Λ hcoeff f))
            (by simp [diagonal, second] : (diagonal f).left ≫ (second f).left = 𝟙 X.left)) ≫
          (leftDerivedUpperStarId Λ X.left).hom.app (omega D ell hell E n hn Λ hcoeff f) := by
  sorry

end DiagonalBaseChange
end AlgebraicGeometry.ProEtale.CondensedRing
