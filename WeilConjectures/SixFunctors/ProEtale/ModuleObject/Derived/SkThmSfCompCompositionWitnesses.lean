/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SkThmSfCompComposition

/-!
# Named witnesses of compact-support composition and base change

`sk_thm_sf_comp_composition` asserts six nested existential witnesses with one law
conjunction. Selecting them one `Exists.choose` at a time makes every later type mention the
earlier choices, and elaboration and kernel checking then time out. Here the six witnesses
are the fields of one structure, `sk_thm_sf_comp_composition_witnesses` repackages Q76's
theorem with the same law conjunction, and `compCompositionWitnesses` chooses the package
once. Its fields have Q76's small types.

Source: sk-thm-sf-comp-composition, clauses (1)--(2) (blueprint: sk-thm-sf-comp-composition).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 1024

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open CompactSupportComposition

/-- The six witness families of `sk_thm_sf_comp_composition`, field for field, with Q76's
own types: compact-support preservation, the compactification comparison, the composition
isomorphism alpha, the open base-change comparison, pullback preservation and the
compact-support exchange.
Source: sk-thm-sf-comp-composition, clauses (1)--(2) (blueprint: sk-thm-sf-comp-composition). -/
structure CompCompositionWitnesses (k : Type u) [Field k]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ] where
  preserves : ∀ {X Y : SepFinType k} (f : X ⟶ Y) (c : Compactification f.hom.left),
    (∀ K, localizingClosureProEtale Λ X.obj.left K →
      localizingClosureProEtale Λ Y.obj.left
        ((rightDerivedLowerShriekOfCompactification Λ c).obj K)) ∧
    (∀ K, (constantModelBoundedConstructible Λ X.obj.left K ∧
        DerivedCategory.finiteTorAmplitude _ K) →
      constantModelBoundedConstructible Λ Y.obj.left
          ((rightDerivedLowerShriekOfCompactification Λ c).obj K) ∧
        DerivedCategory.finiteTorAmplitude _
          ((rightDerivedLowerShriekOfCompactification Λ c).obj K))
  comparison : ∀ {X Y : SepFinType k} (f : X ⟶ Y) (c d : Compactification f.hom.left),
    (localizingClosureProEtale Λ X.obj.left).ι ⋙
        rightDerivedLowerShriekOfCompactification Λ c ≅
      (localizingClosureProEtale Λ X.obj.left).ι ⋙
        rightDerivedLowerShriekOfCompactification Λ d
  comp : ∀ {X Y Z : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z)
      (c : Compactification f.hom.left) (d : Compactification g.hom.left)
      (e : Compactification (f.hom.left ≫ g.hom.left)),
    (localizingClosureProEtale Λ X.obj.left).ι ⋙
        (rightDerivedLowerShriekOfCompactification Λ c ⋙
          rightDerivedLowerShriekOfCompactification Λ d) ≅
      (localizingClosureProEtale Λ X.obj.left).ι ⋙
        rightDerivedLowerShriekOfCompactification Λ e
  openIso : ∀ {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {a : X' ⟶ X} {v : Y' ⟶ Y}
      (sq : IsPullback a.hom.left f'.hom.left f.hom.left v.hom.left)
      (c : Compactification f.hom.left),
    D((c.i)_!open⟦Λ⟧) ⋙ moduleObjectDerivedPullback Λ (pullback.fst c.g v.hom.left) ≅
      moduleObjectDerivedPullback Λ a.hom.left ⋙ D(((c.ofIsPullback sq).i)_!open⟦Λ⟧)
  pullback_preserves : ∀ (X Y : SepFinType k) (v : X ⟶ Y),
    (∀ K, localizingClosureProEtale Λ Y.obj.left K →
      localizingClosureProEtale Λ X.obj.left ((moduleObjectDerivedPullback Λ v.hom.left).obj K)) ∧
    (∀ K, (constantModelBoundedConstructible Λ Y.obj.left K ∧
        DerivedCategory.finiteTorAmplitude _ K) →
      constantModelBoundedConstructible Λ X.obj.left
          ((moduleObjectDerivedPullback Λ v.hom.left).obj K) ∧
        DerivedCategory.finiteTorAmplitude _ ((moduleObjectDerivedPullback Λ v.hom.left).obj K))
  exchange : ∀ {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {a : X' ⟶ X} {v : Y' ⟶ Y}
      (_sq : IsPullback a.hom.left f'.hom.left f.hom.left v.hom.left)
      (c : Compactification f.hom.left) (d : Compactification f'.hom.left),
    (localizingClosureProEtale Λ X.obj.left).ι ⋙
        (rightDerivedLowerShriekOfCompactification Λ c ⋙ moduleObjectDerivedPullback Λ v.hom.left) ≅
      (localizingClosureProEtale Λ X.obj.left).ι ⋙
        (moduleObjectDerivedPullback Λ a.hom.left ⋙ rightDerivedLowerShriekOfCompactification Λ d)

set_option maxHeartbeats 2000000 in
-- The law conjunction is Q76's twelve clauses; matching it against Q76's statement needs more
-- than the default budget.
/-- `sk_thm_sf_comp_composition` with its six witnesses as the fields of one package. The
law conjunction is Q76's, verbatim, read on those fields; nothing is added or dropped.
Source: sk-thm-sf-comp-composition, clauses (1)--(2) (blueprint: sk-thm-sf-comp-composition).
Proof: eliminate the six existentials of `sk_thm_sf_comp_composition` and repackage the
witnesses; the law conjunction is the same proposition. -/
theorem sk_thm_sf_comp_composition_witnesses
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hk : Finite k ∨ IsAlgClosed k)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    ∃ H : CompCompositionWitnesses k Λ,
  -- refinement
  (∀ {X Y : SepFinType k} (f : X ⟶ Y)
      (c d : Compactification f.hom.left)
      (r : Compactification.DenseBoundaryCompactification f.hom.left)
      [QuasiCompact f.hom.left]
      (hc : r.obj ⟶ detSfBoundaryCompactification c)
      (hd : r.obj ⟶ detSfBoundaryCompactification d)
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (H.comparison f c d).hom.app K ≫ compactificationRefinementComponent Λ hd K.obj =
      compactificationRefinementComponent Λ hc K.obj) ∧
  -- comparison_id
  (∀ {X Y : SepFinType k} (f : X ⟶ Y) (c : Compactification f.hom.left),
    H.comparison f c c = Iso.refl _) ∧
  -- comparison_cocycle
  (∀ {X Y : SepFinType k} (f : X ⟶ Y)
      (c d e : Compactification f.hom.left),
    H.comparison f c d ≪≫ H.comparison f d e = H.comparison f c e) ∧
  -- comp_normalized
  (∀ {X Y Z : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z)
      (T : Compactification.Triangle f.hom.left g.hom.left)
      (_hT : IsSchemeTheoreticallyDominant T.q)
      [QuasiCompact (T.cf.g ≫ T.cg.i)]
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    ∃ m, compositionInterchangeIsNormalized Λ T.cf.g T.cg.i
        (detSfBoundaryCompactification (middle T))
        (D((T.cf.i)_!open⟦Λ⟧).obj K.obj) m ∧
      (H.comp f g T.cf T.cg T.cfg).hom.app K =
        R((T.cg.g)_*⟦Λ⟧).map
          (m ≫ R((T.p)_*⟦Λ⟧).map
            ((openFactor Λ T.cf.i T.q T.cfg.i T.i_q).hom.app K.obj)) ≫
          (rightDerivedLowerStarComp Λ T.p T.cg.g).hom.app
            (D((T.cfg.i)_!open⟦Λ⟧).obj K.obj) ≫
          (Functor.rightDerivedFunctorNatIso
            (eqToIso (congrArg (lowerStar Λ) T.p_g))).hom.app
              (D((T.cfg.i)_!open⟦Λ⟧).obj K.obj)) ∧
  -- comp_independent
  (∀ {X Y Z : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z)
      (c c' : Compactification f.hom.left) (d d' : Compactification g.hom.left)
      (e e' : Compactification (f.hom.left ≫ g.hom.left))
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (H.comp f g c d e).hom.app K ≫ (H.comparison (f ≫ g) e e').hom.app K =
      (rightDerivedLowerShriekOfCompactification Λ d).map ((H.comparison f c c').hom.app K) ≫
        (H.comparison g d d').hom.app
          ⟨_, (H.preserves f c').1 K.obj K.property⟩ ≫ (H.comp f g c' d' e').hom.app K) ∧
  -- unit_left
  (∀ {X Y : SepFinType k} (f : X ⟶ Y) (c : Compactification f.hom.left)
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (H.comp (𝟙 X) f (Compactification.ofIsProper (𝟙 X.obj.left)) c
      (c.copy (Category.id_comp f.hom.left))).hom.app K =
      (rightDerivedLowerShriekOfCompactification Λ c).map ((identity Λ X.obj.left).hom.app K.obj)) ∧
  -- unit_right
  (∀ {X Y : SepFinType k} (f : X ⟶ Y) (c : Compactification f.hom.left)
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (H.comp f (𝟙 Y) c (Compactification.ofIsProper (𝟙 Y.obj.left))
      (c.copy (Category.comp_id f.hom.left))).hom.app K =
      (identity Λ Y.obj.left).hom.app ((rightDerivedLowerShriekOfCompactification Λ c).obj K.obj)) ∧
  -- assoc
  (∀ {X Y Z W : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
      (c : Compactification f.hom.left) (d : Compactification g.hom.left)
      (e : Compactification h.hom.left)
      (cd : Compactification (f.hom.left ≫ g.hom.left))
      (de : Compactification (g.hom.left ≫ h.hom.left))
      (cde : Compactification ((f.hom.left ≫ g.hom.left) ≫ h.hom.left))
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (rightDerivedLowerShriekOfCompactification Λ e).map ((H.comp f g c d cd).hom.app K) ≫
        (H.comp (f ≫ g) h cd e cde).hom.app K =
      (H.comp g h d e de).hom.app ⟨_, (H.preserves f c).1 K.obj K.property⟩ ≫
        (H.comp f (g ≫ h) c de (cde.copy (Category.assoc _ _ _).symm)).hom.app K) ∧
  -- open_normalized
  (∀ {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {a : X' ⟶ X} {v : Y' ⟶ Y}
      (sq : IsPullback a.hom.left f'.hom.left f.hom.left v.hom.left)
      (c : Compactification f.hom.left),
    (H.openIso (a := a) (v := v) sq c).inv = openExchange Λ sq c) ∧
  -- exchange_normalized
  (∀ {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {a : X' ⟶ X} {v : Y' ⟶ Y}
      (sq : IsPullback a.hom.left f'.hom.left f.hom.left v.hom.left)
      (c : Compactification f.hom.left) (d : Compactification f'.hom.left)
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (H.exchange (a := a) (v := v) sq c d).hom.app K =
      (condensedAmbientExchange Λ (square (c.isPullback_g_ofIsPullback sq).flip)).app
          (D((c.i)_!open⟦Λ⟧).obj K.obj) ≫
        R(((c.ofIsPullback sq).g)_*⟦Λ⟧).map ((H.openIso (a := a) (v := v) sq c).hom.app K.obj) ≫
        (H.comparison f' (c.ofIsPullback sq) d).hom.app
          ⟨_, (H.pullback_preserves X' X a).1 K.obj K.property⟩) ∧
  -- exchange_independent
  (∀ {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {a : X' ⟶ X} {v : Y' ⟶ Y}
      (sq : IsPullback a.hom.left f'.hom.left f.hom.left v.hom.left)
      (c c' : Compactification f.hom.left) (d d' : Compactification f'.hom.left)
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (moduleObjectDerivedPullback Λ v.hom.left).map ((H.comparison f c c').hom.app K) ≫
        (H.exchange (a := a) (v := v) sq c' d').hom.app K =
      (H.exchange (a := a) (v := v) sq c d).hom.app K ≫ (H.comparison f' d d').hom.app
        ⟨_, (H.pullback_preserves X' X a).1 K.obj K.property⟩) ∧
  -- pasting
  (∀ {X Y X' Y' X'' Y'' : SepFinType k}
      {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
      {a : X' ⟶ X} {v : Y' ⟶ Y} {b : X'' ⟶ X'} {w : Y'' ⟶ Y'}
      (sq : IsPullback a.hom.left f'.hom.left f.hom.left v.hom.left)
      (sq' : IsPullback b.hom.left f''.hom.left f'.hom.left w.hom.left)
      (c : Compactification f.hom.left) (d : Compactification f'.hom.left)
      (e : Compactification f''.hom.left)
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (leftDerivedUpperStarComp Λ w.hom.left v.hom.left).hom.app
        ((rightDerivedLowerShriekOfCompactification Λ c).obj K.obj) ≫
      (moduleObjectDerivedPullback Λ w.hom.left).map
        ((H.exchange (a := a) (v := v) sq c d).hom.app K) ≫
      (H.exchange (a := b) (v := w) sq' d e).hom.app
        ⟨_, (H.pullback_preserves X' X a).1 K.obj K.property⟩ =
    (H.exchange (a := b ≫ a) (v := w ≫ v) (sq'.paste_horiz sq) c e).hom.app K ≫
      (rightDerivedLowerShriekOfCompactification Λ e).map
        ((leftDerivedUpperStarComp Λ b.hom.left a.hom.left).hom.app K.obj)) :=
  (sk_thm_sf_comp_composition ℓ k hk Λ hΛ).elim fun p hp =>
    hp.elim fun c hc => hc.elim fun m hm => hm.elim fun o ho => ho.elim fun b hb =>
      hb.elim fun e h => ⟨⟨p, c, m, o, b, e⟩, h⟩

/-- The comparison cocycle for the same single selected compact-support witness package.
Source: sk-thm-sf-comp-composition, comparison_cocycle clause, and
det-sf-comp-coherence-cocycle (blueprint: lem-sf-comp-witness-cocycle).

Proof: apply Exists.choose_spec to sk_thm_sf_comp_composition_witnesses and project
its third conjunct. The selected witness is definitionally compCompositionWitnesses.
The private proof above performs this projection literally, without re-elaborating
the large choice predicate. -/
theorem compCompositionWitnesses_comparison_cocycle
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hk : Finite k ∨ IsAlgClosed k)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {X Y : SepFinType k} (f : X ⟶ Y) (c d e : Compactification f.hom.left) :
    (compCompositionWitnesses ℓ k hk Λ hΛ).comparison f c d ≪≫
      (compCompositionWitnesses ℓ k hk Λ hΛ).comparison f d e =
        (compCompositionWitnesses ℓ k hk Λ hΛ).comparison f c e := by
  exact _private.Sheaf.SixFunctorsBasics.SkThmSfCompCompositionWitnesses.comparisonCocycle
    ℓ k hk Λ hΛ f c d e

/- The lawful witness package of `sk_thm_sf_comp_composition`, chosen once: the kernel
declaration `compCompositionWitnesses := fun params ↦
Exists.choose (sk_thm_sf_comp_composition_witnesses params)`. It is added directly, with
the choice predicate taken literally from the theorem's statement: the ordinary definition
elaborator abstracts the nested proofs of that predicate into auxiliary lemmas, and
re-identifying them with the theorem's statement exceeds the kernel's budget. -/
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let thm := ``sk_thm_sf_comp_composition_witnesses
  let name := `AlgebraicGeometry.ProEtale.CondensedRing.compCompositionWitnesses
  let info ← getConstInfo thm
  let lvls := info.levelParams.map Level.param
  let (type, value) ← forallTelescope info.type fun xs body => do
    let .app (.app (.const ``Exists [lv]) α) p := body
      | throwError "unexpected statement of {thm}"
    let h := mkAppN (.const thm lvls) xs
    let v := mkApp3 (.const ``Exists.choose [lv]) α p h
    return (← mkForallFVars xs α, ← mkLambdaFVars xs v)
  addDecl <| .defnDecl
    { name := name
      levelParams := info.levelParams
      type := type
      value := value
      hints := .opaque
      safety := .safe }
  modifyEnv fun env => addNoncomputable env name
  addDocStringCore name "The lawful witness package of `sk_thm_sf_comp_composition`, \
    chosen once: `Exists.choose` of `sk_thm_sf_comp_composition_witnesses`, whose law \
    conjunction is Q76's verbatim. A consumer takes the composition and exchange as fields \
    of this one package, so Q76's normalization laws hold for exactly those maps.\n\
    Source: sk-thm-sf-comp-composition (blueprint: sk-thm-sf-comp-composition)."

end AlgebraicGeometry.ProEtale.CondensedRing
