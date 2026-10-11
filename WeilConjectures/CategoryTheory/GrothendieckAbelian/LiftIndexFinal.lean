/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension

/-!
# The lifts through a localization functor of a small site

For `h : P f` with `f : V ⟶ U`, the comma category indexing the pointwise left Kan extension
along the opposite of the localization functor `P.Over ⊤ V ⥤ P.Over ⊤ U` at `W` receives a
final functor from the discrete category of lifts of `W` through `f`, and the structure
morphisms of the comma objects in its image are isomorphisms
(`AlgebraicGeometry.SmallSite.exists_final_discrete_costructuredArrow_overMap`). This is the
form in which the projection formula for left Kan extensions
(`CategoryTheory.Functor.isIso_lanProjectionMap_app`) applies to extension by zero along an
étale morphism. The construction repeats the private one of
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.SmallSite

section LiftIndex

variable {P : MorphismProperty Scheme.{u}} {V U : Scheme.{u}}

/-- The type of lifts of `W : P.Over ⊤ U` through `f : V ⟶ U`: factorizations of the
structure morphism of `W` through `f`. It indexes the colimit computing the presheaf-level
left Kan extension along the localization functor of `h : P f`. -/
private def LiftIndex (f : V ⟶ U) (W : P.Over ⊤ U) : Type u :=
  {α : W.left ⟶ V // α ≫ f = W.hom}

namespace LiftIndex

variable [P.IsMultiplicative] [P.HasOfPostcompProperty P] {f : V ⟶ U} {W : P.Over ⊤ U}

omit [P.IsMultiplicative] in
/-- The lift of a `P`-scheme over `U` through `f` with `P f` satisfies `P`, by the
cancellation property `MorphismProperty.HasOfPostcompProperty P P`. -/
private lemma prop_val (h : P f) (α : LiftIndex f W) : P α.1 :=
  MorphismProperty.of_postcomp (W := P) (W' := P) α.1 f h (by rw [α.2]; exact W.prop)

/-- The `P`-scheme over `V` determined by a lift of `W : P.Over ⊤ U` through `f`. -/
private def toOver (h : P f) (α : LiftIndex f W) : P.Over ⊤ V :=
  MorphismProperty.Over.mk ⊤ α.1 (α.prop_val h)

/-- The comparison morphism from `W` to the image of `α.toOver` in `P.Over ⊤ U`; its
underlying morphism is the identity. -/
private def homToComp (h : P f) (α : LiftIndex f W) :
    W ⟶ (MorphismProperty.Over.map ⊤ h).obj (α.toOver h) :=
  MorphismProperty.Over.homMk (𝟙 W.left) ((Category.id_comp _).trans α.2)

/-- A lift of `W` through `f` identifies `W` with the image of a `P`-scheme over `V`
under the localization functor: the comparison morphism `LiftIndex.homToComp` is the
identity on underlying schemes. -/
private def isoComp (h : P f) (α : LiftIndex f W) :
    W ≅ (MorphismProperty.Over.map ⊤ h).obj (α.toOver h) where
  hom := α.homToComp h
  inv := MorphismProperty.Over.homMk (𝟙 W.left) ((Category.id_comp _).trans α.2.symm)
  hom_inv_id := by
    apply MorphismProperty.Over.Hom.ext
    exact Category.id_comp _
  inv_hom_id := by
    apply MorphismProperty.Over.Hom.ext
    exact Category.id_comp _

/-- The object of the comma category indexing the pointwise left Kan extension at `W`
associated with a lift `α`; for a monomorphism `f` it is terminal, see
`LiftIndex.isTerminalCostructuredArrow`. -/
private def costructuredArrow (h : P f) (α : LiftIndex f W) :
    CostructuredArrow (MorphismProperty.Over.map ⊤ h).op (op W) :=
  CostructuredArrow.mk (α.homToComp h).op

/-- The lift of `W` extracted from an object of the indexing comma category. -/
private def ofCostructuredArrow (h : P f) (W : P.Over ⊤ U)
    (s : CostructuredArrow (MorphismProperty.Over.map ⊤ h).op (op W)) :
    LiftIndex f W :=
  ⟨s.hom.unop.left ≫ s.left.unop.hom, by
    have hw : s.hom.unop.left ≫
        ((MorphismProperty.Over.map ⊤ h).obj s.left.unop).hom = W.hom :=
      MorphismProperty.Over.w s.hom.unop
    rw [Category.assoc]
    exact hw⟩

omit [P.HasOfPostcompProperty P] in
/-- If `W` has no lift through `f`, the indexing comma category is empty. -/
private lemma isEmpty_costructuredArrow (h : P f) (W : P.Over ⊤ U)
    (hempty : IsEmpty (LiftIndex f W)) :
    IsEmpty (CostructuredArrow (MorphismProperty.Over.map ⊤ h).op (op W)) :=
  ⟨fun s => hempty.elim (ofCostructuredArrow h W s)⟩

/-- For a monomorphism `f`, the comma object associated with a lift `α` of `W` is
terminal: the pointwise left Kan extension formula collapses to a single value. -/
private noncomputable def isTerminalCostructuredArrow (h : P f) [Mono f]
    (α : LiftIndex f W) :
    IsTerminal (α.costructuredArrow h) :=
  IsTerminal.ofUniqueHom
    (fun s =>
      CostructuredArrow.homMk
        (Quiver.Hom.op
          (MorphismProperty.Over.homMk s.hom.unop.left
            (by
              have hs : s.hom.unop.left ≫ s.left.unop.hom ≫ f = W.hom :=
                MorphismProperty.Over.w s.hom.unop
              exact (cancel_mono f).mp
                (((Category.assoc _ _ _).trans hs).trans α.2.symm)) :
            α.toOver h ⟶ s.left.unop))
        (by
          apply Quiver.Hom.unop_inj
          apply MorphismProperty.Over.Hom.ext
          exact Category.id_comp _))
    (fun s m => by
      ext
      apply Quiver.Hom.unop_inj
      apply MorphismProperty.Over.Hom.ext
      have hw := m.w
      apply_fun (fun z => z.unop.left) at hw
      exact (Category.id_comp _).symm.trans hw)

omit [P.HasOfPostcompProperty P] in
/-- The lift of `W` extracted from an object of the indexing comma category is constant along
the morphisms of the comma category. -/
private lemma ofCostructuredArrow_eq_of_hom (h : P f)
    {s t : CostructuredArrow (MorphismProperty.Over.map ⊤ h).op (op W)} (m : s ⟶ t) :
    ofCostructuredArrow h W s = ofCostructuredArrow h W t := by
  apply Subtype.ext
  have hw : s.hom.unop.left = t.hom.unop.left ≫ m.left.unop.left := by
    have := congrArg (fun z ↦ z.unop.left) (CostructuredArrow.w m)
    exact this.symm
  change s.hom.unop.left ≫ s.left.unop.hom = t.hom.unop.left ≫ t.left.unop.hom
  rw [hw, Category.assoc, MorphismProperty.Over.w m.left.unop]

/-- The lift of `W` extracted from the comma object associated with a lift `α` is `α`. -/
private lemma ofCostructuredArrow_costructuredArrow (h : P f) (α : LiftIndex f W) :
    ofCostructuredArrow h W (α.costructuredArrow h) = α :=
  Subtype.ext (Category.id_comp _)

/-- A morphism of the indexing comma category into the comma object associated with a lift
`α`, from an object inducing the lift `α`. -/
private def homCostructuredArrow (h : P f) (α : LiftIndex f W)
    (s : CostructuredArrow (MorphismProperty.Over.map ⊤ h).op (op W))
    (hs : ofCostructuredArrow h W s = α) : s ⟶ α.costructuredArrow h :=
  CostructuredArrow.homMk
    (Quiver.Hom.op
      (MorphismProperty.Over.homMk s.hom.unop.left (congrArg Subtype.val hs) :
        α.toOver h ⟶ s.left.unop))
    (by
      apply Quiver.Hom.unop_inj
      apply MorphismProperty.Over.Hom.ext
      exact Category.id_comp _)

/-- There is at most one morphism of the indexing comma category into the comma object
associated with a lift. -/
private lemma subsingleton_hom_costructuredArrow (h : P f) (α : LiftIndex f W)
    (s : CostructuredArrow (MorphismProperty.Over.map ⊤ h).op (op W)) :
    Subsingleton (s ⟶ α.costructuredArrow h) := by
  refine ⟨fun m m' ↦ ?_⟩
  ext
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  have hw := congrArg (fun z ↦ z.unop.left) m.w
  have hw' := congrArg (fun z ↦ z.unop.left) m'.w
  exact ((Category.id_comp _).symm.trans hw).trans
    (((Category.id_comp _).symm.trans hw').symm)

/-- The functor sending a lift `α` of `W` through `f` to the associated object of the indexing
comma category. -/
private def discreteFunctor (h : P f) :
    Discrete (LiftIndex f W) ⥤ CostructuredArrow (MorphismProperty.Over.map ⊤ h).op (op W) :=
  Discrete.functor (costructuredArrow h)

/-- The functor sending an object of the indexing comma category to the lift of `W` it
induces. -/
private def toDiscrete (h : P f) :
    CostructuredArrow (MorphismProperty.Over.map ⊤ h).op (op W) ⥤ Discrete (LiftIndex f W) where
  obj s := ⟨ofCostructuredArrow h W s⟩
  map m := Discrete.eqToHom (ofCostructuredArrow_eq_of_hom h m)

/-- The indexing comma category is the disjoint union, over the lifts `α` of `W` through `f`,
of categories with terminal object `α.costructuredArrow h`: sending an object to its lift is
left adjoint to `LiftIndex.discreteFunctor`. -/
private def toDiscreteAdjunction (h : P f) :
    toDiscrete (W := W) h ⊣ discreteFunctor h :=
  Adjunction.mkOfHomEquiv
    { homEquiv s α :=
        have := subsingleton_hom_costructuredArrow h α.as s
        { toFun e := homCostructuredArrow h α.as s (Discrete.eq_of_hom e)
          invFun m := Discrete.eqToHom ((ofCostructuredArrow_eq_of_hom h m).trans
            (ofCostructuredArrow_costructuredArrow h α.as))
          left_inv _ := Subsingleton.elim _ _
          right_inv _ := (subsingleton_hom_costructuredArrow h α.as s).elim _ _ }
      homEquiv_naturality_left_symm _ _ := Subsingleton.elim _ _
      homEquiv_naturality_right {s _ α} _ _ :=
        (subsingleton_hom_costructuredArrow h α.as s).elim _ _ }

/-- The inclusion of the lifts of `W` into the indexing comma category is final. -/
private lemma final_discreteFunctor (h : P f) : (discreteFunctor (W := W) h).Final :=
  Functor.final_of_adjunction (toDiscreteAdjunction h)

end LiftIndex

end LiftIndex

variable {P : MorphismProperty Scheme.{u}} {V U : Scheme.{u}}
  [P.IsMultiplicative] [P.HasOfPostcompProperty P] {f : V ⟶ U}

/-- The comma category indexing the pointwise left Kan extension along the opposite of the
localization functor of `h : P f` at `W` receives a final functor from a discrete category,
namely the lifts of `W` through `f`, whose comma objects have invertible structure maps. -/
theorem exists_final_discrete_costructuredArrow_overMap (h : P f) (W : P.Over ⊤ U) :
    ∃ (ι : Type u) (s : Discrete ι ⥤ CostructuredArrow (MorphismProperty.Over.map ⊤ h).op (op W)),
      s.Final ∧ ∀ i, IsIso (s.obj i).hom :=
  ⟨_, LiftIndex.discreteFunctor h, LiftIndex.final_discreteFunctor h, fun i ↦
    inferInstanceAs (IsIso (i.as.isoComp h).hom.op)⟩

end AlgebraicGeometry.SmallSite
