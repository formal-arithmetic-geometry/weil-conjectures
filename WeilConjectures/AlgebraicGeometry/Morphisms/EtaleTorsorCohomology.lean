/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorPullback
public import WeilConjectures.AlgebraicGeometry.Sites.UpperStarSections
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Naturality of the torsor attached to an étale `H¹`-class

Let `M` be a finite abelian group and `Y` a scheme. Every class `ξ ∈ H¹(Y_ét, M)` of the
constant sheaf `M` is the class of an `M`-torsor `t` over `Y`
(`AlgebraicGeometry.Scheme.EtaleTorsor.exists_quotientEquivSheafH`), and the classification
is natural in `Y`: the pullback of `ξ` along a morphism `f : Y' ⟶ Y` is the class of the
pulled-back torsor `t ×_Y Y'`. Since a torsor has class zero exactly when it has a section,
the pullback of `ξ` along `f` vanishes exactly when `f` lifts to the total space of `t`.

This is the form in which the vanishing theorem `sk-thm-vanishing` uses the classification:
it kills a class of `H¹` by pulling it back to a cover over which the torsor acquires a
section.

## Main definitions

- `AlgebraicGeometry.Scheme.EtaleTorsor.pullbackSheafTorsor`: for an `M`-torsor `P` over `Y`
  and `f : Y' ⟶ Y`, the sheaf of lifts `U ⟶ P` of `U ⟶ Y' ⟶ Y` on the small étale site of
  `Y'`, as a torsor under `U ↦ C(U, M)`.

## Main statements

- `AlgebraicGeometry.Scheme.EtaleTorsor.exists_forall_cohomologyMap_eq_zero_iff`: a class of
  `H¹(Y_ét, M)` is represented by an `M`-torsor `t`, in the sense that it dies after pullback
  along `f` exactly when `f` lifts to `t`.

## Implementation notes

Write `t` as the torsor of local lifts of a global section `s` of `Q` along `I ⟶ Q`, for an
injective resolution `0 → M → I → Q → 0`; then `ξ = δ(s)`. The pullback `f^*` is exact, so the
pullback of `ξ` is `δ'(s')` for the pulled-back sequence `0 → f^*M → f^*I → f^*Q → 0` and the
pulled-back section `s'`, and it vanishes iff the torsor of local lifts of `s'` to `f^*I` has a
global section. This torsor is identified with the torsor of lifts of `f` to `P`
(`AlgebraicGeometry.Scheme.EtaleTorsor.pullbackSheafTorsor`) by the equivariant map which sends
a lift `φ : U ⟶ P` to the pullback along `φ` of the tautological lift `x₀ ∈ I(P)` of `s`. The
pullback of sections is described only through the unit `I ⟶ f_* f^* I` of the adjunction
`f^* ⊣ f_*`, and its compatibility with constant sections comes from the definition of the
comparison `f^* M ≅ M` (`AlgebraicGeometry.Scheme.upperStarConstantSheafIso`) by uniqueness of
adjoints.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

/-! ### Pullback of sections along a morphism of schemes -/

namespace AlgebraicGeometry.Etale

section PullbackSection

variable {Y Y' : Scheme.{u}} (f : Y' ⟶ Y)

/-- The pullback of sections along `f : Y' ⟶ Y`: a section `x` of an abelian sheaf `G` over
`V` in the small étale site of `Y` gives, for every morphism `k : U ⟶ V ×_Y Y'` of the small
étale site of `Y'`, the section of `f^* G` over `U` obtained by restricting along `k` the image
of `x` under the unit `G ⟶ f_* f^* G`. -/
noncomputable def pullbackSection (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    {V : Y.Etale} {U : Y'.Etale} (k : U ⟶ f.Etale.obj V) :
    G.obj.obj (op V) ⟶ ((upperStar AddCommGrpCat.{u + 1} f).obj G).obj.obj (op U) :=
  ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app G).hom.app (op V) ≫
    ((upperStar AddCommGrpCat.{u + 1} f).obj G).obj.map k.op

variable (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})

lemma pullbackSection_comp_map {V : Y.Etale} {U W : Y'.Etale} (k : U ⟶ f.Etale.obj V)
    (h : W ⟶ U) :
    pullbackSection f G k ≫ ((upperStar AddCommGrpCat.{u + 1} f).obj G).obj.map h.op =
      pullbackSection f G (h ≫ k) := by
  rw [pullbackSection, pullbackSection, Category.assoc, ← Functor.map_comp, ← op_comp]

lemma map_pullbackSection {V : Y.Etale} {U W : Y'.Etale} (k : U ⟶ f.Etale.obj V) (h : W ⟶ U)
    (x : G.obj.obj (op V)) :
    ((upperStar AddCommGrpCat.{u + 1} f).obj G).obj.map h.op (pullbackSection f G k x) =
      pullbackSection f G (h ≫ k) x := by
  rw [← ConcreteCategory.comp_apply, pullbackSection_comp_map]

lemma map_comp_pullbackSection {V₁ V₂ : Y.Etale} (v : V₁ ⟶ V₂) {U : Y'.Etale}
    (k : U ⟶ f.Etale.obj V₁) :
    G.obj.map v.op ≫ pullbackSection f G k = pullbackSection f G (k ≫ f.Etale.map v) := by
  have hn : G.obj.map v.op ≫
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app G).hom.app (op V₁) =
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app G).hom.app (op V₂) ≫
        ((upperStar AddCommGrpCat.{u + 1} f).obj G).obj.map (f.Etale.map v).op :=
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app G).hom.naturality v.op
  rw [pullbackSection, pullbackSection, ← Category.assoc, hn, Category.assoc, ← Functor.map_comp,
    ← op_comp]

lemma pullbackSection_map {V₁ V₂ : Y.Etale} (v : V₁ ⟶ V₂) {U : Y'.Etale}
    (k : U ⟶ f.Etale.obj V₁) (x : G.obj.obj (op V₂)) :
    pullbackSection f G k (G.obj.map v.op x) = pullbackSection f G (k ≫ f.Etale.map v) x := by
  rw [← ConcreteCategory.comp_apply, map_comp_pullbackSection]

lemma pullbackSection_comp_upperStar_map {G' : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (φ : G ⟶ G') {V : Y.Etale} {U : Y'.Etale} (k : U ⟶ f.Etale.obj V) :
    pullbackSection f G k ≫ ((upperStar AddCommGrpCat.{u + 1} f).map φ).hom.app (op U) =
      φ.hom.app (op V) ≫ pullbackSection f G' k := by
  have hu : ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app G).hom.app (op V) ≫
      ((upperStar AddCommGrpCat.{u + 1} f).map φ).hom.app (op (f.Etale.obj V)) =
      φ.hom.app (op V) ≫
        ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app G').hom.app (op V) :=
    (congr_arg (fun g ↦ g.hom.app (op V))
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.naturality φ)).symm
  rw [pullbackSection, pullbackSection, Category.assoc,
    ← ((upperStar AddCommGrpCat.{u + 1} f).map φ).hom.naturality k.op, ← Category.assoc, hu,
    Category.assoc]

lemma pullbackSection_natural {G' : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (φ : G ⟶ G') {V : Y.Etale} {U : Y'.Etale} (k : U ⟶ f.Etale.obj V) (x : G.obj.obj (op V)) :
    ((upperStar AddCommGrpCat.{u + 1} f).map φ).hom.app (op U) (pullbackSection f G k x) =
      pullbackSection f G' k (φ.hom.app (op V) x) := by
  rw [← ConcreteCategory.comp_apply, pullbackSection_comp_upperStar_map,
    ConcreteCategory.comp_apply]

/-- The comparison morphism from the terminal object of the small étale site of `Y'` to the
base change of the terminal object of the small étale site of `Y`. -/
noncomputable abbrev terminalToEtale : ⊤_ Y'.Etale ⟶ f.Etale.obj (⊤_ Y.Etale) :=
  (PreservesTerminal.iso f.Etale).inv

/-- The base change of the terminal object of the small étale site is terminal. -/
noncomputable def isTerminalEtaleObjTerminal : IsTerminal (f.Etale.obj (⊤_ Y.Etale)) :=
  IsTerminal.ofIso terminalIsTerminal (PreservesTerminal.iso f.Etale).symm

lemma eq_terminalFrom_comp_terminalToEtale {U : Y'.Etale} (k : U ⟶ f.Etale.obj (⊤_ Y.Etale)) :
    k = terminal.from U ≫ terminalToEtale f :=
  (isTerminalEtaleObjTerminal f).hom_ext _ _

/-- The pullback of a constant global section is the constant global section: this is the
definition of the comparison `f^* X ≅ X` of `Scheme.upperStarConstantSheafIso` by uniqueness of
left adjoints. -/
lemma unit_comp_pullbackSection_comp_upperStarConstantSheafIso_hom (X : AddCommGrpCat.{u + 1}) :
    (constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1} terminalIsTerminal).unit.app X ≫
      pullbackSection f _ (terminalToEtale f) ≫
        ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).hom.app X).hom.app
          (op (⊤_ Y'.Etale)) =
    (constantSheafAdj Y'.smallEtaleTopology AddCommGrpCat.{u + 1} terminalIsTerminal).unit.app
      X := by
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (((constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1} terminalIsTerminal).comp
        (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f)).ofNatIsoRight
      (lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} f))
    (constantSheafAdj Y'.smallEtaleTopology AddCommGrpCat.{u + 1} terminalIsTerminal) X
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_unit,
    Adjunction.comp_unit_app] at h
  refine Eq.trans ?_ h
  have hn : ((upperStar AddCommGrpCat.{u + 1} f).obj
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj X)).obj.map
          (terminalToEtale f).op ≫
        ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).hom.app X).hom.app
          (op (⊤_ Y'.Etale)) =
      ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).hom.app X).hom.app
          (op (f.Etale.obj (⊤_ Y.Etale))) ≫
        ((constantSheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}).obj X).obj.map
          (terminalToEtale f).op :=
    ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).hom.app X).hom.naturality _
  simp only [pullbackSection, Category.assoc]
  rw [hn]
  rfl

lemma upperStarConstantSheafIso_hom_pullbackSection (X : AddCommGrpCat.{u + 1}) (x : X) :
    ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).hom.app X).hom.app
        (op (⊤_ Y'.Etale))
      (pullbackSection f _ (terminalToEtale f)
        ((constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1} terminalIsTerminal).unit.app
          X x)) =
    (constantSheafAdj Y'.smallEtaleTopology AddCommGrpCat.{u + 1} terminalIsTerminal).unit.app
      X x := by
  rw [← unit_comp_pullbackSection_comp_upperStarConstantSheafIso_hom f X,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]

end PullbackSection

end AlgebraicGeometry.Etale

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u + 1}] [HasExt.{u + 1} (Sheaf J AddCommGrpCat.{u + 1})]

/-- The global section of an abelian sheaf `F` corresponding to the class of a morphism
`g : ℤ ⟶ F` is the image of the constant section `1` under `g`. -/
lemma H.equiv₀_mk₀ {F : Sheaf J AddCommGrpCat.{u + 1}} {T : C} (hT : IsTerminal T)
    (g : (constantSheaf J AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ)) ⟶ F) :
    H.equiv₀ F hT (Abelian.Ext.mk₀ g) =
      g.hom.app (op T) ((constantSheafAdj J AddCommGrpCat.{u + 1} hT).unit.app _ ⟨1⟩) := by
  have h : Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ g) = g :=
    Abelian.Ext.addEquiv₀.apply_symm_apply g
  simp only [H.equiv₀, AddEquiv.trans_apply]
  erw [h]
  rfl

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Etale

variable {Y Y' : Scheme.{u}} (f : Y' ⟶ Y)

/-- In degree `0`, the comparison map on étale cohomology is the pullback of global sections
`AlgebraicGeometry.Etale.pullbackSection`. -/
lemma cohomologyMap_zero_equiv₀_symm (Q : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (s : Q.obj.obj (op (⊤_ Y.Etale))) :
    cohomologyMap f Q 0 ((Sheaf.H.equiv₀ Q terminalIsTerminal).symm s) =
      (Sheaf.H.equiv₀ _ terminalIsTerminal).symm (pullbackSection f Q (terminalToEtale f) s) := by
  obtain ⟨φ, hφ⟩ := (Abelian.Ext.mk₀_bijective _ _).2
    ((Sheaf.H.equiv₀ Q terminalIsTerminal).symm s)
  have hs : s = φ.hom.app _ ((constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1}
      terminalIsTerminal).unit.app _ ⟨1⟩) := by
    rw [← Sheaf.H.equiv₀_mk₀, hφ, AddEquiv.apply_symm_apply]
  have hinv (y : ((upperStar AddCommGrpCat.{u + 1} f).obj ((constantSheaf Y.smallEtaleTopology
      AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ)))).obj.obj (op (⊤_ Y'.Etale))) :
      ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).inv.app _).hom.app _
        (((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).hom.app _).hom.app _ y) = y :=
    Iso.hom_inv_id_apply (((sheafSections _ _).obj (op (⊤_ Y'.Etale))).mapIso
      ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).app _)) y
  rw [← hφ, AddEquiv.eq_symm_apply, cohomologyMap_apply, Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.mk₀_comp_mk₀, Sheaf.H.equiv₀_mk₀, hs, ← pullbackSection_natural,
    ← upperStarConstantSheafIso_hom_pullbackSection]
  exact congr_arg (((upperStar AddCommGrpCat.{u + 1} f).map φ).hom.app (op (⊤_ Y'.Etale)))
    (hinv _)

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Scheme.EtaleTorsor

variable {M : Type (u + 1)} [AddCommGroup M] [Finite M] {Y : Scheme.{u}}

/-- The constant section `m` of the constant sheaf `M`, over `V`. -/
noncomputable abbrev constSection (V : Y.Etale) (m : M) :
    ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of M)).obj.obj (op V) :=
  ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of M)).obj.map
    (terminal.from V).op
    ((constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1} terminalIsTerminal).unit.app
      (AddCommGrpCat.of M) m)

/-- The isomorphism of the constant sheaf with the sheaf of continuous functions sends the
constant section `m` to the constant function `m`. -/
lemma constantSheafIsoContinuousMapSheaf_hom_constSection [TopologicalSpace M]
    [DiscreteTopology M] (V : Y.Etale) (m : M) :
    (Etale.constantSheafIsoContinuousMapSheaf Y M).hom.hom.app (op V) (constSection V m) =
      ContinuousMap.const _ m := by
  have hu : (constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1}
      terminalIsTerminal).unit.app (AddCommGrpCat.of M) m =
      (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj
        (AddCommGrpCat.of M))).app (op (⊤_ Y.Etale)) m := by
    first
    | rfl
    | simp [constantSheafAdj, Adjunction.comp_unit_app]
  have h := ConcreteCategory.congr_hom (congr_arg (fun g ↦ g.app (op (⊤_ Y.Etale)))
    (Etale.toSheafify_constantSheafToContinuousMapSheaf Y M)) m
  rw [constSection, ← ConcreteCategory.comp_apply,
    (Etale.constantSheafIsoContinuousMapSheaf Y M).hom.hom.naturality,
    ConcreteCategory.comp_apply, hu]
  exact congr_arg (fun a : C((⊤_ Y.Etale).left, M) ↦ a.comp (terminal.from V).left.base.hom) h

/-- In the sheaf torsor of `t`, the constant section `m` acts on the identity of `P` by the
action of `m`. -/
lemma toSheafTorsor_vadd_constSection (t : EtaleTorsor M Y) (m : M) :
    t.toSheafTorsor.vadd (op t.toEtale) (constSection t.toEtale m) ⟨𝟙 _⟩ = ⟨t.vaddEtale m⟩ := by
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  have h : t.toSheafTorsor.vadd (op t.toEtale) (constSection t.toEtale m) ⟨𝟙 _⟩ =
      ⟨t.smulHom ((Etale.constantSheafIsoContinuousMapSheaf Y M).hom.hom.app _
        (constSection t.toEtale m)) (𝟙 _)⟩ := rfl
  rw [h, constantSheafIsoContinuousMapSheaf_hom_constSection]
  exact ULift.ext _ _ (etaleHom_ext ((t.smulHom_const m _).trans (Category.id_comp _)))

section Naturality

variable [TopologicalSpace M] [DiscreteTopology M]
  {I Q : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
  {ι : (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of M) ⟶ I}
  {d : I ⟶ Q} {w : ι ≫ d = 0} (hS : (ShortComplex.mk ι d w).ShortExact)
  (s : Q.obj.obj (op (⊤_ Y.Etale))) (t : EtaleTorsor M Y)
  (e : Sheaf.Torsor.Iso t.toSheafTorsor (Sheaf.Torsor.lifts terminalIsTerminal hS s))
  {Y' : Scheme.{u}} (f : Y' ⟶ Y)

/-- The tautological lift of `s` over the total space of `t`: the image of the identity of `P`
under the identification of `t` with the torsor of local lifts of `s`. -/
noncomputable def tautologicalLift : I.obj.obj (op t.toEtale) :=
  (e.iso.hom.hom.app (op t.toEtale) ⟨𝟙 _⟩).1

lemma map_vaddEtale_tautologicalLift (m : M) :
    I.obj.map (t.vaddEtale m).op (tautologicalLift hS s t e) =
      tautologicalLift hS s t e + ι.hom.app _ (constSection t.toEtale m) := by
  have h₁ := e.map_vadd (op t.toEtale) (constSection t.toEtale m) ⟨𝟙 _⟩
  rw [toSheafTorsor_vadd_constSection] at h₁
  have h₂ := ConcreteCategory.congr_hom (e.iso.hom.hom.naturality (t.vaddEtale m).op)
    (⟨𝟙 _⟩ : ULift.{u + 1} (t.toEtale ⟶ t.toEtale))
  simp only [ConcreteCategory.comp_apply] at h₂
  have h₃ : t.toSheafTorsor.sheaf.obj.map (t.vaddEtale m).op
      (⟨𝟙 _⟩ : ULift.{u + 1} (t.toEtale ⟶ t.toEtale)) = ⟨t.vaddEtale m⟩ :=
    ULift.ext _ _ (Category.comp_id _)
  rw [h₃, h₁] at h₂
  exact (congr_arg Subtype.val h₂).symm

/-- The short exact sequence `0 → f^*M → f^*I → f^*Q → 0`. -/
lemma shortExact_upperStar :
    (ShortComplex.mk ((Etale.upperStar AddCommGrpCat.{u + 1} f).map ι)
      ((Etale.upperStar AddCommGrpCat.{u + 1} f).map d)
      (by rw [← Functor.map_comp, w, Functor.map_zero])).ShortExact :=
  hS.map_of_exact (Etale.upperStar AddCommGrpCat.{u + 1} f)

/-- The pullback `s' ∈ Γ(Y', f^*Q)` of the global section `s`. -/
noncomputable abbrev pullbackGlobalSection :
    ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj Q).obj.obj (op (⊤_ Y'.Etale)) :=
  Etale.pullbackSection f Q (Etale.terminalToEtale f) s

/-- The isomorphism `f^* M ≅ (U ↦ C(U, M))` on the small étale site of `Y'`. -/
noncomputable abbrev upperStarIso :
    (Etale.upperStar AddCommGrpCat.{u + 1} f).obj
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of M)) ≅
      Etale.continuousMapSheaf Y' M :=
  (upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).app (AddCommGrpCat.of M) ≪≫
    Etale.constantSheafIsoContinuousMapSheaf Y' M

/-- The torsor of local lifts of `s'` to `f^* I`, as a torsor under `U ↦ C(U, M)`. -/
noncomputable abbrev pullbackLifts : Sheaf.Torsor (Etale.continuousMapSheaf Y' M) :=
  Sheaf.Torsor.ofIso (upperStarIso f)
    (Sheaf.Torsor.lifts terminalIsTerminal (shortExact_upperStar hS f)
      (pullbackGlobalSection s f))

omit [Finite M] in
lemma upperStarIso_hom_pullbackSection_constSection {V : Y.Etale} {U : Y'.Etale}
    (ψ : U ⟶ f.Etale.obj V) (m : M) :
    (upperStarIso f).hom.hom.app (op U) (Etale.pullbackSection f _ ψ (constSection V m)) =
      ContinuousMap.const _ m := by
  have hψ : ψ ≫ f.Etale.map (terminal.from V) = terminal.from U ≫ Etale.terminalToEtale f :=
    Etale.eq_terminalFrom_comp_terminalToEtale f _
  have hn := ConcreteCategory.congr_hom
    (((upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).hom.app
      (AddCommGrpCat.of M)).hom.naturality (terminal.from U).op)
    (Etale.pullbackSection f _ (Etale.terminalToEtale f)
      ((constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1} terminalIsTerminal).unit.app
        (AddCommGrpCat.of M) m))
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    Etale.upperStarConstantSheafIso_hom_pullbackSection] at hn
  rw [constSection, Etale.pullbackSection_map, hψ, ← Etale.map_pullbackSection, Iso.trans_hom]
  erw [ConcreteCategory.comp_apply]
  erw [hn]
  exact constantSheafIsoContinuousMapSheaf_hom_constSection U m

omit [Finite M] in
lemma pullbackSection_constSection {V : Y.Etale} {U : Y'.Etale} (ψ : U ⟶ f.Etale.obj V)
    (m : M) :
    Etale.pullbackSection f _ ψ (constSection V m) =
      (upperStarIso f).inv.hom.app (op U) (ContinuousMap.const _ m) := by
  rw [← upperStarIso_hom_pullbackSection_constSection f ψ m]
  exact (Iso.hom_inv_id_apply (((sheafSections _ _).obj (op U)).mapIso (upperStarIso f)) _).symm

/-- The map from the torsor of lifts of `f` to `P` to the torsor of local lifts of `s'`, which
sends `φ : U ⟶ P ×_Y Y'` to the pullback along `φ` of the tautological lift of `s`. -/
noncomputable def toPullbackLifts :
    (t.pullbackSheafTorsor f).sheaf ⟶ (pullbackLifts hS s f).sheaf :=
  ObjectProperty.homMk
    { app U := TypeCat.ofHom fun φ ↦
        ⟨Etale.pullbackSection f I φ.down (tautologicalLift hS s t e), by
          have h₁ := Etale.pullbackSection_natural f I d φ.down (tautologicalLift hS s t e)
          have h₂ : d.hom.app (op t.toEtale) (tautologicalLift hS s t e) =
              Q.obj.map (terminal.from t.toEtale).op s :=
            Sheaf.Torsor.lifts_val terminalIsTerminal hS (e.iso.hom.hom.app (op t.toEtale) ⟨𝟙 _⟩)
          rw [h₂, Etale.pullbackSection_map, Etale.eq_terminalFrom_comp_terminalToEtale f
            (φ.down ≫ _), ← Etale.map_pullbackSection] at h₁
          exact h₁⟩
      naturality U V h := by
        ext φ
        apply Subtype.ext
        exact (Etale.map_pullbackSection f I φ.down h.unop _).symm }

lemma toPullbackLifts_app_val (U : Y'.Etaleᵒᵖ) (φ : (t.pullbackSheafTorsor f).sheaf.obj.obj U) :
    ((toPullbackLifts hS s t e f).hom.app U φ).1 =
      Etale.pullbackSection f I φ.down (tautologicalLift hS s t e) :=
  rfl

omit [TopologicalSpace M] [DiscreteTopology M] in
lemma pullbackLifts_vadd_val (U : Y'.Etaleᵒᵖ) (a : C(U.unop.left, M))
    (x : (pullbackLifts hS s f).sheaf.obj.obj U) :
    ((pullbackLifts hS s f).vadd U a x).1 = x.1 +
      ((Etale.upperStar AddCommGrpCat.{u + 1} f).map ι).hom.app U
        ((upperStarIso f).inv.hom.app U a) :=
  rfl

lemma toPullbackLifts_vadd (U : Y'.Etaleᵒᵖ) (a : C(U.unop.left, M))
    (φ : (t.pullbackSheafTorsor f).sheaf.obj.obj U) :
    (toPullbackLifts hS s t e f).hom.app U ((t.pullbackSheafTorsor f).vadd U a φ) =
      (pullbackLifts hS s f).vadd U a ((toPullbackLifts hS s t e f).hom.app U φ) := by
  apply Subtype.ext
  rw [pullbackLifts_vadd_val, toPullbackLifts_app_val, toPullbackLifts_app_val]
  rw [← sub_eq_zero]
  refine Etale.eq_zero_of_forall_map_eq_zero _ (fun m : M ↦ Etale.fiberι a m)
    (fun x ↦ ⟨a x, ⟨x, rfl⟩, Scheme.Opens.ι_apply _ _⟩) _ fun m ↦ ?_
  have hw : Etale.fiberι a m ≫ t.pullbackSmulHom f a φ.down =
      Etale.fiberι a m ≫ φ.down ≫ t.pullbackVadd f m := by
    refine etaleHom_ext ?_
    rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left, Etale.fiberι_left,
      ι_pullbackSmulHom_left_of_le f t a φ.down le_rfl]
    rfl
  have ha : (Etale.continuousMapSheaf Y' M).obj.map (Etale.fiberι a m).op a =
      ContinuousMap.const _ m := by
    ext x
    exact x.2
  have hφ : ((t.pullbackSheafTorsor f).vadd U a φ).down = t.pullbackSmulHom f a φ.down := rfl
  rw [map_sub, map_add, hφ, Etale.map_pullbackSection, hw, ← Category.assoc,
    ← Etale.pullbackSection_map, map_vaddEtale_tautologicalLift, map_add,
    Etale.map_pullbackSection, ← Etale.pullbackSection_natural,
    ← ConcreteCategory.comp_apply ((upperStarIso f).inv.hom.app U),
    ← ConcreteCategory.comp_apply _ (((Etale.upperStar AddCommGrpCat.{u + 1} f).map ι).hom.app U),
    ← ((Etale.upperStar AddCommGrpCat.{u + 1} f).map ι).hom.naturality,
    ← Category.assoc, ← (upperStarIso f).inv.hom.naturality, Category.assoc,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ha,
    pullbackSection_constSection]
  abel

/-- The torsor of lifts of `f` to `P` is isomorphic to the torsor of local lifts of `s'`. -/
lemma pullbackSheafTorsor_equiv_pullbackLifts :
    t.pullbackSheafTorsor f ≈ pullbackLifts hS s f :=
  ⟨Sheaf.Torsor.Iso.ofHom (toPullbackLifts hS s t e f) (toPullbackLifts_vadd hS s t e f)⟩

end Naturality

section Delta

variable {I Q : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
  {ι : (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of M) ⟶ I}
  {d : I ⟶ Q} {w : ι ≫ d = 0} (hS : (ShortComplex.mk ι d w).ShortExact)
  (s : Q.obj.obj (op (⊤_ Y.Etale))) {Y' : Scheme.{u}} (f : Y' ⟶ Y)

omit [Finite M] in
/-- The pullback of `δ(s)` is `δ'(s')`, the connecting homomorphism of the pulled-back short
exact sequence applied to the pulled-back section. -/
lemma cohomologyMap_δ :
    Etale.cohomologyMap f _ 1 (Sheaf.H.δ hS terminalIsTerminal s) =
      Sheaf.H.δ (shortExact_upperStar hS f) terminalIsTerminal (pullbackGlobalSection s f) := by
  rw [Etale.cohomologyMap_apply, Sheaf.H.δ_apply, Sheaf.H.δ_apply,
    Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_extClass,
    ← Abelian.Ext.comp_assoc_of_second_deg_zero, ← Etale.cohomologyMap_apply,
    Etale.cohomologyMap_zero_equiv₀_symm]

end Delta

variable (M) in
/-- Blueprint `sk-prop-input-torsors` (naturality): Torsors and étale H^1

Let `M` be a finite abelian group and `ξ ∈ H¹(Y_ét, M)` a class of the constant sheaf `M` on a
scheme `Y`. Then there is an `M`-torsor `t` over `Y` representing `ξ` naturally: for every
morphism `f : Y' ⟶ Y`, the pullback of `ξ` along `f` vanishes exactly when `f` lifts to the
total space of `t`, that is, exactly when the pulled-back torsor `t ×_Y Y'` is trivial.

Writing `t` as the torsor of local lifts of a section `s` for an injective resolution
`0 → M → I → Q → 0`, so that `ξ = δ(s)`, the pullback of `ξ` is `δ'(s')` for the pulled-back
sequence (`AlgebraicGeometry.Scheme.EtaleTorsor.cohomologyMap_δ`); it vanishes iff `s'` lifts,
iff the torsor of local lifts of `s'` has a global section, and this torsor is the torsor of
lifts of `f` to `t`
(`AlgebraicGeometry.Scheme.EtaleTorsor.pullbackSheafTorsor_equiv_pullbackLifts`).
-/
@[stacks 02NE]
theorem exists_forall_cohomologyMap_eq_zero_iff
    (ξ : Sheaf.H ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of M)) 1) :
    ∃ t : EtaleTorsor M Y, ∀ ⦃Y' : Scheme.{u}⦄ (f : Y' ⟶ Y),
      Etale.cohomologyMap f _ 1 ξ = 0 ↔ ∃ s : Y' ⟶ t.P, s ≫ t.π = f := by
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  obtain ⟨q, hq⟩ := (bijective_classH1 M Y).2 ξ
  induction q using Quotient.inductionOn with | h t => ?_
  have hS := Sheaf.Torsor.injectiveSequence_shortExact
    ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of M))
  obtain ⟨s, hs⟩ := Sheaf.Torsor.exists_equiv_lifts terminalIsTerminal hS t.toSheafTorsor
  have hξ : ξ = Sheaf.H.δ hS terminalIsTerminal s := by
    rw [← hq, classH1_mk, Quotient.sound hs, Sheaf.Torsor.classH1_lifts]
  obtain ⟨e⟩ := hs
  refine ⟨t, fun Y' f ↦ ?_⟩
  rw [hξ, cohomologyMap_δ, ← AddMonoidHom.mem_ker, Sheaf.H.ker_δ, AddMonoidHom.mem_range,
    ← nonempty_pullbackSheafTorsor_iff,
    Sheaf.Torsor.nonempty_iff_of_equiv (pullbackSheafTorsor_equiv_pullbackLifts hS s t e f)]
  exact (Sheaf.Torsor.nonempty_lifts_iff terminalIsTerminal _ _).symm

end AlgebraicGeometry.Scheme.EtaleTorsor
