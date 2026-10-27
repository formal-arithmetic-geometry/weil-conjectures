/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineLogSchemeMorphisms
public import Sheaf.AlgebraicGeometry.FineLogEtaleDescentDatum
public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

import Sheaf.AlgebraicGeometry.EtaleLocalNoetherianDescent
import Sheaf.AlgebraicGeometry.FineLogEtaleDescent

/-!
# Fine logarithmic enhancement of a prescribed scheme and map

Source: ILO, Exposé VI 1.1, VIII 3.3.4(ii), 3.3.8, printed pp. 69, 107--108;
Stacks Project, Tags 034C and 04TQ
(blueprint: lem-trf-log-structure-fixed-scheme-enhancement).

`FineLogEtaleDescentDatum` presents log isomorphisms on the actual overlaps by their
sections on all common étale test schemes. `HomAlong` presents the homomorphism
from the inverse image of the base log sheaf, including its structural-map equation.
The extra compatibility hypothesis compares these maps with the same base test section.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The sieve of test schemes admitting a lift to a member of the cover. -/
private def localLiftSieve {X : Scheme.{u}} {ι : Type v} (U : ι → X.Etale)
    (V : X.Etale) : Sieve V where
  arrows := fun {Z} _ ↦ ∃ a, Nonempty (Z ⟶ U a)
  downward_closed := by
    rintro Z Q j ⟨a, ⟨g⟩⟩ c
    exact ⟨a, ⟨c ≫ g⟩⟩

private theorem localLiftSieve_mem {X : Scheme.{u}} {ι : Type v} (U : ι → X.Etale)
    (hcover : ∀ x : X, ∃ (a : ι) (y : (U a).left), (U a).hom y = x)
    (V : X.Etale) : localLiftSieve U V ∈ X.smallEtaleTopology V := by
  have hc : ⋃ a, Set.range (fun y : (U a).left ↦ ((U a).hom y : X)) = (Set.univ : Set X) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact hcover x
  apply X.smallEtaleTopology.superset_covering (S := Sieve.ofArrows
    (fun a ↦ Scheme.Etale.baseChange (U a).hom V)
    (fun a ↦ Scheme.Etale.baseChangeHom (U a).hom V)) ?_
    (Scheme.Etale.ofArrows_baseChange_mem_smallEtaleTopology V (fun a ↦ (U a).hom) hc)
  rintro Z j ⟨Q, c, _, ⟨a⟩, rfl⟩
  exact ⟨a, ⟨c ≫ MorphismProperty.Over.homMk
    (pullback.snd V.hom (U a).hom) (pullback.condition (f := V.hom) (g := (U a).hom)).symm⟩⟩

private theorem hom_ext_local {X : Scheme.{u}} {ι : Type v} (U : ι → X.Etale)
    (hcover : ∀ x : X, ∃ (a : ι) (y : (U a).left), (U a).hom y = x)
    (P : Sheaf X.smallEtaleTopology CommMonCat.{u}) {E : CommMonCat.{u}} {V : X.Etale}
    (s t : E ⟶ P.obj.obj (op V))
    (h : ∀ (a : ι) (Z : X.Etale) (j : Z ⟶ V) (_g : Z ⟶ U a),
      s ≫ P.obj.map j.op = t ≫ P.obj.map j.op) : s = t := by
  classical
  apply P.property.hom_ext ⟨localLiftSieve U V, localLiftSieve_mem U hcover V⟩ s t
  intro I
  exact h I.hf.choose I.Y I.f I.hf.choose_spec.some

/-- Glue maps into the sections of a sheaf, using all lifts to the cover. -/
private theorem glue_local_sections {X : Scheme.{u}} {ι : Type v} (U : ι → X.Etale)
    (hcover : ∀ x : X, ∃ (a : ι) (y : (U a).left), (U a).hom y = x)
    (P : Sheaf X.smallEtaleTopology CommMonCat.{u}) (E : CommMonCat.{u}) (V : X.Etale)
    (t : ∀ (a : ι) (Z : X.Etale) (_j : Z ⟶ V) (_g : Z ⟶ U a), E ⟶ P.obj.obj (op Z))
    (ht : ∀ (a b : ι) (Z Z' Q : X.Etale) (j : Z ⟶ V) (j' : Z' ⟶ V)
      (g : Z ⟶ U a) (g' : Z' ⟶ U b) (c : Q ⟶ Z) (d : Q ⟶ Z'),
      c ≫ j = d ≫ j' → t a Z j g ≫ P.obj.map c.op = t b Z' j' g' ≫ P.obj.map d.op) :
    ∃ h : E ⟶ P.obj.obj (op V), ∀ (a : ι) (Z : X.Etale) (j : Z ⟶ V) (g : Z ⟶ U a),
      h ≫ P.obj.map j.op = t a Z j g := by
  classical
  let C : X.smallEtaleTopology.Cover V := ⟨localLiftSieve U V, localLiftSieve_mem U hcover V⟩
  let x (I : C.Arrow) : E ⟶ P.obj.obj (op I.Y) :=
    t I.hf.choose I.Y I.f I.hf.choose_spec.some
  have hx : ∀ (I J : C.Arrow) (r : I.Relation J),
      x I ≫ P.obj.map r.g₁.op = x J ≫ P.obj.map r.g₂.op := by
    intro I J r
    exact ht _ _ _ _ _ _ _ _ _ _ _ r.w
  refine ⟨P.property.amalgamate C x (fun {_ _} r ↦ hx _ _ r), ?_⟩
  intro a Z j g
  let I : C.Arrow := ⟨Z, j, a, ⟨g⟩⟩
  have he := P.property.amalgamate_map C x (fun {_ _} r ↦ hx _ _ r) I
  change _ ≫ P.obj.map j.op = _ at he
  rw [he]
  have hi := ht I.hf.choose a Z Z Z j j I.hf.choose_spec.some g (𝟙 Z) (𝟙 Z) rfl
  simpa only [op_id, P.obj.map_id, Category.comp_id] using hi

/-- A compatible fine log structure and its relative log map descend to the fixed scheme.
The labelled gluing identifies the descended structure with each given local structure.
No saturation is assumed; saturated charts descend when all local structures have them.

Source: ILO VI 1.1, VIII 3.3.4(ii), 3.3.8; Stacks Project, Tags 034C and 04TQ
(blueprint: lem-trf-log-structure-fixed-scheme-enhancement).

Proof:
1. Apply `lem-trf-etale-local-noetherian-descent` to `U` and `hcover`, using the
   local Noetherianity of each member, to obtain local Noetherianity of `X`.
2. Apply the existence clause of `lem-trf-fine-log-structure-etale-descent` to `D`.
   Its transitions preserve alpha and satisfy the diagonal and triple cocycle equations.
   This gives `M`, fineness, and `e`, with `e_b = phi_ab e_a`. The same clause gives
   the conditional assertion on fine saturated charts.
3. On every relative test diagram, transport the local section homomorphisms by
   `e_a⁻¹`. Naturality of `e_a` and `localMap a` gives restriction compatibility.
   The hypothesis `hover` and `e_b = phi_ab e_a` make the transported maps agree
   for different lifts to the cover. The sieve of arrows whose sources admit
   such a lift is covering, since it contains the base changes of `U`.
   Apply the sheaf axiom in `CommMonCat` to glue the section homomorphisms.
   Separatedness proves naturality in both test objects. Separatedness of the
   multiplicative structure sheaf proves compatibility with the structural map.
4. These section homomorphisms give the desired `HomAlong` over `f` by
   `def-trf-fine-log-scheme-morphisms`. The amalgamation equation at the identity
   arrow gives `e_a u = f_a^flat`, exactly the restriction equation below. -/
theorem exists_fineLogStructure_fixedScheme_enhancement
    (S : FineLogScheme.{u}) (X : Scheme.{u}) (f : X ⟶ S.scheme)
    {ι : Type v} (U : ι → X.Etale) [∀ a : ι, IsLocallyNoetherian (U a).left]
    (hcover : ∀ x : X, ∃ (a : ι) (y : (U a).left), (U a).hom y = x)
    (D : FineLogEtaleDescentDatum U)
    (localMap : ∀ a : ι, (D.localLog a).HomAlong S.logStructure ((U a).hom ≫ f))
    (hover : ∀ (a b : ι) (V : X.Etale) (g : V ⟶ U a) (h : V ⟶ U b)
      (W : S.scheme.Etale) (k : V.left ⟶ W.left)
      (ha : k ≫ W.hom = g.left ≫ ((U a).hom ≫ f))
      (hb : k ≫ W.hom = h.left ≫ ((U b).hom ≫ f))
      (s : S.logStructure.monoidSheaf.obj.obj (op W)),
      D.transition a b V g h
          ((localMap a).sectionMap W
            ((Scheme.Etale.overToEtale (U a)).obj (Over.mk g)) k ha s) =
        (localMap b).sectionMap W
          ((Scheme.Etale.overToEtale (U b)).obj (Over.mk h)) k hb s) :
    IsLocallyNoetherian X ∧
      ∃ (M : EtaleLogStructure X) (_hM : M.IsFine) (e : D.Gluing M)
        (F : M.HomAlong S.logStructure f),
        (∀ (a : ι) (V : X.Etale) (g : V ⟶ U a)
          (W : S.scheme.Etale) (k : V.left ⟶ W.left)
          (hk : k ≫ W.hom = V.hom ≫ f)
          (ha : k ≫ W.hom = g.left ≫ ((U a).hom ≫ f))
          (s : S.logStructure.monoidSheaf.obj.obj (op W)),
          e.component a V g (F.sectionMap W V k hk s) =
            (localMap a).sectionMap W
              ((Scheme.Etale.overToEtale (U a)).obj (Over.mk g)) k ha s) ∧
        ((∀ a : ι, (D.localLog a).IsFineSaturated) → M.IsFineSaturated) := by
  classical
  have hX : IsLocallyNoetherian X :=
    isLocallyNoetherian_of_etale_cover (fun a ↦ (U a).left) (fun a ↦ (U a).hom) hcover
  let := hX
  obtain ⟨M, hM, e, hsat, _⟩ := (fineLogStructure_etale_descent U hcover).1 D
  let t (a : ι) (V : X.Etale) (g : V ⟶ U a) (W : S.scheme.Etale)
      (k : V.left ⟶ W.left) (hk : k ≫ W.hom = V.hom ≫ f) :
      S.logStructure.monoidSheaf.obj.obj (op W) →* M.monoidSheaf.obj.obj (op V) :=
    (e.component a V g).symm.toMonoidHom.comp
      ((localMap a).sectionMap W
        ((Scheme.Etale.overToEtale (U a)).obj (Over.mk g)) k (by
          change k ≫ W.hom = g.left ≫ ((U a).hom ≫ f)
          rw [hk, ← Category.assoc, MorphismProperty.Over.w g]))
  have tnat (a : ι) (V Q : X.Etale) (g : V ⟶ U a) (c : Q ⟶ V)
      (W : S.scheme.Etale) (k : V.left ⟶ W.left)
      (hk : k ≫ W.hom = V.hom ≫ f) (s : S.logStructure.monoidSheaf.obj.obj (op W)) :
      M.monoidSheaf.obj.map c.op (t a V g W k hk s) =
        t a Q (c ≫ g) W (c.left ≫ k) (by
          rw [Category.assoc, hk, ← Category.assoc, MorphismProperty.Over.w c]) s := by
    apply (e.component a Q (c ≫ g)).injective
    rw [e.naturality]
    simp only [t, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    let c' := (Scheme.Etale.overToEtale (U a)).map
      (Over.homMk c : Over.mk (c ≫ g) ⟶ Over.mk g)
    have hn := (localMap a).naturality W W
      ((Scheme.Etale.overToEtale (U a)).obj (Over.mk (c ≫ g)))
      ((Scheme.Etale.overToEtale (U a)).obj (Over.mk g)) (𝟙 W) c'
      (c.left ≫ k) k (by
        change (c.left ≫ k) ≫ W.hom = (c ≫ g).left ≫ ((U a).hom ≫ f)
        rw [Category.assoc, hk, ← Category.assoc, MorphismProperty.Over.w c,
          ← Category.assoc, MorphismProperty.Over.w (c ≫ g)])
      (by
        change k ≫ W.hom = g.left ≫ ((U a).hom ≫ f)
        rw [hk, ← Category.assoc, MorphismProperty.Over.w g]) (by
        change c.left ≫ k = (c.left ≫ k) ≫ 𝟙 W.left
        exact (Category.comp_id _).symm)
    simpa only [EtalePrelogStructure.localMap, MonoidHom.comp_apply, op_id,
      S.logStructure.monoidSheaf.obj.map_id, CommMonCat.hom_id, MonoidHom.id_apply] using
      congrArg (fun h ↦ h s) hn
  have tover (a b : ι) (V : X.Etale) (g : V ⟶ U a) (h : V ⟶ U b)
      (W : S.scheme.Etale) (k : V.left ⟶ W.left)
      (hk : k ≫ W.hom = V.hom ≫ f) (s : S.logStructure.monoidSheaf.obj.obj (op W)) :
      t a V g W k hk s = t b V h W k hk s := by
    apply (e.component b V h).injective
    rw [← e.transition a b V g h]
    simp only [t, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    exact hover a b V g h W k _ _ s
  have tbase (a : ι) (V : X.Etale) (g : V ⟶ U a) (W₁ W₂ : S.scheme.Etale)
      (b : W₁ ⟶ W₂) (k₁ : V.left ⟶ W₁.left) (k₂ : V.left ⟶ W₂.left)
      (h₁ : k₁ ≫ W₁.hom = V.hom ≫ f) (h₂ : k₂ ≫ W₂.hom = V.hom ≫ f)
      (hb : k₂ = k₁ ≫ b.left) (s : S.logStructure.monoidSheaf.obj.obj (op W₂)) :
      t a V g W₂ k₂ h₂ s =
        t a V g W₁ k₁ h₁ (S.logStructure.monoidSheaf.obj.map b.op s) := by
    have hn := (localMap a).naturality W₁ W₂
      ((Scheme.Etale.overToEtale (U a)).obj (Over.mk g))
      ((Scheme.Etale.overToEtale (U a)).obj (Over.mk g)) b (𝟙 _)
      k₁ k₂ (by
        change k₁ ≫ W₁.hom = g.left ≫ ((U a).hom ≫ f)
        rw [h₁, ← Category.assoc, MorphismProperty.Over.w g])
      (by
        change k₂ ≫ W₂.hom = g.left ≫ ((U a).hom ≫ f)
        rw [h₂, ← Category.assoc, MorphismProperty.Over.w g]) (by
        change 𝟙 V.left ≫ k₂ = k₁ ≫ b.left
        simpa only [Category.id_comp] using hb)
    apply congrArg (e.component a V g).symm
    simpa only [op_id, (D.localLog a).monoidSheaf.obj.map_id, CommMonCat.hom_id,
      MonoidHom.comp_apply, MonoidHom.id_apply] using congrArg (fun h ↦ h s) hn
  have talpha (a : ι) (V : X.Etale) (g : V ⟶ U a) (W : S.scheme.Etale)
      (k : V.left ⟶ W.left) (hk : k ≫ W.hom = V.hom ≫ f)
      (s : S.logStructure.monoidSheaf.obj.obj (op W)) :
      M.alpha.app (op V) (t a V g W k hk s) = k.appTop (S.logStructure.alpha.app (op W) s) := by
    rw [← e.alpha a V g]
    simp only [t, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    exact (localMap a).compatibility W
      ((Scheme.Etale.overToEtale (U a)).obj (Over.mk g)) k _ s
  have hex (W : S.scheme.Etale) (V : X.Etale) (k : V.left ⟶ W.left)
      (hk : k ≫ W.hom = V.hom ≫ f) :
      ∃ h : S.logStructure.monoidSheaf.obj.obj (op W) ⟶ M.monoidSheaf.obj.obj (op V),
        ∀ (a : ι) (Z : X.Etale) (j : Z ⟶ V) (g : Z ⟶ U a),
          h ≫ M.monoidSheaf.obj.map j.op = CommMonCat.ofHom
            (t a Z g W (j.left ≫ k) (by
              rw [Category.assoc, hk, ← Category.assoc, MorphismProperty.Over.w j])) := by
    apply glue_local_sections U hcover M.monoidSheaf _ V
    intro a b Z Z' Q j j' g g' c d hcd
    ext s
    change M.monoidSheaf.obj.map c.op (t a Z g W (j.left ≫ k) (by
      calc
        (j.left ≫ k) ≫ W.hom = j.left ≫ (k ≫ W.hom) := Category.assoc j.left k W.hom
        _ = j.left ≫ (V.hom ≫ f) := congrArg (fun q ↦ j.left ≫ q) hk
        _ = (j.left ≫ V.hom) ≫ f := (Category.assoc j.left V.hom f).symm
        _ = Z.hom ≫ f := by rw [MorphismProperty.Over.w j]) s) =
      M.monoidSheaf.obj.map d.op (t b Z' g' W (j'.left ≫ k) (by
        rw [Category.assoc, hk, ← Category.assoc, MorphismProperty.Over.w j']) s)
    rw [tnat a Z Q g c W (j.left ≫ k) (by
      rw [Category.assoc, hk, ← Category.assoc, MorphismProperty.Over.w j]) s,
      tnat b Z' Q g' d W (j'.left ≫ k) (by
        rw [Category.assoc, hk, ← Category.assoc, MorphismProperty.Over.w j']) s]
    have he : c.left ≫ (j.left ≫ k) = d.left ≫ (j'.left ≫ k) := by
      simp only [← Category.assoc]
      exact congrArg (fun q ↦ q.left ≫ k) hcd
    simp only [he]
    exact tover a b Q (c ≫ g) (d ≫ g') W (d.left ≫ (j'.left ≫ k)) (by
      rw [Category.assoc, Category.assoc, hk, ← Category.assoc j'.left V.hom f,
        MorphismProperty.Over.w j', ← Category.assoc, MorphismProperty.Over.w d]) s
  choose F hF using hex
  have hnat (W₁ W₂ : S.scheme.Etale) (V₁ V₂ : X.Etale) (b : W₁ ⟶ W₂)
      (c : V₁ ⟶ V₂) (k₁ : V₁.left ⟶ W₁.left) (k₂ : V₂.left ⟶ W₂.left)
      (h₁ : k₁ ≫ W₁.hom = V₁.hom ≫ f) (h₂ : k₂ ≫ W₂.hom = V₂.hom ≫ f)
      (hc : c.left ≫ k₂ = k₁ ≫ b.left) :
      F W₂ V₂ k₂ h₂ ≫ M.monoidSheaf.obj.map c.op =
        S.logStructure.monoidSheaf.obj.map b.op ≫ F W₁ V₁ k₁ h₁ := by
    apply hom_ext_local U hcover M.monoidSheaf
    intro a Z j g
    calc
      (F W₂ V₂ k₂ h₂ ≫ M.monoidSheaf.obj.map c.op) ≫ M.monoidSheaf.obj.map j.op =
          F W₂ V₂ k₂ h₂ ≫ M.monoidSheaf.obj.map (j ≫ c).op := by
        rw [Category.assoc, ← Functor.map_comp, ← op_comp]
      _ = _ := hF W₂ V₂ k₂ h₂ a Z (j ≫ c) g
      _ = S.logStructure.monoidSheaf.obj.map b.op ≫
          (F W₁ V₁ k₁ h₁ ≫ M.monoidSheaf.obj.map j.op) := by
        rw [hF W₁ V₁ k₁ h₁ a Z j g]
        ext s
        apply tbase a Z g W₁ W₂ b (j.left ≫ k₁) ((j ≫ c).left ≫ k₂)
          (by rw [Category.assoc, h₁, ← Category.assoc, MorphismProperty.Over.w j])
          (by rw [Category.assoc, h₂, ← Category.assoc, MorphismProperty.Over.w (j ≫ c)])
          ?_ s
        change (j.left ≫ c.left) ≫ k₂ = (j.left ≫ k₁) ≫ b.left
        rw [Category.assoc, hc, Category.assoc]
      _ = _ := (Category.assoc _ _ _).symm
  let O : Sheaf X.smallEtaleTopology CommMonCat.{u} :=
    ⟨X.etaleStructurePresheaf ⋙ forget₂ CommRingCat CommMonCat,
      Presheaf.isSheaf_comp_of_isSheaf _ _ _ X.isSheaf_etaleStructurePresheaf⟩
  have halpha (W : S.scheme.Etale) (V : X.Etale) (k : V.left ⟶ W.left)
      (hk : k ≫ W.hom = V.hom ≫ f) :
      F W V k hk ≫ M.alpha.app (op V) =
        S.logStructure.alpha.app (op W) ≫
          (forget₂ CommRingCat CommMonCat).map k.appTop := by
    apply hom_ext_local U hcover O
    intro a Z j g
    rw [Category.assoc, ← M.alpha.naturality j.op, ← Category.assoc, hF W V k hk a Z j g]
    ext s
    change M.alpha.app (op Z) (t a Z g W (j.left ≫ k) (by
      calc
        (j.left ≫ k) ≫ W.hom = j.left ≫ (k ≫ W.hom) := Category.assoc j.left k W.hom
        _ = j.left ≫ (V.hom ≫ f) := congrArg (fun q ↦ j.left ≫ q) hk
        _ = (j.left ≫ V.hom) ≫ f := (Category.assoc j.left V.hom f).symm
        _ = Z.hom ≫ f := by rw [MorphismProperty.Over.w j]) s) =
      j.left.appTop (k.appTop (S.logStructure.alpha.app (op W) s))
    calc
      _ = (j.left ≫ k).appTop (S.logStructure.alpha.app (op W) s) :=
        talpha a Z g W (j.left ≫ k) (by
          rw [Category.assoc, hk, ← Category.assoc, MorphismProperty.Over.w j]) s
      _ = _ := by rw [Scheme.Hom.comp_appTop]; rfl
  refine ⟨hX, M, hM, e, ?_, ?_, hsat⟩
  · exact
      { sectionMap := fun W V k hk ↦ (F W V k hk).hom
        naturality := fun W₁ W₂ V₁ V₂ b c k₁ k₂ h₁ h₂ hc ↦
          congrArg CommMonCat.Hom.hom (hnat W₁ W₂ V₁ V₂ b c k₁ k₂ h₁ h₂ hc)
        compatibility := fun W V k hk s ↦ congrArg (fun h ↦ h s) (halpha W V k hk) }
  · intro a V g W k hk ha s
    have he := congrArg (fun h ↦ h s) (hF W V k hk a V (𝟙 V) g)
    have hr : F W V k hk s = t a V g W k hk s := by
      change M.monoidSheaf.obj.map (𝟙 V).op (F W V k hk s) =
        t a V g W (𝟙 V.left ≫ k) (by simpa only [Category.id_comp] using hk) s at he
      simpa only [op_id, M.monoidSheaf.obj.map_id, CommMonCat.id_apply,
        Category.id_comp] using he
    change e.component a V g (F W V k hk s) = _
    rw [hr]
    exact (e.component a V g).apply_symm_apply _

end AlgebraicGeometry
