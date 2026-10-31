/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PrelogUnitPushoutPresentation
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
public import WeilConjectures.AlgebraicGeometry.PointedEtaleStalk
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.CategoryTheory.Sites.Point.Conservative

/-!
# Étale restriction and stalk recognition of prelog presentations

Source: ILO, Exposé VI 1.1, printed p. 69; Stacks, Tags 00XZ, 00YR, 01T6,
03PQ, 040R and 03PU. This is the agent-isolated argument underlying the associated
log construction, not a verbatim lemma in ILO.
(blueprint: lem-trf-etale-log-presentation-comparison).
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem prelogStalkMap_structural {X : Scheme.{u}}
    (L K : EtalePrelogStructure X) (f : L.monoidSheaf ⟶ K.monoidSheaf)
    (hf : f.hom ≫ K.alpha = L.alpha)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X) :
    prelogStalkMap K.monoidSheaf f.hom t ≫
        CommMonCat.ofHom (K.stalkAlpha t) = CommMonCat.ofHom (L.stalkAlpha t) := by
  unfold prelogStalkMap EtalePrelogStructure.stalkAlpha
  apply colimit.hom_ext
  intro j
  simp only [CommMonCat.ofHom_hom, prelogStalkDiagram, pointedEtaleStalkDiagram,
    colim_map, ι_colimMap_assoc, colimit.ι_desc]
  change f.hom.app _ ≫ (K.alpha.app _ ≫ _) = L.alpha.app _ ≫ _
  rw [← Category.assoc, ← NatTrans.comp_app, hf]

private theorem prelogStalkMap_comp {X : Scheme.{u}}
    {M : X.Etaleᵒᵖ ⥤ CommMonCat.{u}}
    (L K : Sheaf X.smallEtaleTopology CommMonCat.{u})
    (i : M ⟶ L.obj) (f : L ⟶ K)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X) :
    prelogStalkMap L i t ≫ prelogStalkMap K f.hom t =
      prelogStalkMap K (i ≫ f.hom) t := by
  unfold prelogStalkMap
  rw [← Functor.map_comp, ← Functor.whiskerLeft_comp]

private theorem unitsInverse_natural {A B C : Type u}
    [CommMonoid A] [CommMonoid B] [CommMonoid C]
    (α : B →* A) (α' : C →* A) (f : B →* C) (hf : α'.comp f = α)
    (hα : Function.Bijective (Units.map α))
    (hα' : Function.Bijective (Units.map α')) :
    f.comp ((Units.coeHom B).comp
        (MulEquiv.ofBijective (Units.map α) hα).symm.toMonoidHom) =
      (Units.coeHom C).comp
        (MulEquiv.ofBijective (Units.map α') hα').symm.toMonoidHom := by
  ext a
  let e := MulEquiv.ofBijective (Units.map α) hα
  let e' := MulEquiv.ofBijective (Units.map α') hα'
  change f (e.symm a).val = (e'.symm a).val
  have hu : Units.map f (e.symm a) = e'.symm a := by
    apply hα'.1
    change Units.map α' (Units.map f (e.symm a)) = e' (e'.symm a)
    rw [← MonoidHom.comp_apply, ← Units.map_comp, hf]
    exact (e.apply_symm_apply a).trans (e'.apply_symm_apply a).symm
  exact congrArg Units.val hu

private theorem chartMap_bijective {A P B C : Type u}
    [CommMonoid A] [CommMonoid P] [CommMonoid B] [CommMonoid C]
    (β : P →* B) (β' : P →* C) (j : A →* B) (j' : A →* C)
    (f : B →* C) (hβ : f.comp β = β') (hj : f.comp j = j')
    (hs : Function.Surjective (β.coprod j))
    (hs' : Function.Surjective (β'.coprod j'))
    (hk : Con.ker (β.coprod j) = Con.ker (β'.coprod j')) :
    Function.Bijective f := by
  have hp (x : P × A) : f (β.coprod j x) = β'.coprod j' x := by
    change f (β x.1 * j x.2) = β' x.1 * j' x.2
    rw [map_mul, ← MonoidHom.comp_apply, hβ, ← MonoidHom.comp_apply, hj]
  constructor
  · intro b c h
    obtain ⟨x, rfl⟩ := hs b
    obtain ⟨y, rfl⟩ := hs c
    have he : (Con.ker (β'.coprod j')) x y := by
      change β'.coprod j' x = β'.coprod j' y
      rw [← hp, ← hp, h]
    rw [← hk] at he
    exact he
  · intro c
    obtain ⟨x, rfl⟩ := hs' c
    exact ⟨β.coprod j x, hp x⟩

private theorem prelogStalkMap_forget_isIso {X : Scheme.{u}}
    (L K : Sheaf X.smallEtaleTopology CommMonCat.{u}) (f : L ⟶ K)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X)
    [IsIso (prelogStalkMap K f.hom t)] :
    IsIso ((Scheme.pointSmallEtale t).sheafFiber.map
      ((sheafCompose X.smallEtaleTopology (forget CommMonCat.{u})).map f)) := by
  have : PreservesColimitsOfShape (Scheme.pointSmallEtale t).fiber.Elementsᵒᵖ
      (forget CommMonCat.{u}) :=
    Functor.Final.preservesColimitsOfShape_of_final
      (FinallySmall.fromFilteredFinalModel.{u} (Scheme.pointSmallEtale t).fiber.Elementsᵒᵖ)
      (forget CommMonCat.{u})
  let n := Functor.whiskerLeft (CategoryOfElements.π (Scheme.pointSmallEtale t).fiber).op
    f.hom
  let eL := preservesColimitIso (forget CommMonCat.{u}) (prelogStalkDiagram L.obj t)
  let eK := preservesColimitIso (forget CommMonCat.{u}) (prelogStalkDiagram K.obj t)
  change IsIso (colim.map (Functor.whiskerRight n (forget CommMonCat.{u})))
  have he : colim.map (Functor.whiskerRight n (forget CommMonCat.{u})) =
      eL.inv ≫ (forget CommMonCat.{u}).map (prelogStalkMap K f.hom t) ≫ eK.hom := by
    have hn := ((preservesColimitNatIso (forget CommMonCat.{u})).hom.naturality n).symm
    change eL.hom ≫ colim.map (Functor.whiskerRight n (forget CommMonCat.{u})) =
      (forget CommMonCat.{u}).map (prelogStalkMap K f.hom t) ≫ eK.hom at hn
    calc
      _ = eL.inv ≫ (eL.hom ≫
          colim.map (Functor.whiskerRight n (forget CommMonCat.{u}))) := by
        rw [← Category.assoc, eL.inv_hom_id, Category.id_comp]
      _ = eL.inv ≫ ((forget CommMonCat.{u}).map
          (prelogStalkMap K f.hom t) ≫ eK.hom) := congrArg (fun q ↦ eL.inv ≫ q) hn
      _ = _ := (Category.assoc _ _ _).symm
  rw [he]
  infer_instance

private theorem prelogMap_isIso_of_stalks {X : Scheme.{u}}
    (L K : Sheaf X.smallEtaleTopology CommMonCat.{u}) (f : L ⟶ K)
    (hf : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X),
      IsIso (prelogStalkMap K f.hom t)) : IsIso f := by
  let s (x : X) : Spec (.of (AlgebraicClosure (X.residueField x))) ⟶ X :=
    (Scheme.SpecToEquivOfField (AlgebraicClosure (X.residueField x)) X).symm
      ⟨x, CommRingCat.ofHom (algebraMap (X.residueField x) _)⟩
  have hs : ⋃ x : X, Set.range (s x) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨x, default, by simp [s, Scheme.SpecToEquivOfField]⟩
  have hP := Scheme.isConservative_pointSmallEtale s hs
  let F := sheafCompose X.smallEtaleTopology (forget CommMonCat.{u})
  have : IsIso (F.map f) := by
    rw [hP.jointlyReflectIsomorphisms_type.isIso_iff]
    rintro ⟨_, ⟨x⟩⟩
    have := hf _ (s x)
    exact prelogStalkMap_forget_isIso L K f (s x)
  exact isIso_of_reflects_iso f F

/-- Composition from the small étale site of U to that of X, using the canonical
slice equivalence. Source: Stacks Tag 00XZ
(blueprint: lem-trf-etale-log-presentation-comparison). -/
def prelogRestrictionFunctor {X : Scheme.{u}} (U : X.Etale) : U.left.Etale ⥤ X.Etale :=
  Scheme.Etale.etaleToOver U ⋙ Over.forget U

/-- Restriction of the structural map; the test scheme and its functions are
literally unchanged. Source: ILO VI 1.1; Stacks Tag 00XZ
(blueprint: lem-trf-etale-log-presentation-comparison). -/
def prelogRestrictionGamma {X : Scheme.{u}} {M : X.Etaleᵒᵖ ⥤ CommMonCat.{u}}
    (γ : M ⟶ X.etaleStructurePresheaf ⋙ forget₂ CommRingCat CommMonCat) (U : X.Etale) :
    (prelogRestrictionFunctor U).op ⋙ M ⟶
      U.left.etaleStructurePresheaf ⋙ forget₂ CommRingCat CommMonCat :=
  Functor.whiskerLeft (prelogRestrictionFunctor U).op γ

/-- Étale restriction preserves the quotient presentation and its sheafification,
with the unique comparison normalized on the unit, structure, monoid and units.

Source: ILO VI 1.1, printed p. 69; Stacks Tags 01T6, 00XZ and 00YR.
Proof (node steps 1--4): an étale map is locally of finite presentation and hence
locally of finite type; local Noetherianity follows from 01T6. The canonical
`Etale.overEquiv` identifies the two sites and their covering families. On every
object the same M, γ and ring give the same congruence and quotient; restrictions
send [m,a] to the identical restricted pair. Restriction to a slice preserves set
sheafification by `lem-cbc-sieve-slice-sheafification`. Monoid sheafification has
this underlying set sheafification. Its universal property therefore supplies a
unique monoid comparison preserving η, and its underlying set comparison is an
isomorphism. The structural maps agree after η and hence agree by uniqueness.
The maps from M and units agree by substituting [m,1] and [1,a]. The unit inverse
image is carried to that of L, so the induced prelog structure is a log structure.
(blueprint: lem-trf-etale-log-presentation-comparison). -/
theorem etaleLogPresentation_restriction (X : Scheme.{u}) [IsLocallyNoetherian X]
    (M : X.Etaleᵒᵖ ⥤ CommMonCat.{u})
    (γ : M ⟶ X.etaleStructurePresheaf ⋙ forget₂ CommRingCat CommMonCat)
    (L : EtaleLogStructure X) (η : prelogPresentation γ ⟶ L.monoidSheaf.obj)
    (hη : IsPrelogPresentationSheafification γ L.monoidSheaf η)
    (hα : ∀ (W : X.Etale) (m : M.obj (op W)) (a : Γ(W.left, ⊤)ˣ),
      L.alpha.app (op W) (η.app (op W) (prelogPresentationPair γ W (m, a))) =
        @id Γ(W.left, ⊤) (γ.app (op W) m) * a.val)
    (U : X.Etale) :
    IsLocallyNoetherian U.left ∧
    (∀ (W : Over U) (S : Sieve W),
      S ∈ (X.smallEtaleTopology.over U) W ↔
        S.functorPushforward (Scheme.Etale.overEquiv U).functor ∈
          U.left.smallEtaleTopology ((Scheme.Etale.overEquiv U).functor.obj W)) ∧
    prelogPresentation (prelogRestrictionGamma γ U) =
      (prelogRestrictionFunctor U).op ⋙ prelogPresentation γ ∧
    ∀ (LU : EtalePrelogStructure U.left)
      (ηU : prelogPresentation (prelogRestrictionGamma γ U) ⟶ LU.monoidSheaf.obj),
      IsPrelogPresentationSheafification (prelogRestrictionGamma γ U) LU.monoidSheaf ηU →
      (∀ (W : U.left.Etale)
        (m : ((prelogRestrictionFunctor U).op ⋙ M).obj (op W)) (a : Γ(W.left, ⊤)ˣ),
        LU.alpha.app (op W)
          (ηU.app (op W) (prelogPresentationPair (prelogRestrictionGamma γ U) W (m, a))) =
            @id Γ(W.left, ⊤) ((prelogRestrictionGamma γ U).app (op W) m) * a.val) →
      (∃ LLU : EtaleLogStructure U.left, LLU.toEtalePrelogStructure = LU) ∧
      ∃! e : LU.monoidSheaf.obj ≅ (prelogRestrictionFunctor U).op ⋙ L.monoidSheaf.obj,
        (∀ (W : U.left.Etale)
          (m : ((prelogRestrictionFunctor U).op ⋙ M).obj (op W)) (a : Γ(W.left, ⊤)ˣ),
          e.hom.app (op W)
            (ηU.app (op W)
              (prelogPresentationPair (prelogRestrictionGamma γ U) W (m, a))) =
            η.app (op ((prelogRestrictionFunctor U).obj W))
              (prelogPresentationPair γ ((prelogRestrictionFunctor U).obj W) (m, a))) ∧
        (∀ (W : U.left.Etale) (s : LU.monoidSheaf.obj.obj (op W)),
          L.alpha.app (op ((prelogRestrictionFunctor U).obj W)) (e.hom.app (op W) s) =
            LU.alpha.app (op W) s) ∧
        (∀ (W : U.left.Etale)
          (m : ((prelogRestrictionFunctor U).op ⋙ M).obj (op W)),
          e.hom.app (op W)
            ((prelogPresentationIota (prelogRestrictionGamma γ U) LU.monoidSheaf ηU).app
              (op W) m) =
            (prelogPresentationIota γ L.monoidSheaf η).app
              (op ((prelogRestrictionFunctor U).obj W)) m) ∧
        ∀ (W : U.left.Etale) (a : Γ(W.left, ⊤)ˣ),
          e.hom.app (op W)
            (prelogPresentationUnits (prelogRestrictionGamma γ U) LU.monoidSheaf ηU W a) =
              prelogPresentationUnits γ L.monoidSheaf η
                ((prelogRestrictionFunctor U).obj W) a := by
  sorry

/-- The given log map is an isomorphism when both canonical stalk presentations
are isomorphisms, and the universal mapping bijection transfers along this map.

Source: ILO VI 1.1, printed p. 69; Stacks Tags 03PQ, 040R, 04AX and 03PU.
Proof (node steps 5--7): represent the monoid germ and the ring-unit germ on a
common pointed étale neighbourhood. Unit representatives exist by
`lem-trf-filtered-ring-log-pushout`, with auxiliary monoid {1}. Taking germs in
the pair formula gives f_x ρ_L = ρ_K. Each ρ is an isomorphism by the two stalk
chart hypotheses, so f_x is an isomorphism. Choose algebraic closures of all
residue fields. Their geometric points cover X, and conservativity of their
set stalks makes every section map bijective. The inverse preserves products,
identity and restrictions by injectivity; the structural compatibility follows
by composing α_K f = α_L with the inverse. Setting the unit to 1 gives fi=v.
For every N, precomposition with f is a bijection on log morphisms, inverse to
precomposition with f⁻¹. Its composite with the assumed bijection for i is the
bijection for v. Here `IsStalkChart` is exactly surjectivity of the pair map and
its having the generated pushout congruence as kernel, i.e. the stated canonical
quotient map being an isomorphism; no abstract isomorphism is substituted.
(blueprint: lem-trf-etale-log-presentation-comparison). -/
theorem etaleLogPresentation_comparison (X : Scheme.{u}) [IsLocallyNoetherian X]
    (M : X.Etaleᵒᵖ ⥤ CommMonCat.{u})
    (γ : M ⟶ X.etaleStructurePresheaf ⋙ forget₂ CommRingCat CommMonCat)
    (L : EtaleLogStructure X) (η : prelogPresentation γ ⟶ L.monoidSheaf.obj)
    (hη : IsPrelogPresentationSheafification γ L.monoidSheaf η)
    (hα : ∀ (W : X.Etale) (m : M.obj (op W)) (a : Γ(W.left, ⊤)ˣ),
      L.alpha.app (op W) (η.app (op W) (prelogPresentationPair γ W (m, a))) =
        @id Γ(W.left, ⊤) (γ.app (op W) m) * a.val)
    (K : EtaleLogStructure X) (v : M ⟶ K.monoidSheaf.obj)
    (hv : v ≫ K.alpha = γ) (f : L.monoidSheaf ⟶ K.monoidSheaf)
    (hf : f.hom ≫ K.alpha = L.alpha)
    (hpair : ∀ (W : X.Etale) (m : M.obj (op W)) (a : Γ(W.left, ⊤)ˣ),
      f.hom.app (op W) (η.app (op W) (prelogPresentationPair γ W (m, a))) =
        v.app (op W) m * prelogSectionUnit K W a)
    (hstalk : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X),
      L.IsStalkChart t
        (prelogStalkMap L.monoidSheaf (prelogPresentationIota γ L.monoidSheaf η) t).hom ∧
      K.IsStalkChart t (prelogStalkMap K.monoidSheaf v t).hom) :
    (∃ e : L.monoidSheaf ≅ K.monoidSheaf,
      e.hom = f ∧ e.inv.hom ≫ L.alpha = K.alpha) ∧
    (HasPrelogUniversalMapping γ L (prelogPresentationIota γ L.monoidSheaf η) →
      HasPrelogUniversalMapping γ K v) := by
  classical
  have _ := hη
  have _ := hα
  let i := prelogPresentationIota γ L.monoidSheaf η
  -- The pair formula at (1, 1) fixes the sectionwise unit at 1 without extra lemmas.
  have hj (W : X.Etale) : prelogSectionUnit K W 1 = 1 := by
    have h := (hpair W 1 1).symm
    have hz : prelogPresentationPair γ W (1, 1) = 1 := map_one _
    simpa only [hz, map_one, one_mul] using h
  have hfi : i ≫ f.hom = v := by
    ext W m
    change f.hom.app W (η.app W (prelogPresentationPair γ W.unop (m, 1))) =
      v.app W m
    simpa only [hj, mul_one] using hpair W.unop m 1
  have hfiso : IsIso f := prelogMap_isIso_of_stalks L.monoidSheaf K.monoidSheaf f
    (fun Ω _ _ t ↦ by
      let fx := prelogStalkMap K.monoidSheaf f.hom t
      let β := (prelogStalkMap L.monoidSheaf i t).hom
      let β' := (prelogStalkMap K.monoidSheaf v t).hom
      have hβ : fx.hom.comp β = β' := by
        have h := prelogStalkMap_comp L.monoidSheaf K.monoidSheaf i f t
        rw [hfi] at h
        exact congrArg CommMonCat.Hom.hom h
      have ha : (K.toEtalePrelogStructure.stalkAlpha t).comp fx.hom =
          L.toEtalePrelogStructure.stalkAlpha t :=
        congrArg CommMonCat.Hom.hom
          (prelogStalkMap_structural L.toEtalePrelogStructure K.toEtalePrelogStructure f hf t)
      -- A structural map between log stalks necessarily preserves their unit inclusions.
      have hu : fx.hom.comp (L.unitsIn t) = K.unitsIn t :=
        unitsInverse_natural _ _ _ ha (L.unitsBijective Ω t) (K.unitsBijective Ω t)
      have hb : (K.toEtalePrelogStructure.stalkAlpha t).comp β' =
          (L.toEtalePrelogStructure.stalkAlpha t).comp β := by
        rw [← hβ, ← MonoidHom.comp_assoc, ha]
      obtain ⟨hL, hK⟩ := hstalk Ω t
      have hk : Con.ker (β.coprod (L.unitsIn t)) =
          Con.ker (β'.coprod (K.unitsIn t)) := by
        rw [hL.2, hK.2]
        exact congrArg (fun b ↦ divisorialChartCongruence b.mrangeRestrict) hb.symm
      have hbij := chartMap_bijective β β' (L.unitsIn t) (K.unitsIn t)
        fx.hom hβ hu hL.1 hK.1 hk
      exact (MulEquiv.ofBijective fx.hom hbij).toCommMonCatIso.isIso_hom)
  let e := asIso f
  have hinvcomp : e.inv.hom ≫ f.hom = 𝟙 _ := by
    exact congrArg (fun g : K.monoidSheaf ⟶ K.monoidSheaf ↦ g.hom) e.inv_hom_id
  have hinv : e.inv.hom ≫ L.alpha = K.alpha := by
    rw [← hf, ← Category.assoc, hinvcomp, Category.id_comp]
  refine ⟨⟨e, rfl, hinv⟩, ?_⟩
  intro hL N
  -- Precomposition with the constructed isomorphism identifies the compatible Hom sets.
  let E : {g : K.monoidSheaf ⟶ N.monoidSheaf // g.hom ≫ N.alpha = K.alpha} ≃
      {g : L.monoidSheaf ⟶ N.monoidSheaf // g.hom ≫ N.alpha = L.alpha} :=
    { toFun := fun g ↦ ⟨f ≫ g.val, by
        change f.hom ≫ g.val.hom ≫ N.alpha = L.alpha
        rw [g.property, hf]⟩
      invFun := fun g ↦ ⟨e.inv ≫ g.val, by
        change e.inv.hom ≫ g.val.hom ≫ N.alpha = K.alpha
        rw [g.property, hinv]⟩
      left_inv := by
        intro g
        apply Subtype.ext
        change e.inv ≫ (f ≫ g.val) = g.val
        rw [← Category.assoc]
        change (e.inv ≫ e.hom) ≫ g.val = g.val
        rw [e.inv_hom_id, Category.id_comp]
      right_inv := by
        intro g
        apply Subtype.ext
        change f ≫ (e.inv ≫ g.val) = g.val
        rw [← Category.assoc]
        change (e.hom ≫ e.inv) ≫ g.val = g.val
        rw [e.hom_inv_id, Category.id_comp] }
  have hE (g) : i ≫ (E g).val.hom = v ≫ g.val.hom := by
    change i ≫ f.hom ≫ g.val.hom = _
    rw [← Category.assoc, hfi]
  refine ⟨?_, ?_⟩
  · intro g g' h
    apply E.injective
    apply (hL N).1
    change i ≫ (E g).val.hom = i ≫ (E g').val.hom
    rw [hE, hE]
    exact h
  · ext w
    constructor
    · rintro ⟨g, rfl⟩
      change (v ≫ g.val.hom) ≫ N.alpha = γ
      rw [Category.assoc, g.property, hv]
    · intro hw
      have hw' : w ∈ Set.range (fun g :
          {g : L.monoidSheaf ⟶ N.monoidSheaf // g.hom ≫ N.alpha = L.alpha} ↦
          i ≫ g.val.hom) := by
        rw [(hL N).2]
        exact hw
      obtain ⟨g, hg⟩ := hw'
      refine ⟨E.symm g, ?_⟩
      change v ≫ (E.symm g).val.hom = w
      rw [← hE, E.apply_symm_apply]
      exact hg

end AlgebraicGeometry
