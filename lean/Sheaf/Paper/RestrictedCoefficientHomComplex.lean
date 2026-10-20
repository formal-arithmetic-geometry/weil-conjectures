/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.Paper.RestrictedCoefficientHom
public import Sheaf.Algebra.Homology.BilinearHomComplex
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Homology.Functor
import Sheaf.Algebra.Homology.HomComplexProjections
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.CategoryTheory.Whiskering

/-! # Coefficient Hom complexes over a ring-sheaf extension

Source: Stacks Project, Algebraization, Tag 099I
(blueprint: lem-weil-pbc-restricted-coefficient-hom-complex).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

private theorem productComplexComparison
    {D : Type u} [Category D] [Preadditive D]
    (K L : CochainComplex D ℤ) (T : ℤ → ℤ → D)
    (π : ∀ n p q : ℤ, p + n = q → (K.X n ⟶ T p q))
    (ρ : ∀ n p q : ℤ, p + n = q → (L.X n ⟶ T p q))
    (hπ : ∀ n, IsLimit (Fan.mk (K.X n) (fun p ↦ π n p (p + n) rfl)))
    (hρ : ∀ n, IsLimit (Fan.mk (L.X n) (fun p ↦ ρ n p (p + n) rfl)))
    (post : ∀ p q q', T p q' ⟶ T p q)
    (pre : ∀ p p' q, T p' q ⟶ T p q)
    (hdK : ∀ n m p q q' p' : ℤ, n + 1 = m →
      ∀ (h : p + m = q) (h' : p + n = q') (h'' : p' + n = q),
      K.d n m ≫ π m p q h = π n p q' h' ≫ post p q q' -
        n.negOnePow • (π n p' q h'' ≫ pre p p' q))
    (hdL : ∀ n m p q q' p' : ℤ, n + 1 = m →
      ∀ (h : p + m = q) (h' : p + n = q') (h'' : p' + n = q),
      L.d n m ≫ ρ m p q h = ρ n p q' h' ≫ post p q q' -
        n.negOnePow • (ρ n p' q h'' ≫ pre p p' q)) :
    ∃ e : K ≅ L, ∀ (n p q : ℤ) (h : p + n = q),
      e.hom.f n ≫ ρ n p q h = π n p q h := by
  let a (n : ℤ) := (hπ n).conePointUniqueUpToIso (hρ n)
  have ha (n p q : ℤ) (h : p + n = q) :
      (a n).hom ≫ ρ n p q h = π n p q h := by
    subst q
    exact IsLimit.conePointUniqueUpToIso_hom_comp (hπ n) (hρ n) ⟨p⟩
  let E : K ≅ L := HomologicalComplex.Hom.isoOfComponents a (by
    intro n m hnm
    apply Fan.IsLimit.hom_ext (hρ m)
    intro p
    change ((a n).hom ≫ L.d n m) ≫ ρ m p (p + m) rfl =
      (K.d n m ≫ (a m).hom) ≫ ρ m p (p + m) rfl
    rw [Category.assoc,
      hdL n m p (p + m) (p + n) (p + m - n) hnm rfl rfl (by omega),
      Preadditive.comp_sub, Linear.comp_units_smul,
      ← Category.assoc, ha, ← Category.assoc, ha, Category.assoc, ha,
      hdK n m p (p + m) (p + n) (p + m - n) hnm rfl rfl (by omega)])
  exact ⟨E, ha⟩

private theorem mapTwoTermDifferential
    {D E : Type u} [Category D] [Category E] [Preadditive D] [Preadditive E]
    (r : D ⥤ E) [r.Additive] {K K' T T₁ T₂ : D} {U U₁ U₂ : E}
    (d : K ⟶ K') (π : K' ⟶ T) (p₁ : K ⟶ T₁) (p₂ : K ⟶ T₂)
    (t₁ : T₁ ⟶ T) (t₂ : T₂ ⟶ T) (c : r.obj T ⟶ U)
    (c₁ : r.obj T₁ ⟶ U₁) (c₂ : r.obj T₂ ⟶ U₂)
    (u₁ : U₁ ⟶ U) (u₂ : U₂ ⟶ U) (s : ℤˣ)
    (hd : d ≫ π = p₁ ≫ t₁ - s • (p₂ ≫ t₂))
    (h₁ : r.map t₁ ≫ c = c₁ ≫ u₁) (h₂ : r.map t₂ ≫ c = c₂ ≫ u₂) :
    r.map d ≫ (r.map π ≫ c) =
      (r.map p₁ ≫ c₁) ≫ u₁ - s • ((r.map p₂ ≫ c₂) ≫ u₂) := by
  rw [← Category.assoc, ← r.map_comp, hd, r.map_sub, r.map_units_smul,
    Preadditive.sub_comp, Linear.units_smul_comp]
  simp only [r.map_comp, Category.assoc, h₁, h₂]

private theorem projectionIntertwine
    {D E : Type u} [Category D] [Category E] (r : D ⥤ E)
    {A A' B B' : D} {C C' T T' : E}
    (m : A ⟶ A') (p : A ⟶ B) (p' : A' ⟶ B') (t : B ⟶ B')
    (v : C ⟶ C') (ρ : C ⟶ T) (ρ' : C' ⟶ T') (u : T ⟶ T')
    (e : r.obj A ⟶ C) (e' : r.obj A' ⟶ C')
    (c : r.obj B ⟶ T) (c' : r.obj B' ⟶ T')
    (hm : m ≫ p' = p ≫ t) (hv : v ≫ ρ' = ρ ≫ u)
    (he : e ≫ ρ = r.map p ≫ c) (he' : e' ≫ ρ' = r.map p' ≫ c')
    (hc : r.map t ≫ c' = c ≫ u) :
    (r.map m ≫ e') ≫ ρ' = (e ≫ v) ≫ ρ' := by
  rw [Category.assoc, he', ← Category.assoc, ← r.map_comp, hm, r.map_comp,
    Category.assoc, hc, ← Category.assoc, ← he, Category.assoc,
    ← hv, ← Category.assoc]

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)

set_option backward.isDefEq.respectTransparency false in
private theorem coefficientRestriction_preservesLimits :
    PreservesLimitsOfSize.{u, u} (restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)) := by
    let r := restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
    let U := SheafOfModules.forget.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⋙
      PresheafOfModules.toPresheaf.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj
    have : PreservesLimitsOfSize.{u, u} (r ⋙ U) :=
      inferInstanceAs (PreservesLimitsOfSize.{u, u}
        (SheafOfModules.forget.{u}
            ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B) ⋙
          PresheafOfModules.toPresheaf.{u}
            ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj))
    have : ReflectsLimitsOfSize.{u, u} U := reflectsLimits_of_reflectsIsomorphisms
    exact preservesLimits_of_reflects_of_preserves r U

set_option backward.isDefEq.respectTransparency false in
private theorem coefficientHomComplex_comparison
    (H : (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))ᵒᵖ ×
      SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))
    (i : H ⋙ restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) ≅
      (restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).op.prod
        (𝟭 _) ⋙ Functor.uncurry.obj (homFunctor.{u, u, u, u} R))
    (G : (CochainComplex (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) ℤ)ᵒᵖ ⥤
      CochainComplex (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ ⥤
      CochainComplex (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) ℤ)
    (hG : ProductHomComplexSpecification (Functor.curry.obj H) G) :
    Nonempty (Functor.uncurry.obj G ⋙
      (restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
        ).mapHomologicalComplex (.up ℤ) ≅
      ((restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
        ).mapHomologicalComplex (.up ℤ)).op.prod (𝟭 _) ⋙
        Functor.uncurry.obj (homComplexFunctor (R := R))) := by
  let Hc := Functor.curry.obj H
  let MR := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  let MB := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)
  let r := restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  let rc := r.mapHomologicalComplex (.up ℤ)
  have : PreservesLimitsOfSize.{u, u} r := coefficientRestriction_preservesLimits φ
  have : PreservesLimitsOfSize.{0, 0} r := preservesLimitsOfSize_shrink r
  let T : MBᵒᵖ × MR ⥤ MR :=
    { obj X := homObj (R := R) (r.obj X.1.unop) X.2
      map f := homObjMap (R := R) (r.map f.1.unop) f.2
      map_id X := by
        change homObjMap (R := R) (r.map (𝟙 X.1.unop)) (𝟙 X.2) = _
        rw [r.map_id]
        exact homObjMap_id (R := R) (M := r.obj X.1.unop) (N := X.2)
      map_comp f g := by
        change homObjMap (R := R) (r.map (g.1.unop ≫ f.1.unop)) (f.2 ≫ g.2) = _
        rw [r.map_comp]
        exact (homObjMap_comp_homObjMap (r.map f.1.unop) (r.map g.1.unop) f.2 g.2).symm }
  let j : r.op.prod (𝟭 _) ⋙ Functor.uncurry.obj (homFunctor.{u, u, u, u} R) ≅ T :=
    NatIso.ofComponents (fun X ↦ Iso.refl _) (by
      intro X Y f
      change homObjMap (R := R) (r.map f.1.unop) (𝟙 X.2) ≫
          homObjMap (R := R) (𝟙 (r.obj Y.1.unop)) f.2 ≫ 𝟙 _ =
        𝟙 _ ≫ homObjMap (R := R) (r.map f.1.unop) f.2
      simp only [Category.comp_id, Category.id_comp,
        homObjMap_comp_homObjMap])
  let c : Functor.uncurry.obj Hc ⋙ r ≅ T :=
    Functor.isoWhiskerRight (Functor.currying.counitIso.app H) r ≪≫ i ≪≫ j
  obtain ⟨π, hπ, hd, hm⟩ := hG
  obtain ⟨ρ, hρ, hdρ, hmρ⟩ := homComplex_projections_exists (R := R)
  have hc {A A' : MB} {N N' : MR} (f : A' ⟶ A) (g : N ⟶ N') :
      r.map ((Functor.uncurry.obj Hc).map
          (X := (op A, N)) (Y := (op A', N')) (f.op, g)) ≫ c.hom.app (op A', N') =
        c.hom.app (op A, N) ≫
          homObjMap (R := R) (M := r.obj A) (M' := r.obj A')
            (N := N) (N' := N') (r.map f) g := by
    exact c.hom.naturality (show (op A, N) ⟶ (op A', N') from (f.op, g))
  let aπ (L : CochainComplex MB ℤ) (M : CochainComplex MR ℤ)
      (n p q : ℤ) (h : p + n = q) :
      r.obj (((G.obj (op L)).obj M).X n) ⟶
        homObj (R := R) (r.obj (L.X p)) (M.X q) :=
    r.map (π L M n p q h) ≫ c.hom.app (op (L.X p), M.X q)
  have hπr (L : CochainComplex MB ℤ) (M : CochainComplex MR ℤ) (n : ℤ) :
      IsLimit (Fan.mk (r.obj (((G.obj (op L)).obj M).X n))
        (fun p ↦ aπ L M n p (p + n) rfl)) := by
    let T (p : ℤ) := H.obj (op (L.X p), M.X (p + n))
    let h := isLimitFanMkObjOfIsLimit r T
      (fun p ↦ π L M n p (p + n) rfl) (hπ L M n).some
    let e : Discrete.functor (fun p : ℤ ↦ r.obj (H.obj (op (L.X p), M.X (p + n)))) ≅
        Discrete.functor (fun p : ℤ ↦ homObj (R := R) (r.obj (L.X p)) (M.X (p + n))) :=
      Discrete.natIso (fun p : Discrete ℤ ↦ c.app (op (L.X p.as), M.X (p.as + n)))
    exact (IsLimit.postcomposeHomEquiv e _).symm h
  have hE (L : CochainComplex MB ℤ) (M : CochainComplex MR ℤ) :
      ∃ e : rc.obj ((G.obj (op L)).obj M) ≅
          ((homComplexFunctor (R := R)).obj (op (rc.obj L))).obj M,
        ∀ (n p q : ℤ) (h : p + n = q),
          e.hom.f n ≫ ρ (rc.obj L) M n p q h = aπ L M n p q h := by
    apply productComplexComparison
      (rc.obj ((G.obj (op L)).obj M))
      (((homComplexFunctor (R := R)).obj (op (rc.obj L))).obj M)
      (fun p q ↦ homObj (R := R) (r.obj (L.X p)) (M.X q))
      (aπ L M) (ρ (rc.obj L) M) (hπr L M) (fun n ↦ (hρ (rc.obj L) M n).some)
      (fun p q q' ↦ homObjMap (R := R) (𝟙 (r.obj (L.X p))) (M.d q' q))
      (fun p p' q ↦ homObjMap (R := R) (r.map (L.d p p')) (𝟙 (M.X q)))
    · intro n m p q q' p' hnm hpq hq' hp'
      exact mapTwoTermDifferential r _ _ _ _ _ _ _ _ _ _ _ _
        (hd L M n m p q q' p' hnm hpq hq' hp')
        (by simpa only [r.map_id] using hc (𝟙 (L.X p)) (M.d q' q))
        (hc (L.d p p') (𝟙 (M.X q)))
    · exact hdρ (rc.obj L) M
  choose e he using hE
  refine ⟨NatIso.ofComponents (fun X ↦ e X.1.unop X.2) ?_⟩
  intro X Y f
  apply HomologicalComplex.hom_ext
  intro n
  apply Fan.IsLimit.hom_ext (hρ (rc.obj Y.1.unop) Y.2 n).some
  intro p
  let sourceMap := (G.map f.1).app X.2 ≫ (G.obj Y.1).map f.2
  let targetMap := ((homComplexFunctor (R := R)).map (rc.map f.1.unop).op).app X.2 ≫
    ((homComplexFunctor (R := R)).obj (op (rc.obj Y.1.unop))).map f.2
  change (r.map (sourceMap.f n) ≫ (e Y.1.unop Y.2).hom.f n) ≫
      ρ (rc.obj Y.1.unop) Y.2 n p (p + n) rfl =
    ((e X.1.unop X.2).hom.f n ≫ targetMap.f n) ≫
      ρ (rc.obj Y.1.unop) Y.2 n p (p + n) rfl
  exact projectionIntertwine r (sourceMap.f n)
    (π X.1.unop X.2 n p (p + n) rfl) (π Y.1.unop Y.2 n p (p + n) rfl)
    ((Functor.uncurry.obj Hc).map
      (X := (op (X.1.unop.X p), X.2.X (p + n)))
      (Y := (op (Y.1.unop.X p), Y.2.X (p + n)))
      ((f.1.unop.f p).op, f.2.f (p + n)))
    (targetMap.f n)
    (ρ (rc.obj X.1.unop) X.2 n p (p + n) rfl)
    (ρ (rc.obj Y.1.unop) Y.2 n p (p + n) rfl)
    (homObjMap (R := R) (r.map (f.1.unop.f p)) (f.2.f (p + n)))
    ((e X.1.unop X.2).hom.f n) ((e Y.1.unop Y.2).hom.f n)
    (c.hom.app (op (X.1.unop.X p), X.2.X (p + n)))
    (c.hom.app (op (Y.1.unop.X p), Y.2.X (p + n)))
    (hm X.1.unop Y.1.unop X.2 Y.2 f.1.unop f.2 n p (p + n) rfl)
    (hmρ (rc.obj X.1.unop) (rc.obj Y.1.unop) X.2 Y.2
      (rc.map f.1.unop) f.2 n p (p + n) rfl)
    (he X.1.unop X.2 n p (p + n) rfl) (he Y.1.unop Y.2 n p (p + n) rfl)
    (hc (f.1.unop.f p) (f.2.f (p + n)))

set_option backward.isDefEq.respectTransparency false in
/-- The coefficient internal Hom extends to the product Hom-complex bifunctor.
Source: Stacks Project, Algebraization, Tag 099I, construction of E prime
(blueprint: lem-weil-pbc-restricted-coefficient-hom-complex).
Proof: construct the internal-Hom coefficient bifunctor and its precomposition
B-action. It is additive separately in both arguments. These assertions make
its curried form additive as a functor into the functor category: check addition
at each target object. Apply the product Hom-complex construction, with degree
n the product of the coefficient Homs from L to M shifted by n. Its differential
and functorial maps are sums and composites of B-linear maps, and have exactly
the projection formulas below. The square-zero calculation cancels the mixed
terms with the consecutive-degree signs. Restriction preserves arbitrary products:
compose it with the underlying presheaf functor, which reflects limits, and
use its unchanged underlying presheaf. Transport the coefficient comparison
through these products and use the product universal property to compare it
with the chosen R-valued Hom complex. The projection formulas and additivity
show that the resulting degreewise isomorphisms commute with differentials.
The induced-map formulas and naturality of the coefficient comparison show
that these chain isomorphisms are natural in both complex variables. No
boundedness or flatness is needed. -/
theorem exists_restrictedCoefficientHomComplexFunctor :
    let MR := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
    let MB := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)
    let r := restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
    ∃ H : MBᵒᵖ × MR ⥤ MB,
      ∃ i : H ⋙ r ≅ (r.op.prod (𝟭 _) ⋙ Functor.uncurry.obj (homFunctor.{u, u, u, u} R)),
        (∀ (M : SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))
          (N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
          (U : C)
          (b : ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj.obj (op U))
          (h : (H.obj (op M, N)).val.obj (op U)) (W : Over U)
          (m : M.val.obj (op W.left)),
          (((i.hom.app (op M, N)).val.app (op U)).hom
            (@SMul.smul _ _ ((H.obj (op M, N)).val.obj (op U)).isModule.toSMul b h)).app (op W) m =
            (((i.hom.app (op M, N)).val.app (op U)).hom h).app (op W)
              (@SMul.smul _ _ (M.val.obj (op W.left)).isModule.toSMul
                (B.obj.map W.hom.op b) m)) ∧
        ∃ G : (CochainComplex MB ℤ)ᵒᵖ ⥤ CochainComplex MR ℤ ⥤ CochainComplex MB ℤ,
          ProductHomComplexSpecification (Functor.curry.obj H) G ∧
          Nonempty (Functor.uncurry.obj G ⋙ r.mapHomologicalComplex (.up ℤ) ≅
            (r.mapHomologicalComplex (.up ℤ)).op.prod (𝟭 _) ⋙
              Functor.uncurry.obj (homComplexFunctor (R := R))) := by
  obtain ⟨H, i, haction, haddRight, haddLeft⟩ := exists_restrictedCoefficientHomFunctor φ
  refine ⟨H, i, haction, ?_⟩
  let Hc := Functor.curry.obj H
  have : ∀ M, (Hc.obj M).Additive := haddRight
  have : Hc.Additive := by
    constructor
    intro X Y f g
    apply NatTrans.ext
    funext N
    exact (haddLeft N).map_add
  obtain ⟨G, hG⟩ := exists_bilinearHomComplexFunctor Hc
  refine ⟨G, hG, ?_⟩
  exact coefficientHomComplex_comparison φ H i G hG

end SheafOfModules
