/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.TraceFormula.CoherentTopos
public import WeilConjectures.AlgebraicGeometry.OrientedNearbyCycles.OrientedNearbyCycles
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Epimorphic families and finite quasi-compact cover calculus

Source: Stacks Project, `sites.tex`, Tags 00WN, 00W2, 00WK, 0GMP and 0GMQ.

The site and all section and index sets lie in the common containing universe
`max u v w`. Covering sieves express local
lifting independently of the choice of a precoverage presenting the topology.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Coproducts in the containing universe, using Mathlib's sheafification construction
with the discrete diagram shape specified explicitly. This packages the existing
colimit structure so typeclass search need not rediscover its diagram universes.
Source: Stacks Project, Sites, Tag 00WB, the sheafification universal property. -/
instance (priority := 2000) toposFiniteCoverCoproducts
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) :
    HasCoproducts.{max u v w} (Sheaf J (Type (max u v w))) :=
  fun I ↦ Sheaf.instHasColimitsOfShape (K := Discrete I) (D := Type (max u v w))

private theorem epi_desc_iff {E : Type*} [Category E] {I : Type*}
    (X : I → E) [HasCoproduct X] {Y : E} (f : ∀ i, X i ⟶ Y) :
    Epi (Sigma.desc f) ↔
      ∀ (Z : E) (a b : Y ⟶ Z), (∀ i, f i ≫ a = f i ≫ b) → a = b := by
  constructor
  · intro h Z a b hab
    apply (cancel_epi (Sigma.desc f)).mp
    apply Sigma.hom_ext
    intro i
    simpa only [Sigma.ι_comp_desc_assoc] using hab i
  · intro h
    constructor
    intro Z a b hab
    apply h Z a b
    intro i
    simpa only [Sigma.ι_comp_desc_assoc] using
      congrArg (fun k ↦ Sigma.ι X i ≫ k) hab

private theorem family_local_iff
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (I : Type (max u v w)) (X : I → Sheaf J (Type (max u v w)))
    (Y : Sheaf J (Type (max u v w))) (f : ∀ i, X i ⟶ Y) :
    Epi (Sigma.desc f) ↔
      ∀ (U : C) (y : Y.obj.obj (op U)),
        ∃ S : Sieve U, S ∈ J U ∧
          ∀ (V : C) (a : V ⟶ U), S a →
            ∃ (i : I) (x : (X i).obj.obj (op V)),
              (f i).hom.app (op V) x = Y.obj.map a.op y := by
  constructor
  · intro hf
    let G : Subfunctor Y.obj :=
      { obj := fun U ↦ {y | ∃ i x, (f i).hom.app U x = y}
        map := by
          intro U V a y
          rintro ⟨i, x, rfl⟩
          exact ⟨i, (X i).obj.map a x, NatTrans.naturality_apply (f i).hom a x⟩ }
    let H : Sheaf J (Type (max u v w)) :=
      ⟨(G.sheafify J).toFunctor, by
        rw [isSheaf_iff_isSheaf_of_type]
        exact G.sheafify_isSheaf ((isSheaf_iff_isSheaf_of_type J Y.obj).mp Y.property)⟩
    let m : H ⟶ Y := ⟨(G.sheafify J).ι⟩
    let l : ∀ i, X i ⟶ H := fun i ↦
      ⟨{
        app := fun U ↦ ↾fun x ↦
          ⟨(f i).hom.app U x, G.le_sheafify J U ⟨i, x, rfl⟩⟩
        naturality := by
          intro U V a
          ext x
          apply Subtype.ext
          exact NatTrans.naturality_apply (f i).hom a x }⟩
    have fac (i : I) : l i ≫ m = f i := rfl
    have hm : Epi m := by
      apply epi_of_epi_fac (f := Sigma.desc l) (h := Sigma.desc f)
      apply Sigma.hom_ext
      intro i
      simpa only [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc] using fac i
    have : Mono m := (sheafToPresheaf J _).mono_of_mono_map
      (inferInstanceAs (Mono (G.sheafify J).ι))
    have : IsIso m := isIso_of_mono_of_epi m
    have hG : G.sheafify J = ⊤ :=
      (Subfunctor.eq_top_iff_isIso _).mpr
        (inferInstanceAs (IsIso ((sheafToPresheaf J _).map m)))
    intro U y
    have hy : y ∈ (G.sheafify J).obj (op U) := by rw [hG]; trivial
    exact ⟨G.sieveOfSection y, hy, fun V a ha ↦ ha⟩
  · intro h
    apply (Sheaf.isLocallySurjective_iff_epi (Sigma.desc f)).mp
    constructor
    intro U y
    obtain ⟨S, hS, hlocal⟩ := h U y
    apply J.superset_covering (S := S) _ hS
    intro V a ha
    obtain ⟨i, x, hx⟩ := hlocal V a ha
    refine ⟨(Sigma.ι X i).hom.app (op V) x, ?_⟩
    have hi := congrArg (fun k : X i ⟶ Y ↦ k.hom.app (op V) x) (Sigma.ι_comp_desc f i)
    exact hi.trans hx

private theorem pullback_section
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {X Y Z : Sheaf J (Type (max u v w))} (f : X ⟶ Y) (g : Z ⟶ Y)
    (U : C) (x : X.obj.obj (op U)) (z : Z.obj.obj (op U))
    (h : f.hom.app (op U) x = g.hom.app (op U) z) :
    ∃ p : (pullback f g).obj.obj (op U),
      (pullback.fst f g).hom.app (op U) p = x ∧
      (pullback.snd f g).hom.app (op U) p = z := by
  let F := sheafToPresheaf J (Type (max u v w)) ⋙
    (evaluation Cᵒᵖ (Type (max u v w))).obj (op U)
  exact Types.exists_of_isPullback (F.map_isPullback (IsPullback.of_hasPullback f g)) x z h

private theorem family_pullback_epi
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (I : Type (max u v w)) (X : I → Sheaf J (Type (max u v w)))
    (Y Z : Sheaf J (Type (max u v w))) (f : ∀ i, X i ⟶ Y) (g : Z ⟶ Y)
    (hf : Epi (Sigma.desc f)) :
    Epi (Sigma.desc (fun i ↦ pullback.snd (f i) g)) := by
  apply (family_local_iff J I _ Z _).mpr
  intro U z
  obtain ⟨S, hS, hlocal⟩ := (family_local_iff J I X Y f).mp hf U (g.hom.app _ z)
  refine ⟨S, hS, ?_⟩
  intro V a ha
  obtain ⟨i, x, hx⟩ := hlocal V a ha
  obtain ⟨p, _, hp⟩ := pullback_section J (f i) g V x (Z.obj.map a.op z)
    (hx.trans (NatTrans.naturality_apply g.hom a.op z).symm)
  exact ⟨i, p, hp⟩

private theorem single_pullback_epi
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (X Y Z : Sheaf J (Type (max u v w))) (e : X ⟶ Y) (g : Z ⟶ Y)
    (he : Epi e) : Epi (pullback.snd e g) := by
  have : Sheaf.IsLocallySurjective e := (Sheaf.isLocallySurjective_iff_epi e).mpr he
  apply (Sheaf.isLocallySurjective_iff_epi (pullback.snd e g)).mp
  constructor
  intro U z
  apply J.superset_covering (S := Presheaf.imageSieve e.hom (g.hom.app _ z)) _
    (Presheaf.imageSieve_mem J e.hom (g.hom.app _ z))
  intro V a ha
  obtain ⟨x, hx⟩ := ha
  obtain ⟨p, _, hp⟩ := pullback_section J e g V x (Z.obj.map a.op z)
    (hx.trans (NatTrans.naturality_apply g.hom a.op z).symm)
  exact ⟨p, hp⟩

private theorem product_family_epi
    {E : Type*} [Category E] [HasPullbacks E] [HasCoproducts.{w} E]
    (hpb : ∀ (I : Type w) (X : I → E) (Y Z : E)
      (f : ∀ i, X i ⟶ Y) (g : Z ⟶ Y),
      Epi (Sigma.desc f) → Epi (Sigma.desc (fun i ↦ pullback.snd (f i) g)))
    (I K : Type w) (X : I → E) (Y : K → E) (A B D : E)
    (f : ∀ i, X i ⟶ B) (g : ∀ k, Y k ⟶ D) (b : B ⟶ A) (d : D ⟶ A)
    (hf : Epi (Sigma.desc f)) (hg : Epi (Sigma.desc g)) :
    Epi (Sigma.desc (fun p : I × K ↦
      pullback.map (f p.1 ≫ b) (g p.2 ≫ d) b d (f p.1) (g p.2) (𝟙 A)
        (Category.comp_id _) (Category.comp_id _))) := by
  apply (epi_desc_iff _ _).mpr
  intro T a a' haa
  have h₁ := hpb I X B (pullback b d) f (pullback.fst b d) hf
  apply (epi_desc_iff _ _).mp h₁ T a a'
  intro i
  let P := pullback (f i) (pullback.fst b d)
  let r : P ⟶ D := pullback.snd (f i) (pullback.fst b d) ≫ pullback.snd b d
  have h₂ := hpb K Y D P g r hg
  apply (epi_desc_iff _ _).mp h₂ T
    (pullback.snd (f i) (pullback.fst b d) ≫ a)
    (pullback.snd (f i) (pullback.fst b d) ≫ a')
  intro k
  let q : pullback (g k) r ⟶ pullback (f i ≫ b) (g k ≫ d) :=
    pullback.lift (pullback.snd (g k) r ≫ pullback.fst (f i) (pullback.fst b d))
      (pullback.fst (g k) r) (by
        simp only [Category.assoc]
        rw [pullback.condition_assoc, pullback.condition]
        simpa only [r, Category.assoc] using
          (pullback.condition_assoc (f := g k) (g := r) d).symm)
  have hq : q ≫ pullback.map (f i ≫ b) (g k ≫ d) b d (f i) (g k) (𝟙 A)
      (Category.comp_id _) (Category.comp_id _) =
      pullback.snd (g k) r ≫ pullback.snd (f i) (pullback.fst b d) := by
    apply pullback.hom_ext <;> simp [q, r, pullback.condition, Category.assoc]
  simpa only [← Category.assoc, ← hq] using
    congrArg (fun h ↦ q ≫ h) (haa (i, k))

private theorem quasiCompact_of_epi
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (X Y : Sheaf J (Type (max u v w))) (e : X ⟶ Y)
    (he : Epi e) (hX : IsQuasiCompactObject.{max u v w} X) :
    IsQuasiCompactObject.{max u v w} Y := by
  classical
  intro I B f hf
  obtain ⟨s, hs⟩ := hX I (fun i ↦ pullback (f i) e)
    (fun i ↦ pullback.snd (f i) e) (family_pullback_epi J I B Y X f e hf)
  refine ⟨s, (epi_desc_iff _ _).mpr ?_⟩
  intro T a b hab
  apply (cancel_epi e).mp
  apply (epi_desc_iff _ _).mp hs T (e ≫ a) (e ≫ b)
  intro i
  calc
    pullback.snd (f i.1) e ≫ e ≫ a = pullback.fst (f i.1) e ≫ f i.1 ≫ a := by
      rw [← Category.assoc, ← pullback.condition, Category.assoc]
    _ = pullback.fst (f i.1) e ≫ f i.1 ≫ b := by rw [hab i]
    _ = pullback.snd (f i.1) e ≫ e ≫ b := by
      rw [← Category.assoc, pullback.condition, Category.assoc]

private theorem quasiCompact_coproduct
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (I : Type (max u v w)) [Finite I] (X : I → Sheaf J (Type (max u v w)))
    (hX : ∀ i, IsQuasiCompactObject.{max u v w} (X i)) :
    IsQuasiCompactObject.{max u v w} (∐ X) := by
  classical
  let := Fintype.ofFinite I
  intro K B f hf
  have hh (i : I) : ∃ s : Finset K,
      Epi (Sigma.desc (fun k : s ↦ pullback.snd (f k.1) (Sigma.ι X i))) :=
    hX i K (fun k ↦ pullback (f k) (Sigma.ι X i)) _
      (family_pullback_epi J K B (∐ X) (X i) f (Sigma.ι X i) hf)
  choose s hs using hh
  let s₀ : Finset K := Finset.univ.biUnion s
  refine ⟨s₀, (epi_desc_iff _ _).mpr ?_⟩
  intro T a b hab
  apply Sigma.hom_ext
  intro i
  apply (epi_desc_iff _ _).mp (hs i) T (Sigma.ι X i ≫ a) (Sigma.ι X i ≫ b)
  intro k
  have hk : k.1 ∈ s₀ := Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, k.2⟩
  calc
    pullback.snd (f k.1) (Sigma.ι X i) ≫ Sigma.ι X i ≫ a =
        pullback.fst (f k.1) (Sigma.ι X i) ≫ f k.1 ≫ a := by
      rw [← Category.assoc, ← pullback.condition, Category.assoc]
    _ = pullback.fst (f k.1) (Sigma.ι X i) ≫ f k.1 ≫ b := by rw [hab ⟨k.1, hk⟩]
    _ = pullback.snd (f k.1) (Sigma.ι X i) ≫ Sigma.ι X i ≫ b := by
      rw [← Category.assoc, pullback.condition, Category.assoc]

/-- Joint epimorphy is equivalent to local lifting through individual family members,
and is stable under pullback and fibre products of families. Epimorphic images and
finite coproducts preserve quasi-compactness, including the empty coproduct. Hence a
finite jointly epimorphic family of quasi-compact objects has quasi-compact target.

Source: Stacks Project, Tags 00WN, 00W2, 00WK, 0GMP and 0GMQ. -/
theorem topos_finite_cover_calculus
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) :
    (∀ (I : Type (max u v w)) (X : I → Sheaf J (Type (max u v w)))
      (Y : Sheaf J (Type (max u v w))) (f : ∀ i, X i ⟶ Y),
      Epi (Sigma.desc f) ↔
        ∀ (U : C) (y : Y.obj.obj (op U)),
          ∃ S : Sieve U, S ∈ J U ∧
            ∀ (V : C) (a : V ⟶ U), S a →
              ∃ (i : I) (x : (X i).obj.obj (op V)),
                (f i).hom.app (op V) x = Y.obj.map a.op y) ∧
    (∀ (I : Type (max u v w)) (X : I → Sheaf J (Type (max u v w)))
      (Y Z : Sheaf J (Type (max u v w))) (f : ∀ i, X i ⟶ Y) (g : Z ⟶ Y),
      Epi (Sigma.desc f) → Epi (Sigma.desc (fun i ↦ pullback.snd (f i) g))) ∧
    (∀ (X Y Z : Sheaf J (Type (max u v w))) (e : X ⟶ Y) (g : Z ⟶ Y),
      Epi e → Epi (pullback.snd e g)) ∧
    (∀ (I K : Type (max u v w)) (X : I → Sheaf J (Type (max u v w)))
      (Y : K → Sheaf J (Type (max u v w))) (A B D : Sheaf J (Type (max u v w)))
      (f : ∀ i, X i ⟶ B) (g : ∀ k, Y k ⟶ D) (b : B ⟶ A) (d : D ⟶ A),
      Epi (Sigma.desc f) → Epi (Sigma.desc g) →
        Epi (Sigma.desc (fun p : I × K ↦
          pullback.map (f p.1 ≫ b) (g p.2 ≫ d) b d (f p.1) (g p.2) (𝟙 A)
            (Category.comp_id _) (Category.comp_id _)))) ∧
    (∀ (X Y : Sheaf J (Type (max u v w))) (e : X ⟶ Y),
      Epi e → IsQuasiCompactObject.{max u v w} X →
        IsQuasiCompactObject.{max u v w} Y) ∧
    (∀ (I : Type (max u v w)) [Finite I] (X : I → Sheaf J (Type (max u v w))),
      (∀ i, IsQuasiCompactObject.{max u v w} (X i)) →
        IsQuasiCompactObject.{max u v w} (∐ X)) ∧
    (∀ (I : Type (max u v w)) [Finite I] (X : I → Sheaf J (Type (max u v w)))
      (Y : Sheaf J (Type (max u v w))) (f : ∀ i, X i ⟶ Y),
      (∀ i, IsQuasiCompactObject.{max u v w} (X i)) → Epi (Sigma.desc f) →
        IsQuasiCompactObject.{max u v w} Y) := by
  refine ⟨family_local_iff J, family_pullback_epi J, single_pullback_epi J,
    product_family_epi (family_pullback_epi J), quasiCompact_of_epi J, quasiCompact_coproduct J, ?_⟩
  intro I _ X Y f hX hf
  exact quasiCompact_of_epi J (∐ X) Y (Sigma.desc f) hf
    (quasiCompact_coproduct J I X hX)

end CategoryTheory
