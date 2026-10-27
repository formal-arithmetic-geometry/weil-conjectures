/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Sites.SubcanonicalOver
import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFpqcLocalExtension
import Sheaf.AlgebraicGeometry.FpqcRelativeCriterion

/-!
# Morphisms to an algebraic space satisfy fpqc descent

Source: Stacks Project, Descent of Spaces, Tag 04P2,
`lemma-fpqc-universal-effective-epimorphisms`, specialized to scheme domains;
Properties of Spaces, Tag 0APL, `proposition-sheaf-fpqc` (Gabber's proof)
(blueprint: lem-a1-algebraic-space-fpqc-sheaf).

Maps from an `S`-scheme to `E` are sections of its defining fppf sheaf, by Yoneda.
The overlap is the scheme pullback with its structure map through the first projection;
`Limits.pullback.condition_assoc` makes the second projection an `S`-morphism too.
-/

@[expose] public section

universe u w

open CategoryTheory Opposite

namespace AlgebraicGeometry.AlgebraicSpace

private theorem hom_eq_of_fpqc_restrictions
    {S : Scheme.{u}} (E : AlgebraicSpace S) (T : Over S) {I : Type w}
    (U : I → Over S) (v : ∀ i, U i ⟶ T)
    (hv : Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (v i).left) ∈
      Scheme.fpqcPrecoverage T.left)
    (a b : yoneda.obj T ⟶ E.obj.obj)
    (hab : ∀ i, yoneda.map (v i) ≫ a = yoneda.map (v i) ≫ b) : a = b := by
  classical
  obtain ⟨P, p, q, hp, _⟩ := E.property.1 T (Limits.prod.lift a b)
  have : Mono (yoneda.map p) := hp.mono_snd_of_mono
  have : Mono p := yoneda.mono_of_mono_map inferInstance
  let r (i : I) : U i ⟶ P := yoneda.preimage
    (hp.lift (yoneda.map (v i) ≫ a) (yoneda.map (v i)) (by
      apply Limits.prod.hom_ext <;> simp [hab i]))
  have hr (i : I) : r i ≫ p = v i := by
    apply yoneda.map_injective
    simp [r]
  have hcover : Sieve.ofArrows U v ∈ Scheme.fpqcTopology.over S T := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact Precoverage.generate_mem_toGrothendieck hv
  have hP : Presieve.IsSheafFor (yoneda.obj P) (Presieve.ofArrows U v) :=
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _).isSheafFor _ hcover
  obtain ⟨r₀, hr₀, _⟩ := ((Presieve.isSheafFor_arrows_iff _ _).mp hP) r (by
    intro i j Z f g hfg
    change f ≫ r i = g ≫ r j
    apply (cancel_mono p).mp
    simpa only [Category.assoc, hr] using hfg)
  change ∀ i, v i ≫ r₀ = r i at hr₀
  have hT : Presieve.IsSheafFor (yoneda.obj T) (Presieve.ofArrows U v) :=
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _).isSheafFor _ hcover
  have hsection : r₀ ≫ p = 𝟙 T := by
    apply hT.isSeparatedFor.ext
    rintro Z f ⟨i⟩
    change v i ≫ (r₀ ≫ p) = v i ≫ 𝟙 T
    rw [← Category.assoc, hr₀ i, hr, Category.comp_id]
  have heq : yoneda.map p ≫ a = yoneda.map p ≫ b := by
    have h₁ := hp.w =≫ Limits.prod.fst
    have h₂ := hp.w =≫ Limits.prod.snd
    simp only [Category.assoc, Limits.prod.lift_fst, Limits.prod.lift_snd,
      Category.comp_id] at h₁ h₂
    exact h₁.symm.trans h₂
  calc
    a = yoneda.map r₀ ≫ (yoneda.map p ≫ a) := by
      rw [← Category.assoc, ← Functor.map_comp, hsection, yoneda.map_id, Category.id_comp]
    _ = yoneda.map r₀ ≫ (yoneda.map p ≫ b) := by rw [heq]
    _ = b := by
      rw [← Category.assoc, ← Functor.map_comp, hsection, yoneda.map_id, Category.id_comp]

private theorem section_eq_of_fpqc_restrictions
    {S : Scheme.{u}} (E : AlgebraicSpace S) (T : Over S) {I : Type w}
    (U : I → Over S) (v : ∀ i, U i ⟶ T)
    (hv : Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (v i).left) ∈
      Scheme.fpqcPrecoverage T.left)
    (a b : E.obj.obj.obj (op T))
    (hab : ∀ i, E.obj.obj.map (v i).op a = E.obj.obj.map (v i).op b) : a = b := by
  apply yonedaEquiv.symm.injective
  apply hom_eq_of_fpqc_restrictions E T U v hv
  intro i
  rw [yonedaEquiv_symm_naturality_left, yonedaEquiv_symm_naturality_left, hab i]

private theorem section_eq_of_fpqc_singleton
    {S : Scheme.{u}} (E : AlgebraicSpace S) {T T' : Over S} (f : T' ⟶ T)
    (hf : Presieve.singleton f.left ∈ Scheme.fpqcPrecoverage T.left)
    (a b : E.obj.obj.obj (op T)) (hab : E.obj.obj.map f.op a = E.obj.obj.map f.op b) :
    a = b := by
  apply section_eq_of_fpqc_restrictions E T (fun _ : PUnit.{1} ↦ T') (fun _ ↦ f)
  · simpa only [Presieve.ofArrows_pUnit] using hf
  · intro i
    exact hab

private theorem isSheafFor_etale_singleton
    {S : Scheme.{u}} (E : AlgebraicSpace S) {T W : Over S} (p : W ⟶ T)
    [Etale p.left] [Surjective p.left] :
    Presieve.IsSheafFor E.obj.obj (Presieve.singleton p) := by
  exact ((isSheaf_iff_isSheaf_of_type _ _).mp E.obj.property).isSheafFor _
    (Scheme.singleton_mem_over_fppfTopology p)

private theorem affine_singleton_isSheafFor
    {S : Scheme.{u}} (E : AlgebraicSpace S) {T T' : Over S}
    [IsAffine T.left] [IsAffine T'.left] (f : T' ⟶ T)
    [Flat f.left] [Surjective f.left] :
    Presieve.IsSheafFor E.obj.obj (Presieve.singleton f) := by
  classical
  rw [Presieve.isSheafFor_singleton]
  intro x hx
  obtain ⟨W, p, hp, hps, y, hy⟩ :=
    exists_etale_local_extension_of_affine_fpqc E f x hx
  let := hp
  let := hps
  have hlocal {Z : Over S} (a : Z ⟶ W) (b : Z ⟶ T') (h : a ≫ p = b ≫ f) :
      E.obj.obj.map a.op y = E.obj.obj.map b.op x := by
    have h' := congrArg (fun z ↦ E.obj.obj.map (Limits.pullback.lift a b h).op z) hy
    simpa only [← Functor.map_comp_apply, ← op_comp, Limits.pullback.lift_fst,
      Limits.pullback.lift_snd] using h'
  have hcompat {Z : Over S} (a b : Z ⟶ W) (h : a ≫ p = b ≫ p) :
      E.obj.obj.map a.op y = E.obj.obj.map b.op y := by
    let Q := Limits.pullback (a ≫ p) f
    let q : Q ⟶ Z := Limits.pullback.fst (a ≫ p) f
    let r : Q ⟶ T' := Limits.pullback.snd (a ≫ p) f
    have hq : Presieve.singleton q.left ∈ Scheme.fpqcPrecoverage Z.left := by
      have hf := f.left.singleton_mem_fpqcPrecoverage
      rw [← Presieve.ofArrows_pUnit.{0}] at hf ⊢
      exact Precoverage.mem_coverings_of_isPullback _ hf (a ≫ p).left
        (fun _ ↦ q.left) (fun _ ↦ r.left)
        (fun _ ↦ (IsPullback.of_hasPullback (a ≫ p) f).map (Over.forget S))
    apply section_eq_of_fpqc_singleton E q hq
    simp only [← Functor.map_comp_apply, ← op_comp]
    have h₁ : (q ≫ a) ≫ p = r ≫ f := by
      simpa only [Category.assoc] using Limits.pullback.condition (f := a ≫ p) (g := f)
    have h₂ : (q ≫ b) ≫ p = r ≫ f := by
      rw [Category.assoc, ← h]
      exact h₁
    exact (hlocal (q ≫ a) r h₁).trans (hlocal (q ≫ b) r h₂).symm
  obtain ⟨z, hz, hzu⟩ := Presieve.isSheafFor_singleton.mp
    (isSheafFor_etale_singleton E p) y (fun a b h ↦ hcompat a b h)
  have hz' : E.obj.obj.map f.op z = x := by
    let q := Limits.pullback.snd p f
    have : Etale q.left := MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback p f).map (Over.forget S)) hp
    have : Surjective q.left := MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback p f).map (Over.forget S)) hps
    apply (isSheafFor_etale_singleton E q).isSeparatedFor.ext
    rintro Z a ⟨⟩
    rw [← Functor.map_comp_apply, ← op_comp, ← Limits.pullback.condition,
      op_comp, Functor.map_comp_apply, hz]
    exact hy
  refine ⟨z, hz', ?_⟩
  intro z' hz''
  apply section_eq_of_fpqc_singleton E f f.left.singleton_mem_fpqcPrecoverage
  rw [hz'', hz']

/-- Compatible maps from an fpqc covering of schemes to an algebraic space descend
uniquely, and equality of two maps is detected on the covering. The index type may be
empty. No separatedness or finiteness hypothesis is imposed on the algebraic space.
Source: Stacks Project, Tags 04P2 and 0APL
(blueprint: lem-a1-algebraic-space-fpqc-sheaf).

Proof (the seven steps of the node):
1. For two locally equal maps `a,b : T → E`, the representable diagonal gives their
   equalizer scheme `P → T`, a monomorphism. The local equalities give maps to `P`;
   monicity makes them compatible. Scheme fpqc descent
   (`lem-weil-pbc-fpqc-representable-descent`) glues `r : T → P`. Its composite to `T`
   is the identity by scheme descent uniqueness with target `T`. Pulling the equality
   on `P` back by this section proves `a=b`.
2. On all schemes consider the presheaf `H(A)` of pairs `(s : A → S, x ∈ E(A,s))`.
   Scheme morphisms glue Zariski locally, and the fppf sheaf condition glues `x` after
   fixing `s`, including the empty cover. Thus `H` is a Zariski sheaf.
   `lem-a1-fpqc-sheaf-affine-criterion` reduces existence to singleton affine fpqc covers
   `f : T' → T`. Scheme descent first descends the structure map to `S`.
3. For compatible `c : T' → E`, `lem-a1-qc-map-affine-etale-neighbourhood` supplies
   affine `U → E` with `V = T' ×_E U → T'` surjective, étale, separated and locally
   quasi-finite. The two pullbacks of `V` to `T' ×_T T'` identify by keeping the
   `U` coordinate. The triple-product cocycle follows by the fibre-product universal
   property (`def-pd-descent-datum`, `def-pc-fibre-product`).
4. `lem-a1-separated-lqf-fpqc-effective-descent` gives `W → T` and an isomorphism
   `W ×_T T' ≅ V` inducing this datum. `lem-galois-fpqc-descend-etale` makes `W → T`
   étale; surjectivity follows by lifting a point first to `T'` and then to `V`.
5. The map `W ×_T T' → V → U` is invariant under the datum since its `U` coordinate
   is fixed. The fpqc cover `W ×_T T' → W`
   (`lem-galois-fpqc-covering-base-change`) and scheme descent give `b : W → U`.
   Scheme descent uniqueness with target `S` shows `b` is an `S`-map. Its composite
   with `U → E` pulls back to `c` on `W ×_T T'`.
6. On `W ×_T W` the two resulting maps to `E` agree after the fpqc base change by
   `T'`, hence agree by step 1. The étale surjection `W → T` is an fppf covering
   (`def-weil-etale-morphism`, `def-pc-fppf-site`), so the defining fppf sheaf of `E`
   glues them to `a : T → E`. Check `af=c` on the fppf cover `V → T'` and use its
   sheaf uniqueness. Step 1 gives uniqueness of `a`.
7. The affine criterion now gives descent for every fpqc family. Apply it to
   `(T.hom ∘ v_i,e_i)`. Scheme descent uniqueness shows the glued structure map is
   `T.hom`, so the glued section is over the prescribed `S`-scheme `T`. Step 1 also
   gives the equality clause. Only the auxiliary chart was separated; no condition
   on separatedness or finiteness of `E` entered the argument. -/
theorem existsUnique_section_and_eq_of_fpqc_cover
    {S : Scheme.{u}} (E : AlgebraicSpace S) (T : Over S) {I : Type w}
    (T' : I → Scheme.{u}) (v : ∀ i : I, T' i ⟶ T.left)
    (hcover : Presieve.ofArrows T' v ∈ Scheme.fpqcPrecoverage T.left) :
    (∀ e : ∀ i : I, E.obj.obj.obj (op (Over.mk (v i ≫ T.hom))),
      (∀ i j : I,
        E.obj.obj.map
            (Over.homMk
              (U := Over.mk (Limits.pullback.fst (v i) (v j) ≫ v i ≫ T.hom))
              (V := Over.mk (v i ≫ T.hom))
              (Limits.pullback.fst (v i) (v j)) rfl).op (e i) =
          E.obj.obj.map
            (Over.homMk
              (U := Over.mk (Limits.pullback.fst (v i) (v j) ≫ v i ≫ T.hom))
              (V := Over.mk (v j ≫ T.hom))
              (Limits.pullback.snd (v i) (v j))
              (Limits.pullback.condition_assoc (f := v i) (g := v j) T.hom).symm).op (e j)) →
      ∃! a : E.obj.obj.obj (op T),
        ∀ i : I, E.obj.obj.map
          (Over.homMk (U := Over.mk (v i ≫ T.hom)) (V := T) (v i) rfl).op a = e i) ∧
    (∀ a b : E.obj.obj.obj (op T),
      (∀ i : I, E.obj.obj.map
          (Over.homMk (U := Over.mk (v i ≫ T.hom)) (V := T) (v i) rfl).op a =
        E.obj.obj.map
          (Over.homMk (U := Over.mk (v i ≫ T.hom)) (V := T) (v i) rfl).op b) → a = b)  := by
  let U (i : I) : Over S := Over.mk (v i ≫ T.hom)
  let v' (i : I) : U i ⟶ T := Over.homMk (v i) rfl
  have hF : Presieve.IsSheaf (Scheme.fpqcTopology.over S) E.obj.obj :=
    isSheaf_fpqc_over_of_affine E.obj.obj
      ((isSheaf_iff_isSheaf_of_type _ _).mp E.obj.property) (by
        intro R A f hf hs t
        have : IsAffine (Over.mk t).left := by
          change IsAffine (Spec R)
          infer_instance
        have : IsAffine (Over.mk (Spec.map f ≫ t)).left := by
          change IsAffine (Spec A)
          infer_instance
        let k : Over.mk (Spec.map f ≫ t) ⟶ Over.mk t := Over.homMk (Spec.map f) rfl
        have : Flat k.left := hf
        have : Surjective k.left := hs
        exact affine_singleton_isSheafFor E k)
  have hcov : Sieve.ofArrows U v' ∈ Scheme.fpqcTopology.over S T := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact Precoverage.generate_mem_toGrothendieck hcover
  have hsheaf := hF.isSheafFor (Presieve.ofArrows U v') hcov
  constructor
  · intro e he
    apply ((Presieve.isSheafFor_arrows_iff _ _).mp hsheaf) e
    intro i j Z a b hab
    let P : Over S :=
      Over.mk (Limits.pullback.fst (v i) (v j) ≫ v i ≫ T.hom)
    let pi : P ⟶ U i := Over.homMk (Limits.pullback.fst (v i) (v j)) rfl
    let pj : P ⟶ U j := Over.homMk (Limits.pullback.snd (v i) (v j))
      (Limits.pullback.condition_assoc (f := v i) (g := v j) T.hom).symm
    let l : Z ⟶ P := Over.homMk
      (Limits.pullback.lift a.left b.left (congrArg (fun k ↦ k.left) hab)) (by
        dsimp [P]
        rw [← Category.assoc, ← Category.assoc, Limits.pullback.lift_fst]
        exact Over.w a)
    have hl₁ : l ≫ pi = a := by ext; exact Limits.pullback.lift_fst _ _ _
    have hl₂ : l ≫ pj = b := by ext; exact Limits.pullback.lift_snd _ _ _
    have h := congrArg (fun z ↦ E.obj.obj.map l.op z) (he i j)
    change E.obj.obj.map l.op (E.obj.obj.map pi.op (e i)) =
      E.obj.obj.map l.op (E.obj.obj.map pj.op (e j)) at h
    simpa only [← Functor.map_comp_apply, ← op_comp, hl₁, hl₂] using h
  · intro a b hab
    exact section_eq_of_fpqc_restrictions E T U v' hcover a b hab

end AlgebraicGeometry.AlgebraicSpace
