/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.ConstantGroupScheme
public import Sheaf.AlgebraicGeometry.CoproductCopiesMorphismsClopen
public import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Algebra.Group.TransferInstance
import Sheaf.AlgebraicGeometry.ConstantGroupSchemeMorphismsClopenAdditive

/-!
# Constant group scheme morphisms and clopen decompositions

Source: Stacks Project, Etale Cohomology, Remark 59.23.2 (Tag 03P5), and Groupoids,
Example 39.5.6 (Tag 03YW)
(blueprint: lem-weil-pbc-constant-group-scheme-morphism-clopen).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry

open Classical in
/-- Core decomposition correspondence for maps to the constant coproduct.
Source: Stacks Project, Tags 03P5 and 03YW.
(blueprint: lem-weil-pbc-constant-group-scheme-morphism-clopen) -/
private theorem constantGroupSchemeMorphismsClopen_core (T U : Scheme.{u}) (E : Type v)
    [Small.{u} E] [AddCommGroup E] (s : U ⟶ T) :
    ∃ b : ConstantGroupSchemePoint T E s ≃
        {P : E → U.Opens // IsClopenDecomposition U E P},
      (∀ f e, ((b f).1 e : Set U) =
        f.1 ⁻¹' constantGroupSchemeComponent T E e) ∧
      (∀ (P : {P : E → U.Opens // IsClopenDecomposition U E P}) (e : E),
        (P.1 e).ι ≫ (b.symm P).1 =
          ((P.1 e).ι ≫ s) ≫ constantGroupSchemeIncl T E e) ∧
      (∀ (P : {P : E → U.Opens // IsClopenDecomposition U E P}) (e : E),
        IsClopen (P.1 e : Set U)) ∧
      (∀ P : {P : E → U.Opens // IsClopenDecomposition U E P},
        IsCompact (Set.univ : Set U) → Set.Finite {e : E | (P.1 e : Set U).Nonempty}) ∧
      (∀ e₀ e, (b (constantGroupSchemeCanonicalMap T E s e₀)).1 e =
        if e = e₀ then ⊤ else ⊥) ∧
      (∀ P : {P : E → U.Opens // IsClopenDecomposition U E P},
        ∃! f : ConstantGroupSchemePoint T E s,
        ∀ e, (P.1 e).ι ≫ f.1 =
          ((P.1 e).ι ≫ s) ≫ constantGroupSchemeIncl T E e) := by
  classical
  obtain ⟨hrestrict, _, ⟨b, hb⟩, ⟨d, hd⟩, hc, _⟩ :=
    coproductCopiesMorphismsClopen T U E s
  refine ⟨b, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f e
    exact congrArg (fun V : U.Opens ↦ (V : Set U)) (hb f e)
  · intro P e
    have h := (hrestrict (b.symm P).1 (b.symm P).2).2 e
    have he := hb (b.symm P) e
    rw [b.apply_symm_apply] at he
    rw [← he] at h
    exact h
  · intro P e
    have he := congrArg (fun V : U.Opens ↦ (V : Set U)) (hb (b.symm P) e)
    rw [b.apply_symm_apply] at he
    rw [he, hd]
    exact (d (b.symm P)).isLocallyConstant.isClopen_fiber e
  · intro P hcompact
    let : CompactSpace U := ⟨hcompact⟩
    apply (d (b.symm P)).range_finite.subset
    intro e he
    obtain ⟨x, hx⟩ := he
    have hp := congrArg (fun V : U.Opens ↦ (V : Set U)) (hb (b.symm P) e)
    rw [b.apply_symm_apply, hd] at hp
    rw [hp] at hx
    exact ⟨x, hx⟩
  · intro e₀ e
    exact (hb (constantGroupSchemeCanonicalMap T E s e₀) e).trans (hc e₀ e)
  · intro P
    let f := b.symm P
    have hf (e : E) : (P.1 e).ι ≫ f.1 =
        ((P.1 e).ι ≫ s) ≫ constantGroupSchemeIncl T E e := by
      have h := (hrestrict f.1 f.2).2 e
      have he := hb f e
      change (b (b.symm P)).1 e = _ at he
      rw [b.apply_symm_apply] at he
      rw [← he] at h
      exact h
    refine ⟨f, hf, ?_⟩
    intro g hg
    apply Subtype.ext
    have c : CategoryTheory.Limits.IsColimit
        (CategoryTheory.Limits.Cofan.mk U (fun e ↦ (P.1 e).ι)) := by
      apply Nonempty.some
      apply nonempty_isColimit_cofanMk_of
      · simpa using P.2.2
      · intro e e' h
        simpa using P.2.1 e e' h
    apply c.hom_ext
    intro j
    obtain ⟨e⟩ := j
    exact (hg e).trans (hf e).symm

open Classical in
/-- Source: Stacks Project, Remark 59.23.2 (Tag 03P5), Example 39.5.6 (Tag 03YW)
(blueprint: lem-weil-pbc-constant-group-scheme-morphism-clopen).

Step 1: the coproduct components are disjoint open sets covering the constant scheme,
hence closed (lem-weil-pbc-scheme-coproduct-family). The projection on each is the identity.
Step 2: inverse images of these components give a clopen decomposition of the domain.
Step 3: factor the restriction through its component
(lem-weil-pbc-morphism-factors-through-open-subscheme); the equation over the base forces
this factor to be the restricted structure morphism.
Step 4: conversely glue these component maps over any clopen decomposition
(lem-weil-pbc-scheme-morphism-gluing). Empty overlaps give agreement; uniqueness of gluing
forces the base equation and both inverse identities of the decomposition correspondence.
Step 5: assign to each point its unique component label. Open fibres are also closed because
their complements are unions of the other fibres. A quasi-compact domain has a finite
subcover of the fibres, so only finitely many fibres can be nonempty.
Step 6: the canonical point indexed by `e` lies entirely in the `e`-component, and therefore
corresponds to the constant function `e` and the decomposition with only that piece nonempty.
Step 7: on the pair component `(e,e')`, multiplication lands in component `e + e'`
(lem-weil-pbc-constant-group-scheme-multiplication). Thus the label of the sum is the sum
of the labels. Pointwise addition, zero and negation preserve locally constant functions;
transport their abelian group structure across the bijection. The canonical map is additive
because constant functions add pointwise. No step uses etaleness. -/
theorem constantGroupSchemeMorphismsClopen (T U : Scheme.{u}) (E : Type v)
    [Small.{u} E] [AddCommGroup E] (s : U ⟶ T) :
    (∃ b : ConstantGroupSchemePoint T E s ≃
        {P : E → U.Opens // IsClopenDecomposition U E P},
      (∀ f e, ((b f).1 e : Set U) =
        f.1 ⁻¹' constantGroupSchemeComponent T E e) ∧
      (∀ (P : {P : E → U.Opens // IsClopenDecomposition U E P}) (e : E), (P.1 e).ι ≫ (b.symm P).1 =
        ((P.1 e).ι ≫ s) ≫ constantGroupSchemeIncl T E e) ∧
      (∀ (P : {P : E → U.Opens // IsClopenDecomposition U E P}) (e : E), IsClopen (P.1 e : Set U)) ∧
      (∀ P : {P : E → U.Opens // IsClopenDecomposition U E P}, IsCompact (Set.univ : Set U) →
        Set.Finite {e : E | (P.1 e : Set U).Nonempty}) ∧
      (∀ e₀ e, (b (constantGroupSchemeCanonicalMap T E s e₀)).1 e =
        if e = e₀ then ⊤ else ⊥) ∧
      (∀ P : {P : E → U.Opens // IsClopenDecomposition U E P},
        ∃! f : ConstantGroupSchemePoint T E s,
        ∀ e, (P.1 e).ι ≫ f.1 = ((P.1 e).ι ≫ s) ≫ constantGroupSchemeIncl T E e)) ∧
    (∀ φ : U → E,
      (∀ e, IsOpen (φ ⁻¹' {e})) ↔ (∀ e, IsClopen (φ ⁻¹' {e}))) ∧
    (∃ a : AddCommGroup (ConstantGroupSchemePoint T E s),
      letI := a
      (∀ f g : ConstantGroupSchemePoint T E s,
        f + g = constantGroupSchemePointAdd T E s f g) ∧
      ∃ Φ : ConstantGroupSchemePoint T E s ≃+ LocallyConstant U E,
        (∀ f x e, Φ f x = e ↔ f.1 x ∈ constantGroupSchemeComponent T E e) ∧
        (∀ e, Φ (constantGroupSchemeCanonicalMap T E s e) = LocallyConstant.const U e) ∧
        (∀ f g x, Φ (constantGroupSchemePointAdd T E s f g) x = Φ f x + Φ g x) ∧
        ∃ c : E →+ ConstantGroupSchemePoint T E s,
          ∀ e, c e = constantGroupSchemeCanonicalMap T E s e) := by
  obtain ⟨b, hb1, hb2, hb3, hb4, hb5, hb6⟩ :=
    constantGroupSchemeMorphismsClopen_core T U E s
  refine ⟨⟨b, hb1, hb2, hb3, hb4, hb5, hb6⟩, ?_, ?_⟩
  · intro φ
    constructor
    · intro h e
      exact (IsLocallyConstant.iff_isOpen_fiber.mpr h).isClopen_fiber e
    · intro h e
      exact (h e).2
  · obtain ⟨_, _, _, ⟨d, hd⟩, hc, _⟩ := coproductCopiesMorphismsClopen T U E s
    change ConstantGroupSchemePoint T E s ≃ LocallyConstant U E at d
    have labels (f : ConstantGroupSchemePoint T E s) (x : U) (e : E) :
        d f x = e ↔ f.1 x ∈ constantGroupSchemeComponent T E e := by
      have h := hd f e
      exact (Set.ext_iff.mp h x).symm
    have hadd (f g : ConstantGroupSchemePoint T E s) :
        d (constantGroupSchemePointAdd T E s f g) = d f + d g := by
      apply LocallyConstant.ext
      intro x
      exact (labels _ x _).mpr
        (constantGroupSchemePointAdd_component T U E s f g x (d f x) (d g x)
          ((labels f x _).mp rfl) ((labels g x _).mp rfl))
    have hconst (e : E) : d (constantGroupSchemeCanonicalMap T E s e) =
        LocallyConstant.const U e := by
      apply LocallyConstant.ext
      intro x
      apply (labels _ x e).mpr
      exact ⟨s x, rfl⟩
    let a := d.addCommGroup
    let : AddCommGroup (ConstantGroupSchemePoint T E s) := a
    have sum_eq (f g : ConstantGroupSchemePoint T E s) :
        f + g = constantGroupSchemePointAdd T E s f g := by
      apply d.injective
      exact (d.apply_symm_apply (d f + d g)).trans (hadd f g).symm
    refine ⟨a, sum_eq, d.addEquiv, labels, hconst, ?_, ?_⟩
    · intro f g x
      exact congrArg (fun l : LocallyConstant U E ↦ l x) (hadd f g)
    · refine ⟨{ toFun := constantGroupSchemeCanonicalMap T E s
                map_zero' := ?_
                map_add' := ?_ }, fun _ ↦ rfl⟩
      · apply d.injective
        change d (constantGroupSchemeCanonicalMap T E s 0) = d (d.symm 0)
        rw [hconst, d.apply_symm_apply]
        rfl
      · intro e e'
        apply d.injective
        change d (constantGroupSchemeCanonicalMap T E s (e + e')) =
          d (d.symm (d (constantGroupSchemeCanonicalMap T E s e) +
            d (constantGroupSchemeCanonicalMap T E s e')))
        rw [d.apply_symm_apply, hconst, hconst, hconst]
        rfl

end AlgebraicGeometry
