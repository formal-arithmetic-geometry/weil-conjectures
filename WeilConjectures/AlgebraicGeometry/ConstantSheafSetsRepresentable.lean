/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.AlgebraicGeometry.CoproductCopiesMorphismsClopen
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf

/-!
# Constant sheaves of sets represented by disjoint unions

Source: Stacks Project, Etale Cohomology, Remark 59.23.2 (Tag 03P5), Groupoid Schemes,
Example 39.5.6 (Tag 03YW), and Lemma 59.15.8 (Tag 03O3)
(blueprint: lem-galois-constant-sheaf-sets-representable).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The presheaf represented by the disjoint union of `E` copies of `U`, restricted to
the small etale site and lifted to the universe of set-valued sheaves.
Source: Stacks Project, Tags 03YW and 03P5
(blueprint: lem-galois-constant-sheaf-sets-representable). -/
noncomputable abbrev constantSetCoproductPresheaf (U : Scheme.{u}) (E : Type u) :
    U.Etaleᵒᵖ ⥤ Type (max u (u + 1)) :=
  (Etale.forget U).op ⋙
    yoneda.obj (Over.mk (Sigma.desc (fun _ : E => 𝟙 U) : (∐ fun _ : E => U) ⟶ U)) ⋙
    uliftFunctor.{u + 1, u}

set_option backward.isDefEq.respectTransparency.types false in
/-- (blueprint: lem-galois-constant-sheaf-sets-representable) For any scheme `U` and set `E`,
the presheaf on the small etale site of `U` represented by the disjoint union of `E` copies of
`U` is a sheaf and is canonically isomorphic to the constant sheaf of value `E`.

The coproduct codiagonal makes `∐ (_ : E), U` a `U`-scheme. A section of its representable
presheaf is a morphism over `U`; the canonical map from the constant presheaf sends `e` to
the composite of the structure map with the `e`-th coprojection.

Proof: Representable presheaves are etale sheaves by Stacks Tag 03O3; universe lifting
preserves the sheaf condition. The displayed constant-section map is natural because
morphisms in the site commute with the structure maps. It is locally surjective: the
clopen pieces given by Tag 03YW cover the domain, are etale over the base, and on the
piece indexed by `e` a represented section is the image of `e`. It is locally injective:
if two distinct constants have the same image, their component preimages are both the
whole domain and empty, so the domain is empty and the empty family covers it.

Lift the constant-section map using `sheafifyLift`. The unit of sheafification is locally
bijective, so the factorization and Mathlib's composition criteria show that the lift
is locally bijective. Mathlib's `Sheaf.isLocallyBijective_iff_isIso` makes it an
isomorphism; `sheafifyLift_unique` gives the asserted uniqueness. This implements the
sheafification comparison of Tag 03P5 without constructing a second universal property
by hand. The covering argument includes `E` empty. -/
theorem constantSheaf_sets_representable (U : Scheme.{u}) (E : Type u) :
    ∃ (hH : Presheaf.IsSheaf (smallEtaleTopology U)
        (constantSetCoproductPresheaf U E))
      (c : (Functor.const U.Etaleᵒᵖ).obj (ULift.{u + 1, u} E) ⟶
        constantSetCoproductPresheaf U E),
      (∀ (W : U.Etale) (e : E), ((c.app (Opposite.op W)) ⟨e⟩).down.left =
        W.hom ≫ Sigma.ι (fun _ : E => U) e) ∧
      ∃ φ : (constantSheaf (smallEtaleTopology U) (Type (max u (u + 1)))).obj
          (ULift.{u + 1, u} E) ⟶ ⟨constantSetCoproductPresheaf U E, hH⟩,
        (toSheafify (smallEtaleTopology U)
          ((Functor.const U.Etaleᵒᵖ).obj (ULift.{u + 1, u} E))) ≫ φ.hom = c ∧
        IsIso φ ∧
        ∀ ψ : (constantSheaf (smallEtaleTopology U) (Type (max u (u + 1)))).obj
            (ULift.{u + 1, u} E) ⟶ ⟨constantSetCoproductPresheaf U E, hH⟩,
          (toSheafify (smallEtaleTopology U)
            ((Functor.const U.Etaleᵒᵖ).obj (ULift.{u + 1, u} E))) ≫ ψ.hom = c →
            ψ = φ := by
  let H := constantSetCoproductPresheaf U E
  let P := (Functor.const U.Etaleᵒᵖ).obj (ULift.{u + 1, u} E)
  let c : P ⟶ H :=
    { app := fun W => ↾fun e => ⟨Over.homMk
        (W.unop.hom ≫ Sigma.ι (fun _ : E => U) e.down) (by simp)⟩
      naturality := by
        intro W V g
        ext e
        apply ULift.ext
        apply Over.OverMorphism.ext
        change V.unop.hom ≫ Sigma.ι (fun _ : E => U) e.down =
          g.unop.left ≫ (W.unop.hom ≫ Sigma.ι (fun _ : E => U) e.down)
        simp [← Category.assoc] }
  have hc : ∀ (W : U.Etale) (e : E), ((c.app (Opposite.op W)) ⟨e⟩).down.left =
      W.hom ≫ Sigma.ι (fun _ : E => U) e := fun _ _ => rfl
  have hH : Presheaf.IsSheaf (smallEtaleTopology U) H := by
    rw [isSheaf_iff_isSheaf_of_type]
    change Presieve.IsSheaf (smallEtaleTopology U)
      (((Etale.forget U).op ⋙ yoneda.obj
        (Over.mk (Sigma.desc (fun _ : E => 𝟙 U)))) ⋙ uliftFunctor.{u + 1, u})
    apply Presieve.isSheaf_comp_uliftFunctor
    intro W S hS
    let X : Scheme.{u} := ∐ fun _ : E => U
    let p : X ⟶ U := Sigma.desc (fun _ : E => 𝟙 U)
    let : X.Over U := ⟨p⟩
    exact smallEtaleRepresentablePresheaf_isSheaf U X W S.arrows (by simpa using hS)
  have hinj : Presheaf.IsLocallyInjective (smallEtaleTopology U) c := by
    constructor
    intro W a b hab
    by_cases h : a = b
    · subst b
      exact (smallEtaleTopology U).superset_covering (fun _ _ _ => rfl)
        ((smallEtaleTopology U).top_mem _)
    · have hne : a.down ≠ b.down := fun h' => h (ULift.ext a b h')
      have heq : W.unop.hom ≫ Sigma.ι (fun _ : E => U) a.down =
          W.unop.hom ≫ Sigma.ι (fun _ : E => U) b.down :=
        congrArg (fun t => t.down.left) hab
      have ha := (coproductCopiesMorphismsClopen U W.unop.left E W.unop.hom).2.2.2.2.1
      have htop : (⊤ : W.unop.left.Opens) = ⊥ := by
        have h₁ := ha a.down a.down
        have h₂ := ha b.down a.down
        rw [heq] at h₁
        simpa [hne] using h₁.symm.trans h₂
      have : IsEmpty W.unop.left := ⟨fun x => by
        have hx : x ∈ (⊤ : W.unop.left.Opens) := trivial
        rw [htop] at hx
        exact hx⟩
      refine (smallEtaleTopology U).superset_covering ?_
        ((ofArrows_mem_smallEtaleTopology_iff (Z := PEmpty.elim) (W := W.unop)
          (fun i : PEmpty.{1} => i.elim)).2
            (Set.eq_univ_of_forall fun x => isEmptyElim x))
      rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro _ _ ⟨i⟩
      exact i.elim
  have hsurj : Presheaf.IsLocallySurjective (smallEtaleTopology U) c := by
    constructor
    intro W s
    let f : W.left ⟶ ∐ fun _ : E => U := s.down.left
    have hf : f ≫ Sigma.desc (fun _ : E => 𝟙 U) = W.hom := s.down.w
    let V (e : E) := f ⁻¹ᵁ (Sigma.ι (fun _ : E => U) e).opensRange
    have hdecomp := (coproductCopiesMorphismsClopen U W.left E W.hom).1 f hf
    let Z (e : E) : U.Etale := Etale.mk ((V e).ι ≫ W.hom)
    let j (e : E) : Z e ⟶ W := MorphismProperty.Over.homMk (V e).ι rfl
    refine (smallEtaleTopology U).superset_covering ?_
      ((ofArrows_mem_smallEtaleTopology_iff j).2 ?_)
    · rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro _ _ ⟨e⟩
      refine ⟨⟨e⟩, ?_⟩
      apply ULift.ext
      apply Over.OverMorphism.ext
      exact (hdecomp.2 e).symm
    · apply Set.eq_univ_of_forall
      intro x
      have hx : x ∈ (⨆ e, V e) := by rw [hdecomp.1.2]; trivial
      obtain ⟨e, he⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact Set.mem_iUnion.mpr ⟨e, ⟨⟨x, he⟩, rfl⟩⟩
  let φ : (constantSheaf (smallEtaleTopology U) (Type (u + 1))).obj
      (ULift.{u + 1, u} E) ⟶ ⟨H, hH⟩ :=
    ⟨sheafifyLift (smallEtaleTopology U) c hH⟩
  have hφ : toSheafify (smallEtaleTopology U) P ≫ φ.hom = c :=
    toSheafify_sheafifyLift (smallEtaleTopology U) c hH
  refine ⟨hH, c, hc, φ, hφ, ?_, ?_⟩
  · apply (Sheaf.isLocallyBijective_iff_isIso φ).mp
    constructor
    · change Presheaf.IsLocallyInjective _ _
      rw [← Presheaf.comp_isLocallyInjective_iff _
        (toSheafify (smallEtaleTopology U) P), hφ]
      exact hinj
    · change Presheaf.IsLocallySurjective _ _
      rw [← Presheaf.comp_isLocallySurjective_iff _
        (toSheafify (smallEtaleTopology U) P), hφ]
      exact hsurj
  · intro ψ hψ
    apply Sheaf.hom_ext
    exact sheafifyLift_unique (smallEtaleTopology U) c hH ψ.hom hψ

end AlgebraicGeometry.Scheme
