/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.TraceFormula.TotalSiteComponentRestriction
public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Homology.ExactSequence
import Sheaf.TraceFormula.TotalSiteSimplexFreeResolution

/-!
# The free module resolution on a coherent total simplicial site

Source: Stacks Project, `spaces-simplicial.tex`, Tags 0D72 and 0D7C, and the faces
of `lemma-simplicial-resolution-augmentation`
(blueprint: lem-trf-total-site-free-module-resolution).

The diagram below uses actual constant-ring module sheaves and the normalized lifts
of geometric inverse images. Its total category is a fully faithful, essentially
surjective presentation of ALL compatible systems, using `TotalSiteSystemData`.
The equations on underlying sets ensure that no arbitrary module comparison replaces
the given geometric comparison. The resolution is functorial in the base module.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option warn.sorry false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

open ConstantLeftModuleInverseImage

/-- The coherent geometric and canonical constant-module inverse images in the hypothesis.
The site and coefficient objects lie in the chosen common small universe; the total
category may have its own object universe. `id_normalized`, `comp_normalized`, and
`augmentation_normalized` identify the module comparisons on underlying sets with the
specified geometric comparisons. `system` imposes both unit laws and the cocycle law
and presents exactly the category of compatible module families. The final two equations
are the identity and composition coherence of the augmentation.
Source: Stacks, Tags 0D72 and 0D7C; Sites, 00YV (6)
(blueprint: lem-trf-total-site-free-module-resolution). -/
structure TotalSiteConstantModuleDiagram
    (C : SimplexCategoryᵒᵖ → Type u) [∀ i, SmallCategory (C i)]
    (J : ∀ i, GrothendieckTopology (C i))
    (D : Type u) [SmallCategory D] (K : GrothendieckTopology D)
    (Λ : Type u) [CommRing Λ]
    [∀ i, HasWeakSheafify (J i) RingCat.{u}] [HasWeakSheafify K RingCat.{u}]
    (T : Type v) [Category.{u} T] [Preadditive T] where
  geometric : ∀ {i j : SimplexCategoryᵒᵖ}, (j ⟶ i) →
    GeometricMorphism (Sheaf (J j) (Type u)) (Sheaf (J i) (Type u))
  lift : ∀ {i j : SimplexCategoryᵒᵖ} (f : j ⟶ i),
    ConstantLeftModuleInverseImageLift (J i) (J j) Λ
      (geometric f).inverse (geometric f).direct (geometric f).adj (geometric f).leftExact
  geometricId : ∀ i, (geometric (𝟙 i)).inverse ≅ 𝟭 (Sheaf (J i) (Type u))
  geometricComp : ∀ {i j k : SimplexCategoryᵒᵖ} (f : j ⟶ i) (g : k ⟶ j),
    (geometric (g ≫ f)).inverse ≅ (geometric f).inverse ⋙ (geometric g).inverse
  pullId : ∀ i, (lift (𝟙 i)).moduleFunctor ≅ 𝟭 (Modules (J i) Λ)
  pullComp : ∀ {i j k : SimplexCategoryᵒᵖ} (f : j ⟶ i) (g : k ⟶ j),
    (lift (g ≫ f)).moduleFunctor ≅ (lift f).moduleFunctor ⋙ (lift g).moduleFunctor
  id_normalized : ∀ i (M : Modules (J i) Λ),
    (W (J i) Λ).map ((pullId i).hom.app M) =
      (lift (𝟙 i)).moduleSetIso.hom.app M ≫ (geometricId i).hom.app ((W (J i) Λ).obj M)
  comp_normalized : ∀ {i j k : SimplexCategoryᵒᵖ} (f : j ⟶ i) (g : k ⟶ j)
    (M : Modules (J i) Λ),
    (W (J k) Λ).map ((pullComp f g).hom.app M) ≫
        (lift g).moduleSetIso.hom.app ((lift f).moduleFunctor.obj M) ≫
        (geometric g).inverse.map ((lift f).moduleSetIso.hom.app M) =
      (lift (g ≫ f)).moduleSetIso.hom.app M ≫
        (geometricComp f g).hom.app ((W (J i) Λ).obj M)
  system : TotalSiteSystemData (fun i ↦ Modules (J i) Λ)
    (fun f ↦ (lift f).moduleFunctor) pullId pullComp T
  augmentation : ∀ i, GeometricMorphism (Sheaf (J i) (Type u)) (Sheaf K (Type u))
  augmentationLift : ∀ i, ConstantLeftModuleInverseImageLift K (J i) Λ
    (augmentation i).inverse (augmentation i).direct
    (augmentation i).adj (augmentation i).leftExact
  geometricAugment : ∀ {i j : SimplexCategoryᵒᵖ} (f : j ⟶ i),
    (augmentation i).inverse ⋙ (geometric f).inverse ≅ (augmentation j).inverse
  augment : ∀ {i j : SimplexCategoryᵒᵖ} (f : j ⟶ i),
    (augmentationLift i).moduleFunctor ⋙ (lift f).moduleFunctor ≅
      (augmentationLift j).moduleFunctor
  augmentation_normalized : ∀ {i j : SimplexCategoryᵒᵖ} (f : j ⟶ i) (G : Modules K Λ),
    (W (J j) Λ).map ((augment f).hom.app G) ≫ (augmentationLift j).moduleSetIso.hom.app G =
      (lift f).moduleSetIso.hom.app ((augmentationLift i).moduleFunctor.obj G) ≫
        (geometric f).inverse.map ((augmentationLift i).moduleSetIso.hom.app G) ≫
        (geometricAugment f).hom.app ((W K Λ).obj G)
  augment_id : ∀ i (G : Modules K Λ),
    (augment (𝟙 i)).hom.app G =
      (pullId i).hom.app ((augmentationLift i).moduleFunctor.obj G)
  augment_comp : ∀ {i j k : SimplexCategoryᵒᵖ} (f : j ⟶ i) (g : k ⟶ j)
    (G : Modules K Λ),
    (pullComp f g).hom.app ((augmentationLift i).moduleFunctor.obj G) ≫
        (lift g).moduleFunctor.map ((augment f).hom.app G) ≫ (augment g).hom.app G =
      (augment (g ≫ f)).hom.app G

namespace TotalSiteConstantModuleDiagram

variable {C : SimplexCategoryᵒᵖ → Type u} [∀ i, SmallCategory (C i)]
  {J : ∀ i, GrothendieckTopology (C i)}
  {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
  {Λ : Type u} [CommRing Λ]
  [∀ i, HasWeakSheafify (J i) RingCat.{u}] [HasWeakSheafify K RingCat.{u}]
  {T : Type v} [Category.{u} T] [Preadditive T]

/-- A summand in the explicit free resolution, before including it in the coproduct.
Source: Stacks, Tag 0D7C (blueprint: lem-trf-total-site-free-module-resolution). -/
abbrev base (S : TotalSiteConstantModuleDiagram C J D K Λ T)
    (G : Modules K Λ) (m : SimplexCategoryᵒᵖ) :=
  (S.augmentationLift m).moduleFunctor.obj G

/-- The degree-`p`, component-`m` direct sum indexed by ALL simplex maps `[p] → [m]`.
Source: Stacks, Tags 0D72 and 0D7C
(blueprint: lem-trf-total-site-free-module-resolution). -/
abbrev summands (S : TotalSiteConstantModuleDiagram C J D K Λ T)
    (G : Modules K Λ) (p : ℕ) (m : SimplexCategoryᵒᵖ)
    (_ : SimplexCategory.mk p ⟶ m.unop) := S.base G m

end TotalSiteConstantModuleDiagram

/-- The explicit free total-module resolution, including its transitions, faces, fold
augmentation and the natural identity-summand Hom equivalence.
Source: Stacks, Tags 0D72 and 0D7C, with the faces in
`lemma-simplicial-resolution-augmentation`
(blueprint: lem-trf-total-site-free-module-resolution).

Proof (postponed):
1. Canonical constant-coefficient inverse images preserve the coherent comparisons
   (lem-pe-constant-left-module-inverse-image). Form the augmentation system with objects
   `a_m⁻¹G` and transitions `S.augment.hom`. For `P_p`, take the displayed direct sum;
   along `β` use this comparison and relabel `α` by `α ≫ β`. The two unit laws and cocycle
   identity give compatible systems. Full faithfulness and essential surjectivity of
   `S.system` realize them and their maps in `T`, functorially in `G`.
2. Define the faces by sending `α` to `δ_i ≫ α`. The fold is compatible with all
   transitions and faces. The simplicial identities cancel pairs in the alternating
   double sum, giving the chain complex with the specified alternating differential.
3. At component `m`, this is the augmented simplex complex tensored with `a_m⁻¹G`.
   The vertex-zero contraction of lem-trf-total-site-simplex-free-resolution proves
   exactness. Kernels and images of compatible systems are componentwise, since the
   canonical inverse images are exact (lem-pe-constant-left-module-inverse-image).
   The exact conservative component restrictions of lem-trf-total-site-component-restriction
   therefore detect exactness of the entire augmented complex.
4. Restrict a total morphism to the identity summand. Compatibility forces its `α`
   summand to be the pullback of this map followed by the transition of `I`. Conversely
   those formulas commute with transitions by the cocycle law. The two operations are
   inverse, by the coproduct universal property, proving the displayed Hom equivalence.
5. All formulas commute with maps in `G` and `I`. The fold restricts to the identity
   at degree zero, giving the final normalization equation. -/
theorem totalSiteFreeModuleResolution
    {C : SimplexCategoryᵒᵖ → Type u} [∀ i, SmallCategory (C i)]
    {J : ∀ i, GrothendieckTopology (C i)}
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    {Λ : Type u} [CommRing Λ]
    [∀ i, HasWeakSheafify (J i) RingCat.{u}] [HasWeakSheafify K RingCat.{u}]
    {T : Type v} [Category.{u} T] [Abelian T]
    (S : TotalSiteConstantModuleDiagram C J D K Λ T) :
    ∃ (a : Modules K Λ ⥤ T)
      (ea : ∀ (G : Modules K Λ) (m : SimplexCategoryᵒᵖ),
        (S.system.component m).obj (a.obj G) ≅ S.base G m)
      (P : Modules K Λ ⥤ ChainComplex T ℕ)
      (e : ∀ (G : Modules K Λ) (p : ℕ) (m : SimplexCategoryᵒᵖ),
        (S.system.component m).obj ((P.obj G).X p) ≅
          ∐ S.summands G p m)
      (d : ∀ (G : Modules K Λ) (p : ℕ) (i : Fin (p + 2)),
        (P.obj G).X (p + 1) ⟶ (P.obj G).X p)
      (ε : ∀ G : Modules K Λ, (P.obj G).X 0 ⟶ a.obj G),
      (∀ {G H : Modules K Λ} (h : G ⟶ H) (m : SimplexCategoryᵒᵖ),
        (S.system.component m).map (a.map h) ≫ (ea H m).hom =
          (ea G m).hom ≫ (S.augmentationLift m).moduleFunctor.map h) ∧
      (∀ (G : Modules K Λ) (m k : SimplexCategoryᵒᵖ) (β : k ⟶ m),
        (S.lift β).moduleFunctor.map (ea G m).inv ≫
            S.system.transition (a.obj G) m k β ≫ (ea G k).hom =
          (S.augment β).hom.app G) ∧
      (∀ {G H : Modules K Λ} (h : G ⟶ H) (p : ℕ) (m : SimplexCategoryᵒᵖ)
        (α : SimplexCategory.mk p ⟶ m.unop),
        Sigma.ι (S.summands G p m) α ≫ (e G p m).inv ≫
            (S.system.component m).map ((P.map h).f p) ≫
            (e H p m).hom =
          (S.augmentationLift m).moduleFunctor.map h ≫ Sigma.ι (S.summands H p m) α) ∧
      (∀ (G : Modules K Λ) (p : ℕ) (m k : SimplexCategoryᵒᵖ) (β : k ⟶ m)
        (α : SimplexCategory.mk p ⟶ m.unop),
        (S.lift β).moduleFunctor.map
            (Sigma.ι (S.summands G p m) α ≫ (e G p m).inv) ≫
            S.system.transition ((P.obj G).X p) m k β ≫
            (e G p k).hom =
          (S.augment β).hom.app G ≫ Sigma.ι (S.summands G p k) (α ≫ β.unop)) ∧
      (∀ (G : Modules K Λ) (p : ℕ) (i : Fin (p + 2))
        (m : SimplexCategoryᵒᵖ) (α : SimplexCategory.mk (p + 1) ⟶ m.unop),
        Sigma.ι (S.summands G (p + 1) m) α ≫ (e G (p + 1) m).inv ≫
            (S.system.component m).map (d G p i) ≫ (e G p m).hom =
          Sigma.ι (S.summands G p m) (SimplexCategory.δ i ≫ α)) ∧
      (∀ (G : Modules K Λ) (p : ℕ),
        (P.obj G).d (p + 1) p = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • d G p i) ∧
      (∀ {G H : Modules K Λ} (h : G ⟶ H),
        (P.map h).f 0 ≫ ε H = ε G ≫ a.map h) ∧
      (∀ (G : Modules K Λ) (m : SimplexCategoryᵒᵖ)
        (α : SimplexCategory.mk 0 ⟶ m.unop),
        Sigma.ι (S.summands G 0 m) α ≫ (e G 0 m).inv ≫
            (S.system.component m).map (ε G) ≫ (ea G m).hom = 𝟙 (S.base G m)) ∧
      (∀ G : Modules K Λ,
        (P.obj G).d 1 0 ≫ ε G = 0 ∧
        Epi (ε G) ∧
        (∀ n : ℕ, (P.obj G).ExactAt (n + 1)) ∧
        ∃ h : (P.obj G).d 1 0 ≫ ε G = 0,
          (ShortComplex.mk _ _ h).Exact) ∧
      (∃ Φ : ∀ (p : ℕ) (G : Modules K Λ) (I : T),
          ((P.obj G).X p ⟶ I) ≃
            (S.base G (op (SimplexCategory.mk p)) ⟶
              (S.system.component (op (SimplexCategory.mk p))).obj I),
        (∀ (p : ℕ) (G : Modules K Λ) (I : T) (f : (P.obj G).X p ⟶ I),
          Φ p G I f =
            Sigma.ι (S.summands G p (op (SimplexCategory.mk p))) (𝟙 _) ≫
              (e G p (op (SimplexCategory.mk p))).inv ≫
              (S.system.component (op (SimplexCategory.mk p))).map f) ∧
        (∀ (p : ℕ) (G : Modules K Λ) (I : T)
          (f : S.base G (op (SimplexCategory.mk p)) ⟶
            (S.system.component (op (SimplexCategory.mk p))).obj I)
          (m : SimplexCategoryᵒᵖ) (α : SimplexCategory.mk p ⟶ m.unop),
          Sigma.ι (S.summands G p m) α ≫ (e G p m).inv ≫
              (S.system.component m).map ((Φ p G I).symm f) =
            (S.augment α.op).inv.app G ≫ (S.lift α.op).moduleFunctor.map f ≫
              S.system.transition I (op (SimplexCategory.mk p)) m α.op) ∧
        (∀ (p : ℕ) (G : Modules K Λ) (I I' : T)
          (k : I ⟶ I') (f : (P.obj G).X p ⟶ I),
          Φ p G I' (f ≫ k) =
            Φ p G I f ≫ (S.system.component (op (SimplexCategory.mk p))).map k) ∧
        (∀ (p : ℕ) (G H : Modules K Λ) (h : G ⟶ H) (I : T)
          (f : (P.obj H).X p ⟶ I),
          Φ p G I ((P.map h).f p ≫ f) =
            (S.augmentationLift (op (SimplexCategory.mk p))).moduleFunctor.map h ≫
              Φ p H I f) ∧
        (∀ G : Modules K Λ,
          Φ 0 G (a.obj G) (ε G) = (ea G (op (SimplexCategory.mk 0))).inv)) := by
  sorry

end CategoryTheory
