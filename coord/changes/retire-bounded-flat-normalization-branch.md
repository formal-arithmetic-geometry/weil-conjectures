# Withdraw the obsolete bounded-flat normalization branch

## Reason

The launcher explicitly directs withdrawal of this item and the closed unused branch.
P3 has landed the shift-saturated perfect-generation replacement in both
SmoothProperDiagonalTensorFormula and RightAdjointTensorComparisonProjection.
This delivery retires the 29 remaining eligible modules from that old branch.
Every outside importer is absent; all are outside TargetsCheck's import closure.
No target statement or target-visible definition changes, and no unit step is bypassed.

## Old

The complete withdrawn module sources, verbatim from the delivery base:

### Sheaf.Algebra.Homology.RelativeBiprodConeExtension

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V4
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Abelian.Basic
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! # A relative extension with explicit biproduct terms

Source: Stacks Project Tag 06XX, relative cone construction.
(blueprint: lem-sc-relative-biprod-cone-extension).
-/

@[expose] public section
set_option autoImplicit false
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CochainComplex

set_option maxHeartbeats 600000 in
-- The explicit three-summand cone isomorphism needs many dependent-index checks.
/-- A resolution of the cone of a map produces a strict relative extension whose
terms are the biproducts of the old terms and the resolving terms.

Source: Stacks Project Tag 06XX, relative cone construction before the final
termwise-surjectivity addition. The explicit coordinate proof follows
`exists_relative_boundedAbove_flat_extension` but retains its term description.
Proof: Write the components of the cone resolution as a degree-one map to E
and a degree-zero map to H. On E^i ⊞ Q^i use the differential with diagonal
entries d_E and d_Q and off-diagonal entry minus the first component.
The cone chain-map equation gives square-zero and a map to H. The inclusion
of E is split by the first projection and its composite to H equals f.
The cones of the new map and the given resolution are isomorphic by permuting
the three summands, so the new map is a quasi-isomorphism. The maximum of the
two bounds bounds the new complex. This works also for zero maps and objects.
(blueprint: lem-sc-relative-biprod-cone-extension). -/
theorem exists_relative_biprod_cone_extension
    {C : Type u} [Category.{v} C] [Abelian C]
    (E H : CochainComplex C ℤ) (f : E ⟶ H)
    (hE : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (E.X i))
    (Q : CochainComplex C ℤ) (r : Q ⟶ mappingCone f)
    (hQ : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (Q.X i)) (hr : QuasiIso r) :
    ∃ (F : CochainComplex C ℤ) (t : E ⟶ F) (g : F ⟶ H),
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (F.X i)) ∧
      QuasiIso g ∧ t ≫ g = f ∧ (∀ i : ℤ, IsSplitMono (t.f i)) ∧
      ∀ i : ℤ, Nonempty (F.X i ≅ E.X i ⊞ Q.X i) := by
  -- Realize the triangle directly: the cone coordinates of r determine the twisted sum.
  let a (i : ℤ) := r.f i ≫ (mappingCone.fst f).1.v i (i + 1) rfl
  let b (i : ℤ) := r.f i ≫ (mappingCone.snd f).v i i (add_zero i)
  have ha (i : ℤ) :
      a i ≫ E.d (i + 1) (i + 1 + 1) + Q.d i (i + 1) ≫ a (i + 1) = 0 := by
    dsimp [a]
    have eq := r.comm i (i + 1)
    simp only [← Category.assoc] at eq ⊢
    rw [← eq]
    simp only [Category.assoc, mappingCone.d_fst_v f i (i + 1) (i + 1 + 1) rfl rfl,
      Preadditive.comp_neg, add_neg_cancel]
  have hb (i : ℤ) : Q.d i (i + 1) ≫ b (i + 1) =
      a i ≫ f.f (i + 1) + b i ≫ H.d i (i + 1) := by
    dsimp [a, b]
    rw [← Category.assoc, ← r.comm, Category.assoc, mappingCone.d_snd_v f i
      (i + 1) rfl]
    simp [Preadditive.comp_add, Category.assoc]
  let d (i : ℤ) : E.X i ⊞ Q.X i ⟶ E.X (i + 1) ⊞ Q.X (i + 1) :=
    biprod.desc (E.d i (i + 1) ≫ biprod.inl)
      (-a i ≫ biprod.inl + Q.d i (i + 1) ≫ biprod.inr)
  have hd (i : ℤ) : d i ≫ d (i + 1) = 0 := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext
    all_goals simp [d, Preadditive.add_comp, Preadditive.comp_add, Category.assoc]
    have eq := ha i
    simpa only [Preadditive.neg_comp, neg_add, neg_zero] using congrArg Neg.neg eq
  let F := CochainComplex.of (fun i ↦ E.X i ⊞ Q.X i) d hd
  let t : E ⟶ F := CochainComplex.ofHom (fun _ ↦ biprod.inl) (by
    intro i
    simp [F, d])
  let g : F ⟶ H := CochainComplex.ofHom (fun i ↦ biprod.desc (f.f i) (b i)) (by
    intro i
    apply biprod.hom_ext'
    · simp [F, d, f.comm]
    · simp [F, d, Preadditive.add_comp, Category.assoc, hb])
  refine ⟨F, t, g, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨e, he⟩ := hE
    obtain ⟨q, hq⟩ := hQ
    refine ⟨max e q, fun i hi ↦ ?_⟩
    exact (biprod_isZero_iff _ _).2
      ⟨he i (lt_of_le_of_lt (le_max_left _ _) hi),
        hq i (lt_of_le_of_lt (le_max_right _ _) hi)⟩
  -- Cone(g) and Cone(r) have the same three summands, in different orders.
  · let e (i : ℤ) : (mappingCone g).X i ≅ (mappingCone r).X i :=
      { hom :=
          ((mappingCone.fst g).1.v i (i + 1) rfl ≫ biprod.snd) ≫
              (mappingCone.inl r).v (i + 1) i (by omega) +
            (((mappingCone.fst g).1.v i (i + 1) rfl ≫ biprod.fst) ≫
                (mappingCone.inl f).v (i + 1) i (by omega) +
              (mappingCone.snd g).v i i (add_zero i) ≫ (mappingCone.inr f).f i) ≫
                (mappingCone.inr r).f i
        inv :=
          biprod.lift
              ((mappingCone.snd r).v i i (add_zero i) ≫
                (mappingCone.fst f).1.v i (i + 1) rfl)
              ((mappingCone.fst r).1.v i (i + 1) rfl) ≫
                (mappingCone.inl g).v (i + 1) i (by omega) +
            ((mappingCone.snd r).v i i (add_zero i) ≫
              (mappingCone.snd f).v i i (add_zero i)) ≫ (mappingCone.inr g).f i
        hom_inv_id := by
          apply mappingCone.ext_from g (i + 1) i rfl
          · apply biprod.hom_ext'
            all_goals
              apply mappingCone.ext_to g i (i + 1) rfl
              · apply biprod.hom_ext
                all_goals simp [F, Category.assoc, Preadditive.add_comp, Preadditive.comp_add]
              · simp [F, Category.assoc, Preadditive.add_comp, Preadditive.comp_add]
          · apply mappingCone.ext_to g i (i + 1) rfl
            · apply biprod.hom_ext
              all_goals simp [F, Category.assoc, Preadditive.add_comp, Preadditive.comp_add]
            · simp [F, Category.assoc, Preadditive.add_comp, Preadditive.comp_add]
        inv_hom_id := by
          apply mappingCone.ext_from r (i + 1) i rfl
          · apply mappingCone.ext_to r i (i + 1) rfl
            · simp [F, Category.assoc, Preadditive.add_comp, Preadditive.comp_add]
            · apply mappingCone.ext_to f i (i + 1) rfl
              all_goals simp [F, Category.assoc, Preadditive.add_comp, Preadditive.comp_add]
          · apply mappingCone.ext_from f (i + 1) i rfl
            all_goals
              apply mappingCone.ext_to r i (i + 1) rfl
              · simp [F, Category.assoc, Preadditive.add_comp, Preadditive.comp_add]
              · apply mappingCone.ext_to f i (i + 1) rfl
                all_goals simp [F, Category.assoc, Preadditive.add_comp, Preadditive.comp_add] }
    have he₁ (i : ℤ) : (e i).hom ≫ (mappingCone.fst r).1.v i (i + 1) rfl =
        (mappingCone.fst g).1.v i (i + 1) rfl ≫ biprod.snd := by
      simp [e, Category.assoc, Preadditive.add_comp]
    have he₂ (i : ℤ) : (e i).hom ≫ (mappingCone.snd r).v i i (add_zero i) ≫
        (mappingCone.fst f).1.v i (i + 1) rfl =
          (mappingCone.fst g).1.v i (i + 1) rfl ≫ biprod.fst := by
      simp [e, Category.assoc, Preadditive.add_comp]
    have he₃ (i : ℤ) : (e i).hom ≫ (mappingCone.snd r).v i i (add_zero i) ≫
        (mappingCone.snd f).v i i (add_zero i) =
          (mappingCone.snd g).v i i (add_zero i) := by
      simp [e, Category.assoc, Preadditive.add_comp]
    have he₁' (i : ℤ) {Z : C}
        (k : Q.X (i + 1) ⟶ Z) :
        (e i).hom ≫ (mappingCone.fst r).1.v i (i + 1) rfl ≫ k =
          (mappingCone.fst g).1.v i (i + 1) rfl ≫ biprod.snd ≫ k := by
      rw [← Category.assoc, he₁, Category.assoc]
    have he₂' (i : ℤ) {Z : C}
        (k : E.X (i + 1) ⟶ Z) :
        (e i).hom ≫ (mappingCone.snd r).v i i (add_zero i) ≫
          (mappingCone.fst f).1.v i (i + 1) rfl ≫ k =
            (mappingCone.fst g).1.v i (i + 1) rfl ≫ biprod.fst ≫ k := by
      simp only [← Category.assoc, he₂]
    have he₃' (i : ℤ) {Z : C}
        (k : H.X i ⟶ Z) :
        (e i).hom ≫ (mappingCone.snd r).v i i (add_zero i) ≫
          (mappingCone.snd f).v i i (add_zero i) ≫ k =
            (mappingCone.snd g).v i i (add_zero i) ≫ k := by
      simp only [← Category.assoc, he₃]
    have hd₁ (i : ℤ) : F.d i (i + 1) ≫ biprod.fst =
        biprod.fst ≫ E.d i (i + 1) - biprod.snd ≫ a i := by
      dsimp only [F]
      rw [of_d]
      apply biprod.hom_ext'
      all_goals simp [d, Preadditive.comp_sub, Preadditive.add_comp, Category.assoc]
    have hd₂ (i : ℤ) : F.d i (i + 1) ≫ biprod.snd =
        biprod.snd ≫ Q.d i (i + 1) := by
      dsimp only [F]
      rw [of_d]
      apply biprod.hom_ext'
      all_goals simp [d, Preadditive.add_comp, Category.assoc]
    have hg (i : ℤ) : g.f i = biprod.fst ≫ f.f i + biprod.snd ≫ b i := by
      change biprod.desc _ _ = _
      exact biprod.desc_eq
    let ec : mappingCone g ≅ mappingCone r :=
      HomologicalComplex.Hom.isoOfComponents e (by
        rintro i _ rfl
        apply mappingCone.ext_to r (i + 1) (i + 1 + 1) rfl
        · simp only [Category.assoc,
            mappingCone.d_fst_v r i (i + 1) (i + 1 + 1) rfl rfl,
            Preadditive.comp_neg, Preadditive.neg_comp, he₁', he₁,
            mappingCone.d_fst_v_assoc g i (i + 1) (i + 1 + 1) rfl rfl,
            hd₂]
        · apply mappingCone.ext_to f (i + 1) (i + 1 + 1) rfl
          · simp only [Category.assoc,
              mappingCone.d_snd_v_assoc r i (i + 1) rfl, Preadditive.comp_add, Preadditive.add_comp,
              mappingCone.d_fst_v f i (i + 1) (i + 1 + 1) rfl rfl,
              Preadditive.comp_neg, Preadditive.neg_comp, he₁', he₂', he₂,
              mappingCone.d_fst_v_assoc g i (i + 1) (i + 1 + 1) rfl rfl,
              hd₁, Preadditive.comp_sub]
            change _ ≫ _ ≫ a (i + 1) + -(_ ≫ _ ≫ _) = -(_ - _)
            abel
          · simp only [Category.assoc,
              mappingCone.d_snd_v_assoc r i (i + 1) rfl, Preadditive.comp_add, Preadditive.add_comp,
              mappingCone.d_snd_v f i (i + 1) rfl,
              he₁', he₂', he₃', he₃,
              mappingCone.d_snd_v g i (i + 1) rfl, hg, Preadditive.comp_add]
            change _ ≫ _ ≫ b (i + 1) + (_ + _) = (_ + _) + _
            abel)
    apply (mappingCone.quasiIso_iff_acyclic g).2
    have hc := (mappingCone.quasiIso_iff_acyclic r).1 hr
    intro i
    apply (HomologicalComplex.exactAt_iff_isZero_homology _ i).2
    exact ((HomologicalComplex.exactAt_iff_isZero_homology _ i).1 (hc i)).of_iso
      ((HomologicalComplex.homologyFunctor _ _ i).mapIso ec)
  · ext i
    simp [t, g]
  · intro i
    exact ⟨⟨biprod.fst, by simp [t]⟩⟩
  · intro i
    exact ⟨Iso.refl _⟩

end CochainComplex
```

### Sheaf.Algebra.Homology.TensorShiftOneAssociator

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import Mathlib.Algebra.Homology.BifunctorShift

/-! # First-factor translation and the total tensor associator
Source: Stacks Project, Tag 06YH, the homogeneous-summand calculation.
(blueprint: lem-sc-total-tensor-shift-one-associator).
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [HasColimitsOfSize.{0, 0} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- First-factor translation by one commutes with the total tensor associator.
Source: Stacks Project, Tag 06YH, the homogeneous-summand calculation in
lem-sc-scheme-canonical-tensor-shift-associator-kflat-one.
(blueprint: lem-sc-total-tensor-shift-one-associator).

Proof. Test the two maps on each tridegree summand of the source total complex.
The first-factor shift map has coefficient one. Reassociation applies the module
associator, so either order gives the same map into the target summand, with first
index increased by one. Coproduct extensionality in each degree, followed by
complex extensionality, proves equality. The maps already commute with the
signed differentials by construction of mapBifunctorShift₁Iso. This works also
for zero complexes and in characteristic two. -/
theorem tensorShiftOne_associator (P T U : CochainComplex C ℤ) :
    (α_ (P⟦(1 : ℤ)⟧) T U).hom ≫
        (mapBifunctorShift₁Iso P (T ⊗ U) (curriedTensor C) 1).hom =
      (mapBifunctorShift₁Iso P T (curriedTensor C) 1).hom ▷ U ≫
        (mapBifunctorShift₁Iso (P ⊗ T) U (curriedTensor C) 1).hom ≫
        (α_ P T U).hom⟦(1 : ℤ)⟧' := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor₁₂.hom_ext
  intro p q r h
  simp only [HomologicalComplex.comp_f]
  change _ ≫ (HomologicalComplex.mapBifunctorAssociatorX
    (curriedAssociatorNatIso C) (P⟦(1 : ℤ)⟧) T U (.up ℤ) (.up ℤ) (.up ℤ) n).hom ≫ _ =
    _ ≫ _ ≫ _ ≫ (HomologicalComplex.mapBifunctorAssociatorX
      (curriedAssociatorNatIso C) P T U (.up ℤ) (.up ℤ) (.up ℤ) (n + 1)).hom
  rw [HomologicalComplex.ι_mapBifunctorAssociatorX_hom_assoc]
  have h₁ : (p + q) + r = n := h
  have h₂ : p + (q + r) = n := by omega
  rw [HomologicalComplex.mapBifunctor₂₃.ι_eq _ _ _ _ _ _ _ _ _ _ _ (q + r) _ rfl h₂,
    HomologicalComplex.mapBifunctor₁₂.ι_eq _ _ _ _ _ _ _ _ _ _ (p + q) _ rfl h₁]
  simp only [Category.assoc]
  erw [ι_mapBifunctorShift₁Iso_hom_f P (T ⊗ U) (curriedTensor C) 1
    p (q + r) n h₂ (p + 1) (n + 1) rfl rfl]
  erw [HomologicalComplex.ι_mapBifunctorMap_assoc]
  simp only [HomologicalComplex.id_f]
  erw [ι_mapBifunctorShift₁Iso_hom_f_assoc (P ⊗ T) U (curriedTensor C) 1
    (p + q) r n h₁ (p + q + 1) (n + 1) rfl rfl]
  dsimp [shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq]
  simp only [Category.id_comp, Category.comp_id]
  simp only [whiskerLeft_id, Category.id_comp]
  rw [← comp_whiskerRight_assoc]
  erw [ι_mapBifunctorShift₁Iso_hom_f P T (curriedTensor C) 1
    p q (p + q) rfl (p + 1) (p + q + 1) rfl rfl]
  dsimp [shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq]
  dsimp only [curriedAssociatorNatIso, NatIso.ofComponents]
  erw [id_whiskerRight, id_whiskerRight, id_whiskerRight]
  simp only [Category.id_comp]
  have h₃ : (p + 1 + q) + r = n + 1 := by omega
  have h₄ : (p + 1) + (q + r) = n + 1 := by omega
  have he := HomologicalComplex.ι_mapBifunctorAssociatorX_hom
    (curriedAssociatorNatIso C) P T U (.up ℤ) (.up ℤ) (.up ℤ)
    (p + 1) q r (n + 1) h₃
  rw [HomologicalComplex.mapBifunctor₁₂.ι_eq _ _ _ _ _ _ _ _ _ _
    (p + q + 1) _ (by dsimp; omega) (by dsimp; omega),
    HomologicalComplex.mapBifunctor₂₃.ι_eq _ _ _ _ _ _ _ _ _ _ _
    (q + r) _ rfl h₄] at he
  erw [Category.id_comp, Category.comp_id]
  simp only [Category.assoc] at he
  convert he.symm using 1 <;> rfl

end CochainComplex
```

### Sheaf.AlgebraicGeometry.BoundedFlatModelNormalization

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitIso
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import Sheaf.AlgebraicGeometry.DerivedTensorStructure
import Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShift

/-! # Bounded flat model normalization

Source: Stacks Tags 06YS and 06YJ. -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
namespace AlgebraicGeometry

/-- Bounded-above flat complex presentations, including their one-fold translates.
Source: Stacks Tag 06YS (blueprint: def-sc-bounded-flat-shift-representative). -/
def boundedFlatShiftRepresentative (Y : Scheme.{u})
    (X : HomotopyCategory
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)) : Prop :=
  ∃ P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
    (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i)) ∧
    (∀ i : ℤ, SheafOfModules.IsFlat (P.X i)) ∧
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P = X ∨
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)⟦(1 : ℤ)⟧ = X)

/-- Joint translated-unit normalization on bounded-above flat stages only.
Source: steps 1--2 of lem-sc-flat-telescope-model-shift-gauge. Stacks Tags 06YS
and 06YJ supply K-flat computation, not the supplied-tensorator normalization.

Proof. Compute pullback on the bounded-above flat complex itself, which is K-flat.
Use the structure sheaf concentrated in degree zero and its translate for the unit
models. Normalize the degree-zero identification using the supplied monoidal unit.
For each stage rewrite its translate by the first-variable Koszul isomorphism and
translated left unitor. Compose the inverse source rewrite, supplied inverse
pullback tensorator, translated-unit identification tensor the stage comparison,
and target rewrite. The two monoidal unit equations identify the unit normalizations;
associativity identifies repeated rewrites. The maps are invertible and natural
for cochain maps, preserve homotopies, and commute with quasi-isomorphisms between
flat presentations. Transport along the localization comparisons to the indicated
homotopy objects; common flat resolutions identify the transported components.
This gives naturality and the displayed shift equation. This construction does
not take countable sums or transition cones. Zero complexes, arbitrary upper bounds,
and empty schemes require no cancellation of noninvertible maps.
(blueprint: lem-sc-bounded-flat-model-normalization). -/
theorem exists_bounded_flat_model_normalization
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    [(Scheme.Modules.tensorPullback f).Additive] :
    ∃ e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
        (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧,
      ∃ α : ∀ X : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ),
        boundedFlatShiftRepresentative Y X →
          ((DerivedCategory.Qh ⋙ derivedPullback f).obj X ≅
            ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
              (DerivedCategory.Qh : HomotopyCategory
                (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                schemeDerivedCategory Z)).obj X),
        (∀ (X X' : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
          (hX : boundedFlatShiftRepresentative Y X) (hX' : boundedFlatShiftRepresentative Y X')
          (s : X ⟶ X'),
          (DerivedCategory.Qh ⋙ derivedPullback f).map s ≫ (α X' hX').hom =
            (α X hX).hom ≫
              ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
                (DerivedCategory.Qh : HomotopyCategory
                  (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                  schemeDerivedCategory Z)).map s) ∧
        ∀ (P : CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
        (hb : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i))
        (hf : ∀ i : ℤ, SheafOfModules.IsFlat (P.X i)),
        let X := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P
        let G := (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          (DerivedCategory.Qh : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
            schemeDerivedCategory Z)
        (α (X⟦(1 : ℤ)⟧) ⟨P, hb, hf, Or.inr rfl⟩).hom ≫
            (G.commShiftIso (1 : ℤ)).hom.app X =
          (derivedPullback f).map ((DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app X) ≫
            ((derivedPullback f).mapIso
                (schemeCanonicalShiftUnitIso Y (DerivedCategory.Qh.obj X)).symm ≪≫
              asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) (DerivedCategory.Qh.obj X)) ≪≫
              tensorIso e (Iso.refl _) ≪≫
              schemeCanonicalShiftUnitIso Z
                ((derivedPullback f).obj (DerivedCategory.Qh.obj X))).hom ≫
            (α X ⟨P, hb, hf, Or.inl rfl⟩).hom⟦(1 : ℤ)⟧' := by sorry

end AlgebraicGeometry
```

### Sheaf.AlgebraicGeometry.CompactFlatBarUnionAugmentation

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.AlgebraicGeometry.CompactFlatFiniteSubcomplexDiagrams
import Sheaf.AlgebraicGeometry.CompactFlatSourceBarQuasiIso
import Sheaf.AlgebraicGeometry.CompactFlatBarUnionHomotopy

/-! # Canonical augmentation of the enlarged finite-piece bar union

Source: the finite-subcomplex and target-chain portions of
`lem-sc-compact-flat-telescope-bar-enlargement`.
(blueprint: lem-sc-compact-flat-bar-union-augmentation).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The geometric part of bar enlargement: a split flat bar tower with compatible
augmentations whose union augmentation is a homotopy equivalence. This statement
contains no split exact presentation of its union.

Source: the finite-piece and target-chain paragraphs of
`lem-sc-compact-flat-telescope-bar-enlargement`, originally expanded in
`lem-sc-flat-telescope-target-refinement`.

Proof. Use the supplied stage-filtered diagrams D_n of finite complexes. Their
specified colimit cocones have vertices L_n and commute strictly with l_n. Each
D_n is filtered, every object has finitely many nonzero degrees with finite
compact-flat summands, and its objects have a common stage upper bound. Use the
one global indexing preorder to include D_n into D_(n+1); no new generator
choices or subcomplex closure argument is needed.
Take the unnormalized bar total R_n, placing simplicial degree p in degree -p.
Exactness of filtered colimits gives a quasi-isomorphism c_n to L_n. A common
upper bound for stages at most n bounds this total above; its terms are sums of
flat sheaves. Inclusion of stage-labelled diagrams gives s_n, strictly compatible
with the augmentations. Labelled copies avoid requiring the source generator
choices to be compatible with the tower maps.

Write T as its supplied telescope. The finite cone blocks C_k use source indices
at most k and target indices at most k+1. They are flat and bounded above, with
degreewise split inclusions and union T. Every finite source diagram object factors
through a block, by compactness in its finitely many nonzero degrees. The factor
is a chain map because the block inclusion is monic. Enlarge the union diagram
by this target chain, putting an arrow from a source object to k exactly when
its augmentation factors through C_k. There is a least such k, monotone in the
source object; it is left adjoint to target-chain inclusion. Insert the unit in
bar strings with alternating signs to get the corresponding bar homotopy.
Let F_n be the full-subdiagram bar total using D_n and target indices at most n.
Bar inclusions give u_n and a_n; each u_n is degreewise split since its bar
summands form a subset of the next bar summands. Their augmentations q_n into T
satisfy the two stated identities strictly. F_n is flat and bounded above by
the common bound on this finite segment.

The union bar total is the cokernel of identity minus shift: its relations
identify each simplex with the same simplex at the next stage. Compare the bar
of the finite cone blocks with the cone of the two partial-sum bars. The comparison
multiplies the source summand in horizontal degree p by (-1)^p and leaves the target
summand unchanged; the total differential identities verify it is a chain isomorphism.
The partial-sum bars contract onto their infinite sums: on the coefficient at index k,
prepend its first available stage k-r, with r=0 or r=1 respectively. These explicit
extra degeneracies give homotopy equivalences preserving augmentation. Apply the
isomorphism theorem for morphisms of distinguished cone triangles to conclude that
the target-chain bar augmentation is a homotopy equivalence. Cancel the unit-insertion
bar equivalence
to conclude this for the enlarged union's canonical augmentation as well.
Identify the union with the displayed cokernel by its universal property. This
identification carries its augmentation to cokernel.desc of Sigma.desc q.
The zero relation follows from compatibility of q. Its chosen proof is
irrelevant, so the asserted isomorphism holds for every hzero. No witness is
chosen as the data of a definition.
(blueprint: lem-sc-compact-flat-bar-union-augmentation). -/
theorem exists_compact_flat_bar_union_augmentation (Y : Scheme.{u})
    (L : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (l : ∀ n : ℕ, L n ⟶ L (n + 1))
    (D : CompactFlatFiniteSubcomplexDiagrams Y L l)
    (T : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hT : isFlatTelescope Y T) (p : ∀ n : ℕ, L n ⟶ T)
    (hp : ∀ n : ℕ, l n ≫ p (n + 1) = p n) :
    let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
    let Q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
    ∃ (R F : ℕ → CochainComplex A ℤ)
      (s : ∀ n : ℕ, R n ⟶ R (n + 1))
      (u : ∀ n : ℕ, F n ⟶ F (n + 1))
      (c : ∀ n : ℕ, R n ⟶ L n) (a : ∀ n : ℕ, R n ⟶ F n),
      (∀ n : ℕ, ∃ z : ℤ, ∀ i : ℤ, z < i → IsZero ((R n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((R n).X i)) ∧
      (∀ n : ℕ, ∃ z : ℤ, ∀ i : ℤ, z < i → IsZero ((F n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((F n).X i)) ∧
      (∀ n : ℕ, QuasiIso (c n)) ∧
      (∀ n : ℕ, s n ≫ c (n + 1) = c n ≫ l n) ∧
      (∀ n : ℕ, s n ≫ a (n + 1) = a n ≫ u n) ∧
      (∀ (n : ℕ) (i : ℤ), IsSplitMono ((u n).f i)) ∧
      ∃ q : ∀ n : ℕ, F n ⟶ T,
        (∀ n : ℕ, u n ≫ q (n + 1) = q n) ∧
        (∀ n : ℕ, a n ≫ q n = c n ≫ p n) ∧
        ∀ hzero : flatTelescopeDifferential F u ≫ Sigma.desc q = 0,
          IsIso (Q.map
            (cokernel.desc (flatTelescopeDifferential F u) (Sigma.desc q) hzero)) := by
  obtain ⟨E, t, hb, hf, hE⟩ := hT
  change CochainComplex.mappingCone (flatTelescopeDifferential E t) = T at hE
  subst T
  dsimp only
  refine ⟨D.sourceBar, CompactFlatBarIndex.enlargedBar D E t p hp,
    D.sourceBarMap, CompactFlatBarIndex.enlargedBarMap D E t p hp,
    D.sourceBarAugmentation, CompactFlatBarIndex.sourceToBar D E t p hp,
    D.sourceBar_bounded, D.sourceBar_flat,
    CompactFlatBarIndex.enlargedBar_bounded D E t p hp hb,
    CompactFlatBarIndex.enlargedBar_flat D E t p hp hf,
    D.sourceBarAugmentation_quasiIso, D.sourceBarAugmentation_naturality,
    CompactFlatBarIndex.sourceToBar_naturality D E t p hp,
    CompactFlatBarIndex.enlargedBarMap_split D E t p hp,
    CompactFlatBarIndex.enlargedBarAugmentation D E t p hp,
    CompactFlatBarIndex.enlargedBarAugmentation_naturality D E t p hp,
    CompactFlatBarIndex.sourceToBar_augmentation D E t p hp,
    CompactFlatBarIndex.cokernelAugmentation_isIso D E t p hp⟩

end AlgebraicGeometry
```

### Sheaf.AlgebraicGeometry.CompactFlatGeneratorCover

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V4
-/
module

public import Sheaf.Paper.DerivedHomMayerVietoris
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
import Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.CategoryTheory.Limits.Constructions.Filtered
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-! # Functorial covers by compact flat generators

Source: Stacks Project Tags 03EW and 077J, specialized to affine opens of a scheme.
(blueprint: lem-sc-compact-flat-generator-cover).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Limits.CoproductsFromFiniteFiltered
namespace AlgebraicGeometry

private noncomputable def affineGenerator (Y : Scheme.{u}) (U : TopologicalSpace.Opens Y) :
    SheafOfModules.{u} (moduleRings Y.toRingedSpace) :=
  (PresheafOfModules.sheafification (𝟙 (moduleRings Y.toRingedSpace).obj)).obj
    ((PresheafOfModules.free (moduleRings Y.toRingedSpace).obj).obj (yoneda.obj U))
private noncomputable def affineGeneratorHomEquiv (Y : Scheme.{u}) (U : TopologicalSpace.Opens Y)
    (M : SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :
    (affineGenerator Y U ⟶ M) ≃ M.val.obj (op U) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 (moduleRings Y.toRingedSpace).obj)).trans
    PresheafOfModules.freeYonedaEquiv
private theorem affineGeneratorHomEquiv_comp (Y : Scheme.{u}) (U : TopologicalSpace.Opens Y)
    {M N : SheafOfModules.{u} (moduleRings Y.toRingedSpace)}
    (f : affineGenerator Y U ⟶ M) (g : M ⟶ N) :
    affineGeneratorHomEquiv Y U N (f ≫ g) =
      g.val.app (op U) (affineGeneratorHomEquiv Y U M f) := by
  change PresheafOfModules.freeYonedaEquiv
      ((PresheafOfModules.sheafificationAdjunction _).homEquiv _ _ (f ≫ g)) = _
  rw [Adjunction.homEquiv_naturality_right]
  exact PresheafOfModules.freeYonedaEquiv_comp _ _
private theorem affineGenerator_flat (Y : Scheme.{u}) (U : TopologicalSpace.Opens Y) :
    SheafOfModules.IsFlat (affineGenerator Y U) := by
  let O := moduleRings Y.toRingedSpace
  let P := (PresheafOfModules.free O.obj).obj (yoneda.obj U)
  have hflatX (V : (TopologicalSpace.Opens Y)ᵒᵖ) :
      Module.Flat (Y.toRingedSpace.sheaf.obj.obj V) (P.obj V) := by
    change Module.Flat (Y.toRingedSpace.sheaf.obj.obj V)
      ((V.unop ⟶ U) →₀ Y.toRingedSpace.sheaf.obj.obj V)
    infer_instance
  have hpres : PreservesFiniteLimits (MonoidalCategory.tensorRight P) := by
    constructor
    intro K _ _
    constructor
    intro F
    constructor
    intro c hc
    have hpresX (V : (TopologicalSpace.Opens Y)ᵒᵖ) :
        PreservesFiniteLimits (MonoidalCategory.tensorRight
          (show ModuleCat (Y.toRingedSpace.sheaf.obj.obj V) from P.obj V)) := by
      have := hflatX V
      infer_instance
    exact ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun V ↦
      isLimitOfPreserves (MonoidalCategory.tensorRight
        (show ModuleCat (Y.toRingedSpace.sheaf.obj.obj V) from P.obj V))
        (isLimitOfPreserves (PresheafOfModules.evaluation _ V) hc))⟩
  have : Presheaf.IsLocallyInjective
      (Opens.grothendieckTopology Y) (𝟙 O.obj) :=
    Presheaf.isLocallyInjective_of_injective _ _ (fun _ ↦ Function.injective_id)
  have : Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology Y) (𝟙 O.obj) :=
    Presheaf.isLocallySurjective_of_surjective _ _ (fun _ ↦ Function.surjective_id)
  exact (PresheafOfModules.isFlat_sheafification_obj
    (R := Y.toRingedSpace.sheaf) (𝟙 O.obj) P hpres).2

private noncomputable def affineGeneratorCover (Y : Scheme.{u}) :
    SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings Y.toRingedSpace) where
  obj M := ∐ (fun x : Σ U : Y.affineOpens, M.val.obj (op U.1) ↦ affineGenerator Y x.1.1)
  map {M N} f := Sigma.desc (fun x ↦ Sigma.ι
    (fun y : Σ U : Y.affineOpens, N.val.obj (op U.1) ↦ affineGenerator Y y.1.1)
    ⟨x.1, f.val.app (op x.1.1) x.2⟩)
  map_id M := by
    apply Sigma.hom_ext
    intro x
    simp only [Sigma.ι_desc, Category.comp_id]
    rfl
  map_comp f g := by
    apply Sigma.hom_ext
    intro x
    simp only [Sigma.ι_desc, Sigma.ι_desc_assoc]
    rfl
private noncomputable def affineCoverAugmentation (Y : Scheme.{u}) :
    affineGeneratorCover Y ⟶ 𝟭 _ where
  app M := Sigma.desc (fun x ↦ (affineGeneratorHomEquiv Y x.1.1 M).symm x.2)
  naturality {M N} f := by
    apply Sigma.hom_ext
    intro x
    symm
    change Sigma.ι _ x ≫
      Sigma.desc (fun x ↦ (affineGeneratorHomEquiv Y x.1.1 M).symm x.2) ≫ f =
      Sigma.ι _ x ≫ Sigma.desc (fun x ↦ Sigma.ι
        (fun y : Σ U : Y.affineOpens, N.val.obj (op U.1) ↦ affineGenerator Y y.1.1)
        ⟨x.1, f.val.app (op x.1.1) x.2⟩) ≫
      Sigma.desc (fun x ↦ (affineGeneratorHomEquiv Y x.1.1 N).symm x.2)
    simp only [Sigma.ι_desc, Sigma.ι_desc_assoc]
    apply (affineGeneratorHomEquiv Y x.1.1 N).injective
    rw [affineGeneratorHomEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
set_option backward.isDefEq.respectTransparency false in
private theorem affineCover_epi (Y : Scheme.{u})
    (M : SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    (q : (∐ (fun x : Σ U : Y.affineOpens, M.val.obj (op U.1) ↦
      affineGenerator Y x.1.1)) ⟶ M)
    (hq : ∀ x : Σ U : Y.affineOpens, M.val.obj (op U.1),
      Sigma.ι _ x ≫ q = (affineGeneratorHomEquiv Y x.1.1 M).symm x.2) :
    Epi q := by
  constructor
  intro N f g h
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  rintro ⟨U⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  let V := {V : Y.affineOpens // V.1 ≤ U}
  let cover : V → TopologicalSpace.Opens Y := fun V ↦ V.1.1
  have hc : U ≤ iSup cover := by
    intro x hx
    obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWU⟩, hxW⟩
  let Nsheaf : TopCat.Sheaf AddCommGrpCat.{u} Y :=
    ⟨N.val.presheaf, N.isSheaf⟩
  apply Nsheaf.eq_of_locally_eq' cover U
    (fun V ↦ homOfLE V.2) hc
  intro V
  change N.val.map (homOfLE V.2).op (f.val.app (op U) s) =
    N.val.map (homOfLE V.2).op (g.val.app (op U) s)
  have hh := Sigma.ι
    (fun x : Σ W : Y.affineOpens, M.val.obj (op W.1) ↦ affineGenerator Y x.1.1)
    ⟨V.1, M.val.map (homOfLE V.2).op s⟩ ≫= h
  simp only [← Category.assoc, hq] at hh
  have he := congrArg (affineGeneratorHomEquiv Y V.1.1 N) hh
  simp only [affineGeneratorHomEquiv_comp, Equiv.apply_symm_apply] at he
  rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply] at he
  exact he
set_option backward.isDefEq.respectTransparency false in
private theorem colimit_comparison_locally_surjective
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {K : Type u} [SmallCategory K]
    (D : K ⥤ SheafOfModules.{u} R) (c : Limits.Cocone D) (hc : Limits.IsColimit c) :
    Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map
        (Limits.colimit.desc (D ⋙ SheafOfModules.forget R)
          ((SheafOfModules.forget R).mapCocone c))) := by
  let U := SheafOfModules.forget R
  let L := PresheafOfModules.sheafification (𝟙 R.obj)
  let adj : L ⊣ U := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  let P := Limits.colimit.cocone (D ⋙ U)
  let hP := Limits.colimit.isColimit (D ⋙ U)
  let hQ := Limits.isColimitOfPreserves L hP
  let e : (D ⋙ U) ⋙ L ≅ D := Functor.isoWhiskerLeft D (asIso adj.counit)
  let hcE := (Limits.IsColimit.precomposeHomEquiv e c).symm hc
  let θ := hQ.coconePointUniqueUpToIso hcE
  let k := adj.unit.app P.pt ≫ U.map θ.hom
  have hk (i : K) : P.ι.app i ≫ k = U.map (c.ι.app i) := by
    dsimp only [k]
    have hn := adj.unit.naturality (P.ι.app i)
    change P.ι.app i ≫ adj.unit.app P.pt =
      adj.unit.app (U.obj (D.obj i)) ≫ U.map (L.map (P.ι.app i)) at hn
    rw [← Category.assoc, hn, Category.assoc, ← U.map_comp]
    have hθ := hQ.comp_coconePointUniqueUpToIso_hom hcE i
    change L.map (P.ι.app i) ≫ θ.hom = adj.counit.app (D.obj i) ≫ c.ι.app i at hθ
    rw [hθ, U.map_comp, ← Category.assoc, adj.right_triangle_components]
    exact Category.id_comp _
  have heq : Limits.colimit.desc (D ⋙ U) (U.mapCocone c) = k := by
    apply hP.hom_ext
    intro i
    exact (hP.fac _ i).trans (hk i).symm
  rw [heq, Functor.map_comp]
  have : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map (adj.unit.app P.pt)) := by
    change Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P.pt.presheaf)
    infer_instance
  infer_instance


set_option backward.isDefEq.respectTransparency false in
private theorem exists_local_subcoproduct_section (Y : Scheme.{u}) (U : TopologicalSpace.Opens Y)
    (K : Type u) (H : K → SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    (s : (∐ H).val.obj (op U)) (x : U) :
    ∃ (W : TopologicalSpace.Opens Y) (hWU : W ≤ U), x.val ∈ W ∧
      ∃ (S : Finset (Discrete K))
        (t : (∐ (fun k : S ↦ H k.val.as)).val.obj (op W)),
        (Sigma.desc (fun k : S ↦ Sigma.ι H k.val.as)).val.app (op W) t =
          (∐ H).val.map (homOfLE hWU).op s := by
  let R := moduleRings Y.toRingedSpace
  let D := liftToFinsetObj (Discrete.functor H)
  let c := finiteSubcoproductsCocone H
  let hc := isColimitFiniteSubproductsCocone H
  let F := D ⋙ SheafOfModules.forget R
  let P := colimit F
  let k : P ⟶ (∐ H).val := colimit.desc F ((SheafOfModules.forget R).mapCocone c)
  let q := (PresheafOfModules.toPresheaf R.obj).map k
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y) q :=
    colimit_comparison_locally_surjective R D c hc
  have hcover := Presheaf.imageSieve_mem (Opens.grothendieckTopology Y) q s
  obtain ⟨W, f, hf, hxW⟩ := hcover x.val x.property
  obtain ⟨t, ht⟩ := hf
  let E := PresheafOfModules.evaluation R.obj (op W) ⋙ CategoryTheory.forget _
  have : PreservesColimit F E := by dsimp [E]; infer_instance
  obtain ⟨i, a, ha⟩ := Types.jointly_surjective (F ⋙ E)
    (isColimitOfPreserves E (colimit.isColimit F)) t
  refine ⟨W, leOfHom f, hxW, i, a, ?_⟩
  have hk := colimit.ι_desc ((SheafOfModules.forget R).mapCocone c) i
  have hk' := congrArg (fun g ↦ g.app (op W) a) hk
  change k.app (op W) ((colimit.ι F i).app (op W) a) =
    (c.ι.app i).val.app (op W) a at hk'
  change (colimit.ι F i).app (op W) a = t at ha
  rw [ha] at hk'
  exact hk'.symm.trans ht

set_option backward.isDefEq.respectTransparency false in
private theorem affineGenerator_compact (Y : Scheme.{u}) (U : Y.affineOpens)
    (K : Type u) (H : K → SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    (f : affineGenerator Y U.1 ⟶ ∐ H) :
    ∃ (S : Finset K) (g : affineGenerator Y U.1 ⟶ ∐ (fun k : {k // k ∈ S} ↦ H k.1)),
      g ≫ Sigma.desc (fun k : {k // k ∈ S} ↦ Sigma.ι H k.1) = f := by
  classical
  let s := affineGeneratorHomEquiv Y U.1 (∐ H) f
  choose W hWU hx S t ht using fun x : U.1 ↦ exists_local_subcoproduct_section Y U.1 K H s x
  obtain ⟨B, hB⟩ := U.2.isCompact.elim_finite_subcover
    (fun x : U.1 ↦ (W x : Set Y)) (fun x ↦ (W x).isOpen) (by
      intro x hxU
      exact Set.mem_iUnion.mpr ⟨(⟨x, hxU⟩ : U.1), hx (⟨x, hxU⟩ : U.1)⟩)
  let S' : Finset K := (B.biUnion S).image Discrete.as
  have hS (x : U.1) (hxB : x ∈ B) (k : S x) : k.val.as ∈ S' := by
    exact Finset.mem_image.mpr ⟨k.val,
      Finset.mem_biUnion.mpr ⟨x, hxB, k.property⟩, rfl⟩
  let inc : (∐ (fun k : {k // k ∈ S'} ↦ H k.1)) ⟶ ∐ H :=
    Sigma.desc (fun k ↦ Sigma.ι H k.1)
  let p : (∐ H) ⟶ ∐ (fun k : {k // k ∈ S'} ↦ H k.1) :=
    Sigma.desc (fun k ↦ if h : k ∈ S' then Sigma.ι (fun k : {k // k ∈ S'} ↦ H k.1) ⟨k, h⟩ else 0)
  refine ⟨S', f ≫ p, ?_⟩
  apply (affineGeneratorHomEquiv Y U.1 (∐ H)).injective
  rw [affineGeneratorHomEquiv_comp, affineGeneratorHomEquiv_comp]
  change inc.val.app (op U.1) (p.val.app (op U.1) s) = s
  let F : TopCat.Sheaf AddCommGrpCat.{u} Y := ⟨(∐ H).val.presheaf, (∐ H).isSheaf⟩
  let cover : B → TopologicalSpace.Opens Y := fun x ↦ W x.1
  have hc : U.1 ≤ iSup cover := by
    intro x hxU
    obtain ⟨y, hy⟩ := Set.mem_iUnion.mp (hB hxU)
    obtain ⟨hyB, hxy⟩ := Set.mem_iUnion.mp hy
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hyB⟩, hxy⟩
  apply F.eq_of_locally_eq' cover U.1 (fun x ↦ homOfLE (hWU x.1)) hc
  intro x
  change (∐ H).val.map (homOfLE (hWU x.1)).op
      (inc.val.app (op U.1) (p.val.app (op U.1) s)) =
    (∐ H).val.map (homOfLE (hWU x.1)).op s
  rw [← PresheafOfModules.naturality_apply inc.val,
    ← PresheafOfModules.naturality_apply p.val, ← ht x.1]
  let incx : (∐ (fun k : S x.1 ↦ H k.val.as)) ⟶ ∐ H :=
    Sigma.desc (fun k ↦ Sigma.ι H k.val.as)
  have he : incx ≫ p ≫ inc = incx := by
    apply Sigma.hom_ext
    intro k
    simp [incx, p, inc, hS x.1 x.2 k]
  have ee := congrArg (fun e ↦ e.val.app (op (W x.1)) (t x.1)) he
  exact ee

/-- Every module sheaf has a functorial epic cover by a coproduct of flat sheaves
whose maps into arbitrary coproducts have finite support.

Source: Stacks Project Tag 03EW (3), the affine-open specialization of the
resolving class in Tag 077J and the parent relative-extension proof.
Proof: For each affine open U take the sheafification of the free module
presheaf on the representable presheaf U. This is a concrete model of j_! O_U.
Its section modules before sheafification are free; sheafification preserves
flatness. The sheafification and free-Yoneda adjunctions identify maps from this
generator with sections on U. Express a coproduct as the filtered colimit of
its finite subcoproducts. The comparison from the presheaf colimit to the sheaf
colimit is locally surjective because it is the sheafification unit followed
by an isomorphism. A lifted section of the presheaf colimit comes from one
finite stage. Quasi-compactness of U gives a finite subcover of these local
lifts. Take the union of their supports and project the original section onto
this finite subsum. On each member of the finite cover this projection followed
by inclusion fixes the section; sheaf separatedness gives the equality on U.
Define the cover of M to be the coproduct of these generators over all pairs
(U,s), where U is affine and s is a section of M on U. Its augmentation is
evaluation under the adjunction. A sheaf map sends (U,s) to (U,f(s)), using
the identity on the generator; coproduct universality gives functoriality
and naturality. To prove the augmentation epic, two maps out of M agreeing
after augmentation agree on every affine local section. Affine opens form
a basis, so sheaf separatedness makes the two maps equal on every open.
All indices lie in the scheme universe. The empty scheme and empty supports
need no exceptions. No sectionwise surjectivity or projectivity is asserted.
(blueprint: lem-sc-compact-flat-generator-cover). -/
theorem exists_functorial_compact_flat_generator_cover (Y : Scheme.{u}) :
    let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
    ∃ (T : A ⥤ A) (π : T ⟶ 𝟭 A),
      ∀ M : A, Epi (π.app M) ∧
        ∃ (I : Type u)
        (G : I → SheafOfModules.{u} (moduleRings Y.toRingedSpace)),
        Nonempty ((T.obj M) ≅ ∐ G) ∧
        (∀ j : I, SheafOfModules.IsFlat (G j)) ∧
        ∀ (j : I) (K : Type u)
          (H : K → SheafOfModules.{u} (moduleRings Y.toRingedSpace))
          (f : G j ⟶ ∐ H),
          ∃ (S : Finset K) (g : G j ⟶ ∐ (fun k : {k // k ∈ S} ↦ H k.1)),
            g ≫ Sigma.desc (fun k : {k // k ∈ S} ↦ Sigma.ι H k.1) = f := by
  refine ⟨affineGeneratorCover Y, affineCoverAugmentation Y, fun M ↦ ?_⟩
  refine ⟨affineCover_epi Y M ((affineCoverAugmentation Y).app M) ?_, ?_⟩
  · intro x
    change Sigma.ι _ x ≫ Sigma.desc _ = _
    exact Sigma.ι_desc _ _
  · refine ⟨(Σ U : Y.affineOpens, M.val.obj (op U.1)),
      (fun x ↦ affineGenerator Y x.1.1), ⟨Iso.refl _⟩, ?_, ?_⟩
    · intro x
      exact affineGenerator_flat Y x.1.1
    · intro x K H f
      exact affineGenerator_compact Y x.1 K H f

end AlgebraicGeometry
```

### Sheaf.AlgebraicGeometry.CompactFlatGeneratorRelativeExtension

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.AlgebraicGeometry.FlatTelescopeStageMap
import Sheaf.AlgebraicGeometry.CompactFlatGeneratorCover
import Sheaf.Algebra.Homology.RelativeBiprodConeExtension
import Sheaf.Algebra.Homology.CyclePullbackResolution
import Mathlib.Algebra.Homology.Refinements

/-! # One relative compact flat generator resolution step

Source: Stacks Project Tags 03EW, 077J and the cone induction in Tag 06XX.
(blueprint: lem-sc-compact-flat-generator-relative-extension).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private abbrev GeneratorSum (Y : Scheme.{u})
    (M : SheafOfModules.{u} (moduleRings Y.toRingedSpace)) : Prop :=
  ∃ (I : Type u)
        (G : I → SheafOfModules.{u} (moduleRings Y.toRingedSpace)),
        Nonempty (M ≅ ∐ G) ∧
        (∀ j : I, SheafOfModules.IsFlat (G j)) ∧
        ∀ (j : I) (K : Type u)
          (H : K → SheafOfModules.{u} (moduleRings Y.toRingedSpace))
          (f : G j ⟶ ∐ H),
          ∃ (S : Finset K) (g : G j ⟶ ∐ (fun k : {k // k ∈ S} ↦ H k.1)),
            g ≫ Sigma.desc (fun k : {k // k ∈ S} ↦ Sigma.ι H k.1) = f

private theorem generatorSum_biprod (Y : Scheme.{u})
    (M N : SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    (hM : GeneratorSum Y M) (hN : GeneratorSum Y N) :
    GeneratorSum Y (M ⊞ N) := by
  classical
  obtain ⟨I, G, ⟨eM⟩, hG, hcG⟩ := hM
  obtain ⟨J, H, ⟨eN⟩, hH, hcH⟩ := hN
  let K : I ⊕ J → SheafOfModules.{u} (moduleRings Y.toRingedSpace) := Sum.elim G H
  let e : (∐ G) ⊞ (∐ H) ≅ ∐ K :=
    { hom := biprod.desc (Sigma.desc (fun i ↦ Sigma.ι K (.inl i)))
        (Sigma.desc (fun j ↦ Sigma.ι K (.inr j)))
      inv := Sigma.desc (fun k ↦ match k with
        | .inl i => Sigma.ι G i ≫ biprod.inl
        | .inr j => Sigma.ι H j ≫ biprod.inr)
      hom_inv_id := by
        apply biprod.hom_ext'
        all_goals apply Sigma.hom_ext; intro i; simp [K]
      inv_hom_id := by
        apply Sigma.hom_ext
        intro i
        cases i <;> simp [K, Category.assoc] }
  refine ⟨I ⊕ J, K, ⟨biprod.mapIso eM eN ≪≫ e⟩, ?_, ?_⟩
  · intro i
    cases i with
    | inl i => exact hG i
    | inr j => exact hH j
  · intro i
    cases i with
    | inl i => exact hcG i
    | inr j => exact hcH j

/-- Extend a bounded-above generator complex along an arbitrary map into a
bounded-above complex, keeping its inclusion split in each degree.

Source: Stacks Project Tag 06XX, the induction step before the final
termwise-surjectivity addition; Tags 03EW and 077J supply generator resolutions.
This is the finite extension in the first paragraph of the original proof of
`lem-sc-flat-telescope-target-refinement`.

Proof. Use the affine-open sheaves j_! O_U. Their stalks are either zero or the
local ring, so they are flat. Adjunction identifies maps from them with sections
on U. A section of a sheaf coproduct locally comes from a finite subsum; an affine
open is quasi-compact, so finitely many such neighborhoods suffice. The union of
their finite supports gives the required factorization, with uniqueness and
gluing supplied by the monic inclusion of a subsum. Every module sheaf is covered
by a sum of these sheaves: for every local section choose an affine neighborhood
and its corresponding adjunction map. Resolve the bounded-above mapping cone of
a by these generators, downward from its upper bound, choosing generator covers
of the successive pullbacks of cycles as in the bounded resolution construction
underlying 077J. This gives a bounded-above complex Q and a quasi-isomorphism
Q -> Cone(a). Compose with Cone(a) -> L[1]. Its shifted cone gives L', with the
termwise split inclusion L -> L' and terms the direct sums of terms of L and Q.
The triangle comparison gives L' -> E. Its composite with L -> L' equals a up to
homotopy. Extend the comparison homotopy degreewise along the split inclusion,
and subtract its boundary; this makes the equality strict without changing the
homotopy class. The map is a quasi-isomorphism by comparison of the two triangles,
since the other vertical maps are the identity of L and Q -> Cone(a).
Finite direct sums of generator coproducts are reindexed by disjoint union, so
all terms of L' have the required generator description. The maximum of the
bounds, with the shift accounted for, bounds L'. There is no assumption on a:
a zero map, a zero target, and an acyclic target are covered by the same argument.
Empty coproducts represent zero terms. No projective lifting is used.
(blueprint: lem-sc-compact-flat-generator-relative-extension). -/
theorem exists_compact_flat_generator_relative_extension (Y : Scheme.{u})
    (L E : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (a : L ⟶ E)
    (hL : ∃ z : ℤ, ∀ i : ℤ, z < i → IsZero (L.X i))
    (hE : ∃ z : ℤ, ∀ i : ℤ, z < i → IsZero (E.X i))
    (hgen : ∀ i : ℤ, ∃ (I : Type u)
        (G : I → SheafOfModules.{u} (moduleRings Y.toRingedSpace)),
        Nonempty (L.X i ≅ ∐ G) ∧
        (∀ j : I, SheafOfModules.IsFlat (G j)) ∧
        ∀ (j : I) (K : Type u)
          (H : K → SheafOfModules.{u} (moduleRings Y.toRingedSpace))
          (f : G j ⟶ ∐ H),
          ∃ (S : Finset K) (g : G j ⟶ ∐ (fun k : {k // k ∈ S} ↦ H k.1)),
            g ≫ Sigma.desc (fun k : {k // k ∈ S} ↦ Sigma.ι H k.1) = f) :
    ∃ (L' : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
      (l : L ⟶ L') (v : L' ⟶ E),
      (∃ z : ℤ, ∀ i : ℤ, z < i → IsZero (L'.X i)) ∧
      QuasiIso v ∧ (l ≫ v = a) ∧ (∀ i : ℤ, IsSplitMono (l.f i)) ∧
    ∀ i : ℤ, ∃ (I : Type u)
        (G : I → SheafOfModules.{u} (moduleRings Y.toRingedSpace)),
        Nonempty (L'.X i ≅ ∐ G) ∧
        (∀ j : I, SheafOfModules.IsFlat (G j)) ∧
        ∀ (j : I) (K : Type u)
          (H : K → SheafOfModules.{u} (moduleRings Y.toRingedSpace))
          (f : G j ⟶ ∐ H),
          ∃ (S : Finset K) (g : G j ⟶ ∐ (fun k : {k // k ∈ S} ↦ H k.1)),
            g ≫ Sigma.desc (fun k : {k // k ∈ S} ↦ Sigma.ι H k.1) = f := by
  classical
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let S : ObjectProperty A := GeneratorSum Y
  have hzero (M : A) (hM : IsZero M) : S M := by
    let G : PEmpty.{u + 1} → A := PEmpty.elim
    have hG : IsZero (∐ G) := by
      rw [IsZero.iff_id_eq_zero]
      apply Sigma.hom_ext
      intro j
      exact PEmpty.elim j
    exact ⟨PEmpty.{u + 1}, G, ⟨hM.iso hG⟩, fun j ↦ PEmpty.elim j,
      fun j ↦ PEmpty.elim j⟩
  obtain ⟨T, π, hT⟩ := exists_functorial_compact_flat_generator_cover Y
  obtain ⟨bL, hbL⟩ := hL
  obtain ⟨bE, hbE⟩ := hE
  let N := max bL bE
  have hc : ∀ i : ℤ, N < i → IsZero ((CochainComplex.mappingCone a).X i) := by
    intro i hi
    apply (CochainComplex.mappingCone.isZero_X_iff a i).2
    exact ⟨hbL (i + 1) (by dsimp [N] at hi; omega),
      hbE i (by dsimp [N] at hi; omega)⟩
  let P : ObjectProperty (CochainComplex A ℤ) :=
    fun F ↦ ∀ i : ℤ, N < i → IsZero (F.X i)
  let F : P.FullSubcategory := ⟨CochainComplex.mappingCone a, hc⟩
  obtain ⟨Q, ε, hQ⟩ := CochainComplex.exists_functorial_cyclePullback_construction
    S hzero T π (fun M ↦ (hT M).2) (fun M ↦ (hT M).1) N
  have hr : QuasiIso (ε.app F) := by
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap, isIso_iff_mono_and_epi]
    constructor
    · rw [HomologicalComplex.mono_homologyMap_iff_up_to_refinements
        (ε.app F) (i - 1) i (i + 1) (by simp) (by simp)]
      intro B x hx y hy
      have hlift := (hQ F).2.2 (i - 1)
      rw [show i - 1 + 1 = i by omega] at hlift
      obtain ⟨B', p, hp, z, _, hz⟩ := hlift B x y hx hy
      exact ⟨B', p, hp, z, by simpa using hz.symm⟩
    · rw [HomologicalComplex.epi_homologyMap_iff_up_to_refinements
        (ε.app F) (i - 1) i (i + 1) (by simp) (by simp)]
      intro B y hy
      obtain ⟨B', p, hp, z, hz, hd⟩ :=
        (hQ F).2.2 i B 0 y (by simp) (by simpa using hy.symm)
      exact ⟨B', p, hp, z, by simpa using hd, 0, by simpa using hz.symm⟩
  obtain ⟨L', l, v, hb, hv, hlv, hs, ht⟩ :=
    CochainComplex.exists_relative_biprod_cone_extension L E a ⟨bL, hbL⟩
      (Q.obj F) (ε.app F) ⟨N, (hQ F).2.1⟩ hr
  refine ⟨L', l, v, hb, hv, hlv, hs, ?_⟩
  intro i
  obtain ⟨e⟩ := ht i
  obtain ⟨I, G, ⟨eG⟩, hg, hcompact⟩ :=
    generatorSum_biprod Y (L.X i) ((Q.obj F).X i) (hgen i) ((hQ F).1 i)
  exact ⟨I, G, ⟨e ≪≫ eG⟩, hg, hcompact⟩

end AlgebraicGeometry
```

### Sheaf.AlgebraicGeometry.CompactFlatGeneratorTowerResolution

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.FlatTelescopeStageMap
import Sheaf.AlgebraicGeometry.CompactFlatGeneratorRelativeExtension

/-! # Split towers resolved by compact flat generators

Source: Stacks Project 03EW, 077J and the relative cone induction of 06XX,
as expanded in the first paragraph of the one-target refinement argument.
(blueprint: lem-sc-compact-flat-generator-tower-resolution).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex
namespace AlgebraicGeometry

/-- A bounded-above tower admits a strict levelwise quasi-isomorphic resolution
by coproducts of compact flat generators, with degreewise split transitions.
Compactness here is explicitly finite support for maps into arbitrary coproducts.

Source: Stacks Project 03EW and 077J; relative cone induction of 06XX,
expanded in `lem-sc-flat-telescope-target-refinement`, first proof paragraph.

Proof. Use the affine-open extension-by-zero generators j_! O_U. They are flat;
their Hom functor is sections on U. Quasi-compactness of U makes a section of a
sheaf coproduct finitely supported, giving exactly the finite-subcoproduct
factorization in the conclusion. Arbitrary module sheaves are covered by sums
of these generators. Resolve L_0 -> E_0 downward with that resolving class.
Given L_n -> E_n, resolve the bounded-above cone of L_n -> E_(n+1) by Q.
Compose Q -> Cone -> L_n[1] and take its shifted cone to obtain L_(n+1).
Its terms are sums of the old generators and the generators of Q; the map from
L_n is degreewise split. The comparison triangle gives v_(n+1), initially
commuting up to homotopy. Extend the comparison homotopy along each degreewise
split inclusion and subtract its boundary to get strict commutation. The
comparison of triangles makes v_(n+1) a quasi-isomorphism. Each stage has an
upper bound, with no uniform bound required. Empty coproducts handle zero terms;
zero complexes and arbitrary transitions need no exceptions. This construction
uses no projectivity or lifting through a sheaf epimorphism.
(blueprint: lem-sc-compact-flat-generator-tower-resolution). -/
theorem exists_compact_flat_generator_tower_resolution (Y : Scheme.{u})
    (E : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (t : ∀ n : ℕ, E n ⟶ E (n + 1))
    (hb : ∀ n : ℕ, ∃ z : ℤ, ∀ i : ℤ, z < i → IsZero ((E n).X i)) :
    ∃ (L : ℕ → CochainComplex
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
      (l : ∀ n : ℕ, L n ⟶ L (n + 1)) (v : ∀ n : ℕ, L n ⟶ E n),
      (∀ n : ℕ, ∃ z : ℤ, ∀ i : ℤ, z < i → IsZero ((L n).X i)) ∧
      (∀ n : ℕ, QuasiIso (v n)) ∧
      (∀ n : ℕ, l n ≫ v (n + 1) = v n ≫ t n) ∧
      (∀ (n : ℕ) (i : ℤ), IsSplitMono ((l n).f i)) ∧
      ∀ (n : ℕ) (i : ℤ), ∃ (I : Type u)
        (G : I → SheafOfModules.{u} (moduleRings Y.toRingedSpace)),
        Nonempty ((L n).X i ≅ ∐ G) ∧
        (∀ j : I, SheafOfModules.IsFlat (G j)) ∧
        ∀ (j : I) (K : Type u)
          (H : K → SheafOfModules.{u} (moduleRings Y.toRingedSpace))
          (f : G j ⟶ ∐ H),
          ∃ (S : Finset K) (g : G j ⟶ ∐ (fun k : {k // k ∈ S} ↦ H k.1)),
            g ≫ Sigma.desc (fun k : {k // k ∈ S} ↦ Sigma.ι H k.1) = f := by
  classical
  open ZeroObject in
  let C := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let Good (L : CochainComplex C ℤ) : Prop :=
    ∀ i : ℤ, ∃ (I : Type u)
        (G : I → SheafOfModules.{u} (moduleRings Y.toRingedSpace)),
        Nonempty (L.X i ≅ ∐ G) ∧
        (∀ j : I, SheafOfModules.IsFlat (G j)) ∧
        ∀ (j : I) (K : Type u)
          (H : K → SheafOfModules.{u} (moduleRings Y.toRingedSpace))
          (f : G j ⟶ ∐ H),
          ∃ (S : Finset K) (g : G j ⟶ ∐ (fun k : {k // k ∈ S} ↦ H k.1)),
            g ≫ Sigma.desc (fun k : {k // k ∈ S} ↦ Sigma.ι H k.1) = f
  have hzero : Good (HomologicalComplex.zero : CochainComplex C ℤ) := by
    intro i
    let G : PEmpty.{u + 1} → C := PEmpty.elim
    have hG : IsZero (∐ G) := by
      rw [IsZero.iff_id_eq_zero]
      apply Sigma.hom_ext
      intro j
      exact PEmpty.elim j
    refine ⟨PEmpty.{u + 1}, G, ?_, ?_, ?_⟩
    · exact ⟨(isZero_zero C).iso hG⟩
    · intro j
      exact PEmpty.elim j
    · intro j
      exact PEmpty.elim j
  have hbzero : ∃ z : ℤ, ∀ i : ℤ, z < i →
      IsZero ((HomologicalComplex.zero : CochainComplex C ℤ).X i) :=
    ⟨0, fun _ _ ↦ isZero_zero C⟩
  let State (n : ℕ) := Σ L : CochainComplex C ℤ,
    {v : L ⟶ E n //
      (∃ z : ℤ, ∀ i : ℤ, z < i → IsZero (L.X i)) ∧ QuasiIso v ∧ Good L}
  obtain ⟨L₀, _, v₀, hb₀, hv₀, _, _, hg₀⟩ :=
    exists_compact_flat_generator_relative_extension Y HomologicalComplex.zero (E 0) 0
      hbzero (hb 0) hzero
  let s₀ : State 0 := ⟨L₀, v₀, hb₀, hv₀, hg₀⟩
  have step (n : ℕ) (s : State n) :
      ∃ s' : State (n + 1), ∃ l : s.1 ⟶ s'.1,
        l ≫ s'.2.val = s.2.val ≫ t n ∧ ∀ i : ℤ, IsSplitMono (l.f i) := by
    obtain ⟨L', l, v, hb', hv, hc, hs, hg⟩ :=
      exists_compact_flat_generator_relative_extension Y s.1 (E (n + 1))
        (s.2.val ≫ t n) s.2.property.1 (hb (n + 1)) s.2.property.2.2
    exact ⟨⟨L', v, hb', hv, hg⟩, l, hc, hs⟩
  choose next transition comm split using step
  let s : ∀ n : ℕ, State n := Nat.rec s₀ (fun n sn ↦ next n sn)
  refine ⟨(fun n ↦ (s n).1), (fun n ↦ transition n (s n)),
    (fun n ↦ (s n).2.val), ?_, ?_, ?_, ?_, ?_⟩
  · exact fun n ↦ (s n).2.property.1
  · exact fun n ↦ (s n).2.property.2.1
  · exact fun n ↦ comm n (s n)
  · exact fun n ↦ split n (s n)
  · exact fun n ↦ (s n).2.property.2.2

end AlgebraicGeometry
```

### Sheaf.AlgebraicGeometry.CompactFlatTelescopeBarEnlargement

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.FlatTelescopeStageMap
import Sheaf.AlgebraicGeometry.CompactFlatBarUnionAugmentation

/-! # Bar enlargement of a split compact-generator tower

Source: finite-piece and target-chain bar argument in
`lem-sc-flat-telescope-target-refinement`, following the generator resolution.
(blueprint: lem-sc-compact-flat-telescope-bar-enlargement).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex
namespace AlgebraicGeometry


-- The finite recurrence of FilteredFreeTelescopeSplitting, used for sheaves as well.
private theorem sequential_sum_retraction {C : Type*} [Category C] [Preadditive C]
    (F : ℕ → C) (D : C) (j : ∀ n, F n ⟶ D)
    (hD : IsColimit (Cofan.mk D j)) (step : ∀ n, F n ⟶ F (n + 1))
    (d : D ⟶ D) (hd : ∀ n, j n ≫ d = j n - step n ≫ j (n + 1))
    (hsplit : ∀ n, ∃ r : F (n + 1) ⟶ F n, step n ≫ r = 𝟙 (F n)) :
    ∃ r : D ⟶ D, d ≫ r = 𝟙 D := by
  classical
  choose r hr using hsplit
  let t : ∀ n, F n ⟶ D := fun n ↦
    Nat.rec (motive := fun n ↦ F n ⟶ D) 0 (fun n t ↦ r n ≫ (t - j n)) n
  let b : D ⟶ D := Cofan.IsColimit.desc hD t
  refine ⟨b, Cofan.IsColimit.hom_ext hD _ _ (fun n ↦ ?_)⟩
  change j n ≫ (d ≫ b) = j n ≫ 𝟙 D
  rw [← Category.assoc, hd, Preadditive.sub_comp, Category.assoc]
  rw [show j n ≫ b = t n from Cofan.IsColimit.fac hD t n,
    show j (n + 1) ≫ b = t (n + 1) from Cofan.IsColimit.fac hD t (n + 1)]
  simp only [Category.comp_id]
  change t n - step n ≫ (r n ≫ (t n - j n)) = j n
  rw [← Category.assoc, hr, Category.id_comp]
  exact sub_sub_cancel _ _

private theorem split_telescope_cokernel (Y : Scheme.{u})
    (F : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (u : ∀ n : ℕ, F n ⟶ F (n + 1))
    (hsplit : ∀ (n : ℕ) (i : ℤ), IsSplitMono ((u n).f i)) :
    ∀ i : ℤ, Nonempty
      (((ShortComplex.mk (flatTelescopeDifferential F u)
        (cokernel.π (flatTelescopeDifferential F u))
        (cokernel.condition (flatTelescopeDifferential F u))).map
          (HomologicalComplex.eval _ (ComplexShape.up ℤ) i)).Splitting) := by
  intro i
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let ev := HomologicalComplex.eval A (ComplexShape.up ℤ) i
  let d := flatTelescopeDifferential F u
  let S := ShortComplex.mk d (cokernel.π d) (cokernel.condition d)
  let G : ℕ → A := fun n ↦ (F n).X i
  let D := (∐ F).X i
  let j : ∀ n, G n ⟶ D := fun n ↦ (Sigma.ι F n).f i
  have hD : IsColimit (Cofan.mk D j) :=
    (Cofan.isColimitMapCoconeEquiv ev F (Cofan.mk _ (Sigma.ι F)))
      (isColimitOfPreserves ev (coproductIsCoproduct F))
  have hd (n : ℕ) : j n ≫ d.f i = j n - (u n).f i ≫ j (n + 1) := by
    have h : Sigma.ι F n ≫ d = Sigma.ι F n - u n ≫ Sigma.ι F (n + 1) := by
      simp [d, flatTelescopeDifferential, Preadditive.comp_sub]
    exact congrArg (fun f ↦ f.f i) h
  have hr (n : ℕ) : ∃ r : G (n + 1) ⟶ G n, (u n).f i ≫ r = 𝟙 (G n) := by
    have := hsplit n i
    exact ⟨retraction ((u n).f i), IsSplitMono.id ((u n).f i)⟩
  obtain ⟨r, hdr⟩ := sequential_sum_retraction G D j hD
    (fun n ↦ (u n).f i) (d.f i) hd hr
  have hS : S.Exact := S.exact_of_g_is_cokernel (cokernelIsCokernel d)
  have hSev : (S.map ev).Exact := hS.map_of_epi_of_preservesCokernel ev
    (by dsimp [S]; infer_instance) (by infer_instance)
  have hg : Epi (S.map ev).g := by
    change Epi (ev.map (cokernel.π d))
    exact epi_of_isColimit_cofork
      (CokernelCofork.mapIsColimit _ (cokernelIsCokernel d) ev)
  exact ⟨ShortComplex.Splitting.ofExactOfRetraction (S.map ev) hSev r hdr hg⟩

/-- A split bounded-above compact-generator tower augmented into a flat telescope
admits a flat bar refinement and a split presentation of its enlarged bar total.
The input has the compact-generator structure needed for the finite-piece argument;
no resolution of a general input tower is asserted here.

Source: `lem-sc-flat-telescope-target-refinement`, proof from "Close finite sets"
through the final augmentation identity; the agent-written finite-piece bar argument
of `lem-sc-flat-telescope-arrow-bar-data`.

Proof. Fix generator decompositions in each term. Starting with finitely many
summands in finitely many degrees, close under the differential upwards: each
summand maps through finitely many next-degree summands by hgen. The upper bound
ends the procedure, producing finite subcomplexes. Keep stage-labelled copies of
these subcomplexes for stages at most n, with an arrow when the transition carries
one into the other. A finite subcomplex at an earlier stage maps into a finite
subcomplex at stage n: factor its finitely many generator terms through finite
subcoproducts, then close under the differential. Thus the stage-n subdiagram is
cofinal in this filtered diagram D_n, whose colimit is L_n. No compatibility of
generator decompositions across stages is required, and sums of images are never
assumed flat. Each diagram object retains its finite generator terms.
The unnormalized bar total
R_n of D_n is bounded above and flat; its augmentation c_n is a quasi-isomorphism
by exactness of filtered colimits of module sheaves. Simplicial degree p has
cochain degree -p; the common upper bound for the finite initial tower segment
makes the associated total-complex argument legitimate. Inclusions give s_n.

Write T as the supplied telescope and take finite cone blocks C_k, using domain
indices at most k and codomain indices at most k+1. They are bounded above and
flat, with split inclusions and union T. Each finite source subcomplex maps through
some C_k by finite support in each of its finitely many degrees. Monicity into T
makes that factor a chain map. Adjoin the target chain to the union of D_n, with
arrows from a source object to every block through which it factors. The least
factorization index is monotone and left adjoint to the target-chain inclusion.
Inserting the adjunction unit in bar strings, with alternating signs, gives a
homotopy equivalence from the enlarged bar total to the target-chain bar total.

Let F_n be the bar total on D_n and target indices at most n. Bar inclusions give
u and a, and satisfy the two transition identities strictly. The union bar total
has the degreewise split exact presentation by 1-shift on the sum of F_n: a
simplex's first stage splits the augmentation, and the finite-support recurrence
identifies its kernel. This gives exactly the displayed degreewise splittings; the cone calculation
is left to the caller. Compare the target-chain bar resolution of the augmented constant
right functor with its two-term representable resolution by 1-shift. Successive
projective lifts give maps and homotopies lifting the identity of that functor;
tensor with C_k. Every homotopy is finite on each input, so totalization is valid.
The finite-block telescope maps homotopy equivalently to T by the same split
exact-sequence cone calculation. Cancel the target-chain bar equivalence to see
that the enlarged bar augmentation into T is a homotopy equivalence.
Use that canonical bar augmentation as e, and the sum of stage inclusions
as b. The finite-support recurrence gives hzero and the splittings. Naturality
with a gives the displayed sum identity. Include the zero subcomplex to handle empty
source diagrams. Every construction is existential, not a choice in a definition.
(blueprint: lem-sc-compact-flat-telescope-bar-enlargement). -/
theorem exists_compact_flat_telescope_bar_enlargement (Y : Scheme.{u})
    (L : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (l : ∀ n : ℕ, L n ⟶ L (n + 1))
    (hb : ∀ n : ℕ, ∃ z : ℤ, ∀ i : ℤ, z < i → IsZero ((L n).X i))
    (hsplit : ∀ (n : ℕ) (i : ℤ), IsSplitMono ((l n).f i))
    (hgen :
      ∀ (n : ℕ) (i : ℤ), ∃ (I : Type u)
        (G : I → SheafOfModules.{u} (moduleRings Y.toRingedSpace)),
        Nonempty ((L n).X i ≅ ∐ G) ∧
        (∀ j : I, SheafOfModules.IsFlat (G j)) ∧
        ∀ (j : I) (K : Type u)
          (H : K → SheafOfModules.{u} (moduleRings Y.toRingedSpace))
          (f : G j ⟶ ∐ H),
          ∃ (S : Finset K) (g : G j ⟶ ∐ (fun k : {k // k ∈ S} ↦ H k.1)),
            g ≫ Sigma.desc (fun k : {k // k ∈ S} ↦ Sigma.ι H k.1) = f)
    (T : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hT : isFlatTelescope Y T) (p : ∀ n : ℕ, L n ⟶ T)
    (hp : ∀ n : ℕ, l n ≫ p (n + 1) = p n) :
    let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
    let Q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
    ∃ (R F : ℕ → CochainComplex A ℤ)
      (s : ∀ n : ℕ, R n ⟶ R (n + 1))
      (u : ∀ n : ℕ, F n ⟶ F (n + 1))
      (c : ∀ n : ℕ, R n ⟶ L n) (a : ∀ n : ℕ, R n ⟶ F n),
      (∀ n : ℕ, ∃ z : ℤ, ∀ i : ℤ, z < i → IsZero ((R n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((R n).X i)) ∧
      (∀ n : ℕ, ∃ z : ℤ, ∀ i : ℤ, z < i → IsZero ((F n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((F n).X i)) ∧
      (∀ n : ℕ, QuasiIso (c n)) ∧
      (∀ n : ℕ, s n ≫ c (n + 1) = c n ≫ l n) ∧
      (∀ n : ℕ, s n ≫ a (n + 1) = a n ≫ u n) ∧
      ∃ (B : CochainComplex A ℤ) (b : (∐ F) ⟶ B) (e : B ⟶ T)
        (hzero : flatTelescopeDifferential F u ≫ b = 0),
        (∀ i : ℤ, Nonempty
          (((ShortComplex.mk (flatTelescopeDifferential F u) b hzero).map
            (HomologicalComplex.eval A (ComplexShape.up ℤ) i)).Splitting)) ∧
        IsIso (Q.map e) ∧
        Limits.Sigma.map a ≫ b ≫ e = Sigma.desc (fun n : ℕ ↦ c n ≫ p n) := by
  obtain ⟨D⟩ := exists_compact_flat_finite_subcomplex_diagrams Y L l hb hsplit hgen
  obtain ⟨R, F, s, u, c, a, hbR, hfR, hbF, hfF, hc, hs, ha, hu, q, hq, haq, he⟩ :=
    exists_compact_flat_bar_union_augmentation Y L l D T hT p hp
  let d := flatTelescopeDifferential F u
  have hzero : d ≫ Sigma.desc q = 0 := by
    apply Sigma.hom_ext
    intro n
    simp [d, flatTelescopeDifferential, Preadditive.comp_sub, Preadditive.sub_comp,
      Category.assoc, hq]
  let e := cokernel.desc d (Sigma.desc q) hzero
  refine ⟨R, F, s, u, c, a, hbR, hfR, hbF, hfF, hc, hs, ha,
    cokernel d, cokernel.π d, e, cokernel.condition d,
    split_telescope_cokernel Y F u hu, he hzero, ?_⟩
  dsimp [e]
  rw [cokernel.π_desc]
  apply Sigma.hom_ext
  intro n
  simp only [Sigma.ι_map_assoc, Sigma.ι_desc, haq]


end AlgebraicGeometry
```

### Sheaf.AlgebraicGeometry.DerivedPullbackKFlatCounitAdjustmentFactor

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
import Sheaf.Algebra.Homology.KFlatResolution

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 800000 in
-- The two universal lifts elaborate through the recorded derived-pullback witness.
/-- Two K-flat counits differ by a natural automorphism of their common source.
No monoidal, properness, or Noetherian hypothesis is needed for this comparison.

Source: Stacks Project, Tag 06YJ, computation on K-flat resolutions, and the
right Kan extension universal property recorded by `exists_derivedPullback`.

Proof. Let δ be the recorded universal counit. The universal property gives lifts
`t₀` and `t` of the two supplied counits to endomorphisms of derived pullback,
with `Qh(t₀) ≫ δ = ε₀` and `Qh(t) ≫ δ = ε`. On a K-flat representative P,
δ, ε₀ and ε are invertible, so these equations show that both lifts are invertible
at Qh(P). Every derived object is isomorphic to the localization of a K-flat
representative: take a complex representative and then a K-flat resolution.
Naturality transports invertibility along these isomorphisms. Thus both lifts
are natural isomorphisms. Whisker `t ≫ t₀⁻¹` with Qh to obtain a. Its composite
with ε₀ is ε by the two universal-property equations and inverse cancellation.
Identity and zero resolutions satisfy the same cancellation equations; neither
an empty scheme nor a zero object requires a separate choice.
(blueprint: lem-sc-derived-pullback-kflat-counit-shift-adjustment-factor). -/
theorem exists_derivedPullback_kFlat_counit_adjustment_factor
    {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [(Scheme.Modules.tensorPullback f).Additive]
    (ε₀ : DerivedCategory.Qh ⋙ derivedPullback f ⟶
      (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (DerivedCategory.Qh : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
          schemeDerivedCategory Z))
    (hε₀ : ∀ P : CochainComplex
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
      CochainComplex.IsKFlat (R := Y.sheaf) P →
      IsIso (ε₀.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)))
    (ε : DerivedCategory.Qh ⋙ derivedPullback f ⟶
      (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (DerivedCategory.Qh : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
          schemeDerivedCategory Z))
    (hε : ∀ P : CochainComplex
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
      CochainComplex.IsKFlat (R := Y.sheaf) P →
      IsIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))) :
    ∃ a : (DerivedCategory.Qh ⋙ derivedPullback f) ≅
          (DerivedCategory.Qh ⋙ derivedPullback f), a.hom ≫ ε₀ = ε
:= by
  classical
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  let Q := DerivedCategory.Qh (C := A)
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  obtain ⟨_, _, _, _, _, _, _, E, hE, hEmap, hEadd, δ, hδ, _, hK⟩ :=
    Classical.choose_spec (exists_derivedPullback f)
  have hE' : E = Scheme.Modules.tensorPullback f :=
    CategoryTheory.Functor.ext hE (fun M N a ↦ hEmap a)
  subst E
  have : (derivedPullback f).IsLeftDerivedFunctor δ W := hδ
  have hlift : ∀ (β : Q ⋙ derivedPullback f ⟶
      (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (DerivedCategory.Qh : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
            schemeDerivedCategory Z)),
      (∀ P : CochainComplex A ℤ, CochainComplex.IsKFlat (R := Y.sheaf) P →
        IsIso (β.app (q.obj P))) →
      IsIso ((derivedPullback f).leftDerivedLift δ W (derivedPullback f) β) := by
    intro β hβ
    let t := (derivedPullback f).leftDerivedLift δ W (derivedPullback f) β
    apply NatTrans.isIso_iff_isIso_app t |>.2
    intro X
    rw [← NatTrans.isIso_app_iff_of_iso t (Q.objObjPreimageIso X)]
    obtain ⟨G, hG⟩ := HomotopyCategory.quotient_obj_surjective (Q.objPreimage X)
    rw [← hG]
    obtain ⟨P, s, hP, _, hs, _⟩ := CochainComplex.exists_isKFlatResolution (R := Y.sheaf) G
    have hqs : W (q.map s) := (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs
    have : IsIso (Q.map (q.map s)) := Localization.inverts Q W _ hqs
    rw [← NatTrans.isIso_app_iff_of_iso t (asIso (Q.map (q.map s)))]
    have : IsIso (δ.app (q.obj P)) := hK P hP
    have : IsIso (β.app (q.obj P)) := hβ P hP
    have hfac : t.app (Q.obj (q.obj P)) ≫ δ.app (q.obj P) = β.app (q.obj P) :=
      (derivedPullback f).leftDerived_fac_app δ W (derivedPullback f) β (q.obj P)
    have : IsIso (t.app (Q.obj (q.obj P)) ≫ δ.app (q.obj P)) := by
      rw [hfac]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (δ.app (q.obj P))
  let t₀ := (derivedPullback f).leftDerivedLift δ W (derivedPullback f) ε₀
  let t := (derivedPullback f).leftDerivedLift δ W (derivedPullback f) ε
  have : IsIso t₀ := hlift ε₀ hε₀
  have : IsIso t := hlift ε hε
  let a := Functor.isoWhiskerLeft Q (asIso t ≪≫ (asIso t₀).symm)
  refine ⟨a, ?_⟩
  ext X
  change (t.app (Q.obj X) ≫ (inv t₀).app (Q.obj X)) ≫ ε₀.app X = ε.app X
  rw [← (derivedPullback f).leftDerived_fac_app δ W (derivedPullback f) ε₀ X]
  change (t.app (Q.obj X) ≫ (inv t₀).app (Q.obj X)) ≫
    t₀.app (Q.obj X) ≫ δ.app X = ε.app X
  rw [Category.assoc, ← Category.assoc ((inv t₀).app _) (t₀.app _) (δ.app X),
    ← NatTrans.comp_app, IsIso.inv_hom_id, NatTrans.id_app, Category.id_comp]
  exact (derivedPullback f).leftDerived_fac_app δ W (derivedPullback f) ε X

end AlgebraicGeometry
```

### Sheaf.AlgebraicGeometry.FlatComparisonPreservesCountableCoproducts

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Sheaf.AlgebraicGeometry.DerivedAmbientDirectSumsCofan
import Sheaf.AlgebraicGeometry.DerivedAdjoint
import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
import all Sheaf.CategoryTheory.DerivedModuleDirectSums

/-! # Countable coproduct preservation for the two flat comparison functors

Source: step 3 of lem-sc-flat-telescope-sum-comparison-is-iso; Stacks Tags
07D9 and 079W. (blueprint: lem-sc-flat-comparison-preserves-countable-coproducts).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private noncomputable def quotient_coproduct_cofan
    {C : Type*} [Category C] [Preadditive C] {I : Type*}
    [HasColimitsOfShape (Discrete I) C] (K : I → CochainComplex C ℤ) :
    IsColimit (Cofan.mk ((HomotopyCategory.quotient C (.up ℤ)).obj (∐ K))
      (fun i ↦ (HomotopyCategory.quotient C (.up ℤ)).map (Sigma.ι K i))) := by
  classical
  let q := HomotopyCategory.quotient C (.up ℤ)
  have hu (X : HomotopyCategory C (.up ℤ)) (a : ∀ i, q.obj (K i) ⟶ X) :
      ∃! d : q.obj (∐ K) ⟶ X, ∀ i, q.map (Sigma.ι K i) ≫ d = a i := by
    obtain ⟨J, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    choose f hf using fun i ↦ q.map_surjective (a i)
    refine ⟨q.map (Sigma.desc f), ?_, ?_⟩
    · intro i
      rw [← Functor.map_comp, Sigma.ι_desc, hf]
    · intro m hm
      obtain ⟨g, rfl⟩ := q.map_surjective m
      have h (i : I) : Homotopy (Sigma.ι K i ≫ g) (Sigma.ι K i ≫ Sigma.desc f) :=
        HomotopyCategory.homotopyOfEq _ _ (by
          rw [Sigma.ι_desc, Functor.map_comp, hm, hf])
      exact HomotopyCategory.eq_of_homotopy _ _
        (CategoryTheory.coproduct_homotopy K g (Sigma.desc f) h).some
  exact Cofan.IsColimit.mk _ (fun t ↦ (hu t.pt t.inj).choose)
    (fun t i ↦ (hu t.pt t.inj).choose_spec.1 i)
    (fun t m hm ↦ (hu t.pt t.inj).choose_spec.2 m hm)

private theorem homotopy_preserves_coproducts_of_composite
    {C : Type*} [Category C] [Preadditive C] {I : Type*}
    [HasColimitsOfShape (Discrete I) C]
    {D : Type*} [Category D] (F : HomotopyCategory C (.up ℤ) ⥤ D)
    [PreservesColimitsOfShape (Discrete I) (HomotopyCategory.quotient C (.up ℤ) ⋙ F)] :
    PreservesColimitsOfShape (Discrete I) F := by
  classical
  let q := HomotopyCategory.quotient C (.up ℤ)
  have hp (X : I → HomotopyCategory C (.up ℤ)) :
      PreservesColimit (Discrete.functor X) F := by
    choose K hK using fun i ↦ HomotopyCategory.quotient_obj_surjective (X i)
    have hc := quotient_coproduct_cofan K
    have hm := isColimitCofanMkObjOfIsColimit (q ⋙ F) K _ (coproductIsCoproduct K)
    have : PreservesColimit (Discrete.functor (fun i ↦ q.obj (K i))) F :=
      preservesColimit_of_preserves_colimit_cocone hc
        ((Cofan.isColimitMapCoconeEquiv F _ _).symm hm)
    let e : Discrete.functor (fun i ↦ q.obj (K i)) ≅ Discrete.functor X :=
      Discrete.natIso (fun i ↦ eqToIso (hK i.as))
    exact preservesColimit_of_iso_diagram F e
  exact preservesColimitsOfShape_of_discrete F

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_Q_preserves_coproducts (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (I : Type u) :
    PreservesColimitsOfShape (Discrete I)
      (DerivedCategory.Q (C := SheafOfModules.{u} (moduleRings Y.toRingedSpace))) := by
  let Q := DerivedCategory.Q (C := SheafOfModules.{u} (moduleRings Y.toRingedSpace))
  have hp (K : I → CochainComplex
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) :
      PreservesColimit (Discrete.functor K) Q := by
    apply preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct K)
    refine (Cofan.isColimitMapCoconeEquiv Q K _).symm ?_
    change IsColimit (Cofan.mk (DerivedCategory.Q.obj (∐ K))
      (fun i ↦ DerivedCategory.Q.map (Sigma.ι K i)))
    have hc := (derivedAmbientDirectSumsCofan Y I (fun i ↦ Q.obj (K i)) K
      (fun i ↦ Iso.refl _)).some
    exact IsColimit.ofIsoColimit hc (Cofan.ext (Iso.refl _) (fun i ↦ by
      change (𝟙 _ ≫ DerivedCategory.Q.map (Sigma.ι K i)) ≫ 𝟙 _ = _
      simp only [Category.id_comp, Category.comp_id, cofan_mk_inj]))
  exact preservesColimitsOfShape_of_discrete Q

/-- Both sides of the flat comparison preserve countable homotopy coproducts.

Source: step 3 of lem-sc-flat-telescope-sum-comparison-is-iso; Stacks Tags
07D9 and 079W, and the module pullback adjunction (Tag 0096).

Proof. Represent every homotopy object by a complex. The homotopy coproduct is
represented by their termwise coproduct: maps and homotopies out of it assemble
independently on each summand. The derived ambient direct-sums cofan theorem
identifies its image under Qh as the derived coproduct, since module sheaves have
exact coproducts. Reindex by ULift to use that theorem in the scheme universe,
then transport back along the discrete equivalence. Derived pullback is a left
adjoint by the derived ringed-space adjunction and hence preserves this coproduct.
For the other functor the tensor pullback is left adjoint to module pushforward.
It preserves termwise coproducts, and its additive homotopy functor transports
the same cofan. Apply the derived ambient direct-sums cofan theorem on Z to
finish. Transport from the representative coproduct cofan to any colimit cofan
by uniqueness of colimits. This argument uses no flatness or boundedness,
no comparison family, and no properness; it also applies to zero summands.
(blueprint: lem-sc-flat-comparison-preserves-countable-coproducts). -/
theorem flat_comparison_preserves_countable_coproducts
    {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [(Scheme.Modules.tensorPullback f).Additive] :
    PreservesColimitsOfShape (Discrete ℕ) (DerivedCategory.Qh ⋙ derivedPullback f) ∧
      PreservesColimitsOfShape (Discrete ℕ)
        ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          (DerivedCategory.Qh : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
            schemeDerivedCategory Z)) := by
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let B := SheafOfModules.{u} (moduleRings Z.toRingedSpace)
  let qA := HomotopyCategory.quotient A (.up ℤ)
  let qB := HomotopyCategory.quotient B (.up ℤ)
  let QY := DerivedCategory.Q (C := A)
  let QZ := DerivedCategory.Q (C := B)
  let L := DerivedCategory.Qh ⋙ derivedPullback f
  let H : A ⥤ B := Scheme.Modules.tensorPullback f
  let G := H.mapHomotopyCategory (.up ℤ) ⋙ (DerivedCategory.Qh (C := B))
  let I := ULift.{u} ℕ
  have : PreservesColimitsOfShape (Discrete I) QY := derived_Q_preserves_coproducts Y I
  have : PreservesColimitsOfShape (Discrete I) QZ := derived_Q_preserves_coproducts Z I
  obtain ⟨adj⟩ := nonempty_derivedPullbackAdjunction f
  have : (derivedPullback f).IsLeftAdjoint := ⟨_, ⟨adj⟩⟩
  have : PreservesColimitsOfShape (Discrete I) (QY ⋙ derivedPullback f) := inferInstance
  have : PreservesColimitsOfShape (Discrete I) (qA ⋙ L) :=
    preservesColimitsOfShape_of_natIso
      ((Functor.associator qA DerivedCategory.Qh (derivedPullback f)).symm ≪≫
        Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A) (derivedPullback f)).symm
  have hL : PreservesColimitsOfShape (Discrete I) L :=
    homotopy_preserves_coproducts_of_composite L
  obtain ⟨adjH, _⟩ := Scheme.Modules.exists_tensorPullbackAdjunction f
  have : H.IsLeftAdjoint := ⟨_, ⟨adjH⟩⟩
  have : PreservesColimitsOfShape (Discrete I) (H.mapHomologicalComplex (.up ℤ) ⋙ QZ) :=
    inferInstance
  have : PreservesColimitsOfShape (Discrete I) (qA ⋙ G) :=
    preservesColimitsOfShape_of_natIso
      ((Functor.associator qA (H.mapHomotopyCategory (.up ℤ))
        (DerivedCategory.Qh (C := B))).symm ≪≫
        Functor.isoWhiskerRight (H.mapHomotopyCategoryFactors (.up ℤ))
          (DerivedCategory.Qh (C := B)) ≪≫
        Functor.associator (H.mapHomologicalComplex (.up ℤ)) qB
          (DerivedCategory.Qh (C := B)) ≪≫
        Functor.isoWhiskerLeft (H.mapHomologicalComplex (.up ℤ))
          (DerivedCategory.quotientCompQhIso B)).symm
  have hG : PreservesColimitsOfShape (Discrete I) G :=
    homotopy_preserves_coproducts_of_composite (C := A) G
  exact ⟨preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) L,
    preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) G⟩

end AlgebraicGeometry
```

### Sheaf.AlgebraicGeometry.FlatTelescopeArrowBarData

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.FlatTelescopeStageMap
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Sheaf.AlgebraicGeometry.FlatTelescopeTargetRefinement
import Sheaf.Algebra.Homology.FlatTruncationTower

/-! # Strict augmentation data from finite-piece bar diagrams

Source: Stacks Project Tags 03EW, 077J and 06XX for flat-generator resolutions;
the finite-piece and bar-enlargement argument below is an agent-written expansion
of the parent arrow-diagram construction, not a literal assertion of those tags.
(blueprint: lem-sc-flat-telescope-arrow-bar-data).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex
namespace AlgebraicGeometry

private theorem telescope_square_of_level_square {Y : Scheme.{u}}
    (E F : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (t : ∀ n : ℕ, E n ⟶ E (n + 1)) (u : ∀ n : ℕ, F n ⟶ F (n + 1))
    (a : ∀ n : ℕ, E n ⟶ F n)
    (ha : ∀ n : ℕ, t n ≫ a (n + 1) = a n ≫ u n) :
    flatTelescopeDifferential E t ≫ Limits.Sigma.map a =
      Limits.Sigma.map a ≫ flatTelescopeDifferential F u := by
  apply Sigma.hom_ext
  intro n
  simp only [flatTelescopeDifferential, Preadditive.comp_sub,
    Preadditive.sub_comp, Category.id_comp, Category.comp_id,
    Sigma.ι_map_assoc, Sigma.ι_desc_assoc, Sigma.ι_map, Category.assoc]
  rw [← Category.assoc, ha n, Category.assoc]
  simp only [Sigma.ι_desc]

/-- Tower and target-augmentation data, before constructing a source-cone map.
The target augmentations have zero shifted component and agree strictly with the
source augmentation on the two sum maps.

Source: Stacks Project 03EW, 077J and 06XX, and the finite-piece bar enlargement
isolated in `exists_flat_telescope_target_refinement`.

Proof. Choose a bounded flat truncation tower E,t,q for P. Augment it into P by
p_n = q_n followed by the truncation inclusion. Refine this tower against the first
target P. This gives a source R with level quasi-isomorphisms c_n:R_n -> E_n,
a target tower F and maps a_n:R_n -> F_n, and the required augmentation r1.
The maps c_n;p_n;f form a strictly compatible augmentation of R into Pprime.
Refine R against this second target, giving S with level quasi-isomorphisms
d_n:S_n -> R_n, a target tower G and maps b_n:S_n -> G_n, and augmentation r2.
Use S,F,G as the final three towers, d_n;a_n as the first level map, and b_n as
the second. Naturality of d implies that its sum map commutes with 1-shift;
compose that square with the first refinement's square. Put q'_n=d_n;c_n;q_n.
Quasi-isomorphisms compose, and the two naturality identities and the original
truncation compatibility give strict compatibility of q'. The two augmentation
identities follow by testing on coproduct inclusions and associating compositions.
The target augmentations and their zero shifted restrictions are unchanged.
(blueprint: lem-sc-flat-telescope-arrow-bar-data). -/
theorem exists_flat_telescope_arrow_bar_data (Y : Scheme.{u})
    (P P' : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hP : isFlatTelescope Y P) (hP' : isFlatTelescope Y P') (f : P ⟶ P') :
    let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
    let Q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
    ∃ (E₀ E₁ E₂ : ℕ → CochainComplex A ℤ)
      (t₀ : ∀ n : ℕ, E₀ n ⟶ E₀ (n + 1))
      (t₁ : ∀ n : ℕ, E₁ n ⟶ E₁ (n + 1))
      (t₂ : ∀ n : ℕ, E₂ n ⟶ E₂ (n + 1))
      (a : ∀ n : ℕ, E₀ n ⟶ E₁ n) (b : ∀ n : ℕ, E₀ n ⟶ E₂ n),
      (∀ n : ℕ, ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero ((E₀ n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E₀ n).X i)) ∧
      (∀ n : ℕ, ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero ((E₁ n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E₁ n).X i)) ∧
      (∀ n : ℕ, ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero ((E₂ n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E₂ n).X i)) ∧
      ∃ (_c₁ : flatTelescopeDifferential E₀ t₀ ≫ Limits.Sigma.map a =
          Limits.Sigma.map a ≫ flatTelescopeDifferential E₁ t₁)
        (_c₂ : flatTelescopeDifferential E₀ t₀ ≫ Limits.Sigma.map b =
          Limits.Sigma.map b ≫ flatTelescopeDifferential E₂ t₂)
        (r₁ : CochainComplex.mappingCone (flatTelescopeDifferential E₁ t₁) ⟶ P)
        (r₂ : CochainComplex.mappingCone (flatTelescopeDifferential E₂ t₂) ⟶ P')
        (q : ∀ n : ℕ, E₀ n ⟶ P.truncLE (n : ℤ)),
        IsIso (Q.map r₁) ∧ IsIso (Q.map r₂) ∧
        (∀ n : ℕ, QuasiIso (q n)) ∧
        (∀ n : ℕ, t₀ n ≫ q (n + 1) ≫ P.ιTruncLE ((n + 1 : ℕ) : ℤ) =
          q n ≫ P.ιTruncLE (n : ℤ)) ∧
        (CochainComplex.mappingCone.inl (flatTelescopeDifferential E₁ t₁)).comp
          (Cochain.ofHom r₁) (add_zero _) = 0 ∧
        (CochainComplex.mappingCone.inl (flatTelescopeDifferential E₂ t₂)).comp
          (Cochain.ofHom r₂) (add_zero _) = 0 ∧
        Limits.Sigma.map a ≫
            CochainComplex.mappingCone.inr (flatTelescopeDifferential E₁ t₁) ≫ r₁ =
          Sigma.desc (fun n : ℕ ↦ q n ≫ P.ιTruncLE (n : ℤ)) ∧
        Limits.Sigma.map b ≫
            CochainComplex.mappingCone.inr (flatTelescopeDifferential E₂ t₂) ≫ r₂ =
          Sigma.desc (fun n : ℕ ↦ q n ≫ P.ιTruncLE (n : ℤ)) ≫ f := by
  obtain ⟨E, t, q, hb, hf, hq, _, ht⟩ :=
    CochainComplex.exists_flat_truncation_tower P
  let p : ∀ n : ℕ, E n ⟶ P := fun n ↦ q n ≫ P.ιTruncLE (n : ℤ)
  have hp (n : ℕ) : t n ≫ p (n + 1) = p n := ht n
  obtain ⟨R, F, s, u, c, a, hbR, hfR, hbF, hfF, hc, hs, ha,
    r₁, hr₁, hz₁, he₁⟩ :=
    exists_flat_telescope_target_refinement Y E t hb hf P hP p hp
  let p' : ∀ n : ℕ, R n ⟶ P' := fun n ↦ c n ≫ p n ≫ f
  have hp' (n : ℕ) : s n ≫ p' (n + 1) = p' n := by
    dsimp [p']
    rw [← Category.assoc, hs n, Category.assoc,
      ← Category.assoc (t n) (p (n + 1)) f, hp n]
  obtain ⟨S, G, v, w, d, b, hbS, hfS, hbG, hfG, hd, hv, hb',
    r₂, hr₂, hz₂, he₂⟩ :=
    exists_flat_telescope_target_refinement Y R s hbR hfR P' hP' p' hp'
  let q' : ∀ n : ℕ, S n ⟶ P.truncLE (n : ℤ) := fun n ↦ d n ≫ c n ≫ q n
  let a' : ∀ n : ℕ, S n ⟶ F n := fun n ↦ d n ≫ a n
  have hδ := telescope_square_of_level_square S R v s d hv
  have ha₀ := telescope_square_of_level_square R F s u a ha
  have hb₀ := telescope_square_of_level_square S G v w b hb'
  have ha' : flatTelescopeDifferential S v ≫ Limits.Sigma.map a' =
      Limits.Sigma.map a' ≫ flatTelescopeDifferential F u := by
    simp only [a', ← Sigma.map_comp_map]
    rw [← Category.assoc, hδ, Category.assoc, ha₀, ← Category.assoc]
  have hq' (n : ℕ) : QuasiIso (q' n) := by
    have := hd n
    have := hc n
    have := hq n
    dsimp [q']
    infer_instance
  have ht' (n : ℕ) :
      v n ≫ q' (n + 1) ≫ P.ιTruncLE ((n + 1 : ℕ) : ℤ) =
        q' n ≫ P.ιTruncLE (n : ℤ) := by
    dsimp [q']
    simp only [Category.assoc]
    rw [← Category.assoc (v n) (d (n + 1)), hv n]
    simp only [Category.assoc]
    rw [← Category.assoc (s n) (c (n + 1)), hs n]
    simp only [Category.assoc]
    simpa only [Category.assoc, Int.natCast_succ] using
      congrArg (fun k ↦ d n ≫ c n ≫ k) (ht n)
  refine ⟨S, F, G, v, u, w, a', b, hbS, hfS, hbF, hfF, hbG, hfG,
    ha', hb₀, r₁, r₂, q', hr₁, hr₂, hq', ht', hz₁, hz₂, ?_, ?_⟩
  · simp only [a', ← Sigma.map_comp_map, Category.assoc]
    rw [he₁]
    apply Sigma.hom_ext
    intro n
    simp [q', p, Category.assoc]
  · rw [he₂]
    apply Sigma.hom_ext
    intro n
    simp [q', p', p, Category.assoc]


end AlgebraicGeometry
```

### Sheaf.AlgebraicGeometry.FlatTelescopeArrowCocycles

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.FlatTelescopeStageMap
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Sheaf.AlgebraicGeometry.FlatTelescopeArrowBarData

/-! # Summand cocycles for a simultaneous flat-tower resolution

Source: the geometric construction and retained homotopies of
lem-sc-flat-telescope-arrow-diagram, steps 1--3; Stacks Project Tags 077J and 06YS.
(blueprint: lem-sc-flat-telescope-arrow-cocycles).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex
namespace AlgebraicGeometry

/-- The geometric part of the simultaneous resolution, before assembling a map
out of the source cone. The four equations are equations of cochains on the source
sum, retaining both components of the comparison homotopies. No source-cone
augmentation or equality of maps from that cone is asserted here.

Source: lem-sc-flat-telescope-arrow-diagram, steps 1 and 2 and the retained arrow
homotopies in step 3; Stacks Project Tags 077J and 06YS. The simultaneous comparison
is the parent plan's agent expansion, not a theorem stated verbatim by Stacks.

Proof. Apply the finite-piece bar construction of
`exists_flat_telescope_arrow_bar_data`. It supplies zero shifted restrictions for
both target augmentations and strict agreement of their unshifted restrictions
with the source sum augmentation. Choose all four cochains to be zero. Their
differentials and their composites are zero. Substitution of the two shifted
restriction equalities proves the first and third equations. Apply `Cochain.ofHom`
to the two strict sum identities and reverse the resulting equalities to obtain
the second and fourth equations. The tower, bounds, flatness, quasi-isomorphisms,
and target homotopy isomorphisms are preserved unchanged. No support or lifting
argument is used in this algebraic step.
(blueprint: lem-sc-flat-telescope-arrow-cocycles). -/
theorem exists_flat_telescope_arrow_cocycles (Y : Scheme.{u})
    (P P' : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hP : isFlatTelescope Y P) (hP' : isFlatTelescope Y P') (f : P ⟶ P') :
    let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
    let Q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
    ∃ (E₀ E₁ E₂ : ℕ → CochainComplex A ℤ)
      (t₀ : ∀ n : ℕ, E₀ n ⟶ E₀ (n + 1))
      (t₁ : ∀ n : ℕ, E₁ n ⟶ E₁ (n + 1))
      (t₂ : ∀ n : ℕ, E₂ n ⟶ E₂ (n + 1))
      (a : ∀ n : ℕ, E₀ n ⟶ E₁ n) (b : ∀ n : ℕ, E₀ n ⟶ E₂ n),
      (∀ n : ℕ, ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero ((E₀ n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E₀ n).X i)) ∧
      (∀ n : ℕ, ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero ((E₁ n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E₁ n).X i)) ∧
      (∀ n : ℕ, ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero ((E₂ n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E₂ n).X i)) ∧
      ∃ (_c₁ : flatTelescopeDifferential E₀ t₀ ≫ Limits.Sigma.map a =
          Limits.Sigma.map a ≫ flatTelescopeDifferential E₁ t₁)
        (_c₂ : flatTelescopeDifferential E₀ t₀ ≫ Limits.Sigma.map b =
          Limits.Sigma.map b ≫ flatTelescopeDifferential E₂ t₂)
        (r₁ : CochainComplex.mappingCone (flatTelescopeDifferential E₁ t₁) ⟶ P)
        (r₂ : CochainComplex.mappingCone (flatTelescopeDifferential E₂ t₂) ⟶ P')
        (q : ∀ n : ℕ, E₀ n ⟶ P.truncLE (n : ℤ)),
        IsIso (Q.map r₁) ∧ IsIso (Q.map r₂) ∧
        (∀ n : ℕ, QuasiIso (q n)) ∧
        (∀ n : ℕ, t₀ n ≫ q (n + 1) ≫ P.ιTruncLE ((n + 1 : ℕ) : ℤ) =
          q n ≫ P.ιTruncLE (n : ℤ)) ∧
        let s := Sigma.desc (fun n : ℕ ↦ q n ≫ P.ιTruncLE (n : ℤ))
        ∃ (α₁ : Cochain (∐ E₀) P (-2)) (β₁ : Cochain (∐ E₀) P (-1))
          (α₂ : Cochain (∐ E₀) P' (-2)) (β₂ : Cochain (∐ E₀) P' (-1)),
          (0 : Cochain (∐ E₀) P (-1)) =
            δ (-2) (-1) α₁ +
            (Cochain.ofHom (flatTelescopeDifferential E₀ t₀)).comp β₁ (zero_add _) +
            (Cochain.ofHom (Limits.Sigma.map a)).comp
              ((CochainComplex.mappingCone.inl (flatTelescopeDifferential E₁ t₁)).comp
                (Cochain.ofHom r₁) (add_zero _)) (zero_add _) ∧
          Cochain.ofHom s = δ (-1) 0 β₁ +
            Cochain.ofHom (Limits.Sigma.map a ≫
              CochainComplex.mappingCone.inr (flatTelescopeDifferential E₁ t₁) ≫
              r₁) ∧
          (0 : Cochain (∐ E₀) P' (-1)) =
            δ (-2) (-1) α₂ +
            (Cochain.ofHom (flatTelescopeDifferential E₀ t₀)).comp β₂ (zero_add _) +
            (Cochain.ofHom (Limits.Sigma.map b)).comp
              ((CochainComplex.mappingCone.inl (flatTelescopeDifferential E₂ t₂)).comp
                (Cochain.ofHom r₂) (add_zero _)) (zero_add _) ∧
          Cochain.ofHom (s ≫ f) = δ (-1) 0 β₂ +
            Cochain.ofHom (Limits.Sigma.map b ≫
              CochainComplex.mappingCone.inr (flatTelescopeDifferential E₂ t₂) ≫
              r₂) := by
  obtain ⟨E₀, E₁, E₂, t₀, t₁, t₂, a, b, hb₀, hf₀, hb₁, hf₁, hb₂, hf₂,
    _c₁, _c₂, r₁, r₂, q, hi₁, hi₂, hq, hc, hL₁, hL₂, hs₁, hs₂⟩ :=
    exists_flat_telescope_arrow_bar_data Y P P' hP hP' f
  dsimp only
  refine ⟨E₀, E₁, E₂, t₀, t₁, t₂, a, b, hb₀, hf₀, hb₁, hf₁, hb₂, hf₂,
    _c₁, _c₂, r₁, r₂, q, hi₁, hi₂, hq, hc, ?_⟩
  let s := Sigma.desc (fun n : ℕ ↦ q n ≫ P.ιTruncLE (n : ℤ))
  refine ⟨0, 0, 0, 0, ?_, ?_, ?_, ?_⟩
  · simp only [δ_zero, Cochain.comp_zero, zero_add, hL₁]
  · simpa only [δ_zero, zero_add] using (congrArg Cochain.ofHom hs₁).symm
  · simp only [δ_zero, Cochain.comp_zero, zero_add, hL₂]
  · simpa only [δ_zero, zero_add] using (congrArg Cochain.ofHom hs₂).symm

end AlgebraicGeometry
```

### Sheaf.AlgebraicGeometry.FlatTelescopeArrowDiagram

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.AlgebraicGeometry.FlatTelescopeStageMap
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Sheaf.AlgebraicGeometry.FlatTelescopeArrowCocycles

/-! # A compatible flat-tower diagram over a cochain arrow

Source: the diagram construction in lem-sc-flat-telescope-stage-map-refinement,
step 1, using Stacks Project Tags 06YS, 06YJ and 077J.
(blueprint: lem-sc-flat-telescope-arrow-diagram).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem telescope_augmentation
    (Y : Scheme.{u})
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (E : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (t : ∀ n : ℕ, E n ⟶ E (n + 1))
    (q : ∀ n : ℕ, E n ⟶ P.truncLE (n : ℤ))
    (hc : ∀ n : ℕ, t n ≫ q (n + 1) ≫ P.ιTruncLE ((n + 1 : ℕ) : ℤ) =
      q n ≫ P.ιTruncLE (n : ℤ)) :
    ∃ g : CochainComplex.mappingCone (flatTelescopeDifferential E t) ⟶ P,
      CochainComplex.mappingCone.inr _ ≫ g =
        Sigma.desc (fun n : ℕ ↦ q n ≫ P.ιTruncLE (n : ℤ)) ∧
      (CochainComplex.mappingCone.inl _).comp
        (CochainComplex.HomComplex.Cochain.ofHom g) (add_zero _) = 0 := by
  let s := Sigma.desc (fun n : ℕ ↦ q n ≫ P.ιTruncLE (n : ℤ))
  have hz : flatTelescopeDifferential E t ≫ s = 0 := by
    dsimp [flatTelescopeDifferential, s]
    rw [Preadditive.sub_comp, Category.id_comp]
    apply sub_eq_zero.mpr
    apply Sigma.hom_ext
    intro n
    simp only [Category.assoc, Sigma.ι_desc_assoc, Sigma.ι_desc]
    exact (hc n).symm
  have hd : CochainComplex.HomComplex.δ (-1) 0
      (0 : CochainComplex.HomComplex.Cochain (∐ E) P (-1)) =
      CochainComplex.HomComplex.Cochain.ofHom (flatTelescopeDifferential E t ≫ s) := by
    rw [hz]
    simp
  exact ⟨CochainComplex.mappingCone.desc _ 0 s hd,
    CochainComplex.mappingCone.inr_desc _ 0 s hd,
    CochainComplex.mappingCone.inl_desc _ 0 s hd⟩

open CochainComplex.HomComplex in
private theorem cone_comparison
    {Y : Scheme.{u}}
    {F G P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ}
    (φ : F ⟶ F) (ψ : G ⟶ G) (a : F ⟶ G) (hc : φ ≫ a = a ≫ ψ)
    (r : CochainComplex.mappingCone ψ ⟶ P)
    (s : F ⟶ P) (g : CochainComplex.mappingCone φ ⟶ P)
    (hinr : CochainComplex.mappingCone.inr φ ≫ g = s)
    (hinl : (CochainComplex.mappingCone.inl φ).comp (Cochain.ofHom g) (add_zero _) = 0)
    (α : Cochain F P (-2)) (β : Cochain F P (-1))
    (hα : (0 : Cochain F P (-1)) = δ (-2) (-1) α +
      (Cochain.ofHom φ).comp β (zero_add _) +
      (Cochain.ofHom a).comp ((CochainComplex.mappingCone.inl ψ).comp
        (Cochain.ofHom r) (add_zero _)) (zero_add _))
    (hβ : Cochain.ofHom s = δ (-1) 0 β +
      Cochain.ofHom (a ≫ CochainComplex.mappingCone.inr ψ ≫ r)) :
    Nonempty (Homotopy g (CochainComplex.mappingCone.map φ ψ a a hc ≫ r)) := by
  constructor
  apply CochainComplex.mappingCone.descHomotopy φ _ _ α β
  · rw [hinl]
    convert hα using 1
    rw [Cochain.ofHom_comp, ← Cochain.comp_assoc_of_second_is_zero_cochain]
    simp only [CochainComplex.mappingCone.map, CochainComplex.mappingCone.inl_desc]
    rw [Cochain.comp_assoc_of_third_is_zero_cochain]
  · simpa only [hinr, CochainComplex.mappingCone.map, Category.assoc,
      CochainComplex.mappingCone.inr_desc_assoc] using hβ

/-- Assemble a simultaneous flat tower diagram from its summand cocycles.
Source: parent construction steps 1--3; Mathlib mapping-cone descent and homotopy
constructors. The finite-piece bar construction supplies the geometric input.
Proof. Strict truncation compatibility annihilates the one-minus-shift differential.
Descend the sum augmentation to the source cone, with shifted component zero.
The two pairs of summand cochain identities give the two comparison homotopies by
`mappingCone.descHomotopy`. Pass to the homotopy category and take the isomorphisms
associated with the target augmentation maps.
(blueprint: lem-sc-flat-telescope-arrow-diagram). -/
theorem exists_flat_telescope_arrow_diagram (Y : Scheme.{u})
    (P P' : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hP : isFlatTelescope Y P) (hP' : isFlatTelescope Y P') (f : P ⟶ P') :
    let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
    let Q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
    ∃ (E₀ E₁ E₂ : ℕ → CochainComplex A ℤ)
      (t₀ : ∀ n : ℕ, E₀ n ⟶ E₀ (n + 1))
      (t₁ : ∀ n : ℕ, E₁ n ⟶ E₁ (n + 1))
      (t₂ : ∀ n : ℕ, E₂ n ⟶ E₂ (n + 1))
      (a : ∀ n : ℕ, E₀ n ⟶ E₁ n) (b : ∀ n : ℕ, E₀ n ⟶ E₂ n),
      (∀ n : ℕ, ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero ((E₀ n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E₀ n).X i)) ∧
      (∀ n : ℕ, ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero ((E₁ n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E₁ n).X i)) ∧
      (∀ n : ℕ, ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero ((E₂ n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E₂ n).X i)) ∧
      ∃ (c₁ : flatTelescopeDifferential E₀ t₀ ≫ Limits.Sigma.map a =
          Limits.Sigma.map a ≫ flatTelescopeDifferential E₁ t₁)
        (c₂ : flatTelescopeDifferential E₀ t₀ ≫ Limits.Sigma.map b =
          Limits.Sigma.map b ≫ flatTelescopeDifferential E₂ t₂)
        (e₁ : Q.obj (CochainComplex.mappingCone (flatTelescopeDifferential E₁ t₁)) ≅
          Q.obj P)
        (e₂ : Q.obj (CochainComplex.mappingCone (flatTelescopeDifferential E₂ t₂)) ≅
          Q.obj P')
        (g : CochainComplex.mappingCone (flatTelescopeDifferential E₀ t₀) ⟶ P)
        (q : ∀ n : ℕ, E₀ n ⟶ P.truncLE (n : ℤ)),
        (∀ n : ℕ, QuasiIso (q n)) ∧
        (∀ n : ℕ, t₀ n ≫ q (n + 1) ≫ P.ιTruncLE ((n + 1 : ℕ) : ℤ) =
          q n ≫ P.ιTruncLE (n : ℤ)) ∧
        (CochainComplex.mappingCone.inr _ ≫ g =
          Sigma.desc (fun n : ℕ ↦ q n ≫ P.ιTruncLE (n : ℤ))) ∧
        ((CochainComplex.mappingCone.inl _).comp
          (CochainComplex.HomComplex.Cochain.ofHom g) (add_zero _) = 0) ∧
        (Q.map g = Q.map (CochainComplex.mappingCone.map
          (flatTelescopeDifferential E₀ t₀) (flatTelescopeDifferential E₁ t₁)
          (Limits.Sigma.map a) (Limits.Sigma.map a) c₁) ≫ e₁.hom) ∧
        (Q.map g ≫ Q.map f = Q.map (CochainComplex.mappingCone.map
          (flatTelescopeDifferential E₀ t₀) (flatTelescopeDifferential E₂ t₂)
          (Limits.Sigma.map b) (Limits.Sigma.map b) c₂) ≫ e₂.hom) := by
  dsimp only
  obtain ⟨E₀, E₁, E₂, t₀, t₁, t₂, a, b, hb₀, hf₀, hb₁, hf₁, hb₂, hf₂,
    c₁, c₂, r₁, r₂, q, hr₁, hr₂, hq, hc, α₁, β₁, α₂, β₂, hα₁, hβ₁, hα₂, hβ₂⟩ :=
    exists_flat_telescope_arrow_cocycles Y P P' hP hP' f
  obtain ⟨g, hinr, hinl⟩ := telescope_augmentation Y P E₀ t₀ q hc
  let Q := HomotopyCategory.quotient
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)
  let : IsIso (Q.map r₁) := hr₁
  let : IsIso (Q.map r₂) := hr₂
  refine ⟨E₀, E₁, E₂, t₀, t₁, t₂, a, b, hb₀, hf₀, hb₁, hf₁, hb₂, hf₂,
    c₁, c₂, asIso (Q.map r₁), asIso (Q.map r₂), g, q, hq, hc, hinr, hinl, ?_, ?_⟩
  · obtain ⟨H⟩ := cone_comparison (flatTelescopeDifferential E₀ t₀)
      (flatTelescopeDifferential E₁ t₁) (Limits.Sigma.map a) c₁ r₁ _ g
      hinr hinl α₁ β₁ hα₁ hβ₁
    simpa only [Functor.map_comp, asIso_hom] using
      HomotopyCategory.eq_of_homotopy _ _ H
  · have hinr' : CochainComplex.mappingCone.inr _ ≫ (g ≫ f) =
        Sigma.desc (fun n : ℕ ↦ q n ≫ P.ιTruncLE (n : ℤ)) ≫ f := by
      rw [← Category.assoc, hinr]
    have hinl' : (CochainComplex.mappingCone.inl _).comp
        (CochainComplex.HomComplex.Cochain.ofHom (g ≫ f)) (add_zero _) = 0 := by
      rw [CochainComplex.HomComplex.Cochain.ofHom_comp,
        ← CochainComplex.HomComplex.Cochain.comp_assoc_of_second_is_zero_cochain,
        hinl, CochainComplex.HomComplex.Cochain.zero_comp]
    obtain ⟨H⟩ := cone_comparison (flatTelescopeDifferential E₀ t₀)
      (flatTelescopeDifferential E₂ t₂) (Limits.Sigma.map b) c₂ r₂ _ (g ≫ f)
      hinr' hinl' α₂ β₂ hα₂ hβ₂
    simpa only [Functor.map_comp, asIso_hom] using
      HomotopyCategory.eq_of_homotopy _ _ H


-- Preserve the legacy signature, whose core proposition binds unused maps.
set_option linter.unusedVariables false in
/-- Construct the bounded-flat tower diagram over a cochain arrow, together with
its augmentation to the good truncations of the source. This is the construction
step only: the augmentation's quasi-isomorphism and the stage-map predicates are
verified separately by the caller.

Source: step 1 and the diagram-construction portion of step 2 of
lem-sc-flat-telescope-stage-map-refinement; Stacks Project Tags 06YS and 077J,
bounded flat resolutions and compatible-pair lifts. The assertion about maps to
supplied telescope models is an expansion of that plan, not a literal Stacks lemma.

Proof. Apply the unconditional arrow-diagram theorem proved above; the
legacy structural-core hypothesis is not needed. That theorem constructs the
source augmentation by mapping-cone descent from strictly compatible truncation
maps, and proves both comparisons with the cone homotopy constructor. The tower
and target augmentation input comes from the finite-piece bar construction,
through its zero comparison cochains. This replaces the former invalid claim
that finite support of individual generators gives a single bound for an entire
source stage. The bar construction includes all finite source pieces at each
stage and does not make that claim.
(blueprint: lem-sc-flat-telescope-arrow-diagram-construction). -/
theorem exists_flat_telescope_arrow_diagram_construction (Y : Scheme.{u})
    (P P' : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hP : isFlatTelescope Y P) (hP' : isFlatTelescope Y P') (f : P ⟶ P')
    (hcore : ∃ (E₀ E₁ E₂ : ℕ →
        CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
      (t₀ : ∀ n : ℕ, E₀ n ⟶ E₀ (n + 1))
      (t₁ : ∀ n : ℕ, E₁ n ⟶ E₁ (n + 1))
      (t₂ : ∀ n : ℕ, E₂ n ⟶ E₂ (n + 1))
      (a : ∀ n : ℕ, E₀ n ⟶ E₁ n) (b : ∀ n : ℕ, E₀ n ⟶ E₂ n),
      (∀ n : ℕ, ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero ((E₀ n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E₀ n).X i)) ∧
      (∀ n : ℕ, ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero ((E₁ n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E₁ n).X i)) ∧
      (∀ n : ℕ, ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero ((E₂ n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E₂ n).X i))) :
    let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
    let Q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
    ∃ (E₀ E₁ E₂ : ℕ → CochainComplex A ℤ)
      (t₀ : ∀ n : ℕ, E₀ n ⟶ E₀ (n + 1))
      (t₁ : ∀ n : ℕ, E₁ n ⟶ E₁ (n + 1))
      (t₂ : ∀ n : ℕ, E₂ n ⟶ E₂ (n + 1))
      (a : ∀ n : ℕ, E₀ n ⟶ E₁ n) (b : ∀ n : ℕ, E₀ n ⟶ E₂ n),
      (∀ n : ℕ, ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero ((E₀ n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E₀ n).X i)) ∧
      (∀ n : ℕ, ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero ((E₁ n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E₁ n).X i)) ∧
      (∀ n : ℕ, ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero ((E₂ n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E₂ n).X i)) ∧
      ∃ (c₁ : flatTelescopeDifferential E₀ t₀ ≫ Limits.Sigma.map a =
          Limits.Sigma.map a ≫ flatTelescopeDifferential E₁ t₁)
        (c₂ : flatTelescopeDifferential E₀ t₀ ≫ Limits.Sigma.map b =
          Limits.Sigma.map b ≫ flatTelescopeDifferential E₂ t₂)
        (e₁ : Q.obj (CochainComplex.mappingCone (flatTelescopeDifferential E₁ t₁)) ≅
          Q.obj P)
        (e₂ : Q.obj (CochainComplex.mappingCone (flatTelescopeDifferential E₂ t₂)) ≅
          Q.obj P')
        (g : CochainComplex.mappingCone (flatTelescopeDifferential E₀ t₀) ⟶ P)
        (q : ∀ n : ℕ, E₀ n ⟶ P.truncLE (n : ℤ)),
        (∀ n : ℕ, QuasiIso (q n)) ∧
        (∀ n : ℕ, t₀ n ≫ q (n + 1) ≫ P.ιTruncLE ((n + 1 : ℕ) : ℤ) =
          q n ≫ P.ιTruncLE (n : ℤ)) ∧
        (CochainComplex.mappingCone.inr _ ≫ g =
          Sigma.desc (fun n : ℕ ↦ q n ≫ P.ιTruncLE (n : ℤ))) ∧
        ((CochainComplex.mappingCone.inl _).comp
          (CochainComplex.HomComplex.Cochain.ofHom g) (add_zero _) = 0) ∧
        (Q.map g = Q.map (CochainComplex.mappingCone.map
          (flatTelescopeDifferential E₀ t₀) (flatTelescopeDifferential E₁ t₁)
          (Limits.Sigma.map a) (Limits.Sigma.map a) c₁) ≫ e₁.hom) ∧
        (Q.map g ≫ Q.map f = Q.map (CochainComplex.mappingCone.map
          (flatTelescopeDifferential E₀ t₀) (flatTelescopeDifferential E₂ t₂)
          (Limits.Sigma.map b) (Limits.Sigma.map b) c₂) ≫ e₂.hom) := by
  clear hcore
  exact exists_flat_telescope_arrow_diagram Y P P' hP hP' f

end AlgebraicGeometry
```

### Sheaf.AlgebraicGeometry.FlatTelescopeNormalizationIsIso

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Sheaf.AlgebraicGeometry.FlatTelescopeStageMap
public import Sheaf.AlgebraicGeometry.BoundedFlatModelNormalization
import Sheaf.AlgebraicGeometry.FlatTelescopeNormalizationUnshiftedIsIso

/-! # Invertibility of normalized telescope morphisms

Source: steps 1--3 of lem-sc-flat-telescope-bounded-normalization-extension. -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
namespace AlgebraicGeometry

/-- Extend invertibility on literal telescopes to their one-fold translates.

Source: the translated-cone clause of steps 1--2 of
lem-sc-flat-telescope-bounded-normalization-extension, Stacks Tags 06YS and 06YJ.

Proof. Destruct the representative. For an unshifted representative apply
unshifted invertibility. For a translate, the shift equation expresses its
component composed with the target shift comparison as a composite of
isomorphisms: the localization shift map, the fixed normalized-unit comparison,
and the shifted unshifted component. Cancel the invertible target shift
comparison. This covers the zero telescope without an extra assumption.
(blueprint: lem-sc-flat-telescope-normalization-is-iso). -/
theorem flat_telescope_normalization_isIso
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    [(Scheme.Modules.tensorPullback f).Additive]
    (e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
        (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧)
    (α : ∀ X : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ),
        flatTelescopeShiftRepresentative Y X →
          ((DerivedCategory.Qh ⋙ derivedPullback f).obj X ⟶
            ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
              (DerivedCategory.Qh : HomotopyCategory
                (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                schemeDerivedCategory Z)).obj X))
    (hαnat : (∀ (X X' : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
          (hX : flatTelescopeShiftRepresentative Y X) (hX' : flatTelescopeShiftRepresentative Y X')
          (s : X ⟶ X'),
          (DerivedCategory.Qh ⋙ derivedPullback f).map s ≫ (α X' hX') =
            (α X hX) ≫
              ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
                (DerivedCategory.Qh : HomotopyCategory
                  (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                  schemeDerivedCategory Z)).map s))
    (hαshift :
        ∀ (P : CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
        (htel : isFlatTelescope Y P),
        let X := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P
        let G := (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          (DerivedCategory.Qh : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
            schemeDerivedCategory Z)
        (α (X⟦(1 : ℤ)⟧) ⟨P, htel, Or.inr rfl⟩) ≫
            (G.commShiftIso (1 : ℤ)).hom.app X =
          (derivedPullback f).map ((DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app X) ≫
            ((derivedPullback f).mapIso
                (schemeCanonicalShiftUnitIso Y (DerivedCategory.Qh.obj X)).symm ≪≫
              asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) (DerivedCategory.Qh.obj X)) ≪≫
              tensorIso e (Iso.refl _) ≪≫
              schemeCanonicalShiftUnitIso Z
                ((derivedPullback f).obj (DerivedCategory.Qh.obj X))).hom ≫
            (α X ⟨P, htel, Or.inl rfl⟩)⟦(1 : ℤ)⟧')
    (hαbounded : ∀ (X : HomotopyCategory
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
      (hX : flatTelescopeShiftRepresentative Y X),
      boundedFlatShiftRepresentative Y X → IsIso (α X hX)) :
    ∀ (X : HomotopyCategory
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
      (hX : flatTelescopeShiftRepresentative Y X), IsIso (α X hX) := by
  intro X hX
  obtain ⟨P, htel, h | h⟩ := hX
  · subst X
    exact flat_telescope_normalization_unshifted_isIso f e α hαnat hαshift hαbounded
      P htel
  · subst X
    let X := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P
    let G := (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      (DerivedCategory.Qh : HomotopyCategory
        (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
        schemeDerivedCategory Z)
    have : IsIso (α X ⟨P, htel, Or.inl rfl⟩) :=
      flat_telescope_normalization_unshifted_isIso f e α hαnat hαshift hαbounded P htel
    have : IsIso (α (X⟦(1 : ℤ)⟧) ⟨P, htel, Or.inr rfl⟩ ≫
        (G.commShiftIso (1 : ℤ)).hom.app X) := by
      rw [hαshift P htel]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((G.commShiftIso (1 : ℤ)).hom.app X)

end AlgebraicGeometry
```

### Sheaf.AlgebraicGeometry.FlatTelescopeNormalizationUnshiftedIsIso

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Sheaf.AlgebraicGeometry.FlatTelescopeStageMap
public import Sheaf.AlgebraicGeometry.BoundedFlatModelNormalization
import Sheaf.AlgebraicGeometry.FlatTelescopeSumComparisonIsIso

/-! # Invertibility of normalized telescope morphisms

Source: steps 1--3 of lem-sc-flat-telescope-bounded-normalization-extension. -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
namespace AlgebraicGeometry


-- The five lemma only needs the four squares of the five-term exact sequences.
-- In particular, the fourth vertical map need not be the shift of the first.
private theorem cone_five_lemma
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {T T' : Triangle C} (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C)
    (a : T.obj₁ ⟶ T'.obj₁) (b : T.obj₂ ⟶ T'.obj₂) (c : T.obj₃ ⟶ T'.obj₃)
    (d : T.obj₁⟦(1 : ℤ)⟧ ⟶ T'.obj₁⟦(1 : ℤ)⟧)
    (e : T.obj₂⟦(1 : ℤ)⟧ ⟶ T'.obj₂⟦(1 : ℤ)⟧)
    [IsIso a] [IsIso b] [IsIso d] [IsIso e]
    (h₁ : T.mor₁ ≫ b = a ≫ T'.mor₁)
    (h₂ : T.mor₂ ≫ c = b ≫ T'.mor₂)
    (h₃ : T.mor₃ ≫ d = c ≫ T'.mor₃)
    (h₄ : T.mor₁⟦(1 : ℤ)⟧' ≫ e = d ≫ T'.mor₁⟦(1 : ℤ)⟧') : IsIso c := by
  have : Mono c := by
    rw [Preadditive.mono_iff_cancel_zero]
    intro A x hx
    obtain ⟨y, rfl⟩ := T.coyoneda_exact₃ hT x (by
      rw [← cancel_mono d, Category.assoc, h₃, reassoc_of% hx,
        zero_comp, zero_comp])
    have hy : (y ≫ b) ≫ T'.mor₂ = 0 := by
      rw [Category.assoc, ← h₂, ← Category.assoc]
      exact hx
    obtain ⟨z, hz⟩ := T'.coyoneda_exact₂ hT' (y ≫ b) hy
    have heq : y = (z ≫ inv a) ≫ T.mor₁ := by
      apply (cancel_mono b).1
      rw [Category.assoc, h₁]
      simpa only [Category.assoc, IsIso.inv_hom_id_assoc] using hz
    rw [heq, Category.assoc, comp_distTriang_mor_zero₁₂ T hT, comp_zero]
  apply isIso_of_yoneda_map_bijective c
  intro A
  constructor
  · intro x y h
    exact (cancel_mono c).1 h
  · intro y
    let x₄ := y ≫ T'.mor₃ ≫ inv d
    have hx₄ : x₄ ≫ T.mor₁⟦(1 : ℤ)⟧' = 0 := by
      apply (cancel_mono e).1
      dsimp only [x₄]
      rw [Category.assoc, Category.assoc, h₄]
      simp only [Category.assoc, IsIso.inv_hom_id_assoc,
        comp_distTriang_mor_zero₃₁ T' hT', comp_zero, zero_comp]
    obtain ⟨x, hx⟩ := T.coyoneda_exact₁ hT x₄ hx₄
    have hxc : x ≫ c ≫ T'.mor₃ = y ≫ T'.mor₃ := by
      rw [← h₃, ← Category.assoc, ← hx]
      dsimp only [x₄]
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    obtain ⟨z, hz⟩ := T'.coyoneda_exact₃ hT' (y - x ≫ c) (by
      rw [Preadditive.sub_comp, Category.assoc, hxc, sub_self])
    refine ⟨x + (z ≫ inv b) ≫ T.mor₂, ?_⟩
    change (x + (z ≫ inv b) ≫ T.mor₂) ≫ c = y
    rw [Preadditive.add_comp, Category.assoc, h₂]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    rw [← hz]
    exact add_sub_cancel _ _


private theorem transport_naturality
    {C D : Type*} [Category C] [Category D] (F G : C ⥤ D) (P : C → Prop)
    (a : ∀ X, P X → (F.obj X ⟶ G.obj X))
    (hn : ∀ X X' hX hX' (s : X ⟶ X'), F.map s ≫ a X' hX' = a X hX ≫ G.map s)
    {X X' S S' : C} (hS : P S) (hS' : P S') (i : X ≅ S) (i' : X' ≅ S')
    (s : X ⟶ X') :
    F.map s ≫ (F.map i'.hom ≫ a S' hS' ≫ G.map i'.inv) =
      (F.map i.hom ≫ a S hS ≫ G.map i.inv) ≫ G.map s := by
  have h := congrArg (fun z ↦ F.map i.hom ≫ z ≫ G.map i'.inv)
    (hn S S' hS hS' (i.inv ≫ s ≫ i'.hom))
  simp only [Functor.map_comp, Category.assoc] at h
  rw [← Category.assoc (F.map i.hom) (F.map i.inv), ← F.map_comp,
    Iso.hom_inv_id, F.map_id, Category.id_comp] at h
  rw [← G.map_comp i'.hom i'.inv, Iso.hom_inv_id, G.map_id, Category.comp_id] at h
  simpa only [Category.assoc] using h



private theorem shifted_transport_comm
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    (F G : C ⥤ D) [F.CommShift ℤ] [G.CommShift ℤ]
    {X : C} (s : X ⟶ X) (a : F.obj (X⟦(1 : ℤ)⟧) ⟶ G.obj (X⟦(1 : ℤ)⟧))
    (h : F.map (s⟦(1 : ℤ)⟧') ≫ a = a ≫ G.map (s⟦(1 : ℤ)⟧')) :
    (F.map s)⟦(1 : ℤ)⟧' ≫
        ((F.commShiftIso (1 : ℤ)).inv.app X ≫ a ≫
          (G.commShiftIso (1 : ℤ)).hom.app X) =
      ((F.commShiftIso (1 : ℤ)).inv.app X ≫ a ≫
          (G.commShiftIso (1 : ℤ)).hom.app X) ≫ (G.map s)⟦(1 : ℤ)⟧' := by
  rw [← Category.assoc, F.commShiftIso_inv_naturality]
  simp only [Category.assoc]
  rw [← Category.assoc (F.map (s⟦(1 : ℤ)⟧')), h]
  simp only [Category.assoc]
  rw [G.commShiftIso_hom_naturality]

/-- A normalized natural comparison invertible on bounded-flat models
is invertible on each literal unshifted telescope model. This is the invertibility step, not a
construction of the comparison or of its shift equation.

Source: the sum and inverse-cone parts of steps 1--2 of
lem-sc-flat-telescope-bounded-normalization-extension, Stacks Tags 06YS and 06YJ.

Proof. First replace the sum of the bounded-flat stages by the telescope of
its finite partial sums. Every finite partial sum is bounded above and flat;
the standard split telescope augmentation identifies this telescope with the
sum in the homotopy category. Naturality for the finite-stage inclusions and
preservation of coproducts identify the comparison on this sum with the sum
of invertible bounded comparisons, hence it is invertible. The shift identity
identifies its translated component with a composite of isomorphisms.
Now use the triangle of one minus transition. Stage naturality gives its first
two squares; the normalized shift identity gives the connecting square.
Thus the comparison is a morphism between the two distinguished triangles.
Its first two components are invertible, so its cone component is invertible
by the two-out-of-three theorem for morphisms of distinguished triangles.
Use common flat refinements to identify the literal telescope with the
transition cone presentation used in this argument. The zero tower and empty
scheme have zero-object components, which are invertible; no common upper
bound on the whole tower is assumed.
(blueprint: lem-sc-flat-telescope-normalization-unshifted-is-iso). -/
theorem flat_telescope_normalization_unshifted_isIso
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    [(Scheme.Modules.tensorPullback f).Additive]
    (e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
        (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧)
    (α : ∀ X : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ),
        flatTelescopeShiftRepresentative Y X →
          ((DerivedCategory.Qh ⋙ derivedPullback f).obj X ⟶
            ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
              (DerivedCategory.Qh : HomotopyCategory
                (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                schemeDerivedCategory Z)).obj X))
    (hαnat : (∀ (X X' : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
          (hX : flatTelescopeShiftRepresentative Y X) (hX' : flatTelescopeShiftRepresentative Y X')
          (s : X ⟶ X'),
          (DerivedCategory.Qh ⋙ derivedPullback f).map s ≫ (α X' hX') =
            (α X hX) ≫
              ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
                (DerivedCategory.Qh : HomotopyCategory
                  (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                  schemeDerivedCategory Z)).map s))
    (hαshift :
        ∀ (P : CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
        (htel : isFlatTelescope Y P),
        let X := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P
        let G := (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          (DerivedCategory.Qh : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
            schemeDerivedCategory Z)
        (α (X⟦(1 : ℤ)⟧) ⟨P, htel, Or.inr rfl⟩) ≫
            (G.commShiftIso (1 : ℤ)).hom.app X =
          (derivedPullback f).map ((DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app X) ≫
            ((derivedPullback f).mapIso
                (schemeCanonicalShiftUnitIso Y (DerivedCategory.Qh.obj X)).symm ≪≫
              asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) (DerivedCategory.Qh.obj X)) ≪≫
              tensorIso e (Iso.refl _) ≪≫
              schemeCanonicalShiftUnitIso Z
                ((derivedPullback f).obj (DerivedCategory.Qh.obj X))).hom ≫
            (α X ⟨P, htel, Or.inl rfl⟩)⟦(1 : ℤ)⟧')
    (hαbounded : ∀ (X : HomotopyCategory
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
      (hX : flatTelescopeShiftRepresentative Y X),
      boundedFlatShiftRepresentative Y X → IsIso (α X hX)) :
    ∀ (P : CochainComplex
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
      (htel : isFlatTelescope Y P),
      IsIso (α ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)
        ⟨P, htel, Or.inl rfl⟩) := by
  intro P htel
  obtain ⟨E, t, hb, hf, rfl⟩ := htel
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let H := HomotopyCategory A (ComplexShape.up ℤ)
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let F := derivedPullback f
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ⟨sF, hF⟩, _⟩ :=
    Classical.choose_spec (exists_derivedPullback f)
  let : F.CommShift ℤ := sF
  have : F.IsTriangulated := hF
  let L : H ⥤ schemeDerivedCategory Z := DerivedCategory.Qh ⋙ F
  let G : H ⥤ schemeDerivedCategory Z :=
    (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      (DerivedCategory.Qh : HomotopyCategory
        (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
        schemeDerivedCategory Z)
  obtain ⟨R, hR, ⟨i⟩, h₀⟩ :=
    exists_flat_telescope_sum_comparison_isIso f α hαnat hαbounded E hb hf
  let X := q.obj (∐ E)
  let S := q.obj R
  let hS : flatTelescopeShiftRepresentative Y S := ⟨R, hR, Or.inl rfl⟩
  let hS' : flatTelescopeShiftRepresentative Y (S⟦(1 : ℤ)⟧) := ⟨R, hR, Or.inr rfl⟩
  let i' : X⟦(1 : ℤ)⟧ ≅ S⟦(1 : ℤ)⟧ := (shiftFunctor H (1 : ℤ)).mapIso i
  let a : L.obj X ⟶ G.obj X := L.map i.hom ≫ α S hS ≫ G.map i.inv
  let a' : L.obj (X⟦(1 : ℤ)⟧) ⟶ G.obj (X⟦(1 : ℤ)⟧) :=
    L.map i'.hom ≫ α (S⟦(1 : ℤ)⟧) hS' ≫ G.map i'.inv
  have : IsIso (α S hS) := h₀
  have : IsIso (α (S⟦(1 : ℤ)⟧) hS') := by
    have : IsIso (α (S⟦(1 : ℤ)⟧) hS' ≫ (G.commShiftIso (1 : ℤ)).hom.app S) := by
      rw [hαshift R hR]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((G.commShiftIso (1 : ℤ)).hom.app S)
  have : IsIso a := by dsimp only [a]; infer_instance
  have : IsIso a' := by dsimp only [a']; infer_instance
  let p := flatTelescopeDifferential E t
  let C := CochainComplex.mappingCone.triangleh p
  let hC : flatTelescopeShiftRepresentative Y C.obj₃ :=
    ⟨CochainComplex.mappingCone p, ⟨E, t, hb, hf, rfl⟩, Or.inl rfl⟩
  let c := α C.obj₃ hC
  let T := L.mapTriangle.obj C
  let T' := G.mapTriangle.obj C
  have hT : T ∈ distTriang (schemeDerivedCategory Z) :=
    L.map_distinguished _ (HomotopyCategory.mappingCone_triangleh_distinguished p)
  have hT' : T' ∈ distTriang (schemeDerivedCategory Z) :=
    G.map_distinguished _ (HomotopyCategory.mappingCone_triangleh_distinguished p)
  let d : (L.obj X)⟦(1 : ℤ)⟧ ⟶ (G.obj X)⟦(1 : ℤ)⟧ :=
    (L.commShiftIso (1 : ℤ)).inv.app X ≫ a' ≫ (G.commShiftIso (1 : ℤ)).hom.app X
  have : IsIso d := by dsimp only [d]; infer_instance
  have hn₁ : L.map C.mor₁ ≫ a = a ≫ G.map C.mor₁ :=
    transport_naturality L G _ α hαnat hS hS i i C.mor₁
  have hn₂ : L.map C.mor₂ ≫ c = a ≫ G.map C.mor₂ := by
    simpa only [Iso.refl_hom, Iso.refl_inv, L.map_id, G.map_id, Category.id_comp,
      Category.comp_id] using
      transport_naturality L G _ α hαnat hS hC i (Iso.refl _) C.mor₂
  have hn₃ : L.map C.mor₃ ≫ a' = c ≫ G.map C.mor₃ := by
    simpa only [Iso.refl_hom, Iso.refl_inv, L.map_id, G.map_id, Category.id_comp,
      Category.comp_id] using
      transport_naturality L G _ α hαnat hC hS' (Iso.refl _) i' C.mor₃
  have hn₄ : L.map ((q.map p)⟦(1 : ℤ)⟧') ≫ a' =
      a' ≫ G.map ((q.map p)⟦(1 : ℤ)⟧') :=
    transport_naturality L G _ α hαnat hS' hS' i' i' ((q.map p)⟦(1 : ℤ)⟧')
  have hc : IsIso c := by
    refine cone_five_lemma hT hT' a a c d d hn₁ hn₂ ?_ ?_
    · change (L.map C.mor₃ ≫ (L.commShiftIso (1 : ℤ)).hom.app X) ≫ d =
        c ≫ G.map C.mor₃ ≫ (G.commShiftIso (1 : ℤ)).hom.app X
      dsimp only [d]
      simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
      rw [← Category.assoc, hn₃, Category.assoc]
    · change (L.map (q.map p))⟦(1 : ℤ)⟧' ≫ d = d ≫ (G.map (q.map p))⟦(1 : ℤ)⟧'
      exact shifted_transport_comm L G (q.map p) a' hn₄
  exact hc

end AlgebraicGeometry
```

### Sheaf.AlgebraicGeometry.FlatTelescopePullbackSumColimit

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Sheaf.AlgebraicGeometry.DerivedAdjoint
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-! # Pullback of the source coproduct in a flat telescope

Source: Stacks Tags 06YS and 06YJ, sum step of the telescope normalization plan.
(blueprint: lem-sc-flat-telescope-pullback-sum-colimit). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
namespace AlgebraicGeometry

private lemma coproduct_homotopy
    {C : Type*} [Category C] [Preadditive C] {I : Type*}
    [HasColimitsOfShape (Discrete I) C]
    (K : I → CochainComplex C ℤ) {L : CochainComplex C ℤ}
    (f g : ∐ K ⟶ L) (h : ∀ i, Homotopy (Sigma.ι K i ≫ f) (Sigma.ι K i ≫ g)) :
    Nonempty (Homotopy f g) := by
  let hc (n : ℤ) := isColimitOfPreserves
    (HomologicalComplex.eval C (ComplexShape.up ℤ) n) (coproductIsCoproduct K)
  let t (n m : ℤ) : Cocone
      (Discrete.functor K ⋙ HomologicalComplex.eval C (ComplexShape.up ℤ) n) :=
    { pt := L.X m
      ι := { app := fun i ↦ (h i.as).hom n m
             naturality := by
               rintro ⟨i⟩ ⟨j⟩ f
               obtain rfl := Discrete.eq_of_hom f
               simp } }
  let a (n m : ℤ) : (∐ K).X n ⟶ L.X m :=
    (hc n).desc (t n m)
  have ha (i : I) (n m : ℤ) : (Sigma.ι K i).f n ≫ a n m = (h i).hom n m := by
    exact (hc n).fac (t n m) ⟨i⟩
  refine ⟨{ hom := a, zero := ?_, comm := ?_ }⟩
  · intro n m hnm
    apply (hc n).hom_ext
    rintro ⟨i⟩
    simpa only [Functor.mapCocone_ι_app, Cofan.mk_ι_app, HomologicalComplex.eval_map,
      ha, comp_zero] using (h i).zero n m hnm
  · intro n
    apply (hc n).hom_ext
    rintro ⟨i⟩
    change (Sigma.ι K i).f n ≫ f.f n = _
    simp only [Functor.mapCocone_ι_app, Cofan.mk_ι_app, HomologicalComplex.eval_map,
      Preadditive.comp_add, dNext, prevD, AddMonoidHom.mk'_apply]
    rw [(Sigma.ι K i).comm_assoc, ha, ← Category.assoc, ha]
    exact (h i).comm n

private lemma derived_map_surjective
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (K L : CochainComplex C ℤ) [L.IsKInjective] :
    Function.Surjective (DerivedCategory.Q.map : (K ⟶ L) → _) := by
  intro f
  let e := DerivedCategory.quotientCompQhIso C
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ _).obj K) L).surjective
    (e.hom.app K ≫ f ≫ e.inv.app L)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  refine ⟨g, ?_⟩
  apply (cancel_mono (e.inv.app L)).1
  rw [DerivedCategory.quotientCompQhIso_inv_naturality, hg]
  simp [e]

private lemma derived_map_homotopy
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {K L : CochainComplex C ℤ} [L.IsKInjective] (f g : K ⟶ L)
    (h : DerivedCategory.Q.map f = DerivedCategory.Q.map g) :
    Nonempty (Homotopy f g) := by
  refine ⟨HomotopyCategory.homotopyOfEq f g ?_⟩
  apply (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ _).obj K) L).injective
  apply (cancel_mono ((DerivedCategory.quotientCompQhIso C).hom.app L)).1
  simp only [DerivedCategory.quotientCompQhIso_hom_naturality, h]


private theorem derived_coproduct
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Abelian.HasKInjectiveResolutions C] {I : Type*}
    [HasColimitsOfShape (Discrete I) C] (K : I → CochainComplex C ℤ) :
    Nonempty (IsColimit (Cofan.mk (DerivedCategory.Q.obj (∐ K))
      (fun i ↦ DerivedCategory.Q.map (Sigma.ι K i)))) := by
  classical
  have hu (X : DerivedCategory C)
      (a : ∀ i, DerivedCategory.Q.obj (K i) ⟶ X) :
      ∃! d : DerivedCategory.Q.obj (∐ K) ⟶ X,
        ∀ i, DerivedCategory.Q.map (Sigma.ι K i) ≫ d = a i := by
    obtain ⟨L, _, r, _, _⟩ :=
      Abelian.HasKInjectiveResolutions.exists_isKInjective
        (DerivedCategory.Q.objPreimage X)
    let e : X ≅ DerivedCategory.Q.obj L :=
      (DerivedCategory.Q.objObjPreimageIso X).symm ≪≫ asIso (DerivedCategory.Q.map r)
    choose f hf using fun i ↦ derived_map_surjective (K i) L (a i ≫ e.hom)
    let d := DerivedCategory.Q.map (Sigma.desc f) ≫ e.inv
    have hd (i : I) : DerivedCategory.Q.map (Sigma.ι K i) ≫ d = a i := by
      dsimp [d]
      rw [← Category.assoc, ← Functor.map_comp, Sigma.ι_desc, hf]
      simp
    refine ⟨d, hd, ?_⟩
    intro m hm
    apply (cancel_mono e.hom).1
    obtain ⟨g, hg⟩ := derived_map_surjective (∐ K) L (m ≫ e.hom)
    have he (i : I) :
        DerivedCategory.Q.map (Sigma.ι K i ≫ g) = DerivedCategory.Q.map (f i) := by
      rw [Functor.map_comp, hg, ← Category.assoc, hm, hf]
    have hhom := coproduct_homotopy K g (Sigma.desc f) (fun i ↦
      (derived_map_homotopy (Sigma.ι K i ≫ g) (Sigma.ι K i ≫ Sigma.desc f)
        (by simpa only [Sigma.ι_desc] using he i)).some)
    rw [← hg, DerivedCategory.Q_map_eq_of_homotopy _ hhom.some]
    simp [d]
  refine ⟨Cofan.IsColimit.mk _ (fun t ↦ (hu t.pt t.inj).choose) ?_ ?_⟩
  · intro t i
    exact (hu t.pt t.inj).choose_spec.1 i
  · intro t m hm
    exact (hu t.pt t.inj).choose_spec.2 m hm


/-- Derived pullback of a complex sum, and of its translate, gives the coproduct
of the corresponding stage images. No flatness or boundedness is required.

Source: Stacks Tag 07D9, Injectives, direct sums in derived categories, and Tag 079W,
Cohomology, derived pullback adjunction. Sum step of
lem-sc-flat-telescope-normalization-morphisms.

Proof. Sheaf modules have K-injective resolutions. Represent any target by a
K-injective complex. Each derived map from a stage lifts to a chain map into this
representative, by bijectivity of Qh on maps into K-injectives and surjectivity of
the homotopy quotient. The coproduct of complexes assembles these chain maps.
Two factorizations equal on all stages have homotopies on each stage; the degreewise
coproduct universal property assembles these into a homotopy on the sum. Thus Q of
the sum has the coproduct universal property, with the prescribed inclusions.
Derived pullback is left adjoint to derived direct image and preserves the cofan.
Transport along quotientCompQhIso to the homotopy-localization formulation.
For the translated cofan use the Qh shift comparison, preservation of coproducts
by the derived shift equivalence, and preservation by derived pullback again.
Zero stages and the zero category on an empty scheme are included.
(blueprint: lem-sc-flat-telescope-pullback-sum-colimit). -/
theorem flat_telescope_pullback_sum_colimit
    {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (E : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) :
    let q := HomotopyCategory.quotient
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)
    let L := DerivedCategory.Qh ⋙ derivedPullback f
    Nonempty (IsColimit (Cofan.mk (L.obj (q.obj (∐ E)))
      (fun n ↦ L.map (q.map (Sigma.ι E n))))) ∧
    Nonempty (IsColimit (Cofan.mk (L.obj ((q.obj (∐ E))⟦(1 : ℤ)⟧))
      (fun n ↦ L.map ((q.map (Sigma.ι E n))⟦(1 : ℤ)⟧')))) := by
  classical
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let F := derivedPullback f
  have : Abelian.HasKInjectiveResolutions A :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian
  have hQ := (derived_coproduct E).some
  have : PreservesColimit (Discrete.functor E) (DerivedCategory.Q : _ ⥤
      schemeDerivedCategory Y) :=
    preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct E)
      ((Cofan.isColimitMapCoconeEquiv DerivedCategory.Q E _).symm hQ)
  have : PreservesColimit (Discrete.functor E) (q ⋙ DerivedCategory.Qh) :=
    preservesColimit_of_natIso _ (DerivedCategory.quotientCompQhIso A).symm
  have : F.IsLeftAdjoint := (nonempty_derivedPullbackAdjunction f).some.isLeftAdjoint
  have hc := isColimitOfPreserves ((q ⋙ DerivedCategory.Qh) ⋙ F)
    (coproductIsCoproduct E)
  have hc₀ : IsColimit (Cofan.mk (F.obj (DerivedCategory.Qh.obj (q.obj (∐ E))))
      (fun n ↦ F.map (DerivedCategory.Qh.map (q.map (Sigma.ι E n))))) :=
    Cofan.isColimitMapCoconeEquiv _ E _ hc
  let S := shiftFunctor (HomotopyCategory A (ComplexShape.up ℤ)) (1 : ℤ)
  have : PreservesColimit (Discrete.functor E) (q ⋙ S ⋙ DerivedCategory.Qh) := by
    let S' := shiftFunctor (schemeDerivedCategory Y) (1 : ℤ)
    have : PreservesColimit (Discrete.functor E) ((q ⋙ DerivedCategory.Qh) ⋙ S') :=
      inferInstance
    exact preservesColimit_of_natIso _
      ((Functor.associator q S DerivedCategory.Qh) ≪≫
        Functor.isoWhiskerLeft q (DerivedCategory.Qh.commShiftIso (1 : ℤ)) ≪≫
        (Functor.associator q DerivedCategory.Qh S').symm).symm
  have hc' := isColimitOfPreserves ((q ⋙ S ⋙ DerivedCategory.Qh) ⋙ F)
    (coproductIsCoproduct E)
  refine ⟨⟨hc₀⟩, ⟨?_⟩⟩
  exact Cofan.isColimitMapCoconeEquiv _ E _ hc'

end AlgebraicGeometry
```

### Sheaf.AlgebraicGeometry.FlatTelescopeStageMapRefinement

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Sheaf.AlgebraicGeometry.FlatTelescopeStageMap

import Sheaf.AlgebraicGeometry.FlatTelescopeArrowDiagram
import Sheaf.Algebra.Homology.FlatTruncationTelescopeComparison

/-! # Refining a homotopy map to maps of flat towers

Source: the common-replacement argument in step 3 of the normalized telescope
comparison plan, Stacks Project Tags 06YS, 06YJ and 04VC.
(blueprint: lem-sc-flat-telescope-stage-map-refinement).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

private theorem telescope_shift_presentation (Y : Scheme.{u})
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hP : isFlatTelescope Y P) (k : ℤ) :
    ∃ P' : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
      isFlatTelescope Y P' ∧ Nonempty
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P' ≅
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)⟦k⟧) := by
  obtain ⟨E, t, hb, hf, rfl⟩ := hP
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let Q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let S := shiftFunctor (CochainComplex A ℤ) k
  let E' := fun n ↦ S.obj (E n)
  let t' := fun n ↦ S.map (t n)
  let φ := flatTelescopeDifferential E t
  let φ' := flatTelescopeDifferential E' t'
  let σ : (∐ E') ⟶ S.obj (∐ E) := Limits.sigmaComparison S E
  have hb' : ∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → Limits.IsZero ((E' n).X i) := by
    intro n
    obtain ⟨b, hb⟩ := hb n
    refine ⟨b - k, fun i hi ↦ ?_⟩
    change Limits.IsZero ((E n).X (i + k))
    exact hb (i + k) (by omega)
  have hf' : ∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E' n).X i) :=
    fun n i ↦ hf n (i + k)
  have hc : φ' ≫ σ = σ ≫ S.map φ := by
    dsimp [φ', φ, flatTelescopeDifferential]
    rw [Functor.map_sub, CategoryTheory.Functor.map_id, Preadditive.sub_comp,
      Preadditive.comp_sub, Category.id_comp, Category.comp_id]
    congr 1
    apply Limits.Sigma.hom_ext
    intro n
    rw [Limits.Sigma.ι_desc_assoc]
    change S.map (t n) ≫ Limits.Sigma.ι (fun n ↦ S.obj (E n)) (n + 1) ≫
        Limits.sigmaComparison S E = Limits.Sigma.ι (fun n ↦ S.obj (E n)) n ≫
        Limits.sigmaComparison S E ≫
          S.map (Limits.Sigma.desc (fun n ↦ t n ≫ Limits.Sigma.ι E (n + 1)))
    rw [Limits.ι_comp_sigmaComparison, Limits.ι_comp_sigmaComparison_assoc, ← S.map_comp,
      ← S.map_comp, Limits.Sigma.ι_desc]
  let m := CochainComplex.mappingCone.map φ' (S.map φ) σ σ hc
  have hσ : IsIso σ := by
    dsimp [σ]
    infer_instance
  have hm : IsIso (Q.map m) := by
    exact CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂
      (Q.mapTriangle.map (CochainComplex.mappingCone.triangleMap φ' (S.map φ) σ σ hc))
      (HomotopyCategory.mappingCone_triangleh_distinguished φ')
      (HomotopyCategory.mappingCone_triangleh_distinguished (S.map φ))
      (by exact inferInstanceAs (IsIso (Q.map σ)))
      (by exact inferInstanceAs (IsIso (Q.map σ)))
  refine ⟨CochainComplex.mappingCone φ', ⟨E', t', hb', hf', rfl⟩, ⟨?_⟩⟩
  exact asIso (Q.map m) ≪≫ (Q.mapIso (CochainComplex.mappingCone.shiftIso φ k)).symm ≪≫
    (Q.commShiftIso k).app _

private theorem telescope_presentation (Y : Scheme.{u})
    (X : HomotopyCategory
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
    (hX : flatTelescopeShiftRepresentative Y X) :
    ∃ P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
      isFlatTelescope Y P ∧
        Nonempty ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P ≅ X) := by
  obtain ⟨P, hP, h | h⟩ := hX
  · exact ⟨P, hP, ⟨eqToIso h⟩⟩
  · obtain ⟨P', hP', ⟨e⟩⟩ := telescope_shift_presentation Y P hP 1
    exact ⟨P', hP', ⟨e ≪≫ eqToIso h⟩⟩

private theorem stage_map_of_tower_map (Y : Scheme.{u})
    (E E' : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (t : ∀ n : ℕ, E n ⟶ E (n + 1)) (t' : ∀ n : ℕ, E' n ⟶ E' (n + 1))
    (a : ∀ n : ℕ, E n ⟶ E' n)
    (hb : ∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → Limits.IsZero ((E n).X i))
    (hf : ∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E n).X i))
    (hb' : ∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → Limits.IsZero ((E' n).X i))
    (hf' : ∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E' n).X i))
    (comm : flatTelescopeDifferential E t ≫ Limits.Sigma.map a =
      Limits.Sigma.map a ≫ flatTelescopeDifferential E' t')
    {X : HomotopyCategory
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)}
    (e : (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      (CochainComplex.mappingCone (flatTelescopeDifferential E' t')) ≅ X) :
    flatTelescopeStageMap Y
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (CochainComplex.mappingCone.map (flatTelescopeDifferential E t)
          (flatTelescopeDifferential E' t') (Limits.Sigma.map a)
          (Limits.Sigma.map a) comm) ≫ e.hom) := by
  let H := HomotopyCategory
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)
  refine ⟨E, E', t, t', a, hb, hf, hb', hf', comm, 0,
    (shiftFunctorZero H ℤ).app _, (shiftFunctorZero H ℤ).app _ ≪≫ e, ?_⟩
  simp only [Iso.trans_hom, Iso.app_hom, Iso.app_inv]
  rw [(shiftFunctorZero H ℤ).hom.naturality_assoc]
  simp

/-- A homotopy map between telescope representatives admits a common source
on which it is induced by maps of bounded-flat towers. This assertion contains
no pullback, tensorator, or normalized comparison.

Source: Stacks Project, Tags 06YS and 06YJ, common flat replacement, and Tag 04VC,
right fractions; this explicit tower refinement is the expansion of parent
step 3 rather than a literal assertion of those tags.

Proof. Choose flat-tower presentations of the two objects, with their given
possible one-fold translates. Lift the homotopy morphism to a cochain map.
Resolve the resulting arrow diagram by bounded-above flat truncation towers,
retaining the maps to both original diagrams. At a given truncation level use
a common flat resolution for the source and the pullback of the target
resolution along the arrow; the projections then give a commuting square.
Construct the next level resolving this square together with the previous
level, so the transition squares commute. Taking sums and their transition
cones gives a third flat telescope R and two model maps a and b. The source
augmentation is a quasi-isomorphism by the flat truncation telescope comparison.
Their composites represent the given arrow after localization. Apply the right
fraction equality criterion and refine the source once more to turn that
localized equality into equality in the homotopy category. Compose the two
source refinements; their quasi-isomorphisms compose, and the composite tower
maps are again tower maps. Shift the diagrams and transport by their original
homotopy isomorphisms to cover the translated presentations. Thus a;s=b in the
homotopy category, with a a quasi-isomorphism. For the zero map use the zero
arrow diagram; for the identity use its identical presentations. Empty schemes
have the unique zero diagrams, so no nonzero-object assumption is needed.
(blueprint: lem-sc-flat-telescope-stage-map-refinement). -/
theorem exists_flat_telescope_stage_map_refinement (Y : Scheme.{u})
    {X X' : HomotopyCategory
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)}
    (hX : flatTelescopeShiftRepresentative Y X)
    (hX' : flatTelescopeShiftRepresentative Y X') (s : X ⟶ X') :
    ∃ (R : HomotopyCategory
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
      (a : R ⟶ X) (b : R ⟶ X'),
      flatTelescopeShiftRepresentative Y R ∧
        HomotopyCategory.quasiIso
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ) a ∧
        flatTelescopeStageMap Y a ∧ flatTelescopeStageMap Y b ∧ a ≫ s = b := by
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let Q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  obtain ⟨P, hP, ⟨e⟩⟩ := telescope_presentation Y X hX
  obtain ⟨P', hP', ⟨e'⟩⟩ := telescope_presentation Y X' hX'
  obtain ⟨f, hf⟩ := Q.map_surjective (e.hom ≫ s ≫ e'.inv)
  obtain ⟨E₀, E₁, E₂, t₀, t₁, t₂, c, d, hb₀, hf₀, hb₁, hf₁, hb₂, hf₂,
    comm₁, comm₂, e₁, e₂, g, q, hq, hcompat, hinr, hinl, hgc, hgd⟩ :=
      exists_flat_telescope_arrow_diagram Y P P' hP hP' f
  let φ₀ := flatTelescopeDifferential E₀ t₀
  let φ₂ := flatTelescopeDifferential E₂ t₂
  let m₂ := CochainComplex.mappingCone.map φ₀ φ₂ (Limits.Sigma.map d) (Limits.Sigma.map d) comm₂
  have hg : QuasiIso g :=
    CochainComplex.quasiIso_flat_truncation_telescope P E₀ t₀ q hq hcompat g hinr hinl
  have hQg : W (Q.map g) := (HomotopyCategory.quotient_map_mem_quasiIso_iff g).2 hg
  refine ⟨Q.obj (CochainComplex.mappingCone φ₀), Q.map g ≫ e.hom,
    Q.map m₂ ≫ (e₂ ≪≫ e').hom, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨CochainComplex.mappingCone φ₀, ⟨E₀, t₀, hb₀, hf₀, rfl⟩, Or.inl rfl⟩
  · exact W.comp_mem _ _ hQg (W.of_isIso e.hom)
  · rw [hgc, Category.assoc]
    exact stage_map_of_tower_map Y E₀ E₁ t₀ t₁ c hb₀ hf₀ hb₁ hf₁ comm₁ (e₁ ≪≫ e)
  · exact stage_map_of_tower_map Y E₀ E₂ t₀ t₂ d hb₀ hf₀ hb₂ hf₂ comm₂ (e₂ ≪≫ e')
  · have hgd' : Q.map g ≫ Q.map f = Q.map m₂ ≫ e₂.hom := hgd
    rw [hf] at hgd'
    simpa only [Iso.trans_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      using congrArg (fun k ↦ k ≫ e'.hom) hgd'

end AlgebraicGeometry
```

### Sheaf.AlgebraicGeometry.FlatTelescopeStageNaturality

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Sheaf.AlgebraicGeometry.FlatTelescopeStageMap
import Sheaf.AlgebraicGeometry.FlatTelescopeStageMapRefinement

/-! # Naturality from flat telescope stage maps

Source: common-refinement cancellation in step 3 of
lem-sc-flat-telescope-bounded-normalization-extension. -/

@[expose] public section
set_option autoImplicit false
universe u w v v'
open CategoryTheory
namespace AlgebraicGeometry

/-- Stage naturality implies naturality for arbitrary maps between the indicated
representatives when the source functor factors through derived localization.

Source: step 3 of lem-sc-flat-telescope-bounded-normalization-extension,
Stacks Tags 06YS and 06YJ for the flat refinements, with the explicit refinement
statement supplied by lem-sc-flat-telescope-stage-map-refinement.

Proof. Refine a map s through a telescope R with stage maps a and b, where
 a is a quasi-isomorphism and a;s=b. Localization and then F send a to an
isomorphism. Precompose the desired equality with that invertible map.
Functoriality rewrites its left side using a;s=b, and stage naturality for
b and a identifies both sides. Cancel the invertible precomposition.
(blueprint: lem-sc-flat-telescope-stage-naturality). -/
theorem flat_telescope_stage_naturality
    {Y : Scheme.{u}} [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {D : Type v} [Category.{v'} D]
    (F : schemeDerivedCategory Y ⥤ D)
    (G : HomotopyCategory
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ) ⥤ D)
    (α : ∀ X : HomotopyCategory
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ),
      flatTelescopeShiftRepresentative Y X →
        ((DerivedCategory.Qh ⋙ F).obj X ⟶ G.obj X))
    (hα : ∀ (X X' : HomotopyCategory
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
      (hX : flatTelescopeShiftRepresentative Y X)
      (hX' : flatTelescopeShiftRepresentative Y X') (s : X ⟶ X'),
      flatTelescopeStageMap Y s →
        (DerivedCategory.Qh ⋙ F).map s ≫ α X' hX' = α X hX ≫ G.map s) :
    ∀ (X X' : HomotopyCategory
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
      (hX : flatTelescopeShiftRepresentative Y X)
      (hX' : flatTelescopeShiftRepresentative Y X') (s : X ⟶ X'),
      (DerivedCategory.Qh ⋙ F).map s ≫ α X' hX' = α X hX ≫ G.map s := by
  intro X X' hX hX' s
  obtain ⟨R, a, b, hR, ha, hstageA, hstageB, hab⟩ :=
    exists_flat_telescope_stage_map_refinement Y hX hX' s
  let L := DerivedCategory.Qh ⋙ F
  have : IsIso (DerivedCategory.Qh.map a) :=
    Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)) a ha
  have : IsIso (L.map a) := F.map_isIso (DerivedCategory.Qh.map a)
  apply (cancel_epi (L.map a)).1
  change L.map a ≫ (L.map s ≫ α X' hX') = L.map a ≫ (α X hX ≫ G.map s)
  calc
    L.map a ≫ (L.map s ≫ α X' hX') = L.map b ≫ α X' hX' := by
      rw [← Category.assoc, ← Functor.map_comp, hab]
    _ = α R hR ≫ G.map b := hα R X' hR hX' b hstageB
    _ = L.map a ≫ (α X hX ≫ G.map s) := by
      rw [← hab, G.map_comp, ← Category.assoc, ← hα R X hR hX a hstageA,
        Category.assoc]

end AlgebraicGeometry
```

### Sheaf.AlgebraicGeometry.FlatTelescopeSumComparisonIsIso

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.FlatTelescopeStageMap
public import Sheaf.AlgebraicGeometry.BoundedFlatModelNormalization
import Sheaf.AlgebraicGeometry.FlatTelescopeSumModels
import Sheaf.AlgebraicGeometry.FlatComparisonPreservesCountableCoproducts

/-! # The normalized comparison on sums of bounded-flat stages

Source: the finite-partial-sum argument of step 1 of
lem-sc-flat-telescope-normalization-unshifted-is-iso, expanding Stacks Tags 06YS and 06YJ.
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
namespace AlgebraicGeometry

/-- The sum of bounded-flat stages has a literal telescope representative on which
the comparison is invertible.
This concerns the sum of the stages, not the cone of their transition map.
No transition maps, normalized shifted-unit isomorphism, or shift equation are inputs.

Source: step 1 of lem-sc-flat-telescope-normalization-unshifted-is-iso;
Stacks Tags 06YS and 06YJ, the sum part of the telescope argument, expanded by the agent.

Proof. Let B_n be the finite sum of E_0,...,E_n and let its transition be the split
inclusion. The finite maximum of the upper bounds bounds B_n, and finite sums of
flat modules are flat. Define R to be the cone of one minus transition on the sum
of the B_n. The split telescope augmentation R -> sum E is a homotopy equivalence:
on each E_j summand the tail of the partial-sum tower is the constant identity tower;
write D_j = sum over n >= j of E_j. The augmentation D_j -> E_j sums
the coordinates and has a section into the first coordinate. One minus successor
is an isomorphism from D_j to the augmentation kernel: its inverse takes finite
partial sums, whose tail vanishes because the input coordinates sum to zero.
All these maps commute with the differentials. The split sequence therefore
identifies its cone with E_j plus a contractible cone of an identity. Taking
the direct sum of these splittings gives the required cochain homotopy equivalence.
Thus the homotopy quotient of sum E is isomorphic to qR.
Represent each bounded E_j by its constant identity telescope. Its terms and cone
remain bounded above and flat, since countable sums preserve flatness and a cone's
terms are finite sums. It satisfies the bounded normalization hypothesis. Its augmentation
is a homotopy equivalence to E_j. Transport alpha through these isomorphisms.
Naturality makes this transport independent of the presentation and intertwines every inclusion.
The functors Qh, derived pullback, and termwise tensor pullback preserve the relevant
countable coproducts: localization uses exact coproducts, derived pullback is a left
adjoint, and tensor pullback is a left adjoint. The coproduct universal property
therefore identifies the transported alpha on sum E with the direct sum of its
invertible stage components. Transfer the resulting isomorphism along the split telescope
augmentation to alpha at qR. The construction also covers the zero tower
and the empty scheme. No uniform upper bound on all E_n is used.
(blueprint: lem-sc-flat-telescope-sum-comparison-is-iso). -/
theorem exists_flat_telescope_sum_comparison_isIso
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    [(Scheme.Modules.tensorPullback f).Additive]
    (α : ∀ X : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ),
        flatTelescopeShiftRepresentative Y X →
          ((DerivedCategory.Qh ⋙ derivedPullback f).obj X ⟶
            ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
              (DerivedCategory.Qh : HomotopyCategory
                (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                schemeDerivedCategory Z)).obj X))
    (hαnat : (∀ (X X' : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
          (hX : flatTelescopeShiftRepresentative Y X) (hX' : flatTelescopeShiftRepresentative Y X')
          (s : X ⟶ X'),
          (DerivedCategory.Qh ⋙ derivedPullback f).map s ≫ (α X' hX') =
            (α X hX) ≫
              ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
                (DerivedCategory.Qh : HomotopyCategory
                  (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                  schemeDerivedCategory Z)).map s))
    (hαbounded : ∀ (X : HomotopyCategory
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
      (hX : flatTelescopeShiftRepresentative Y X),
      boundedFlatShiftRepresentative Y X → IsIso (α X hX))
    (E : ℕ → CochainComplex
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hb : ∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((E n).X i))
    (hf : ∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E n).X i)) :
    ∃ (R : CochainComplex
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
      (hR : isFlatTelescope Y R),
      Nonempty ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (∐ E) ≅
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj R) ∧
      IsIso (α ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj R)
        ⟨R, hR, Or.inl rfl⟩) := by
  classical
  obtain ⟨R, hR, T, hT, s, e, hTb, hc⟩ := exists_flat_telescope_sum_models Y E hb hf
  let q := HomotopyCategory.quotient
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)
  let L := DerivedCategory.Qh ⋙ derivedPullback f
  let G := (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    (DerivedCategory.Qh : HomotopyCategory
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
      schemeDerivedCategory Z)
  let hR' : flatTelescopeShiftRepresentative Y (q.obj R) := ⟨R, hR, Or.inl rfl⟩
  let hT' (n : ℕ) : flatTelescopeShiftRepresentative Y (q.obj (T n)) :=
    ⟨T n, hT n, Or.inl rfl⟩
  obtain ⟨hL, hG⟩ := flat_comparison_preserves_countable_coproducts f
  let : PreservesColimitsOfShape (Discrete ℕ) L := hL
  let : PreservesColimitsOfShape (Discrete ℕ) G := hG
  have cL : IsColimit (Cofan.mk (L.obj (q.obj R)) (fun n ↦ L.map (s n))) :=
    isColimitCofanMkObjOfIsColimit L _ _ hc.some
  have cG : IsColimit (Cofan.mk (G.obj (q.obj R)) (fun n ↦ G.map (s n))) :=
    isColimitCofanMkObjOfIsColimit G _ _ hc.some
  let a := α (q.obj R) hR'
  let b (n : ℕ) := α (q.obj (T n)) (hT' n)
  have (n : ℕ) : IsIso (b n) := hαbounded _ (hT' n) (hTb n)
  have hn (n : ℕ) : L.map (s n) ≫ a = b n ≫ G.map (s n) :=
    hαnat _ _ (hT' n) hR' (s n)
  let d : G.obj (q.obj R) ⟶ L.obj (q.obj R) :=
    Cofan.IsColimit.desc cG (fun n ↦ inv (b n) ≫ L.map (s n))
  have hd (n : ℕ) : G.map (s n) ≫ d = inv (b n) ≫ L.map (s n) :=
    Cofan.IsColimit.fac cG _ n
  have had : a ≫ d = 𝟙 _ := by
    apply Cofan.IsColimit.hom_ext cL
    intro n
    change L.map (s n) ≫ (a ≫ d) = L.map (s n) ≫ 𝟙 _
    rw [← Category.assoc, hn, Category.assoc, hd]
    simp
  have hda : d ≫ a = 𝟙 _ := by
    apply Cofan.IsColimit.hom_ext cG
    intro n
    change G.map (s n) ≫ (d ≫ a) = G.map (s n) ≫ 𝟙 _
    rw [← Category.assoc, hd, Category.assoc, hn]
    simp
  refine ⟨R, hR, e, ?_⟩
  exact ⟨⟨d, had, hda⟩⟩

end AlgebraicGeometry
```

### Sheaf.AlgebraicGeometry.FlatTelescopeSumModels

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Sheaf.AlgebraicGeometry.FlatTelescopeStageMap
public import Sheaf.AlgebraicGeometry.BoundedFlatModelNormalization
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct

/-! # Literal telescope models for a countable coproduct

Source: steps 1--2 of lem-sc-flat-telescope-sum-comparison-is-iso, expanding
Stacks Tags 06YS and 06YJ. (blueprint: lem-sc-flat-telescope-sum-models).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

section PartialSums

variable {C : Type*} [Category C] [Preadditive C]
  [HasBinaryBiproducts C] [HasCountableCoproducts C]

private noncomputable def partialSum (E : ℕ → C) : ℕ → C
  | 0 => E 0
  | n + 1 => partialSum E n ⊞ E (n + 1)

private noncomputable def partialSumAug (E : ℕ → C) : ∀ n, partialSum E n ⟶ ∐ E
  | 0 => Sigma.ι E 0
  | n + 1 => biprod.desc (partialSumAug E n) (Sigma.ι E (n + 1))

private noncomputable def partialSumLast (E : ℕ → C) : ∀ n, E n ⟶ partialSum E n
  | 0 => 𝟙 _
  | _ + 1 => biprod.inr

private noncomputable def partialSumStep (E : ℕ → C) (n : ℕ) :
    partialSum E n ⟶ partialSum E (n + 1) := biprod.inl

private noncomputable def partialSumLeft (E : ℕ → C) :
    ∀ n, partialSum E n ⟶ ∐ partialSum E
  | 0 => 0
  | n + 1 => biprod.fst ≫ (partialSumLeft E n - Sigma.ι (partialSum E) n)

private noncomputable def partialSumDelta (E : ℕ → C) :
    (∐ partialSum E) ⟶ ∐ partialSum E :=
  𝟙 _ - Sigma.desc (fun n ↦ partialSumStep E n ≫ Sigma.ι (partialSum E) (n + 1))

private lemma partialSumDelta_ι (E : ℕ → C) (n : ℕ) :
    Sigma.ι (partialSum E) n ≫ partialSumDelta E =
      Sigma.ι (partialSum E) n - partialSumStep E n ≫
        Sigma.ι (partialSum E) (n + 1) := by
  simp [partialSumDelta, Preadditive.comp_sub]

private noncomputable def partialSumSequence (E : ℕ → C) : ShortComplex C :=
  ShortComplex.mk (partialSumDelta E) (Sigma.desc (partialSumAug E)) (by
    apply Sigma.hom_ext
    intro n
    rw [← Category.assoc, partialSumDelta_ι]
    simp [partialSumStep, partialSumAug, Preadditive.sub_comp, Category.assoc])

set_option backward.isDefEq.respectTransparency false in
private noncomputable def partialSumSplitting (E : ℕ → C) :
    (partialSumSequence E).Splitting where
  r := Sigma.desc (partialSumLeft E)
  s := Sigma.desc (fun n ↦ partialSumLast E n ≫ Sigma.ι (partialSum E) n)
  f_r := by
    change partialSumDelta E ≫ Sigma.desc (partialSumLeft E) = 𝟙 _
    apply Sigma.hom_ext
    intro n
    rw [← Category.assoc, partialSumDelta_ι]
    simp only [Preadditive.sub_comp, Category.assoc, Sigma.ι_desc, Category.comp_id]
    change partialSumLeft E n - biprod.inl ≫
      (biprod.fst ≫ (partialSumLeft E n - Sigma.ι (partialSum E) n)) = _
    simp only [← Category.assoc, biprod.inl_fst, Category.id_comp, sub_sub_cancel]
  s_g := by
    change (Sigma.desc fun n ↦ partialSumLast E n ≫ Sigma.ι (partialSum E) n) ≫
      Sigma.desc (partialSumAug E) = 𝟙 _
    apply Sigma.hom_ext
    intro n
    cases n <;> simp [partialSumLast, partialSumAug, Category.assoc]
  id := by
    change Sigma.desc (partialSumLeft E) ≫ partialSumDelta E +
      Sigma.desc (partialSumAug E) ≫
        Sigma.desc (fun n ↦ partialSumLast E n ≫ Sigma.ι (partialSum E) n) =
      𝟙 (∐ partialSum E)
    apply Sigma.hom_ext
    intro n
    simp only [Preadditive.comp_add, ← Category.assoc, Sigma.ι_desc, Category.comp_id]
    induction n with
    | zero => simp [partialSumLeft, partialSumAug, partialSumLast]
    | succ n ih =>
      apply biprod.hom_ext'
      · simp only [Preadditive.comp_add, partialSumLeft, partialSumAug, Category.assoc,
          biprod.inl_fst_assoc, biprod.inl_desc_assoc, Preadditive.sub_comp]
        rw [sub_add_eq_add_sub, ih, partialSumDelta_ι]
        simp [partialSumStep]
      · simp [partialSumLeft, partialSumAug, partialSumLast,
          Preadditive.comp_add, Category.assoc]

private noncomputable def constantLeft (X : C) : ℕ → (X ⟶ ∐ fun _ : ℕ ↦ X)
  | 0 => 0
  | n + 1 => constantLeft X n - Sigma.ι (fun _ : ℕ ↦ X) n

private noncomputable def constantDelta (X : C) :
    (∐ fun _ : ℕ ↦ X) ⟶ ∐ fun _ : ℕ ↦ X :=
  𝟙 _ - Sigma.desc (fun n : ℕ ↦ Sigma.ι (fun _ : ℕ ↦ X) (n + 1))

omit [HasBinaryBiproducts C] in
private lemma constantDelta_ι (X : C) (n : ℕ) :
    Sigma.ι (fun _ : ℕ ↦ X) n ≫ constantDelta X =
      Sigma.ι (fun _ : ℕ ↦ X) n - Sigma.ι (fun _ : ℕ ↦ X) (n + 1) := by
  simp [constantDelta, Preadditive.comp_sub]

private noncomputable def constantSequence (X : C) : ShortComplex C :=
  ShortComplex.mk (constantDelta X) (Sigma.desc (fun _ : ℕ ↦ 𝟙 X)) (by
    apply Sigma.hom_ext
    intro n
    rw [← Category.assoc, constantDelta_ι]
    simp [Preadditive.sub_comp])

private noncomputable def constantSplitting (X : C) : (constantSequence X).Splitting where
  r := Sigma.desc (constantLeft X)
  s := Sigma.ι (fun _ : ℕ ↦ X) 0
  f_r := by
    change constantDelta X ≫ Sigma.desc (constantLeft X) = 𝟙 _
    apply Sigma.hom_ext
    intro n
    rw [← Category.assoc, constantDelta_ι]
    simp [Preadditive.sub_comp, constantLeft]
  s_g := by
    change Sigma.ι (fun _ : ℕ ↦ X) 0 ≫ Sigma.desc (fun _ : ℕ ↦ 𝟙 X) = 𝟙 _
    simp
  id := by
    change Sigma.desc (constantLeft X) ≫ constantDelta X +
      Sigma.desc (fun _ : ℕ ↦ 𝟙 X) ≫ Sigma.ι (fun _ : ℕ ↦ X) 0 = 𝟙 _
    apply Sigma.hom_ext
    intro n
    simp only [Preadditive.comp_add, ← Category.assoc, Sigma.ι_desc,
      Category.id_comp, Category.comp_id]
    induction n with
    | zero => simp [constantLeft]
    | succ n ih =>
      simp only [constantLeft, Preadditive.sub_comp]
      rw [sub_add_eq_add_sub, ih, constantDelta_ι, sub_sub_cancel]

end PartialSums

section SplitCone

variable {C : Type*} [Category C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

private noncomputable def splitConeIso (S : ShortComplex (CochainComplex C ℤ))
    (σ : S.Splitting) :
    (HomotopyCategory.quotient C (.up ℤ)).obj (CochainComplex.mappingCone S.f) ≅
      (HomotopyCategory.quotient C (.up ℤ)).obj S.X₃ := by
  let τ (n : ℤ) := σ.map (HomologicalComplex.eval C (.up ℤ) n)
  let T := CochainComplex.trianglehOfDegreewiseSplit S τ
  have hT : T ∈ distTriang _ :=
    (HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit T).2
      ⟨S, τ, ⟨Iso.refl _⟩⟩
  exact CategoryTheory.Pretriangulated.Triangle.π₃.mapIso
    (CategoryTheory.Pretriangulated.isoTriangleOfIso₁₂
      (CochainComplex.mappingCone.triangleh S.f) T
      (HomotopyCategory.mappingCone_triangleh_distinguished S.f) hT
      (Iso.refl _) (Iso.refl _) (by simp [T, CochainComplex.mappingCone.triangleh]; rfl))

end SplitCone

private theorem flatOfIso {Y : Scheme.{u}}
    {M N : SheafOfModules.{u} (moduleRings Y.toRingedSpace)}
    (e : M ≅ N) (hN : SheafOfModules.IsFlat N) : SheafOfModules.IsFlat M := by
  let := SheafOfModules.monoidalCategory Y.sheaf
  change exactFunctor _ _ (MonoidalCategory.tensorRight N) at hN
  change exactFunctor _ _ (MonoidalCategory.tensorRight M)
  exact ObjectProperty.prop_of_iso _
    ((MonoidalCategory.curriedTensor _).flip.mapIso e.symm) hN

private theorem flatSum {Y : Scheme.{u}} {I : Type}
    (M : I → SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    (hM : ∀ j, SheafOfModules.IsFlat (M j)) : SheafOfModules.IsFlat (∐ M) := by
  have h := SheafOfModules.isFlat_coproduct Y.sheaf
    (fun j : ULift.{u} I ↦ M j.down) (fun j ↦ hM j.down)
  exact flatOfIso (Limits.Sigma.reindex (Equiv.ulift : ULift.{u} I ≃ I) M).symm h

private theorem flatBiprod {Y : Scheme.{u}}
    {M N : SheafOfModules.{u} (moduleRings Y.toRingedSpace)}
    (hM : SheafOfModules.IsFlat M) (hN : SheafOfModules.IsFlat N) :
    SheafOfModules.IsFlat (M ⊞ N) := by
  apply flatOfIso (biprod.isoCoprod M N)
  exact flatSum _ (fun j ↦ by
    cases j
    · exact hM
    · exact hN)

private theorem flatComplexSum {Y : Scheme.{u}} {I : Type}
    (E : I → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hf : ∀ n i, SheafOfModules.IsFlat ((E n).X i)) (i : ℤ) :
    SheafOfModules.IsFlat ((∐ E).X i) := by
  exact flatOfIso
    (PreservesCoproduct.iso (HomologicalComplex.eval _ (.up ℤ) i) E)
    (flatSum _ (fun n ↦ hf n i))

private theorem zeroComplexSum {C : Type*} [Category C] [Preadditive C]
    {I : Type} [HasColimitsOfShape (Discrete I) C]
    (E : I → CochainComplex C ℤ) (i : ℤ) (hi : ∀ n, IsZero ((E n).X i)) :
    IsZero ((∐ E).X i) := by
  have hc := (Cofan.isColimitMapCoconeEquiv (HomologicalComplex.eval C (.up ℤ) i)
    E (Cofan.mk (∐ E) (Sigma.ι E))) (isColimitOfPreserves
      (HomologicalComplex.eval C (.up ℤ) i) (coproductIsCoproduct E))
  rw [IsZero.iff_id_eq_zero]
  apply Cofan.IsColimit.hom_ext hc
  intro n
  exact (hi n).eq_of_src _ _

private theorem partialSumBounded {Y : Scheme.{u}}
    (E : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hb : ∀ n, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((E n).X i)) :
    ∀ n, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((partialSum E n).X i) := by
  intro n
  induction n with
  | zero => exact hb 0
  | succ n ih =>
    obtain ⟨b, hbN⟩ := ih
    obtain ⟨c, hc⟩ := hb (n + 1)
    refine ⟨max b c, fun i hi ↦ ?_⟩
    apply (Functor.mapBiprod (HomologicalComplex.eval _ (.up ℤ) i)
      (partialSum E n) (E (n + 1))).isZero_iff.2
    exact (biprod_isZero_iff _ _).2
      ⟨hbN i (lt_of_le_of_lt (le_max_left _ _) hi),
        hc i (lt_of_le_of_lt (le_max_right _ _) hi)⟩

private theorem partialSumFlat {Y : Scheme.{u}}
    (E : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hf : ∀ n i, SheafOfModules.IsFlat ((E n).X i)) :
    ∀ n i, SheafOfModules.IsFlat ((partialSum E n).X i) := by
  intro n
  induction n with
  | zero => exact hf 0
  | succ n ih =>
    intro i
    exact flatOfIso
      (Functor.mapBiprod (HomologicalComplex.eval _ (.up ℤ) i)
        (partialSum E n) (E (n + 1))) (flatBiprod (ih i) (hf (n + 1) i))

section HomotopyCoproduct

variable {C : Type*} [Category C] [Preadditive C] [HasCountableCoproducts C]

-- Assemble homotopies using the degreewise coproduct universal property.
private lemma sumHomotopy (K : ℕ → CochainComplex C ℤ) {L : CochainComplex C ℤ}
    (f g : ∐ K ⟶ L) (h : ∀ i, Homotopy (Sigma.ι K i ≫ f) (Sigma.ι K i ≫ g)) :
    Nonempty (Homotopy f g) := by
  let hc (n : ℤ) := isColimitOfPreserves
    (HomologicalComplex.eval C (.up ℤ) n) (coproductIsCoproduct K)
  let t (n m : ℤ) : Cocone (Discrete.functor K ⋙ HomologicalComplex.eval C (.up ℤ) n) :=
    { pt := L.X m
      ι := { app := fun i ↦ (h i.as).hom n m
             naturality := by
               rintro ⟨i⟩ ⟨j⟩ f
               obtain rfl := Discrete.eq_of_hom f
               simp } }
  let a (n m : ℤ) : (∐ K).X n ⟶ L.X m := (hc n).desc (t n m)
  have ha (i : ℕ) (n m : ℤ) : (Sigma.ι K i).f n ≫ a n m = (h i).hom n m :=
    (hc n).fac (t n m) ⟨i⟩
  refine ⟨{ hom := a, zero := ?_, comm := ?_ }⟩
  · intro n m hnm
    apply (hc n).hom_ext
    rintro ⟨i⟩
    simpa only [Functor.mapCocone_ι_app, Cofan.mk_ι_app, HomologicalComplex.eval_map,
      ha, comp_zero] using (h i).zero n m hnm
  · intro n
    apply (hc n).hom_ext
    rintro ⟨i⟩
    change (Sigma.ι K i).f n ≫ f.f n = _
    simp only [Functor.mapCocone_ι_app, Cofan.mk_ι_app, HomologicalComplex.eval_map,
      Preadditive.comp_add, dNext, prevD, AddMonoidHom.mk'_apply]
    rw [(Sigma.ι K i).comm_assoc, ha, ← Category.assoc, ha]
    exact (h i).comm n

private noncomputable def quotientCoproduct (K : ℕ → CochainComplex C ℤ) :
    IsColimit (Cofan.mk ((HomotopyCategory.quotient C (.up ℤ)).obj (∐ K))
      (fun i ↦ (HomotopyCategory.quotient C (.up ℤ)).map (Sigma.ι K i))) := by
  classical
  let q := HomotopyCategory.quotient C (.up ℤ)
  have hu (X : HomotopyCategory C (.up ℤ)) (a : ∀ i, q.obj (K i) ⟶ X) :
      ∃! d : q.obj (∐ K) ⟶ X, ∀ i, q.map (Sigma.ι K i) ≫ d = a i := by
    obtain ⟨J, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    choose f hf using fun i ↦ q.map_surjective (a i)
    refine ⟨q.map (Sigma.desc f), ?_, ?_⟩
    · intro i
      rw [← Functor.map_comp, Sigma.ι_desc, hf]
    · intro m hm
      obtain ⟨g, rfl⟩ := q.map_surjective m
      have h (i : ℕ) : Homotopy (Sigma.ι K i ≫ g) (Sigma.ι K i ≫ Sigma.desc f) :=
        HomotopyCategory.homotopyOfEq _ _ (by
          rw [Sigma.ι_desc, Functor.map_comp, hm, hf])
      exact HomotopyCategory.eq_of_homotopy _ _ (sumHomotopy K g (Sigma.desc f) h).some
  exact Cofan.IsColimit.mk _ (fun t ↦ (hu t.pt t.inj).choose)
    (fun t i ↦ (hu t.pt t.inj).choose_spec.1 i)
    (fun t m hm ↦ (hu t.pt t.inj).choose_spec.2 m hm)

end HomotopyCoproduct

private noncomputable def transportCoproduct {C : Type*} [Category C]
    {E T : ℕ → C} {S R : C} (j : ∀ n, E n ⟶ S)
    (h : IsColimit (Cofan.mk S j)) (e : S ≅ R) (a : ∀ n, T n ≅ E n) :
    IsColimit (Cofan.mk R (fun n ↦ (a n).hom ≫ j n ≫ e.hom)) := by
  refine Cofan.IsColimit.mk _
    (fun c ↦ e.inv ≫ Cofan.IsColimit.desc h (fun n ↦ (a n).inv ≫ c.inj n)) ?_ ?_
  · intro c n
    dsimp only [cofan_mk_inj]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [show j n ≫ Cofan.IsColimit.desc h (fun n ↦ (a n).inv ≫ c.inj n) =
      (a n).inv ≫ c.inj n from Cofan.IsColimit.fac h _ n]
    simp
  · intro c m hm
    apply (cancel_epi e.hom).1
    simp only [Iso.hom_inv_id_assoc]
    apply Cofan.IsColimit.hom_ext h
    intro n
    change j n ≫ (e.hom ≫ m) = _
    rw [Cofan.IsColimit.fac]
    apply (cancel_epi (a n).hom).1
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, cofan_mk_inj] using hm n

private theorem constantConeBounded {Y : Scheme.{u}}
    (E : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hb : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (E.X i)) :
    ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((CochainComplex.mappingCone (constantDelta E)).X i) := by
  obtain ⟨b, hb⟩ := hb
  refine ⟨b, fun i hi ↦ ?_⟩
  rw [CochainComplex.mappingCone.isZero_X_iff]
  exact ⟨zeroComplexSum _ _ (fun _ ↦ hb (i + 1) (by omega)),
    zeroComplexSum _ _ (fun _ ↦ hb i hi)⟩

private theorem constantConeFlat {Y : Scheme.{u}}
    (E : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hf : ∀ i, SheafOfModules.IsFlat (E.X i)) (i : ℤ) :
    SheafOfModules.IsFlat ((CochainComplex.mappingCone (constantDelta E)).X i) := by
  apply flatOfIso
    (HomologicalComplex.homotopyCofiber.XIsoBiprod (constantDelta E) i (i + 1) rfl)
  exact flatBiprod (flatComplexSum _ (fun _ ↦ hf) (i + 1))
    (flatComplexSum _ (fun _ ↦ hf) i)

-- Preserve the original existential witness names in the statement.
set_option linter.unusedVariables false in
/-- A sum of individually bounded flat complexes admits a literal telescope model
and a coproduct cofan whose summands are bounded literal telescope models.

Source: steps 1--2 of lem-sc-flat-telescope-sum-comparison-is-iso, expanding
Stacks Tags 06YS and 06YJ.

Proof. Put B_n = E_0 + ... + E_n, with the split inclusion into B_(n+1),
and let R be the mapping cone of one minus transition on the coproduct of B_n.
Each B_n has flat terms and is bounded by the finite maximum of its stage bounds.
Reindex the double coproduct by pairs (n,j) with j <= n. For each j its contribution
is the constant identity tower on E_j, starting at n=j. The augmentation sums the
coordinates, and the section inserts into the first coordinate. One minus successor
identifies the direct sum with the augmentation kernel: the inverse sends a
zero-sum finite sequence to its finite partial sums. Its tail vanishes precisely
because the input sums to zero. These operations commute with differentials.
Equivalently, on the n-th tail coordinate define the retraction of one minus
successor by minus the sum of the preceding coordinate inclusions. This sum is
finite on each input summand, so the coproduct universal property defines a
cochain map without any choice of lifts. The retraction identities telescope:
delta followed by retraction is identity; retraction followed by delta plus
augmentation followed by section is identity. The split cone is therefore E_j
plus a contractible identity cone. Sum these
splittings to obtain q(sum E) isomorphic to qR.
For each j let T_j be the same identity-tower cone on E_j. Its terms are sums of
flat terms and it is bounded above by the bound of E_j increased by one.
The same splitting gives qT_j isomorphic to qE_j. Compose its augmentation,
the j-th coprojection and the inverse augmentation of R to obtain the cofan legs.
The homotopy quotient preserves this coproduct: degreewise coproducts assemble
both chain maps and homotopies, so restriction to the summands gives a bijection
on homotopy classes into every target. Transport that universal property along
the displayed homotopy isomorphisms. This also proves the assertion for zero
complexes and the empty scheme; no uniform bound on j is used.
(blueprint: lem-sc-flat-telescope-sum-models). -/
theorem exists_flat_telescope_sum_models (Y : Scheme.{u})
    (E : ℕ → CochainComplex
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hb : ∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((E n).X i))
    (hf : ∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E n).X i)) :
    ∃ (R : CochainComplex
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
      (hR : isFlatTelescope Y R)
      (T : ℕ → CochainComplex
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
      (hT : ∀ n, isFlatTelescope Y (T n))
      (s : ∀ n, (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (T n) ⟶
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj R),
      Nonempty ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (∐ E) ≅
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj R) ∧
      (∀ n, boundedFlatShiftRepresentative Y
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (T n))) ∧
      Nonempty (IsColimit (Cofan.mk
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj R) s)) := by
  let q := HomotopyCategory.quotient
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ)
  let R := CochainComplex.mappingCone (partialSumDelta E)
  have hR : isFlatTelescope Y R :=
    ⟨partialSum E, partialSumStep E, partialSumBounded E hb, partialSumFlat E hf, rfl⟩
  let T (n : ℕ) := CochainComplex.mappingCone (constantDelta (E n))
  have hT (n : ℕ) : isFlatTelescope Y (T n) := by
    refine ⟨fun _ ↦ E n, fun _ ↦ 𝟙 _, fun _ ↦ hb n, fun _ ↦ hf n, ?_⟩
    simp only [Category.id_comp]
    rfl
  let eR : q.obj (∐ E) ≅ q.obj R :=
    (splitConeIso (partialSumSequence E) (partialSumSplitting E)).symm
  let a (n : ℕ) : q.obj (T n) ≅ q.obj (E n) :=
    splitConeIso (constantSequence (E n)) (constantSplitting (E n))
  refine ⟨R, hR, T, hT, fun n ↦ (a n).hom ≫ q.map (Sigma.ι E n) ≫ eR.hom,
    ⟨eR⟩, ?_, ⟨transportCoproduct _ (quotientCoproduct E) eR a⟩⟩
  intro n
  exact ⟨T n, constantConeBounded (E n) (hb n), constantConeFlat (E n) (hf n),
    Or.inl rfl⟩

end AlgebraicGeometry
```

### Sheaf.AlgebraicGeometry.FlatTelescopeTargetRefinement

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V4
-/
module

public import Sheaf.AlgebraicGeometry.FlatTelescopeStageMap
import Sheaf.AlgebraicGeometry.CompactFlatGeneratorTowerResolution
import Sheaf.AlgebraicGeometry.CompactFlatTelescopeBarEnlargement
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit

/-! # Refining one augmented tower against one flat telescope

Source: the finite-piece bar-enlargement argument of
`lem-sc-flat-telescope-arrow-bar-data`, with the source tower retained through a
levelwise quasi-isomorphism. Stacks Project 03EW, 077J and 06XX supply the resolving
class and bounded resolutions; the bar argument is an agent-written expansion.
(blueprint: lem-sc-flat-telescope-target-refinement).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex
namespace AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem isIso_split_cone_augmentation
    {C : Type*} [Category C] [Abelian C]
    (S : ShortComplex (CochainComplex C ℤ))
    (σ : ∀ k : ℤ,
      (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) k)).Splitting) :
    IsIso ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
      (CochainComplex.mappingCone.descShortComplex S)) := by
  -- The retractions give the degree -1 part of the cone homotopy.
  let γ : CochainComplex.HomComplex.Cochain S.X₂ (S.X₁⟦(1 : ℤ)⟧) (-1) :=
    CochainComplex.HomComplex.Cochain.mk (fun p q hpq ↦
      (σ p).r ≫ (S.X₁.XIsoOfEq (by omega : p = q + 1)).hom)
  have h : Homotopy
      (CochainComplex.mappingCone.descShortComplex S ≫ CochainComplex.homOfDegreewiseSplit S σ)
      (CochainComplex.mappingCone.triangle S.f).mor₃ := by
    refine CochainComplex.mappingCone.descHomotopy S.f _ _ 0 γ ?_ ?_
    · -- On the first cone summand, the retraction cancels the negative projection.
      ext p q hpq
      rw [CochainComplex.HomComplex.Cochain.comp_v _ _ (add_zero (-1)) p q q hpq (add_zero q),
        CochainComplex.HomComplex.Cochain.add_v, CochainComplex.HomComplex.Cochain.add_v,
        CochainComplex.HomComplex.δ_zero, CochainComplex.HomComplex.Cochain.zero_v,
        CochainComplex.HomComplex.Cochain.comp_v _ _ (zero_add (-1)) p p q (add_zero p) hpq,
        CochainComplex.HomComplex.Cochain.comp_v _ _ (add_zero (-1)) p q q hpq (add_zero q)]
      simp only [CochainComplex.HomComplex.Cochain.ofHom_v, HomologicalComplex.comp_f,
        CochainComplex.mappingCone.inl_v_descShortComplex_f_assoc, zero_comp, zero_add,
        CochainComplex.mappingCone.inl_v_triangle_mor₃_f]
      have hf := (σ p).f_r
      dsimp at hf
      dsimp [γ, CochainComplex.shiftFunctorObjXIso]
      rw [← Category.assoc, hf, Category.id_comp]
      simp [HomologicalComplex.XIsoOfEq]
    · -- On the second summand, expand g s = id - r f and use the chain-map identity.
      ext p
      simp only [CochainComplex.HomComplex.Cochain.ofHom_v, HomologicalComplex.comp_f,
        CochainComplex.mappingCone.inr_f_descShortComplex_f_assoc,
        CochainComplex.homOfDegreewiseSplit_f,
        CochainComplex.cocycleOfDegreewiseSplit, CochainComplex.HomComplex.Cocycle.mk_coe,
        CochainComplex.HomComplex.Cochain.mk_v,
        CochainComplex.HomComplex.Cochain.add_v, CochainComplex.mappingCone.inr_f_triangle_mor₃_f]
      rw [CochainComplex.HomComplex.δ_v (-1) 0 (by omega) γ p p (by omega) (p - 1) (p + 1) rfl rfl]
      dsimp [γ]
      simp only [Units.neg_smul, one_smul, Preadditive.comp_neg, Category.assoc, Category.comp_id,
        add_zero, HomologicalComplex.XIsoOfEq_hom_comp_d]
      have hg := (σ p).g_s
      have hf := (σ (p + 1)).f_r
      dsimp at hg hf
      rw [← Category.assoc, hg]
      simp only [Preadditive.sub_comp, Category.id_comp, Category.assoc, S.f.comm_assoc,
        hf, Category.comp_id]
      abel
  let Q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let φ : CochainComplex.mappingCone.triangleh S.f ⟶
      CochainComplex.trianglehOfDegreewiseSplit S σ :=
    { hom₁ := 𝟙 _
      hom₂ := 𝟙 _
      hom₃ := Q.map (CochainComplex.mappingCone.descShortComplex S)
      comm₁ := by simp
      comm₂ := by
        dsimp [Q]
        rw [← Functor.map_comp, CochainComplex.mappingCone.inr_descShortComplex]
        simp
      comm₃ := by
        have heq := HomotopyCategory.eq_of_homotopy _ _ h
        have heq' := congrArg
          (fun f ↦ f ≫ (Functor.commShiftIso Q (1 : ℤ)).hom.app S.X₁) heq.symm
        simpa [Q, Functor.map_comp, Category.assoc] using heq'  }
  exact CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂ φ
    (HomotopyCategory.mappingCone_triangleh_distinguished S.f)
    ((HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit _).2
      ⟨S, σ, ⟨Iso.refl _⟩⟩) (by dsimp [φ]; infer_instance) (by dsimp [φ]; infer_instance)

/-- A bounded flat tower augmented into one actual flat telescope can be refined,
levelwise by quasi-isomorphisms, to admit a strict map into a tower presenting that
one target up to homotopy. No truncation augmentations or second target are involved.

Source: finite-piece bar enlargement in the proof of
`lem-sc-flat-telescope-arrow-bar-data`; Stacks Project 03EW, 077J and 06XX.

Proof. First resolve the source tower by a generator-valued tower L with maps
v_n:L_n -> E_n. Take the resolving class to be sums of affine-open generators
j_{U!} O_U; 03EW supplies covers, and the bounded resolution argument underlying
077J applies to this class. At stage zero resolve the bounded-above complex E_0.
Suppose L_n and v_n are constructed. Form the bounded-above cone H of
L_n -> E_n -> E_(n+1), and choose a bounded-above generator resolution Q -> H.
Compose Q -> H -> L_n[1], and form its shifted cone L_(n+1). This realizes the
triangle L_n -> L_(n+1) -> Q -> L_n[1] with degreewise split first map and
cokernel Q. The triangle comparison with L_n -> E_(n+1) -> H -> L_n[1]
provides a map L_(n+1) -> E_(n+1) commuting up to homotopy with v_n;t_n.
Extend that homotopy degreewise along the split inclusion of L_n, and subtract
its boundary from the comparison map. The resulting map v_(n+1) commutes
strictly; it is a quasi-isomorphism by the triangle comparison since the other
two vertical maps are identity and Q -> H. No lifting through a sheaf epimorphism
is assumed. This is the cone induction of 06XX with E_(n+1) replacing a good
truncation; its final termwise-surjectivity addition is unnecessary here.
Choose the degreewise splittings so that old generator summands remain named.
Augment L_n into T by v_n;p_n. The upper bounds may increase with n, but any
finite initial segment has a common upper bound.

Each affine-open generator is compact for coproducts: its Hom functor is sections
on a quasi-compact affine open. A section has locally finite support in a sheaf
coproduct, hence finite support on that open. Close finite sets of named summands
of L_m under the differential upwards. Compactness gives finitely many new summands
at each step; boundedness above terminates the procedure. The resulting finite
subcomplexes have finitely many nonzero degrees. Let D_n be the filtered diagram
of such subcomplexes at stages m <= n, ordered by inclusion after transition.
Its colimit is L_n. Set R_n to the direct-sum total of the unnormalized bar diagram
of D_n, with simplicial degree p placed in cochain degree -p. The augmentation
c_n:R_n -> L_n -> E_n is a quasi-isomorphism. Indeed filtered colimits of module
sheaves are exact, so the horizontal augmented bar complex is exact; the common
upper bound at stage n makes each total diagonal finite after reindexing. The bar
inclusions give s_n and strictly satisfy s_n c_(n+1) = c_n t_n.

Write the supplied target as a telescope. Its finite cone blocks C_k use domain
indices <= k and codomain indices <= k+1. They are bounded above and flat, their
inclusions split degreewise, and their union is the target T. Each finite source
subcomplex maps into some C_k, because its finitely many compact generator terms
use only finitely many target summands. The factor is a chain map since C_k -> T
is monic. Adjoin the chain of C_k to the union D of the source diagrams, putting
an arrow x -> k exactly when the augmentation of x factors through C_k. The least
such k is monotone and is left adjoint to inclusion of the target chain. The unit
of this adjunction gives, by inserting its arrow in bar strings with alternating
signs, a bar homotopy equivalence with the target-chain bar construction.

Let F_n be the bar total of the full subdiagram on D_n and target indices <= n.
These terms are flat and bounded above. Inclusions define u and a:R -> F. Their
transition squares commute strictly, so their sum maps commute with 1-shift. The
union bar total has a degreewise split exact presentation by 1-shift on the sum
of the F_n: split the augmentation using each simplex's first stage, and solve
the finite-support recurrence for its kernel. The cone augmentation is a homotopy
equivalence by the split exact-sequence cone calculation. For the target chain,
compare its bar augmentation with the telescope augmentation: compare the bar
resolution of the constant right functor with its two-term representable resolution
by 1-shift. Both are projective resolutions, so successive lifts give comparison
maps and homotopies; tensor these with the diagram C_k.
Comparison homotopies use finite sums on each input, so totalization is legitimate.
Choose this comparison to lift identity on the augmented constant functor;
then tensoring makes its composite with the augmentation into T exactly the
bar augmentation. The telescope of the finite cone blocks maps homotopy
equivalently to T by the same split exact-sequence calculation. Thus the
canonical bar augmentation B(I) -> T itself is a homotopy equivalence: compose
with the target-chain inclusion, a homotopy equivalence by the unit-insertion
homotopy, and cancel that equivalence. Define r to be the canonical cone
augmentation Tel(F) -> B(I) -> T, rather than an arbitrary comparison map.
Its shifted restriction is zero and its unshifted restriction is the sum of
bar augmentations. Naturality gives the displayed equality with Sigma.desc(c_n;p_n).
Zero complexes and zero maps require no exception; include the zero subcomplex
as an initial source object when necessary. All witnesses are existential data.
(blueprint: lem-sc-flat-telescope-target-refinement). -/
theorem exists_flat_telescope_target_refinement (Y : Scheme.{u})
    (E : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (t : ∀ n : ℕ, E n ⟶ E (n + 1))
    (hb : ∀ n : ℕ, ∃ z : ℤ, ∀ i : ℤ, z < i → IsZero ((E n).X i))
    (hf : ∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E n).X i))
    (T : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hT : isFlatTelescope Y T) (p : ∀ n : ℕ, E n ⟶ T)
    (hp : ∀ n : ℕ, t n ≫ p (n + 1) = p n) :
    let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
    let Q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
    ∃ (R F : ℕ → CochainComplex A ℤ)
      (s : ∀ n : ℕ, R n ⟶ R (n + 1))
      (u : ∀ n : ℕ, F n ⟶ F (n + 1))
      (c : ∀ n : ℕ, R n ⟶ E n) (a : ∀ n : ℕ, R n ⟶ F n),
      (∀ n : ℕ, ∃ z : ℤ, ∀ i : ℤ, z < i → IsZero ((R n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((R n).X i)) ∧
      (∀ n : ℕ, ∃ z : ℤ, ∀ i : ℤ, z < i → IsZero ((F n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((F n).X i)) ∧
      (∀ n : ℕ, QuasiIso (c n)) ∧
      (∀ n : ℕ, s n ≫ c (n + 1) = c n ≫ t n) ∧
      (∀ n : ℕ, s n ≫ a (n + 1) = a n ≫ u n) ∧
      ∃ r : CochainComplex.mappingCone (flatTelescopeDifferential F u) ⟶ T,
        IsIso (Q.map r) ∧
        (CochainComplex.mappingCone.inl (flatTelescopeDifferential F u)).comp
          (Cochain.ofHom r) (add_zero _) = 0 ∧
        Limits.Sigma.map a ≫
            CochainComplex.mappingCone.inr (flatTelescopeDifferential F u) ≫ r =
          Sigma.desc (fun n : ℕ ↦ c n ≫ p n) := by
  have _hfE := hf
  obtain ⟨L, l, v, hbL, hv, hl, hsplit, hgen⟩ :=
    exists_compact_flat_generator_tower_resolution Y E t hb
  let pL : ∀ n : ℕ, L n ⟶ T := fun n ↦ v n ≫ p n
  have hpL (n : ℕ) : l n ≫ pL (n + 1) = pL n := by
    dsimp [pL]
    rw [← Category.assoc, hl n, Category.assoc, hp n]
  obtain ⟨R, F, s, u, d, a, hbR, hfR, hbF, hfF, hd, hs, ha, B, b, e, hzero, hsplitB, heiso, he⟩ :=
    exists_compact_flat_telescope_bar_enlargement Y L l hbL hsplit hgen T hT pL hpL
  classical
  let S := ShortComplex.mk (flatTelescopeDifferential F u) b hzero
  let σ (i : ℤ) := Classical.choice (hsplitB i)
  let rB := CochainComplex.mappingCone.descShortComplex S
  let r := rB ≫ e
  have hrB := isIso_split_cone_augmentation S σ
  have hr : IsIso ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map r) := by
    dsimp [r]
    rw [Functor.map_comp]
    have := heiso
    exact inferInstance
  have hz : (CochainComplex.mappingCone.inl (flatTelescopeDifferential F u)).comp
      (Cochain.ofHom r) (add_zero _) = 0 := by
    ext i j hij : 1
    rw [Cochain.comp_v _ _ (add_zero (-1)) i j j hij (add_zero j)]
    simp only [Cochain.ofHom_v, HomologicalComplex.comp_f, r]
    change (CochainComplex.mappingCone.inl S.f).v i j hij ≫
      (CochainComplex.mappingCone.descShortComplex S).f j ≫ e.f j = 0
    rw [CochainComplex.mappingCone.inl_v_descShortComplex_f_assoc,
      Limits.zero_comp]
  let c : ∀ n : ℕ, R n ⟶ E n := fun n ↦ d n ≫ v n
  have hc (n : ℕ) : QuasiIso (c n) := by
    have := hd n
    have := hv n
    dsimp [c]
    infer_instance
  have hsc (n : ℕ) : s n ≫ c (n + 1) = c n ≫ t n := by
    dsimp [c]
    rw [← Category.assoc, hs n, Category.assoc, hl n, ← Category.assoc]
  refine ⟨R, F, s, u, c, a, hbR, hfR, hbF, hfF, hc, hsc, ha, r, hr, hz, ?_⟩
  change Limits.Sigma.map a ≫
    CochainComplex.mappingCone.inr S.f ≫ rB ≫ e = _
  rw [← Category.assoc (CochainComplex.mappingCone.inr S.f) rB e]
  rw [show CochainComplex.mappingCone.inr S.f ≫ rB = b from
    CochainComplex.mappingCone.inr_descShortComplex S, he]
  apply Sigma.hom_ext
  intro n
  simp only [Sigma.ι_desc, c, pL, Category.assoc]

end AlgebraicGeometry
```

### Sheaf.AlgebraicGeometry.KFlatLocalizedConePresentation

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Sheaf.Algebra.Homology.KFlatResolution
import Mathlib.CategoryTheory.Localization.CalculusOfFractions

/-! # K-flat cone representatives of localized homotopy triangles

Source: Stacks Project, Tags 06YS and 06YJ, replacement by K-flat complexes
in the mapping-cone proof of derived pullback exactness.
(blueprint: lem-sc-kflat-localized-cone-presentation).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Pretriangulated
namespace AlgebraicGeometry

/-- A distinguished homotopy triangle becomes isomorphic, after localization, to
an explicit cone triangle of a morphism between K-flat complexes.

Source: Stacks Project, Tag 06YS, termwise surjective K-flat resolutions; Tag
06YJ, K-flat computation of derived pullback and its mapping-cone argument.
(blueprint: lem-sc-kflat-localized-cone-presentation).

Proof. Localize the given distinguished triangle. Resolve a representative of
its second object by a K-flat Q, obtaining an isomorphism eQ from the localization
of Q to that second object. Write its first arrow followed by eQ inverse as a
right fraction for the homotopy quasi-isomorphisms. Resolve the domain R of the
fraction by a K-flat P. Compose the resolution with the numerator and choose a
cochain representative p : P → Q of the resulting homotopy morphism. The
resolution and denominator become invertible after localization; their composite
gives eP from the localization of P to the first object. The right-fraction
identity gives the square between p and the original first arrow. Both triangles
are distinguished, so the triangulated axiom completing a square extends eP and
eQ to an isomorphism of triangles; the third component is invertible by the
five lemma. Take its inverse. No lifting property for K-flat objects is used.
The argument works for unbounded complexes, zero complexes and the empty scheme. -/
theorem exists_kFlat_localized_cone_presentation (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (T₀ : Triangle (HomotopyCategory
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)))
    (hT₀ : T₀ ∈ distTriang (HomotopyCategory
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))) :
    ∃ (P Q : CochainComplex
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) (p : P ⟶ Q),
      CochainComplex.IsKFlat (R := Y.sheaf) P ∧
      CochainComplex.IsKFlat (R := Y.sheaf) Q ∧
      Nonempty (DerivedCategory.Qh.mapTriangle.obj T₀ ≅
        DerivedCategory.Qh.mapTriangle.obj (CochainComplex.mappingCone.triangleh p))  := by
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let L : HomotopyCategory A (ComplexShape.up ℤ) ⥤ schemeDerivedCategory Y :=
    DerivedCategory.Qh
  let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  obtain ⟨B, hB⟩ := HomotopyCategory.quotient_obj_surjective T₀.obj₂
  obtain ⟨Q, t, hQ, _, ht, _⟩ := CochainComplex.exists_isKFlatResolution (R := Y.sheaf) B
  have ht' : W (q.map t) := (HomotopyCategory.quotient_map_mem_quasiIso_iff t).2 ht
  have : IsIso (L.map (q.map t)) := Localization.inverts L W _ ht'
  let eQ : L.obj (q.obj Q) ≅ (L.mapTriangle.obj T₀).obj₂ :=
    asIso (L.map (q.map t)) ≪≫ L.mapIso (eqToIso hB)
  obtain ⟨α, hα⟩ := Localization.exists_rightFraction L W
    ((L.mapTriangle.obj T₀).mor₁ ≫ eQ.inv)
  obtain ⟨R, hR⟩ := HomotopyCategory.quotient_obj_surjective α.X'
  obtain ⟨P, s, hP, _, hs, _⟩ := CochainComplex.exists_isKFlatResolution (R := Y.sheaf) R
  let r : q.obj P ⟶ α.X' := q.map s ≫ eqToHom hR
  have hr : W r := by
    have hs' := (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs
    exact W.comp_mem _ _ hs' (W.of_isIso (eqToHom hR))
  have : IsIso (L.map r) := Localization.inverts L W _ hr
  have : IsIso (L.map α.s) := Localization.inverts L W _ α.hs
  let eP : L.obj (q.obj P) ≅ (L.mapTriangle.obj T₀).obj₁ :=
    asIso (L.map r) ≪≫ asIso (L.map α.s)
  obtain ⟨p, hp⟩ := q.map_surjective (r ≫ α.f)
  refine ⟨P, Q, p, hP, hQ, ⟨?_⟩⟩
  apply Iso.symm
  refine isoTriangleOfIso₁₂ _ _
    (L.map_distinguished _ (HomotopyCategory.mappingCone_triangleh_distinguished p))
    (L.map_distinguished _ hT₀) eP eQ ?_
  change L.map (q.map p) ≫ eQ.hom = (L.map r ≫ L.map α.s) ≫ _
  rw [hp, L.map_comp]
  have h := α.map_s_comp_map L (Localization.inverts L W)
  rw [← hα] at h
  calc
    (L.map r ≫ L.map α.f) ≫ eQ.hom =
        L.map r ≫ (L.map α.s ≫
          ((L.mapTriangle.obj T₀).mor₁ ≫ eQ.inv)) ≫ eQ.hom := by
      rw [h]
      simp only [Category.assoc]
    _ = (L.map r ≫ L.map α.s) ≫ (L.mapTriangle.obj T₀).mor₁ := by
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end AlgebraicGeometry
```

### Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitAssociativity

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitIso
import Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShiftAssociator

/-! # Associativity of tensor with the translated unit

Source: Stacks Project, Tag 06YH, first-variable total tensor translation;
associativity calculation in the parent translated-unit plan.
(blueprint: lem-sc-scheme-canonical-shift-unit-associativity).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry

private theorem tensorShiftUnitCalculation {C : Type*} [Category* C]
    [MonoidalCategory C] [HasShift C ℤ]
    [∀ B : C, (tensorRight B).CommShift ℤ]
    (K M : C) (n : ℤ)
    (h : ((tensorRight (K ⊗ M)).commShiftIso n).hom.app (𝟙_ C) ≫
        (α_ (𝟙_ C) K M).inv⟦n⟧' =
      (α_ ((𝟙_ C)⟦n⟧) K M).inv ≫
        (((tensorRight K).commShiftIso n).hom.app (𝟙_ C)) ▷ M ≫
        ((tensorRight M).commShiftIso n).hom.app ((𝟙_ C) ⊗ K)) :
    ((tensorRight (K ⊗ M)).commShiftIso n).hom.app (𝟙_ C) ≫
        (λ_ (K ⊗ M)).hom⟦n⟧' =
      (α_ ((𝟙_ C)⟦n⟧) K M).inv ≫
        (((tensorRight K).commShiftIso n).hom.app (𝟙_ C) ≫
          (λ_ K).hom⟦n⟧') ▷ M ≫
        ((tensorRight M).commShiftIso n).hom.app K := by
  simp only [comp_whiskerRight, Category.assoc]
  have hn := (tensorRight M).commShiftIso_hom_naturality (λ_ K).hom n
  dsimp at hn
  rw [leftUnitor_tensor_hom, Functor.map_comp, ← Category.assoc, h]
  simp only [Category.assoc]
  rw [← hn]

/-- The first-variable canonical shift comparison is tensoring the translated-unit
comparison with the fixed factor, after reassociating. This is a tensor identity
on a single scheme; it makes no assertion about pullback or triangulated functors.
Source: Stacks Project, Tag 06YH, total tensor translation, and the associativity
calculation of the parent plan.
(blueprint: lem-sc-scheme-canonical-shift-unit-associativity).

Proof. On total tensor complexes use the structure sheaf concentrated in degree
zero as the unit. Its translate has its sole term in degree minus one. The
comparison c_K is the canonical first-variable shift comparison followed by the
translated left unitor. In the triple tensor total complex, reassociation sends
the summand with indices (-1,p,q) to that with the same indices. Applying c_K and
then translating K tensor M gives the same first-variable comparison as applying
c_(K tensor M) directly. The differential of the triple totalization has signs
1, (-1)^(-1), (-1)^(-1+p); the shift comparison on the two paths changes these
signs identically. Thus the component maps agree on each summand, and hence on
the total complex. Choose K-flat representatives and use associativity of the
localized tensor comparisons. Both expressions are natural in K and M and are
unchanged under quasi-isomorphisms of these representatives, so the equality
descends to the recorded tensor product on the derived category. Zero factors
and the empty scheme give the same identity of zero morphisms. -/
theorem schemeCanonicalShiftUnitIso_tensor (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (K M : schemeDerivedCategory X) :
    letI := schemeCanonicalTensorShift X
    letI : (tensorRight M).CommShift ℤ :=
      Functor.CommShift₂.commShiftFlipObj (h := .int) M
    (schemeCanonicalShiftUnitIso X (K ⊗ M)).hom =
      (α_ ((𝟙_ (schemeDerivedCategory X))⟦(1 : ℤ)⟧) K M).inv ≫
        (schemeCanonicalShiftUnitIso X K).hom ▷ M ≫
        ((tensorRight M).commShiftIso (1 : ℤ)).hom.app K := by
  let := schemeCanonicalTensorShift X
  let : ∀ B : schemeDerivedCategory X, (tensorRight B).CommShift ℤ :=
    fun B ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) B
  simpa only [schemeCanonicalShiftUnitIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom] using tensorShiftUnitCalculation K M (1 : ℤ)
      (schemeCanonicalTensorShift_associator X (𝟙_ (schemeDerivedCategory X)) K M 1)

end AlgebraicGeometry
```

### Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShiftAssociator

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShift
import Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShiftAssociatorKFlatOne
import Sheaf.Algebra.Homology.KFlatResolution

/-! # First-variable tensor translation and reassociation

Source: Stacks Project, Tag 06YH, total tensor localization, and the triple-totalization
calculation in lem-sc-scheme-canonical-shift-unit-associativity.
(blueprint: lem-sc-scheme-canonical-tensor-shift-associator).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry

-- Cancel the b-comparison from the (a + b)-square, then use faithfulness of shift by b.
private theorem core_of_add
    {C : Type*} {D : Type*} [Category C] [Category D]
    [HasShift C ℤ] [HasShift D ℤ]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ] (τ : F ⟶ G)
    (a b : ℤ) (hb : NatTrans.CommShiftCore τ b)
    (hab : NatTrans.CommShiftCore τ (a + b)) : NatTrans.CommShiftCore τ a := by
  constructor
  ext X
  apply (shiftFunctor D b).map_injective
  have h := hab.shift_app_comm τ X
  simp only [Functor.commShiftIso_add, Functor.CommShift.isoAdd_hom_app,
    Functor.comp_obj] at h
  have hD := (shiftFunctorAdd D a b).inv.naturality (τ.app X)
  have hC := τ.naturality ((shiftFunctorAdd C a b).hom.app X)
  dsimp at hD hC
  simp only [Category.assoc] at h ⊢
  rw [← hD] at h
  rw [← reassoc_of% hC] at h
  rw [← hb.shift_app_comm_assoc τ] at h
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.map_comp]
  have h := (cancel_epi (F.map ((shiftFunctorAdd C a b).hom.app X))).1 h
  have h := (cancel_epi ((F.commShiftIso b).hom.app (X⟦a⟧))).1 h
  apply (cancel_mono ((shiftFunctorAdd D a b).inv.app (G.obj X))).1
  simpa only [Category.assoc] using h

-- The zero square and cancellation give -1; addition then covers every integer.
private theorem shift_of_one
    {C : Type*} {D : Type*} [Category C] [Category D]
    [HasShift C ℤ] [HasShift D ℤ]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ] (τ : F ⟶ G)
    (h : NatTrans.CommShiftCore τ (1 : ℤ)) : NatTrans.CommShift τ ℤ := by
  apply NatTrans.CommShift.of_core
  have hn : NatTrans.CommShiftCore τ (-1 : ℤ) :=
    core_of_add τ (-1) 1 h (by simpa using (NatTrans.CommShiftCore.zero ℤ))
  intro n
  induction n using Int.induction_on with
  | zero => exact NatTrans.CommShiftCore.zero ℤ
  | succ n ih => exact ih.add h
  | pred n ih => simpa only [sub_eq_add_neg] using ih.add hn

-- The two sides are natural transformations, so equality transports across an isomorphism.
private theorem core_of_iso_representatives
    {C : Type*} {D : Type*} [Category C] [Category D]
    [HasShift C ℤ] [HasShift D ℤ]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ] (τ : F ⟶ G)
    {ι : Type*} (obj : ι → C) (S : ι → Prop)
    (hS : ∀ X, ∃ P, S P ∧ Nonempty (obj P ≅ X))
    (h : ∀ P, S P →
      (F.commShiftIso (1 : ℤ)).hom.app (obj P) ≫ (τ.app (obj P))⟦(1 : ℤ)⟧' =
        τ.app ((obj P)⟦(1 : ℤ)⟧) ≫ (G.commShiftIso (1 : ℤ)).hom.app (obj P)) :
    NatTrans.CommShiftCore τ (1 : ℤ) := by
  constructor
  let α := (F.commShiftIso (1 : ℤ)).hom ≫
    Functor.whiskerRight τ (shiftFunctor D (1 : ℤ))
  let β := Functor.whiskerLeft (shiftFunctor C (1 : ℤ)) τ ≫
    (G.commShiftIso (1 : ℤ)).hom
  change α = β
  ext X
  obtain ⟨P, hP, ⟨e⟩⟩ := hS X
  rw [← cancel_epi ((shiftFunctor C (1 : ℤ) ⋙ F).map e.hom),
    α.naturality, β.naturality]
  congr 1
  exact h P hP

-- A commuting square transports along isomorphisms of its source and target functors.
private theorem core_of_commShift_iso
    {C : Type*} {D : Type*} [Category C] [Category D]
    [HasShift C ℤ] [HasShift D ℤ]
    {F₀ F₁ G₀ G₁ : C ⥤ D}
    [F₀.CommShift ℤ] [F₁.CommShift ℤ] [G₀.CommShift ℤ] [G₁.CommShift ℤ]
    (τ₀ : F₀ ⟶ G₀) (τ₁ : F₁ ⟶ G₁) (eF : F₀ ≅ F₁) (eG : G₀ ≅ G₁)
    [NatTrans.CommShift eF.hom ℤ] [NatTrans.CommShift eG.hom ℤ]
    (hc : eF.hom ≫ τ₁ = τ₀ ≫ eG.hom)
    (n : ℤ) (h : NatTrans.CommShiftCore τ₀ n) : NatTrans.CommShiftCore τ₁ n := by
  constructor
  ext A
  rw [← cancel_epi (eF.hom.app (A⟦n⟧))]
  have hcA := congr_app hc A
  have hcn := congr_app hc (A⟦n⟧)
  dsimp at hcA hcn
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [← NatTrans.shift_app_comm_assoc eF.hom, ← Functor.map_comp, hcA,
    Functor.map_comp, h.shift_app_comm_assoc, NatTrans.shift_app_comm]
  rw [← reassoc_of% hcn]

-- Naturality in the middle tensor factor transports the reassociation square.
private theorem associator_core_of_iso_middle
    {C : Type*} [Category C] [MonoidalCategory C] [Preadditive C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [(curriedTensor C).CommShift₂Int]
    {K₀ K : C} (e : K₀ ≅ K) (M : C) (n : ℤ)
    (h : NatTrans.CommShiftCore (tensorRightTensor K₀ M).hom n) :
    NatTrans.CommShiftCore (tensorRightTensor K M).hom n := by
  let eF := (curriedTensor C).flip.mapIso (e ⊗ᵢ Iso.refl M)
  let eG := Functor.isoWhiskerRight ((curriedTensor C).flip.mapIso e) (tensorRight M)
  have : NatTrans.CommShift eF.hom ℤ :=
    Functor.CommShift₂.commShift_flip_map (h := .int) (e ⊗ᵢ Iso.refl M).hom
  have : NatTrans.CommShift ((curriedTensor C).flip.mapIso e).hom ℤ :=
    Functor.CommShift₂.commShift_flip_map (h := .int) e.hom
  have : NatTrans.CommShift eG.hom ℤ := by
    change NatTrans.CommShift
      (Functor.whiskerRight ((curriedTensor C).flip.mapIso e).hom (tensorRight M)) ℤ
    infer_instance
  apply core_of_commShift_iso (tensorRightTensor K₀ M).hom
    (tensorRightTensor K M).hom eF eG _ n h
  ext A
  change A ◁ (e.hom ⊗ₘ 𝟙 M) ≫ (α_ A K M).inv =
    (α_ A K₀ M).inv ≫ (A ◁ e.hom) ▷ M
  simpa only [tensorHom_id] using associator_inv_naturality_middle A e.hom M

-- Naturality in the final tensor factor transports the reassociation square.
private theorem associator_core_of_iso_right
    {C : Type*} [Category C] [MonoidalCategory C] [Preadditive C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [(curriedTensor C).CommShift₂Int]
    (K : C) {M₀ M : C} (e : M₀ ≅ M) (n : ℤ)
    (h : NatTrans.CommShiftCore (tensorRightTensor K M₀).hom n) :
    NatTrans.CommShiftCore (tensorRightTensor K M).hom n := by
  let eF := (curriedTensor C).flip.mapIso (Iso.refl K ⊗ᵢ e)
  let eG := Functor.isoWhiskerLeft (tensorRight K) ((curriedTensor C).flip.mapIso e)
  have : NatTrans.CommShift eF.hom ℤ :=
    Functor.CommShift₂.commShift_flip_map (h := .int) (Iso.refl K ⊗ᵢ e).hom
  have : NatTrans.CommShift ((curriedTensor C).flip.mapIso e).hom ℤ :=
    Functor.CommShift₂.commShift_flip_map (h := .int) e.hom
  have : NatTrans.CommShift eG.hom ℤ := by
    change NatTrans.CommShift
      (Functor.whiskerLeft (tensorRight K) ((curriedTensor C).flip.mapIso e).hom) ℤ
    infer_instance
  apply core_of_commShift_iso (tensorRightTensor K M₀).hom
    (tensorRightTensor K M).hom eF eG _ n h
  ext A
  change A ◁ (𝟙 K ⊗ₘ e.hom) ≫ (α_ A K M).inv =
    (α_ A K M₀).inv ≫ (A ⊗ K) ◁ e.hom
  simpa only [id_tensorHom] using associator_inv_naturality_right A K e.hom

-- Localization inverts a K-flat resolution of a complex representing the derived object.
private theorem exists_kFlat_derived_iso (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (K : schemeDerivedCategory X) :
    ∃ P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ,
      CochainComplex.IsKFlat (R := X.sheaf) P ∧ Nonempty (DerivedCategory.Q.obj P ≅ K) := by
  obtain ⟨P, s, hP, _, hs, _⟩ :=
    CochainComplex.exists_isKFlatResolution (R := X.sheaf) (DerivedCategory.Q.objPreimage K)
  have : QuasiIso s := hs
  exact ⟨P, hP, ⟨asIso (DerivedCategory.Q.map s) ≪≫ DerivedCategory.Q.objObjPreimageIso K⟩⟩


/-- Moving a translation out of the first factor commutes with reassociation.
This concerns only the associator and the tensor-shift comparisons, without any unitors.
Source: Stacks Project, Tag 06YH, total tensor localization; the triple-totalization
step of lem-sc-scheme-canonical-shift-unit-associativity.
(blueprint: lem-sc-scheme-canonical-tensor-shift-associator).

Proof. Use schemeCanonicalTensorShift_associator_kFlat_one for shift one at
three K-flat representatives. Every derived object is isomorphic to Q(P) for a
K-flat P: take a K-flat resolution of Q.objPreimage and localize its augmentation.
First extend the square in A by naturality of the two transformations forming
its sides, cancelling the image of the representative isomorphism. Then extend
in M and K using associator naturality and the tensor-morphism shift squares of
CommShift₂Int. This proves CommShiftCore for the natural transformation
(tensorRightTensor K M).hom at shift one. Expand the shift-addition formula;
cancel its invertible comparisons and use faithfulness of shift by one to
recover the shift-minus-one square from the zero square. Integer induction and
CommShiftCore.add give the square for every n. Evaluating at A and expanding
the composite-functor shift comparison gives precisely the displayed identity.
The K-flat representative calculation is a separate theorem; all transport,
cancellation, and integer induction here are proved in Lean. -/
theorem schemeCanonicalTensorShift_associator (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (A K M : schemeDerivedCategory X) (n : ℤ) :
    letI := schemeCanonicalTensorShift X
    letI : ∀ B : schemeDerivedCategory X, (tensorRight B).CommShift ℤ :=
      fun B ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) B
    ((tensorRight (K ⊗ M)).commShiftIso n).hom.app A ≫ (α_ A K M).inv⟦n⟧' =
      (α_ (A⟦n⟧) K M).inv ≫
        (((tensorRight K).commShiftIso n).hom.app A) ▷ M ≫
        ((tensorRight M).commShiftIso n).hom.app (A ⊗ K) := by
  let := schemeCanonicalTensorShift X
  let : ∀ B : schemeDerivedCategory X, (tensorRight B).CommShift ℤ :=
    fun B ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) B
  have h : NatTrans.CommShiftCore (tensorRightTensor K M).hom (1 : ℤ) := by
    obtain ⟨T, hT, ⟨eK⟩⟩ := exists_kFlat_derived_iso X K
    obtain ⟨U, hU, ⟨eM⟩⟩ := exists_kFlat_derived_iso X M
    apply associator_core_of_iso_middle eK M (1 : ℤ)
    apply associator_core_of_iso_right (DerivedCategory.Q.obj T) eM (1 : ℤ)
    apply core_of_iso_representatives
      (tensorRightTensor (DerivedCategory.Q.obj T) (DerivedCategory.Q.obj U)).hom
      (fun P ↦ DerivedCategory.Q.obj P) (CochainComplex.IsKFlat (R := X.sheaf))
      (exists_kFlat_derived_iso X)
    intro P hP
    simpa only [tensorRightTensor_hom_app, Functor.commShiftIso_comp_hom_app,
      tensorRight, Functor.flip, curriedTensor,
      Functor.comp_obj] using schemeCanonicalTensorShift_associator_kFlat_one X P T U hP hT hU
  have := shift_of_one (tensorRightTensor K M).hom h
  simpa only [tensorRightTensor_hom_app, Functor.commShiftIso_comp_hom_app,
    tensorRight, Functor.flip, curriedTensor,
    Functor.comp_obj] using NatTrans.shift_app_comm (tensorRightTensor K M).hom n A

end AlgebraicGeometry
```

### Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShiftAssociatorKFlatOne

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShift
public import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.TensorShiftOneAssociator
import Sheaf.AlgebraicGeometry.SchemeTensorShiftLocalizationNormalization

/-! # Reassociation of the first-factor translation on K-flat representatives

Source: Stacks Project, Tag 06YH, K-flat total tensor localization; the
triple-totalization calculation of lem-sc-scheme-canonical-tensor-shift-associator.
(blueprint: lem-sc-scheme-canonical-tensor-shift-associator-kflat-one).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 600000 in
-- Comparing the recorded monoidal and shift instance terms needs extra elaboration work.
/-- First-factor translation by one commutes with reassociation at a K-flat representative.
Source: Stacks Project, Tag 06YH, total tensor localization; the representative
calculation of lem-sc-scheme-canonical-tensor-shift-associator.
(blueprint: lem-sc-scheme-canonical-tensor-shift-associator-kflat-one).

Proof. Use P, T and U themselves as representatives of all three factors.
K-flatness makes the tensor localization comparisons invertible.
On the total tensor summand of tridegree (p,q,r), the first-factor translation
comparison has no extra scalar and changes the first index to p+1. Both composites
therefore apply the inverse sheaf-module associator to this same summand.
The differential coefficients of the translated source are -1, (-1)^p and
(-1)^(p+q). Translating the target differential multiplies its coefficients
1, (-1)^(p+1) and (-1)^(p+1+q) by -1, giving the same coefficients.
Thus the two chain maps agree on every summand. Localize this equality. The lax
monoidal associativity equation for localization replaces the complex associators
with the recorded derived associators. The localization shift squares defining
schemeCanonicalTensorShift replace the complex shift comparisons with the recorded
ones. Cancel the invertible tensor and shift comparisons. This asserts the equality only
at Q(P), Q(T), Q(U) and for shift one; transport in all three factors and extension
to other integer shifts are separate steps. Zero factors and the empty scheme give the
unique maps between zero objects, and the sign computation also holds in
characteristic two. No cancellation of noninvertible maps is used. -/
theorem schemeCanonicalTensorShift_associator_kFlat_one (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (P T U : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlat (R := X.sheaf) P)
    (hT : CochainComplex.IsKFlat (R := X.sheaf) T)
    (hU : CochainComplex.IsKFlat (R := X.sheaf) U) :
    letI := schemeCanonicalTensorShift X
    letI : ∀ B : schemeDerivedCategory X, (tensorRight B).CommShift ℤ :=
      fun B ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) B
    let A := DerivedCategory.Q.obj P
    let K := DerivedCategory.Q.obj T
    let M := DerivedCategory.Q.obj U
    ((tensorRight (K ⊗ M)).commShiftIso (1 : ℤ)).hom.app A ≫
        (α_ A K M).inv⟦(1 : ℤ)⟧' =
      (α_ (A⟦(1 : ℤ)⟧) K M).inv ≫
        (((tensorRight K).commShiftIso (1 : ℤ)).hom.app A) ▷ M ≫
        ((tensorRight M).commShiftIso (1 : ℤ)).hom.app (A ⊗ K) := by
  let := schemeCanonicalTensorShift X
  let : ∀ B : schemeDerivedCategory X, (tensorRight B).CommShift ℤ :=
    fun B ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) B
  let := SheafOfModules.monoidalCategory X.sheaf
  let := SheafOfModules.symmetricCategory X.sheaf
  have : MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  let : MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
  have : CategoryTheory.IsGrothendieckAbelian.{u}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  have : CategoryTheory.Limits.HasColimitsOfSize.{0, 0}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    CategoryTheory.Limits.hasColimitsOfSizeShrink.{0, 0, u, u} _
  have := schemeModule_hasFunctorialFlatResolution X
  have := DerivedCategory.hasDerivedMonoidalCategory
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  dsimp only
  obtain ⟨hc, hl, hr⟩ := schemeTensorShift_localization_normalization X P T U hP hT hU
  have : IsIso (schemeTensorShiftTargetComparison X P T U) := hc
  have hf := CochainComplex.tensorShiftOne_associator P T U
  have hd :
      (α_ (DerivedCategory.Q.obj P⟦(1 : ℤ)⟧) (DerivedCategory.Q.obj T)
        (DerivedCategory.Q.obj U)).hom ≫
        ((tensorRight (DerivedCategory.Q.obj T ⊗ DerivedCategory.Q.obj U)).commShiftIso
          (1 : ℤ)).hom.app (DerivedCategory.Q.obj P) =
      (((tensorRight (DerivedCategory.Q.obj T)).commShiftIso (1 : ℤ)).hom.app
        (DerivedCategory.Q.obj P)) ▷ DerivedCategory.Q.obj U ≫
        ((tensorRight (DerivedCategory.Q.obj U)).commShiftIso (1 : ℤ)).hom.app
          (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj T) ≫
        (α_ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj T)
          (DerivedCategory.Q.obj U)).hom⟦(1 : ℤ)⟧' := by
    apply (cancel_mono (schemeTensorShiftTargetComparison X P T U)).1
    rw [hl, hr, hf]
  apply (cancel_epi (α_ (DerivedCategory.Q.obj P⟦(1 : ℤ)⟧)
    (DerivedCategory.Q.obj T) (DerivedCategory.Q.obj U)).hom).1
  apply (cancel_mono ((α_ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj T)
    (DerivedCategory.Q.obj U)).hom⟦(1 : ℤ)⟧')).1
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, Iso.inv_hom_id]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact hd

end AlgebraicGeometry
```

### Sheaf.AlgebraicGeometry.SchemeTensorShiftBinaryLocalizationSquare

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K4
-/
module

public import Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShift
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex

/-! # Binary localization square for the first tensor shift
Source: Stacks Project, Tag 06YH, localization of total tensor products.
(blueprint: lem-sc-scheme-tensor-shift-binary-localization-square).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w u'
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace DerivedCategory.IndependentTensorShift

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{u'} C]
  [HasDerivedCategory.{w} C]
  [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C] [HasColimitsOfSize.{0, 0} C]
  [Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (.up ℤ))]

local instance (P T : CochainComplex C ℤ) :
    CochainComplex.HasMapBifunctor P T (curriedTensor C) := inferInstance

noncomputable local instance : MonoidalCategory (CochainComplex C ℤ) := inferInstance

noncomputable local instance : MonoidalCategory (DerivedCategory C) := inferInstance

attribute [local instance] commShift₂CurriedTensor
open DerivedCategory.IndependentTensorShift.TensorCommShift₂

private theorem squareL (P : CochainComplex.KFlat C) (T : CochainComplex C ℤ) :
    ((tensorRight ((L C).obj T)).commShiftIso (1 : ℤ)).hom.app ((LKFlat C).obj P) ≫
      (Functor.LaxMonoidal.μ (L C) P.obj T)⟦(1 : ℤ)⟧' ≫
      ((L C).commShiftIso (1 : ℤ)).inv.app (P.obj ⊗ T) =
    (((L C).commShiftIso (1 : ℤ)).inv.app P.obj) ▷ (L C).obj T ≫
      Functor.LaxMonoidal.μ (L C) (P.obj⟦(1 : ℤ)⟧) T ≫
      (L C).map (CochainComplex.mapBifunctorShift₁Iso P.obj T (curriedTensor C) 1).hom := by
  have := Functor.CommShift₂OfLocalization.commShift_liftingIsoApp (M := ℤ) (L C) (LKFlat C)
    (HomologicalComplex.quasiIso C (.up ℤ)) (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat
    (F C).flip (curriedTensor (DerivedCategory C)).flip T
  have h := NatTrans.shift_app_comm (Functor.CommShift₂OfLocalization.liftingIsoApp (L C)
    (LKFlat C) (HomologicalComplex.quasiIso C (.up ℤ))
    (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat
    (F C).flip (curriedTensor (DerivedCategory C)).flip T) (1 : ℤ) P
  rw [Functor.commShiftIso_comp_hom_app] at h
  let a := ((CochainComplex.ιKFlat C).commShiftIso (1 : ℤ)).hom.app P
  have hl (V : CochainComplex.KFlat C) :
      (Functor.CommShift₂OfLocalization.liftingIsoApp (L C) (LKFlat C)
        (HomologicalComplex.quasiIso C (.up ℤ))
        (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat
        (F C).flip (curriedTensor (DerivedCategory C)).flip T).app V =
      Functor.LaxMonoidal.μ (L C) V.obj T := by
    simp only [Functor.LaxMonoidal.comp_μ]
    change _ = _ ≫ Qh.map (𝟙 _)
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
    rfl
  have hf : (((F C).flip.obj T).commShiftIso (1 : ℤ)).hom.app P =
      (L C).map (a ▷ T ≫
        (CochainComplex.mapBifunctorShift₁Iso P.obj T (curriedTensor C) 1).hom) ≫
        ((L C).commShiftIso (1 : ℤ)).hom.app _ := by
    erw [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_hom_app]
    rfl
  have hk : ((LKFlat C).commShiftIso (1 : ℤ)).hom.app P =
      (L C).map a ≫ ((L C).commShiftIso (1 : ℤ)).hom.app P.obj :=
    Functor.commShiftIso_comp_hom_app _ _ _ _
  rw [hl, hl, hf, hk] at h
  simp only [Functor.map_comp, Category.assoc] at h
  change (L C).map a ▷ (L C).obj T ≫
      (((L C).commShiftIso (1 : ℤ)).hom.app P.obj) ▷ (L C).obj T ≫
      ((tensorRight ((L C).obj T)).commShiftIso (1 : ℤ)).hom.app ((L C).obj P.obj) ≫
      (Functor.LaxMonoidal.μ (L C) P.obj T)⟦(1 : ℤ)⟧' = _ at h
  erw [← Functor.LaxMonoidal.μ_natural_left_assoc] at h
  rw [CategoryTheory.cancel_epi] at h
  have h' := congrArg (fun f ↦
    (((L C).commShiftIso (1 : ℤ)).inv.app P.obj) ▷ (L C).obj T ≫ f ≫
      ((L C).commShiftIso (1 : ℤ)).inv.app (P.obj ⊗ T)) h
  simp only [Category.assoc] at h'
  change _ = _ ≫ _ ≫ _ ≫
    ((L C).commShiftIso (1 : ℤ)).hom.app (P.obj ⊗ T) ≫
      ((L C).commShiftIso (1 : ℤ)).inv.app (P.obj ⊗ T) at h'
  simp only [← comp_whiskerRight_assoc, Iso.inv_hom_id_app,
    id_whiskerRight, Category.id_comp, Iso.hom_inv_id_app, Category.comp_id] at h'
  exact h'

private theorem squareQ (P T : CochainComplex C ℤ)
    (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P) :
    ((tensorRight (Q.obj T)).commShiftIso (1 : ℤ)).hom.app (Q.obj P) ≫
      (Functor.LaxMonoidal.μ Q P T)⟦(1 : ℤ)⟧' ≫
      (Q.commShiftIso (1 : ℤ)).inv.app (P ⊗ T) =
    ((Q.commShiftIso (1 : ℤ)).inv.app P) ▷ Q.obj T ≫
      Functor.LaxMonoidal.μ Q (P⟦(1 : ℤ)⟧) T ≫
      Q.map (CochainComplex.mapBifunctorShift₁Iso P T (curriedTensor C) 1).hom := by
  have hμ (A B : CochainComplex C ℤ) :
      Functor.LaxMonoidal.μ Q A B = Functor.LaxMonoidal.μ (L C) A B := by
    change (𝟙 _ ⊗ₘ 𝟙 _) ≫ Functor.LaxMonoidal.μ (L C) A B ≫ 𝟙 _ = _
    simp
  have hη (A : CochainComplex C ℤ) :
      (Q.commShiftIso (1 : ℤ)).inv.app A = ((L C).commShiftIso (1 : ℤ)).inv.app A := by
    rw [Functor.CommShift.ofIso_commShiftIso_inv_app]
    change (𝟙 _)⟦(1 : ℤ)⟧' ≫ ((L C).commShiftIso (1 : ℤ)).inv.app A ≫ 𝟙 _ = _
    simp
  simp only [hμ, hη]
  exact squareL C ⟨P, hP⟩ T

end DerivedCategory.IndependentTensorShift

namespace AlgebraicGeometry

variable (X : Scheme.{u})

noncomputable local instance SchemeTensorShiftBinaryLocalizationSquare_monoidalCategory :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.sheaf
noncomputable local instance SchemeTensorShiftBinaryLocalizationSquare_symmetricCategory :
    SymmetricCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.symmetricCategory X.sheaf
local instance SchemeTensorShiftBinaryLocalizationSquare_monoidalPreadditive : MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
noncomputable local instance SchemeTensorShiftBinaryLocalizationSquare_monoidalClosed :
    MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
local instance SchemeTensorShiftBinaryLocalizationSquare_isGrothendieckAbelian : IsGrothendieckAbelian.{u}
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
local instance SchemeTensorShiftBinaryLocalizationSquare_hasColimitsOfSize : HasColimitsOfSize.{0, 0}
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) := hasColimitsOfSizeShrink.{0, 0, u, u} _
local instance SchemeTensorShiftBinaryLocalizationSquare_hasFunctorialFlatResolution : Abelian.HasFunctorialFlatResolution
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  schemeModule_hasFunctorialFlatResolution X
variable [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

local instance SchemeTensorShiftBinaryLocalizationSquare_hasDerivedMonoidalCategory : DerivedCategory.Qh.HasDerivedMonoidalCategory
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :=
  DerivedCategory.hasDerivedMonoidalCategory _

local instance SchemeTensorShiftBinaryLocalizationSquare_hasTensor (A B : GradedObject ℤ
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))) : A.HasTensor B := inferInstance

local instance SchemeTensorShiftBinaryLocalizationSquare_hasTensor₄ObjExt (A B C D : GradedObject ℤ
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))) :
    GradedObject.HasTensor₄ObjExt A B C D := inferInstance

local instance SchemeTensorShiftBinaryLocalizationSquare_hasGoodTensor₁₂Tensor (A B C : GradedObject ℤ
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))) :
    GradedObject.HasGoodTensor₁₂Tensor A B C := inferInstance

local instance SchemeTensorShiftBinaryLocalizationSquare_hasGoodTensorTensor₂₃ (A B C : GradedObject ℤ
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))) :
    GradedObject.HasGoodTensorTensor₂₃ A B C := inferInstance

local instance SchemeTensorShiftBinaryLocalizationSquare_hasMapBifunctor (A B : CochainComplex
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    CochainComplex.HasMapBifunctor A B
      (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace))) := inferInstance

noncomputable local instance SchemeTensorShiftBinaryLocalizationSquare_monoidalCategory2 : MonoidalCategory
    (CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) := inferInstance

noncomputable local instance SchemeTensorShiftBinaryLocalizationSquare_monoidalCategory3 : MonoidalCategory (schemeDerivedCategory X) :=
  schemeDerivedTensorMonoidal X

noncomputable local instance SchemeTensorShiftBinaryLocalizationSquare_laxMonoidal :
    (DerivedCategory.Q (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).LaxMonoidal :=
  Functor.LaxMonoidal.ofIso (DerivedCategory.quotientCompQhIso _)

set_option linter.unusedVariables false in
/-- The first-variable tensor shift agrees with localization on a K-flat first factor.
Source: Stacks Project, Tag 06YH; the explicit localization construction
`Functor.CommShift₂OfLocalization.commShift_liftingIsoApp`.
(blueprint: lem-sc-scheme-tensor-shift-binary-localization-square).

Proof. Restrict the first variable to K-flat complexes. The natural comparison
from localized tensor to localization of total tensor is `liftingIsoHom` and
commutes with translation by the defining localization construction. Evaluate
its flipped component at the second complex. Expand the shift of the inclusion
of K-flat complexes, and cancel its invertible comparison by naturality of the
tensorator. This gives the square for quotient followed by Qh. Transport along
`quotientCompQhIso`, whose tensorator and shift structures are transported along
this same isomorphism, to obtain the displayed square for Q. This is a binary
square, independent of any associator coherence; it also holds for zero complexes. -/
theorem schemeTensorShift_binary_localization_square
    (P T : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)).kFlat P) :
    letI := schemeCanonicalTensorShift X
    letI : ∀ B : schemeDerivedCategory X, (tensorRight B).CommShift ℤ :=
      fun B ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) B
    ((tensorRight (DerivedCategory.Q.obj T)).commShiftIso (1 : ℤ)).hom.app
        (DerivedCategory.Q.obj P) ≫
      (Functor.LaxMonoidal.μ DerivedCategory.Q P T)⟦(1 : ℤ)⟧' ≫
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app (P ⊗ T) =
    ((DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app P) ▷ DerivedCategory.Q.obj T ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q (P⟦(1 : ℤ)⟧) T ≫
      DerivedCategory.Q.map (CochainComplex.mapBifunctorShift₁Iso P T
        (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace))) 1).hom := by
  let := schemeCanonicalTensorShift X
  let : ∀ B : schemeDerivedCategory X, (tensorRight B).CommShift ℤ :=
    fun B ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) B
  exact DerivedCategory.IndependentTensorShift.squareQ
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) P T hP

end AlgebraicGeometry
```

### Sheaf.AlgebraicGeometry.SchemeTensorShiftLocalizationNormalization

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShift
public import Sheaf.Algebra.Homology.KFlat
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import Sheaf.AlgebraicGeometry.SchemeTensorShiftBinaryLocalizationSquare

/-! # Normalizing tensor-shift composites through localization
Source: Stacks Project, Tag 06YH, K-flat total tensor localization.
(blueprint: lem-sc-scheme-tensor-shift-localization-normalization).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w u' v'
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry

private theorem first_generic
    {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    [MonoidalCategory C] [MonoidalCategory D] [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) [F.LaxMonoidal] [F.CommShift ℤ]
    [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [(curriedTensor D).CommShift₂Int]
    (P T U : C) (σ : P⟦(1 : ℤ)⟧ ⊗ (T ⊗ U) ⟶ (P ⊗ (T ⊗ U))⟦(1 : ℤ)⟧)
    (hs : ((tensorRight (F.obj (T ⊗ U))).commShiftIso (1 : ℤ)).hom.app (F.obj P) ≫
      (Functor.LaxMonoidal.μ F P (T ⊗ U))⟦(1 : ℤ)⟧' ≫
      (F.commShiftIso (1 : ℤ)).inv.app (P ⊗ (T ⊗ U)) =
      ((F.commShiftIso (1 : ℤ)).inv.app P) ▷ F.obj (T ⊗ U) ≫
      Functor.LaxMonoidal.μ F (P⟦(1 : ℤ)⟧) (T ⊗ U) ≫ F.map σ) :
    (α_ (F.obj P⟦(1 : ℤ)⟧) (F.obj T) (F.obj U)).hom ≫
      ((tensorRight (F.obj T ⊗ F.obj U)).commShiftIso (1 : ℤ)).hom.app (F.obj P) ≫
      (F.obj P ◁ Functor.LaxMonoidal.μ F T U ≫
        Functor.LaxMonoidal.μ F P (T ⊗ U))⟦(1 : ℤ)⟧' ≫
      (F.commShiftIso (1 : ℤ)).inv.app (P ⊗ (T ⊗ U)) =
    (((F.commShiftIso (1 : ℤ)).inv.app P) ▷ F.obj T) ▷ F.obj U ≫
      (Functor.LaxMonoidal.μ F (P⟦(1 : ℤ)⟧) T) ▷ F.obj U ≫
      Functor.LaxMonoidal.μ F (P⟦(1 : ℤ)⟧ ⊗ T) U ≫
      F.map ((α_ (P⟦(1 : ℤ)⟧) T U).hom ≫ σ) := by
  have hn := NatTrans.shift_app_comm
    ((curriedTensor D).flip.map (Functor.LaxMonoidal.μ F T U)) (1 : ℤ) (F.obj P)
  change ((tensorRight (F.obj T ⊗ F.obj U)).commShiftIso (1 : ℤ)).hom.app (F.obj P) ≫
      (F.obj P ◁ Functor.LaxMonoidal.μ F T U)⟦(1 : ℤ)⟧' =
    F.obj P⟦(1 : ℤ)⟧ ◁ Functor.LaxMonoidal.μ F T U ≫
      ((tensorRight (F.obj (T ⊗ U))).commShiftIso (1 : ℤ)).hom.app (F.obj P) at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, hs, whisker_exchange_assoc,
    ← associator_naturality_left_assoc]
  simp only [Functor.comp_obj]
  rw [← Functor.LaxMonoidal.associativity_assoc F (P⟦(1 : ℤ)⟧) T U]

private theorem second_generic
    {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    [MonoidalCategory C] [MonoidalCategory D] [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) [F.LaxMonoidal] [F.CommShift ℤ]
    [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [(curriedTensor D).CommShift₂Int]
    (P T U : C) (σ₁ : P⟦(1 : ℤ)⟧ ⊗ T ⟶ (P ⊗ T)⟦(1 : ℤ)⟧)
    (σ₂ : (P ⊗ T)⟦(1 : ℤ)⟧ ⊗ U ⟶ ((P ⊗ T) ⊗ U)⟦(1 : ℤ)⟧)
    (hs₁ : ((tensorRight (F.obj T)).commShiftIso (1 : ℤ)).hom.app (F.obj P) ≫
      (Functor.LaxMonoidal.μ F P T)⟦(1 : ℤ)⟧' ≫
      (F.commShiftIso (1 : ℤ)).inv.app (P ⊗ T) =
      ((F.commShiftIso (1 : ℤ)).inv.app P) ▷ F.obj T ≫
      Functor.LaxMonoidal.μ F (P⟦(1 : ℤ)⟧) T ≫ F.map σ₁)
    (hs₂ : ((tensorRight (F.obj U)).commShiftIso (1 : ℤ)).hom.app (F.obj (P ⊗ T)) ≫
      (Functor.LaxMonoidal.μ F (P ⊗ T) U)⟦(1 : ℤ)⟧' ≫
      (F.commShiftIso (1 : ℤ)).inv.app ((P ⊗ T) ⊗ U) =
      ((F.commShiftIso (1 : ℤ)).inv.app (P ⊗ T)) ▷ F.obj U ≫
      Functor.LaxMonoidal.μ F ((P ⊗ T)⟦(1 : ℤ)⟧) U ≫ F.map σ₂) :
    (((tensorRight (F.obj T)).commShiftIso (1 : ℤ)).hom.app (F.obj P)) ▷ F.obj U ≫
      ((tensorRight (F.obj U)).commShiftIso (1 : ℤ)).hom.app (F.obj P ⊗ F.obj T) ≫
      (α_ (F.obj P) (F.obj T) (F.obj U)).hom⟦(1 : ℤ)⟧' ≫
      (F.obj P ◁ Functor.LaxMonoidal.μ F T U ≫
        Functor.LaxMonoidal.μ F P (T ⊗ U))⟦(1 : ℤ)⟧' ≫
      (F.commShiftIso (1 : ℤ)).inv.app (P ⊗ (T ⊗ U)) =
    (((F.commShiftIso (1 : ℤ)).inv.app P) ▷ F.obj T) ▷ F.obj U ≫
      (Functor.LaxMonoidal.μ F (P⟦(1 : ℤ)⟧) T) ▷ F.obj U ≫
      Functor.LaxMonoidal.μ F (P⟦(1 : ℤ)⟧ ⊗ T) U ≫
      F.map (σ₁ ▷ U ≫ σ₂ ≫ (α_ P T U).hom⟦(1 : ℤ)⟧') := by
  have hn := (tensorRight (F.obj U)).commShiftIso_hom_naturality
    (Functor.LaxMonoidal.μ F P T) (1 : ℤ)
  change (Functor.LaxMonoidal.μ F P T)⟦(1 : ℤ)⟧' ▷ F.obj U ≫
      ((tensorRight (F.obj U)).commShiftIso (1 : ℤ)).hom.app (F.obj (P ⊗ T)) =
    ((tensorRight (F.obj U)).commShiftIso (1 : ℤ)).hom.app (F.obj P ⊗ F.obj T) ≫
      (Functor.LaxMonoidal.μ F P T ▷ F.obj U)⟦(1 : ℤ)⟧' at hn
  have ha := congrArg (fun f ↦ (shiftFunctor D (1 : ℤ)).map f)
    (Functor.LaxMonoidal.associativity F P T U)
  simp only [Functor.map_comp] at ha
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% ha, ← reassoc_of% hn,
    F.commShiftIso_inv_naturality (α_ P T U).hom (1 : ℤ), reassoc_of% hs₂]
  have hw := congrArg (fun f ↦ f ▷ F.obj U) hs₁
  simp only [comp_whiskerRight] at hw
  rw [reassoc_of% hw, Functor.LaxMonoidal.μ_natural_left_assoc]


open Functor.LaxMonoidal in
private theorem tensorator_isIso
    (C : Type*) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{u} C]
    [HasDerivedCategory.{w} C] [MonoidalCategory C] [MonoidalClosed C]
    [MonoidalPreadditive C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
    [HasColimitsOfSize.{0, 0} C]
    [DerivedCategory.Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (.up ℤ))]
    (P T : CochainComplex C ℤ)
    (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P) :
    IsIso (μ DerivedCategory.Q P T) := by
  have : IsIso (μ DerivedCategory.Qh
      ((HomotopyCategory.quotient C (.up ℤ)).obj P)
      ((HomotopyCategory.quotient C (.up ℤ)).obj T)) :=
    inferInstanceAs (IsIso
      (((DerivedCategory.IndependentTensorShift.TensorCommShift₂.liftingIsoHom C).app
        ⟨P, hP⟩).app T))
  change IsIso
    (((DerivedCategory.quotientCompQhIso C).inv.app P ⊗ₘ
        (DerivedCategory.quotientCompQhIso C).inv.app T) ≫
      μ (HomotopyCategory.quotient C (.up ℤ) ⋙ DerivedCategory.Qh) P T ≫
      (DerivedCategory.quotientCompQhIso C).hom.app (P ⊗ T))
  rw [Functor.LaxMonoidal.comp_μ]
  infer_instance

variable (X : Scheme.{u})

noncomputable local instance SchemeTensorShiftLocalizationNormalization_monoidalCategory :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.sheaf
noncomputable local instance SchemeTensorShiftLocalizationNormalization_symmetricCategory :
    SymmetricCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.symmetricCategory X.sheaf
local instance SchemeTensorShiftLocalizationNormalization_monoidalPreadditive : MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
noncomputable local instance SchemeTensorShiftLocalizationNormalization_monoidalClosed :
    MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
local instance SchemeTensorShiftLocalizationNormalization_isGrothendieckAbelian : IsGrothendieckAbelian.{u}
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
local instance SchemeTensorShiftLocalizationNormalization_hasColimitsOfSize : HasColimitsOfSize.{0, 0}
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) := hasColimitsOfSizeShrink.{0, 0, u, u} _
local instance SchemeTensorShiftLocalizationNormalization_hasFunctorialFlatResolution : Abelian.HasFunctorialFlatResolution
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  schemeModule_hasFunctorialFlatResolution X
variable [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

local instance SchemeTensorShiftLocalizationNormalization_hasDerivedMonoidalCategory : DerivedCategory.Qh.HasDerivedMonoidalCategory
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :=
  DerivedCategory.hasDerivedMonoidalCategory _

local instance SchemeTensorShiftLocalizationNormalization_hasTensor (A B : GradedObject ℤ
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))) : A.HasTensor B := inferInstance

local instance SchemeTensorShiftLocalizationNormalization_hasTensor₄ObjExt (A B C D : GradedObject ℤ
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))) :
    GradedObject.HasTensor₄ObjExt A B C D := inferInstance

local instance SchemeTensorShiftLocalizationNormalization_hasGoodTensor₁₂Tensor (A B C : GradedObject ℤ
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))) :
    GradedObject.HasGoodTensor₁₂Tensor A B C := inferInstance

local instance SchemeTensorShiftLocalizationNormalization_hasGoodTensorTensor₂₃ (A B C : GradedObject ℤ
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))) :
    GradedObject.HasGoodTensorTensor₂₃ A B C := inferInstance

local instance SchemeTensorShiftLocalizationNormalization_hasMapBifunctor (A B : CochainComplex
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    CochainComplex.HasMapBifunctor A B
      (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace))) := inferInstance

noncomputable local instance SchemeTensorShiftLocalizationNormalization_monoidalCategory2 : MonoidalCategory
    (CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) := inferInstance

noncomputable local instance SchemeTensorShiftLocalizationNormalization_monoidalCategory3 : MonoidalCategory (schemeDerivedCategory X) :=
  schemeDerivedTensorMonoidal X

noncomputable local instance SchemeTensorShiftLocalizationNormalization_laxMonoidal :
    (DerivedCategory.Q (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).LaxMonoidal :=
  Functor.LaxMonoidal.ofIso (DerivedCategory.quotientCompQhIso _)

omit [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] in
private theorem upstreamKFlat
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlat (R := X.sheaf) P) :
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)).kFlat P := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff,
    HomotopyCategory.kFlat_iff_preserves_acyclic]
  intro N hN
  obtain ⟨N, rfl⟩ := N.quotient_obj_surjective
  rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hN
  have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
    (CochainComplex.mapBifunctor N P (curriedTensor _))).2 (hP N hN)
  exact ⟨(HomotopyCategory.subcategoryAcyclic _).prop_of_iso (β_ _ _) hr, hr⟩

open Functor.LaxMonoidal in
/-- The comparison from a translated derived triple tensor to its total tensor representative.
Source: Stacks Project, Tag 06YH.
(blueprint: lem-sc-scheme-tensor-shift-localization-normalization). -/
noncomputable def schemeTensorShiftSourceComparison
    (P T U : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    (DerivedCategory.Q.obj P⟦(1 : ℤ)⟧ ⊗ DerivedCategory.Q.obj T) ⊗
        DerivedCategory.Q.obj U ⟶ DerivedCategory.Q.obj ((P⟦(1 : ℤ)⟧ ⊗ T) ⊗ U) :=
  (((DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app P) ▷ DerivedCategory.Q.obj T) ▷
      DerivedCategory.Q.obj U ≫
    (μ DerivedCategory.Q (P⟦(1 : ℤ)⟧) T) ▷ DerivedCategory.Q.obj U ≫
    μ DerivedCategory.Q (P⟦(1 : ℤ)⟧ ⊗ T) U

open Functor.LaxMonoidal in
/-- The comparison from the translated right-associated derived tensor to localization.
Source: Stacks Project, Tag 06YH.
(blueprint: lem-sc-scheme-tensor-shift-localization-normalization). -/
noncomputable def schemeTensorShiftTargetComparison
    (P T U : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    (DerivedCategory.Q.obj P ⊗ (DerivedCategory.Q.obj T ⊗ DerivedCategory.Q.obj U))⟦(1 : ℤ)⟧ ⟶
      DerivedCategory.Q.obj ((P ⊗ (T ⊗ U))⟦(1 : ℤ)⟧) :=
  (DerivedCategory.Q.obj P ◁ μ DerivedCategory.Q T U ≫
    μ DerivedCategory.Q P (T ⊗ U))⟦(1 : ℤ)⟧' ≫
    (DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app (P ⊗ (T ⊗ U))

/- The target comparison is invertible for K-flat representatives.  The proof uses
the K-flat localization comparison theorem: each tensorator involving a K-flat
factor is an isomorphism, as are the shift comparison maps.  The displayed map is
their composite, so `infer_instance` supplies its `IsIso` instance after unfolding.
Source: Stacks Project, Tag 06YH, localization normalization calculation.
(blueprint: aux-sc-target-comparison-isIso) -/
set_option linter.unusedVariables false in
theorem schemeTensorShift_targetComparison_isIso
    (P T U : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlat (R := X.sheaf) P)
    (hT : CochainComplex.IsKFlat (R := X.sheaf) T)
    (hU : CochainComplex.IsKFlat (R := X.sheaf) U) :
    letI := schemeCanonicalTensorShift X
    letI : ∀ B : schemeDerivedCategory X, (tensorRight B).CommShift ℤ :=
      fun B ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) B
    IsIso (schemeTensorShiftTargetComparison X P T U) := by
  have hp := upstreamKFlat X P hP
  have ht := upstreamKFlat X T hT
  have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q T U) :=
    tensorator_isIso (SheafOfModules.{u} (moduleRings X.toRingedSpace)) T U ht
  have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P (T ⊗ U)) :=
    tensorator_isIso (SheafOfModules.{u} (moduleRings X.toRingedSpace)) P (T ⊗ U) hp
  dsimp only [schemeTensorShiftTargetComparison]
  infer_instance

set_option linter.unusedVariables false in
/-- Expanded first normalization coherence intermediate.
The proof unfolds all local abbreviations in the localization calculation.
(blueprint: aux-sc-target-comparison-first-core). -/
theorem schemeTensorShift_first_normalization_core
    (P T U : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlat (R := X.sheaf) P)
    (hT : CochainComplex.IsKFlat (R := X.sheaf) T)
    (hU : CochainComplex.IsKFlat (R := X.sheaf) U) :
    letI := schemeCanonicalTensorShift X
    letI : ∀ B : schemeDerivedCategory X, (tensorRight B).CommShift ℤ :=
      fun B ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) B
    ((α_ (DerivedCategory.Q.obj P⟦(1 : ℤ)⟧) (DerivedCategory.Q.obj T)
      (DerivedCategory.Q.obj U)).hom ≫
      ((tensorRight (DerivedCategory.Q.obj T ⊗ DerivedCategory.Q.obj U)).commShiftIso
        (1 : ℤ)).hom.app (DerivedCategory.Q.obj P)) ≫
      schemeTensorShiftTargetComparison X P T U =
      schemeTensorShiftSourceComparison X P T U ≫
      DerivedCategory.Q.map ((α_ (P⟦(1 : ℤ)⟧) T U).hom ≫
        (CochainComplex.mapBifunctorShift₁Iso P (T ⊗ U)
          (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace))) 1).hom) := by
  let := schemeCanonicalTensorShift X
  let : ∀ B : schemeDerivedCategory X, (tensorRight B).CommShift ℤ :=
    fun B ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) B
  simpa only [schemeTensorShiftTargetComparison, schemeTensorShiftSourceComparison,
    Category.assoc] using first_generic DerivedCategory.Q P T U
    (CochainComplex.mapBifunctorShift₁Iso P (T ⊗ U)
      (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace))) 1).hom
    (schemeTensorShift_binary_localization_square X P (T ⊗ U) (upstreamKFlat X P hP))

theorem schemeTensorShift_first_normalization
    (P T U : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlat (R := X.sheaf) P)
    (hT : CochainComplex.IsKFlat (R := X.sheaf) T)
    (hU : CochainComplex.IsKFlat (R := X.sheaf) U) :
    letI := schemeCanonicalTensorShift X
    letI : ∀ B : schemeDerivedCategory X, (tensorRight B).CommShift ℤ :=
      fun B ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) B
    let A := DerivedCategory.Q.obj P
    let K := DerivedCategory.Q.obj T
    let M := DerivedCategory.Q.obj U
    let c := schemeTensorShiftTargetComparison X P T U
    let v := schemeTensorShiftSourceComparison X P T U
    ((α_ (A⟦(1 : ℤ)⟧) K M).hom ≫
        ((tensorRight (K ⊗ M)).commShiftIso (1 : ℤ)).hom.app A) ≫ c =
      v ≫ DerivedCategory.Q.map ((α_ (P⟦(1 : ℤ)⟧) T U).hom ≫
        (CochainComplex.mapBifunctorShift₁Iso P (T ⊗ U)
          (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace))) 1).hom) := by
  simpa using schemeTensorShift_first_normalization_core X P T U hP hT hU

set_option linter.unusedVariables false in
/-- Second route normalization component.  Apply the localization shift square
first to `P,T` and then to `P ⊗ T,U`; K-flatness is preserved by tensoring.
Use lax monoidal associativity and naturality of the shift comparison to move
the two tensorators through the translated factors.  Their composite is the
localized complex associator shown on the right, by functoriality of `Q`.
Source: Stacks Project, Tag 06YH, second localization normalization calculation.
(blueprint: aux-sc-target-comparison-second) -/
theorem schemeTensorShift_second_normalization
    (P T U : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlat (R := X.sheaf) P)
    (hT : CochainComplex.IsKFlat (R := X.sheaf) T)
    (hU : CochainComplex.IsKFlat (R := X.sheaf) U) :
    letI := schemeCanonicalTensorShift X
    letI : ∀ B : schemeDerivedCategory X, (tensorRight B).CommShift ℤ :=
      fun B ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) B
    let A := DerivedCategory.Q.obj P
    let K := DerivedCategory.Q.obj T
    let M := DerivedCategory.Q.obj U
    let c := schemeTensorShiftTargetComparison X P T U
    let v := schemeTensorShiftSourceComparison X P T U
    ((((tensorRight K).commShiftIso (1 : ℤ)).hom.app A) ▷ M ≫
        ((tensorRight M).commShiftIso (1 : ℤ)).hom.app (A ⊗ K) ≫
        (α_ A K M).hom⟦(1 : ℤ)⟧') ≫ c =
      v ≫ DerivedCategory.Q.map
        ((CochainComplex.mapBifunctorShift₁Iso P T
          (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace))) 1).hom ▷ U ≫
        (CochainComplex.mapBifunctorShift₁Iso (P ⊗ T) U
          (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace))) 1).hom ≫
        (α_ P T U).hom⟦(1 : ℤ)⟧') := by
  let := schemeCanonicalTensorShift X
  let : ∀ B : schemeDerivedCategory X, (tensorRight B).CommShift ℤ :=
    fun B ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) B
  have hp := upstreamKFlat X P hP
  have ht := upstreamKFlat X T hT
  have hpt : (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)).kFlat (P ⊗ T) :=
    ObjectProperty.prop_tensor hp ht
  have hs₁ := schemeTensorShift_binary_localization_square X P T hp
  have hs₂ := schemeTensorShift_binary_localization_square X (P ⊗ T) U hpt
  simpa only [schemeTensorShiftTargetComparison, schemeTensorShiftSourceComparison,
    Category.assoc] using second_generic DerivedCategory.Q P T U
    (CochainComplex.mapBifunctorShift₁Iso P T
      (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace))) 1).hom
    (CochainComplex.mapBifunctorShift₁Iso (P ⊗ T) U
      (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace))) 1).hom hs₁ hs₂

theorem schemeTensorShift_localization_normalization
    (P T U : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlat (R := X.sheaf) P)
    (hT : CochainComplex.IsKFlat (R := X.sheaf) T)
    (hU : CochainComplex.IsKFlat (R := X.sheaf) U) :
    letI := schemeCanonicalTensorShift X
    letI : ∀ B : schemeDerivedCategory X, (tensorRight B).CommShift ℤ :=
      fun B ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) B
    let A := DerivedCategory.Q.obj P
    let K := DerivedCategory.Q.obj T
    let M := DerivedCategory.Q.obj U
    let c := schemeTensorShiftTargetComparison X P T U
    let v := schemeTensorShiftSourceComparison X P T U
    IsIso c ∧
      ((α_ (A⟦(1 : ℤ)⟧) K M).hom ≫
          ((tensorRight (K ⊗ M)).commShiftIso (1 : ℤ)).hom.app A) ≫ c =
        v ≫ DerivedCategory.Q.map ((α_ (P⟦(1 : ℤ)⟧) T U).hom ≫
          (CochainComplex.mapBifunctorShift₁Iso P (T ⊗ U)
            (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace))) 1).hom) ∧
      ((((tensorRight K).commShiftIso (1 : ℤ)).hom.app A) ▷ M ≫
          ((tensorRight M).commShiftIso (1 : ℤ)).hom.app (A ⊗ K) ≫
          (α_ A K M).hom⟦(1 : ℤ)⟧') ≫ c =
        v ≫ DerivedCategory.Q.map
          ((CochainComplex.mapBifunctorShift₁Iso P T
            (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace))) 1).hom ▷ U ≫
          (CochainComplex.mapBifunctorShift₁Iso (P ⊗ T) U
            (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace))) 1).hom ≫
          (α_ P T U).hom⟦(1 : ℤ)⟧') := by
  dsimp
  exact ⟨schemeTensorShift_targetComparison_isIso X P T U hP hT hU,
    schemeTensorShift_first_normalization X P T U hP hT hU,
    schemeTensorShift_second_normalization X P T U hP hT hU⟩

end AlgebraicGeometry
```

### Sheaf.CategoryTheory.IntegerShiftFromOne

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Data.Int.Basic

/-! # Extending a degree-one shift comparison

Source: iteration and inverse iteration in the proof of
lem-sc-derived-pullback-tensor-unit-shift, using the shift addition isomorphisms.
(blueprint: lem-sc-integer-shift-from-one).
-/

@[expose] public section
set_option autoImplicit false

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
  (F : C ⥤ D)
local notation "I" n => shiftFunctor C n ⋙ F ≅ F ⋙ shiftFunctor D n
private noncomputable def predecessor (a : I(1 : ℤ)) (n : ℤ) (e : I(n + 1)) : I n :=
  ((whiskeringRight C D D).obj (shiftFunctor D (1 : ℤ))).preimageIso
    (Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (Iso.symm a) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (shiftFunctorAdd C n 1).symm F ≪≫ e ≪≫
      isoWhiskerLeft F (shiftFunctorAdd D n 1) ≪≫
      (Functor.associator _ _ _).symm)

private lemma add_predecessor (a : I(1 : ℤ)) (n : ℤ) (e : I(n + 1)) :
    CommShift.isoAdd (predecessor F a n e) a = e := by
  ext X
  simp only [CommShift.isoAdd_hom_app]
  have h := ((whiskeringRight C D D).obj (shiftFunctor D (1 : ℤ))).map_preimage
    (show (shiftFunctor C n ⋙ F) ⋙ shiftFunctor D (1 : ℤ) ⟶
      (F ⋙ shiftFunctor D n) ⋙ shiftFunctor D (1 : ℤ) from
      (Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (Iso.symm a) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (shiftFunctorAdd C n 1).symm F ≪≫ e ≪≫
        isoWhiskerLeft F (shiftFunctorAdd D n 1) ≪≫
        (Functor.associator _ _ _).symm).hom)
  have hh := NatTrans.congr_app h X
  dsimp [predecessor, Functor.preimageIso] at hh ⊢
  rw [hh]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← F.map_comp_assoc,
    Iso.hom_inv_id_app, F.map_id, Category.id_comp, Category.comp_id]

private lemma isoAdd'_left_injective {i j k : ℤ} (h : i + j = k)
    (b : I j) {e e' : I i} (he : CommShift.isoAdd' h e b = CommShift.isoAdd' h e' b) :
    e = e' := by
  ext X
  apply (shiftFunctor D j).map_injective
  apply (cancel_mono ((shiftFunctorAdd' D i j k h).inv.app (F.obj X))).1
  apply (cancel_epi (b.hom.app ((shiftFunctor C i).obj X))).1
  apply (cancel_epi (F.map ((shiftFunctorAdd' C i j k h).hom.app X))).1
  simpa only [CommShift.isoAdd'_hom_app, Category.assoc] using
    congrArg (fun t ↦ t.hom.app X) he

private noncomputable def iterated (a : I(1 : ℤ)) (n : ℤ) : I n :=
  Int.inductionOn' n 0 (CommShift.isoZero F ℤ)
    (fun k _ e ↦ CommShift.isoAdd e a)
    (fun k _ e ↦ predecessor F a (k - 1)
      (CommShift.isoAdd' (show k + 0 = k - 1 + 1 by omega) e (CommShift.isoZero F ℤ)))

private lemma iterated_zero (a : I(1 : ℤ)) : iterated F a 0 = CommShift.isoZero F ℤ := by
  exact Int.inductionOn'_self

private lemma iterated_succ (a : I(1 : ℤ)) (n : ℤ) :
    iterated F a (n + 1) = CommShift.isoAdd (iterated F a n) a := by
  by_cases hn : 0 ≤ n
  · exact Int.inductionOn'_add_one hn
  · have hn' : n + 1 ≤ 0 := by omega
    have h := Int.inductionOn'_sub_one (motive := fun n ↦ I n) (z := n + 1)
      (zero := CommShift.isoZero F ℤ)
      (succ := fun k _ e ↦ CommShift.isoAdd e a)
      (pred := fun k _ e ↦ predecessor F a (k - 1)
        (CommShift.isoAdd' (show k + 0 = k - 1 + 1 by omega) e
          (CommShift.isoZero F ℤ))) hn'
    rw! [show n + 1 - 1 = n by omega] at h
    simp only [CommShift.isoAdd'_isoZero] at h
    have hh : iterated F a n = predecessor F a n (iterated F a (n + 1)) := by
      exact h
    rw [hh, add_predecessor]

private lemma iterated_succ' (a : I(1 : ℤ)) (n k : ℤ) (h : n + 1 = k) :
    iterated F a k = CommShift.isoAdd' h (iterated F a n) a := by
  subst k
  exact iterated_succ F a n

private lemma iterated_add' (a : I(1 : ℤ)) (n m k : ℤ) (h : n + m = k) :
    iterated F a k = CommShift.isoAdd' h (iterated F a n) (iterated F a m) := by
  induction m using Int.inductionOn' (b := 0) generalizing k with
  | zero =>
    have hk : k = n := by omega
    cases hk
    rw [iterated_zero]
    exact (CommShift.isoAdd'_isoZero (F := F) (iterated F a n)).symm
  | succ m hm ih =>
    rw [iterated_succ' F a (n + m) k (by omega), ih (n + m) rfl, iterated_succ]
    exact CommShift.isoAdd'_assoc (iterated F a n) (iterated F a m) a
      rfl rfl (by omega)
  | pred m hm ih =>
    apply isoAdd'_left_injective F (show k + 1 = n + m by omega) a
    rw [← iterated_succ' F a k (n + m) (by omega), ih (n + m) rfl]
    rw [CommShift.isoAdd'_assoc (iterated F a n) (iterated F a (m - 1)) a
      h (show m - 1 + 1 = m by omega) (show n + (m - 1) + 1 = n + m by omega)]
    rw [← iterated_succ' F a (m - 1) m (by omega)]


/-- A natural isomorphism commuting with translation by one extends to an integer
shift structure.

Source: the iteration step of lem-sc-derived-pullback-tensor-unit-shift.
(blueprint: lem-sc-integer-shift-from-one).

Proof. Postcomposition with shift by one is fully faithful. Given a comparison
at n+1, compose its hom with the inverse of a and with the source and target
shift addition maps, then take its unique preimage under that postcomposition.
This gives the comparison at n. Functor.map_preimage and cancellation show that
adding a to it recovers the given comparison at n+1. Addition on the right by
any comparison is injective, by faithfulness of its shift and cancellation of
its isomorphisms. Start at the canonical zero comparison and use integer
recursion, adding a upwards and taking the preimage downwards. The successor
identity holds on both sides of zero by the inverse-step calculation. Prove the
addition identity by integer induction on the second summand: the zero case is
the zero identity; the successor case is CommShift.isoAdd'_assoc; the predecessor
case follows by adding a on the right, using associativity and the successor
identity, then cancelling. The comparison at one is a by the left zero identity.
This proves both CommShift equations and works also for zero functors and zero
categories. -/
theorem exists_commShift_of_one
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) (a : shiftFunctor C (1 : ℤ) ⋙ F ≅ F ⋙ shiftFunctor D (1 : ℤ)) :
    ∃ s : F.CommShift ℤ, letI := s
      F.commShiftIso (1 : ℤ) = a := by
  let s : F.CommShift ℤ :=
    { commShiftIso := iterated F a
      commShiftIso_zero := iterated_zero F a
      commShiftIso_add := fun n m ↦ iterated_add' F a n m (n + m) rfl }
  refine ⟨s, ?_⟩
  change iterated F a (0 + 1) = a
  rw [iterated_succ, iterated_zero]
  exact CommShift.isoZero_isoAdd'_ a

end CategoryTheory.Functor
```

### Sheaf.CategoryTheory.NatTransFromResolvingClass

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions

/-! # Extending a natural comparison from a resolving class

Source: Stacks Project, Tag 06YJ, resolving-class argument, and Tag 04VC,
right fractions. (blueprint: lem-sc-nattrans-from-resolving-class).
-/

@[expose] public section
set_option autoImplicit false
universe u v u' v'
open CategoryTheory
namespace CategoryTheory

/-- A comparison out of a functor inverting weak equivalences extends from a full
resolving class. The target functor need not invert weak equivalences.

Source: Stacks Project, Tags 06YJ and 04VC, resolving-class and right-fraction arguments.
Proof. Choose a resolution s_X : P_X → X. Set β_X = A(s_X)⁻¹ α_P_X B(s_X).
For any arrow t : P → X from a resolving object, the right Ore condition supplies
a common source for t and s_X. Resolve that source once more. Naturality of α
on the resulting two arrows and cancellation of A of the weak equivalence show
A(t) β_X = α_P B(t). Applying this formula to a resolution of the source of an
arbitrary arrow proves naturality of β. Applying it to an identity proves β_P = α_P.
The argument uses only invertibility of A(s), and therefore also works for zero
objects and for a resolving class containing all objects.
(blueprint: lem-sc-nattrans-from-resolving-class). -/
theorem exists_natTrans_from_resolvingClass
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
    (P : C → Prop)
    (hres : ∀ X : C, ∃ (R : C) (s : R ⟶ X), P R ∧ W s)
    (A B : C ⥤ D) (hA : W.IsInvertedBy A)
    (α : ∀ X : C, P X → (A.obj X ⟶ B.obj X))
    (hα : ∀ (X Y : C) (hX : P X) (hY : P Y) (s : X ⟶ Y),
      A.map s ≫ α Y hY = α X hX ≫ B.map s) :
    ∃ β : A ⟶ B, ∀ (X : C) (hX : P X), β.app X = α X hX := by
  classical
  choose R s hR hs using hres
  have hiso (X : C) : IsIso (A.map (s X)) := hA _ (hs X)
  let β (X : C) : A.obj X ⟶ B.obj X :=
    inv (A.map (s X)) ≫ α (R X) (hR X) ≫ B.map (s X)
  have hchosen (X : C) :
      A.map (s X) ≫ β X = α (R X) (hR X) ≫ B.map (s X) := by
    dsimp only [β]
    simp
  have hfac (X Y : C) (hX : P X) (t : X ⟶ Y) :
      A.map t ≫ β Y = α X hX ≫ B.map t := by
    obtain ⟨z, hz⟩ := (MorphismProperty.LeftFraction.mk t (s Y) (hs Y)).exists_rightFraction
    let a := s z.X' ≫ z.s
    let b := s z.X' ≫ z.f
    have hab : a ≫ t = b ≫ s Y := by
      dsimp only [a, b]
      rw [Category.assoc, hz, ← Category.assoc]
    have ha : W a := W.comp_mem _ _ (hs z.X') z.hs
    have : IsIso (A.map a) := hA _ ha
    apply (cancel_epi (A.map a)).1
    calc
      A.map a ≫ A.map t ≫ β Y = A.map b ≫ A.map (s Y) ≫ β Y := by
        rw [← A.map_comp_assoc, hab, A.map_comp_assoc]
      _ = A.map b ≫ α (R Y) (hR Y) ≫ B.map (s Y) := by rw [hchosen]
      _ = α (R z.X') (hR z.X') ≫ B.map b ≫ B.map (s Y) := by
        rw [← Category.assoc, hα _ _ (hR z.X') (hR Y) b, Category.assoc]
      _ = α (R z.X') (hR z.X') ≫ B.map a ≫ B.map t := by
        rw [← B.map_comp, ← hab, B.map_comp]
      _ = A.map a ≫ α X hX ≫ B.map t := by
        rw [← Category.assoc, ← hα _ _ (hR z.X') hX a, Category.assoc]
  refine ⟨{ app := β, naturality := ?_ }, ?_⟩
  · intro X Y f
    apply (cancel_epi (A.map (s X))).1
    calc
      A.map (s X) ≫ A.map f ≫ β Y = A.map (s X ≫ f) ≫ β Y := by
        rw [A.map_comp, Category.assoc]
      _ = α (R X) (hR X) ≫ B.map (s X ≫ f) := hfac _ _ (hR X) _
      _ = (A.map (s X) ≫ β X) ≫ B.map f := by
        rw [B.map_comp, hchosen, Category.assoc]
      _ = A.map (s X) ≫ β X ≫ B.map f := Category.assoc _ _ _
  · intro X hX
    simpa only [Functor.map_id, Category.id_comp, Category.comp_id] using hfac X X hX (𝟙 X)

end CategoryTheory
```

## New

Each listed module is withdrawn through deleted.txt and materialized by
deliver3.py as the following empty module:

```lean
module

/-! Withdrawn: no declarations remain. -/
```

The 35 existing DAG nodes remain with only their Lean attachment removed
(`lean: null` in their sandbox copies). Their mathematical statements and plans stay.
The replacement route already landed in P3; no replacement proof is resubmitted.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.RelativeBiprodConeExtension | unclaimed | Withdrawn together; no outside importer remains. |
| Sheaf.Algebra.Homology.TensorShiftOneAssociator | unclaimed | Withdrawn together; no outside importer remains. |
| Sheaf.AlgebraicGeometry.BoundedFlatModelNormalization | E2 | Withdrawn together; no outside importer remains. |
| Sheaf.AlgebraicGeometry.CompactFlatBarUnionAugmentation | unclaimed | Withdrawn together; no outside importer remains. |
| Sheaf.AlgebraicGeometry.CompactFlatGeneratorCover | unclaimed | Withdrawn together; no outside importer remains. |
| Sheaf.AlgebraicGeometry.CompactFlatGeneratorRelativeExtension | unclaimed | Withdrawn together; no outside importer remains. |
| Sheaf.AlgebraicGeometry.CompactFlatGeneratorTowerResolution | unclaimed | Withdrawn together; no outside importer remains. |
| Sheaf.AlgebraicGeometry.CompactFlatTelescopeBarEnlargement | unclaimed | Withdrawn together; no outside importer remains. |
| Sheaf.AlgebraicGeometry.DerivedPullbackKFlatCounitAdjustmentFactor | unclaimed | Withdrawn together; no outside importer remains. |
| Sheaf.AlgebraicGeometry.FlatComparisonPreservesCountableCoproducts | unclaimed | Withdrawn together; no outside importer remains. |
| Sheaf.AlgebraicGeometry.FlatTelescopeArrowBarData | unclaimed | Withdrawn together; no outside importer remains. |
| Sheaf.AlgebraicGeometry.FlatTelescopeArrowCocycles | unclaimed | Withdrawn together; no outside importer remains. |
| Sheaf.AlgebraicGeometry.FlatTelescopeArrowDiagram | unclaimed | Withdrawn together; no outside importer remains. |
| Sheaf.AlgebraicGeometry.FlatTelescopeNormalizationIsIso | unclaimed | Withdrawn together; no outside importer remains. |
| Sheaf.AlgebraicGeometry.FlatTelescopeNormalizationUnshiftedIsIso | unclaimed | Withdrawn together; no outside importer remains. |
| Sheaf.AlgebraicGeometry.FlatTelescopePullbackSumColimit | unclaimed | Withdrawn together; no outside importer remains. |
| Sheaf.AlgebraicGeometry.FlatTelescopeStageMapRefinement | unclaimed | Withdrawn together; no outside importer remains. |
| Sheaf.AlgebraicGeometry.FlatTelescopeStageNaturality | unclaimed | Withdrawn together; no outside importer remains. |
| Sheaf.AlgebraicGeometry.FlatTelescopeSumComparisonIsIso | unclaimed | Withdrawn together; no outside importer remains. |
| Sheaf.AlgebraicGeometry.FlatTelescopeSumModels | unclaimed | Withdrawn together; no outside importer remains. |
| Sheaf.AlgebraicGeometry.FlatTelescopeTargetRefinement | unclaimed | Withdrawn together; no outside importer remains. |
| Sheaf.AlgebraicGeometry.KFlatLocalizedConePresentation | unclaimed | Withdrawn together; no outside importer remains. |
| Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitAssociativity | unclaimed | Withdrawn together; no outside importer remains. |
| Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShiftAssociator | unclaimed | Withdrawn together; no outside importer remains. |
| Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShiftAssociatorKFlatOne | unclaimed | Withdrawn together; no outside importer remains. |
| Sheaf.AlgebraicGeometry.SchemeTensorShiftBinaryLocalizationSquare | unclaimed | Withdrawn together; no outside importer remains. |
| Sheaf.AlgebraicGeometry.SchemeTensorShiftLocalizationNormalization | unclaimed | Withdrawn together; no outside importer remains. |
| Sheaf.CategoryTheory.IntegerShiftFromOne | unclaimed | Withdrawn together; no outside importer remains. |
| Sheaf.CategoryTheory.NatTransFromResolvingClass | unclaimed | Withdrawn together; no outside importer remains. |

The current import audit preserves five side-route modules: CompactFlatFiniteSubcomplexDiagrams, DerivedPullbackKFlatCounitData, DerivedPullbackShiftedUnitIsoData, FlatTelescopeStageMap, and SchemeCanonicalShiftUnitIso.
Their live clients and the retained route are unchanged. No forced adaptation is needed.

## Status

landed 20261014T144457-L-564949 2026-10-14 (merge of deliver/E2/Sheaf.AlgebraicGeometry.BoundedFlatModelNormalization)
