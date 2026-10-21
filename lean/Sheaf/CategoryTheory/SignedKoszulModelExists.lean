/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.CategoryTheory.SignedKoszulCompletionModel
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Sheaf.CategoryTheory.SignedKoszulFiniteCoordinates
import Sheaf.Algebra.Homology.RoosCoordinatesQuasiIso
import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsCore
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# Existence and quasi-isomorphism invariance of the normalized negative Koszul model

Source: Stacks Project, algebraization.tex, Tag 0A0E, lemma-derived-completion-koszul,
and the explicit signed-coordinate refinement of the completion construction.
(blueprint: lem-cbc-signed-koszul-model-exists).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u v z w
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace KoszulConstruction
variable {E : Type u} [Category.{v} E] [Abelian E] [HasCountableProducts E]
variable (T : ℕ → CochainComplex E ℤ ⥤ CochainComplex E ℤ)
private def prod : CochainComplex E ℤ ⥤ CochainComplex E ℤ where
  obj K := ∏ᶜ (fun m ↦ (T m).obj K)
  map f := Limits.Pi.map (fun m ↦ (T m).map f)
  map_id K := by
    apply Pi.hom_ext
    intro m
    simp
  map_comp f g := by
    apply Pi.hom_ext
    intro m
    simp
@[reassoc] private theorem prod_map_π {K L : CochainComplex E ℤ} (f : K ⟶ L) (m : ℕ) :
    (prod T).map f ≫ Pi.π (fun m ↦ (T m).obj L) m =
      Pi.π (fun m ↦ (T m).obj K) m ≫ (T m).map f := by
  dsimp only [prod]
  exact Pi.map_π (fun m ↦ (T m).map f) m
private def proj (m : ℕ) : prod T ⟶ T m where
  app _ := Pi.π _ m
  naturality _ _ f := prod_map_π T f m
variable (step : ∀ m, T (m + 1) ⟶ T m)
private def shift : prod T ⟶ prod T where
  app K := Pi.lift (fun m ↦ (proj T (m + 1)).app K ≫ (step m).app K)
  naturality K L f := by
    dsimp only [prod, proj]
    apply Pi.hom_ext
    intro m
    simp only [Category.assoc, Pi.lift_π, Pi.map_π, Pi.lift_π_assoc,
      Pi.map_π_assoc]
    rw [(step m).naturality]
private def u : prod T ⟶ prod T := 𝟙 _ - shift T step
variable (inc : ∀ m, 𝟭 (CochainComplex E ℤ) ⟶ T m)
private def diag : 𝟭 (CochainComplex E ℤ) ⟶ prod T where
  app K := Pi.lift (fun m ↦ (inc m).app K)
  naturality K L f := by
    dsimp only [prod]
    apply Pi.hom_ext
    intro m
    simp only [Category.assoc, Pi.lift_π, Pi.map_π, Pi.lift_π_assoc]
    exact (inc m).naturality f
variable (hic : ∀ (m : ℕ) (K : CochainComplex E ℤ),
  (inc (m + 1)).app K ≫ (step m).app K = (inc m).app K)
include hic in
private theorem diag_u (K : CochainComplex E ℤ) :
    (diag T inc).app K ≫ (u T step).app K = 0 := by
  apply Pi.hom_ext
  intro m
  simp [u, shift, diag, proj, Preadditive.comp_sub, Preadditive.sub_comp,
    Category.assoc, hic]
private def d (K : CochainComplex E ℤ) (q : ℤ) :
    ((prod T).obj K).X q ⊞ ((prod T).obj K).X (q - 1) ⟶
      ((prod T).obj K).X (q + 1) ⊞ ((prod T).obj K).X ((q + 1) - 1) :=
  biprod.lift (biprod.fst ≫ ((prod T).obj K).d q (q + 1))
    (biprod.fst ≫ ((u T step).app K).f q ≫
        (((prod T).obj K).XIsoOfEq (Int.add_sub_cancel q 1).symm).hom -
      biprod.snd ≫ ((prod T).obj K).d (q - 1) ((q + 1) - 1))
private theorem d_sq (K : CochainComplex E ℤ) (q : ℤ) :
    d T step K q ≫ d T step K (q + 1) = 0 := by
  apply biprod.hom_ext
  · simp [d, Category.assoc]
  · simp only [d, Category.assoc, biprod.lift_snd, Preadditive.comp_sub,
      biprod.lift_fst_assoc, biprod.lift_snd_assoc, Preadditive.sub_comp]
    simp only [HomologicalComplex.d_comp_d, comp_zero, sub_zero]
    rw [← HomologicalComplex.Hom.comm_assoc]
    simp

private def fibObj (K : CochainComplex E ℤ) : CochainComplex E ℤ :=
  CochainComplex.of (fun q ↦ ((prod T).obj K).X q ⊞ ((prod T).obj K).X (q - 1))
    (d T step K) (d_sq T step K)

private def fibMap {K L : CochainComplex E ℤ} (f : K ⟶ L) : fibObj T step K ⟶ fibObj T step L :=
  CochainComplex.ofHom (fun q ↦
    biprod.map (((prod T).map f).f q) (((prod T).map f).f (q - 1))) (by
      intro q
      apply biprod.hom_ext
      · simp [fibObj, d, Category.assoc, HomologicalComplex.Hom.comm]
      · simp only [fibObj, CochainComplex.of_d, d, Category.assoc,
          biprod.lift_snd, Preadditive.comp_sub, biprod.map_fst_assoc,
          biprod.map_snd_assoc, biprod.map_snd, Preadditive.sub_comp,
          biprod.lift_snd_assoc]
        rw [HomologicalComplex.Hom.comm]
        congr 1
        rw [← HomologicalComplex.XIsoOfEq_hom_naturality]
        simpa only [HomologicalComplex.comp_f, Category.assoc] using
          congrArg (fun t ↦ biprod.fst ≫ t.f q ≫
            (((prod T).obj L).XIsoOfEq (Int.add_sub_cancel q 1).symm).hom)
            ((u T step).naturality f))

private def fib : CochainComplex E ℤ ⥤ CochainComplex E ℤ where
  obj := fibObj T step
  map := fibMap T step
  map_id K := by
    ext q : 1
    apply biprod.hom_ext <;> simp [fibMap, CochainComplex.ofHom]
  map_comp f g := by
    ext q : 1
    apply biprod.hom_ext <;> simp [fibMap, CochainComplex.ofHom, Category.assoc]
private def unitObj (hc : ∀ (m : ℕ) (K : CochainComplex E ℤ),
    (inc (m + 1)).app K ≫ (step m).app K = (inc m).app K)
    (K : CochainComplex E ℤ) : K ⟶ fibObj T step K :=
  CochainComplex.ofHom (fun q ↦ biprod.lift (((diag T inc).app K).f q) 0) (by
    intro q
    apply biprod.hom_ext
    · simp [fibObj, d, Category.assoc, HomologicalComplex.Hom.comm]
    · have hz := congrArg (fun t ↦ t.f q) (diag_u T step inc hc K)
      simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] at hz
      simp only [fibObj, CochainComplex.of_d, d, Category.assoc, biprod.lift_snd,
        Preadditive.comp_sub, biprod.lift_fst_assoc, biprod.lift_snd_assoc,
        zero_comp, sub_zero]
      rw [← Category.assoc, hz]
      simp)
private def unit (hc : ∀ (m : ℕ) (K : CochainComplex E ℤ),
    (inc (m + 1)).app K ≫ (step m).app K = (inc m).app K) :
    𝟭 (CochainComplex E ℤ) ⟶ fib T step where
  app := unitObj T step inc hc
  naturality K L f := by
    ext q : 1
    apply biprod.hom_ext
    · simpa [unitObj, fib, fibMap, CochainComplex.ofHom] using
        congrArg (fun t ↦ t.f q) ((diag T inc).naturality f)
    · simp [unitObj, fib, fibMap, CochainComplex.ofHom]

variable [HasDerivedCategory.{w} E] [CountableAB4Star E]
private theorem productQuasiIso {K L : CochainComplex E ℤ} (f : K ⟶ L)
    (hf : ∀ m, QuasiIso ((T m).map f)) : QuasiIso ((prod T).map f) := by
  let Q : CochainComplex E ℤ ⥤ DerivedCategory E := DerivedCategory.Q
  let hK : IsLimit (Fan.mk (Q.obj ((prod T).obj K))
      (fun m ↦ Q.map ((proj T m).app K))) :=
    Fan.isLimitMapConeEquiv _ _ _
      (derivedCategory_termwiseProduct_isLimit E ℕ (fun m ↦ (T m).obj K)).some
  let hL : IsLimit (Fan.mk (Q.obj ((prod T).obj L))
      (fun m ↦ Q.map ((proj T m).app L))) :=
    Fan.isLimitMapConeEquiv _ _ _
      (derivedCategory_termwiseProduct_isLimit E ℕ (fun m ↦ (T m).obj L)).some
  have (m : ℕ) : IsIso (Q.map ((T m).map f)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso E _).2 (hf m)
  let g : Q.obj ((prod T).obj L) ⟶ Q.obj ((prod T).obj K) :=
    Fan.IsLimit.lift hK (fun m ↦ Q.map ((proj T m).app L) ≫ inv (Q.map ((T m).map f)))
  have hmap (m : ℕ) : Q.map ((prod T).map f) ≫ Q.map ((proj T m).app L) =
      Q.map ((proj T m).app K) ≫ Q.map ((T m).map f) := by
    rw [← Q.map_comp, ← Q.map_comp]
    exact congrArg Q.map (prod_map_π T f m)
  have hg (m : ℕ) : g ≫ Q.map ((proj T m).app K) =
      Q.map ((proj T m).app L) ≫ inv (Q.map ((T m).map f)) :=
    Fan.IsLimit.fac hK _ m
  have : IsIso (Q.map ((prod T).map f)) := ⟨⟨g, by
    apply Fan.IsLimit.hom_ext hK
    intro m
    simp only [fan_mk_proj, Category.id_comp]
    rw [Category.assoc, hg, ← Category.assoc, hmap]
    simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    , by
    apply Fan.IsLimit.hom_ext hL
    intro m
    simp only [fan_mk_proj, Category.id_comp, Category.assoc]
    rw [hmap, ← Category.assoc, hg]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]⟩⟩
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso E _).1 this
private theorem fibreQuasiIso {K L : CochainComplex E ℤ} (f : K ⟶ L)
    (hf : ∀ m, QuasiIso ((T m).map f)) : QuasiIso ((fib T step).map f) := by
  apply CochainComplex.quasiIso_of_roos_coordinates
    ((prod T).obj K) ((prod T).obj L) ((fib T step).obj K) ((fib T step).obj L)
    ((u T step).app K) ((u T step).app L)
    (fun _ ↦ Iso.refl _) (fun _ ↦ Iso.refl _)
    (by
      intro q
      simp only [fib, fibObj, CochainComplex.of_d, Iso.refl_hom,
        Category.comp_id, Category.id_comp, d,
        HomologicalComplex.XIsoOfEq, eqToIso.hom])
    (by
      intro q
      simp only [fib, fibObj, CochainComplex.of_d, Iso.refl_hom,
        Category.comp_id, Category.id_comp, d,
        HomologicalComplex.XIsoOfEq, eqToIso.hom])
    ((prod T).map f) ((fib T step).map f)
    (by intro q; simp [fib, fibMap, CochainComplex.ofHom])
  exact productQuasiIso T f hf
end KoszulConstruction
end


/-- The actual ordered negative Koszul tensors admit their pure-tensor-normalized
completion model, whose fibre takes quasi-isomorphisms to quasi-isomorphisms after
localization. This is a construction on one ringed site and makes no assertion about
comparison along a functor between coefficient categories.

Source: Stacks Project, algebraization.tex, Tag 0A0E, lemma-derived-completion-koszul;
the finite-coordinate expansion in steps 1 and 7 of
lem-cbc-exact-linear-koszul-fiber.
(blueprint: lem-cbc-signed-koszul-model-exists).

Proof in words:
Induct on the ordered list of sections. In one factor the two nonzero terms are the
unit module in degrees -1 and 0. Expand each tensor degree as the finite direct sum
indexed by subsets I, using the inverse right unitor followed by tensoring with the
specified basis of ones. The inverse maps multiply by coefficients in each rank-one
factor. The tensor universal property gives the two inverse equations and the stated
normalization. The total differential on this summand is d_K plus, for each i in I,
(-1)^(q+|I|) (-1)^#{j in I : j<i} a_i^(m+1) in the erased-i summand. Maps of K are
coordinatewise. Conjugate the diagonal matrix with entry product(i in I, a_i) by these
coordinates to define the transition. Its chain equation is the identity
product(i in I, a_i) a_j^(m+1) = a_j^(m+2) product(i in I.erase j, a_i).
The empty-subset inclusions are chain maps and commute with transitions.

Take the categorical product of the resulting functors, with its actual projections,
and define the shift by projection m as transition after projection m+1. The diagonal
has the empty-subset inclusion at every projection; hence (1-shift) diagonal is zero.
Construct the fibre degreewise as B^q biproduct B^(q-1), with differential
(dx, (1-shift)x-dy), diagonal action on maps, and unit (diagonal,0). The chain-map
identity for the shift cancels the mixed terms in the differential squared. Projection
identities give functoriality, naturality, and every remaining model equation.

Filter the finite-coordinate tensor by subset cardinality at most k, for k=0,...,r.
The erased-index differential lowers cardinality and d_K preserves it. The kth
successive quotient is the finite direct sum of degree-reindexed copies of K indexed
by subsets of cardinality k, with the inherited d_K differential (isomorphic to the
usual shifts by the standard degreewise sign twist). A quasi-isomorphism of K induces
a quasi-isomorphism on each such quotient. The long exact homology sequences of
these degreewise split short exact sequences and finite induction prove that every
tensor level preserves quasi-isomorphisms, including for unbounded K. Exact
countable products preserve these levelwise quasi-isomorphisms; equivalently, use
the localized product-cone statement lem-weil-derived-countable-products-core and
invertibility of the localized level maps. Apply lem-pe-roos-coordinates-quasi-iso
to the two-coordinate fibre map, and then use that Q inverts quasi-isomorphisms.
For the empty list only the empty subset occurs and every
transition is identity. No division or regular-sequence assumption occurs. -/
theorem exists_ringedSignedKoszulCompletionModel
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) {A : Type z} [CommRing A]
    (ρ : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat))
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [HasCountableProducts (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [CountableAB4Star (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    (r : ℕ) (a : Fin r → A) :
    ∃ M : RingedSignedKoszulCompletionModel R ρ a,
      (HomologicalComplex.quasiIso
        (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
        (.up ℤ)).IsInvertedBy (M.model.fibre ⋙ DerivedCategory.Q) := by
  let := Abelian.hasFiniteBiproducts (C := ringedSiteModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
  obtain ⟨c, s, i, hd, hm, hs, hi, hn, hic, hq⟩ :=
    exists_ringedSignedKoszulFiniteCoordinates R ρ r a
  let T := ringedNegativeKoszulTensor R ρ a
  let M : RingedSignedKoszulCompletionModel R ρ a := {
    model := {
      coordinates := c
      differential := hd
      map_coordinates := hm
      step := s
      step_coordinates := hs
      inclusion := i
      inclusion_coordinates := hi
      product := KoszulConstruction.prod T
      projection := KoszulConstruction.proj T
      isProduct := fun K ↦ limit.isLimit (Discrete.functor (fun m ↦ (T m).obj K))
      shift := KoszulConstruction.shift T s
      shift_projection := by
        intro m K
        exact Pi.lift_π _ _
      diagonal := KoszulConstruction.diag T i
      diagonal_projection := by
        intro m K
        exact Pi.lift_π _ _
      fibre := KoszulConstruction.fib T s
      fibreCoordinates := fun _ _ ↦ Iso.refl _
      fibre_differential := by
        intro K q
        simp only [KoszulConstruction.fib, KoszulConstruction.fibObj,
          CochainComplex.of_d, Iso.refl_hom, Iso.refl_inv, Category.id_comp,
          Category.comp_id, KoszulConstruction.d]
        rfl
      fibre_map := by
        intro K L f q
        simp [KoszulConstruction.fib, KoszulConstruction.fibObj, KoszulConstruction.fibMap,
          CochainComplex.ofHom]
      unit := KoszulConstruction.unit T s i hic
      unit_coordinates := by
        intro K q
        simp only [KoszulConstruction.unit, KoszulConstruction.unitObj,
          CochainComplex.ofHom, Iso.refl_hom, Category.comp_id] }
    normalization := hn }
  refine ⟨M, ?_⟩
  intro K L f hf
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
    (KoszulConstruction.fibreQuasiIso T s f (fun m ↦ hq m f hf))

end CategoryTheory
