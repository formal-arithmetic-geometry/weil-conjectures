/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups R1 and D2
-/
module

public import Sheaf.AlgebraicGeometry.TruncationExchangeCouple
public import Sheaf.CategoryTheory.ExactCoupleMorphism
public import WeilConjectures.CategoryTheory.CanonicalFiltration
import WeilConjectures.CategoryTheory.DerivedCoupleFunctoriality
import WeilConjectures.CategoryTheory.HalfPlaneConvergence
import WeilConjectures.CategoryTheory.DerivedCategory.PlusDevissage

/-!
# The abutment of the truncation exchange couples

Source: blueprint sec-proper-base-change/sk-thm-properbasechange,
lemma-weil-pbc-exact-couple-abutment, Detailed form; Stacks Tags 0DDE and 05TC
(blueprint: lemma-weil-pbc-exact-couple-abutment).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.privateModule false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.TruncationExchange
open CategoryTheory.BigradedExactCouple

namespace CategoryTheory.TruncationExchange

private theorem family_map_eq.{u₁, v₁}
    {B : Type u₁} [Category.{v₁} B]
    {D₁ D₂ E₁ E₂ : ℤ → ℤ → B}
    (hD : D₁ = D₂) (hE : E₁ = E₂) (r s : ℤ → ℤ → ℤ)
    (t₁ : ∀ p q, D₁ p q ⟶ E₁ (r p q) (s p q))
    (t₂ : ∀ p q, D₂ p q ⟶ E₂ (r p q) (s p q))
    (ht : HEq t₁ t₂) (p q : ℤ) :
    t₁ p q = eqToHom (congrFun (congrFun hD p) q) ≫ t₂ p q ≫
      eqToHom (congrFun (congrFun hE (r p q)) (s p q)).symm := by
  subst D₂ E₂
  cases ht
  simp

private theorem family_map_eq_shift.{u₁, v₁}
    {B : Type u₁} [Category.{v₁} B]
    {D₁ D₂ E₁ E₂ : ℤ → ℤ → B}
    (hD : D₁ = D₂) (hE : E₁ = E₂) (r₁ s₁ r₂ s₂ : ℤ → ℤ → ℤ)
    (hr : r₁ = r₂) (hs : s₁ = s₂)
    (t₁ : ∀ p q, D₁ p q ⟶ E₁ (r₁ p q) (s₁ p q))
    (t₂ : ∀ p q, D₂ p q ⟶ E₂ (r₂ p q) (s₂ p q))
    (ht : HEq t₁ t₂) (p q : ℤ) :
    t₁ p q = eqToHom (congrFun (congrFun hD p) q) ≫ t₂ p q ≫
      eqToHom ((congrFun (congrFun hE (r₁ p q)) (s₁ p q)).trans
        (congrArg₂ E₂ (congrFun (congrFun hr p) q)
          (congrFun (congrFun hs p) q))).symm := by
  subst D₂ E₂ r₂ s₂
  cases ht
  simp

private theorem initialG_eq.{u₀, v, w, u₁, v₁, w₁}
    {C : Type u₀} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {B : Type u₁} [Category.{v₁} B] [Abelian B] [HasDerivedCategory.{w₁} B]
    (F : DerivedCategory.Plus C ⥤ DerivedCategory.Plus B)
    (K : DerivedCategory.Plus C) (X : BigradedExactCouple B 0)
    (hD : X.D = D F K) (hE : X.E = E F K)
    (hg : HEq X.g (CategoryTheory.TruncationExchange.g F K)) (p q : ℤ) :
    X.initialG p q = eqToHom (congrFun (congrFun hD p) q) ≫
      CategoryTheory.TruncationExchange.g F K p q ≫
      eqToHom (congrFun (congrFun hE p) q).symm := by
  dsimp [initialG]
  rw [family_map_eq_shift hD hE (fun p _ ↦ p + (0 : ℕ))
    (fun _ q ↦ q - (0 : ℕ)) (fun p _ ↦ p) (fun _ q ↦ q)
    (by funext p q; omega) (by funext p q; omega) X.g
    (CategoryTheory.TruncationExchange.g F K) hg]
  simp only [Category.assoc, eqToHom_trans]

private noncomputable def canonicalMap.{u₀, v, w, u₁, v₁, w₁}
    {C : Type u₀} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {B : Type u₁} [Category.{v₁} B] [Abelian B] [HasDerivedCategory.{w₁} B]
    (F : DerivedCategory.Plus C ⥤ DerivedCategory.Plus B)
    (K : DerivedCategory.Plus C) (n p : ℤ) :
    D F K p (n - p) ⟶ (DerivedCategory.Plus.homologyFunctor B n).obj (F.obj K) :=
  eqToHom (congrArg (fun i ↦ (DerivedCategory.Plus.homologyFunctor B i).obj
    (F.obj (trunc K (n - p)))) (by omega : p + (n - p) = n)) ≫
    (DerivedCategory.Plus.homologyFunctor B n).map
      (F.map ((DerivedCategory.Plus.TStructure.t.truncLEι (n - p)).app K))

private theorem canonicalMap_comm.{u₀, v, w, u₁, v₁, w₁}
    {C : Type u₀} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {B : Type u₁} [Category.{v₁} B] [Abelian B] [HasDerivedCategory.{w₁} B]
    (F : DerivedCategory.Plus C ⥤ DerivedCategory.Plus B)
    (K : DerivedCategory.Plus C) (n p : ℤ) :
    alpha F K (p + 1) (n - (p + 1)) ≫
      eqToHom (by congr 1 <;> omega :
        D F K (p + 1 - 1) (n - (p + 1) + 1) = D F K p (n - p)) ≫
      canonicalMap F K n p = canonicalMap F K n (p + 1) := by
  dsimp [alpha, canonicalMap]
  simp only [Category.assoc, eqToHom_trans_assoc]
  rw [← eqToHom_naturality
    (fun iq : ℤ × ℤ ↦ (DerivedCategory.Plus.homologyFunctor B iq.1).map
      (F.map ((DerivedCategory.Plus.TStructure.t.truncLEι iq.2).app K)))
    (show (p + 1 + (n - (p + 1)), n - (p + 1) + 1) = (n, n - p) by
      ext <;> omega)]
  rw [← Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
  have hinc (q : ℤ) : (eqToHom (congrArg (trunc K)
      (by omega : q = (q + 1) - 1)) ≫ inclusion K (q + 1)) ≫
      (DerivedCategory.Plus.TStructure.t.truncLEι (q + 1)).app K =
      (DerivedCategory.Plus.TStructure.t.truncLEι q).app K := by
    simp only [inclusion, Category.assoc,
      Triangulated.TStructure.natTransTruncLEOfLE_ι_app]
    simpa only [eqToHom_refl, Category.comp_id] using
      (eqToHom_naturality (fun j ↦
        (DerivedCategory.Plus.TStructure.t.truncLEι j).app K)
        (by omega : q = (q + 1) - 1)).symm
  rw [hinc]
  exact eqToHom_naturality
    (fun i ↦ (DerivedCategory.Plus.homologyFunctor B i).map
      (F.map ((DerivedCategory.Plus.TStructure.t.truncLEι (n - (p + 1))).app K)))
    (by omega : p + 1 + (n - (p + 1)) = n)

private theorem canonicalMap_naturality.{u₀, v, w, u₁, v₁, w₁}
    {C : Type u₀} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {B : Type u₁} [Category.{v₁} B] [Abelian B] [HasDerivedCategory.{w₁} B]
    {F G : DerivedCategory.Plus C ⥤ DerivedCategory.Plus B} (τ : F ⟶ G)
    (K : DerivedCategory.Plus C) (n p : ℤ) :
    canonicalMap F K n p ≫ (DerivedCategory.Plus.homologyFunctor B n).map (τ.app K) =
      tD τ K p (n - p) ≫ canonicalMap G K n p := by
  dsimp [canonicalMap, tD]
  rw [← Category.assoc ((DerivedCategory.Plus.homologyFunctor B (p + (n - p))).map
    (τ.app (trunc K (n - p)))), eqToHom_naturality
      (fun m ↦ (DerivedCategory.Plus.homologyFunctor B m).map
        (τ.app (trunc K (n - p)))) (by omega : p + (n - p) = n)]
  simp only [Category.assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, τ.naturality]

private theorem canonical_iso.{u₀, v, w, u₁, v₁, w₁}
    {C : Type u₀} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {B : Type u₁} [Category.{v₁} B] [Abelian B] [HasDerivedCategory.{w₁} B]
    (F : DerivedCategory.Plus C ⥤ DerivedCategory.Plus B)
    (K : DerivedCategory.Plus C) (X : BigradedExactCouple B 0)
    (hD : X.D = D F K) (hα : HEq X.alpha (alpha F K))
    (n : ℤ) (A : X.AlphaColimit n) (hA : A.obj = X.D 0 n)
    (h0 : A.ι 0 ≫ eqToHom hA = eqToHom (by congr 1; omega))
    (hc : IsIso ((DerivedCategory.Plus.homologyFunctor B n).map
      (F.map ((DerivedCategory.Plus.TStructure.t.truncLEι n).app K)))) :
    ∃ i : A.obj ≅ (DerivedCategory.Plus.homologyFunctor B n).obj (F.obj K),
      HEq i.hom ((DerivedCategory.Plus.homologyFunctor B n).map
        (F.map ((DerivedCategory.Plus.TStructure.t.truncLEι n).app K))) ∧
      ∀ p : ℤ, A.ι p ≫ i.hom =
        eqToHom (congrFun (congrFun hD p) (n - p)) ≫ canonicalMap F K n p := by
  let k (p : ℤ) := eqToHom (congrFun (congrFun hD p) (n - p)) ≫ canonicalMap F K n p
  have hk (p : ℤ) : X.alphaDiagonal n p ≫ k p = k (p + 1) := by
    dsimp [k, alphaDiagonal]
    rw [family_map_eq hD hD (fun p _ ↦ p - 1) (fun _ q ↦ q + 1)
      X.alpha (alpha F K) hα]
    simpa only [Category.assoc, eqToHom_trans_assoc] using
      congrArg (fun l ↦ eqToHom
        (congrFun (congrFun hD (p + 1)) (n - (p + 1))) ≫ l)
        (canonicalMap_comm F K n p)
  obtain ⟨c, hι, huniq⟩ := A.isColimit _ k hk
  have hc0 : c = eqToHom hA ≫
      eqToHom (congrFun (congrFun hD 0) n) ≫
      eqToHom (congrArg (fun j ↦ (DerivedCategory.Plus.homologyFunctor B j).obj
        (F.obj (trunc K n))) (by omega : 0 + n = n)) ≫
      (DerivedCategory.Plus.homologyFunctor B n).map
        (F.map ((DerivedCategory.Plus.TStructure.t.truncLEι n).app K)) := by
    have : IsIso (A.ι 0) := by
      have : IsIso (A.ι 0 ≫ eqToHom hA) := h0 ▸ inferInstance
      exact IsIso.of_isIso_comp_right _ (eqToHom hA)
    apply (cancel_epi (A.ι 0)).1
    rw [← Category.assoc (A.ι 0), h0, hι]
    dsimp [k, canonicalMap]
    simp only [eqToHom_trans_assoc]
    have hnat := eqToHom_naturality (fun q ↦
      (DerivedCategory.Plus.homologyFunctor B n).map
        (F.map ((DerivedCategory.Plus.TStructure.t.truncLEι q).app K))) (by omega : n - 0 = n)
    simpa only [eqToHom_refl, Category.comp_id, eqToHom_trans_assoc] using
      congrArg (fun l ↦ eqToHom
        ((congrFun (congrFun hD 0) (n - 0)).trans
          (congrArg (fun j ↦ (DerivedCategory.Plus.homologyFunctor B j).obj
            (F.obj (trunc K (n - 0)))) (by omega : 0 + (n - 0) = n))) ≫ l) hnat
  have : IsIso c := by rw [hc0]; infer_instance
  refine ⟨asIso c, ?_, hι⟩
  rw [show (asIso c).hom = c from rfl, hc0]
  simp only [eqToHom_trans_assoc]
  exact (eqToHom_comp_heq _ _)

private theorem terms_vanish.{u₀, v, w, u₁, v₁, w₁}
    {C : Type u₀} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {B : Type u₁} [Category.{v₁} B] [Abelian B] [HasDerivedCategory.{w₁} B]
    (F : DerivedCategory.Plus C ⥤ DerivedCategory.Plus B) [F.Additive]
    (hF : ∀ (Z : DerivedCategory.Plus C) (b : ℤ), Z.IsGE b →
      ∀ i : ℤ, i < b → IsZero ((DerivedCategory.Plus.homologyFunctor B i).obj (F.obj Z)))
    (K : DerivedCategory.Plus C) (a : ℤ)
    (hK : ∀ i : ℤ, i < a → IsZero ((DerivedCategory.Plus.homologyFunctor C i).obj K)) :
    (∀ p q : ℤ, q < a → IsZero (D F K p q)) ∧
      (∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero (E F K p q)) := by
  have htrunc (q : ℤ) (hq : q < a) : IsZero (trunc K q) := by
    apply IsZero.of_full_of_faithful_of_isZero (DerivedCategory.Plus.ι (C := C))
    apply DerivedCategory.isZero_of_forall_isZero_homology
    intro i
    change IsZero ((DerivedCategory.Plus.homologyFunctor C i).obj (trunc K q))
    by_cases hi : i ≤ q
    · have : IsIso ((DerivedCategory.Plus.homologyFunctor C i).map
          ((DerivedCategory.Plus.TStructure.t.truncLEι q).app K)) := by
        exact DerivedCategory.Plus.isIso_homologyFunctor_map_truncLTι_app K (q + 1) i
          (by omega)
      exact (hK i (by omega)).of_iso
        (asIso ((DerivedCategory.Plus.homologyFunctor C i).map
          ((DerivedCategory.Plus.TStructure.t.truncLEι q).app K)))
    · exact DerivedCategory.Plus.isZero_homology_of_isLE (trunc K q) q i (by omega)
  constructor
  · intro p q hq
    exact (DerivedCategory.Plus.homologyFunctor B (p + q)).map_isZero
      (F.map_isZero (htrunc q hq))
  · intro p q hpq
    rcases hpq with hp | hq
    · apply hF (layer K q) q ?_ (p + q) (by omega)
      exact DerivedCategory.Plus.TStructure.t.isGE_shift (sheaf K q) 0 (-q) q (by omega)
    · exact (DerivedCategory.Plus.homologyFunctor B (p + q)).map_isZero
        (F.map_isZero ((shiftFunctor (DerivedCategory.Plus C) (-q)).map_isZero
          ((DerivedCategory.Plus.singleFunctor C 0).map_isZero (hK q hq))))

private noncomputable def imageStepIso.{u₁, v₁}
    {B : Type u₁} [Category.{v₁} B] [Abelian B] {T H : B} (F : DecreasingFiltration T)
    (i : T ≅ H) (p : ℤ) : (F.step p : B) ≅ ((F.image i.hom).step p : B) := by
  have : Mono (factorThruImageSubobject ((F.step p).arrow ≫ i.hom)) :=
    mono_of_mono_fac (imageSubobject_arrow_comp ((F.step p).arrow ≫ i.hom))
  have : IsIso (factorThruImageSubobject ((F.step p).arrow ≫ i.hom)) :=
    isIso_of_mono_of_epi _
  exact asIso (factorThruImageSubobject ((F.step p).arrow ≫ i.hom))

private theorem imageStepIso_arrow.{u₁, v₁}
    {B : Type u₁} [Category.{v₁} B] [Abelian B] {T H : B} (F : DecreasingFiltration T)
    (i : T ≅ H) (p : ℤ) :
    (imageStepIso F i p).hom ≫ ((F.image i.hom).step p).arrow =
      (F.step p).arrow ≫ i.hom := imageSubobject_arrow_comp _

private noncomputable def imageGradedIso.{u₁, v₁}
    {B : Type u₁} [Category.{v₁} B] [Abelian B] {T H : B} (F : DecreasingFiltration T)
    (i : T ≅ H) (p : ℤ) : F.gradedPiece p ≅ (F.image i.hom).gradedPiece p := by
  apply cokernel.mapIso _ _ (imageStepIso F i (p + 1)) (imageStepIso F i p)
  apply (cancel_mono ((F.image i.hom).step p).arrow).1
  simp only [Category.assoc, imageStepIso_arrow, Subobject.ofLE_arrow_assoc,
    Subobject.ofLE_arrow]

private theorem imageGradedIso_π.{u₁, v₁}
    {B : Type u₁} [Category.{v₁} B] [Abelian B] {T H : B} (F : DecreasingFiltration T)
    (i : T ≅ H) (p : ℤ) :
    cokernel.π (Subobject.ofLE _ _ (F.antitone_step (by omega : p ≤ p + 1))) ≫
      (imageGradedIso F i p).hom =
      (imageStepIso F i p).hom ≫ cokernel.π
        (Subobject.ofLE _ _ ((F.image i.hom).antitone_step (by omega : p ≤ p + 1))) := by
  simp only [imageGradedIso, cokernel.mapIso_hom, cokernel.map, cokernel.π_desc]

/- TAKEN OUT at the upstream sync e47efb5a5 (2026-10-17): does not compile against the source;
returned as a stage-3 repair item.
set_option backward.isDefEq.respectTransparency false in
private theorem imageFiltration_factor.{u₁, v₁}
    {B : Type u₁} [Category.{v₁} B] [Abelian B]
    (X : BigradedExactCouple B 0) (n : ℤ) (A : X.AlphaColimit n)
    {H : B} (i : A.obj ≅ H) (p : ℤ)
    (h : ((X.imageFiltration n A).image i.hom).step p =
      imageSubobject (A.ι p ≫ i.hom)) :
    factorThruImageSubobject (A.ι p) ≫
      (imageStepIso (X.imageFiltration n A) i p).hom =
      factorThruImageSubobject (A.ι p ≫ i.hom) ≫
        eqToHom (congrArg (fun S : Subobject H ↦ (S : B)) h.symm) := by
  apply (cancel_mono (((X.imageFiltration n A).image i.hom).step p).arrow).1
  rw [Category.assoc, imageStepIso_arrow]
  rw [Category.assoc (factorThruImageSubobject (A.ι p ≫ i.hom)),
    Subobject.arrow_congr _ _ h.symm]
  change factorThruImageSubobject (A.ι p) ≫ (imageSubobject (A.ι p)).arrow ≫ i.hom = _
  rw [← Category.assoc, imageSubobject_arrow_comp, imageSubobject_arrow_comp]
-/

private theorem infinity_diagonal.{u₁, v₁}
    {B : Type u₁} [Category.{v₁} B] [Abelian B]
    (X : BigradedExactCouple B 0) (L : X.LimitSubobjects)
    (A : ∀ m : ℤ, X.AlphaColimit m)
    (he : ∀ p q : ℤ, ∃ e : X.pageInfinity L p q ≅
      (X.imageFiltration (p + q) (A (p + q))).gradedPiece p,
      X.toPageInfinity L p q ≫ e.hom = X.toGradedPiece A p q)
    (n p : ℤ) :
    ∃ e : X.pageInfinity L p (n - p) ≅ (X.imageFiltration n (A n)).gradedPiece p,
      X.toPageInfinity L p (n - p) ≫ e.hom =
        factorThruImageSubobject ((A n).ι p) ≫
          cokernel.π (Subobject.ofLE _ _
            ((X.imageFiltration n (A n)).antitone_step (by omega : p ≤ p + 1))) := by
  obtain ⟨e, he⟩ := he p (n - p)
  let h : p + (n - p) = n := by omega
  refine ⟨e ≪≫ eqToIso (congrArg
    (fun m ↦ (X.imageFiltration m (A m)).gradedPiece p) h), ?_⟩
  simp only [Iso.trans_hom, eqToIso.hom, ← Category.assoc, he]
  dsimp [toGradedPiece]
  rw [Category.assoc, eqToHom_naturality (fun m : ℤ ↦
    factorThruImageSubobject ((A m).ι p) ≫
      cokernel.π (Subobject.ofLE _ _
        ((X.imageFiltration m (A m)).antitone_step (by omega : p ≤ p + 1)))) h]
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

end CategoryTheory.TruncationExchange

namespace AlgebraicGeometry.Etale

/- TAKEN OUT at the upstream sync e47efb5a5 (2026-10-17): does not compile against the source;
returned as a stage-3 repair item.
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
-- Elaborating the dependent abutment and graded-piece witnesses requires additional heartbeats.
/ -- The two truncation couples converge with finite image filtrations, their canonical
abutments identify with the cohomology of the whole complexes, and their induced map is
cohomology of exchange, including on associated graded objects.
The parameters P and Q, with the ten data identifications, specify the two exact couples
of def-weil-pbc-truncation-exact-couples; they impose no additional geometric hypothesis.

Proof, Step 1: For q < a, upper truncation and the q-th layer vanish. Negative derived
functor vanishing (lem-weil-pbc-derived-functor-negative-vanishing) and exact inverse
image (lem-weil-pbc-exact-functor-bounded-below) give E = 0 for p < 0. Apply
thm-sp-half-plane-convergence to obtain canonical diagonal colimits, finite exhaustive
separated filtrations, and the canonical infinite-page comparisons.
Step 2: Both derived composites preserve lower cohomological bounds. Apply the proved
source-library truncation criterion
`DerivedCategory.Plus.isIso_homologyFunctor_map_map_truncLEι_app` to each composite.
The canonical maps from the diagonal terms into cohomology form a cocone; its universal
map is an isomorphism because its composite with the normalized zeroth leg is one.
Step 3: Composing the diagonal cocone maps with these isomorphisms gives the maps from
truncation at n-p into K. Their images are precisely the transported image filtrations
(def-sp-image-filtration). Naturality of cohomology/inverse-image comparison and exact
preservation of images identify the first filtration with g inverse image of the
filtration on H^n(Rf_*K) (def-weil-pbc-hypercohomology-filtrations).
Step 4: Naturality of derived exchange at truncLEι gives the displayed abutment square.
Step 5: Construct the exchange CoupleMorphism using the squares of
lem-weil-pbc-truncation-couple-morphism and apply lem-sp-derived-couple-functoriality
to the limiting subobjects already chosen by half-plane convergence. Construct the
filtration step maps by imageSubobjectMap and the graded maps by cokernel.map.
Transport the canonical infinite-page comparisons along the step isomorphisms induced
by the abutment isomorphisms. Their compatibility follows after cancellation of the
epimorphism toPageInfinity, using its square and the cokernel equations.
Source: blueprint lemma-weil-pbc-exact-couple-abutment, Detailed form, Proof;
Stacks Tags 0DDE, 05TC and 011Q
(blueprint: lemma-weil-pbc-exact-couple-abutment). - /
theorem truncation_exchange_exact_couple_abutment
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (a n : ℤ)
    (hK : ∀ q : ℤ, q < a → IsZero
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K))
    (P Q : BigradedExactCouple (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) 0)
    (hPD : P.D = D (truncationPhi f g) K)
    (hPE : P.E = E (truncationPhi f g) K)
    (_hPalpha : HEq P.alpha (alpha (truncationPhi f g) K))
    (_hPf : HEq P.f (CategoryTheory.TruncationExchange.f (truncationPhi f g) K))
    (_hPg : HEq P.g (CategoryTheory.TruncationExchange.g (truncationPhi f g) K))
    (hQD : Q.D = D (truncationPsi g' f') K)
    (hQE : Q.E = E (truncationPsi g' f') K)
    (_hQalpha : HEq Q.alpha (alpha (truncationPsi g' f') K))
    (_hQf : HEq Q.f (CategoryTheory.TruncationExchange.f (truncationPsi g' f') K))
    (_hQg : HEq Q.g (CategoryTheory.TruncationExchange.g (truncationPsi g' f') K)) :
    (∀ p q : ℤ, q < a → IsZero (P.D p q)) ∧
    (∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero (P.E p q)) ∧
    (∀ p q : ℤ, q < a → IsZero (Q.D p q)) ∧
    (∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero (Q.E p q)) ∧
    ∃ L : LimitSubobjects P, ∃ M : LimitSubobjects Q,
    ∃ A : ∀ m : ℤ, AlphaColimit P m, ∃ B : ∀ m : ℤ, AlphaColimit Q m,
    ∃ hA : ∀ m : ℤ, (A m).obj = P.D 0 m,
    ∃ hB : ∀ m : ℤ, (B m).obj = Q.D 0 m,
      (∀ m : ℤ, (A m).ι 0 ≫ eqToHom (hA m) = eqToHom (by congr 1; omega)) ∧
      (∀ m : ℤ, (B m).ι 0 ≫ eqToHom (hB m) = eqToHom (by congr 1; omega)) ∧
      P.ConvergesTo L A ∧ Q.ConvergesTo M B ∧
      (∀ m : ℤ, (P.imageFiltration m (A m)).IsFinite ∧
        (P.imageFiltration m (A m)).IsExhaustive ∧
        (P.imageFiltration m (A m)).IsSeparated) ∧
      (∀ m : ℤ, (Q.imageFiltration m (B m)).IsFinite ∧
        (Q.imageFiltration m (B m)).IsExhaustive ∧
        (Q.imageFiltration m (B m)).IsSeparated) ∧
      (∀ p q : ℤ, ∃ e : P.pageInfinity L p q ≅
        (P.imageFiltration (p + q) (A (p + q))).gradedPiece p,
        P.toPageInfinity L p q ≫ e.hom = P.toGradedPiece A p q) ∧
      (∀ p q : ℤ, ∃ e : Q.pageInfinity M p q ≅
        (Q.imageFiltration (p + q) (B (p + q))).gradedPiece p,
        Q.toPageInfinity M p q ≫ e.hom = Q.toGradedPiece B p q) ∧
      ∃ i : (A n).obj ≅ (_root_.DerivedCategory.Plus.homologyFunctor _ n).obj ((truncationPhi f
        g).obj K),
      ∃ j : (B n).obj ≅ (_root_.DerivedCategory.Plus.homologyFunctor _ n).obj ((truncationPsi g'
        f').obj K),
      HEq i.hom ((_root_.DerivedCategory.Plus.homologyFunctor _ n).map ((truncationPhi f g).map
        ((_root_.DerivedCategory.Plus.TStructure.t.truncLEι (n)).app K))) ∧
      HEq j.hom ((_root_.DerivedCategory.Plus.homologyFunctor _ n).map ((truncationPsi g' f').map
        ((_root_.DerivedCategory.Plus.TStructure.t.truncLEι (n)).app K))) ∧
      ∃ U : DecreasingFiltration ((_root_.DerivedCategory.Plus.homologyFunctor _ n).obj
        ((truncationPhi f g).obj K)),
      ∃ V : DecreasingFiltration ((_root_.DerivedCategory.Plus.homologyFunctor _ n).obj
        ((truncationPsi g' f').obj K)),
      U = (P.imageFiltration n (A n)).image i.hom ∧
      V = (Q.imageFiltration n (B n)).image j.hom ∧
      (∀ p : ℤ, U.step p = imageSubobject ((_root_.DerivedCategory.Plus.homologyFunctor _ n).map
        ((truncationPhi f g).map ((_root_.DerivedCategory.Plus.TStructure.t.truncLEι (n - p)).app
        K)))) ∧
      (∀ p : ℤ, V.step p = imageSubobject ((_root_.DerivedCategory.Plus.homologyFunctor _ n).map
        ((truncationPsi g' f').map ((_root_.DerivedCategory.Plus.TStructure.t.truncLEι (n -
        p)).app K)))) ∧
      (∀ p : ℤ, (Subobject.«exists» (((upperStar AddCommGrpCat.{u + 1}
        g).mapDerivedCategoryPlusHomologyFunctorIso n).symm.app ((lowerStar AddCommGrpCat.{u + 1}
        f).rightDerivedFunctorPlus.obj K)).hom).obj (U.step p) =
        imageSubobject ((upperStar AddCommGrpCat.{u + 1} g).map
          (imageSubobject ((_root_.DerivedCategory.Plus.homologyFunctor _ n).map ((lowerStar
            AddCommGrpCat.{u + 1} f).rightDerivedFunctorPlus.map
            ((_root_.DerivedCategory.Plus.TStructure.t.truncLEι (n - p)).app K)))).arrow)) ∧
      ∃ t : P.D 0 n ⟶ Q.D 0 n, HEq t (tD (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
        sq.toCommSq) K 0 n) ∧
      eqToHom (hA n) ≫ t ≫ eqToHom (hB n).symm ≫ j.hom =
        i.hom ≫ (_root_.DerivedCategory.Plus.homologyFunctor _ n).map ((derivedBaseChangeMapPlus
          AddCommGrpCat.{u + 1} sq.toCommSq).app K) ∧
      ∃ lift : ∀ p : ℤ, (U.step p : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) ⟶ (V.step p
        : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}),
      (∀ p : ℤ, lift p ≫ (V.step p).arrow =
        (U.step p).arrow ≫ (_root_.DerivedCategory.Plus.homologyFunctor _ n).map
          ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app K)) ∧
      ∃ gr : ∀ p : ℤ, U.gradedPiece p ⟶ V.gradedPiece p,
      (∀ p : ℤ,
        cokernel.π (Subobject.ofLE _ _ (U.antitone_step (by omega : p ≤ p + 1))) ≫
          gr p = lift p ≫
            cokernel.π (Subobject.ofLE _ _ (V.antitone_step (by omega : p ≤ p + 1)))) ∧
      ∃ z : ∀ p : ℤ, (L.Z p (n - p) : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) ⟶ (M.Z p
        (n - p) : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}),
      ∃ tInf : ∀ p : ℤ, P.pageInfinity L p (n - p) ⟶ Q.pageInfinity M p (n - p),
      (∀ p : ℤ, HEq (z p ≫ (M.Z p (n - p)).arrow)
        ((L.Z p (n - p)).arrow ≫
          eqToHom (congrFun (congrFun hPE p) (n - p)) ≫
          tE (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq) K p (n - p))) ∧
      (∀ p : ℤ,
        cokernel.π (Subobject.ofLE _ _ (limitBoundary_le_cycle P L p (n - p))) ≫
          tInf p = z p ≫
            cokernel.π (Subobject.ofLE _ _ (limitBoundary_le_cycle Q M p (n - p)))) ∧
      ∃ e : ∀ p : ℤ, P.pageInfinity L p (n - p) ≅ U.gradedPiece p,
      ∃ e' : ∀ p : ℤ, Q.pageInfinity M p (n - p) ≅ V.gradedPiece p,
      ∃ hU : ∀ p : ℤ, U.step p = imageSubobject ((A n).ι p ≫ i.hom),
      ∃ hV : ∀ p : ℤ, V.step p = imageSubobject ((B n).ι p ≫ j.hom),
      (∀ p : ℤ, P.toPageInfinity L p (n - p) ≫ (e p).hom =
        factorThruImageSubobject ((A n).ι p ≫ i.hom) ≫
        eqToHom (congrArg (fun S : Subobject _ ↦ (S : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u
          + 1})) (hU p).symm) ≫
        cokernel.π (Subobject.ofLE _ _ (U.antitone_step (by omega : p ≤ p + 1)))) ∧
      (∀ p : ℤ, Q.toPageInfinity M p (n - p) ≫ (e' p).hom =
        factorThruImageSubobject ((B n).ι p ≫ j.hom) ≫
        eqToHom (congrArg (fun S : Subobject _ ↦ (S : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u
          + 1})) (hV p).symm) ≫
        cokernel.π (Subobject.ofLE _ _ (V.antitone_step (by omega : p ≤ p + 1)))) ∧
      (∀ p : ℤ, (e p).hom ≫ gr p = tInf p ≫ (e' p).hom) := by
  have hPhi (Z : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) (b : ℤ) (hZ : Z.IsGE b)
      (i : ℤ) (hi : i < b) :
      IsZero ((_root_.DerivedCategory.Plus.homologyFunctor _ i).obj
        ((truncationPhi f g).obj Z)) := by
    have := hZ
    exact ((upperStar AddCommGrpCat.{u + 1} g).map_isZero
      (Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
        (lowerStar AddCommGrpCat.{u + 1} f) Z b hi)).of_iso
      (((upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategoryPlusHomologyFunctorIso i).app _).symm
  have hPsi (Z : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) (b : ℤ) (hZ : Z.IsGE b)
      (i : ℤ) (hi : i < b) :
      IsZero ((_root_.DerivedCategory.Plus.homologyFunctor _ i).obj
        ((truncationPsi g' f').obj Z)) := by
    have := hZ
    have : ((upperStar AddCommGrpCat.{u + 1} g').mapDerivedCategoryPlus.obj Z).IsGE b := by
      rw [← _root_.DerivedCategory.Plus.isGE_ι_obj_iff,
        _root_.DerivedCategory.isGE_iff]
      intro j hj
      exact ((upperStar AddCommGrpCat.{u + 1} g').map_isZero
        (_root_.DerivedCategory.Plus.isZero_homology_of_isGE Z b j hj)).of_iso
        (((upperStar AddCommGrpCat.{u + 1} g').mapDerivedCategoryPlusHomologyFunctorIso
          j).app _).symm
    exact Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
      (lowerStar AddCommGrpCat.{u + 1} f') _ b hi
  obtain ⟨hDP, hEP⟩ := terms_vanish (truncationPhi f g) hPhi K a hK
  obtain ⟨hDQ, hEQ⟩ := terms_vanish (truncationPsi g' f') hPsi K a hK
  have hDP' : ∀ p q : ℤ, q < a → IsZero (P.D p q) := by
    intro p q hq
    exact (hDP p q hq).of_iso (eqToIso (congrFun (congrFun hPD p) q))
  have hEP' : ∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero (P.E p q) := by
    intro p q hpq
    exact (hEP p q hpq).of_iso (eqToIso (congrFun (congrFun hPE p) q))
  have hDQ' : ∀ p q : ℤ, q < a → IsZero (Q.D p q) := by
    intro p q hq
    exact (hDQ p q hq).of_iso (eqToIso (congrFun (congrFun hQD p) q))
  have hEQ' : ∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero (Q.E p q) := by
    intro p q hpq
    exact (hEQ p q hpq).of_iso (eqToIso (congrFun (congrFun hQE p) q))
  let τ := derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq
  let d (p q : ℤ) : P.D p q ⟶ Q.D p q :=
    eqToHom (congrFun (congrFun hPD p) q) ≫ tD τ K p q ≫
      eqToHom (congrFun (congrFun hQD p) q).symm
  let e (p q : ℤ) : P.E p q ⟶ Q.E p q :=
    eqToHom (congrFun (congrFun hPE p) q) ≫ tE τ K p q ≫
      eqToHom (congrFun (congrFun hQE p) q).symm
  obtain ⟨_, hα, hg, hf, _⟩ := truncation_exchange_couple_morphism sq K
  let T : CoupleMorphism P Q :=
    { tD := d
      tE := e
      alpha_comm := by
        intro p q
        rw [family_map_eq hQD hQD (fun p _ ↦ p - 1) (fun _ q ↦ q + 1)
          Q.alpha (alpha (truncationPsi g' f') K) _hQalpha,
          family_map_eq hPD hPD (fun p _ ↦ p - 1) (fun _ q ↦ q + 1)
            P.alpha (alpha (truncationPhi f g) K) _hPalpha]
        simp only [d, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        rw [← Category.assoc (tD τ K p q), ← hα]
        simp only [Category.assoc]
        rfl
      f_comm := by
        intro p q
        rw [family_map_eq hQE hQD (fun p _ ↦ p + 2) (fun _ q ↦ q - 1)
          Q.f (CategoryTheory.TruncationExchange.f (truncationPsi g' f') K) _hQf,
          family_map_eq hPE hPD (fun p _ ↦ p + 2) (fun _ q ↦ q - 1)
            P.f (CategoryTheory.TruncationExchange.f (truncationPhi f g) K) _hPf]
        simp only [d, e, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
          Category.id_comp]
        rw [← Category.assoc (tE τ K p q), ← hf]
        simp only [Category.assoc]
        rfl
      g_comm := by
        intro p q
        apply (cancel_mono (eqToHom (show Q.E (p + (0 : ℕ)) (q - (0 : ℕ)) =
          Q.E p q by congr 1 <;> omega))).1
        simp only [Category.assoc]
        rw [eqToHom_naturality (fun pq : ℤ × ℤ ↦ e pq.1 pq.2)
          (show (p + (0 : ℕ), q - (0 : ℕ)) = (p, q) by ext <;> omega)]
        change d p q ≫ Q.initialG p q = P.initialG p q ≫ e p q
        rw [initialG_eq (truncationPsi g' f') K Q hQD hQE _hQg,
          initialG_eq (truncationPhi f g) K P hPD hPE _hPg]
        simp only [d, e, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
          Category.id_comp]
        rw [← Category.assoc (tD τ K p q), ← hg]
        simp only [Category.assoc]
        rfl }
  -- Use the same normalized colimits for the abutment and infinite-page comparisons.
  obtain ⟨L, A, hA, hA0, _, _, _, hAfin, hAinf, _, hAconv⟩ :=
    P.halfPlaneConvergence a hDP' hEP'
  obtain ⟨M, B, hB, hB0, _, _, _, hBfin, hBinf, _, hBconv⟩ :=
    Q.halfPlaneConvergence a hDQ' hEQ'
  have hi : IsIso ((_root_.DerivedCategory.Plus.homologyFunctor _ n).map
      ((truncationPhi f g).map
        ((_root_.DerivedCategory.Plus.TStructure.t.truncLEι n).app K))) :=
    _root_.DerivedCategory.Plus.isIso_homologyFunctor_map_map_truncLEι_app
      (truncationPhi f g) (fun Z b hb i hi ↦ hPhi Z b hb i hi) K n
  have hj : IsIso ((_root_.DerivedCategory.Plus.homologyFunctor _ n).map
      ((truncationPsi g' f').map
        ((_root_.DerivedCategory.Plus.TStructure.t.truncLEι n).app K))) :=
    _root_.DerivedCategory.Plus.isIso_homologyFunctor_map_map_truncLEι_app
      (truncationPsi g' f') (fun Z b hb i hi ↦ hPsi Z b hb i hi) K n
  obtain ⟨i, hi, hiι⟩ := canonical_iso (truncationPhi f g) K P hPD _hPalpha n
    (A n) (hA n) (hA0 n) hi
  obtain ⟨j, hj, hjι⟩ := canonical_iso (truncationPsi g' f') K Q hQD _hQalpha n
    (B n) (hB n) (hB0 n) hj
  let U := (P.imageFiltration n (A n)).image i.hom
  let V := (Q.imageFiltration n (B n)).image j.hom
  have hU (p : ℤ) : U.step p = imageSubobject ((A n).ι p ≫ i.hom) := by
    dsimp [U, DecreasingFiltration.image, BigradedExactCouple.imageFiltration]
    rw [← imageSubobject_comp_of_epi (factorThruImageSubobject ((A n).ι p))]
    simp only [imageSubobject_arrow_comp_assoc]
  have hV (p : ℤ) : V.step p = imageSubobject ((B n).ι p ≫ j.hom) := by
    dsimp [V, DecreasingFiltration.image, BigradedExactCouple.imageFiltration]
    rw [← imageSubobject_comp_of_epi (factorThruImageSubobject ((B n).ι p))]
    simp only [imageSubobject_arrow_comp_assoc]
  have hUtr (p : ℤ) : U.step p = imageSubobject
      ((_root_.DerivedCategory.Plus.homologyFunctor _ n).map
        ((truncationPhi f g).map
          ((_root_.DerivedCategory.Plus.TStructure.t.truncLEι (n - p)).app K))) := by
    simpa only [hiι, canonicalMap, Category.assoc, imageSubobject_iso_comp] using hU p
  have hVtr (p : ℤ) : V.step p = imageSubobject
      ((_root_.DerivedCategory.Plus.homologyFunctor _ n).map
        ((truncationPsi g' f').map
          ((_root_.DerivedCategory.Plus.TStructure.t.truncLEι (n - p)).app K))) := by
    simpa only [hjι, canonicalMap, Category.assoc, imageSubobject_iso_comp] using hV p
  let H := (_root_.DerivedCategory.Plus.homologyFunctor _ n).map (τ.app K)
  have hnat (p : ℤ) : ((A n).ι p ≫ i.hom) ≫ H =
      d p (n - p) ≫ ((B n).ι p ≫ j.hom) := by
    rw [hiι, hjι]
    dsimp [d, H]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← canonicalMap_naturality]
  have hnat0 : eqToHom (hA n) ≫ d 0 n ≫ eqToHom (hB n).symm ≫ j.hom =
      i.hom ≫ H := by
    have h0 := hnat 0
    have hAι : (A n).ι 0 = eqToHom
        ((show P.D 0 (n - 0) = P.D 0 n by congr 1; omega).trans (hA n).symm) := by
      apply (cancel_mono (eqToHom (hA n))).1
      simpa only [eqToHom_trans] using hA0 n
    have hBι : (B n).ι 0 = eqToHom
        ((show Q.D 0 (n - 0) = Q.D 0 n by congr 1; omega).trans (hB n).symm) := by
      apply (cancel_mono (eqToHom (hB n))).1
      simpa only [eqToHom_trans] using hB0 n
    rw [hAι, hBι] at h0
    have : IsIso ((A n).ι 0) := by rw [hAι]; infer_instance
    apply (cancel_epi ((A n).ι 0)).1
    rw [hAι]
    simp only [eqToHom_trans_assoc]
    have hd0 := eqToHom_naturality (fun pq : ℤ × ℤ ↦ d pq.1 pq.2)
        (show (0, n - 0) = (0, n) by ext <;> omega)
    have hd0' := congrArg (fun l ↦ l ≫ eqToHom (hB n).symm ≫ j.hom) hd0
    simp only [Category.assoc, eqToHom_trans_assoc] at hd0'
    rw [← hd0']
    simpa only [Category.assoc, eqToHom_trans_assoc] using h0.symm
  have hInv (p : ℤ) :
      (Subobject.«exists»
        (((upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategoryPlusHomologyFunctorIso
          n).symm.app
          ((lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctorPlus.obj K)).hom).obj
          (U.step p) =
        imageSubobject ((upperStar AddCommGrpCat.{u + 1} g).map
          (imageSubobject ((_root_.DerivedCategory.Plus.homologyFunctor _ n).map
            ((lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctorPlus.map
              ((_root_.DerivedCategory.Plus.TStructure.t.truncLEι (n - p)).app K)))).arrow) := by
    let c := (_root_.DerivedCategory.Plus.TStructure.t.truncLEι (n - p)).app K
    let R := (lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctorPlus
    let G := upperStar AddCommGrpCat.{u + 1} g
    let χ := (G.mapDerivedCategoryPlusHomologyFunctorIso n).symm
    have hχ := χ.hom.naturality (R.map c)
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hχ
    rw [hUtr, Subobject.exists_obj_eq_imageSubobject]
    rw [← imageSubobject_comp_of_epi (factorThruImageSubobject
      ((_root_.DerivedCategory.Plus.homologyFunctor _ n).map ((truncationPhi f g).map c)))]
    rw [← Category.assoc, imageSubobject_arrow_comp]
    change imageSubobject
      ((_root_.DerivedCategory.Plus.homologyFunctor _ n).map (G.mapDerivedCategoryPlus.map
        (R.map c)) ≫ χ.hom.app (R.obj K)) = _
    simp only [hχ, imageSubobject_iso_comp]
    rw [← imageSubobject_comp_of_epi (G.map (factorThruImageSubobject
      ((_root_.DerivedCategory.Plus.homologyFunctor _ n).map (R.map c))))]
    rw [← Functor.map_comp, imageSubobject_arrow_comp]
  let lift (p : ℤ) : (U.step p : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) ⟶
      (V.step p : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    eqToHom (congrArg (fun S : Subobject _ ↦
      (S : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})) (hU p)) ≫
      imageSubobjectMap (Arrow.homMk (d p (n - p)) H (hnat p).symm) ≫
      eqToHom (congrArg (fun S : Subobject _ ↦
        (S : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})) (hV p).symm)
  have hlift (p : ℤ) : lift p ≫ (V.step p).arrow = (U.step p).arrow ≫ H := by
    dsimp only [lift]
    simp only [Category.assoc]
    rw [Subobject.arrow_congr _ _ (hV p).symm,
      imageSubobjectMap_arrow, ← Category.assoc,
      Subobject.arrow_congr _ _ (hU p)]
    rfl
  have hstep (p : ℤ) :
      Subobject.ofLE _ _ (U.antitone_step (by omega : p ≤ p + 1)) ≫ lift p =
        lift (p + 1) ≫ Subobject.ofLE _ _ (V.antitone_step (by omega : p ≤ p + 1)) := by
    apply (cancel_mono (V.step p).arrow).1
    rw [Category.assoc, hlift, ← Category.assoc, Subobject.ofLE_arrow,
      Category.assoc, Subobject.ofLE_arrow, hlift]
  let gr (p : ℤ) : U.gradedPiece p ⟶ V.gradedPiece p :=
    cokernel.map _ _ (lift (p + 1)) (lift p) (hstep p)
  have hgr (p : ℤ) :
      cokernel.π (Subobject.ofLE _ _ (U.antitone_step (by omega : p ≤ p + 1))) ≫ gr p =
        lift p ≫ cokernel.π (Subobject.ofLE _ _
          (V.antitone_step (by omega : p ≤ p + 1))) := by
    simp only [gr, cokernel.map, cokernel.π_desc]
  choose en hen using infinity_diagonal P L A hAinf n
  choose en' hen' using infinity_diagonal Q M B hBinf n
  let eU (p : ℤ) := en p ≪≫ imageGradedIso (P.imageFiltration n (A n)) i p
  let eV (p : ℤ) := en' p ≪≫ imageGradedIso (Q.imageFiltration n (B n)) j p
  have heU (p : ℤ) : P.toPageInfinity L p (n - p) ≫ (eU p).hom =
      factorThruImageSubobject ((A n).ι p ≫ i.hom) ≫
        eqToHom (congrArg (fun S : Subobject _ ↦
          (S : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})) (hU p).symm) ≫
        cokernel.π (Subobject.ofLE _ _ (U.antitone_step (by omega : p ≤ p + 1))) := by
    dsimp [eU]
    rw [← Category.assoc, hen, Category.assoc, imageGradedIso_π,
      ← Category.assoc, imageFiltration_factor P n (A n) i p (hU p)]
    rfl
  have heV (p : ℤ) : Q.toPageInfinity M p (n - p) ≫ (eV p).hom =
      factorThruImageSubobject ((B n).ι p ≫ j.hom) ≫
        eqToHom (congrArg (fun S : Subobject _ ↦
          (S : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})) (hV p).symm) ≫
        cokernel.π (Subobject.ofLE _ _ (V.antitone_step (by omega : p ≤ p + 1))) := by
    dsimp [eV]
    rw [← Category.assoc, hen', Category.assoc, imageGradedIso_π,
      ← Category.assoc, imageFiltration_factor Q n (B n) j p (hV p)]
    rfl
  choose tInf z hz htInf using ((derivedCoupleFunctoriality P Q T).2 L M).2
  have hpage (p q : ℤ) :
      P.toPageInfinity L p q ≫ tInf p q = d p q ≫ Q.toPageInfinity M p q := by
    dsimp [toPageInfinity]
    rw [Category.assoc, ← htInf, ← Category.assoc, ← Category.assoc]
    apply congrArg (fun k : P.D p q ⟶
      (M.Z p q : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) ↦
      k ≫ cokernel.π (Subobject.ofLE _ _ (limitBoundary_le_cycle Q M p q)))
    apply (cancel_mono (M.Z p q).arrow).1
    simp only [Category.assoc, ← hz, Subobject.factorThru_arrow]
    rw [← Category.assoc, Subobject.factorThru_arrow]
    change P.initialG p q ≫ e p q = d p q ≫ Q.initialG p q
    rw [initialG_eq (truncationPsi g' f') K Q hQD hQE _hQg,
      initialG_eq (truncationPhi f g) K P hPD hPE _hPg]
    simp only [d, e, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]
    rw [← Category.assoc (CategoryTheory.TruncationExchange.g (truncationPhi f g) K p q),
      hg]
    simp only [Category.assoc]
    rfl
  have hfac (p : ℤ) :
      factorThruImageSubobject ((A n).ι p ≫ i.hom) ≫
          eqToHom (congrArg (fun S : Subobject _ ↦
            (S : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})) (hU p).symm) ≫
          lift p =
        d p (n - p) ≫ factorThruImageSubobject ((B n).ι p ≫ j.hom) ≫
          eqToHom (congrArg (fun S : Subobject _ ↦
            (S : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})) (hV p).symm) := by
    apply (cancel_mono (V.step p).arrow).1
    simp only [Category.assoc, hlift]
    rw [← Category.assoc _ (U.step p).arrow H,
      Subobject.arrow_congr _ _ (hU p).symm,
      Subobject.arrow_congr _ _ (hV p).symm,
      ← Category.assoc, imageSubobject_arrow_comp,
      imageSubobject_arrow_comp]
    exact hnat p
  have hgraded (p : ℤ) : (eU p).hom ≫ gr p = tInf p (n - p) ≫ (eV p).hom := by
    have : Epi (P.toPageInfinity L p (n - p)) := (hAconv.2.1.1 p (n - p)).1
    apply (cancel_epi (P.toPageInfinity L p (n - p))).1
    have hh := congrArg (fun k ↦ k ≫ cokernel.π
      (Subobject.ofLE _ _ (V.antitone_step (by omega : p ≤ p + 1)))) (hfac p)
    simp only [Category.assoc] at hh
    rw [← Category.assoc, heU, Category.assoc, Category.assoc, hgr, hh,
      ← heV]
    simpa only [Category.assoc] using
      congrArg (fun k ↦ k ≫ (eV p).hom) (hpage p (n - p)).symm
  refine ⟨hDP', hEP', hDQ', hEQ', L, M, A, B, hA, hB, hA0, hB0, hAconv, hBconv,
    hAfin, hBfin, hAinf, hBinf, i, j, hi, hj, U, V, rfl, rfl, hUtr, hVtr, hInv,
    d 0 n, ?_, hnat0, lift, hlift, gr, hgr, (fun p ↦ z p (n - p)),
    (fun p ↦ tInf p (n - p)), ?_, (fun p ↦ (htInf p (n - p)).symm),
    eU, eV, hU, hV, heU, heV, hgraded⟩
  · dsimp [d]
    exact (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)
  · intro p
    rw [← hz]
    dsimp [T, e]
    simpa only [← Category.assoc] using comp_eqToHom_heq
      ((L.Z p (n - p)).arrow ≫
        eqToHom (congrFun (congrFun hPE p) (n - p)) ≫ tE τ K p (n - p))
      (congrFun (congrFun hQE p) (n - p)).symm
-/

end AlgebraicGeometry.Etale
