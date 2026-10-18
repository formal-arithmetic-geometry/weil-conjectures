/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.ProEtale.Etale
public import WeilConjectures.RingTheory.ProEtale.Contraction.Covers
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import WeilConjectures.RingTheory.ProEtale.IndEtale
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.RingTheory.ProEtale.WeaklyEtale
public import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.RingTheory.Localization.Pi
public import WeilConjectures.RingTheory.ProEtale.WLocal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Finiteness.FinitePresentationLocal
import WeilConjectures.RingTheory.FactorsThroughLocalization
import Mathlib.Topology.Separation.DisjointCover
import Mathlib.RingTheory.Idempotents
import WeilConjectures.RingTheory.FilteredColimitOfFactorization
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Algebra.Pi
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.FinitePresentation
import WeilConjectures.RingTheory.ProEtale.RetractionsStrictlyHenselian

/-!
# Supporting results for `sk-thm-pe-indetale-refinement`

Supporting results for the blueprint unit `sk-thm-pe-indetale-refinement` of `sec-proetale-
coefficients`, grouped from `EtaleContraction`, `IndPrincipalZariski`, `IndEtaleStability`,
`IndPrincipalZariskiOfLocalRingIso`, `PrincipalWLocalization`, `EtaleContractionProperties`.
-/

@[expose] public section

/-! ### From `EtaleContraction` -/
section
/-!
# Successive adjoining of étale sections

Source: blueprint, sec-proper-base-change/sk-thm-properbasechange,
node def-weil-pbc-etale-contraction, order 1226
(blueprint: def-weil-pbc-etale-contraction).

We work dually in commutative rings: finite wide pullbacks are finite tensor
coproducts, and the two limits below are the two ring colimits in the source.
Taking the skeleton of the small model ensures exactly one representative per
algebra isomorphism class, rather than one factor for every object of the model.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CommRingCat.EtaleContraction

/-- Representatives of faithfully flat étale algebras, in the fixed universe `u`.
Étale ring maps are of finite presentation. Source: blueprint order 1226
(blueprint: def-weil-pbc-etale-contraction). -/
abbrev Representatives (R : CommRingCat.{u}ᵒᵖ) : Type u :=
  Skeleton (SmallModel.{u} ((CommRingCat.etale.op ⊓ CommRingCat.faithfullyFlat.op).Over ⊤ R))

/-- The finite tensor coproducts and their canonical inclusion maps, written dually.
`FiniteFamilies` includes the empty subset, whose wide pullback is the base ring.
Source: blueprint order 1226 (blueprint: def-weil-pbc-etale-contraction). -/
noncomputable def finiteDiagram (R : CommRingCat.{u}ᵒᵖ) :
    (FiniteFamilies (Representatives R))ᵒᵖ ⥤ Over R :=
  (FiniteFamilies.map (fromSkeleton (SmallModel.{u}
    ((CommRingCat.etale.op ⊓ CommRingCat.faithfullyFlat.op).Over ⊤ R)))).op ⋙
      FiniteFamilies.diag (CommRingCat.etale.op ⊓ CommRingCat.faithfullyFlat.op) R

/-- Adjoin all the representatives by the filtered colimit of finite tensor coproducts.
Its structural map is the arrow of this `Over` object. Source: blueprint order 1226
(blueprint: def-weil-pbc-etale-contraction). -/
noncomputable def step (R : CommRingCat.{u}ᵒᵖ) : Over R :=
  limit (finiteDiagram R)

/-- The successive rings, with `stage R 0 = R`. Source: blueprint order 1226
(blueprint: def-weil-pbc-etale-contraction). -/
noncomputable def stage (R : CommRingCat.{u}ᵒᵖ) : ℕ → CommRingCat.{u}ᵒᵖ
  | 0 => R
  | n + 1 => (step (stage R n)).left

/-- The sequential diagram with the structural maps from the finite-tensor colimits.
Source: blueprint order 1226 (blueprint: def-weil-pbc-etale-contraction). -/
noncomputable def sequence (R : CommRingCat.{u}ᵒᵖ) : ℕᵒᵖ ⥤ CommRingCat.{u}ᵒᵖ :=
  Functor.ofOpSequence (X := stage R) (fun n ↦ (step (stage R n)).hom)

end CommRingCat.EtaleContraction

/-- The ring `Rᵉ`, the sequential colimit of the successive tensor coproducts of one
representative of each faithfully flat étale algebra of finite presentation.
Both colimits carry their canonical maps and universal properties from `limit` in
the opposite category. Source: blueprint order 1226
(blueprint: def-weil-pbc-etale-contraction). -/
noncomputable def CommRingCat.etaleContraction (R : CommRingCat.{u}) : CommRingCat.{u} :=
  (limit (EtaleContraction.sequence (op R))).unop

/-- The canonical map of the `n`-th ring to `Rᵉ`. Source: blueprint order 1226
(blueprint: def-weil-pbc-etale-contraction). -/
noncomputable def CommRingCat.EtaleContraction.ι (R : CommRingCat.{u}) (n : ℕ) :
    (stage (op R) n).unop ⟶ R.etaleContraction :=
  (limit.π (sequence (op R)) (op n)).unop
end

/-! ### From `IndPrincipalZariski` -/
section
/-! # Ind-etale, principal ind-Zariski, and weakly etale algebras

Source: blueprint, proper base change, definition of ind-etale and ind-Zariski algebras
(blueprint: def-weil-pbc-ind-etale-algebra).

## Main definitions

- `Algebra.IsIndPrincipalZariski`: the blueprint's filtered-colimit definition with terms
  finite products of principal localizations. Upstream `Algebra.IndZariski` instead allows
  arbitrary local isomorphisms as terms, so it does not express this clause verbatim.
- Ind-etale means the existing `Algebra.IndEtale`. Its stages are `Algebra.Etale`, which
  includes finite presentation.
- The corresponding affine inverse-limit description is the existing
  `AlgebraicGeometry.proAffineEtale_Spec_iff`, with affine terms and hence affine transitions.
- Weakly etale means the existing `Algebra.WeaklyEtale`: flatness over the base and flatness
  of tensor multiplication. The equivalence with weak etaleness of the spectrum map is
  `AlgebraicGeometry.weaklyEtale_SpecMap_algebraMap_iff`.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace Algebra

/-- An `A`-algebra `B` is ind-Zariski in the blueprint's principal-localization sense if it
is a filtered colimit of finite products of algebras `A_f`. The empty finite product is
allowed. Source: blueprint, proper base change, definition of ind-etale and ind-Zariski
algebras (blueprint: def-weil-pbc-ind-etale-algebra). -/
def IsIndPrincipalZariski (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] : Prop :=
  ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I)
    (P : ColimitPresentation I (CommAlgCat.of A B)),
    ∀ i : I, ∃ (n : ℕ) (f : Fin n → A),
      Nonempty (P.diag.obj i ≃ₐ[A] ((j : Fin n) → Localization.Away (f j)))

end Algebra
end

/-! ### From `IndEtaleStability` -/
section
/-! # Stability of ind-etale and principal ind-Zariski maps

Source: blueprint, proper base change, lemma "Stability and diagonal of an ind-etale algebra"
(blueprint: lem-weil-pbc-ind-etale-stability).
-/

universe u

open CategoryTheory CategoryTheory.Limits

-- Finite principal-localization blocks and their explicit base changes.
private def blocks (A : Type u) [CommRing A] : ObjectProperty (CommAlgCat.{u} A) :=
  fun B ↦ ∃ (n : ℕ) (f : Fin n → A),
    Nonempty (B ≃ₐ[A] ((j : Fin n) → Localization.Away (f j)))
open TensorProduct in
private noncomputable def tensorBlockEquiv (A S : Type u)
    [CommRing A] [CommRing S] [Algebra A S] (n : ℕ) (f : Fin n → A) :
    S ⊗[A] ((j : Fin n) → Localization.Away (f j)) ≃ₐ[S]
      ((j : Fin n) → Localization.Away (algebraMap A S (f j))) := by
  classical
  refine (Algebra.TensorProduct.piRight A S S _).trans (AlgEquiv.piCongrRight fun j ↦ ?_)
  have : IsLocalization.Away (algebraMap A S (f j)) (S ⊗[A] Localization.Away (f j)) := by
    simpa only [Algebra.algebraMapSubmonoid, Submonoid.map_powers] using
      (inferInstance : IsLocalization
        (Algebra.algebraMapSubmonoid S (Submonoid.powers (f j)))
        (S ⊗[A] Localization.Away (f j)))
  exact IsLocalization.algEquiv (Submonoid.powers (algebraMap A S (f j))) _ _
open TensorProduct in
private theorem block_tensor (A S : Type u) [CommRing A] [CommRing S] [Algebra A S]
    (B : CommAlgCat.{u} A) (hB : blocks A B) :
    blocks S (CommAlgCat.of S (S ⊗[A] B)) := by
  obtain ⟨n, f, ⟨e⟩⟩ := hB
  exact ⟨n, fun j ↦ algebraMap A S (f j),
    ⟨(Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) e).trans
      (tensorBlockEquiv A S n f)⟩⟩
private noncomputable def bc (A S : Type u) [CommRing A] [CommRing S] [Algebra A S] :
    CommAlgCat.{u} A ⥤ CommAlgCat.{u} S :=
  (commAlgCatEquivUnder (.of A)).functor ⋙
    Under.pushout (CommRingCat.ofHom (algebraMap A S)) ⋙
      (commAlgCatEquivUnder (.of S)).inverse
open TensorProduct in
private noncomputable def bcEquiv (A S : Type u) [CommRing A] [CommRing S] [Algebra A S]
    (B : CommAlgCat.{u} A) :
    (bc A S).obj B ≃ₐ[S] S ⊗[A] B := by
  let e := (CommRingCat.isPushout_tensorProduct A B S).isoPushout.symm
  exact
    { __ := e.commRingCatIsoToRingEquiv.trans (Algebra.TensorProduct.comm A B S).toRingEquiv
      commutes' := by
        intro s
        change (Algebra.TensorProduct.comm A B S)
          (e.hom.hom ((pushout.inr (CommRingCat.ofHom (algebraMap A B))
            (CommRingCat.ofHom (algebraMap A S))).hom s)) = _
        have he := (CommRingCat.isPushout_tensorProduct A B S).inr_isoPushout_inv
        have hes := congrArg (fun g ↦ g.hom s) he
        change e.hom.hom _ = 1 ⊗ₜ[A] s at hes
        exact (congrArg (Algebra.TensorProduct.comm A B S) hes).trans (by rfl) }

private theorem bc_preserves (A S : Type u) [CommRing A] [CommRing S] [Algebra A S]
    {I : Type u} [SmallCategory I] : PreservesColimitsOfShape I (bc A S) := by
  unfold bc
  infer_instance
private theorem blocks_of_equiv (A : Type u) [CommRing A] {B C : CommAlgCat.{u} A}
    (e : B ≃ₐ[A] C) (h : blocks A C) : blocks A B := by
  obtain ⟨n, f, ⟨e'⟩⟩ := h
  exact ⟨n, f, ⟨e.trans e'⟩⟩
private theorem principal_of_equiv (A : Type u) [CommRing A]
    {B C : Type u} [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (e : B ≃ₐ[A] C) (h : Algebra.IsIndPrincipalZariski A B) :
    Algebra.IsIndPrincipalZariski A C := by
  change (blocks A).ind (CommAlgCat.of A C)
  exact (blocks A).ind.prop_of_iso (CommAlgCat.isoMk e) h
open TensorProduct in
private theorem principal_tensor (A S B : Type u) [CommRing A] [CommRing S] [CommRing B]
    [Algebra A S] [Algebra A B] (h : Algebra.IsIndPrincipalZariski A B) :
    Algebra.IsIndPrincipalZariski S (S ⊗[A] B) := by
  obtain ⟨I, _, _, P, hP⟩ := h
  have := bc_preserves A S (I := I)
  have h' : Algebra.IsIndPrincipalZariski S ((bc A S).obj (CommAlgCat.of A B)) := by
    refine ⟨I, ‹_›, ‹_›, P.map (bc A S), fun i ↦ ?_⟩
    change blocks S ((bc A S).obj (P.diag.obj i))
    exact blocks_of_equiv S (C := CommAlgCat.of S (S ⊗[A] P.diag.obj i))
      (bcEquiv A S (P.diag.obj i))
      (block_tensor A S (P.diag.obj i) (hP i))
  exact principal_of_equiv S (bcEquiv A S (CommAlgCat.of A B)) h'

private theorem principal_baseChange : RingHom.IsStableUnderBaseChange
    (fun {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) ↦
      @Algebra.IsIndPrincipalZariski A B _ _ f.toAlgebra) := by
  intro R S R' S' _ _ _ _ _ _ _ _ _ _ _ hpush h
  rw [toAlgebra_algebraMap] at h ⊢
  have : Algebra.IsPushout R R' S S' := hpush.symm
  exact principal_of_equiv R' (Algebra.IsPushout.equiv R R' S S')
    (principal_tensor R R' S h)

-- Relate the algebra presentation to the categorical ind-property.
private local instance blocks_closedIso (A : Type u) [CommRing A] :
    (blocks A).IsClosedUnderIsomorphisms where
  of_iso e h := blocks_of_equiv A (CommAlgCat.algEquivOfIso e).symm h
private def blockMaps : MorphismProperty CommRingCat.{u} :=
  fun A B f ↦ let := f.hom.toAlgebra; blocks A (CommAlgCat.of A B)
private theorem principal_iff_ind {A B : CommRingCat.{u}} (f : A ⟶ B) :
    @Algebra.IsIndPrincipalZariski A B _ _ f.hom.toAlgebra ↔ blockMaps.ind.{u} f := by
  rw [MorphismProperty.ind_iff_ind_underMk]
  change (blocks A).ind ((commAlgCatEquivUnder A).inverse.obj (Under.mk f)) ↔ _
  change (blocks A).ind.inverseImage (commAlgCatEquivUnder A).inverse (Under.mk f) ↔ _
  rw [← ObjectProperty.ind_inverseImage_eq_of_isEquivalence
    (blocks A) (commAlgCatEquivUnder A).inverse]
  rfl
private theorem blockMaps_fp :
    blockMaps ≤ MorphismProperty.isFinitelyPresentable.{u} CommRingCat.{u} := by
  intro A B g hg
  apply CommRingCat.isFinitelyPresentable_under
  obtain ⟨n, f, ⟨e⟩⟩ := hg
  let := g.hom.toAlgebra
  have : Algebra.Etale A ((j : Fin n) → Localization.Away (f j)) := inferInstance
  have : Algebra.Etale A B := Algebra.Etale.of_equiv e.symm
  exact (RingHom.etale_algebraMap.mpr (inferInstance : Algebra.Etale A B)).2
private theorem principal_iff_ind_principal {A B : CommRingCat.{u}} (f : A ⟶ B) :
    @Algebra.IsIndPrincipalZariski A B _ _ f.hom.toAlgebra ↔
      (RingHom.toMorphismProperty
        (fun {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) ↦
          @Algebra.IsIndPrincipalZariski A B _ _ f.toAlgebra)).ind.{u} f := by
  rw [principal_iff_ind]
  have heq : RingHom.toMorphismProperty
      (fun {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) ↦
        @Algebra.IsIndPrincipalZariski A B _ _ f.toAlgebra) = blockMaps.ind.{u} := by
    ext A B g
    exact principal_iff_ind g
  rw [heq]
  exact (congrArg (fun P : MorphismProperty CommRingCat.{u} ↦ P f)
    (MorphismProperty.ind_ind blockMaps_fp)).symm.to_iff

private local instance blockMaps_baseChange : blockMaps.{u}.IsStableUnderCobaseChange := by
  change (RingHom.toMorphismProperty
    (fun {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) ↦
      let := f.toAlgebra; blocks A (CommAlgCat.of A B))).IsStableUnderCobaseChange
  apply RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.mpr
  intro R S R' S' _ _ _ _ _ _ _ _ _ _ _ hpush h
  rw [toAlgebra_algebraMap] at h ⊢
  have : Algebra.IsPushout R R' S S' := hpush.symm
  exact blocks_of_equiv R' (Algebra.IsPushout.equiv R R' S S').symm
    (block_tensor R R' (CommAlgCat.of R S) h)

-- Localization and finite products preserve the blocks, including empty products.
private theorem block_away (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)
    (hB : blocks A B) (b : B) : blocks A (CommAlgCat.of A (Localization.Away b)) := by
  classical
  obtain ⟨n, f, ⟨e⟩⟩ := hB
  let R (i : Fin n) := Localization.Away (f i)
  let g : (i : Fin n) → R i := e b
  let T (i : Fin n) := Localization.Away (g i)
  have (i : Fin n) : IsLocalization ((Submonoid.powers g).map (Pi.evalRingHom R i))
      (T i) := by
    simp only [Submonoid.map_powers]
    change IsLocalization.Away (g i) (T i)
    infer_instance
  have : IsLocalization.Away g ((i : Fin n) → T i) :=
    (IsLocalization.iff_map_piEvalRingHom R ((i : Fin n) → T i)
      (Submonoid.powers g)).mpr inferInstance
  let e₁ : Localization.Away b ≃ₐ[A] Localization.Away g :=
    IsLocalization.algEquivOfAlgEquiv (M := Submonoid.powers b)
      (T := Submonoid.powers g) _ _ e (by rw [Submonoid.map_powers])
  let e₂ : Localization.Away g ≃ₐ[A] ((i : Fin n) → T i) :=
    (IsLocalization.algEquiv (Submonoid.powers g) _ _).restrictScalars A
  let a (i : Fin n) : A := (IsLocalization.Away.sec (f i) (g i)).1
  have (i : Fin n) : IsLocalization.Away (f i * a i) (T i) :=
    IsLocalization.Away.mul_of_associated (f i) (a i) (g i)
      (IsLocalization.Away.associated_sec_fst (f i) (g i))
  refine ⟨n, fun i ↦ f i * a i, ⟨e₁.trans (e₂.trans ?_)⟩⟩
  exact AlgEquiv.piCongrRight fun i ↦
    IsLocalization.algEquiv (Submonoid.powers (f i * a i)) _ _
private theorem block_pi (A : Type u) [CommRing A] {m : ℕ}
    (B : Fin m → CommAlgCat.{u} A) (hB : ∀ j, blocks A (B j)) :
    blocks A (CommAlgCat.of A ((j : Fin m) → B j)) := by
  classical
  choose n f e using hB
  let J := (j : Fin m) × Fin (n j)
  let fs : J → A := fun p ↦ f p.1 p.2
  let e₁ : ((j : Fin m) → B j) ≃ₐ[A]
      ((p : J) → Localization.Away (fs p)) :=
    { toFun x p := (e p.1).some (x p.1) p.2
      invFun x j := (e j).some.symm (fun k ↦ x ⟨j, k⟩)
      left_inv x := by ext j; exact (e j).some.symm_apply_apply (x j)
      right_inv x := by ext p; exact congrFun ((e p.1).some.apply_symm_apply _) p.2
      map_mul' x y := by ext p; simp
      map_add' x y := by ext p; simp
      commutes' a := by
        ext p
        simpa only [fs, Pi.algebraMap_apply] using congrFun ((e p.1).some.commutes a) p.2 }
  let k := Fintype.card J
  let eqv : Fin k ≃ J := (Fintype.equivFin J).symm
  refine ⟨k, fs ∘ eqv, ⟨e₁.trans ?_⟩⟩
  exact (AlgEquiv.piCongrLeft A (fun p : J ↦ Localization.Away (fs p)) eqv).symm
private theorem block_comp (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (hB : blocks A (CommAlgCat.of A B)) (hC : blocks B (CommAlgCat.of B C)) :
    blocks A (CommAlgCat.of A C) := by
  obtain ⟨n, f, ⟨e⟩⟩ := hC
  apply blocks_of_equiv A
    (C := CommAlgCat.of A ((j : Fin n) → Localization.Away (f j))) (e.restrictScalars A)
  apply block_pi A (fun j ↦ CommAlgCat.of A (Localization.Away (f j)))
  intro j
  exact block_away A (CommAlgCat.of A B) hB (f j)

private local instance blockMaps_comp : blockMaps.{u}.IsStableUnderComposition where
  comp_mem {A B C} f g hf hg := by
    let := f.hom.toAlgebra
    let := g.hom.toAlgebra
    let := (g.hom.comp f.hom).toAlgebra
    have : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' rfl
    exact block_comp A B C hf hg
-- Descend the finite list of denominators to one filtered stage.
private theorem finite_reps {I : Type u} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CommRingCat.{u}) (c : Cocone D) (hc : IsColimit c)
    (n : ℕ) (x : Fin n → c.pt) :
    ∃ (i : I) (y : Fin n → D.obj i), ∀ j, (c.ι.app i).hom (y j) = x j := by
  classical
  choose i y hy using fun j ↦ Concrete.isColimit_exists_rep D hc (x j)
  let co := IsFiltered.cocone (Discrete.functor i)
  refine ⟨co.pt, fun j ↦ (D.map (co.ι.app ⟨j⟩)).hom (y j), fun j ↦ ?_⟩
  have hw := congrArg (fun k ↦ k.hom (y j)) (c.w (co.ι.app ⟨j⟩))
  exact hw.trans (hy j)
open TensorProduct in
private local instance blockMaps_spreads : MorphismProperty.PreIndSpreads.{u} blockMaps.{u} where
  exists_isPushout {I} _ _ {D} {c} hc {T} f hf := by
    let : Algebra c.pt T := f.hom.toAlgebra
    obtain ⟨n, g, ⟨e⟩⟩ := hf
    obtain ⟨i, gi, hgi⟩ := finite_reps D c hc n g
    let : Algebra (D.obj i) c.pt := (c.ι.app i).hom.toAlgebra
    let Ti := (j : Fin n) → Localization.Away (gi j)
    let e₀ : c.pt ⊗[D.obj i] Ti ≃ₐ[c.pt]
        ((j : Fin n) → Localization.Away (g j)) := by
      refine (tensorBlockEquiv (D.obj i) c.pt n gi).trans
        (AlgEquiv.piCongrRight fun j ↦ ?_)
      have hh : algebraMap (D.obj i) c.pt (gi j) = g j := hgi j
      rw [hh]
    let ebc : c.pt ⊗[D.obj i] Ti ≃ₐ[c.pt] T := e₀.trans e.symm
    let fi : D.obj i ⟶ CommRingCat.of Ti := CommRingCat.ofHom (algebraMap (D.obj i) Ti)
    let v : CommRingCat.of Ti ⟶ T := CommRingCat.ofHom
      (ebc.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)
    refine ⟨i, CommRingCat.of Ti, fi, v, ?_, ?_⟩
    · refine (CommRingCat.isPushout_tensorProduct (D.obj i) c.pt Ti).of_iso
        (Iso.refl _) (Iso.refl _) (Iso.refl _) ebc.toRingEquiv.toCommRingCatIso
        ?_ ?_ ?_ ?_
      · rfl
      · rfl
      · ext x
        exact ebc.commutes x
      · rfl
    · change @blocks (D.obj i) _
        (@CommAlgCat.of (D.obj i) _ Ti _ (algebraMap (D.obj i) Ti).toAlgebra)
      rw [toAlgebra_algebraMap]
      exact ⟨n, gi, ⟨AlgEquiv.refl⟩⟩

private theorem principal_comp : RingHom.StableUnderComposition
    (fun {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) ↦
      @Algebra.IsIndPrincipalZariski A B _ _ f.toAlgebra) := by
  have : blockMaps.ind.{u}.IsStableUnderComposition :=
    .ind_of_le_isFinitelyPresentable blockMaps_fp
  intro A B C _ _ _ f g hf hg
  exact (principal_iff_ind (CommRingCat.ofHom (g.comp f))).mpr
    (blockMaps.ind.comp_mem (CommRingCat.ofHom f) (CommRingCat.ofHom g)
      ((principal_iff_ind (CommRingCat.ofHom f)).mp hf)
      ((principal_iff_ind (CommRingCat.ofHom g)).mp hg))

-- Push out to a fixed source, then construct the colimit universal property.
private theorem colimit_mem_ind {C : Type (u + 1)} [Category.{u} C] [HasPushouts C]
    (P : MorphismProperty C) [P.IsStableUnderCobaseChange]
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (F G : I ⥤ C) (a : Cocone F) (b : Cocone G)
    (ha : IsColimit a) (hb : IsColimit b) (η : F ⟶ G)
    (hη : ∀ i, P (η.app i)) (f : a.pt ⟶ b.pt)
    (hf : ∀ i, a.ι.app i ≫ f = η.app i ≫ b.ι.app i) : P.ind.{u} f := by
  let E : I ⥤ C :=
    { obj i := pushout (a.ι.app i) (η.app i)
      map {i j} k := pushout.desc (pushout.inl _ _)
        (G.map k ≫ pushout.inr _ _) (by
          rw [← Category.assoc, ← η.naturality k]
          simp only [Category.assoc, ← pushout.condition]
          rw [← Category.assoc, a.w k])
      map_id i := by apply pushout.hom_ext <;> simp
      map_comp {i j k} x y := by apply pushout.hom_ext <;> simp }
  have hinl {i j : I} (k : i ⟶ j) :
      pushout.inl (a.ι.app i) (η.app i) ≫ E.map k =
        pushout.inl (a.ι.app j) (η.app j) := by simp [E]
  have hinr {i j : I} (k : i ⟶ j) :
      pushout.inr (a.ι.app i) (η.app i) ≫ E.map k =
        G.map k ≫ pushout.inr (a.ι.app j) (η.app j) := by simp [E]
  have hinlw : ∀ (w : Cocone E) {i j : I} (k : i ⟶ j),
      pushout.inl (a.ι.app i) (η.app i) ≫ w.ι.app i =
        pushout.inl (a.ι.app j) (η.app j) ≫ w.ι.app j := by
    intro w i j k
    rw [← w.w k, ← Category.assoc, hinl k]
  have hleft (w : Cocone E) (i j : I) :
      pushout.inl (a.ι.app i) (η.app i) ≫ w.ι.app i =
        pushout.inl (a.ι.app j) (η.app j) ≫ w.ι.app j :=
    (hinlw w (IsFiltered.leftToMax i j)).trans
      (hinlw w (IsFiltered.rightToMax i j)).symm
  let rightCocone (w : Cocone E) : Cocone G :=
    { pt := w.pt
      ι :=
        { app i := pushout.inr _ _ ≫ w.ι.app i
          naturality {i j} k := by
            dsimp
            rw [Category.comp_id, ← Category.assoc, ← hinr k, Category.assoc, w.w k] } }
  let t : (Functor.const I).obj a.pt ⟶ E :=
    { app i := pushout.inl _ _
      naturality {i j} k := by dsimp; rw [Category.id_comp, hinl k] }
  let s : E ⟶ (Functor.const I).obj b.pt :=
    { app i := pushout.desc f (b.ι.app i) (hf i)
      naturality {i j} k := by apply pushout.hom_ext <;> simp [E] }
  refine ⟨I, ‹_›, ‹_›, E, t, s, ?_, fun i ↦ ⟨P.pushout_inl _ _ (hη i), by simp [t, s]⟩⟩
  refine
    { desc := fun w ↦ hb.desc (rightCocone w)
      fac := fun w i ↦ ?_
      uniq := fun w m hm ↦ ?_ }
  · dsimp only
    apply pushout.hom_ext
    · simp only [s, pushout.inl_desc_assoc]
      change f ≫ hb.desc (rightCocone w) = pushout.inl _ _ ≫ w.ι.app i
      apply ha.hom_ext
      intro j
      rw [← Category.assoc, hf j, Category.assoc, hb.fac]
      dsimp [rightCocone]
      rw [hleft w i j, ← pushout.condition_assoc]
    · simp only [s, pushout.inr_desc_assoc]
      change b.ι.app i ≫ hb.desc (rightCocone w) = _
      exact hb.fac _ i
  · apply hb.hom_ext
    intro i
    rw [hb.fac]
    have hi := congrArg (fun g ↦ pushout.inr (a.ι.app i) (η.app i) ≫ g) (hm i)
    simpa [s, rightCocone] using hi
private theorem indEtale_colimit {I : Type u} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ Arrow CommRingCat.{u}) (c : Cocone D) (hc : IsColimit c)
    (h : ∀ i, (D.obj i).hom.hom.IndEtale) : c.pt.hom.hom.IndEtale := by
  have : (RingHom.toMorphismProperty (@RingHom.IndEtale.{u})).IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.mpr
      RingHom.IndEtale.isStableUnderBaseChange
  have h' := colimit_mem_ind (RingHom.toMorphismProperty (@RingHom.IndEtale.{u}))
    (D ⋙ Arrow.leftFunc) (D ⋙ Arrow.rightFunc)
    (Arrow.leftFunc.mapCocone c) (Arrow.rightFunc.mapCocone c)
    (isColimitOfPreserves Arrow.leftFunc hc) (isColimitOfPreserves Arrow.rightFunc hc)
    { app i := (D.obj i).hom
      naturality i j f := (D.map f).w }
    h c.pt.hom (fun i ↦ (c.ι.app i).w)
  exact (RingHom.IndEtale.iff_ind_indEtale c.pt.hom.hom).mpr h'

private theorem principal_colimit {I : Type u} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ Arrow CommRingCat.{u}) (c : Cocone D) (hc : IsColimit c)
    (h : ∀ i, @Algebra.IsIndPrincipalZariski (D.obj i).left (D.obj i).right
      _ _ (D.obj i).hom.hom.toAlgebra) :
    @Algebra.IsIndPrincipalZariski c.pt.left c.pt.right _ _ c.pt.hom.hom.toAlgebra := by
  have : (RingHom.toMorphismProperty
      (fun {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) ↦
        @Algebra.IsIndPrincipalZariski A B _ _ f.toAlgebra)).IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.mpr principal_baseChange
  have h' := colimit_mem_ind (RingHom.toMorphismProperty
      (fun {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) ↦
        @Algebra.IsIndPrincipalZariski A B _ _ f.toAlgebra))
    (D ⋙ Arrow.leftFunc) (D ⋙ Arrow.rightFunc)
    (Arrow.leftFunc.mapCocone c) (Arrow.rightFunc.mapCocone c)
    (isColimitOfPreserves Arrow.leftFunc hc) (isColimitOfPreserves Arrow.rightFunc hc)
    { app i := (D.obj i).hom
      naturality i j f := (D.map f).w }
    h c.pt.hom (fun i ↦ (c.ι.app i).w)
  exact (principal_iff_ind_principal c.pt.hom).mpr h'

-- The remaining clauses use existing ind-etale and weakly etale APIs.
private theorem weaklyEtale_of_bijective {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Bijective f) : f.WeaklyEtale := by
  let := f.toAlgebra
  have : Algebra.Etale R S := (RingHom.Etale.of_bijective hf).toAlgebra
  exact inferInstanceAs (Algebra.WeaklyEtale R S)
private theorem weaklyEtale_baseChange :
    RingHom.IsStableUnderBaseChange (@RingHom.WeaklyEtale.{u,u}) := by
  apply RingHom.IsStableUnderBaseChange.mk
  · apply RingHom.StableUnderComposition.respectsIso
    · intro R S T _ _ _ f g hf hg
      exact hf.comp hg
    · intro R S _ _ e
      exact weaklyEtale_of_bijective _ e.bijective
  · intro R S T _ _ _ _ _ h
    rw [RingHom.weaklyEtale_algebraMap_iff] at h ⊢
    have := h
    infer_instance
private theorem relative_indEtale
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (hB : Algebra.IndEtale A B)
    (hC : Algebra.IndEtale A C) (f : B →ₐ[A] C) : f.toRingHom.IndEtale := by
  apply RingHom.IndEtale.of_comp ((RingHom.IndEtale.algebraMap_iff A B).mpr hB)
  have heq : f.toRingHom.comp (algebraMap A B) = algebraMap A C :=
    RingHom.ext f.commutes
  rw [heq]
  exact (RingHom.IndEtale.algebraMap_iff A C).mpr hC

namespace RingHom

/-- Stability under base change, composition and filtered colimits of ind-etale and principal
ind-Zariski maps; weak etaleness of ind-etale maps; the relative ind-etale assertion; and
composition and base-change stability of weakly etale maps.
Source: blueprint, proper base change, lemma "Stability and diagonal of an ind-etale algebra"
(blueprint: lem-weil-pbc-ind-etale-stability).

Filtered colimits are expressed in the arrow category, allowing varying source rings.
The principal ind-Zariski condition is evaluated using the algebra structure of each ring map.

Proof:

The source library already proves ind-etale base change and composition, weak etaleness of
ind-etale maps, relative ind-etaleness by cancellation, and weakly etale composition. Weakly
etale base change follows from the tensor-product instance and invariance under ring isomorphism.

For principal ind-Zariski maps, use finite products of principal localizations as building
blocks. Tensor product preserves these blocks: it distributes over finite products and changes
localization at f into localization at the image of f. The base-change functor on algebra
categories preserves colimits, giving base-change stability of their filtered colimits.

The blocks are finitely presented because they are etale. They compose: localizing a product
amounts to localizing each factor, and if g = a/f^N in A_f then (A_f)_g is A_(fa). Flatten the
resulting finite product. They also spread over filtered colimits: finitely many denominators
have representatives at a common stage. Apply the source library's composition theorem for
ind-properties of finitely presented morphisms that spread.

For filtered colimits with varying bases, push each stage arrow out to the colimit source.
These pushouts form a filtered diagram with that fixed source, whose target colimit is the
original target colimit. Construct its universal property using the two original colimit
universal properties and pushout descent; filteredness identifies all the source injections.
Cobase-change stability makes its stages satisfy the original property, so the colimit arrow
satisfies its ind-property. Finally flatten twice-ind presentations, using
`RingHom.IndEtale.iff_ind_indEtale` and `MorphismProperty.ind_ind`, respectively.
-/
theorem indEtale_principalZariski_stability :
    RingHom.IsStableUnderBaseChange (@RingHom.IndEtale.{u}) ∧
    RingHom.IsStableUnderBaseChange
      (fun {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) ↦
        @Algebra.IsIndPrincipalZariski A B _ _ f.toAlgebra) ∧
    RingHom.StableUnderComposition (@RingHom.IndEtale.{u}) ∧
    RingHom.StableUnderComposition
      (fun {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) ↦
        @Algebra.IsIndPrincipalZariski A B _ _ f.toAlgebra) ∧
    (∀ (I : Type u) [SmallCategory I] [IsFiltered I]
      (D : I ⥤ Arrow CommRingCat.{u}) (c : Cocone D), IsColimit c →
      (∀ i : I, (D.obj i).hom.hom.IndEtale) → c.pt.hom.hom.IndEtale) ∧
    (∀ (I : Type u) [SmallCategory I] [IsFiltered I]
      (D : I ⥤ Arrow CommRingCat.{u}) (c : Cocone D), IsColimit c →
      (∀ i : I, @Algebra.IsIndPrincipalZariski (D.obj i).left (D.obj i).right
        _ _ (D.obj i).hom.hom.toAlgebra) →
      @Algebra.IsIndPrincipalZariski c.pt.left c.pt.right _ _ c.pt.hom.hom.toAlgebra) ∧
    (∀ (A B : Type u) [CommRing A] [CommRing B] (f : A →+* B),
      f.IndEtale → f.WeaklyEtale) ∧
    (∀ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra A C], Algebra.IndEtale A B → Algebra.IndEtale A C →
      ∀ f : B →ₐ[A] C, f.toRingHom.IndEtale) ∧
    RingHom.StableUnderComposition (@RingHom.WeaklyEtale.{u, u}) ∧
    RingHom.IsStableUnderBaseChange (@RingHom.WeaklyEtale.{u, u}) := by
  refine ⟨IndEtale.isStableUnderBaseChange, principal_baseChange, ?_, principal_comp,
    ?_, ?_, ?_, ?_, ?_, weaklyEtale_baseChange⟩
  · intro A B C _ _ _ f g hf hg
    exact hg.comp hf
  · intro I _ _ D c hc h
    exact indEtale_colimit D c hc h
  · intro I _ _ D c hc h
    exact principal_colimit D c hc h
  · intro A B _ _ f hf
    exact hf.weaklyEtale
  · intro A B C _ _ _ _ _ hB hC f
    exact relative_indEtale A B C hB hC f
  · intro A B C _ _ _ f g hf hg
    exact hf.comp hg

end RingHom
end

/-! ### From `IndPrincipalZariskiOfLocalRingIso` -/
section
/-! # Local-ring identifications with w-local target

Source: blueprint, proper base change, `sk-thm-properbasechange`, lemma
`lem-weil-pbc-local-rings-ind-zariski`
(blueprint: lem-weil-pbc-local-rings-ind-zariski).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace Algebra

open scoped BigOperators

/-- Descend the inverse stalk map to a principal neighbourhood, then clear the finitely
many generator equalities. Source: blueprint lem-weil-pbc-local-rings-ind-zariski,
proof paragraphs 1--2 (blueprint: lem-weil-pbc-local-rings-ind-zariski). -/
private theorem local_factorization
    (A B P : Type u) [CommRing A] [CommRing B] [CommRing P]
    [Algebra A B] [Algebra A P] [FinitePresentation A P]
    (q : Ideal B) [q.IsPrime]
    (hq : Function.Bijective
      (Localization.localRingHom (q.comap (algebraMap A B)) q (algebraMap A B) rfl))
    (α : P →ₐ[A] B) :
    ∃ (f : A) (g : B), g ∉ q ∧
      ∃ (β : P →ₐ[A] Localization.Away f)
        (γ : Localization.Away f →ₐ[A] Localization.Away g),
        γ.comp β = (IsScalarTower.toAlgHom A B (Localization.Away g)).comp α := by
  classical
  let p := q.comap (algebraMap A B)
  let l : Localization.AtPrime p →ₐ[A] Localization.AtPrime q :=
    { Localization.localRingHom p q (algebraMap A B) rfl with
      commutes' := fun a ↦ by
        change Localization.localRingHom p q (algebraMap A B) rfl
          (algebraMap A (Localization.AtPrime p) a) = _
        rw [Localization.localRingHom_to_map]
        exact (IsScalarTower.algebraMap_apply A B (Localization.AtPrime q) a).symm }
  let e : Localization.AtPrime p ≃ₐ[A] Localization.AtPrime q := AlgEquiv.ofBijective l hq
  let αq := (IsScalarTower.toAlgHom A B (Localization.AtPrime q)).comp α
  obtain ⟨f, β, k, hk⟩ := factors_through_principal_localization A P A p.primeCompl
    (e.symm.toAlgHom.comp αq)
  have hf : algebraMap A B (f : A) ∈ q.primeCompl := f.property
  let g₀ := algebraMap A B (f : A)
  let γ₀ : Localization.Away (f : A) →ₐ[A] Localization.Away g₀ :=
    IsLocalization.Away.liftAlgHom (f : A)
      (f := Algebra.ofId A (Localization.Away g₀))
      (IsLocalization.Away.algebraMap_isUnit g₀)
  let kq : Localization.Away g₀ →ₐ[A] Localization.AtPrime q :=
    IsLocalization.Away.liftAlgHom g₀
      (f := IsScalarTower.toAlgHom A B (Localization.AtPrime q))
      (IsLocalization.map_units _ ⟨g₀, hf⟩)
  have hkq (b : B) : kq (algebraMap B _ b) = algebraMap B _ b := by
    simp only [kq, IsLocalization.Away.coe_liftAlgHom, IsLocalization.Away.lift_eq]
    rfl
  have hmaps : kq.comp γ₀ = e.toAlgHom.comp k := by
    apply IsLocalization.algHom_ext (Submonoid.powers (f : A))
    ext
  have heq : kq.comp (γ₀.comp β) = αq := by
    rw [← AlgHom.comp_assoc, hmaps, AlgHom.comp_assoc, hk]
    ext x
    exact e.apply_symm_apply _
  obtain ⟨n, t, ht, _⟩ := FinitePresentation.out (R := A) (A := P)
  have kill (i : Fin n) : ∃ b : q.primeCompl,
      algebraMap B (Localization.Away g₀) b *
        ((γ₀.comp β) (t (MvPolynomial.X i)) -
          algebraMap B _ (α (t (MvPolynomial.X i)))) = 0 := by
    let x := (γ₀.comp β) (t (MvPolynomial.X i)) -
      algebraMap B (Localization.Away g₀) (α (t (MvPolynomial.X i)))
    obtain ⟨m, c, hc⟩ := IsLocalization.Away.surj g₀ x
    have hx : kq x = 0 := by
      simp only [x, map_sub, hkq]
      exact sub_eq_zero.mpr (AlgHom.congr_fun heq _)
    have hczero : algebraMap B (Localization.AtPrime q) c = 0 := by
      have h := congrArg kq hc
      simpa only [map_mul, map_pow, hkq, hx, zero_mul] using h.symm
    obtain ⟨b, hb⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl _ c).mp hczero
    refine ⟨b, ?_⟩
    apply ((IsLocalization.Away.algebraMap_isUnit g₀).pow m).mul_right_cancel
    change (algebraMap B _ b * x) * algebraMap B _ g₀ ^ m = _
    rw [mul_assoc, hc, ← map_mul, hb, map_zero, zero_mul]
  choose b hb using kill
  let g : q.primeCompl := ⟨g₀, hf⟩ * ∏ i, b i
  let j : Localization.Away g₀ →ₐ[A] Localization.Away (g : B) :=
    IsLocalization.Away.liftAlgHom g₀
      (f := Algebra.algHom A B (Localization.Away (g : B)))
      (IsLocalization.Away.isUnit_of_dvd (g : B)
        (show g₀ ∣ (g : B) from ⟨_, rfl⟩))
  have hj (c : B) : j (algebraMap B _ c) = algebraMap B _ c := by
    simp only [j, IsLocalization.Away.coe_liftAlgHom, IsLocalization.Away.lift_eq]
    rfl
  refine ⟨f, g, g.property, β, j.comp γ₀, ?_⟩
  have hgen : (j.comp (γ₀.comp β)).comp t =
      ((IsScalarTower.toAlgHom A B (Localization.Away (g : B))).comp α).comp t := by
    apply MvPolynomial.algHom_ext
    intro i
    have hdvd : (b i : B) ∣ (g : B) := by
      exact (Finset.dvd_prod_of_mem (fun i ↦ (b i : B)) (Finset.mem_univ i)).trans
        (by
          change (∏ i, (b i : B)) ∣ g₀ * ↑(∏ i, b i)
          simpa only [Submonoid.coe_finsetProd] using dvd_mul_left (∏ i, (b i : B)) g₀)
    have h := congrArg j (hb i)
    simp only [map_mul, map_sub, hj, map_zero] at h
    exact sub_eq_zero.mp
      ((IsLocalization.Away.isUnit_of_dvd (g : B) hdvd).mul_left_cancel
        (h.trans (mul_zero _).symm))
  apply AlgHom.ext
  intro x
  obtain ⟨y, rfl⟩ := ht x
  exact AlgHom.congr_fun hgen y

/-- Pull a disjoint clopen refinement on the closed points back along the continuous
closed-specialization map. Source: blueprint lem-weil-pbc-local-rings-ind-zariski,
proof paragraph 2 (blueprint: lem-weil-pbc-local-rings-ind-zariski). -/
private theorem clopen_refinement
    (B : Type u) [CommRing B] [IsWLocalRing B]
    (ι : Type u) (O : ι → TopologicalSpace.Opens (PrimeSpectrum B))
    (hO : ∀ c : closedPoints (PrimeSpectrum B), ∃ i, (c : PrimeSpectrum B) ∈ O i) :
    ∃ (n : ℕ) (Q : Fin n → Set (PrimeSpectrum B)) (r : Fin n → ι),
      (∀ i, IsClopen (Q i)) ∧ Pairwise (fun i j ↦ Disjoint (Q i) (Q j)) ∧
      (⋃ i, Q i) = Set.univ ∧ ∀ i, Q i ⊆ O (r i) := by
  classical
  let H := WLocalSpace.closedPointsHomeomorph (X := PrimeSpectrum B)
  let π : PrimeSpectrum B → closedPoints (PrimeSpectrum B) :=
    fun x ↦ H.symm (ConnectedComponents.mk x)
  have hπ : Continuous π := H.symm.continuous.comp ConnectedComponents.continuous_coe
  have : T2Space (closedPoints (PrimeSpectrum B)) := H.symm.t2Space
  have : TotallyDisconnectedSpace (closedPoints (PrimeSpectrum B)) :=
    H.symm.totallyDisconnectedSpace
  let U : ι → TopologicalSpace.Opens (closedPoints (PrimeSpectrum B)) :=
    fun i ↦ (O i).comap ⟨Subtype.val, continuous_subtype_val⟩
  have hU : TopologicalSpace.IsOpenCover U := by
    apply TopologicalSpace.IsOpenCover.mk
    apply TopologicalSpace.Opens.ext
    rw [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top]
    exact Set.eq_univ_of_forall fun c ↦ Set.mem_iUnion.mpr (hO c)
  obtain ⟨n, V, hV, hcover, hdisj⟩ :=
    hU.exists_finite_nonempty_disjoint_clopen_cover
  choose r hr using fun i ↦ (hV i).2
  let Q := fun i ↦ π ⁻¹' (V i : Set (closedPoints (PrimeSpectrum B)))
  have hQ (i : Fin n) : IsClopen (Q i) := (V i).isClopen.preimage hπ
  refine ⟨n, Q, r, hQ, ?_, ?_, fun i x hx ↦ ?_⟩
  · intro i j hij
    exact (TopologicalSpace.Clopens.coe_disjoint.mpr (hdisj hij)).preimage π
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover (Set.mem_univ (π x)))
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  · obtain ⟨c, hc, hxc⟩ := exists_isClosed_specializes x
    have hπx : π x = ⟨c, mem_closedPoints_iff.mpr hc⟩ := by
      apply H.injective
      change H (H.symm (ConnectedComponents.mk x)) = ConnectedComponents.mk c
      rw [H.apply_symm_apply]
      exact hxc.connectedComponents_mk_eq
    have hcV : (⟨c, mem_closedPoints_iff.mpr hc⟩ : closedPoints (PrimeSpectrum B)) ∈ V i := by
      change π x ∈ V i at hx
      rwa [hπx] at hx
    exact hxc.mem_open (O (r i)).isOpen (hr i hcV)

/-- Patch neighbourhood factorizations using the Chinese remainder isomorphism associated
with a finite clopen partition. Source: blueprint lem-weil-pbc-local-rings-ind-zariski,
proof paragraph 2 (blueprint: lem-weil-pbc-local-rings-ind-zariski). -/
private theorem patch_factorization
    (A B P : Type u) [CommRing A] [CommRing B] [CommRing P]
    [Algebra A B] [Algebra A P]
    (α : P →ₐ[A] B) (n : ℕ) (f : Fin n → A) (g : Fin n → B)
    (β : ∀ i, P →ₐ[A] Localization.Away (f i))
    (γ : ∀ i, Localization.Away (f i) →ₐ[A] Localization.Away (g i))
    (hfactor : ∀ i, (γ i).comp (β i) =
      (IsScalarTower.toAlgHom A B (Localization.Away (g i))).comp α)
    (Q : Fin n → Set (PrimeSpectrum B)) (hQ : ∀ i, IsClopen (Q i))
    (hdisj : Pairwise (fun i j ↦ Disjoint (Q i) (Q j)))
    (hcover : (⋃ i, Q i) = Set.univ)
    (hsub : ∀ i, Q i ⊆ PrimeSpectrum.basicOpen (g i)) :
    ∃ δ : ((i : Fin n) → Localization.Away (f i)) →ₐ[A] B,
      δ.comp (AlgHom.pi β) = α := by
  classical
  choose e he heQ using fun i ↦
    PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen (hQ i)
  have hortho : OrthogonalIdempotents e := by
    refine ⟨he, fun i j hij ↦ ?_⟩
    apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem ((he i).mul (he j)) .zero
    rw [PrimeSpectrum.basicOpen_mul, PrimeSpectrum.basicOpen_zero]
    apply TopologicalSpace.Opens.ext
    change (PrimeSpectrum.basicOpen (e i) : Set (PrimeSpectrum B)) ∩
      (PrimeSpectrum.basicOpen (e j) : Set (PrimeSpectrum B)) = ∅
    rw [← heQ i, ← heQ j]
    exact Set.disjoint_iff_inter_eq_empty.mp (hdisj hij)
  have hcomplete : CompleteOrthogonalIdempotents e := by
    refine ⟨hortho, ?_⟩
    have hs : IsIdempotentElem (∑ i, e i) := by
      simpa using hortho.isIdempotentElem_sum (s := Finset.univ)
    apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem hs .one
    apply TopologicalSpace.Opens.ext
    apply Set.ext
    intro x
    change (∑ i, e i) ∉ x.asIdeal ↔ (1 : B) ∉ x.asIdeal
    refine ⟨fun _ ↦ x.isPrime.one_notMem, fun _ ↦ ?_⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover ▸ Set.mem_univ x)
    have hei : e i ∉ x.asIdeal := by
      have := hi
      rw [heQ i] at this
      exact this
    intro hsum
    apply hei
    have h := x.asIdeal.mul_mem_left (e i) hsum
    rwa [hortho.mul_sum_of_mem (Finset.mem_univ i)] at h
  let J : Fin n → Ideal B := fun i ↦ Ideal.span {1 - e i}
  let C := fun i ↦ B ⧸ J i
  let π : B →ₐ[A] ((i : Fin n) → C i) := AlgHom.pi fun i ↦ Ideal.Quotient.mkₐ A (J i)
  let E : B ≃ₐ[A] ((i : Fin n) → C i) := AlgEquiv.ofBijective π hcomplete.bijective_pi
  have hg (i : Fin n) : IsUnit (algebraMap B (C i) (g i)) := by
    apply Ideal.span_singleton_eq_top.mp
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    let q : PrimeSpectrum B :=
      PrimeSpectrum.comap (algebraMap B (C i)) ⟨m, hm.isPrime⟩
    have h1e : 1 - e i ∈ q.asIdeal := by
      change algebraMap B (C i) (1 - e i) ∈ m
      have hz : algebraMap B (C i) (1 - e i) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
      rw [hz]
      exact m.zero_mem
    have heq : e i ∉ q.asIdeal := by
      intro h
      apply q.isPrime.ne_top
      apply (Ideal.eq_top_iff_one q.asIdeal).mpr
      simpa using q.asIdeal.add_mem h1e h
    have hqQ : q ∈ Q i := by rw [heQ i]; exact heq
    exact hsub i hqQ (hle (Ideal.subset_span (Set.mem_singleton _)))
  let ρ : ∀ i, Localization.Away (g i) →ₐ[A] C i := fun i ↦
    IsLocalization.Away.liftAlgHom (g i)
      (f := IsScalarTower.toAlgHom A B (C i)) (hg i)
  have hρ (i : Fin n) (b : B) : ρ i (algebraMap B _ b) = algebraMap B (C i) b := by
    simp only [ρ, IsLocalization.Away.coe_liftAlgHom, IsLocalization.Away.lift_eq]
    rfl
  let δ₀ : ((i : Fin n) → Localization.Away (f i)) →ₐ[A] ((i : Fin n) → C i) :=
    AlgHom.pi fun i ↦ ((ρ i).comp (γ i)).comp (Pi.evalAlgHom A _ i)
  refine ⟨E.symm.toAlgHom.comp δ₀, ?_⟩
  apply AlgHom.ext
  intro x
  apply E.injective
  change E (E.symm (δ₀ (AlgHom.pi β x))) = E (α x)
  rw [E.apply_symm_apply]
  funext i
  change ρ i (γ i (β i x)) = algebraMap B (C i) (α x)
  change ρ i (((γ i).comp (β i)) x) = _
  rw [AlgHom.congr_fun (hfactor i) x]
  exact hρ i (α x)

/-- A ring map identifying all prime localizations and having w-local target presents that
 target as a filtered colimit of finite products of principal localizations of the source.
 No w-locality of the source or of the map is assumed.

Source: blueprint, proper base change, `sk-thm-properbasechange`, lemma
`lem-weil-pbc-local-rings-ind-zariski`
(blueprint: lem-weil-pbc-local-rings-ind-zariski).

Proof:
1. Given a finitely presented algebra `P` and `α : P → B`, invert the stalk isomorphism
   at each prime `q`. Apply `factors_through_principal_localization` to descend the resulting
   map `P → A_p` to `β : P → A_f`, with `f` outside the contracted prime `p`.
2. Map `A_f` canonically to `B` localized at `g₀ = algebraMap A B f`. Its composite with
   `β` agrees with `α` in `B_q`, by localization extensionality. Choose a finite polynomial
   presentation of `P`. For each generator, write the difference as a fraction in `B_g₀`;
   its numerator vanishes in `B_q`, hence has an annihilator outside `q`. Multiply these
   annihilators with `g₀` to obtain `g` outside `q`. After mapping to `B_g`, all differences
   vanish by unit cancellation. Equality on generators and surjectivity give the desired
   factorization `P → A_f → B_g`.
3. The proved homeomorphism `WLocalSpace.closedPointsHomeomorph` makes the closed points
   profinite. Mathlib's finite disjoint clopen refinement theorem gives a finite partition
   subordinate to the neighbourhoods `D(g)`. Pull it back to the spectrum along the
   continuous map sending a point to the closed point of its connected component.
   A point specializes to that closed point, so each pulled-back part stays inside its
   selected open. This includes the empty partition of the empty spectrum.
4. Associate idempotents `e_i` to the clopen parts. Disjointness and injectivity of the
   idempotent/basic-open correspondence give orthogonality. The sum is idempotent and
   belongs to no prime, so its basic open is `D(1)` and the same injectivity gives sum one.
   `CompleteOrthogonalIdempotents.bijective_pi` identifies `B` with `∏ B/(1-e_i)`.
5. Each selected `g_i` becomes a unit in `B/(1-e_i)`: otherwise a maximal ideal containing
   it contracts to a prime in `D(e_i)`, contradicting `D(e_i) ⊆ D(g_i)`. Extend the local
   maps by the localization universal property and compose their product with the inverse
   Chinese remainder isomorphism. This gives `P → ∏ A_fᵢ → B` with composite `α`.
6. Principal localizations are finitely presented by
   `IsLocalization.Away.finitePresentation`; their finite products are finitely presented
   by `Algebra.FinitePresentation.pi`, including the empty product. Transport along algebra
   equivalences, and let `E` be the set of all algebras equivalent to these products.
7. Apply `CommAlgCat.exists_filtered_colimit_of_factorization` to `E` and step 5. Its small
   filtered diagram and colimit cocone give exactly `IsIndPrincipalZariski A B`. -/
theorem isIndPrincipalZariski_of_bijective_localRingHom
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [IsWLocalRing B]
    (hlocal : ∀ (q : Ideal B) [q.IsPrime],
      Function.Bijective
        (Localization.localRingHom (q.comap (algebraMap A B)) q (algebraMap A B) rfl)) :
    IsIndPrincipalZariski A B := by
  classical
  let E : Set (CommAlgCat.{u} A) := fun C ↦
    ∃ (n : ℕ) (f : Fin n → A),
      Nonempty (C ≃ₐ[A] ((i : Fin n) → Localization.Away (f i)))
  have hfp : ∀ C ∈ E, FinitePresentation A C := by
    rintro C ⟨n, f, ⟨e⟩⟩
    exact FinitePresentation.equiv e.symm
  have hfact : ∀ (P : CommAlgCat.{u} A), FinitePresentation A P →
      ∀ α : P ⟶ CommAlgCat.of A B,
      ∃ C ∈ E, ∃ (β : P ⟶ C) (γ : C ⟶ CommAlgCat.of A B), β ≫ γ = α := by
    intro P hP α
    have := hP
    have hloc (q : PrimeSpectrum B) :=
      local_factorization A B P q.asIdeal (hlocal q.asIdeal) α.hom
    choose f g hg β γ hγ using hloc
    obtain ⟨n, Q, r, hQ, hdisj, hcover, hsub⟩ :=
      clopen_refinement B (PrimeSpectrum B) (fun q ↦ PrimeSpectrum.basicOpen (g q))
        (fun c ↦ ⟨c.val, hg c.val⟩)
    obtain ⟨δ, hδ⟩ := patch_factorization A B P α.hom n
      (f ∘ r) (g ∘ r) (fun i ↦ β (r i)) (fun i ↦ γ (r i))
      (fun i ↦ hγ (r i)) Q hQ hdisj hcover hsub
    refine ⟨CommAlgCat.of A ((i : Fin n) → Localization.Away (f (r i))),
      ⟨n, f ∘ r, ⟨AlgEquiv.refl⟩⟩, CommAlgCat.ofHom (AlgHom.pi (fun i ↦ β (r i))),
      CommAlgCat.ofHom δ, ?_⟩
    exact CommAlgCat.hom_ext hδ
  obtain ⟨I, hI, hfiltered, D, ι, hD, ⟨hc⟩⟩ :=
    CommAlgCat.exists_filtered_colimit_of_factorization A (CommAlgCat.of A B) E hfp hfact
  exact ⟨I, hI, hfiltered, ⟨D, ι, hc⟩, hD⟩

end Algebra
end

/-! ### From `PrincipalWLocalization` -/
section
/-! # The finite-partition principal w-localization

Source: blueprint, proper base change, definition of the affine w-localization, order 1222
(blueprint: def-weil-pbc-w-localization).

The indices remember both the finite constructible partition and its denominators.
Refinement requires divisibility of denominators, so the component localization maps exist.
This construction is distinct from the upstream `WLocalization`, whose stages use localizations
at larger submonoids. No geometric property or comparison with that construction is asserted.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace PrincipalWLocalization

variable (A : Type u) [CommRing A]

/-- A finite constructible partition of `Spec A` with one nonvanishing denominator per part.
The unique-membership condition allows the empty partition precisely for an empty spectrum.
Source: blueprint order 1222 (blueprint: def-weil-pbc-w-localization). -/
structure Index where
  parts : Finset (Set (PrimeSpectrum A))
  nonempty : ∀ E ∈ parts, Set.Nonempty E
  constructible : ∀ E ∈ parts, Topology.IsConstructible E
  partition : ∀ p : PrimeSpectrum A, ∃! E : parts, p ∈ E.val
  denominator : parts → A
  nonvanishing : ∀ E : parts, E.val ⊆ PrimeSpectrum.basicOpen (denominator E)

variable {A}

/-- Refinement together with divisibility from each parent denominator to the child denominator.
Source: blueprint order 1222 (blueprint: def-weil-pbc-w-localization). -/
def Refines (i j : Index A) : Prop :=
  ∀ F : j.parts, ∃ E : i.parts, F.val ⊆ E.val ∧ i.denominator E ∣ j.denominator F

/-- Refinement is reflexive: use each part itself and reflexivity of subset and divisibility.
Source: blueprint order 1222 (blueprint: def-weil-pbc-w-localization). -/
theorem refines_refl (i : Index A) : Refines i i := by
  intro F
  exact ⟨F, Set.Subset.rfl, dvd_refl _⟩

/-- Refinement is transitive: choose the intermediate parent, then its parent, and compose
subset inclusions and divisibility relations. Source: blueprint order 1222
(blueprint: def-weil-pbc-w-localization). -/
theorem refines_trans (i j k : Index A) (hij : Refines i j) (hjk : Refines j k) :
    Refines i k := by
  intro F
  obtain ⟨E, hFE, hdFE⟩ := hjk F
  obtain ⟨D, hED, hdED⟩ := hij E
  exact ⟨D, hFE.trans hED, hdED.trans hdFE⟩

/-- The index preorder, with exactly the refinement/divisibility relation as its order.
Source: blueprint order 1222 (blueprint: def-weil-pbc-w-localization). -/
instance indexPreorder : Preorder (Index A) where
  le := Refines
  le_refl := refines_refl
  le_trans := refines_trans

/-- The product of principal localizations at an index; the empty product is the zero ring.
Its ring operations and its diagonal algebra structure are the standard Pi structures.
Source: blueprint order 1222 (blueprint: def-weil-pbc-w-localization). -/
abbrev Stage (i : Index A) : Type u :=
  (E : i.parts) → Localization.Away (i.denominator E)

/-- Choose the parent supplied by refinement. It is unique because the child is nonempty
and different parts of a partition are disjoint. Source: blueprint order 1222
(blueprint: def-weil-pbc-w-localization). -/
noncomputable def parent {i j : Index A} (h : i ≤ j) (F : j.parts) : i.parts :=
  Classical.choose (h F)

/-- The chosen parent's denominator divides the child's denominator, by the refinement data.
Source: blueprint order 1222 (blueprint: def-weil-pbc-w-localization).
Proof: take the divisibility clause of the witness selected by `parent`. -/
theorem parent_dvd {i j : Index A} (h : i ≤ j) (F : j.parts) :
    i.denominator (parent h F) ∣ j.denominator F := by
  exact (Classical.choose_spec (h F)).2

/-- The component map is projection to the parent followed by the unique localization map.
The parent's denominator is a unit in the child localization by divisibility. The lift sends
`a/f^n` to `(a/1)(f/1)^(-n)`. Source: blueprint order 1222
(blueprint: def-weil-pbc-w-localization). -/
noncomputable def transition {i j : Index A} (h : i ≤ j) : Stage i →ₐ[A] Stage j :=
  AlgHom.pi fun F ↦
    (IsLocalization.Away.liftAlgHom (i.denominator (parent h F))
      (f := Algebra.ofId A (Localization.Away (j.denominator F)))
      (IsLocalization.Away.isUnit_of_dvd (j.denominator F) (parent_dvd h F))).comp
        (Pi.evalAlgHom A (fun E : i.parts ↦ Localization.Away (i.denominator E)) (parent h F))

private theorem parent_eq_of_subset {i j : Index A} (h : i ≤ j) (F : j.parts)
    (E : i.parts) (hFE : F.val ⊆ E.val) : parent h F = E := by
  obtain ⟨p, hp⟩ := j.nonempty F.val F.property
  exact (i.partition p).unique ((Classical.choose_spec (h F)).1 hp) (hFE hp)

private theorem parent_self (i : Index A) (E : i.parts) : parent (le_refl i) E = E :=
  parent_eq_of_subset _ _ _ Set.Subset.rfl

private theorem component_eq {B : Type u} [CommRing B] [Algebra A B]
    (i : Index A) {E F : i.parts} (h : E = F)
    (φ : Localization.Away (i.denominator E) →ₐ[A] B)
    (ψ : Localization.Away (i.denominator F) →ₐ[A] B) (x : Stage i) :
    φ (x E) = ψ (x F) := by
  subst F
  exact DFunLike.congr_fun
    (Subsingleton.elim (h := IsLocalization.algHom_subsingleton
      (Submonoid.powers (i.denominator E))) φ ψ) (x E)

/-- Identity transitions are identities. A nonempty part has itself as its unique parent;
localization uniqueness identifies its component map with the identity.
Source: blueprint order 1222 (blueprint: def-weil-pbc-w-localization). -/
theorem transition_id (i : Index A) : transition (le_refl i) = AlgHom.id A (Stage i) := by
  apply AlgHom.ext
  intro x
  funext E
  exact component_eq i (parent_self i E)
    (IsLocalization.Away.liftAlgHom (i.denominator (parent (le_refl i) E))
      (f := Algebra.ofId A (Localization.Away (i.denominator E)))
      (IsLocalization.Away.isUnit_of_dvd (i.denominator E) (parent_dvd (le_refl i) E)))
    (AlgHom.id A _) x

/-- Transitions compose. For each final child the two successive parents equal its direct
parent by the partition property. The resulting localization maps agree on `A`, so
`IsLocalization.ringHom_ext` identifies them; product extensionality finishes.
Source: blueprint order 1222 (blueprint: def-weil-pbc-w-localization). -/
theorem transition_comp {i j k : Index A} (hij : i ≤ j) (hjk : j ≤ k) :
    transition (le_trans hij hjk) = (transition hjk).comp (transition hij) := by
  apply AlgHom.ext
  intro x
  funext F
  have hparent : parent (le_trans hij hjk) F = parent hij (parent hjk F) :=
    parent_eq_of_subset _ _ _
      ((Classical.choose_spec (hjk F)).1.trans
        (Classical.choose_spec (hij (parent hjk F))).1)
  exact component_eq i hparent
    (IsLocalization.Away.liftAlgHom (i.denominator (parent (le_trans hij hjk) F))
      (f := Algebra.ofId A (Localization.Away (k.denominator F)))
      (IsLocalization.Away.isUnit_of_dvd (k.denominator F)
        (parent_dvd (le_trans hij hjk) F)))
    ((IsLocalization.Away.liftAlgHom (j.denominator (parent hjk F))
      (f := Algebra.ofId A (Localization.Away (k.denominator F)))
      (IsLocalization.Away.isUnit_of_dvd (k.denominator F) (parent_dvd hjk F))).comp
        (IsLocalization.Away.liftAlgHom (i.denominator (parent hij (parent hjk F)))
          (f := Algebra.ofId A (Localization.Away (j.denominator (parent hjk F))))
          (IsLocalization.Away.isUnit_of_dvd (j.denominator (parent hjk F))
            (parent_dvd hij (parent hjk F))))) x

/-- The diagram of commutative `A`-algebras with the specified component localization maps.
Source: blueprint order 1222 (blueprint: def-weil-pbc-w-localization). -/
noncomputable def diagram : Index A ⥤ CommAlgCat.{u} A where
  obj i := CommAlgCat.of A (Stage i)
  map h := CommAlgCat.ofHom (transition h.le)
  map_id i := congrArg CommAlgCat.ofHom (transition_id i)
  map_comp h g := congrArg CommAlgCat.ofHom (transition_comp h.le g.le)

/-- The index category is filtered. It is inhabited by the one-part partition with denominator
one when the spectrum is nonempty, and by the empty partition otherwise. For two indices,
take all nonempty intersections, with denominator the product of the two denominators.
Constructibility is closed under intersections; primality gives nonvanishing of the product.
Each factor divides that product, giving both refinement arrows. Parallel arrows are equal
because the category is a preorder. Source: blueprint order 1222
(blueprint: def-weil-pbc-w-localization). -/
theorem index_isFiltered : IsFiltered (Index A) := by
  classical
  have hnonempty : Nonempty (Index A) := by
    let P := ({Set.univ} : Finset (Set (PrimeSpectrum A))).filter Set.Nonempty
    refine ⟨{
      parts := P
      nonempty := fun E hE ↦ (Finset.mem_filter.mp hE).2
      constructible := ?_
      partition := ?_
      denominator := fun _ ↦ 1
      nonvanishing := ?_ }⟩
    · intro E hE
      have h : E = Set.univ := Finset.mem_singleton.mp (Finset.mem_filter.mp hE).1
      rw [h]
      exact Topology.IsConstructible.univ
    · intro p
      have hU : Set.univ ∈ P :=
        Finset.mem_filter.mpr ⟨Finset.mem_singleton_self _, ⟨p, Set.mem_univ p⟩⟩
      refine ⟨⟨Set.univ, hU⟩, Set.mem_univ p, ?_⟩
      intro E _
      exact Subtype.ext (Finset.mem_singleton.mp (Finset.mem_filter.mp E.property).1)
    · intro E
      simp only [PrimeSpectrum.basicOpen_one, TopologicalSpace.Opens.coe_top]
      exact Set.subset_univ _
  have hcommon : ∀ i j : Index A, ∃ k : Index A, i ≤ k ∧ j ≤ k := by
    intro i j
    let P := ((i.parts ×ˢ j.parts).image fun EF ↦ EF.1 ∩ EF.2).filter Set.Nonempty
    have hparts : ∀ G ∈ P, ∃ (E : i.parts) (F : j.parts), G = E.val ∩ F.val := by
      intro G hG
      obtain ⟨hG, _⟩ := Finset.mem_filter.mp hG
      obtain ⟨EF, hEF, hG⟩ := Finset.mem_image.mp hG
      obtain ⟨hE, hF⟩ := Finset.mem_product.mp hEF
      exact ⟨⟨EF.1, hE⟩, ⟨EF.2, hF⟩, hG.symm⟩
    choose left right heq using fun G : P ↦ hparts G.val G.property
    let k : Index A := {
      parts := P
      nonempty := fun G hG ↦ (Finset.mem_filter.mp hG).2
      constructible := by
        intro G hG
        have h : G = (left ⟨G, hG⟩).val ∩ (right ⟨G, hG⟩).val := heq ⟨G, hG⟩
        rw [h]
        exact (i.constructible _ (left ⟨G, hG⟩).property).inter
          (j.constructible _ (right ⟨G, hG⟩).property)
      partition := by
        intro p
        obtain ⟨E, hpE, hE⟩ := i.partition p
        obtain ⟨F, hpF, hF⟩ := j.partition p
        have hG : E.val ∩ F.val ∈ P := by
          apply Finset.mem_filter.mpr
          refine ⟨?_, ⟨p, hpE, hpF⟩⟩
          exact Finset.mem_image.mpr
            ⟨(E.val, F.val), Finset.mem_product.mpr ⟨E.property, F.property⟩, rfl⟩
        refine ⟨⟨E.val ∩ F.val, hG⟩, ⟨hpE, hpF⟩, ?_⟩
        intro G hpG
        have hp : p ∈ (left G).val ∩ (right G).val := (heq G) ▸ hpG
        have hleft : left G = E := hE _ hp.1
        have hright : right G = F := hF _ hp.2
        apply Subtype.ext
        exact (heq G).trans (by rw [hleft, hright])
      denominator := fun G ↦ i.denominator (left G) * j.denominator (right G)
      nonvanishing := by
        intro G p hp
        rw [PrimeSpectrum.basicOpen_mul]
        have hp' : p ∈ (left G).val ∩ (right G).val := (heq G) ▸ hp
        exact ⟨i.nonvanishing (left G) hp'.1, j.nonvanishing (right G) hp'.2⟩ }
    refine ⟨k, ?_, ?_⟩
    · intro G
      refine ⟨left G, ?_, dvd_mul_right _ _⟩
      exact fun p hp ↦ ((heq G) ▸ hp).1
    · intro G
      refine ⟨right G, ?_, dvd_mul_left _ _⟩
      exact fun p hp ↦ ((heq G) ▸ hp).2
  exact {
    nonempty := hnonempty
    cocone_objs := fun i j ↦ by
      obtain ⟨k, hi, hj⟩ := hcommon i j
      exact ⟨k, homOfLE hi, homOfLE hj, trivial⟩
    cocone_maps := fun {i j} f g ↦ ⟨j, 𝟙 j, Subsingleton.elim _ _⟩ }

attribute [instance] index_isFiltered

/-- The affine principal w-localization is the colimit of the partition/denominator diagram
in commutative `A`-algebras. Its algebra structure is the structural map induced by the diagonal
maps into the stages. Source: blueprint order 1222 (blueprint: def-weil-pbc-w-localization). -/
noncomputable def algebra (A : Type u) [CommRing A] : CommAlgCat.{u} A :=
  colimit (diagram (A := A))

/-- This colimit is ind-Zariski in the principal-localization sense. Use the filtered diagram
above and its colimit cocone; enumerate each finite set of parts by `Fin n` and transport the
product along that enumeration. The empty set gives `n = 0`.
Source: blueprint order 1222 (blueprint: def-weil-pbc-w-localization). -/
theorem isIndPrincipalZariski : Algebra.IsIndPrincipalZariski A (algebra A) := by
  classical
  refine ⟨Index A, inferInstance, inferInstance,
    ColimitPresentation.colimit (diagram (A := A)), ?_⟩
  intro i
  let e := Fintype.equivFin i.parts
  refine ⟨Fintype.card i.parts, fun j ↦ i.denominator (e.symm j), ?_⟩
  exact ⟨AlgEquiv.piCongrLeft' A
    (fun E : i.parts ↦ Localization.Away (i.denominator E)) e⟩

end PrincipalWLocalization
end

/-! ### From `EtaleContractionProperties` -/
section
/-!
# Properties of the étale contraction

Source: blueprint, sec-proper-base-change/sk-thm-properbasechange, order 1227;
Stacks Project, proetale.tex, lemma-first-construction and Tag 097V
(blueprint: lem-weil-pbc-etale-contraction).
-/

universe u

namespace CommRingCat

-- The finite tensors present the step map as a pro-morphism in the opposite category.
open CategoryTheory CategoryTheory.Limits Opposite in
private theorem step_pro
    (Q : MorphismProperty CommRingCat.{u}ᵒᵖ)
    [Q.IsMultiplicative] [Q.IsStableUnderBaseChange]
    (hQ : etale.op ⊓ faithfullyFlat.op ≤ Q) (R : CommRingCat.{u}ᵒᵖ) :
    MorphismProperty.pro.{u} Q (EtaleContraction.step R).hom := by
  let : Nonempty (FiniteFamilies (EtaleContraction.Representatives R)) :=
    ⟨⟨∅, Set.finite_empty⟩⟩
  refine ⟨(FiniteFamilies (EtaleContraction.Representatives R))ᵒᵖ,
    inferInstance, inferInstance, EtaleContraction.finiteDiagram R ⋙ Over.forget R,
    ?_, ?_, ?_, fun j ↦ ⟨?_, ?_⟩⟩
  · exact { app i := ((EtaleContraction.finiteDiagram R).obj i).hom }
  · exact Functor.whiskerRight (limit.cone (EtaleContraction.finiteDiagram R)).π
      (Over.forget R)
  · exact isLimitOfPreserves (Over.forget R) (limit.isLimit _)
  · change Q (WidePullback.base _)
    apply MorphismProperty.widePullbackBase
    intro i
    exact hQ _ (FiniteFamilies.property_hom _ i)
  · exact (limit.π (EtaleContraction.finiteDiagram R) j).w

open CategoryTheory CategoryTheory.Limits Opposite in
private theorem projection_prop
    (Q : MorphismProperty CommRingCat.{u}ᵒᵖ) [Q.IsMultiplicative]
    (hQ : MorphismProperty.pro.{u} Q = Q)
    (hstep : ∀ R : CommRingCat.{u}ᵒᵖ, Q (EtaleContraction.step R).hom)
    (R : CommRingCat.{u}) (n : ℕ) : Q (limit.π (EtaleContraction.sequence (op R)) (op n)) := by
  have hπ : MorphismProperty.pro.{0} Q
      (limit.π (EtaleContraction.sequence (op R)) (op n)) := by
    apply MorphismProperty.pro_coneπ (P := Q) (limit.isLimit _) (op n)
    intro k f
    apply MorphismProperty.ofOpSequence_map_of_isMultiplicative
    intro m
    exact hstep _
  exact hQ.le _ (MorphismProperty.pro_of_univLE.{0, u} _ hπ)

open CategoryTheory CategoryTheory.Limits Opposite in
private theorem projection_faithfullyFlat (R : CommRingCat.{u}) (n : ℕ) :
    (EtaleContraction.ι R n).hom.FaithfullyFlat := by
  have hQ : MorphismProperty.pro.{u} faithfullyFlat.op = faithfullyFlat.op := by
    conv_rhs => rw [← CommRingCat.ind_faithfullyFlat_eq_faithfullyFlat]
    rw [MorphismProperty.ind_eq_unop_pro_op, MorphismProperty.op_unop]
  exact projection_prop faithfullyFlat.op hQ
    (fun A ↦ hQ.le _ (step_pro faithfullyFlat.op inf_le_right A)) R n

open CategoryTheory CategoryTheory.Limits Opposite in
private theorem projection_indEtale (R : CommRingCat.{u}) (n : ℕ) :
    (EtaleContraction.ι R n).hom.IndEtale := by
  let P := CommRingCat.etale.op
  have hfp := MorphismProperty.le_isFinitelyPresentable_op_op
    CommRingCat.etale_le_isFinitelyPresentable.{u}
  let : (MorphismProperty.pro.{u} P).IsMultiplicative :=
    MorphismProperty.IsMultiplicative.pro_of_le_isFinitelyPresentable hfp
  rw [RingHom.IndEtale.iff_ind_etale, MorphismProperty.ind_eq_unop_pro_op]
  exact projection_prop (MorphismProperty.pro.{u} P) (MorphismProperty.pro_pro hfp)
    (step_pro P inf_le_left) R n

-- The singleton containing the chosen isomorphism class supplies the next-stage map.
open CategoryTheory CategoryTheory.Limits Opposite in
private theorem step_factor (X : CommRingCat.{u}ᵒᵖ) {Y : CommRingCat.{u}ᵒᵖ}
    (f : Y ⟶ X) (hf : (etale.op ⊓ faithfullyFlat.op) f) :
    ∃ g : (EtaleContraction.step X).left ⟶ Y, g ≫ f = (EtaleContraction.step X).hom := by
  classical
  let P := etale.op ⊓ faithfullyFlat.op
  let A : P.Over ⊤ X := .mk _ _ hf
  let E := equivSmallModel.{u} (P.Over ⊤ X)
  let M := E.functor.obj A
  let r := toSkeleton M
  let U : FiniteFamilies (EtaleContraction.Representatives X) :=
    ⟨{r}, Set.finite_singleton _⟩
  let V := (FiniteFamilies.map (fromSkeleton (SmallModel.{u} (P.Over ⊤ X)))).obj U
  let i : V.Index := ⟨(fromSkeleton _).obj r, r, rfl, rfl⟩
  let e : E.inverse.obj ((fromSkeleton _).obj r) ≅ A :=
    E.inverse.mapIso (fromSkeletonToSkeletonIso M) ≪≫ (E.unitIso.app A).symm
  let p : (EtaleContraction.step X) ⟶ Over.mk f :=
    limit.π (EtaleContraction.finiteDiagram X) (op U) ≫
      Over.homMk (WidePullback.π V.hom i) (WidePullback.π_arrow _ _) ≫
      (Functor.mapIso (MorphismProperty.Over.forget P ⊤ X) e).hom
  exact ⟨p.left, p.w⟩

open CategoryTheory CategoryTheory.Limits Opposite in
private theorem contraction_retraction (R : CommRingCat.{u})
    {Y : CommRingCat.{u}ᵒᵖ} (f : Y ⟶ op R.etaleContraction)
    (hf : etale.op f) (hf' : faithfullyFlat.op f) :
    ∃ g : op R.etaleContraction ⟶ Y, g ≫ f = 𝟙 (op R.etaleContraction) := by
  let P := etale.op
  let : MorphismProperty.PreProSpreads.{0} P := by
    rw [MorphismProperty.PreProSpreads.op_iff]
    exact MorphismProperty.PreIndSpreads.of_univLE.{u} _
  -- Algebraic étale descent already supplies an affine model and its pullback square.
  obtain ⟨⟨n⟩, D', u, v, hv, hu⟩ := P.exists_isPullback_of_isCofiltered
    (limit.cone (EtaleContraction.sequence (op R))) (limit.isLimit _) f hf
  have hu' : faithfullyFlat.op u := by
    have hfg : faithfullyFlat.op (v ≫ u) := by
      rw [← hv.w]
      exact faithfullyFlat.op.comp_mem _ _ hf' (projection_faithfullyFlat R n)
    change faithfullyFlat u.unop
    -- The composite is surjective on spectra; the descended étale map is flat.
    rw [CommRingCat.faithfullyFlat_eq] at ⊢ hfg
    refine ⟨hu.smooth.flat, ?_⟩
    exact Function.Surjective.of_comp (g := PrimeSpectrum.comap v.unop.hom) hfg.2
  obtain ⟨p, hp⟩ := step_factor (EtaleContraction.stage (op R) n) u ⟨hu, hu'⟩
  let l : op R.etaleContraction ⟶ Y :=
    hv.lift (𝟙 _) (limit.π (EtaleContraction.sequence (op R)) (op (n + 1)) ≫ p) (by
      rw [Category.id_comp, Category.assoc, hp]
      have h := limit.w (EtaleContraction.sequence (op R))
        (homOfLE (Nat.le_succ n)).op
      simpa [EtaleContraction.sequence, Functor.ofOpSequence] using h.symm)
  exact ⟨l, by simp [l]⟩

open CategoryTheory CategoryTheory.Limits Opposite in
private theorem ring_retraction (R : CommRingCat.{u})
    (B : Type u) [CommRing B] [Algebra R.etaleContraction B]
    (hB : Algebra.Etale R.etaleContraction B)
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R.etaleContraction B))) :
    ∃ g : B →+* R.etaleContraction,
      g.comp (algebraMap R.etaleContraction B) = RingHom.id R.etaleContraction := by
  have het : (algebraMap R.etaleContraction B).Etale := RingHom.etale_algebraMap.mpr hB
  have hff : (algebraMap R.etaleContraction B).FaithfullyFlat :=
    RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mpr ⟨het.smooth.flat, hsurj⟩
  obtain ⟨g, hg⟩ := contraction_retraction R
    (CommRingCat.ofHom (algebraMap R.etaleContraction B)).op het hff
  exact ⟨g.unop.hom, congr($(hg).unop.hom)⟩

/-- The canonical map to the étale contraction is faithfully flat and ind-étale;
faithfully flat étale algebras of finite presentation over it admit a section,
and its maximal localizations are strictly henselian.
Source: blueprint order 1227; Stacks, lemma-first-construction and Tag 097V
(blueprint: lem-weil-pbc-etale-contraction).

Proof plan:
1. Each chosen factor is faithfully flat. Tensor base change and composition preserve
faithful flatness, by the tensor identities on complexes, so all finite tensors and their
transition maps are faithfully flat, including the empty tensor.
2. Apply lem-weil-pbc-directed-colimit-faithfully-flat-algebras to finite-subset colimits
and then the sequential colimit. Apply lem-weil-pbc-ind-etale-stability to finite tensors,
base changes, compositions and these filtered colimits to get ind-étaleness.
3. An étale finitely presented algebra over the contraction descends to a stage by
lem-weil-pbc-etale-finite-data-descent. Use lem-weil-pbc-limit-affine-transition and
lem-weil-pbc-limit-affine-stage to make the model affine; its quasi-compactness and
quasi-separatedness and affine transitions follow from
lem-weil-pbc-affine-morphism-permanence. Faithful flatness descends by applying the
faithfully flat stage-to-colimit extension to complexes and the tensor identities.
4. The descended algebra is isomorphic to a chosen representative. Its singleton tensor
factor maps into the next stage and hence into the contraction. The tensor universal
property (lem-weil-pbc-algebra-tensor-base-change-universal-property) gives the retraction
by sending s ⊗ b to s h(b).
5. Every étale map of affine spectra is of finite presentation, since it is locally so
and affine maps are quasi-compact and quasi-separated. Thus the section property applies
to all faithfully flat étale algebras. Apply
lem-weil-pbc-split-etale-covers-maximal-local-criterion (Tag 097V) to each maximal ideal.
-/
theorem etaleContraction_properties (R : CommRingCat.{u}) :
    (EtaleContraction.ι R 0).hom.FaithfullyFlat ∧
    (EtaleContraction.ι R 0).hom.IndEtale ∧
    (∀ (B : Type u) [CommRing B] [Algebra R.etaleContraction B],
      Module.FaithfullyFlat R.etaleContraction B →
      Algebra.Etale R.etaleContraction B →
      Algebra.FinitePresentation R.etaleContraction B →
      Nonempty (B →ₐ[R.etaleContraction] R.etaleContraction)) ∧
    (∀ (m : Ideal R.etaleContraction) [m.IsMaximal],
      IsStrictlyHenselianLocalRing (Localization.AtPrime m)) := by
  refine ⟨projection_faithfullyFlat R 0, projection_indEtale R 0, ?_, ?_⟩
  · intro B _ _ hff het _
    have hff' : (algebraMap R.etaleContraction B).FaithfullyFlat :=
      RingHom.faithfullyFlat_algebraMap_iff.mpr hff
    obtain ⟨g, hg⟩ := ring_retraction R B het
      (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp hff').2
    exact ⟨{ g with commutes' := fun r ↦ congrFun (congrArg DFunLike.coe hg) r }⟩
  · intro m _
    exact IsStrictlyHenselianLocalRing.localization_atPrime_of_forall_retraction
      (ring_retraction R) m

end CommRingCat
end
