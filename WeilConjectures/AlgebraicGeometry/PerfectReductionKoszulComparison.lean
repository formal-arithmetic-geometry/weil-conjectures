/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PerfectReductionCoefficientUnits
import WeilConjectures.AlgebraicGeometry.PerfectReductionKoszulDeltaData
import WeilConjectures.AlgebraicGeometry.PerfectReductionKoszulAlphaData
import WeilConjectures.AlgebraicGeometry.PerfectReductionKoszulTransitionData
import WeilConjectures.AlgebraicGeometry.PerfectReductionKoszulSquareData
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

/-! # The strict finite Koszul comparison before derived tower descent

Source: Bhatt--Scholze, Lemma 3.5.5, perfect-complex comparison a.
(blueprint: lem-sp-perfect-reduction-koszul-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v r wR wA a b w
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules SheafOfModules.RegularQuotientCone SheafOfModules.TotalTensorSigns
open scoped ChangeOfRings

namespace CategoryTheory.PerfectReductionRoos

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  [HasSheafify J CommRingCat.{r}]
  (R : Sheaf J CommRingCat.{r})
  (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)


-- The degree-zero cone inclusion and arbitrary-term naturality are the two
-- normalizations used when checking the augmentation square on coordinates.
omit [HasSheafify J CommRingCat.{r}] in
private theorem zeroInclusion_isIso (m : ℕ) : IsIso (koszulZeroInclusion R t m) := by
  classical
  let f := principalKoszulScalarComplex R t m
  let S := (CochainComplex.singleFunctor (RegularQuotientCone.Modules R) 0).obj
    (unit (derivedChangeRingIndependentCoefficients J R))
  let e := HomologicalComplex.singleObjXSelf (.up ℤ) 0
    (unit (derivedChangeRingIndependentCoefficients J R))
  let g := (CochainComplex.mappingCone.snd f).v 0 0 (by omega) ≫ e.hom
  have hz : IsZero (S.X 1) := HomologicalComplex.isZero_single_obj_X
    (.up ℤ) 0 _ 1 (by omega)
  refine ⟨⟨g, ?_, ?_⟩⟩
  · change e.inv ≫ (CochainComplex.mappingCone.inr f).f 0 ≫
        (CochainComplex.mappingCone.snd f).v 0 0 (by omega) ≫ e.hom = 𝟙 _
    simp only [CochainComplex.mappingCone.inr_f_snd_v_assoc, Iso.inv_hom_id]
  · apply CochainComplex.mappingCone.ext_from f 1 0 (by omega)
    · exact hz.eq_of_src _ _
    · change (CochainComplex.mappingCone.inr f).f 0 ≫
        ((CochainComplex.mappingCone.snd f).v 0 0 (by omega) ≫ e.hom) ≫
          e.inv ≫ (CochainComplex.mappingCone.inr f).f 0 = _
      simp only [Category.assoc, CochainComplex.mappingCone.inr_f_snd_v_assoc,
        Iso.hom_inv_id_assoc]
      change (CochainComplex.mappingCone.inr f).f 0 =
        (CochainComplex.mappingCone.inr f).f 0 ≫ 𝟙 ((CochainComplex.mappingCone f).X 0)
      rw [Category.comp_id]

variable [HasDerivedCategory.{wR} (RegularQuotientCone.Modules R)]
  [∀ m, HasDerivedCategory.{wA} (RegularQuotientCone.Modules (powerRing R t m))]

private theorem coefficientUnit_degree_naturality
    (d : ∀ m, DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (c : CoefficientUnits R t d) (m : ℕ)
    (Z W : CochainComplex (RegularQuotientCone.Modules R) ℤ) (i j : ℤ)
    (f : Z.X i ⟶ W.X j) :
    f ≫ ((c.ρ m).app W).f j =
      ((c.ρ m).app Z).f i ≫ (restriction (powerProjection R t m)).map ((d m).E.map f) := by
  classical
  obtain ⟨_hlim, _hcol, ho⟩ := sheafRingCoefficientOrdinaryAdjunction (powerProjection R t m)
  obtain ⟨adj, ha⟩ := ho (d m).E (d m).obj_eq (d m).map_eq
  have he (P : CochainComplex (RegularQuotientCone.Modules R) ℤ) (n : ℤ) :
      ((c.ρ m).app P).f n = adj.unit.app (P.X n) := by
    let e := (restriction (powerProjection R t m)).map (eqToHom ((d m).obj_eq (P.X n)))
    apply (cancel_mono e).mp
    ext U x
    change (eqToHom ((d m).obj_eq (P.X n))).val.app U
        ((((c.ρ m).app P).f n).val.app U x) =
      (eqToHom ((d m).obj_eq (P.X n))).val.app U
        ((adj.unit.app (P.X n)).val.app U x)
    have h := ha (P.X n) (changeOfRings (powerProjection R t m) (P.X n)) (𝟙 _) U x
    simp only [Category.comp_id, Adjunction.homEquiv_unit] at h
    exact (c.ρ_sections m P n U x).trans h.symm
  rw [he W j, he Z i]
  exact adj.unit.naturality f

variable [HasDerivedCategory.{wR} (ℕᵒᵖ ⥤ RegularQuotientCone.Modules R)]
  [∀ m, HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ RegularQuotientCone.Modules (powerRing R t m))]
  [HasCountableProducts (RegularQuotientCone.Modules R)]
  [∀ m, HasCountableProducts (RegularQuotientCone.Modules (powerRing R t m))]

/-- The finite Koszul comparison and augmentation, including its strict Roos square.
Source: Bhatt--Scholze, Lemma 3.5.5, comparison a
(blueprint: lem-sp-perfect-reduction-koszul-comparison). -/
structure KoszulComparison
    (d : ∀ m, DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (c : CoefficientUnits R t d) where
  δ : ∀ m P, ((total R).obj (principalKoszul R t m)).obj (roosF.obj P) ≅
    roosF.obj (tensorTower R (principalKoszul R t m) P)
  α : ∀ m, (total R).obj (principalKoszul R t m) ⟶
    (d m).E.mapHomologicalComplex (.up ℤ) ⋙
      (restriction (powerProjection R t m)).mapHomologicalComplex (.up ℤ)
  δ_shifted : ∀ m P i p n (h : p + (i + 1) = n + 1) j,
      ι R (principalKoszul R t m) (roosF.obj P) p (i + 1) (n + 1) h ≫
        (δ m P).hom.f (n + 1) ≫
        (roosχ (tensorTower R (principalKoszul R t m) P) n).hom ≫ biprod.fst ≫
        (Pi.π (fun k : ℕ ↦ (tensorTower R (principalKoszul R t m) P).asFunctor.obj
          (op k)) j).f n =
        p.negOnePow • ((tensor R).obj ((principalKoszul R t m).X p)).map
          ((roosχ P i).hom ≫ biprod.fst ≫
            (Pi.π (fun k : ℕ ↦ P.asFunctor.obj (op k)) j).f i) ≫
          ι R (principalKoszul R t m) (P.asFunctor.obj (op j)) p i n (by omega)
  δ_unshifted : ∀ m P i p n (h : p + (i + 1) = n + 1) j,
      ι R (principalKoszul R t m) (roosF.obj P) p (i + 1) (n + 1) h ≫
        (δ m P).hom.f (n + 1) ≫
        (roosχ (tensorTower R (principalKoszul R t m) P) n).hom ≫ biprod.snd ≫
        (Pi.π (fun k : ℕ ↦ (tensorTower R (principalKoszul R t m) P).asFunctor.obj
          (op k)) j).f (n + 1) =
        ((tensor R).obj ((principalKoszul R t m).X p)).map
          ((roosχ P i).hom ≫ biprod.snd ≫
            (Pi.π (fun k : ℕ ↦ P.asFunctor.obj (op k)) j).f (i + 1)) ≫
          ι R (principalKoszul R t m) (P.asFunctor.obj (op j)) p (i + 1) (n + 1) h
  α_zero : ∀ m Z i p n (h : p + i = n), p ≠ 0 →
      ι R (principalKoszul R t m) Z p i n h ≫ ((α m).app Z).f n = 0
  α_unit : ∀ m Z n,
      ((tensor R).map (koszulZeroInclusion R t m)).app (Z.X n) ≫
        ι R (principalKoszul R t m) Z 0 n n (zero_add n) ≫ ((α m).app Z).f n =
          ((SheafOfModules.monoidalCategory R).leftUnitor (Z.X n)).hom ≫
            ((c.ρ m).app Z).f n
  α_quasiIso : ∀ m Z,
      CochainComplex.IsKFlatIndependentCoefficients (R := R) Z → QuasiIso ((α m).app Z)
  koszul_changes : ∀ l m (h : l ≤ m) P,
      ((total R).map
        ((principalKoszulTower R t).map (homOfLE h).op)).app (roosF.obj P) ≫ (δ l P).hom =
        (δ m P).hom ≫ roosF.map
          (tensorTowerMap R ((principalKoszulTower R t).map (homOfLE h).op) P)

  augmentation_square : ∀ m P,
    (α m).app (roosF.obj P) ≫
      ((restriction (powerProjection R t m)).mapHomologicalComplex (.up ℤ)).map
        (roosAdditiveComparison (d m).E P) ≫
      roosAdditiveComparison (restriction (powerProjection R t m))
        ((roosTowerAction (d m).E).obj P) =
    (δ m P).hom ≫ roosF.map
      (koszulTowerComplexMap R (Functor.whiskerLeft P.asFunctor (α m)))

/-- Insert the separately constructed derived tower comparison into the strict data.
Source: Bhatt--Scholze, Lemma 3.5.5, comparison a
(blueprint: lem-sp-perfect-reduction-koszul-comparison). -/
def KoszulComparison.withDerived
    {d : ∀ m, DerivedChangeOfRingsCochainModel (powerProjection R t m)}
    {c : CoefficientUnits R t d}
    (k : KoszulComparison R t d c)
    (cR : RoosModel (RegularQuotientCone.Modules R))
    (cA : ∀ m, RoosModel (RegularQuotientCone.Modules (powerRing R t m)))
    (e : ∀ m, TowerExtension (d m).E)
    (θ : ∀ m, cR.F ⋙ (d m).T ≅ (e m).F ⋙ (cA m).F) :
    ComparisonData R t d cR cA where
  extension := e
  θ := θ
  δ := k.δ
  ρ := c.ρ
  α := k.α
  V := c.V
  v := c.v

/-- The strict finite-free calculation, independently of deriving the category of towers.

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 3.5.5, the
perfect-complex comparison a (blueprint: lem-sp-perfect-reduction-koszul-comparison).

Proof:
1. Powers of the monomorphism t remain monomorphisms. The cokernel of t^(m+1)
on the unit is the restriction of the actual sheafified quotient ring, because
both cokernels represent module maps annihilating that power. Consequently the
unit, its power multiplication and the quotient form a short exact sequence.
2. Tensor the two-term Koszul cone with an arbitrary complex. Distribute its two
finite-free terms through the countable products and the finite biproduct of the
Roos mapping cocone. Moving a Koszul summand of degree p past the shifted Roos
coordinate contributes (-1)^p; the unshifted coordinate has no sign. The total
differential dx tensor y + (-1)^p x tensor dy proves the chain-map equation.
The same distribution with the inverse signs constructs its inverse. Check the
two inverse equations on each tensor summand and each product projection.
3. Use the supplied normalized coefficient unit c, whose sections are 1 tensor x.
Since the
quotient kills t^(m+1), the scalar cone descends to ordinary extension. Transport
this augmentation through the unit-tensor cone identification. It vanishes on
all nonzero Koszul degrees and equals the coefficient unit on degree zero.
4. For a flat-term complex, tensor the short exact coefficient sequence degreewise;
the cone-to-cokernel map is a quasi-isomorphism. Resolve a K-flat complex by a
flat-term K-flat one. Naturality, K-flat tensor invariance and the two-out-of-three
property give the quasi-isomorphism for every K-flat complex.
5. Use the supplied exact restriction localization c.V and c.v. The Koszul transition
has components (t^(m-l),1); the signed
product distribution commutes with both of them. Finally the augmentation followed
by the two additive Roos comparisons agrees with the signed distribution followed
by the Roos map of the augmentations: on nonzero Koszul degree both maps vanish,
and on degree zero both apply the coefficient unit to the same product coordinate.
Product, biproduct and total-tensor extensionality give the strict square. -/
theorem nonempty_koszulComparison
    (ht : Mono (globalSectionMultiplication R t))
    (d : ∀ m, DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (c : CoefficientUnits R t d) :
    Nonempty (KoszulComparison R t d c) := by
  obtain ⟨kd⟩ := nonempty_koszulDeltaData R t ht d c
  obtain ⟨ka⟩ := nonempty_koszulAlphaData R t ht d c
  obtain ⟨kt⟩ := nonempty_koszulTransitionData R t ht d c kd.δ
    kd.δ_shifted kd.δ_unshifted
  obtain ⟨ks⟩ := nonempty_koszulSquareData R t ht d c kd.δ ka.α
    kd.δ_shifted kd.δ_unshifted ka.α_zero ka.α_unit
  refine ⟨{
    δ := kd.δ
    α := ka.α
    δ_shifted := kd.δ_shifted
    δ_unshifted := kd.δ_unshifted
    α_zero := ka.α_zero
    α_unit := ka.α_unit
    α_quasiIso := ka.α_quasiIso
    koszul_changes := kt.koszul_changes
    augmentation_square := ks.augmentation_square
  }⟩

end CategoryTheory.PerfectReductionRoos
