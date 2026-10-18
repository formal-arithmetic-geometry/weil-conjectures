/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.CategoryTheory.RingedKoszulSystem
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Homology.TelescopeColimit

import Sheaf.CategoryTheory.RingedKoszulColimitCech
import Sheaf.CategoryTheory.RingedKoszulDualFlatTerms
import Sheaf.CategoryTheory.RingedKoszulCechLocalModel
import Sheaf.CategoryTheory.RingedCechNormalizedRestriction
public import Sheaf.Algebra.Homology.KFlatCoefficientUniverse
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat

/-!
# Extended Cech complex and the strict Koszul dual limit

Source: Stacks Project, Tags 0913, 0A0A, 0941, 08JB and 0949
(blueprint: lem-weil-pbc-ringed-cech-koszul-dual-limit).

A comparison includes its actual strict tower, its total right derived inverse limit,
its unit normalization, and normalized restriction comparisons. Uniqueness of the normalized
natural isomorphisms specifies canonical comparisons, rather than arbitrary isomorphisms.
-/

@[expose] public noncomputable section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u}) (r : ℕ)
variable (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
variable [HasDerivedCategory.{w} (SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
variable [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
variable [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{u}
  ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
variable [∀ U : C, HasDerivedCategory.{w} (ℕᵒᵖ ⥤ SheafOfModules.{u}
  ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]

/-- The normalized Cech--Koszul comparison, with its slice comparisons and their coherence.
The source is the actual extended localization complex; the target is the total derived
inverse limit of the actual strict tensor tower. Units come from the degree-zero maps,
not from a choice of a triangulated filler. Natural isomorphisms are required to be uniquely
normalized by those units. This is also a specification of the comparisons on all further
slice restrictions: the coherence field applies to the derived restriction functor and
its canonical composition isomorphism, and more generally to every normalized comparison.
Source: Stacks Project, Tags 0A0A, 0941 and 08JB
(blueprint: lem-weil-pbc-ringed-cech-koszul-dual-limit). -/
structure RingedKoszulCechComparison where
  presentation : RingedKoszulLimitPresentation O r b
  theta : ringedCechCompletionFunctor O (ringedExtendedCech O r b).1 ≅
    presentation.completion
  unit : ∀ E, ringedCechCompletionUnit O (ringedExtendedCech O r b).1
    (ringedExtendedCech O r b).2 E ≫ theta.hom.app E = presentation.unit E
  theta_unique : ∀ theta' : ringedCechCompletionFunctor O (ringedExtendedCech O r b).1 ≅
      presentation.completion,
    (∀ E, ringedCechCompletionUnit O (ringedExtendedCech O r b).1
      (ringedExtendedCech O r b).2 E ≫ theta'.hom.app E = presentation.unit E) → theta' = theta
  slicePresentation : ∀ U : C, RingedKoszulLimitPresentation (O.over U) r
    (fun i ↦ ringedKoszulSliceSection O (b i) U)
  sliceTheta : ∀ U : C,
    ringedCechCompletionFunctor (O.over U)
      (ringedExtendedCech (O.over U) r (fun i ↦ ringedKoszulSliceSection O (b i) U)).1 ≅
      (slicePresentation U).completion
  slice_unit : ∀ (U : C) E,
    ringedCechCompletionUnit (O.over U)
        (ringedExtendedCech (O.over U) r (fun i ↦ ringedKoszulSliceSection O (b i) U)).1
        (ringedExtendedCech (O.over U) r (fun i ↦ ringedKoszulSliceSection O (b i) U)).2 E ≫
      (sliceTheta U).hom.app E = (slicePresentation U).unit E
  sourceRestriction : ∀ U : C,
    ringedCechCompletionFunctor O (ringedExtendedCech O r b).1 ⋙ ringedDerivedRestriction O U ≅
      ringedDerivedRestriction O U ⋙ ringedCechCompletionFunctor (O.over U)
        (ringedExtendedCech (O.over U) r (fun i ↦ ringedKoszulSliceSection O (b i) U)).1
  targetRestriction : ∀ U : C,
    presentation.completion ⋙ ringedDerivedRestriction O U ≅
      ringedDerivedRestriction O U ⋙ (slicePresentation U).completion
  source_unit : ∀ (U : C) E,
    (ringedDerivedRestriction O U).map
        (ringedCechCompletionUnit O (ringedExtendedCech O r b).1
          (ringedExtendedCech O r b).2 E) ≫ (sourceRestriction U).hom.app E =
      ringedCechCompletionUnit (O.over U)
        (ringedExtendedCech (O.over U) r (fun i ↦ ringedKoszulSliceSection O (b i) U)).1
        (ringedExtendedCech (O.over U) r (fun i ↦ ringedKoszulSliceSection O (b i) U)).2
        ((ringedDerivedRestriction O U).obj E)
  target_unit : ∀ (U : C) E,
    (ringedDerivedRestriction O U).map (presentation.unit E) ≫
      (targetRestriction U).hom.app E =
        (slicePresentation U).unit ((ringedDerivedRestriction O U).obj E)
  restriction_square : ∀ U : C,
    Functor.whiskerRight theta.hom (ringedDerivedRestriction O U) ≫
        (targetRestriction U).hom =
      (sourceRestriction U).hom ≫
        Functor.whiskerLeft (ringedDerivedRestriction O U) (sliceTheta U).hom
  target_unique : ∀ (U : C)
      (beta : presentation.completion ⋙ ringedDerivedRestriction O U ≅
        ringedDerivedRestriction O U ⋙ (slicePresentation U).completion),
    (∀ E, (ringedDerivedRestriction O U).map (presentation.unit E) ≫ beta.hom.app E =
      (slicePresentation U).unit ((ringedDerivedRestriction O U).obj E)) →
        beta = targetRestriction U
  target_coherence : ∀ (U V : C)
      (F : ringedSiteDerived (O.over U) ⥤ ringedSiteDerived (O.over V))
      (rho : ringedDerivedRestriction O U ⋙ F ≅ ringedDerivedRestriction O V)
      (gamma : (slicePresentation U).completion ⋙ F ≅ F ⋙ (slicePresentation V).completion),
    (∀ E, F.map ((slicePresentation U).unit E) ≫ gamma.hom.app E =
      (slicePresentation V).unit (F.obj E)) →
    Functor.whiskerRight (targetRestriction U).hom F ≫
        Functor.whiskerLeft (ringedDerivedRestriction O U) gamma.hom ≫
        Functor.whiskerRight rho.hom (slicePresentation V).completion =
      Functor.whiskerLeft presentation.completion rho.hom ≫ (targetRestriction V).hom
  furtherTarget : ∀ (U V : C) (f : V ⟶ U),
    (slicePresentation U).completion ⋙ ringedKoszulDerivedOverMap O f ≅
      ringedKoszulDerivedOverMap O f ⋙ (slicePresentation V).completion
  further_unit : ∀ (U V : C) (f : V ⟶ U) E,
    (ringedKoszulDerivedOverMap O f).map ((slicePresentation U).unit E) ≫
        (furtherTarget U V f).hom.app E =
      (slicePresentation V).unit ((ringedKoszulDerivedOverMap O f).obj E)
  further_coherence : ∀ (U V : C) (f : V ⟶ U),
    Functor.whiskerRight (targetRestriction U).hom (ringedKoszulDerivedOverMap O f) ≫
        Functor.whiskerLeft (ringedDerivedRestriction O U) (furtherTarget U V f).hom ≫
        Functor.whiskerRight (ringedKoszulDerivedOverComparison O f).hom
          (slicePresentation V).completion =
      Functor.whiskerLeft presentation.completion (ringedKoszulDerivedOverComparison O f).hom ≫
        (targetRestriction V).hom
  empty_identity : r = 0 → ∀ E, IsIso (presentation.unit E)

private theorem normalizedRestriction_injective
    {A B : Type*} [Category A] [Category B]
    (L : A ⥤ A) (R : A ⥤ B) (M : B ⥤ B)
    (eta : ∀ E, E ⟶ L.obj E) (mu : ∀ E, E ⟶ M.obj E)
    (h : ∀ E X, Function.Injective
      (fun f : M.obj E ⟶ M.obj X ↦ mu E ≫ f))
    (beta : L ⋙ R ≅ R ⋙ M)
    (hnorm : ∀ E, R.map (eta E) ≫ beta.hom.app E = mu (R.obj E))
    (E : A) (X : B) : Function.Injective
      (fun f : R.obj (L.obj E) ⟶ M.obj X ↦ R.map (eta E) ≫ f) := by
  intro f g hfg
  apply (cancel_epi (beta.inv.app E)).1
  apply h (R.obj E) X
  have hm : mu (R.obj E) ≫ beta.inv.app E = R.map (eta E) := by
    rw [← hnorm E]
    simp only [Category.assoc, Iso.hom_inv_id_app]
    exact Category.comp_id _
  simpa only [← Category.assoc, hm] using hfg

private theorem normalizedRestriction_coherence
    {A B D : Type*} [Category A] [Category B] [Category D]
    (L : A ⥤ A) (M : B ⥤ B) (N : D ⥤ D)
    (R : A ⥤ B) (S : A ⥤ D) (F : B ⥤ D) (rho : R ⋙ F ≅ S)
    (eta : ∀ E, E ⟶ L.obj E) (mu : ∀ E, E ⟶ M.obj E)
    (nu : ∀ E, E ⟶ N.obj E)
    (hnat : ∀ E E' (f : E ⟶ E'), nu E ≫ N.map f = f ≫ nu E')
    (beta : L ⋙ R ≅ R ⋙ M) (delta : L ⋙ S ≅ S ⋙ N)
    (hb : ∀ E, R.map (eta E) ≫ beta.hom.app E = mu (R.obj E))
    (hd : ∀ E, S.map (eta E) ≫ delta.hom.app E = nu (S.obj E))
    (hi : ∀ E X, Function.Injective
      (fun f : S.obj (L.obj E) ⟶ N.obj X ↦ S.map (eta E) ≫ f))
    (gamma : M ⋙ F ≅ F ⋙ N)
    (hg : ∀ E, F.map (mu E) ≫ gamma.hom.app E = nu (F.obj E)) :
    Functor.whiskerRight beta.hom F ≫ Functor.whiskerLeft R gamma.hom ≫
        Functor.whiskerRight rho.hom N =
      Functor.whiskerLeft L rho.hom ≫ delta.hom := by
  apply NatTrans.ext
  funext E
  change F.map (beta.hom.app E) ≫ gamma.hom.app (R.obj E) ≫
      N.map (rho.hom.app E) = rho.hom.app (L.obj E) ≫ delta.hom.app E
  apply (cancel_epi (rho.inv.app (L.obj E))).1
  apply hi E (S.obj E)
  have hr : S.map (eta E) ≫ rho.inv.app (L.obj E) =
      rho.inv.app E ≫ F.map (R.map (eta E)) := rho.inv.naturality (eta E)
  calc
    S.map (eta E) ≫ rho.inv.app (L.obj E) ≫
        F.map (beta.hom.app E) ≫ gamma.hom.app (R.obj E) ≫ N.map (rho.hom.app E) =
        rho.inv.app E ≫ F.map (mu (R.obj E)) ≫
          gamma.hom.app (R.obj E) ≫ N.map (rho.hom.app E) := by
      rw [← Category.assoc, hr]
      simp only [Category.assoc]
      rw [← Category.assoc (F.map _) (F.map _), ← F.map_comp, hb]
    _ = rho.inv.app E ≫ nu (F.obj (R.obj E)) ≫ N.map (rho.hom.app E) := by
      rw [← Category.assoc (F.map _) _, hg]
    _ = nu (S.obj E) := by
      calc
        _ = rho.inv.app E ≫ (rho.hom.app E ≫ nu (S.obj E)) := by
          exact congrArg (fun f ↦ rho.inv.app E ≫ f) (hnat _ _ (rho.hom.app E))
        _ = _ := by simp
    _ = S.map (eta E) ≫ rho.inv.app (L.obj E) ≫
        rho.hom.app (L.obj E) ≫ delta.hom.app E := by
      simpa only [← Category.assoc, Iso.inv_hom_id_app, Category.comp_id] using (hd E).symm

private theorem normalizedTransport_unit
    {A B : Type*} [Category A] [Category B]
    (L M : A ⥤ A) (L' M' : B ⥤ B) (R : A ⥤ B)
    (eta : ∀ E, E ⟶ L.obj E) (mu : ∀ E, E ⟶ M.obj E)
    (eta' : ∀ E, E ⟶ L'.obj E) (mu' : ∀ E, E ⟶ M'.obj E)
    (theta : L ≅ M) (theta' : L' ≅ M')
    (ht : ∀ E, eta E ≫ theta.hom.app E = mu E)
    (ht' : ∀ E, eta' E ≫ theta'.hom.app E = mu' E)
    (sigma : L ⋙ R ≅ R ⋙ L')
    (hs : ∀ E, R.map (eta E) ≫ sigma.hom.app E = eta' (R.obj E)) :
    ∀ E, R.map (mu E) ≫
      (Functor.isoWhiskerRight theta.symm R ≪≫ sigma ≪≫ Functor.isoWhiskerLeft R theta').hom.app E =
        mu' (R.obj E) := by
  intro E
  have hi : mu E ≫ theta.inv.app E = eta E := by
    rw [← ht E, Category.assoc, Iso.hom_inv_id_app]
    exact Category.comp_id _
  change R.map (mu E) ≫ (R.map (theta.inv.app E) ≫
    (sigma.hom.app E ≫ theta'.hom.app (R.obj E))) = mu' (R.obj E)
  rw [← Category.assoc, ← R.map_comp, hi, ← Category.assoc, hs, ht']

private theorem normalizedModel_unique
    {A : Type*} [Category A] (L M : A ⥤ A)
    (eta : ∀ E, E ⟶ L.obj E) (mu : ∀ E, E ⟶ M.obj E)
    (theta : L ≅ M) (ht : ∀ E, eta E ≫ theta.hom.app E = mu E)
    (hi : ∀ E X, Function.Injective (fun f : M.obj E ⟶ M.obj X ↦ mu E ≫ f))
    (theta' : L ≅ M) (ht' : ∀ E, eta E ≫ theta'.hom.app E = mu E) : theta' = theta := by
  apply Iso.ext
  apply NatTrans.ext
  funext E
  apply (cancel_epi (theta.inv.app E)).1
  apply hi E E
  have h : mu E ≫ theta.inv.app E = eta E := by
    rw [← ht E, Category.assoc, Iso.hom_inv_id_app]
    exact Category.comp_id _
  simpa only [← Category.assoc, h] using (ht' E).trans (ht E).symm

/-- The augmented extended Cech complex is the filtered colimit and homotopy colimit of
its finite positive Koszul system; internal Hom from it is canonically the strict total
derived inverse limit of tensor with its finite duals. The supplied normalized comparison
is natural on the derived category, compatible with every representative and slice, and
is identity for the empty sequence under the constant-tower and unit identifications.

Source: Stacks Project, More on Algebra, Tag 0913; Cohomology on Sites, Tags 0A0A, 0941,
08JB; Derived Categories, Tag 0949
(blueprint: lem-weil-pbc-ringed-cech-koszul-dual-limit).

Proof:
1. Expand the positive factors in degrees zero and one. In degree q the summands are
   indexed by q-element subsets I, with differential given by insertion of j with sign
   (-1)^(number of earlier indices) times b_j^(m+1). The transition on I multiplies by
   the product t_I. Dualizing gives factors in degrees minus one and zero and maps (b_j,1).
   Evaluation identifies Hom(P_m,N) with the finite total tensor N tensor Q_m, naturally
   in both variables; the Hom differential gives the total-tensor sign.
2. Send the I-coordinate a at level m to a/t_I^(m+1), then sheafify. The fraction equivalence
   relation is precisely eventual equality in the diagram. This identifies the differential
   with alternating localization and the degree-zero projection with the augmentation.
3. Apply lem-pc-complex-hocolim-colimit to the canonical telescope map, and compose with
   the colimit isomorphism. Hom from this quasi-isomorphism into a functorial K-injective
   replacement I computes derived internal Hom (def-pur-derived-internal-hom).
4. Hom from the telescope is the fibre of 1-shift on the product of Hom(P_m,I).
   The finite split-perfect tensor theorem lem-weil-pbc-split-perfect-tensor-kinjective
   makes those complexes K-injective, and lem-pc-ringed-space-product-kinjective computes
   the derived product without exactness of products of sheaves. The ordinary Hom-cone
   sign identification gives the Roos fibre, with the degree-zero family sent to (0,(x)_m).
5. Apply lem-weil-pbc-ringed-strict-tower-homotopy-limit. Resolve the strict tower by a
   K-injective tower with injective terms; its evaluations are K-injective. Comparison
   gives homotopy equivalences at each level and hence on their products. On injective
   towers the transitions split, so 1-shift is sectionwise surjective with inverse-limit
   kernel. The inverse limit is therefore quasi-isomorphic to the Roos fibre.
6. Each finite dual is K-flat by its finite filtration with finite free graded pieces.
   Thus replacing N by I gives a levelwise quasi-isomorphism of actual strict tensor
   towers. Localization and total right derived inverse limit give the asserted natural
   comparison on the derived category, including its representative independence.
7. The compatible positive projections dualize to the actual degree-zero units of the
   strict tensor tower. In the fibre they send x to (0,(x)_m), agreeing with the map obtained
   from the compatible maps into the K-injective tower resolution and its ordinary limit.
   Unit normalization uniquely specifies the natural comparison: both functors are the
   derived-completion reflector, so precomposition with its unit determines every map
   into a complete object. This also proves uniqueness of normalized restriction maps.
8. Restriction is exact and preserves K-injectives, products, finite totalizations and
   cones (lem-pur-site-restriction-module-adjunction-exact and
   lem-pur-kinjective-restrict-localized). Hence it restricts the actual Roos calculation
   to that on the slice. All maps agree after further restriction; alternatively use
   uniqueness of the normalized comparisons to obtain their composition coherence.
9. For the empty list the positive diagram is constant O[0], the dual is canonically
   O[0] by evaluation at one, and 1-shift on the product of I is split surjective by the
   recursion x_0=0, x_(m+1)=x_m-y_m. Its kernel is the diagonal I. The strict unit is thus
   an isomorphism, and the normalized comparison is identity under these identifications. -/
theorem ringed_cech_koszul_dual_limit :
    (∃ alpha : colimit (ringedKoszulDiagram O r b) ≅ (ringedExtendedCech O r b).1,
      alpha.hom ≫ (ringedExtendedCech O r b).2 =
        colimit.desc _ (ringedKoszulAugmentationCocone O r b) ∧
      ∃ t : CochainComplex.mappingCone
          (CochainComplex.telescopeShiftColimit O (ringedKoszulDiagram O r b)) ⟶
            (ringedExtendedCech O r b).1,
        CochainComplex.mappingCone.inr _ ≫ t =
          CochainComplex.telescopeToColimit O (ringedKoszulDiagram O r b) ≫ alpha.hom ∧
        QuasiIso t) ∧
    (∀ m : ℕ, CochainComplex.IsAcyclicTensorKFlat ((ringedKoszulDualTower O r b).obj (op m))) ∧
    Nonempty (RingedKoszulCechComparison O r b) := by
  classical
  obtain ⟨alpha, halpha⟩ := ringedKoszul_colimit_cech O r b
  obtain ⟨t, ht, _, hqt⟩ :=
    CochainComplex.quasiIso_telescopeColimit O (ringedKoszulDiagram O r b)
  have hflat (m : ℕ) :
      CochainComplex.IsAcyclicTensorKFlat ((ringedKoszulDualTower O r b).obj (op m)) := by
    obtain ⟨hb, hf⟩ := ringedKoszulDual_flat_terms O r b m
    exact CochainComplex.isKFlat_of_boundedAbove_flat _ ⟨0, hb⟩ hf
  refine ⟨⟨alpha, halpha, t ≫ alpha.hom, ?_, ?_⟩, hflat, ?_⟩
  · rw [← Category.assoc, ht]
  · have : QuasiIso t := hqt
    infer_instance
  obtain ⟨D, theta, htheta, hfaith, hnat, hempty⟩ := ringedKoszul_cech_local_model O r b
  choose Ds thetas hthetas hfaiths hnats hemptys using
    (fun U : C ↦ ringedKoszul_cech_local_model (O.over U) r
      (fun i ↦ ringedKoszulSliceSection O (b i) U))
  obtain ⟨sigma, tau, hsigma, htau⟩ := ringedCech_normalized_restriction O r b
  let beta (U : C) : D.completion ⋙ ringedDerivedRestriction O U ≅
      ringedDerivedRestriction O U ⋙ (Ds U).completion :=
    Functor.isoWhiskerRight theta.symm (ringedDerivedRestriction O U) ≪≫ sigma U ≪≫
      Functor.isoWhiskerLeft (ringedDerivedRestriction O U) (thetas U)
  have hbeta (U : C) : ∀ E,
      (ringedDerivedRestriction O U).map (D.unit E) ≫ (beta U).hom.app E =
        (Ds U).unit ((ringedDerivedRestriction O U).obj E) :=
    normalizedTransport_unit _ _ _ _ _ _ _ _ _ theta (thetas U)
      htheta (hthetas U) (sigma U) (hsigma U)
  let gamma (U V : C) (f : V ⟶ U) :
      (Ds U).completion ⋙ ringedKoszulDerivedOverMap O f ≅
        ringedKoszulDerivedOverMap O f ⋙ (Ds V).completion :=
    Functor.isoWhiskerRight (thetas U).symm (ringedKoszulDerivedOverMap O f) ≪≫ tau U V f ≪≫
      Functor.isoWhiskerLeft (ringedKoszulDerivedOverMap O f) (thetas V)
  have hgamma (U V : C) (f : V ⟶ U) : ∀ E,
      (ringedKoszulDerivedOverMap O f).map ((Ds U).unit E) ≫
          (gamma U V f).hom.app E = (Ds V).unit ((ringedKoszulDerivedOverMap O f).obj E) :=
    normalizedTransport_unit _ _ _ _ _ _ _ _ _ (thetas U) (thetas V)
      (hthetas U) (hthetas V) (tau U V f) (htau U V f)
  have hinj (U : C) := normalizedRestriction_injective _ _ _ D.unit (Ds U).unit
    (hfaiths U) (beta U) (hbeta U)
  have hcoherence := fun U V F rho gamma' hgamma' ↦
    normalizedRestriction_coherence D.completion (Ds U).completion (Ds V).completion
      (ringedDerivedRestriction O U) (ringedDerivedRestriction O V) F rho D.unit
      (Ds U).unit (Ds V).unit (hnats V) (beta U) (beta V) (hbeta U) (hbeta V)
      (hinj V) gamma' hgamma'
  refine ⟨{
    presentation := D
    theta := theta
    unit := htheta
    theta_unique := normalizedModel_unique _ _ _ _ theta htheta hfaith
    slicePresentation := Ds
    sliceTheta := thetas
    slice_unit := hthetas
    sourceRestriction := sigma
    targetRestriction := beta
    source_unit := hsigma
    target_unit := hbeta
    restriction_square := ?_
    target_unique := ?_
    target_coherence := hcoherence
    furtherTarget := gamma
    further_unit := hgamma
    further_coherence := ?_
    empty_identity := hempty }⟩
  · intro U
    apply NatTrans.ext
    funext E
    change (ringedDerivedRestriction O U).map (theta.hom.app E) ≫
        ((ringedDerivedRestriction O U).map (theta.inv.app E) ≫
          ((sigma U).hom.app E ≫ (thetas U).hom.app _)) = _
    rw [← Category.assoc, ← Functor.map_comp]
    simp
  · intro U beta' hb'
    apply Iso.ext
    apply NatTrans.ext
    funext E
    apply hinj U E ((ringedDerivedRestriction O U).obj E)
    exact (hb' E).trans (hbeta U E).symm
  · intro U V f
    exact hcoherence U V _ (ringedKoszulDerivedOverComparison O f) (gamma U V f)
      (hgamma U V f)

end CategoryTheory
