/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q139
-/
module


public import Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeData
import Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeTensor
import Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeHom
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
/-! # Finite free scalar extension and derived internal Hom

Source: Stacks Project, sites-cohomology.tex, Tag 08J9, lemma-internal-hom,
and Tag 08JA, lemma-section-RHom-over-U; finite-free evaluation specialization
(blueprint: lem-sf-ringed-finite-free-hom-base-change).
The tensor comparisons are fixed on sheafified pure tensors. The comparison
of internal Homs is their evaluation transpose, not an unspecified isomorphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace CategoryTheory

section Site
variable {C : Type c} [Category.{v} C]
  (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S)

set_option maxHeartbeats 800000 in
-- Elaborating both closed tensor models and the large dependent witness takes extra heartbeats.
/-- Finite free change of ring sheaves commutes with derived internal Hom,
with its canonical evaluation normalization and naturality in both variables.
The existential data present ordinary scalar extension, its universal derived
functor, and the existing normalized closed tensor models. They impose no
additional mathematical hypothesis on the site, rings, or derived inputs.
The chain tensor comparison and its derived comparison are normalized below;
the displayed natural isomorphism is exactly the transpose of extended evaluation.
The tensor order here is Hom tensor P, the convention of CoefficientClosedStructure;
Koszul symmetry identifies it with P tensor Hom in the node's displayed pairing.

Source: Stacks Project, Tag 08J9, lemma-internal-hom; Tag 08JA,
lemma-section-RHom-over-U, finite-free specialization
(blueprint: lem-sf-ringed-finite-free-hom-base-change).

Proof:
1. Choose the ordinary scalar-extension functor with exactly changeOfRings objects
   and maps. Apply lem-pur-derived-change-of-rings to obtain its universal left
   derived pair; passing between Q and the homotopy localization gives ε here.
   K-flat resolutions make ε invertible on K-flat complexes. Use the recorded
   tensor-Hom adjunction and rhom-global-sections to obtain the normalized closed
   tensor models on R and S. Scalar extension preserves K-flat complexes.
2. On ordinary total tensors send s tensor (x tensor y) to
   (s tensor x) tensor (1 tensor y). The inverse sends
   (s tensor x) tensor (t tensor y) to st tensor (x tensor y).
   Balanced relations and sheafification give mutually inverse chain maps;
   the signed total differential commutes with them. Localize this natural
   comparison on pairs of K-flats to obtain μ with the displayed ε square.
3. Apply lem-sfb-dc-hom-scalar-adjunction for the normalized scalar-Hom
   adjunction and conservativity of restriction. Choose a free basis S = R^d.
   Restriction U gives natural isomorphisms
   X^d = U(T X), computed by a K-flat resolution and degreewise finite sums.
   The derived scalar adjunction identifies U H_S(T P,T Q) with H_R(P,U T Q).
   Its transpose is restricted S-evaluation after the scalar unit on P.
   Restriction is conservative, since it preserves underlying cohomology sheaves.
4. The tensor-Hom right adjoint preserves finite products, which are finite sums.
   Thus H_R(P,Q^d) = H_R(P,Q)^d. Under the preceding identifications the restricted
   evaluation transpose has matrix entries δ_ij times the identity: insertion
   of the scalar unit followed by the j-th basis coefficient multiplies 1 by e_j.
   Uniqueness of transpose gives these entries, proving the map invertible.
5. For d = 0 all these are empty biproducts and the same matrix argument applies.
   Naturality of evaluation, μ and transposition gives contravariant naturality
   in P and covariant naturality in Q. Its basis-free defining transpose proves
   independence of the basis. No bound or perfectness of either input was used. -/
theorem ringedFiniteFreeHomBaseChange
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S))]
    (hfree : ∃ d : ℕ, Nonempty
      ((SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map φ)).obj
          (SheafOfModules.unit
            (SheafOfModules.derivedChangeRingIndependentCoefficients J S)) ≅
        SheafOfModules.free (R :=
          SheafOfModules.derivedChangeRingIndependentCoefficients J R)
            (ULift.{max c v r} (Fin d)))) :
    ∃ (E : SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R) ⥤ SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S))
      (h : ∀ M, E.obj M = SheafOfModules.changeOfRings φ M)
      (_hm : ∀ {M N : SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)} (f : M ⟶ N),
        E.map f = eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom φ M f ≫
          eqToHom (h N).symm)
      (_hE : E.Additive)
      (T : DerivedCategory (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ⥤
        DerivedCategory (SheafOfModules.{max c v r}
          (SheafOfModules.derivedChangeRingIndependentCoefficients J S)))
      (ε : DerivedCategory.Q ⋙ T ⟶
        E.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (_hT : T.IsLeftDerivedFunctor ε
        (HomologicalComplex.quasiIso (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) (ComplexShape.up ℤ)))
      (AR : WeilConjectures.CoefficientClosedStructure
        (derivedInternalHomOfUniverses.{c, v, r, w} J R))
      (AS : WeilConjectures.CoefficientClosedStructure
        (derivedInternalHomOfUniverses.{c, v, r, w} J S))
      (MR : WeilConjectures.CoefficientTensorModels.{r, c, v, w} J R AR)
      (MS : WeilConjectures.CoefficientTensorModels.{r, c, v, w} J S AS)
      (κ : WeilConjectures.coefficientTotalTensor.{r, c, v} J R ⋙
          E.mapHomologicalComplex (ComplexShape.up ℤ) ≅
        (E.mapHomologicalComplex (ComplexShape.up ℤ)).prod
          (E.mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
            WeilConjectures.coefficientTotalTensor.{r, c, v} J S)
      (μ : AR.tensor ⋙ T ≅ T.prod T ⋙ AS.tensor)
      (α : derivedInternalHomOfUniverses.{c, v, r, w} J R ⋙ T ≅
        T.op.prod T ⋙ derivedInternalHomOfUniverses.{c, v, r, w} J S),
      (∀ (P Q : CochainComplex (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
        (p q : ℤ) (U : Cᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        ((κ.hom.app (P, Q)).f (p + q)).val.app U
          (ringedFiniteFreeScalarSection.{c, v, r} J φ E h
            (((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)).X (p + q))
            U 1 (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R
              P Q p q (p + q) rfl U x y)) =
        WeilConjectures.coefficientTensorGenerator.{r, c, v} J S
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) p q (p + q) rfl U
          (ringedFiniteFreeScalarSection.{c, v, r} J φ E h (P.X p) U 1 x)
          (ringedFiniteFreeScalarSection.{c, v, r} J φ E h (Q.X q) U 1 y)) ∧
      (∀ (P Q : CochainComplex (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
        (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
        (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q),
        ∃ (hEP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
            ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
          (hEQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
            ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)),
          IsIso (ε.app P) ∧ IsIso (ε.app Q) ∧
          T.map ((MR.iso J R AR P Q hP hQ).hom) ≫
              μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
              AS.tensor.map (Prod.mkHom (ε.app P) (ε.app Q)) =
            ε.app ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≫
              DerivedCategory.Q.map (κ.hom.app (P, Q)) ≫
              (MS.iso J S AS _ _ hEP hEQ).hom) ∧
      (∀ P Q : DerivedCategory (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)),
        α.hom.app (op P, Q) = AS.transpose _ (T.obj P) (T.obj Q)
          (μ.inv.app ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op P, Q), P) ≫
            T.map (AR.evaluation P Q)))  := by
  obtain ⟨D⟩ := SheafOfModules.nonempty_derivedChangeOfRingsCochainModel.{c, v, max c v r, w, w} φ
  obtain ⟨AR, MR, _, _⟩ := ringedDerived_closed_symmetric_monoidal.{c, v, r, w} J R
  obtain ⟨AS, MS, _, _⟩ := ringedDerived_closed_symmetric_monoidal.{c, v, r, w} J S
  obtain ⟨κ, μ, hκ, hcomp⟩ :=
    ringedFiniteFreeHomBaseChange_tensor.{c, v, r, w} J φ D AR AS MR MS
  have hcomp' : ∀ (P Q : CochainComplex (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
        (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
        (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q),
        ∃ (hEP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
            ((D.E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
          (hEQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
            ((D.E.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)),
          IsIso (D.ε.app P) ∧ IsIso (D.ε.app Q) ∧
          D.T.map ((MR.iso J R AR P Q hP hQ).hom) ≫
              μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
              AS.tensor.map (Prod.mkHom (D.ε.app P) (D.ε.app Q)) =
            D.ε.app ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≫
              DerivedCategory.Q.map (κ.hom.app (P, Q)) ≫
              (MS.iso J S AS _ _ hEP hEQ).hom := by
    intro P Q hP hQ
    obtain ⟨hEP, hEQ, hsq⟩ := hcomp P Q hP hQ
    exact Exists.intro hEP (Exists.intro hEQ
      (And.intro (D.computes P hP) (And.intro (D.computes Q hQ) hsq)))
  obtain ⟨α, hα⟩ := ringedFiniteFreeHomBaseChange_hom.{c, v, r, w} J φ hfree
      D.E D.obj_eq D.map_eq D.additive D.T D.ε D.universal AR AS MR MS κ μ hκ hcomp'
  exact ⟨D.E, D.obj_eq, D.map_eq, D.additive, D.T, D.ε, D.universal,
    AR, AS, MR, MS, κ, μ, α, hκ, hcomp', hα⟩

end Site
end CategoryTheory
