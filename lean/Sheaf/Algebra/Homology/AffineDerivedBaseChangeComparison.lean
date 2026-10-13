/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups C1 and Q3
-/
module

public import Sheaf.Algebra.Homology.RingTensorCohomology
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
import all Sheaf.Algebra.Homology.KFlatScalarExtensionDerivedIso
import Sheaf.Algebra.Homology.BaseTensorOrdinaryIso

/-!
# Affine derived base change and localization

Source: Stacks Project, More on Algebra, equation comparison-map, and
`perfect.tex`, Tag 0DJ8, affine proof
(blueprint: lem-pc-affine-derived-base-change-comparison-map).

We use the functorial K-flat models of `RingTensorCohomology`. The comparison in the
derived category is specified by its K-flat span. Lifts of the cohomology functors to
modules over the tensor algebra specify the scalar actions explicitly. All localization
isomorphisms are natural transformations of functors on unbounded complexes.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace RingTensorCohomology

private theorem augmentation_quasiIso (R : Type u) [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) : QuasiIso ((augmentation R).app K) := by
  dsimp [augmentation]
  infer_instance

private theorem resolution_kFlat (R : Type u) [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat
      ((resolution R).obj K) := by
  exact (flatResolution R).kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le K

private theorem resolution_quasiIso_map (R : Type u) [CommRing R]
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) (hf : QuasiIso f) :
    QuasiIso ((resolution R).map f) := by
  have := augmentation_quasiIso R K
  have := augmentation_quasiIso R L
  have : QuasiIso (((augmentation R).app K) ≫ f) := inferInstance
  have : QuasiIso ((resolution R).map f ≫ (augmentation R).app L) := by
    rw [(augmentation R).naturality f]
    change QuasiIso ((augmentation R).app K ≫ f)
    infer_instance
  exact (quasiIso_iff_comp_right ((resolution R).map f) ((augmentation R).app L)).1 this

open scoped ChangeOfRings in
private theorem restrictedExtension_quasiIso_of_kFlat
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    {P Q : CochainComplex (ModuleCat.{u} A) ℤ} (a : P ⟶ Q)
    (ha : QuasiIso a)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat P)
    (hQ : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat Q) :
    QuasiIso ((extend R B).map ((restrict R A).map a)) := by
  have : (ModuleCat.extendScalars (algebraMap R B)).Additive :=
    (ModuleCat.extendRestrictScalarsAdj _).left_adjoint_additive
  have : (ModuleCat.extendScalars (algebraMap A (A ⊗[R] B))).Additive :=
    (ModuleCat.extendRestrictScalarsAdj _).left_adjoint_additive
  obtain ⟨eP, heP⟩ := ModuleCat.exists_baseTensorOrdinaryIso R A B P
  obtain ⟨eQ, heQ⟩ := ModuleCat.exists_baseTensorOrdinaryIso R A B Q
  let F := (ModuleCat.extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex (.up ℤ)
  let G := (ModuleCat.restrictScalars
    (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).mapHomologicalComplex
      (.up ℤ)
  have : QuasiIso (F.map a) :=
    CochainComplex.scalarExtension_quasiIso_of_kFlat _ a ha hP hQ
  have : QuasiIso (G.map (F.map a)) := inferInstance
  apply (quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk eP eQ ?_)).2 this
  apply HomologicalComplex.Hom.ext
  funext j
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b x =>
    change (G.map (F.map a)).f j (eP.hom.f j (b ⊗ₜ[R, algebraMap R B] x)) =
      eQ.hom.f j (b ⊗ₜ[R, algebraMap R B] (a.f j x))
    rw [heP, heQ]
    rfl
  | add x y hx hy => simp only [_root_.map_add] at hx hy ⊢; rw [hx, hy]

/-- Stacks, equation comparison-map and Tag 0DJ8, affine proof.
(blueprint: lem-pc-affine-derived-base-change-comparison-map)

The K-flat comparison span becomes a unique morphism in the derived category.
Its cohomology is the previously defined comparison. The last clause gives its value
on every pair of K-flat models P -> M and E -> P. The equations fixing `es,et` use the
resolution augmentations, so these are the canonical model identifications, not arbitrary
isomorphisms. No Tor independence is assumed.

Proof:
1. The existing spanLeft_isIso says that every cohomology map of the left span
   arrow is invertible. Hence the arrow is a quasi-isomorphism and becomes an
   isomorphism under Q. Define c by its inverse followed by the right span arrow.
2. Naturality of homologyFunctorFactors identifies H(c) with comparison. Cancel
   the left span arrow to prove uniqueness.
3. Apply the existing CochainComplex.scalarExtension_quasiIso_of_kFlat theorem
   from KFlatScalarExtensionDerivedIso to preserve quasi-isomorphisms between
   K-flat complexes under ordinary scalar extension.
   exists_baseTensorOrdinaryIso identifies extension of restricted A-complexes
   with extension to A tensor_R B followed by restriction to B; its pure-tensor
   formula proves naturality. Thus this functor also preserves quasi-isomorphisms
   between A-K-flat complexes.
4. For p and e, the source identification is the inverse of Q(extend(augmentation E))
   followed by Q(extend(resolution(e followed by restrict(p)))). The target
   identification is the inverse of Q(extend(restrict(augmentation P))) followed
   by Q(targetComplex(p)). These are isomorphisms by Step 3. Naturality of the
   augmentations gives c(P) followed by the target augmentation equal to the
   R-augmentation of restrict(P), and its naturality at e gives the model equation
   after cancellation. Naturality of c at p gives the asserted value at M. -/
theorem exists_affineDerivedBaseChangeComparison
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [HasDerivedCategory.{w} (ModuleCat.{u} B)] :
    IsIso (Functor.whiskerRight (spanLeft R A B) DerivedCategory.Q) ∧
    ∃! c : sourceComplex R A B ⋙ DerivedCategory.Q ⟶
        targetComplex R A B ⋙ DerivedCategory.Q,
      Functor.whiskerRight (spanLeft R A B) DerivedCategory.Q ≫ c =
        Functor.whiskerRight (spanRight R A B) DerivedCategory.Q ∧
      (∀ i : ℤ,
        Functor.whiskerRight c (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i) ≫
          (Functor.isoWhiskerLeft (targetComplex R A B)
            (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B) i)).hom =
        (Functor.isoWhiskerLeft (sourceComplex R A B)
          (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B) i)).hom ≫
          comparison R A B i) ∧
      ∀ (M P : CochainComplex (ModuleCat.{u} A) ℤ)
        (E : CochainComplex (ModuleCat.{u} R) ℤ)
        (p : P ⟶ M) (e : E ⟶ (restrict R A).obj P),
        QuasiIso p → QuasiIso e →
        (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat P →
        (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat E →
        ∃ (es : DerivedCategory.Q.obj ((extend R B).obj E) ≅
            DerivedCategory.Q.obj ((sourceComplex R A B).obj M))
          (et : DerivedCategory.Q.obj ((extend R B).obj ((restrict R A).obj P)) ≅
            DerivedCategory.Q.obj ((targetComplex R A B).obj M)),
          DerivedCategory.Q.map ((extend R B).map ((augmentation R).app E)) ≫ es.hom =
            DerivedCategory.Q.map ((extend R B).map ((resolution R).map
              (e ≫ (restrict R A).map p))) ∧
          DerivedCategory.Q.map ((extend R B).map
              ((restrict R A).map ((augmentation A).app P))) ≫ et.hom =
            DerivedCategory.Q.map ((targetComplex R A B).map p) ∧
          es.hom ≫ c.app M = DerivedCategory.Q.map ((extend R B).map e) ≫ et.hom := by
  have hleft : IsIso (Functor.whiskerRight (spanLeft R A B) DerivedCategory.Q) := by
    have (M : CochainComplex (ModuleCat.{u} A) ℤ) :
        IsIso ((Functor.whiskerRight (spanLeft R A B) DerivedCategory.Q).app M) := by
      apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
      rw [quasiIso_iff]
      intro i
      rw [quasiIsoAt_iff_isIso_homologyMap]
      have := spanLeft_isIso R A B i
      exact inferInstanceAs (IsIso
        ((Functor.whiskerRight (spanLeft R A B)
          (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) i)).app M))
    exact NatIso.isIso_of_isIso_app _
  let l := Functor.whiskerRight (spanLeft R A B) DerivedCategory.Q
  let r := Functor.whiskerRight (spanRight R A B) DerivedCategory.Q
  let c := inv l ≫ r
  refine ⟨hleft, c, ⟨?_, ?_, ?_⟩, ?_⟩
  · simp [c, r]
  · intro i
    have := spanLeft_isIso R A B i
    apply NatTrans.ext
    funext M
    apply (cancel_epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
      (l.app M))).1
    have hc : l.app M ≫ c.app M = r.app M := by simp [c]
    change _ ≫ ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
      (c.app M) ≫ _) = _ ≫ (_ ≫ (comparison R A B i).app M)
    rw [← Category.assoc, ← Functor.map_comp, hc]
    change (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
        (DerivedCategory.Q.map ((spanRight R A B).app M)) ≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B) i).hom.app
          ((targetComplex R A B).obj M) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
        (DerivedCategory.Q.map ((spanLeft R A B).app M)) ≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B) i).hom.app
          ((sourceComplex R A B).obj M) ≫ (comparison R A B i).app M
    rw [DerivedCategory.homologyFunctorFactors_hom_naturality,
      DerivedCategory.homologyFunctorFactors_hom_naturality_assoc]
    simp [comparison, NatTrans.comp_app]
  · intro M P E p e hp he hP hE
    let X := extend R B ⋙ DerivedCategory.Q
    let Y := restrict R A ⋙ X
    let Z := resolution R ⋙ X
    let G := targetComplex R A B ⋙ DerivedCategory.Q
    have haugE := augmentation_quasiIso R E
    have haugP := augmentation_quasiIso A P
    have hextE := CochainComplex.scalarExtension_quasiIso_of_kFlat (algebraMap R B)
      ((augmentation R).app E) haugE (resolution_kFlat R E) hE
    have hextP := restrictedExtension_quasiIso_of_kFlat R A B
      ((augmentation A).app P) haugP (resolution_kFlat A P) hP
    have hpR : QuasiIso ((restrict R A).map p) := inferInstance
    have hep : QuasiIso (e ≫ (restrict R A).map p) := inferInstance
    have hres := resolution_quasiIso_map R (e ≫ (restrict R A).map p) hep
    have hextRes := CochainComplex.scalarExtension_quasiIso_of_kFlat (algebraMap R B)
      ((resolution R).map (e ≫ (restrict R A).map p)) hres
      (resolution_kFlat R E) (resolution_kFlat R ((restrict R A).obj M))
    have hpA := resolution_quasiIso_map A p hp
    have hextG := restrictedExtension_quasiIso_of_kFlat R A B ((resolution A).map p)
      hpA (resolution_kFlat A P) (resolution_kFlat A M)
    have : IsIso (X.map ((augmentation R).app E)) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hextE
    have : IsIso (Y.map ((augmentation A).app P)) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hextP
    have : IsIso (Z.map (e ≫ (restrict R A).map p)) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hextRes
    have : IsIso (G.map p) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hextG
    let es := (asIso (X.map ((augmentation R).app E))).symm ≪≫
      asIso (Z.map (e ≫ (restrict R A).map p))
    let et := (asIso (Y.map ((augmentation A).app P))).symm ≪≫ asIso (G.map p)
    refine ⟨es, et, ?_, ?_, ?_⟩
    · change X.map ((augmentation R).app E) ≫ es.hom = _
      simp [es, X, Z]
    · change Y.map ((augmentation A).app P) ≫ et.hom = _
      simp [et, Y, X, G]
    · have hcP : c.app P ≫ Y.map ((augmentation A).app P) =
          X.map ((augmentation R).app ((restrict R A).obj P)) := by
        apply (cancel_epi (l.app P)).1
        rw [← Category.assoc]
        have hspan : l.app P ≫ c.app P = r.app P := by simp [c]
        rw [hspan]
        change X.map ((augmentation R).app ((restrict R A).obj ((resolution A).obj P))) ≫
            X.map ((restrict R A).map ((augmentation A).app P)) =
          X.map ((resolution R).map ((restrict R A).map ((augmentation A).app P))) ≫
            X.map ((augmentation R).app ((restrict R A).obj P))
        rw [← X.map_comp, ← X.map_comp]
        exact congrArg X.map (by
          simpa only [Functor.id_map, Functor.id_obj] using
            ((augmentation R).naturality ((restrict R A).map ((augmentation A).app P))).symm)
      have haug : X.map ((augmentation R).app E) ≫ X.map e =
          Z.map e ≫ X.map ((augmentation R).app ((restrict R A).obj P)) := by
        simpa only [X, Z, Functor.comp_map, Functor.id_map, Functor.map_comp] using
          congrArg X.map ((augmentation R).naturality e).symm
      apply (cancel_epi (X.map ((augmentation R).app E))).1
      change X.map ((augmentation R).app E) ≫ (es.hom ≫ c.app M) =
        X.map ((augmentation R).app E) ≫ (X.map e ≫ et.hom)
      simp only [es, et, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
        Category.assoc, IsIso.hom_inv_id_assoc]
      rw [Functor.map_comp, ← Category.assoc]
      change (Z.map e ≫ (sourceComplex R A B ⋙ DerivedCategory.Q).map p) ≫ c.app M = _
      rw [Category.assoc, c.naturality]
      rw [← Category.assoc, ← Category.assoc, haug, ← hcP]
      simp only [Category.assoc, IsIso.hom_inv_id_assoc]
      rfl
  · intro c' hc'
    apply (cancel_epi l).1
    simpa [c] using hc'.1

/-- Stacks, Tag 0DJ8, affine proof, including the displayed localization identities.
(blueprint: lem-pc-affine-derived-base-change-comparison-map)

`S,T` are the two cohomology functors lifted to A tensor_R B modules, with
`eS,eT` identifying their restrictions with the existing B-module models. The two
scalar equations characterize both actions: a tensor 1 acts by multiplication on M,
and 1 tensor b acts by the existing B-action. The comparison `c` is tensor-algebra-linear
and restricts to the existing canonical comparison. The localized lifts `Sl,Tl` have
the same characterization. `alpha,beta` are the two natural D-linear localization
isomorphisms, and their square identifies the localized comparison with the local one.
The last isomorphism identifies the localized target with M_q tensor-derived_A_q D.

We quantify over models Rp,Aq,Bp,D of the four prime localizations. The scalar towers
and the two equations on `f` specify their canonical maps, rather than assuming
flatness or a base-change isomorphism. Left-sided tensors in extendScalars are the
right-sided tensors in the source by tensor symmetry.

Proof, following the DAG:
1. Choose K-flat A- and R-models as in exists_affineDerivedBaseChangeComparison;
   derived change of rings gives independence and naturality.
2. Multiplication on M induces the A-action on source cohomology. It commutes with B,
   and the two R-actions agree, so these give the A tensor_R B action. On the target
   this is the evident action on P tensor_A (A tensor_R B). Naturality of the comparison
   for multiplication by a makes it linear over the tensor algebra.
3. Apply lem-pc-derived-tensor-localization-cohomology to the source: localize its
   cohomology, not its R-K-flat complex. Localize P over A to Aq for the target;
   P_q is K-flat over Aq and represents M_q. The tensor-localization formula
   lem-weil-pbc-localization-tensor-product identifies its extension to D.
4. Exact localization (lem-weil-pbc-localization-module-exact) commutes with cohomology
   and gives beta and the final identification. All tensor identifications are natural;
   on K-flat models both paths in the square are the localized comparison map. -/
theorem exists_affineDerivedBaseChangeLocalization
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (i : ℤ) :
    ∃ (S T : CochainComplex (ModuleCat.{u} A) ℤ ⥤ ModuleCat.{u} (A ⊗[R] B))
      (eS : S ⋙ ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom ≅
        source R A B i)
      (eT : T ⋙ ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom ≅
        target R A B i)
      (c : S ⟶ T),
      (∀ (M : CochainComplex (ModuleCat.{u} A) ℤ) (a : A) (x : S.obj M),
        eS.hom.app M ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • x) =
          (source R A B i).map (a • 𝟙 M) (eS.hom.app M x)) ∧
      (∀ (M : CochainComplex (ModuleCat.{u} A) ℤ) (a : A) (x : T.obj M),
        eT.hom.app M ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • x) =
          (target R A B i).map (a • 𝟙 M) (eT.hom.app M x)) ∧
      Functor.whiskerRight c
          (ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom) ≫ eT.hom =
        eS.hom ≫ comparison R A B i ∧
      ∀ (q' : PrimeSpectrum (A ⊗[R] B))
        (Rp Aq Bp D : Type u) [CommRing Rp] [CommRing Aq] [CommRing Bp] [CommRing D]
        [Algebra R Rp] [Algebra A Aq] [Algebra B Bp] [Algebra (A ⊗[R] B) D]
        [IsLocalization.AtPrime Rp (q'.asIdeal.comap (algebraMap R (A ⊗[R] B)))]
        [IsLocalization.AtPrime Aq (q'.asIdeal.comap (algebraMap A (A ⊗[R] B)))]
        [IsLocalization.AtPrime Bp (q'.asIdeal.comap
          Algebra.TensorProduct.includeRight.toRingHom)]
        [IsLocalization.AtPrime D q'.asIdeal]
        [Algebra R Aq] [Algebra R Bp] [Algebra Rp Aq] [Algebra Rp Bp]
        [IsScalarTower R A Aq] [IsScalarTower R B Bp]
        [IsScalarTower R Rp Aq] [IsScalarTower R Rp Bp]
        [Algebra A D] [Algebra B D] [Algebra Aq D] [Algebra Bp D]
        [IsScalarTower A (A ⊗[R] B) D]
        [IsScalarTower A Aq D]
        (_hB : ∀ b : B, algebraMap B D b =
          algebraMap (A ⊗[R] B) D (Algebra.TensorProduct.includeRight b))
        [IsScalarTower B Bp D]
        (f : (Aq ⊗[Rp] Bp) →+* D)
        (_hfA : ∀ a : Aq,
          f (Algebra.TensorProduct.includeLeft (S := Rp) a : Aq ⊗[Rp] Bp) = algebraMap Aq D a)
        (_hfB : ∀ b : Bp, f (Algebra.TensorProduct.includeRight b) = algebraMap Bp D b),
        ∃ (Sl Tl : CochainComplex (ModuleCat.{u} Aq) ℤ ⥤
            ModuleCat.{u} (Aq ⊗[Rp] Bp))
          (eSl : Sl ⋙
            ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom ≅
            source Rp Aq Bp i)
          (eTl : Tl ⋙
            ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom ≅
            target Rp Aq Bp i)
          (cl : Sl ⟶ Tl),
          (∀ (M : CochainComplex (ModuleCat.{u} Aq) ℤ) (a : Aq) (x : Sl.obj M),
            eSl.hom.app M ((Algebra.TensorProduct.includeLeft (S := Rp) a : Aq ⊗[Rp] Bp) • x) =
              (source Rp Aq Bp i).map (a • 𝟙 M) (eSl.hom.app M x)) ∧
          (∀ (M : CochainComplex (ModuleCat.{u} Aq) ℤ) (a : Aq) (x : Tl.obj M),
            eTl.hom.app M ((Algebra.TensorProduct.includeLeft (S := Rp) a : Aq ⊗[Rp] Bp) • x) =
              (target Rp Aq Bp i).map (a • 𝟙 M) (eTl.hom.app M x)) ∧
          Functor.whiskerRight cl
              (ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom) ≫
              eTl.hom = eSl.hom ≫ comparison Rp Aq Bp i ∧
          ∃ (alpha : S ⋙ ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D) ≅
              extend A Aq ⋙ Sl ⋙ ModuleCat.extendScalars f)
            (beta : T ⋙ ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D) ≅
              extend A Aq ⋙ Tl ⋙ ModuleCat.extendScalars f),
            Functor.whiskerRight c (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)) ≫
                beta.hom = alpha.hom ≫
              Functor.whiskerLeft (extend A Aq)
                (Functor.whiskerRight cl (ModuleCat.extendScalars f)) ∧
            Nonempty (Tl ⋙ ModuleCat.extendScalars f ≅
              resolution Aq ⋙ extend Aq D ⋙
                HomologicalComplex.homologyFunctor (ModuleCat.{u} D) (.up ℤ) i) := by
  sorry

end RingTensorCohomology
