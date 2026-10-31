/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenTensorNormalizationData
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
import WeilConjectures.Algebra.Homology.RingedDerivedTensorNativeSupplement
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Pinned tensor transport for finite realizations

Source: Stacks 03EK, 06YN and 06YU.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace SheafOfModules.OpenTensorNormalization

private theorem acyclic_map_iff {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] (F : C ⥤ D) [F.Additive] [F.IsEquivalence]
    (P : CochainComplex C ℤ) :
    P.Acyclic ↔ ((F.mapHomologicalComplex (.up ℤ)).obj P).Acyclic := by
  constructor <;> intro h n
  · exact (P.sc n).exact_map_iff_of_faithful F |>.2 (h n)
  · exact (P.sc n).exact_map_iff_of_faithful F |>.1 (h n)

private theorem resolving_iso {X : Scheme.{u}}
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {P Q : CochainComplex (Mod R) ℤ} (e : P ≅ Q) (hP : resolving R P) :
    resolving R Q := by
  constructor
  · intro N hN n
    exact (hP.1 N hN n).of_iso
      (((tensor R).map₂CochainComplex.obj N).mapIso e)
  · intro n
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R (P.X n) ≪≫
        (tensor R).flip.mapIso ((HomologicalComplex.eval _ _ n).mapIso e) ≪≫
        (SheafOfModules.siteSheafTensorRightIso R (Q.X n)).symm) (hP.2 n)

-- Transport full faithfulness of restriction through a square of equivalences.
private theorem restriction_fullyFaithful
    {C D C' D' E : Type*} [Category C] [Category D] [Category C'] [Category D']
    [Category E] (q : C ⥤ D) (q' : C' ⥤ D')
    (a : C ≌ C') (b : D ≌ D') (α : q ⋙ b.functor ≅ a.functor ⋙ q')
    (h : ((Functor.whiskeringLeft C' D' E).obj q').FullyFaithful) :
    Nonempty ((Functor.whiskeringLeft C D E).obj q).FullyFaithful := by
  let V := (Functor.whiskeringLeft D D' E).obj b.functor
  let W := (Functor.whiskeringLeft C D E).obj q
  let U := (Functor.whiskeringLeft C C' E).obj a.functor
  let hU := Functor.FullyFaithful.ofFullyFaithful U
  let hVW : (V ⋙ W).FullyFaithful :=
    (h.comp hU).ofIso ((Functor.whiskeringLeft C D' E).mapIso α.symm)
  let hVW' := (Functor.FullyFaithful.ofFullyFaithful V.asEquivalence.inverse).comp hVW
  exact ⟨hVW'.ofIso
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight V.asEquivalence.counitIso W ≪≫ Functor.leftUnitor W)⟩

section CochainOperations
variable {B : Type*} [Category B] [Preadditive B] [HasZeroObject B]
  [MonoidalCategory B] [MonoidalPreadditive B]
  [∀ (V W : GradedObject ℤ B), V.HasTensor W]
  [∀ (V W Y : GradedObject ℤ B), GradedObject.HasGoodTensor₁₂Tensor V W Y]
  [∀ (V W Y : GradedObject ℤ B), GradedObject.HasGoodTensorTensor₂₃ V W Y]

private theorem complex_whiskerLeft (P : CochainComplex B ℤ)
    {Q Q' : CochainComplex B ℤ} (f : Q ⟶ Q') :
    P ◁ f = HomologicalComplex.mapBifunctorMap (𝟙 P) f (curriedTensor B) (.up ℤ) := by
  rfl

private theorem complex_whiskerRight {P P' : CochainComplex B ℤ} (f : P ⟶ P')
    (Q : CochainComplex B ℤ) :
    f ▷ Q = HomologicalComplex.mapBifunctorMap f (𝟙 Q) (curriedTensor B) (.up ℤ) := by
  rfl

variable [∀ (V W Y Z : GradedObject ℤ B), GradedObject.HasTensor₄ObjExt V W Y Z]

private theorem cochainTensorator_naturality
    {D : Type*} [Category D] [MonoidalCategory D]
    (q : CochainComplex B ℤ ⥤ D) [q.LaxMonoidal]
    {Z Z' : CochainComplex B ℤ × CochainComplex B ℤ} (f : Z ⟶ Z') :
    ((q.prod q) ⋙ Functor.uncurry.obj (curriedTensor D)).map f ≫
        Functor.LaxMonoidal.μ q Z'.1 Z'.2 =
      Functor.LaxMonoidal.μ q Z.1 Z.2 ≫
        (Functor.uncurry.obj ((curriedTensor B).map₂HomologicalComplex
          (.up ℤ) (.up ℤ) (.up ℤ)) ⋙ q).map f := by
  simp only [Functor.comp_map, Functor.prod_map, Functor.uncurry_obj_map,
    Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj, curriedTensor_obj_obj,
    curriedTensor_obj_map, curriedTensor_map_app,
    Functor.map₂HomologicalComplex_map_app, Functor.map₂HomologicalComplex_obj_map]
  simpa only [tensorHom_def, complex_whiskerLeft, complex_whiskerRight] using
    Functor.LaxMonoidal.μ_natural q f.1 f.2

private def cochainTensorator
    {D : Type*} [Category D] [MonoidalCategory D]
    (q : CochainComplex B ℤ ⥤ D) [q.LaxMonoidal] :
    (q.prod q) ⋙ Functor.uncurry.obj (curriedTensor D) ⟶
      Functor.uncurry.obj ((curriedTensor B).map₂HomologicalComplex
        (.up ℤ) (.up ℤ) (.up ℤ)) ⋙ q where
  app Z := Functor.LaxMonoidal.μ q Z.1 Z.2
  naturality _ _ f := cochainTensorator_naturality q f

end CochainOperations

private theorem comparisonDescent_forward
    {K H D E : Type*} [Category K] [Category H] [Category D] [Category E]
    (q : K ⥤ D) (q' : H ⥤ E) (F : K ⥤ H) (LF : D ⥤ E)
    (eps : q ⋙ LF ⟶ F ⋙ q') (P : ObjectProperty K) (S : ObjectProperty H)
    (hF : ∀ X, P X → S (F.obj X))
    (ff : ((Functor.whiskeringLeft (P.FullSubcategory × P.FullSubcategory) (D × D) E).obj
      ((P.ι ⋙ q).prod (P.ι ⋙ q))).FullyFaithful)
    (t : K × K ⥤ K) (t' : H × H ⥤ H) (T : D × D ⥤ D) (T' : E × E ⥤ E)
    (r : ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ T ≅ (P.ι.prod P.ι) ⋙ t ⋙ q)
    (r' : (S.ι.prod S.ι) ⋙ t' ⋙ q' ≅ ((S.ι ⋙ q').prod (S.ι ⋙ q')) ⋙ T')
    (b : t ⋙ F ≅ (F.prod F) ⋙ t')
    (he : ∀ X, P X → IsIso (eps.app X))
    (het : ∀ X Y, P X → P Y → IsIso (eps.app (t.obj (X, Y)))) :
    ∃ d : T ⋙ LF ≅ (LF.prod LF) ⋙ T',
      ∀ (X Y : K) (hx : P X) (hy : P Y),
        LF.map (r.hom.app (⟨X, hx⟩, ⟨Y, hy⟩)) ≫ eps.app (t.obj (X, Y)) ≫
            q'.map (b.hom.app (X, Y)) ≫
              r'.hom.app (⟨F.obj X, hF X hx⟩, ⟨F.obj Y, hF Y hy⟩) =
          d.hom.app (q.obj X, q.obj Y) ≫
            T'.map (CategoryTheory.Prod.mkHom (eps.app X) (eps.app Y)) := by
  obtain ⟨d, hd, _⟩ := CategoryTheory.tensorComparisonDescent q q' F LF eps P S hF ff
    t t' T T' r.symm r' b he het
  refine ⟨d, ?_⟩
  intro X Y hx hy
  have h := congrArg
    (fun z ↦ LF.map (r.hom.app (⟨X, hx⟩, ⟨Y, hy⟩)) ≫ z) (hd X Y hx hy)
  simpa only [Iso.symm_hom, ← LF.map_comp_assoc, Iso.hom_inv_id_app,
    LF.map_id, Category.id_comp, Category.assoc] using h.symm

set_option maxHeartbeats 800000 in
-- Native tensor structures require a larger elaboration budget.
private theorem tensorator_isIso
    {A : Type (u + 1)} [CommRing A] [Finite A] {X : Scheme.{u}}
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    (e : FiniteRealization A X R i)
    (s : Functor.uncurry.obj
        ((curriedTensor (FiniteModules A X)).map₂HomologicalComplex
          (.up ℤ) (.up ℤ) (.up ℤ)) ⋙ finiteComplexRealization e ≅
      ((finiteComplexRealization e).prod (finiteComplexRealization e)) ⋙ total R)
    (P Q : CochainComplex (FiniteModules A X) ℤ)
    (hP : resolving R ((finiteComplexRealization e).obj P)) :
    IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) := by
  have hright (N : CochainComplex (FiniteModules A X) ℤ) (hN : N.Acyclic) :
      (N ⊗ P).Acyclic := by
    apply (acyclic_map_iff e.equivalence.functor (N ⊗ P)).2
    intro n
    exact (hP.1 ((finiteComplexRealization e).obj N)
      ((acyclic_map_iff e.equivalence.functor N).1 hN) n).of_iso (s.app (N, P)).symm
  exact RingedDerivedNative.localization_isIso_mu P Q
    (Or.inl (RingedDerivedNative.kFlat_of_acyclic P hright))

set_option maxHeartbeats 800000 in
-- The native derived tensor structures require a larger elaboration budget.
/-- A natural pure-summand tensor comparison descends to the specified derived tensor.

Source: Stacks, Cohomology on Sites, Tags 06YS, 06YP and 06YU.
(blueprint: lem-sf-finite-tensor-derived-comparison).

Proof: restricting the supplied total comparison to complexes supported in degree
zero recovers the pure-pair ordinary tensor comparison. Its pure-pair equation
identifies it with the bilinear universal-property comparison. In particular it is
natural and conjugates tensoring by M to tensoring by e(M). Exactness of e and its
inverse then shows that they preserve and reflect flat objects.

The supplied natural total comparison conjugates the acyclic-tensor test as well.
Every target complex is isomorphic to the termwise image of a source complex,
because e is an equivalence. Exactness preserves and reflects acyclicity. Thus a
source complex is K-flat if and only if its termwise image is K-flat. Together with
the flat-object result, this identifies flat-term K-flat resolving classes under the
termwise equivalence. Both classes give localizations presenting the derived
categories: resolve an arbitrary complex, and refine roofs and equality witnesses by
flat-term K-flat resolutions. The product localizations are fully faithful on
functor categories.

On a resolving pair P,Q compose the realization factor at their total tensor, the
localized supplied total comparison, and t.representative. Compose on the other side
with the inverses of the two realization factors and of the native fixed-coefficient
localization tensorator. That tensorator is invertible on these K-flat pairs by the
native derived tensor's representative computation. Naturality in the resolving
pair follows from the naturality of the supplied comparison and of all localization
factors. Full faithfulness of restriction along the product localization extends this
natural isomorphism uniquely to d on the derived categories. Its restriction is the
specified composite. Cancel the invertible native tensorator and realization
factors to get precisely finiteTensorModel on every pair whose images are resolving.
The acyclic-tensor equivalence ensures these pairs belong to the same resolving
class, so the equation holds on every pair quantified there, not only on a chosen
resolution. -/
theorem finite_tensor_derived_comparison_exists
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj)
    [Presheaf.IsLocallySurjective (ProEt.topology X) i]
    (e : FiniteRealization A X R i)
    (s : Functor.uncurry.obj
        ((curriedTensor (FiniteModules A X)).map₂HomologicalComplex
          (.up ℤ) (.up ℤ) (.up ℤ)) ⋙ finiteComplexRealization e ≅
      ((finiteComplexRealization e).prod (finiteComplexRealization e)) ⋙ total R)
    (hs : finiteTensorPure e (fun P Q ↦ s.app (P, Q))) (t : TensorModel R) :
    ∃ d : finiteTensor A X ⋙ e.derived ≅ (e.derived.prod e.derived) ⋙ t.functor,
      finiteTensorModel e t d (fun P Q ↦ s.app (P, Q)) := by
  classical
  -- The natural total comparison already suffices for this descent.
  have _hPure := hs
  let F := finiteComplexRealization e
  let C := CochainComplex (FiniteModules A X) ℤ
  let S : ObjectProperty C := (resolving R).inverseImage F
  have : (resolving R).IsClosedUnderIsomorphisms :=
    ⟨fun c h ↦ resolving_iso c h⟩
  let ec := (e.equivalence.mapHomologicalComplex (.up ℤ)).congrFullSubcategory
    (P := S) (Q := resolving R) rfl
  let ed := e.equivalence.mapDerivedCategory
  let q := S.ι ⋙ DerivedCategory.Q
  let q' := (resolving R).ι ⋙ DerivedCategory.Q
  let φ := e.equivalence.functor.mapDerivedCategoryFactors
  let α : q ⋙ ed.functor ≅ ec.functor ⋙ q' := Functor.isoWhiskerLeft S.ι φ
  have htarget : ((Functor.whiskeringLeft _ _ (Der R)).obj (q'.prod q')).FullyFaithful :=
    ((Functor.FullyFaithful.nonempty_iff_map_bijective _).2 t.descent).some
  obtain ⟨hW⟩ := restriction_fullyFaithful (q.prod q) (q'.prod q')
    (ec.prod ec) (ed.prod ed) (NatIso.prod α α) htarget
  let T := Functor.uncurry.obj
    ((curriedTensor (FiniteModules A X)).map₂HomologicalComplex
      (.up ℤ) (.up ℤ) (.up ℤ))
  let μ : q.prod q ⋙ finiteTensor A X ⟶ (S.ι.prod S.ι) ⋙ T ⋙ DerivedCategory.Q :=
    Functor.whiskerLeft (S.ι.prod S.ι) (cochainTensorator DerivedCategory.Q)
  have hμ (Z : S.FullSubcategory × S.FullSubcategory) : IsIso (μ.app Z) :=
    tensorator_isIso e s Z.1.obj Z.2.obj Z.1.property
  have : IsIso μ := NatIso.isIso_of_isIso_app μ
  obtain ⟨d, hd⟩ := comparisonDescent_forward DerivedCategory.Q DerivedCategory.Q
    F e.derived φ.hom S (resolving R) (fun _ hp ↦ hp) hW T (total R)
    (finiteTensor A X) t.functor (asIso μ) t.representative s
    (fun _ _ ↦ inferInstance) (fun _ _ _ _ ↦ inferInstance)
  refine ⟨d, ?_⟩
  intro P Q hp hq
  apply heq_of_eq
  exact hd P Q hp hq

end SheafOfModules.OpenTensorNormalization
