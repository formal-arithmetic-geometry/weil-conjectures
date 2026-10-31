/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PointDerivedHomModels
public import WeilConjectures.AlgebraicGeometry.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.AlgebraicGeometry.PointFiniteCohomologyComplexes
public import WeilConjectures.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import WeilConjectures.AlgebraicGeometry.ModuleHomSignedEvaluation
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleIhom
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleDevissageSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleBound
public import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleConstructible
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

/-! # Reconstructed finite-point Hom with an arbitrary target

Source: blueprint main-20261015, sec-six-functors/sk-thm-sf-package,
lem-pod-point-dualizing-complex.proof.md, second sentence; Stacks 03CY,
03EI, 08BJ, 070I and 0A95
(blueprint: lem-coef-finite-point-reconstructed-hom-model).

The chain comparison is normalized on every homogeneous element. Its localization
square uses the actual internal-Hom resolution map and the transpose of ordinary
Hom evaluation, so neither the comparison nor the reconstructed composite is arbitrary.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct

namespace WeilConjectures.FinitePointHom

/-- Ordinary modules use the recorded small Grothendieck derived localization.
Source: Stacks 05RU (blueprint: lem-coef-finite-point-reconstructed-hom-model). -/
instance (priority := 2100) ordinaryDerived (R : Type v) [CommRing R] :
    HasDerivedCategory.{v} (ModuleCat.{v} R) :=
  HasDerivedCategory.ofIsGrothendieckAbelian (ModuleCat.{v} R)

/-- The ordinary signed evaluation is uniquely determined on all total-tensor summands.
Source: Stacks 0A8H, 0A8X (blueprint: lem-coef-finite-point-reconstructed-hom-model).
Proof: define the map on the (p,j) summand by (-1)^(p*j) h(x). Balancing gives a
linear map. The direct-sum universal property gives each degree map. Expanding the
Hom differential cancels the two terms containing h(d x), proving the chain equation.
Pure tensors generate every summand, proving uniqueness. No boundedness is used. -/
theorem ordinaryEvaluation_existsUnique {A : Type v} [CommRing A]
    (P J : CochainComplex (ModuleCat.{v} A) ℤ) :
    ∃! e : P ⊗ CochainComplex.moduleHomComplex P J ⟶ J,
      ∀ (p j : ℤ) (x : P.X p) (h : (CochainComplex.moduleHomComplex P J).X j),
        (e.f (p + j)).hom
          ((HomologicalComplex.ιTensorObj P (CochainComplex.moduleHomComplex P J)
            p j (p + j) rfl).hom (x ⊗ₜ[A] h)) =
          (p * j).negOnePow • (h.v p (p + j) rfl).hom x := by
  obtain ⟨e, he⟩ := CochainComplex.module_hom_signed_evaluation P J
  refine ⟨e, he, ?_⟩
  intro f hf
  apply HomologicalComplex.Hom.ext
  funext r
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p j hpj
  have h : p + j = r := hpj
  subst r
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x z
  exact (hf p j x z).trans (he p j x z).symm

/-- Ordinary evaluation, chosen from its unique pure-tensor characterization.
Source: Stacks 0A8H (blueprint: lem-coef-finite-point-reconstructed-hom-model). -/
def ordinaryEvaluation {A : Type v} [CommRing A]
    (P J : CochainComplex (ModuleCat.{v} A) ℤ) :
    P ⊗ CochainComplex.moduleHomComplex P J ⟶ J :=
  (ordinaryEvaluation_existsUnique P J).choose

/-- The canonical ordinary Hom representative map is the transpose of localized evaluation.
Source: Stacks 0A95 (blueprint: lem-coef-finite-point-reconstructed-hom-model). -/
def ordinaryModelMap {A : Type v} [CommRing A]
    (P J : CochainComplex (ModuleCat.{v} A) ℤ) :
    DerivedCategory.Q.obj (CochainComplex.moduleHomComplex P J) ⟶
      (ordinaryModuleDerivedInternalHom A).obj
        (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj J) :=
  MonoidalClosed.curry
    (Functor.LaxMonoidal.μ DerivedCategory.Q P (CochainComplex.moduleHomComplex P J) ≫
      DerivedCategory.Q.map (ordinaryEvaluation P J))

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ)

/-- The recorded positive-level quotient, lifted to the small site's coefficient universe.
Source: blueprint point proof (blueprint: lem-coef-finite-point-reconstructed-hom-model). -/
abbrev A := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)

/-- The actual constant ring sheaf of the quotient coefficient ring.
Source: Stacks 03CY (blueprint: lem-coef-finite-point-reconstructed-hom-model). -/
abbrev B := PointDerivedHom.coefficientSheaf.{u, u} D.k l E n false

/-- The existing module category on the small pro-etale site of Spec k.
Source: Stacks 03D1 (blueprint: lem-coef-finite-point-reconstructed-hom-model). -/
abbrev Mod := PointDerivedHom.Modules.{u, u} D.k (B D l E n)

/-- Fix the existing module sheafification at the site's coefficient size.
Source: Stacks 03CY (blueprint: lem-coef-finite-point-reconstructed-hom-model). -/
instance (priority := 2100) finiteAbSheafify :
    HasSheafify (ProEt.topology (Spec (.of D.k))) AddCommGrpCat.{u + 1} :=
  PointDerivedHom.abSheafify.{u, u} D.k

/-- Fix the existing local bijectivity criterion at the same size.
Source: Stacks 03CY (blueprint: lem-coef-finite-point-reconstructed-hom-model). -/
instance (priority := 2100) finiteAbLocallyBijective :
    (ProEt.topology (Spec (.of D.k))).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  PointDerivedHom.abLocallyBijective.{u, u} D.k

/-- Sheaf modules retain the recorded standard localization used by constructibility.
Source: Stacks 05RU (blueprint: lem-coef-finite-point-reconstructed-hom-model). -/
instance (priority := 2100) finiteSheafDerived : HasDerivedCategory.{u + 2} (Mod D l E n) :=
  HasDerivedCategory.standard _

/-- Final-object sections with the canonical A-action, without a new scalar choice.
Source: Stacks 03CW (blueprint: lem-coef-finite-point-reconstructed-hom-model). -/
abbrev G : Mod D l E n ⥤ ModuleCat.{u + 1} (A l E n) :=
  PointDerivedHom.sections.{u, u} D.k (B D l E n)
  (PointDerivedHom.coefficientMap.{u, u} D.k l E n false)

/-- Sections have the existing evaluation and scalar-restriction additive structure.
Source: Stacks 03CW (blueprint: lem-coef-finite-point-reconstructed-hom-model). -/
instance finiteSectionsAdditive : (G D l E n).Additive :=
  PointDerivedHom.sections_additive.{u, u} D.k (B D l E n) (𝟙 _)

/-- The recorded ambient derived internal Hom, including unbounded targets.
Source: Stacks 0A95 (blueprint: lem-coef-finite-point-reconstructed-hom-model). -/
abbrev H := derivedInternalHomOfUniverses.{u + 1, u, u}
  (ProEt.topology (Spec (.of D.k))) (B D l E n)

variable (L : ModuleCat.{u + 1} (A l E n) ⥤ Mod D l E n) [L.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits (G D l E n)] [PreservesFiniteColimits (G D l E n)]

/-- The source of q as a bifunctor of the ordinary source and ambient sheaf target.
Source: Stacks 0A95 (blueprint: lem-coef-finite-point-reconstructed-hom-model). -/
abbrev qSource :
    (DerivedCategory (ModuleCat.{u + 1} (A l E n)))ᵒᵖ ×
      DerivedCategory (Mod D l E n) ⥤ DerivedCategory (ModuleCat.{u + 1} (A l E n)) :=
  L.mapDerivedCategory.op.prod (𝟭 _) ⋙ H D l E n ⋙
  (G D l E n).mapDerivedCategory

/-- The target of q, using the recorded ordinary-module RHom.
Source: Stacks 0A95 (blueprint: lem-coef-finite-point-reconstructed-hom-model). -/
abbrev qTarget :
    (DerivedCategory (ModuleCat.{u + 1} (A l E n)))ᵒᵖ ×
      DerivedCategory (Mod D l E n) ⥤ DerivedCategory (ModuleCat.{u + 1} (A l E n)) :=
  (𝟭 (DerivedCategory (ModuleCat.{u + 1} (A l E n)))).op.prod (G D l E n).mapDerivedCategory ⋙
  ordinaryModuleDerivedInternalHom (A l E n)

/-- The canonical sheaf-Hom representative map after exact sections and extension.
Source: Stacks 0A95 (blueprint: lem-coef-finite-point-reconstructed-hom-model). -/
def sourceModelMap (P : CochainComplex (ModuleCat.{u + 1} (A l E n)) ℤ)
    (J : CochainComplex (Mod D l E n) ℤ) :
    DerivedCategory.Q.obj (((G D l E n).mapHomologicalComplex (.up ℤ)).obj
      (PointDerivedHom.sheafHom.{u, u} D.k (B D l E n)
        ((L.mapHomologicalComplex (.up ℤ)).obj P) J)) ⟶
      (qSource D l E n L).obj (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj J) :=
  (G D l E n).mapDerivedCategoryFactors.inv.app _ ≫
    (G D l E n).mapDerivedCategory.map
      (IntegralHom.homModelMap.{u, u} (Spec (.of D.k)) (B D l E n)
        ((L.mapHomologicalComplex (.up ℤ)).obj P) J) ≫
    (G D l E n).mapDerivedCategory.map
      ((H D l E n).map
        ((L.mapDerivedCategoryFactors.hom.app P).op, 𝟙 (DerivedCategory.Q.obj J)))

/-- The canonical ordinary-Hom representative map and exact-sections factorization.
Source: Stacks 0A95 (blueprint: lem-coef-finite-point-reconstructed-hom-model). -/
def targetModelMap (P : CochainComplex (ModuleCat.{u + 1} (A l E n)) ℤ)
    (J : CochainComplex (Mod D l E n) ℤ) :
    DerivedCategory.Q.obj (CochainComplex.moduleHomComplex P
      (((G D l E n).mapHomologicalComplex (.up ℤ)).obj J)) ⟶
      (qTarget D l E n).obj (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj J) :=
  ordinaryModelMap P (((G D l E n).mapHomologicalComplex (.up ℤ)).obj J) ≫
    (ordinaryModuleDerivedInternalHom (A l E n)).map
      (𝟙 (op (DerivedCategory.Q.obj P)), (G D l E n).mapDerivedCategoryFactors.inv.app J)

/-- Finite cohomology and reconstruction use the actual derived adjunction counit.
Source: blueprint point proof (blueprint: lem-coef-finite-point-reconstructed-hom-model). -/
def Reconstruction (hn : 1 ≤ n) (adj : L ⊣ G D l E n) : Prop :=
  ∀ C : DerivedCategory (Mod D l E n),
    intrinsicFiniteTorsionConstructible l E n hn (Spec (.of D.k)) C →
      DerivedCategory.pointFiniteCohomology (A l E n)
        ((G D l E n).mapDerivedCategory.obj C) ∧
      IsIso (adj.mapDerivedCategoryAdjunction.counit.app C) ∧
      adj.mapDerivedCategoryAdjunction.unit.app ((G D l E n).mapDerivedCategory.obj C) ≫
        (G D l E n).mapDerivedCategory.map
          (adj.mapDerivedCategoryAdjunction.counit.app C) =
            𝟙 ((G D l E n).mapDerivedCategory.obj C)

/-- The chain comparison is fixed on every product component by h maps to h(1 tensor x).
Source: Stacks 0A8X (blueprint: lem-coef-finite-point-reconstructed-hom-model). -/
def ChainComparison
    (hobj : ∀ M : ModuleCat.{u + 1} (A l E n), L.obj M =
      PointDerivedHom.extensionObject.{u, u} D.k (B D l E n) (𝟙 _) M)
    (P : CochainComplex (ModuleCat.{u + 1} (A l E n)) ℤ)
    (J : CochainComplex (Mod D l E n) ℤ)
    (q : ((G D l E n).mapHomologicalComplex (.up ℤ)).obj
      (PointDerivedHom.sheafHom.{u, u} D.k (B D l E n)
        ((L.mapHomologicalComplex (.up ℤ)).obj P) J) ≅
      CochainComplex.moduleHomComplex P
        (((G D l E n).mapHomologicalComplex (.up ℤ)).obj J)) : Prop :=
  ∀ (j p : ℤ)
    (h : (((G D l E n).mapHomologicalComplex (.up ℤ)).obj
      (PointDerivedHom.sheafHom.{u, u} D.k (B D l E n)
        ((L.mapHomologicalComplex (.up ℤ)).obj P) J)).X j) (x : P.X p),
    (((q.hom.f j).hom h).v p (p + j) rfl).hom x =
      PointDerivedHom.homValue.{u, u} D.k (B D l E n)
        ((L.mapHomologicalComplex (.up ℤ)).obj P) J j p
          (op (PointDerivedHom.finalObject D.k)) h
          (PointDerivedHom.generator.{u, u} D.k (B D l E n) (𝟙 _) L hobj
            (P.X p) (op (PointDerivedHom.finalObject D.k)) 1 x)

/-- Naturality for every derived morphism, with no restriction on the ambient target.
Source: Stacks 070I, 0A95 (blueprint: lem-coef-finite-point-reconstructed-hom-model). -/
def QNatural
    (q : ∀ (c : DerivedCategory (ModuleCat.{u + 1} (A l E n))),
      DerivedCategory.pointFiniteCohomology (A l E n) c →
      ∀ V : DerivedCategory (Mod D l E n),
        (qSource D l E n L).obj (op c, V) ≅ (qTarget D l E n).obj (op c, V)) : Prop :=
  ∀ (c c' : DerivedCategory (ModuleCat.{u + 1} (A l E n)))
    (hc : DerivedCategory.pointFiniteCohomology (A l E n) c)
    (hc' : DerivedCategory.pointFiniteCohomology (A l E n) c')
    (f : c' ⟶ c) (V V' : DerivedCategory (Mod D l E n)) (g : V ⟶ V'),
    (qSource D l E n L).map (f.op, g) ≫ (q c' hc' V').hom =
      (q c hc V).hom ≫ (qTarget D l E n).map (f.op, g)

/-- Resolution-independent, normalized derived comparison on bounded finite source cohomology.
The normalization quantifies every flat-term K-flat representative and every K-injective
complex, hence also every K-injective resolution of an arbitrary ambient target.
Source: Stacks 08BJ, 0A95 (blueprint: lem-coef-finite-point-reconstructed-hom-model). -/
def Comparison
    (hobj : ∀ M : ModuleCat.{u + 1} (A l E n), L.obj M =
      PointDerivedHom.extensionObject.{u, u} D.k (B D l E n) (𝟙 _) M)
    (q : ∀ (c : DerivedCategory (ModuleCat.{u + 1} (A l E n))),
      DerivedCategory.pointFiniteCohomology (A l E n) c →
      ∀ V : DerivedCategory (Mod D l E n),
        (qSource D l E n L).obj (op c, V) ≅ (qTarget D l E n).obj (op c, V)) : Prop :=
    QNatural D l E n L q ∧
    (∀ (V J : CochainComplex (Mod D l E n) ℤ) [J.IsKInjective]
      (ι : V ⟶ J) [QuasiIso ι],
      CochainComplex.IsKInjective (((G D l E n).mapHomologicalComplex (.up ℤ)).obj J) ∧
        QuasiIso (((G D l E n).mapHomologicalComplex (.up ℤ)).map ι)) ∧
    ∀ (P : CochainComplex (ModuleCat.{u + 1} (A l E n)) ℤ)
      (hP : DerivedCategory.pointFiniteCohomology (A l E n) (DerivedCategory.Q.obj P)),
      (∀ F : CochainComplex (ModuleCat.{u + 1} (A l E n)) ℤ,
        F.Acyclic → (PointDerivedHom.moduleTotal F P).Acyclic) →
      (∀ i : ℤ, Module.Flat (A l E n) (P.X i)) →
      ∀ (J : CochainComplex (Mod D l E n) ℤ) [J.IsKInjective],
        ∃ qPJ : ((G D l E n).mapHomologicalComplex (.up ℤ)).obj
            (PointDerivedHom.sheafHom.{u, u} D.k (B D l E n)
              ((L.mapHomologicalComplex (.up ℤ)).obj P) J) ≅
            CochainComplex.moduleHomComplex P
              (((G D l E n).mapHomologicalComplex (.up ℤ)).obj J),
          ChainComparison D l E n L hobj P J qPJ ∧
          IsIso (sourceModelMap D l E n L P J) ∧
          IsIso (targetModelMap D l E n P J) ∧
          sourceModelMap D l E n L P J ≫ (q _ hP (DerivedCategory.Q.obj J)).hom =
            DerivedCategory.Q.map qPJ.hom ≫ targetModelMap D l E n P J

/-- The reconstructed Q is q after contravariant precomposition with the actual counit.
The final square expresses naturality for arbitrary morphisms in both derived categories.
Source: blueprint point proof (blueprint: lem-coef-finite-point-reconstructed-hom-model). -/
def ReconstructedComparison (hn : 1 ≤ n) (adj : L ⊣ G D l E n)
    (q : ∀ (c : DerivedCategory (ModuleCat.{u + 1} (A l E n))),
      DerivedCategory.pointFiniteCohomology (A l E n) c →
      ∀ V : DerivedCategory (Mod D l E n),
        (qSource D l E n L).obj (op c, V) ≅ (qTarget D l E n).obj (op c, V))
    (hfin : ∀ C : DerivedCategory (Mod D l E n),
      intrinsicFiniteTorsionConstructible l E n hn (Spec (.of D.k)) C →
        DerivedCategory.pointFiniteCohomology (A l E n)
          ((G D l E n).mapDerivedCategory.obj C)) : Prop :=
  ∃ Q : ∀ (C : DerivedCategory (Mod D l E n)),
      intrinsicFiniteTorsionConstructible l E n hn (Spec (.of D.k)) C →
      ∀ V : DerivedCategory (Mod D l E n),
        (G D l E n).mapDerivedCategory.obj ((H D l E n).obj (op C, V)) ≅
          (ordinaryModuleDerivedInternalHom (A l E n)).obj
            (op ((G D l E n).mapDerivedCategory.obj C),
              (G D l E n).mapDerivedCategory.obj V),
    (∀ (C : DerivedCategory (Mod D l E n))
      (hC : intrinsicFiniteTorsionConstructible l E n hn (Spec (.of D.k)) C)
      (V : DerivedCategory (Mod D l E n)),
      (Q C hC V).hom = (G D l E n).mapDerivedCategory.map
        ((H D l E n).map ((adj.mapDerivedCategoryAdjunction.counit.app C).op, 𝟙 V)) ≫
          (q _ (hfin C hC) V).hom) ∧
    ∀ (C C' : DerivedCategory (Mod D l E n))
      (hC : intrinsicFiniteTorsionConstructible l E n hn (Spec (.of D.k)) C)
      (hC' : intrinsicFiniteTorsionConstructible l E n hn (Spec (.of D.k)) C')
      (f : C' ⟶ C) (V V' : DerivedCategory (Mod D l E n)) (g : V ⟶ V'),
      (G D l E n).mapDerivedCategory.map ((H D l E n).map (f.op, g)) ≫
          (Q C' hC' V').hom =
        (Q C hC V).hom ≫ (ordinaryModuleDerivedInternalHom (A l E n)).map
          (((G D l E n).mapDerivedCategory.map f).op,
            (G D l E n).mapDerivedCategory.map g)

/-- Exact realization, reconstruction and the normalized arbitrary-target Hom comparison.
All hypotheses that describe the adjunction and its exactness are conclusions here;
the subsequent universal proof-instance binders merely expose their derived functors.

Source: blueprint main-20261015, sec-six-functors/sk-thm-sf-package,
lem-pod-point-dualizing-complex.proof.md, second sentence; Stacks 03CY, 03EI,
08BJ, 070I and 0A95 (blueprint: lem-coef-finite-point-reconstructed-hom-model).

Proof (the eight steps of the DAG node):
1. Multiplication identifies B tensor the constant module with the constant module.
   Exact module sheafification proves exactness of L. A map out of L is determined
   by h_s(1 tensor m); conversely restrict t(m) to U and multiply by b. These maps
   are inverse on all local generators and natural, proving the explicit adjunction.
2. The DVR and finite-quotient lemmas make A finite. Finite constant sections on
   the singleton Spec k identify Gamma B with A by the actual constant-value map.
   Point sections exactness applies to all module sheaves, hence to quasi-isomorphisms.
3. Termwise adjunction descends by exact-functor derived factorization and localization.
   Sections finiteness makes c bounded with finite cohomology. The finite branch of
   pointSectionsReconstruction makes the actual counit invertible. Its triangle
   equation is Gamma(e_C) u_c = identity; both maps are the descended termwise maps.
4. Take a flat-term K-flat source representative and any K-injective target resolution.
   The right adjoint of exact L preserves K-injectives; exact Gamma preserves the
   target resolution quasi-isomorphism, without boundedness of the target.
5. Global Hom cochains are products over all source degrees. Apply the explicit
   adjunction factorwise. Evaluation on 1 tensor x commutes with the differential
   d_J h - (-1)^j h d_P. The inverse is b tensor x mapped to b t(x)|_U.
6. Internal Hom into a K-injective computes RHom. The ordinary signed evaluation
   transpose identifies its ordinary-module model. Exact Gamma and the actual
   resolution comparisons give precisely the localization square in Comparison.
7. Pre- and post-composition commute with evaluation on 1 tensor x. Hom invariance
   gives commuting comparisons for all resolving representatives. K-injective
   Hom-to-derived bijectivity and the localization universal property extend these
   equations to every derived morphism. Flat-term K-flat resolutions and invertible
   model comparisons make the normalized derived family unique.
8. Precompose internal Hom with the actual counit and compose with q. This is the
   formula defining Q in ReconstructedComparison. Naturality of the counit and of q
   gives the displayed contravariant/covariant square for every derived morphism;
   the normalization and uniqueness give independence of all resolving choices. -/
theorem finite_point_reconstructed_hom_model (_hl : l ≠ D.p) (hn : 1 ≤ n) :
    ∃ (L : ModuleCat.{u + 1} (A l E n) ⥤ Mod D l E n)
      (hobj : ∀ M : ModuleCat.{u + 1} (A l E n),
        L.obj M = PointDerivedHom.extensionObject.{u, u} D.k (B D l E n) (𝟙 _) M),
      (∀ {M N : ModuleCat.{u + 1} (A l E n)} (f : M ⟶ N),
        L.map f = eqToHom (hobj M) ≫
          PointDerivedHom.extensionMorphism.{u, u} D.k (B D l E n) (𝟙 _) f ≫
            eqToHom (hobj N).symm) ∧
      ∃ multiplication : L ≅ PointDerivedHom.constantModules.{u, u} D.k
          (PointDerivedHom.coefficientRing.{u, u} l E n false),
        (∀ (M : ModuleCat.{u + 1} (A l E n)) (U : (Scheme.ProEt (Spec (.of D.k)))ᵒᵖ)
          (b : (B D l E n).obj.obj U) (x : M),
          (multiplication.hom.app M).val.app U
            (PointDerivedHom.generator.{u, u} D.k (B D l E n) (𝟙 _) L hobj M U b x) =
              b • PointDerivedHom.constantElement.{u, u} D.k
                (PointDerivedHom.coefficientRing.{u, u} l E n false) M U x) ∧
      ∃ adj : L ⊣ G D l E n,
        PointDerivedHom.ExplicitAdjunction.{u, u} D.k (B D l E n) (𝟙 _) L hobj adj ∧
        PreservesFiniteLimits L ∧ PreservesFiniteColimits L ∧
        PreservesFiniteLimits (G D l E n) ∧ PreservesFiniteColimits (G D l E n) ∧
        Function.Bijective (PointDerivedHom.scalar.{u, u} D.k (B D l E n) (𝟙 _)
          (op (PointDerivedHom.finalObject D.k))) ∧
        ∀ [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
          [PreservesFiniteLimits (G D l E n)] [PreservesFiniteColimits (G D l E n)],
          ∃ hr : Reconstruction D l E n L hn adj,
            ∃! q : ∀ (c : DerivedCategory (ModuleCat.{u + 1} (A l E n))),
                DerivedCategory.pointFiniteCohomology (A l E n) c →
                ∀ V : DerivedCategory (Mod D l E n),
                  (qSource D l E n L).obj (op c, V) ≅ (qTarget D l E n).obj (op c, V),
              Comparison D l E n L hobj q ∧
                ReconstructedComparison D l E n L hn adj q (fun C hC ↦ (hr C hC).1) := by
  sorry

end WeilConjectures.FinitePointHom
