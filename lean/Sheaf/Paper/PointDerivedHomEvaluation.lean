/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q125
-/
module

public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.PointProEtaleSectionsExact
public import Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Algebra.Homology.ModuleHomComplex
public import Sheaf.Paper.IntegralHomReduction
public import Sheaf.Algebra.Homology.HomComplexProjections
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMap
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.CategoryTheory.Sites.Sheafification

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.HomComplex
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
-- The high-priority successor-universe sheafification instance gets stuck on coefficient-universe goals.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

/-! # Derived Hom and evaluation for extension from a pro-etale point

Source: Weil blueprint, main-20261015, sec-six-functors/sk-thm-sf-package,
lem-pod-point-dualizing-complex.proof.md, second sentence; Stacks Tags 0A8X,
08J7, 0G7E and 08BJ (blueprint: lem-pod-point-derived-hom-evaluation).

All tensors here are ordinary tensors. The site retains object universe t+1 and
morphism universe t; the coefficient universe is max u (t+1).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t u r

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped TensorProduct ChangeOfRings

namespace WeilConjectures.PointDerivedHom

variable (k : Type t) [Field k]

/-- Existing sheafification at the coefficient size, transported through a small model.
Source: Stacks 03DA (blueprint: lem-pod-point-derived-hom-evaluation). -/
instance abSheafify : HasSheafify (Scheme.ProEt.topology (Spec (.of k)))
    AddCommGrpCat.{max u (t + 1)} :=
  integralCoefficientAbSheafify.{t, u} (Spec (.of k))

/-- Existing local bijectivity criterion in the coefficient universe.
Source: Stacks 03DA (blueprint: lem-pod-point-derived-hom-evaluation). -/
instance abLocallyBijective : (Scheme.ProEt.topology (Spec (.of k))).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)} :=
  integralCoefficientAbLocallyBijective.{t, u} (Spec (.of k))

/-- The same small-model transport for commutative ring sheafification.
Source: Stacks 03CY (blueprint: lem-pod-point-derived-hom-evaluation). -/
instance ringLocallyBijective : (Scheme.ProEt.topology (Spec (.of k))).WEqualsLocallyBijective
    CommRingCat.{max u (t + 1)} :=
  letI : EssentiallySmall.{max u (t + 1)} (Scheme.ProEt (Spec (.of k))) :=
    essentiallySmallSelf _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- The actual final object of the small pro-etale site.
Source: Stacks 098H (blueprint: lem-pod-point-derived-hom-evaluation). -/
abbrev finalObject := Scheme.ProEt.mk (𝟙 (Spec (.of k)))

variable (R : CommRingCat.{max u (t + 1)})

/-- The recorded constant ring sheaf, at the joint coefficient universe.
Source: Stacks 03CY (blueprint: lem-pod-point-derived-hom-evaluation). -/
abbrev constantRing := (constantSheaf (Scheme.ProEt.topology (Spec (.of k)))
  CommRingCat.{max u (t + 1)}).obj R

/-- Forget commutativity of a coefficient sheaf without changing its sections.
Source: Stacks 03D1 (blueprint: lem-pod-point-derived-hom-evaluation). -/
abbrev ring (B : Sheaf (Scheme.ProEt.topology (Spec (.of k)))
    CommRingCat.{max u (t + 1)}) :=
  (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj B

/-- The existing category of modules on the unchanged small site.
Source: Stacks 03D1 (blueprint: lem-pod-point-derived-hom-evaluation). -/
abbrev Modules (B : Sheaf (Scheme.ProEt.topology (Spec (.of k)))
    CommRingCat.{max u (t + 1)}) := SheafOfModules.{max u (t + 1)} (ring.{t, u} k B)

/-- Constant-ring sheafification's actual unit.
Source: Stacks 03CY (blueprint: lem-pod-point-derived-hom-evaluation). -/
def constantUnit : (Functor.const (Scheme.ProEt (Spec (.of k)))ᵒᵖ).obj
    ((forget₂ CommRingCat RingCat).obj R) ⟶ (ring.{t, u} k (constantRing.{t, u} k R)).obj :=
  Functor.whiskerRight (toSheafify (Scheme.ProEt.topology (Spec (.of k)))
    ((Functor.const (Scheme.ProEt (Spec (.of k)))ᵒᵖ).obj R))
      (forget₂ CommRingCat RingCat)

/-- The existing local injectivity of ring sheafification, with commutativity forgotten.
Source: Stacks 03CY (blueprint: lem-pod-point-derived-hom-evaluation). -/
instance constantUnit_injective : Presheaf.IsLocallyInjective
    (Scheme.ProEt.topology (Spec (.of k))) (constantUnit.{t, u} k R) :=
  letI := ringLocallyBijective.{t, u} k
  (Presheaf.isLocallyInjective_forget_iff _ (constantUnit.{t, u} k R)).mp
    (inferInstanceAs (Presheaf.IsLocallyInjective _ (Functor.whiskerRight
      (toSheafify (Scheme.ProEt.topology (Spec (.of k)))
        ((Functor.const (Scheme.ProEt (Spec (.of k)))ᵒᵖ).obj R))
        (forget CommRingCat.{max u (t + 1)}))))

/-- The existing local surjectivity of ring sheafification.
Source: Stacks 03CY (blueprint: lem-pod-point-derived-hom-evaluation). -/
instance constantUnit_surjective : Presheaf.IsLocallySurjective
    (Scheme.ProEt.topology (Spec (.of k))) (constantUnit.{t, u} k R) :=
  letI := ringLocallyBijective.{t, u} k
  (Presheaf.isLocallySurjective_iff_whisker_forget _ (constantUnit.{t, u} k R)).mpr
    (inferInstanceAs (Presheaf.IsLocallySurjective _ (Functor.whiskerRight
      (toSheafify (Scheme.ProEt.topology (Spec (.of k)))
        ((Functor.const (Scheme.ProEt (Spec (.of k)))ᵒᵖ).obj R))
        (forget CommRingCat.{max u (t + 1)}))))

/-- Pull back the existing one-object constant-module presheaf to this site.
Source: Stacks 03CY (blueprint: lem-pod-point-derived-hom-evaluation). -/
def constantPresheaf : ModuleCat.{max u (t + 1)} R ⥤
    PresheafOfModules.{max u (t + 1)}
      ((Functor.const (Scheme.ProEt (Spec (.of k)))ᵒᵖ).obj (RingCat.of R)) :=
  siteConstantModulePresheafGeneral (C := Discrete (ULift.{max u (t + 1)} Unit)) R ⋙
    PresheafOfModules.pushforward₀
      ((Functor.const (Scheme.ProEt (Spec (.of k)))).obj (Discrete.mk (ULift.up ())))
      ((Functor.const (Discrete (ULift.{max u (t + 1)} Unit))ᵒᵖ).obj (RingCat.of R))

/-- The genuine constant module sheaf, formed by associated-module sheafification.
Source: Stacks 03CY (blueprint: lem-pod-point-derived-hom-evaluation). -/
def constantModules : ModuleCat.{max u (t + 1)} R ⥤ Modules.{t, u} k (constantRing.{t, u} k R) :=
  letI := abSheafify.{t, u} k
  letI := abLocallyBijective.{t, u} k
  constantPresheaf.{t, u} k R ⋙
    PresheafOfModules.sheafification.{max u (t + 1), t, max u (t + 1), t + 1}
      (constantUnit.{t, u} k R)

/-- Image of an actual module element under constant-module sheafification.
Source: Stacks 03CY (blueprint: lem-pod-point-derived-hom-evaluation). -/
def constantElement (M : ModuleCat.{max u (t + 1)} R)
    (U : (Scheme.ProEt (Spec (.of k)))ᵒᵖ) (x : M) :
    ((constantModules.{t, u} k R).obj M).val.obj U :=
  letI := abSheafify.{t, u} k
  letI := abLocallyBijective.{t, u} k
  (toSheafify (Scheme.ProEt.topology (Spec (.of k)))
    (((constantPresheaf.{t, u} k R).obj M).presheaf)).app U x

variable {R} (B : Sheaf (Scheme.ProEt.topology (Spec (.of k)))
  CommRingCat.{max u (t + 1)}) (α : constantRing.{t, u} k R ⟶ B)

/-- The canonical constant-value scalar map at each site object.
Source: Stacks 03CY (blueprint: lem-pod-point-derived-hom-evaluation). -/
def scalar (U : (Scheme.ProEt (Spec (.of k)))ᵒᵖ) : R →+* B.obj.obj U :=
  (α.hom.app U).hom.comp ((toSheafify (Scheme.ProEt.topology (Spec (.of k)))
    ((Functor.const (Scheme.ProEt (Spec (.of k)))ᵒᵖ).obj R)).app U).hom

/-- Sections with scalars restricted along the canonical constant-value map.
Source: Stacks 03CW (blueprint: lem-pod-point-derived-hom-evaluation). -/
def sections : Modules.{t, u} k B ⥤ ModuleCat.{max u (t + 1)} R :=
  SheafOfModules.forget (ring.{t, u} k B) ⋙
    PresheafOfModules.evaluation (ring.{t, u} k B).obj (op (finalObject k)) ⋙
    ModuleCat.restrictScalars (scalar.{t, u} k B α (op (finalObject k)))

/-- Evaluation and scalar restriction are the existing additive functors.
Source: Stacks 03CW (blueprint: lem-pod-point-derived-hom-evaluation). -/
instance sections_additive : (sections.{t, u} k B α).Additive :=
  inferInstanceAs ((SheafOfModules.forget (ring.{t, u} k B) ⋙
    PresheafOfModules.evaluation (ring.{t, u} k B).obj
    (op (finalObject k)) ⋙ ModuleCat.restrictScalars
      (scalar.{t, u} k B α (op (finalObject k)))).Additive)

/-- The actual local tensor generator of B tensor the constant module.
Source: Stacks 03EK (blueprint: lem-pod-point-derived-hom-evaluation). -/
def extensionElement (M : ModuleCat.{max u (t + 1)} R)
    (U : (Scheme.ProEt (Spec (.of k)))ᵒᵖ) (b : B.obj.obj U) (x : M) :
    (SheafOfModules.changeOfRings.{t, t + 1, max u (t + 1)} α
      ((constantModules.{t, u} k R).obj M)).val.obj U :=
  (((PresheafOfModules.sheafificationAdjunction.{max u (t + 1), t, max u (t + 1), t + 1}
      (𝟙 (ring.{t, u} k B).obj)).unit.app
    (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)} α
      ((constantModules.{t, u} k R).obj M))).app U)
      (b ⊗ₜ[(constantRing.{t, u} k R).obj.obj U, (α.hom.app U).hom]
        constantElement.{t, u} k R M U x)

/-- Termwise application of the specified additive extension or sections functor.
Source: Stacks 0A8X (blueprint: lem-pod-point-derived-hom-evaluation). -/
abbrev sectionComplex := (sections.{t, u} k B α).mapHomologicalComplex (.up ℤ)

/-- The recorded internal Hom complex, with all module and site universes explicit.
Source: Stacks 0A8X (blueprint: lem-pod-point-derived-hom-evaluation). -/
abbrev sheafHom (P I : CochainComplex (Modules.{t, u} k B) ℤ) :=
  homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := B) P I

/-- The recorded product projection evaluated on the identity slice.
Source: Stacks 0A8X (blueprint: lem-pod-point-derived-hom-evaluation). -/
abbrev homValue := IntegralHom.evaluate.{t, u} (Spec (.of k)) B

/-- The recorded ordinary direct-sum total tensor on the same small site.
Source: Stacks 06YL (blueprint: lem-pod-point-derived-hom-evaluation). -/
abbrev total (P Q : CochainComplex (Modules.{t, u} k B) ℤ) :=
  ((IntegralHom.totalTensor.{t, u} (Spec (.of k)) B).obj P).obj Q

/-- The recorded insertion of local homogeneous pure tensors into the total complex.
Source: Stacks 06YL (blueprint: lem-pod-point-derived-hom-evaluation). -/
abbrev totalElement := IntegralHom.totalPair.{t, u} (Spec (.of k)) B

section
variable {A : Type r} [CommRing A]

/-- The ordinary module total tensor, using the same totalization convention.
Source: Stacks 06YL (blueprint: lem-pod-point-derived-hom-evaluation). -/
abbrev moduleTotal (P Q : CochainComplex (ModuleCat.{r} A) ℤ) :=
  CochainComplex.mapBifunctor P Q (curriedTensor _)

/-- A pure module tensor in its total degree.
Source: Stacks 06YL (blueprint: lem-pod-point-derived-hom-evaluation). -/
def moduleTotalElement (P Q : CochainComplex (ModuleCat.{r} A) ℤ)
    (p j : ℤ) (x : P.X p) (y : Q.X j) : (moduleTotal P Q).X (p + j) :=
  (CochainComplex.ιMapBifunctor P Q (curriedTensor _) p j (p + j) rfl).hom (x ⊗ₜ[A] y)

end

/-- Standard derived-category localization of sheaf modules.
Source: Stacks 05RU (blueprint: lem-pod-point-derived-hom-evaluation). -/
instance derivedSheaves : HasDerivedCategory (Modules.{t, u} k B) := HasDerivedCategory.standard _

/-- Standard derived-category localization of ordinary modules.
Source: Stacks 05RU (blueprint: lem-pod-point-derived-hom-evaluation). -/
instance derivedModules (A : Type r) [CommRing A] : HasDerivedCategory (ModuleCat.{r} A) :=
  HasDerivedCategory.standard _

/-- Restriction from the final object to an arbitrary object of the small site.
Source: Stacks 03CW (blueprint: lem-pod-point-derived-hom-evaluation). -/
def toFinal (U : Scheme.ProEt (Spec (.of k))) : U ⟶ finalObject k :=
  MorphismProperty.Over.homMk U.hom

/-- The actual extension object, with the coefficient-size sheafification fixed.
Source: Stacks 03EK (blueprint: lem-pod-point-derived-hom-evaluation). -/
def extensionObject (M : ModuleCat.{max u (t + 1)} R) : Modules.{t, u} k B :=
  letI := abSheafify.{t, u} k
  letI := abLocallyBijective.{t, u} k
  SheafOfModules.changeOfRings.{t, t + 1, max u (t + 1)} α
    ((constantModules.{t, u} k R).obj M)

/-- Tensor scalar extension of the actual constant-module morphism.
Source: Stacks 03EK (blueprint: lem-pod-point-derived-hom-evaluation). -/
def extensionMorphism {M N : ModuleCat.{max u (t + 1)} R} (f : M ⟶ N) :
    extensionObject.{t, u} k B α M ⟶ extensionObject.{t, u} k B α N :=
  letI := abSheafify.{t, u} k
  letI := abLocallyBijective.{t, u} k
  SheafOfModules.changeOfRingsHom.{t, t + 1, max u (t + 1)} α
    ((constantModules.{t, u} k R).obj M) ((constantModules.{t, u} k R).map f)

variable (L : ModuleCat.{max u (t + 1)} R ⥤ Modules.{t, u} k B)
  (hobj : ∀ M : ModuleCat.{max u (t + 1)} R,
    L.obj M = extensionObject.{t, u} k B α M)
  (adj : L ⊣ sections.{t, u} k B α)

/-- The specified extension applied termwise; additivity follows from the assumed adjunction.
Source: Stacks 0A8X (blueprint: lem-pod-point-derived-hom-evaluation). -/
def extensionComplex : CochainComplex (ModuleCat.{max u (t + 1)} R) ℤ ⥤
    CochainComplex (Modules.{t, u} k B) ℤ :=
  letI := adj.left_adjoint_additive
  L.mapHomologicalComplex (.up ℤ)

/-- The local tensor generator in the strictly specified extension functor.
The equality hobj identifies the actual tensor construction, not an arbitrary isomorphic object.
Source: Stacks 03EK (blueprint: lem-pod-point-derived-hom-evaluation). -/
def generator (M : ModuleCat.{max u (t + 1)} R)
    (U : (Scheme.ProEt (Spec (.of k)))ᵒᵖ) (b : B.obj.obj U) (x : M) :
    (L.obj M).val.obj U :=
  (eqToHom (hobj M).symm).val.app U (extensionElement.{t, u} k B α M U b x)

/-- The stated explicit adjunction, in both directions and on every local tensor generator.
Source: Stacks 03CY and 03EK (blueprint: lem-pod-point-derived-hom-evaluation). -/
def ExplicitAdjunction : Prop :=
  (∀ (M : ModuleCat.{max u (t + 1)} R) (V : Modules.{t, u} k B) (h : L.obj M ⟶ V) (x : M),
    (adj.homEquiv M V h).hom x =
      h.val.app (op (finalObject k)) (generator.{t, u} k B α L hobj M (op (finalObject k)) 1 x)) ∧
  (∀ (M : ModuleCat.{max u (t + 1)} R) (V : Modules.{t, u} k B)
    (f : M ⟶ (sections.{t, u} k B α).obj V) (U : (Scheme.ProEt (Spec (.of k)))ᵒᵖ)
    (b : B.obj.obj U) (x : M),
    ((adj.homEquiv M V).symm f).val.app U (generator.{t, u} k B α L hobj M U b x) =
      b • V.val.map (toFinal k U.unop).op (f.hom x))

variable (c : CochainComplex (ModuleCat.{max u (t + 1)} R) ℤ)
  (I : CochainComplex (Modules.{t, u} k B) ℤ)

/-- The normalization that uniquely specifies q on every homogeneous component.
Source: Stacks 0A8X (blueprint: lem-pod-point-derived-hom-evaluation). -/
def IsComparison
    (q : (sectionComplex.{t, u} k B α).obj
      (sheafHom.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c) I) ≅
      CochainComplex.moduleHomComplex c ((sectionComplex.{t, u} k B α).obj I)) : Prop :=
  ∀ (j p : ℤ)
    (h : ((sectionComplex.{t, u} k B α).obj
      (sheafHom.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c) I)).X j) (x : c.X p),
    (((q.hom.f j).hom h).v p (p + j) rfl).hom x =
      homValue.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c) I j p (op (finalObject k)) h
        (generator.{t, u} k B α L hobj (c.X p) (op (finalObject k)) 1 x)

/-- Naturality of the normalized comparison under arbitrary maps of both complexes.
Source: Stacks 0A8X (blueprint: lem-pod-point-derived-hom-evaluation). -/
def ComparisonNatural
    (q : (sectionComplex.{t, u} k B α).obj
      (sheafHom.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c) I) ≅
      CochainComplex.moduleHomComplex c ((sectionComplex.{t, u} k B α).obj I)) : Prop :=
  ∀ (c' : CochainComplex (ModuleCat.{max u (t + 1)} R) ℤ)
    (I' : CochainComplex (Modules.{t, u} k B) ℤ) (f : c' ⟶ c) (g : I ⟶ I')
    (q' : (sectionComplex.{t, u} k B α).obj
      (sheafHom.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c') I') ≅
        CochainComplex.moduleHomComplex c' ((sectionComplex.{t, u} k B α).obj I')),
    IsComparison.{t, u} k B α L hobj adj c' I' q' → ∀ (j p : ℤ)
      (h : ((sectionComplex.{t, u} k B α).obj
        (sheafHom.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c) I)).X j) (x : c'.X p),
      (((q'.hom.f j).hom
        ((((sectionComplex.{t, u} k B α).map
          (((homComplexFunctor.{t + 1, t, max u (t + 1), max u (t + 1)}
            (R := B)).map ((extensionComplex.{t, u} k B α L adj).map f).op).app I ≫
            ((homComplexFunctor.{t + 1, t, max u (t + 1), max u (t + 1)}
              (R := B)).obj
              (op ((extensionComplex.{t, u} k B α L adj).obj c'))).map g)).f j).hom h)).v
                p (p + j) rfl).hom x =
        ((((sectionComplex.{t, u} k B α).map g).f (p + j)).hom
          ((((q.hom.f j).hom h).v p (p + j) rfl).hom ((f.f p).hom x)))

/-- The constant-value map R to sections of the coefficient unit, as an R-linear morphism.
Source: Stacks 03CW (blueprint: lem-pod-point-derived-hom-evaluation). -/
def coefficientSections : ModuleCat.of R R ⟶
    (sections.{t, u} k B α).obj (SheafOfModules.unit (ring.{t, u} k B)) :=
  ModuleCat.ofHom (X := ModuleCat.of R R)
    (Y := (sections.{t, u} k B α).obj (SheafOfModules.unit (ring.{t, u} k B)))
    { toFun := scalar.{t, u} k B α (op (finalObject k))
      map_add' := map_add _
      map_smul' := by
        intro a b
        change scalar.{t, u} k B α (op (finalObject k)) (a * b) =
          scalar.{t, u} k B α (op (finalObject k)) a *
            scalar.{t, u} k B α (op (finalObject k)) b
        exact map_mul _ a b }

/-- The specified augmentation R[0] to sections of the K-injective resolution.
Source: Stacks 08BJ (blueprint: lem-pod-point-derived-hom-evaluation). -/
def sectionResolution
    (iota : (CochainComplex.singleFunctor (Modules.{t, u} k B) 0).obj
      (SheafOfModules.unit (ring.{t, u} k B)) ⟶ I) :
    (CochainComplex.singleFunctor (ModuleCat.{max u (t + 1)} R) 0).obj
      (ModuleCat.of R R) ⟶ (sectionComplex.{t, u} k B α).obj I :=
  (CochainComplex.singleFunctor _ 0).map (coefficientSections.{t, u} k B α) ≫
    ((sections.{t, u} k B α).mapCochainComplexSingleFunctor 0).inv.app _ ≫
      (sectionComplex.{t, u} k B α).map iota

/-- Compatibility of the three specified chain maps, including the Koszul sign.
The maps are determined on local tensor generators, not supplied as arbitrary hypotheses.
Source: blueprint point comparison, Stacks 08J7 and 0A8X
(blueprint: lem-pod-point-derived-hom-evaluation). -/
def EvaluationCompatible
    (q : (sectionComplex.{t, u} k B α).obj
      (sheafHom.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c) I) ≅
        CochainComplex.moduleHomComplex c ((sectionComplex.{t, u} k B α).obj I)) : Prop :=
  ∃ (eB : total.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c)
      (sheafHom.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c) I) ⟶ I)
    (beta : moduleTotal c ((sectionComplex.{t, u} k B α).obj
      (sheafHom.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c) I)) ⟶
        (sectionComplex.{t, u} k B α).obj (total.{t, u} k B
          ((extensionComplex.{t, u} k B α L adj).obj c)
          (sheafHom.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c) I)))
    (eR : moduleTotal c
      (CochainComplex.moduleHomComplex c ((sectionComplex.{t, u} k B α).obj I)) ⟶
        (sectionComplex.{t, u} k B α).obj I),
    (∀ (p j : ℤ) (U : (Scheme.ProEt (Spec (.of k)))ᵒᵖ)
      (y : (((extensionComplex.{t, u} k B α L adj).obj c).X p).val.obj U)
      (h : ((sheafHom.{t, u} k B
        ((extensionComplex.{t, u} k B α L adj).obj c) I).X j).val.obj U),
      (eB.f (p + j)).val.app U (totalElement.{t, u} k B
        ((extensionComplex.{t, u} k B α L adj).obj c)
        (sheafHom.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c) I) p j U y h) =
          (p * j).negOnePow • homValue.{t, u} k B
            ((extensionComplex.{t, u} k B α L adj).obj c) I j p U h y) ∧
    (∀ (p j : ℤ) (x : c.X p)
      (h : ((sectionComplex.{t, u} k B α).obj
        (sheafHom.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c) I)).X j),
      (beta.f (p + j)).hom (moduleTotalElement c
        ((sectionComplex.{t, u} k B α).obj
          (sheafHom.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c) I)) p j x h) =
        totalElement.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c)
          (sheafHom.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c) I)
          p j (op (finalObject k))
          (generator.{t, u} k B α L hobj (c.X p) (op (finalObject k)) 1 x) h) ∧
    (∀ (p j : ℤ) (x : c.X p)
      (h : (CochainComplex.moduleHomComplex c ((sectionComplex.{t, u} k B α).obj I)).X j),
      (eR.f (p + j)).hom (moduleTotalElement c
        (CochainComplex.moduleHomComplex c ((sectionComplex.{t, u} k B α).obj I)) p j x h) =
          (p * j).negOnePow • (h.v p (p + j) rfl).hom x) ∧
    beta ≫ (sectionComplex.{t, u} k B α).map eB =
      (((curriedTensor (ModuleCat.{max u (t + 1)} R)).map₂CochainComplex.obj c).map q.hom) ≫ eR

variable [PreservesFiniteLimits (sections.{t, u} k B α)]
  [PreservesFiniteColimits (sections.{t, u} k B α)]

/-- The canonical map from the sections of a Hom representative to sections of derived Hom.
It uses the fixed K-injective replacement comparison and the given augmentation iota.
Source: Stacks 08J7 (blueprint: lem-pod-point-derived-hom-evaluation). -/
def derivedModelMap
    (iota : (CochainComplex.singleFunctor (Modules.{t, u} k B) 0).obj
      (SheafOfModules.unit (ring.{t, u} k B)) ⟶ I) [QuasiIso iota] :
    DerivedCategory.Q.obj ((sectionComplex.{t, u} k B α).obj
      (sheafHom.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c) I)) ⟶
        (sections.{t, u} k B α).mapDerivedCategory.obj
          ((derivedInternalHomOfUniverses.{t + 1, t, u}
            (Scheme.ProEt.topology (Spec (.of k))) B).obj
            (op (DerivedCategory.Q.obj ((extensionComplex.{t, u} k B α L adj).obj c)),
              DerivedCategory.Q.obj ((CochainComplex.singleFunctor (Modules.{t, u} k B) 0).obj
                (SheafOfModules.unit (ring.{t, u} k B))))) :=
  (sections.{t, u} k B α).mapDerivedCategoryFactors.inv.app _ ≫
    (sections.{t, u} k B α).mapDerivedCategory.map
      (IntegralHom.homModelMap.{t, u} (Spec (.of k)) B
        ((extensionComplex.{t, u} k B α L adj).obj c) I) ≫
    (sections.{t, u} k B α).mapDerivedCategory.map
      ((derivedInternalHomOfUniverses.{t + 1, t, u}
        (Scheme.ProEt.topology (Spec (.of k))) B).map
          (CategoryTheory.Prod.mkHom (𝟙 _) (inv (DerivedCategory.Q.map iota))))

/-- The complete conclusion, with the derived isomorphism forced by the chain comparison.
The right-hand Hom complex computes RHom_R(c,R) because sectionResolution is K-injective.
Source: blueprint point comparison, Stacks 08J7 and 08BJ
(blueprint: lem-pod-point-derived-hom-evaluation). -/
def ComparisonResult
    (iota : (CochainComplex.singleFunctor (Modules.{t, u} k B) 0).obj
      (SheafOfModules.unit (ring.{t, u} k B)) ⟶ I) [QuasiIso iota] : Prop :=
  CochainComplex.IsKInjective ((sectionComplex.{t, u} k B α).obj I) ∧
    QuasiIso (sectionResolution.{t, u} k B α I iota) ∧
    CochainComplex.IsKFlatIndependentCoefficients (R := B)
      ((extensionComplex.{t, u} k B α L adj).obj c) ∧
    ∃ q : (sectionComplex.{t, u} k B α).obj
        (sheafHom.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c) I) ≅
          CochainComplex.moduleHomComplex c ((sectionComplex.{t, u} k B α).obj I),
      IsComparison.{t, u} k B α L hobj adj c I q ∧
      ComparisonNatural.{t, u} k B α L hobj adj c I q ∧
      EvaluationCompatible.{t, u} k B α L hobj adj c I q ∧
      ∃ d : (sections.{t, u} k B α).mapDerivedCategory.obj
          ((derivedInternalHomOfUniverses.{t + 1, t, u}
            (Scheme.ProEt.topology (Spec (.of k))) B).obj
            (op (DerivedCategory.Q.obj ((extensionComplex.{t, u} k B α L adj).obj c)),
              DerivedCategory.Q.obj ((CochainComplex.singleFunctor (Modules.{t, u} k B) 0).obj
                (SheafOfModules.unit (ring.{t, u} k B))))) ≅
          DerivedCategory.Q.obj
            (CochainComplex.moduleHomComplex c ((sectionComplex.{t, u} k B α).obj I)),
        derivedModelMap.{t, u} k B α L adj c I iota ≫ d.hom = DerivedCategory.Q.map q.hom

omit [PreservesFiniteLimits (sections.{t, u} k B α)]
  [PreservesFiniteColimits (sections.{t, u} k B α)] in
/-- The node's hypotheses and conclusion for a fixed actual coefficient model.
Objects and maps of L are rigidly specified as tensor scalar extension of constant modules.
Source: blueprint point comparison (blueprint: lem-pod-point-derived-hom-evaluation). -/
def Statement : Prop :=
  ∀ (L : ModuleCat.{max u (t + 1)} R ⥤ Modules.{t, u} k B)
    (hobj : ∀ M : ModuleCat.{max u (t + 1)} R,
      L.obj M = extensionObject.{t, u} k B α M)
    (_hmap : ∀ {M N : ModuleCat.{max u (t + 1)} R} (f : M ⟶ N),
      L.map f = eqToHom (hobj M) ≫ extensionMorphism.{t, u} k B α f ≫
          eqToHom (hobj N).symm)
    (adj : L ⊣ sections.{t, u} k B α),
    ExplicitAdjunction.{t, u} k B α L hobj adj →
    ∀ [PreservesFiniteLimits L] [PreservesFiniteColimits L]
      [PreservesFiniteLimits (sections.{t, u} k B α)]
      [PreservesFiniteColimits (sections.{t, u} k B α)],
    Function.Bijective (scalar.{t, u} k B α (op (finalObject k))) →
    ∀ (c : CochainComplex (ModuleCat.{max u (t + 1)} R) ℤ),
    (∀ F : CochainComplex (ModuleCat.{max u (t + 1)} R) ℤ,
      F.Acyclic → (moduleTotal F c).Acyclic) →
    (∀ p : ℤ, Module.Flat R (c.X p)) →
    ∀ (I : CochainComplex (Modules.{t, u} k B) ℤ) [CochainComplex.IsKInjective I]
      (iota : (CochainComplex.singleFunctor (Modules.{t, u} k B) 0).obj
        (SheafOfModules.unit (ring.{t, u} k B)) ⟶ I) [QuasiIso iota],
      ComparisonResult.{t, u} k B α L hobj adj c I iota

section Coefficients

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- false denotes finite coefficients at exponent n, true denotes integral coefficients.
The ULift changes only size, and imposes no relation between field and coefficient universes.
Source: blueprint point comparison (blueprint: lem-pod-point-derived-hom-evaluation). -/
def coefficientRing (n : ℕ) : Bool → CommRingCat.{max u (t + 1)}
  | false => .of (ULift.{t + 1} (Padic.coefficientExtensionRing l E n))
  | true => .of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))

/-- The two actual coefficient sheaves of the node: discrete constant or completed integral.
Source: blueprint point comparison (blueprint: lem-pod-point-derived-hom-evaluation). -/
def coefficientSheaf (n : ℕ) : Bool →
    Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{max u (t + 1)}
  | false => constantRing.{t, u} k (coefficientRing.{t, u} l E n false)
  | true => completedIntegralCommRingSheafUnrestricted l E (Spec (.of k))

/-- The constant-to-coefficient map: identity at finite level and the canonical limit lift
at integral level. Source: blueprint point comparison, Stacks 03CO
(blueprint: lem-pod-point-derived-hom-evaluation). -/
def coefficientMap (n : ℕ) (integral : Bool) :
    constantRing.{t, u} k (coefficientRing.{t, u} l E n integral) ⟶
      coefficientSheaf.{t, u} k l E n integral :=
  match integral with
  | false => 𝟙 _
  | true =>
    { hom :=
        { app := fun U ↦
            letI := completedIntegralCoefficientCommRingUnrestricted l E (Spec (.of k)) U
            CommRingCat.ofHom
            (show (constantRing.{t, u} k (coefficientRing.{t, u} l E n true)).obj.obj U →+*
              (completedIntegralCommRingSheafUnrestricted l E (Spec (.of k))).obj.obj U from
              ((integralConstantToCompletionOfUniverses.{t, u}
                l E (Spec (.of k))).hom.app U).hom)
          naturality := fun _U _V f ↦ (forget₂ CommRingCat RingCat).map_injective
            ((integralConstantToCompletionOfUniverses l E (Spec (.of k))).hom.naturality f) } }

end Coefficients

/-- Derived sections-Hom comparison for both coefficient models at the geometric point.
Source: blueprint main-20261015, lem-pod-point-dualizing-complex.proof.md, second sentence;
Stacks sites-cohomology Tags 0G7E, 0A8X, 08J7, 0A95 and 0FPT, derived Tag 08BJ,
and sites Tag 00WJ (blueprint: lem-pod-point-derived-hom-evaluation).

Proof: constant sheafification is the finite-limit-preserving inverse image of the
geometric morphism to sets. Tensor extension is its module pullback, so a flat-term
K-flat complex remains K-flat by lem-weil-pbc-ringed-topoi-derived-tensor-pullback.
In each Hom degree apply the assumed explicit adjunction to every product factor.
Evaluation at 1 tensor x gives q; its inverse sends t to b tensor x mapped to b t(x).
The differential d_I h - (-1)^j h d_c commutes with this formula, and pre- and
post-composition prove naturality. The exact-left-adjoint lemma
lem-weil-pbc-right-adjoint-preserves-kinjective makes sections of I K-injective.
Exact sections preserve the resolution quasi-isomorphism; the bijective constant-value
map identifies its degree-zero source with R. Thus this is a K-injective resolution
of R. The derived-internal-Hom representative comparison and exact sections descend q
to the specified derived isomorphism; lem-pur-rhom-well-defined gives independence of
representatives. Evaluation with the argument first is the ordinary Hom counit
preceded by symmetry, so on bidegree (p,j) it is (-1)^(p*j) h(y). Its differential
identity follows by cancellation of the two h(dy) terms. Define beta on each total
summand by x tensor h mapped to (1 tensor x) tensor h. Balancing, restriction and
the tensor differential give a chain map without commuting sections with coproducts.
Both composites evaluate to (-1)^(p*j) h(1 tensor x). Pure tensors generate each
module summand, proving the chain-map equality and hence the derived evaluation square.
All tensors are ordinary; this makes no completed-tensor assertion. -/
theorem point_derived_hom_evaluation (D : FiniteFieldDatum.{t})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (_hn : 1 ≤ n) (integral : Bool) :
    Statement.{t, u} D.k
      (coefficientSheaf.{t, u} D.k l E n integral)
      (coefficientMap.{t, u} D.k l E n integral) := by
  sorry

end WeilConjectures.PointDerivedHom
