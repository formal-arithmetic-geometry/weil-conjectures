/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomNativeClosed
public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
public import WeilConjectures.CategoryTheory.Sites.FixedCoefficientDerivedChangeOfRings
public import WeilConjectures.CategoryTheory.SixFunctors.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
public import WeilConjectures.CategoryTheory.SmoothPurity.QuasiIsoHomComplexMapMixedUniverses
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleIntrinsic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal

/-! # General constructible internal Hom and finite coefficient change

Source: latest blueprint `part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
thm-coef-finite-hom.md`, statement, and its eight-step DAG proof
(blueprint: thm-coef-finite-hom).

All categories below are ordinary derived categories of constant-coefficient module
sheaves on the specified small site. Tensor comparison data are constrained by the
ordinary balancing formula on cochain representatives, and are asserted to exist in
the conclusion, never assumed as free input to the theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry
namespace WeilConjectures
namespace GeneralFiniteHom

/-- The pro-étale site is small in its own object universe; use the explicit zero
lift in the existing smallness theorem to avoid an undetermined larger universe.
Source: Mathlib essentiallySmallSelf (blueprint: thm-coef-finite-hom). -/
instance proSmall (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0} _
attribute [local instance 5000] proSmall

section Site
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C)

/-- Constant-coefficient module sheaves. Source: thm-coef-finite-hom, opening setting.
(blueprint: thm-coef-finite-hom). -/
abbrev finiteHomModules (A : Type (u + 1)) [CommRing A] :=
  Sheaf J (ModuleCat.{u + 1} A)

/-- The ordinary uncompleted derived category. Source: thm-coef-finite-hom, setting.
(blueprint: thm-coef-finite-hom). -/
abbrev finiteHomDerived (A : Type (u + 1)) [CommRing A] :=
  DerivedCategory.{u + 1} (finiteHomModules J A)

/-- The recorded K-injective derived internal Hom with its native closed structure.
Source: thm-coef-finite-hom, evaluation paragraph (blueprint: thm-coef-finite-hom). -/
abbrev finiteHomClosedAt (A : Type (u + 1)) [CommRing A] :=
  finiteHomNativeDerivedClosed.{u + 2, u + 1, u + 1} (finiteHomModules J A)

/-- The dependency's canonical K-flat derived scalar extension.
Source: Stacks 06YY; thm-coef-finite-hom (blueprint: thm-coef-finite-hom). -/
abbrev finiteHomScalar {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) :=
  Sheaf.fixedCoefficientDerivedScalarExtension.{u} J φ

/-- Its defining adjunction to the actual exact restriction of scalars.
Source: Stacks 06YY (blueprint: thm-coef-finite-hom). -/
def finiteHomScalarAdjunction {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) : finiteHomScalar J φ ⊣ Sheaf.derivedRestrictScalars.{u} J φ :=
  letI := Sheaf.fixedCoefficientDerivedRestriction_isRightAdjoint.{u} J φ
  Adjunction.ofIsRightAdjoint _

/-- The ordinary scalar extension, the left adjoint to sectionwise restriction.
Source: Stacks 03EK (blueprint: thm-coef-finite-hom). -/
abbrev finiteHomOrdinaryScalar {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) := Sheaf.extendScalars J φ

/-- The ordinary balancing tensorator is transported through sheafification.
Source: Stacks 07A4 (blueprint: thm-coef-finite-hom). -/
local instance finiteHomOrdinaryOplax {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) : (finiteHomOrdinaryScalar J φ).OplaxMonoidal :=
  composeAndSheafifyOplaxMonoidal J (ModuleCat.extendRestrictScalarsAdj.{u + 1} φ)

/-- Scalar extension is additive, by its ordinary adjunction.
Source: Stacks 03EK (blueprint: thm-coef-finite-hom). -/
local instance finiteHomOrdinaryAdditive {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) : (finiteHomOrdinaryScalar J φ).Additive :=
  (Sheaf.extendScalarsAdjunction J φ).left_adjoint_additive

/-- The representative comparison is the transpose of the ordinary scalar unit.
Source: Stacks 06YY (blueprint: thm-coef-finite-hom). -/
def finiteHomScalarRepresentative {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (P : CochainComplex (finiteHomModules J A) ℤ) :
    (finiteHomScalar J φ).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((finiteHomOrdinaryScalar J φ).mapHomologicalComplex (.up ℤ)).obj P) :=
  AlgebraicGeometry.Etale.scalarAdjunctionRepresentativeMap
    (finiteHomOrdinaryScalar J φ) (Sheaf.restrictScalars J φ)
    (Sheaf.extendScalarsAdjunction J φ) (finiteHomScalar J φ)
    (finiteHomScalarAdjunction J φ) P

/-- A simultaneous family of scalar tensor comparisons, with every component fixed
by ordinary balancing on representatives. No categories, Hom functors, scalar functors
or constructibility predicates are fields.
Source: thm-coef-finite-hom, evaluation construction (blueprint: thm-coef-finite-hom). -/
structure FiniteHomSystem where
  tensorComparison : ∀ {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B),
    (finiteHomClosedAt J A).tensor ⋙ finiteHomScalar J φ ≅
      (finiteHomScalar J φ).prod (finiteHomScalar J φ) ⋙ (finiteHomClosedAt J B).tensor
  canonical : ∀ {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B),
    AlgebraicGeometry.Etale.ExceptionalCoefficients.TensorNormalizationAux
      (finiteHomOrdinaryScalar J φ) (finiteHomScalar J φ)
      (finiteHomScalarRepresentative J φ) (tensorComparison φ)

/-- The unique tensor-Hom transpose of changed evaluation.
Source: thm-coef-finite-hom, first paragraph (blueprint: thm-coef-finite-hom). -/
def finiteHomComparison (S : FiniteHomSystem J)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    (K M : finiteHomDerived J A) :=
  coefficientBaseChangeHom (finiteHomClosedAt J A) (finiteHomClosedAt J B)
    (finiteHomScalar J φ) (S.tensorComparison φ) K M

/-- Naturality, all transpose/evaluation equations, and internal composition.
Source: thm-coef-finite-hom, step 7 (blueprint: thm-coef-finite-hom). -/
def FiniteHomEvaluationLaws (S : FiniteHomSystem J) : Prop :=
  ∀ {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B),
    CoefficientEvaluationCompatible (finiteHomClosedAt J A) (finiteHomClosedAt J B)
      (finiteHomScalar J φ) (S.tensorComparison φ)

/-- Successive extension uses the canonical adjunction mate of exact scalar restriction.
Source: Stacks 06YY; thm-coef-finite-hom, step 7 (blueprint: thm-coef-finite-hom). -/
def finiteHomScalarComp {A B D : Type (u + 1)}
    [CommRing A] [CommRing B] [CommRing D] (φ : A →+* B) (ψ : B →+* D) :
    finiteHomScalar J φ ⋙ finiteHomScalar J ψ ≅ finiteHomScalar J (ψ.comp φ) :=
  Adjunction.leftAdjointCompIso (finiteHomScalarAdjunction J φ)
    (finiteHomScalarAdjunction J ψ) (finiteHomScalarAdjunction J (ψ.comp φ))
    (Sheaf.derivedRestrictScalarsCompIso.{u} J (f := φ) (g := ψ) rfl)

/-- The coefficient-chain formula with the canonical successive-scalar isomorphism.
Source: thm-coef-finite-hom, step 7 (blueprint: thm-coef-finite-hom). -/
def FiniteHomTowerLaws (S : FiniteHomSystem J) : Prop :=
  ∀ {A B D : Type (u + 1)} [CommRing A] [CommRing B] [CommRing D]
    (φ : A →+* B) (ψ : B →+* D) (K M : finiteHomDerived J A),
    (finiteHomScalarComp J φ ψ).hom.app
        ((finiteHomDerivedInternalHomGeneral.{u + 2, u + 1, u + 1}
          (finiteHomModules J A)).obj (op K, M)) ≫
      finiteHomComparison J S (ψ.comp φ) K M =
    (finiteHomScalar J ψ).map (finiteHomComparison J S φ K M) ≫
      finiteHomComparison J S ψ ((finiteHomScalar J φ).obj K) ((finiteHomScalar J φ).obj M) ≫
      (finiteHomDerivedInternalHomGeneral.{u + 2, u + 1, u + 1}
        (finiteHomModules J D)).map
        (Prod.mkHom ((finiteHomScalarComp J φ ψ).inv.app K).op
          ((finiteHomScalarComp J φ ψ).hom.app M))

/-- The identity restriction is the identity on every section.
Source: thm-coef-finite-hom, canonical comparison construction
(blueprint: thm-coef-finite-hom). -/
def finiteHomRestrictionIdentity (A : Type (u + 1)) [CommRing A] :
    Sheaf.restrictScalars.{u + 1, u, u + 1} J (RingHom.id A) ≅
      𝟭 (finiteHomModules J A) :=
  NatIso.ofComponents (fun M ↦ (fullyFaithfulSheafToPresheaf J _).preimageIso
    (Functor.isoWhiskerLeft M.obj (ModuleCat.restrictScalarsId A) ≪≫
      Functor.rightUnitor M.obj)) (by intros; ext U x; rfl)

/-- The scalar identity isomorphism is fixed by the actual scalar adjunction.
Source: thm-coef-finite-hom, canonical comparison construction
(blueprint: thm-coef-finite-hom). -/
def finiteHomScalarIdentity (A : Type (u + 1)) [CommRing A] :
    finiteHomScalar J (RingHom.id A) ≅ 𝟭 (finiteHomDerived J A) :=
  Adjunction.leftAdjointIdIso (finiteHomScalarAdjunction J (RingHom.id A))
    (Functor.mapDerivedCategoryNatIso (finiteHomRestrictionIdentity J A) ≪≫
      Functor.mapDerivedCategoryIdIso _)

/-- The identity coefficient formula, under its canonical adjunction identification.
Source: thm-coef-finite-hom, canonical comparison construction
(blueprint: thm-coef-finite-hom). -/
def FiniteHomIdentityLaws (S : FiniteHomSystem J) : Prop :=
  ∀ (A : Type (u + 1)) [CommRing A] (K M : finiteHomDerived J A),
    finiteHomComparison J S (RingHom.id A) K M ≫
      (finiteHomDerivedInternalHomGeneral.{u + 2, u + 1, u + 1}
        (finiteHomModules J A)).map
        (Prod.mkHom ((finiteHomScalarIdentity J A).inv.app K).op
          ((finiteHomScalarIdentity J A).hom.app M)) =
      (finiteHomScalarIdentity J A).hom.app
        ((finiteHomDerivedInternalHomGeneral.{u + 2, u + 1, u + 1}
          (finiteHomModules J A)).obj (op K, M))

/-- Invertibility and both finite-Tor constructible endpoints for a specified predicate.
The final theorem supplies the actual intrinsic predicates on each small site.
Source: thm-coef-finite-hom, canonical comparison construction
(blueprint: thm-coef-finite-hom). -/
def FiniteHomCtfConclusion (S : FiniteHomSystem J) (ell : ℕ)
    (ctf : ∀ (A : Type (u + 1)) [CommRing A] [Finite A],
      ObjectProperty (finiteHomDerived J A)) : Prop :=
  ∀ (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B],
    (∃ n : ℕ, (ell : A) ^ n = 0) → (∃ n : ℕ, (ell : B) ^ n = 0) →
    ∀ (φ : A →+* B) (K M : finiteHomDerived J A), ctf A K → ctf A M →
      ctf B ((finiteHomScalar J φ).obj
        ((finiteHomDerivedInternalHomGeneral.{u + 2, u + 1, u + 1}
          (finiteHomModules J A)).obj (op K, M))) ∧
      ctf B ((finiteHomDerivedInternalHomGeneral.{u + 2, u + 1, u + 1}
        (finiteHomModules J B)).obj
        (op ((finiteHomScalar J φ).obj K), (finiteHomScalar J φ).obj M)) ∧
      IsIso (finiteHomComparison J S φ K M)

end Site

/-- The bounded constructible finite-Tor predicate on the actual small étale site.
Source: thm-coef-finite-hom, setting (blueprint: thm-coef-finite-hom). -/
def finiteHomEtaleCtf (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A] :
    ObjectProperty (finiteHomDerived.{u} X.smallEtaleTopology A) :=
  Etale.DerivedCategory.isBoundedConstructible A X ⊓
    fun K ↦ ∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn A X a b K

/-- Intrinsic bounded constructibility and Tor amplitude on the actual pro-étale site.
Source: thm-coef-finite-hom, setting (blueprint: thm-coef-finite-hom). -/
def finiteHomProEtaleCtf (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A] :
    ObjectProperty (finiteHomDerived.{u} (Scheme.ProEt.topology X) A) :=
  ProEtale.DerivedCategory.boundedConstructibleIntrinsic A X ⊓
    DerivedCategory.finiteTorAmplitude _

/-- The actual exact comparison inverse image, with its constant scalar action.
Source: thm-coef-finite-hom, step 8 (blueprint: thm-coef-finite-hom). -/
abbrev finiteHomNu (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory

/-- The canonical commutation of site inverse image and scalar restriction.
It is the conjugate of sectionwise commutation with scalar coextension.
Source: thm-coef-finite-hom, site comparisons; Stacks 03D2.
Source: thm-coef-finite-hom, canonical comparison construction
(blueprint: thm-coef-finite-hom). -/
def finiteHomOrdinarySiteRestriction (X : Scheme.{u})
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) :
    ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X ⋙
        Sheaf.restrictScalars (Scheme.ProEt.topology X) φ ≅
      Sheaf.restrictScalars X.smallEtaleTopology φ ⋙
        ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X :=
  ((conjugateIsoEquiv
    ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) X).comp
      (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology X) φ))
    ((Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).comp
      (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) X))).symm (Iso.refl _)).symm

/-- Exact descent of the actual site/restriction comparison.
Source: thm-coef-finite-hom, canonical comparison construction
(blueprint: thm-coef-finite-hom). -/
def finiteHomDerivedSiteRestriction (X : Scheme.{u})
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) :
    finiteHomNu X B ⋙ Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology X) φ ≅
      Sheaf.derivedRestrictScalars.{u} X.smallEtaleTopology φ ⋙ finiteHomNu X A :=
  (Functor.mapDerivedCategoryCompIso
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X)
    (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ)).symm ≪≫
  Functor.mapDerivedCategoryNatIso (finiteHomOrdinarySiteRestriction X φ) ≪≫
    Functor.mapDerivedCategoryCompIso (Sheaf.restrictScalars X.smallEtaleTopology φ)
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X)

/-- The site/scalar comparison is the mate of the actual exact restriction comparison.
Source: thm-coef-finite-hom, canonical comparison construction
(blueprint: thm-coef-finite-hom). -/
def finiteHomSiteScalarMap (X : Scheme.{u})
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) :
    finiteHomNu X A ⋙ finiteHomScalar.{u} (Scheme.ProEt.topology X) φ ⟶
      finiteHomScalar.{u} X.smallEtaleTopology φ ⋙ finiteHomNu X B :=
  ((mateEquiv (G := finiteHomNu X A) (H := finiteHomNu X B)
    (finiteHomScalarAdjunction.{u} X.smallEtaleTopology φ)
    (finiteHomScalarAdjunction.{u} (Scheme.ProEt.topology X) φ)).symm
    (TwoSquare.mk _ _ _ _ (finiteHomDerivedSiteRestriction X φ).inv)).natTrans


/-- Tensor comparison for the canonical site inverse image, fixed componentwise by
its published derived monoidal comparison; this is not an arbitrary site equivalence.
Source: thm-coef-finite-hom, final site-comparison clause.
Source: thm-coef-finite-hom, canonical comparison construction
(blueprint: thm-coef-finite-hom). -/
structure FiniteHomSiteComparisons (X : Scheme.{u}) where
  scalarComparison : ∀ {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B),
    finiteHomNu X A ⋙ finiteHomScalar.{u} (Scheme.ProEt.topology X) φ ≅
      finiteHomScalar.{u} X.smallEtaleTopology φ ⋙ finiteHomNu X B
  scalar_canonical : ∀ {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B),
    (scalarComparison φ).hom = finiteHomSiteScalarMap X φ
  tensorComparison : ∀ (A : Type (u + 1)) [CommRing A] [Finite A],
    (finiteHomClosedAt.{u} X.smallEtaleTopology A).tensor ⋙ finiteHomNu X A ≅
      (finiteHomNu X A).prod (finiteHomNu X A) ⋙
        (finiteHomClosedAt.{u} (Scheme.ProEt.topology X) A).tensor
  canonical : ∀ (A : Type (u + 1)) [CommRing A] [Finite A]
    (K M : finiteHomDerived.{u} X.smallEtaleTopology A),
    HEq ((tensorComparison A).hom.app (K, M))
      ((ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        (ModuleCat.{u + 1} A) K).hom.app M)

/-- Evaluation-defined internal-Hom site comparison.
Source: thm-coef-finite-hom, canonical comparison construction
(blueprint: thm-coef-finite-hom). -/
def finiteHomSiteMap {X : Scheme.{u}} (N : FiniteHomSiteComparisons X)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (K M : finiteHomDerived.{u} X.smallEtaleTopology A) :=
  coefficientBaseChangeHom (finiteHomClosedAt.{u} X.smallEtaleTopology A)
    (finiteHomClosedAt.{u} (Scheme.ProEt.topology X) A)
    (finiteHomNu X A) (N.tensorComparison A) K M

/-- The canonical scalar/site square on the evaluation-defined internal-Hom maps.
Source: thm-coef-finite-hom, canonical comparison construction
(blueprint: thm-coef-finite-hom). -/
def FiniteHomSiteSquare (X : Scheme.{u})
    (E : FiniteHomSystem X.smallEtaleTopology)
    (P : FiniteHomSystem (Scheme.ProEt.topology X))
    (N : FiniteHomSiteComparisons X) : Prop :=
  ∀ (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B)
    (K M : finiteHomDerived.{u} X.smallEtaleTopology A),
    (finiteHomScalar.{u} (Scheme.ProEt.topology X) φ).map (finiteHomSiteMap N A K M) ≫
      finiteHomComparison.{u} (Scheme.ProEt.topology X) P φ
        ((finiteHomNu X A).obj K) ((finiteHomNu X A).obj M) ≫
      (finiteHomDerivedInternalHomGeneral
        (finiteHomModules.{u} (Scheme.ProEt.topology X) B)).map
        (Prod.mkHom ((N.scalarComparison φ).inv.app K).op
          ((N.scalarComparison φ).hom.app M)) =
      (N.scalarComparison φ).hom.app
          ((finiteHomDerivedInternalHomGeneral
            (finiteHomModules.{u} X.smallEtaleTopology A)).obj (op K, M)) ≫
        (finiteHomNu X B).map (finiteHomComparison.{u} X.smallEtaleTopology E φ K M) ≫
        finiteHomSiteMap N B ((finiteHomScalar.{u} X.smallEtaleTopology φ).obj K)
          ((finiteHomScalar.{u} X.smallEtaleTopology φ).obj M)

end GeneralFiniteHom

open GeneralFiniteHom
attribute [local instance 5000] GeneralFiniteHom.proSmall


/-- General finite-coefficient internal Hom, on both actual ordinary small sites.
Source: latest blueprint thm-coef-finite-hom, statement and eight-step proof
(blueprint: thm-coef-finite-hom).

Proof: define each tensor comparison by ordinary balancing on K-flat representatives;
its representative equation determines it uniquely. Transpose scalar extension of
evaluation. Hom and scalar preservation give constructible finite-Tor endpoints.
Use a finite perfect-stratum filtration of K. For a stratum factor its immersion
as an open immersion followed by a closed immersion; internal adjunction writes
its Hom as the direct image of Hom on the stratum. The finite coefficient shriek,
direct-image and support comparisons reduce the comparison to bounded finite
projective complexes. There duality and scalar extension commute by the finite
idempotent-matrix calculation, including the signed differentials. Evaluation
identifies this invertible composite with the specified transpose. The thick
invertibility locus and the finite filtration give the étale result. Every
pro-étale constructible finite-Tor input descends to an étale one, with Tor bounds
reflected by comparison; the canonical finite-ring Hom site comparison transports
the result. Finally naturality of the closed adjunction gives naturality and all
transpose equations. Evaluating twice identifies internal composition; uniqueness
of transpose gives the scalar tower, identity and site-square equations.

Accepted DAG proof steps:
1. Define $v$ by scalar extension of evaluation and its unique tensor--Hom transpose. Hom
preservation and scalar preservation put both endpoints in $D^b_{ctf}$ (on the pro-etale site use
step 8).

2. Work etale. $X$ is Noetherian. The finite perfect-stratum filtration, constructed using the
open--closed triangles, reduces $K$ to shifts of $s_!P$, with $P$ locally a bounded finite-
projective complex. The finite-Tor truncation gives the site-perfect models on pro-etale pullback.

3. Factor $s=gj$ through its scheme-theoretic closure, $g$ closed and $j$ open. The closure
comparison identifies the filtration generator with $g_*j_!P$. Put $N=j^*Rg_A^!M$ and
$Q=H_A(P,N)$. The etale shriek comparison gives $N$ ctf and $N_B\cong s_B^!M_B$, with its counit
equation. Hom preservation gives $Q$ ctf.

4. For perfect $P$, $Q=P^\vee\otimes_A^LN$. On a bounded projective model the scalar comparison is
invertible: a summand $eA^r$ has dual the image of $e^{\mathsf t}$; scalar extension gives the
same idempotent on $B^r$. Evaluation and signed differentials agree. Only finite sums occur. Exact
restriction and local detection on cohomology give $Q_B\cong H_B(P_B,N_B)$.

5. Internal adjunction identifies $H_A(s_!P,M)$ with $Rs_*Q$. Move scalars through $Rs_*$, then
through $Q$ by step 4 and the shriek comparison, and apply internal adjunction over $B$. The
support comparison identifies $(s_!P)_B$ with $s_{!,B}P_B$. The pairing-change equation, using the
counit equation of step 3 and its ctf hypotheses, identifies this invertible composite with the
specified $v$.

6. For fixed $M$ the invertibility locus of this specified $v$ is thick. Step 5 and the finite
filtration of step 2 prove the claim for $K$.

7. Naturality of closed adjunction gives naturality and compatibility with transposes. For
composition, evaluate twice: both routes are scalar extension of consecutive evaluations. Tensor
associativity and transpose injectivity give equality. The monoidal scalar tower and its Hom
transpose give the displayed coefficient-chain and identity formulas.

8. Every pro-etale ctf input has bounded constructible etale origin; Tor reflection makes it ctf.
The canonical finite-ring Hom site comparison is invertible over $A,B$. Monoidal scalar/site
comparisons identify their evaluation transposes, so pro-etale $v$ is conjugate to etale $v$. This
also gives the site square and endpoints; step 7 applies on both sites. -/
theorem thm_coef_finite_hom
    (k : Type u) [Field k] (hk : Finite k ∨ IsAlgClosed k)
    (ell : ℕ) [Fact ell.Prime] (hkinv : IsUnit (ell : k))
    (X : Scheme.{u}) (aX : X ⟶ Spec (.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] :
    ∃ E : FiniteHomSystem X.smallEtaleTopology,
    ∃ P : FiniteHomSystem (Scheme.ProEt.topology X),
    ∃ N : FiniteHomSiteComparisons X,
      FiniteHomCtfConclusion.{u} X.smallEtaleTopology E ell (finiteHomEtaleCtf X) ∧
      FiniteHomCtfConclusion.{u} (Scheme.ProEt.topology X) P ell (finiteHomProEtaleCtf X) ∧
      FiniteHomEvaluationLaws.{u} X.smallEtaleTopology E ∧
      FiniteHomEvaluationLaws.{u} (Scheme.ProEt.topology X) P ∧
      FiniteHomTowerLaws.{u} X.smallEtaleTopology E ∧
      FiniteHomTowerLaws.{u} (Scheme.ProEt.topology X) P ∧
      FiniteHomIdentityLaws.{u} X.smallEtaleTopology E ∧
      FiniteHomIdentityLaws.{u} (Scheme.ProEt.topology X) P ∧
      FiniteHomSiteSquare X E P N ∧
      (∀ (A : Type (u + 1)) [CommRing A] [Finite A],
        (∃ n : ℕ, (ell : A) ^ n = 0) →
        ∀ K M : finiteHomDerived.{u} X.smallEtaleTopology A,
          finiteHomEtaleCtf X A K → finiteHomEtaleCtf X A M →
          IsIso (finiteHomSiteMap N A K M)) := by
  sorry

end WeilConjectures
