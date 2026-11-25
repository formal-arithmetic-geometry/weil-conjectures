/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingHomResolutionModel
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale

/-! # Presentation data for reindexed tensor and Hom comparisons

Records the data used to compare tensor products and Hom complexes of coefficient modules on
pro-étale sites with their reindexing along an isomorphism of schemes: the comparison
isomorphisms, their evaluation and shift laws, and the compositor and identity comparisons.

## Implementation details

The comparisons are presentation data, not an assumed preservation property. The signed double
shift `signedShift` applies the source shift first and then the target shift; this fixes the
sign `(-1)^(a*r)`. The evaluation laws use the Hom-first order of the recorded closed
adjunction.

## References

* Stacks Project, Tags 0GMX, 0A8X, 08J9, 08JA, 07A4, 06YN, 08J7, 09A5, 05RU, 0FPI
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme

-- Cache the sheaf composition witness without repeatedly reconstructing the small site.
set_option linter.defProp false in
@[instance_reducible]
private def cachedCompose {C : Type*} [Category C] (J : GrothendieckTopology C)
    [EssentiallySmall.{u + 1} C] :
    J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := by
  exact (equivSmallModel.{u + 1} C).hasSheafCompose J
    ((equivSmallModel.{u + 1} C).inverse.inducedTopology J)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

attribute [local instance 1000001] cachedCompose

attribute [local irreducible] Padic Padic.coefficientExtensionIntegers

namespace WeilConjectures.PodReindexingCoherence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The category of `ℤ`-indexed cochain complexes of coefficient modules on `W`. -/
abbrev K (W : Scheme.{u}) (s : Option ℕ) :=
  CochainComplex (podReindexingModules l E W s) ℤ

/-- A closed structure on the derived category, with the recorded derived Hom. -/
abbrev Closed (W : Scheme.{u}) (s : Option ℕ) :=
  CoefficientClosedStructure (podReindexingDerivedHom l E W s)

/-- K-flat tensor models for the closed structure `S`, with the standard localization
universe. -/
abbrev Models (W : Scheme.{u}) (s : Option ℕ) (S : Closed l E W s) :=
  @CoefficientTensorModels.{u, u + 1, u, u + 2} _ _ (ProEt.topology W) _ _
    (podReindexingRing l E W s) (HasDerivedCategory.standard.{u + 1, u + 2} _) S

/-- The total tensor product of complexes of coefficient modules. -/
abbrev total (W : Scheme.{u}) (s : Option ℕ) :=
  coefficientTotalTensor.{u, u + 1, u} (ProEt.topology W) (podReindexingRing l E W s)

/-- The Hom complex between two complexes of coefficient modules. -/
abbrev hom (W : Scheme.{u}) (s : Option ℕ) (P I : K l E W s) :=
  homComplex.{u + 1, u, u + 1, u + 1} (R := podReindexingRing l E W s) P I

/-- The projection from the Hom complex onto a product factor. -/
abbrev proj (W : Scheme.{u}) (s : Option ℕ) (P I : K l E W s)
    (r p q : ℤ) (h : p + r = q) :=
  homComplexπ.{u + 1, u, u + 1, u + 1} (R := podReindexingRing l E W s) P I r p q h

/-- The signed double shift `RHom(M[a], N[b]) ≅ RHom(M, N)[b - a]` of the recorded derived
Hom. -/
def signedShift (W : Scheme.{u}) (s : Option ℕ)
    (M N : podReindexingDerived l E W s) (a b : ℤ) :
    (podReindexingDerivedHom l E W s).obj (op (M⟦a⟧), N⟦b⟧) ≅
      ((podReindexingDerivedHom l E W s).obj (op M, N))⟦b-a⟧ :=
  letI := HasDerivedCategory.standard.{u + 1, u + 2} (podReindexingModules l E W s)
  let H := CategoryTheory.RingedHomUniverses.hom.{u + 1, u, u, u + 2}
    (ProEt.topology W) (podReindexingRing l E W s) M
  ((CategoryTheory.RingedHomUniverses.sourceShift.{u + 1, u, u, u + 2}
    (ProEt.topology W) (podReindexingRing l E W s) M a).app (N⟦b⟧)).symm ≪≫
    (shiftFunctor _ (-a)).mapIso ((H.commShiftIso b).app N) ≪≫
    (shiftFunctorAdd' _ b (-a) (b-a) (sub_eq_add_neg b a).symm).symm.app (H.obj N)

attribute [local irreducible] signedShift podReindexingCoefficient podReindexingHomModel
  homComplexFunctor homComplexπ
  derivedInternalHomOfUniverses coefficientTotalTensor coefficientTensorGenerator
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  Functor.mapHomologicalComplexUpToQuasiIso Functor.mapHomologicalComplexUpToQuasiIsoFactors
  SheafOfModules.monoidalCategory

set_option allowUnsafeReducibility true in
attribute [local semireducible] podReindexingFunctor podReindexingComplexFunctor
  podReindexingDerivedFunctor podReindexingDerivedFactors

-- Keep structure auxiliaries from expanding unrelated localization presentations.
set_option allowUnsafeReducibility true in
attribute [local irreducible] podReindexingDerivedFunctor podReindexingDerivedFactors

-- Elaborate the representative normalization across the two ringed sites.
/-- Comparisons of Hom complexes and tensor products with reindexing along `g`, together with
their product, tensor-generator and localization normalizations. -/
structure Comparison {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY) where
  /-- Componentwise reindexing, for all unbounded Hom complexes. -/
  chain : ∀ P I : K l E Y s,
    (podReindexingComplexFunctor l E g s).obj (hom l E Y s P I) ≅
      hom l E X s ((podReindexingComplexFunctor l E g s).obj P)
        ((podReindexingComplexFunctor l E g s).obj I)
  /-- The product projections are the slice-module reindexing maps. -/
  chain_projection : ∀ (P I : K l E Y s) (r p : ℤ) (U V : X.ProEt) (a : V ⟶ U)
    (f : ((hom l E Y s P I).X r).val.obj (op ((proEtaleIsoPostcompose g).obj U)))
    (x : (P.X p).val.obj (op ((proEtaleIsoPostcompose g).obj V))),
    (((proj l E X s ((podReindexingComplexFunctor l E g s).obj P)
      ((podReindexingComplexFunctor l E g s).obj I) r p (p+r) rfl).val.app (op U)
        (((chain P I).hom.f r).val.app (op U) f)).app (op (Over.mk a))).hom x =
      (((proj l E Y s P I r p (p+r) rfl).val.app
        (op ((proEtaleIsoPostcompose g).obj U)) f).app
          (op (Over.mk ((proEtaleIsoPostcompose g).map a)))).hom x
  /-- The specified natural product-Hom comparison after localization. -/
  derived : podReindexingDerivedHom l E Y s ⋙ podReindexingDerivedFunctor l E g s ≅
    ((podReindexingDerivedFunctor l E g s).op.prod (podReindexingDerivedFunctor l E g s)) ⋙
      podReindexingDerivedHom l E X s
  /-- Exact agreement with the recorded Hom resolution model. -/
  derived_model : ∀ (P I : K l E Y s) (hI : I.IsKInjective),
    ∃ hFI : CochainComplex.IsKInjective ((podReindexingComplexFunctor l E g s).obj I),
      derived.hom.app (op ((podReindexingQ l E Y s).obj P),
        (podReindexingQ l E Y s).obj I) =
      (podReindexingDerivedFunctor l E g s).map
        (@podReindexingHomModel l _ E _ _ _ Y s P I hI).hom ≫
      (podReindexingDerivedFactors l E g s).hom.app (hom l E Y s P I) ≫
      (podReindexingQ l E X s).map (chain P I).hom ≫
      (@podReindexingHomModel l _ E _ _ _ X s
        ((podReindexingComplexFunctor l E g s).obj P)
        ((podReindexingComplexFunctor l E g s).obj I) hFI).inv ≫
      ((podReindexingDerivedHom l E X s).mapIso
        (((podReindexingDerivedFactors l E g s).app P).op.prod
          ((podReindexingDerivedFactors l E g s).app I).symm)).hom
  /-- The total-tensor chain comparison. -/
  tensorChain : ∀ P L : K l E Y s,
    (podReindexingComplexFunctor l E g s).obj ((total l E Y s).obj (P, L)) ≅
      (total l E X s).obj ((podReindexingComplexFunctor l E g s).obj P,
        (podReindexingComplexFunctor l E g s).obj L)
  /-- Its value on every sheafified pure tensor, including the total summand. -/
  tensorChain_pure : ∀ (P L : K l E Y s) (p q k : ℤ) (h : p+q=k) (U : X.ProEt)
    (x : (P.X p).val.obj (op ((proEtaleIsoPostcompose g).obj U)))
    (y : (L.X q).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
    (((tensorChain P L).hom.f k).val.app (op U))
      (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology Y)
        (podReindexingRing l E Y s) P L p q k h
          (op ((proEtaleIsoPostcompose g).obj U)) x y) =
      coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
        (podReindexingRing l E X s) ((podReindexingComplexFunctor l E g s).obj P)
          ((podReindexingComplexFunctor l E g s).obj L) p q k h (op U) x y
  /-- The ordinary derived total-tensor comparison. -/
  tensor : SY.tensor ⋙ podReindexingDerivedFunctor l E g s ≅
    ((podReindexingDerivedFunctor l E g s).prod (podReindexingDerivedFunctor l E g s)) ⋙
      SX.tensor
  /-- Its K-flat representative characterization, using the recorded tensor models. -/
  tensor_model : ∀ (P L : K l E Y s)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology Y) (R := podReindexingRing l E Y s) P)
    (hL : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology Y) (R := podReindexingRing l E Y s) L),
    ∃ (hFP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology X) (R := podReindexingRing l E X s) ((podReindexingComplexFunctor l E
        g s).obj P))
      (hFL : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology X) (R := podReindexingRing l E X s) ((podReindexingComplexFunctor l E
        g s).obj L)),
      (podReindexingDerivedFunctor l E g s).map
        ((@CoefficientTensorModels.comparison.{u, u + 1, u, u + 2} _ _ (ProEt.topology Y)
          _ _ (podReindexingRing l E Y s) (HasDerivedCategory.standard.{u + 1, u + 2} _) SY
            TY).hom.app (⟨P, hP⟩, ⟨L, hL⟩)) ≫
        tensor.hom.app ((podReindexingQ l E Y s).obj P, (podReindexingQ l E Y s).obj L) ≫
        SX.tensor.map (Prod.mkHom ((podReindexingDerivedFactors l E g s).hom.app P)
          ((podReindexingDerivedFactors l E g s).hom.app L)) =
      (podReindexingDerivedFactors l E g s).hom.app ((total l E Y s).obj (P, L)) ≫
        (podReindexingQ l E X s).map (tensorChain P L).hom ≫
        (@CoefficientTensorModels.comparison.{u, u + 1, u, u + 2} _ _ (ProEt.topology X)
          _ _ (podReindexingRing l E X s) (HasDerivedCategory.standard.{u + 1, u + 2} _) SX
            TX).hom.app (⟨_, hFP⟩, ⟨_, hFL⟩)

/-- The derived Hom comparison of `c` is characterized by evaluation, transports
transposition, and is natural in both variables. -/
structure EvaluationLaws {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY) : Prop where
  /-- Evaluation normalization, equivalently its Koszul-symmetric M-first version. -/
  evaluation : ∀ M N : podReindexingDerived l E Y s,
    c.tensor.hom.app ((podReindexingDerivedHom l E Y s).obj (op M, N), M) ≫
      SX.tensor.map (Prod.mkHom (c.derived.hom.app (op M, N))
        (𝟙 ((podReindexingDerivedFunctor l E g s).obj M))) ≫
      SX.evaluation ((podReindexingDerivedFunctor l E g s).obj M)
        ((podReindexingDerivedFunctor l E g s).obj N) =
      (podReindexingDerivedFunctor l E g s).map (SY.evaluation M N)
  /-- Uniqueness among all arrows, not just among isomorphisms. -/
  unique : ∀ (M N : podReindexingDerived l E Y s)
    (d : (podReindexingDerivedFunctor l E g s).obj
      ((podReindexingDerivedHom l E Y s).obj (op M, N)) ⟶
      (podReindexingDerivedHom l E X s).obj
        (op ((podReindexingDerivedFunctor l E g s).obj M),
          (podReindexingDerivedFunctor l E g s).obj N)),
    c.tensor.hom.app ((podReindexingDerivedHom l E Y s).obj (op M, N), M) ≫
      SX.tensor.map (Prod.mkHom d (𝟙 ((podReindexingDerivedFunctor l E g s).obj M))) ≫
      SX.evaluation ((podReindexingDerivedFunctor l E g s).obj M)
        ((podReindexingDerivedFunctor l E g s).obj N) =
      (podReindexingDerivedFunctor l E g s).map (SY.evaluation M N) ↔
        d = c.derived.hom.app (op M, N)
  /-- Transport of transposition for every derived arrow. -/
  transpose : ∀ (L M N : podReindexingDerived l E Y s)
    (b : SY.tensor.obj (L, M) ⟶ N),
    (podReindexingDerivedFunctor l E g s).map (SY.transpose L M N b) ≫
      c.derived.hom.app (op M, N) =
      SX.transpose ((podReindexingDerivedFunctor l E g s).obj L)
        ((podReindexingDerivedFunctor l E g s).obj M)
        ((podReindexingDerivedFunctor l E g s).obj N)
        (c.tensor.inv.app (L, M) ≫ (podReindexingDerivedFunctor l E g s).map b)
  /-- Contravariance in M and covariance in N. -/
  naturality : ∀ (M M' N N' : podReindexingDerived l E Y s) (a : M' ⟶ M) (b : N ⟶ N'),
    (podReindexingDerivedFunctor l E g s).map
      ((podReindexingDerivedHom l E Y s).map (Prod.mkHom a.op b)) ≫
        c.derived.hom.app (op M', N') =
      c.derived.hom.app (op M, N) ≫ (podReindexingDerivedHom l E X s).map
        (Prod.mkHom ((podReindexingDerivedFunctor l E g s).map a).op
          ((podReindexingDerivedFunctor l E g s).map b))

/-- The canonical signed double shift on Hom complexes, specified on every product factor. -/
structure ChainShift (W : Scheme.{u}) (s : Option ℕ) where
  /-- The signed reindexing isomorphism. -/
  iso : ∀ (P I : K l E W s) (a b : ℤ),
    hom l E W s (P⟦a⟧) (I⟦b⟧) ≅ (hom l E W s P I)⟦b-a⟧
  /-- In Hom degree r, reindex p to p-a and multiply by (-1)^(a*r). -/
  formula : ∀ (P I : K l E W s) (a b r p : ℤ),
    (iso P I a b).hom.f r ≫ proj l E W s P I (r+(b-a)) p (p+(r+(b-a))) rfl =
      (a*r).negOnePow •
        (proj l E W s (P⟦a⟧) (I⟦b⟧) r (p-a) ((p-a)+r) rfl ≫
          SheafOfModules.homObjMap.{u + 1, u, u + 1, u + 1}
            (R := podReindexingRing l E W s)
            (P.shiftFunctorObjXIso a (p-a) p (by omega)).inv
            (I.shiftFunctorObjXIso b ((p-a)+r) (p+(r+(b-a))) (by omega)).hom)

set_option allowUnsafeReducibility true in
attribute [local reducible] podReindexingFunctor podReindexingDerivedFunctor

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The degreewise identity shift comparison of the exact termwise reindexing functor. -/
def complexShift {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (s : Option ℕ) (a : ℤ) :
    shiftFunctor (K l E Y s) a ⋙ podReindexingComplexFunctor l E g s ≅
      podReindexingComplexFunctor l E g s ⋙ shiftFunctor (K l E X s) a :=
  (podReindexingFunctor l E g s).mapCochainComplexShiftIso a

attribute [local irreducible] complexShift

/-- The Hom comparisons of `c` commute with the signed double shifts, both on Hom complexes and
in the derived category. -/
structure ShiftLaws {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY)
    (sX : ChainShift l E X s) (sY : ChainShift l E Y s) : Prop where
  /-- Reindexing and signed double shifts already commute on Hom complexes. -/
  chain : ∀ (P I : K l E Y s) (a b : ℤ),
    (c.chain (P⟦a⟧) (I⟦b⟧)).hom ≫
      (((podReindexingHom l E X s).map
        ((complexShift l E g s a).inv.app P).op).app
          ((podReindexingComplexFunctor l E g s).obj (I⟦b⟧)) ≫
        ((podReindexingHom l E X s).obj
          (op (((podReindexingComplexFunctor l E g s).obj P)⟦a⟧))).map
            ((complexShift l E g s b).hom.app I)) ≫
      (sX.iso ((podReindexingComplexFunctor l E g s).obj P)
        ((podReindexingComplexFunctor l E g s).obj I) a b).hom =
      (podReindexingComplexFunctor l E g s).map (sY.iso P I a b).hom ≫
        (complexShift l E g s (b-a)).hom.app
          (hom l E Y s P I) ≫ ((c.chain P I).hom)⟦b-a⟧'
  /-- The same square after localization, with the normalized derived Hom shifts. -/
  derived : ∀ (M N : podReindexingDerived l E Y s) (a b : ℤ),
    c.derived.hom.app (op (M⟦a⟧), N⟦b⟧) ≫
      (podReindexingDerivedHom l E X s).map
        (Prod.mkHom (((podReindexingDerivedFunctor l E g s).commShiftIso a).inv.app M).op
          (((podReindexingDerivedFunctor l E g s).commShiftIso b).hom.app N)) ≫
      (signedShift l E X s ((podReindexingDerivedFunctor l E g s).obj M)
        ((podReindexingDerivedFunctor l E g s).obj N) a b).hom =
      (podReindexingDerivedFunctor l E g s).map (signedShift l E Y s M N a b).hom ≫
        ((podReindexingDerivedFunctor l E g s).commShiftIso (b-a)).hom.app
          ((podReindexingDerivedHom l E Y s).obj (op M, N)) ≫
        (c.derived.hom.app (op M, N))⟦b-a⟧'

set_option allowUnsafeReducibility true in
attribute [local semireducible] podReindexingFunctor

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical site compositor, identity on the underlying schemes. -/
def siteComp {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Z ⟶ X) [IsIso g] [IsIso h] :
    proEtaleIsoPostcompose (h ≫ g) ≅
      proEtaleIsoPostcompose h ⋙ proEtaleIsoPostcompose g :=
  MorphismProperty.Over.mapComp (P := @WeaklyEtale.{u}) (Q := ⊤)
    (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale g)

attribute [local irreducible] siteComp

/-- The reindexing compositor for `h ≫ g`, given by sheaf restrictions and termwise
localization. -/
structure Compositor {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Z ⟶ X)
    [IsIso g] [IsIso h] (s : Option ℕ) where
  /-- Ordinary module compositor. -/
  ordinary : podReindexingFunctor l E (h ≫ g) s ≅
    podReindexingFunctor l E g s ⋙ podReindexingFunctor l E h s
  /-- The compositor is restriction along the canonical site compositor. -/
  sections : ∀ (M : podReindexingModules l E Y s) (U : Z.ProEt)
    (x : M.val.obj (op ((proEtaleIsoPostcompose (h ≫ g)).obj U))),
    HEq ((ordinary.hom.app M).val.app (op U) x)
      (M.val.map ((siteComp g h).inv.app U).op x)
  /-- Termwise compositor of actual complexes. -/
  complex : ∀ P : K l E Y s,
    (podReindexingComplexFunctor l E (h ≫ g) s).obj P ≅
      (podReindexingComplexFunctor l E h s).obj
        ((podReindexingComplexFunctor l E g s).obj P)
  /-- Its components are the ordinary compositor, with no new sign. -/
  degree : ∀ (P : K l E Y s) (i : ℤ),
    (complex P).hom.f i = ordinary.hom.app (P.X i)
  /-- Derived compositor. -/
  derived : podReindexingDerivedFunctor l E (h ≫ g) s ≅
    podReindexingDerivedFunctor l E g s ⋙ podReindexingDerivedFunctor l E h s
  /-- It is the localization of the termwise compositor. -/
  model : ∀ P : K l E Y s,
    derived.hom.app ((podReindexingQ l E Y s).obj P) ≫
      (podReindexingDerivedFunctor l E h s).map
        ((podReindexingDerivedFactors l E g s).hom.app P) ≫
      (podReindexingDerivedFactors l E h s).hom.app
        ((podReindexingComplexFunctor l E g s).obj P) =
      (podReindexingDerivedFactors l E (h ≫ g) s).hom.app P ≫
        (podReindexingQ l E Z s).map (complex P).hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical identity comparison on the site, identity on underlying schemes. -/
def siteId (X : Scheme.{u}) : proEtaleIsoPostcompose (𝟙 X) ≅ 𝟭 X.ProEt :=
  MorphismProperty.Over.mapId (P := @WeaklyEtale.{u}) (Q := ⊤) X (𝟙 X) rfl

attribute [local irreducible] siteId

/-- The canonical identity comparison for reindexing along `𝟙 X`, specified by restriction and
localization. -/
structure Identity (X : Scheme.{u}) (s : Option ℕ) where
  /-- Ordinary identity pullback comparison. -/
  ordinary : podReindexingFunctor l E (𝟙 X) s ≅ 𝟭 (podReindexingModules l E X s)
  /-- The underlying map is the restriction along the canonical identity of the site. -/
  sections : ∀ (M : podReindexingModules l E X s) (U : X.ProEt)
    (x : M.val.obj (op ((proEtaleIsoPostcompose (𝟙 X)).obj U))),
    HEq ((ordinary.hom.app M).val.app (op U) x)
      (M.val.map ((siteId X).inv.app U).op x)
  /-- Termwise identity comparison. -/
  complex : ∀ P : K l E X s, (podReindexingComplexFunctor l E (𝟙 X) s).obj P ≅ P
  /-- The degreewise comparison is the module comparison. -/
  degree : ∀ (P : K l E X s) (i : ℤ),
    (complex P).hom.f i = ordinary.hom.app (P.X i)
  /-- Derived identity pullback comparison. -/
  derived : podReindexingDerivedFunctor l E (𝟙 X) s ≅ 𝟭 (podReindexingDerived l E X s)
  /-- Its value is fixed on every localized complex. -/
  model : ∀ P : K l E X s,
    derived.hom.app ((podReindexingQ l E X s).obj P) =
      (podReindexingDerivedFactors l E (𝟙 X) s).hom.app P ≫
        (podReindexingQ l E X s).map (complex P).hom

end WeilConjectures.PodReindexingCoherence
