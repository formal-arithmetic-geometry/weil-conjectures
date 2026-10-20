/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.CategoryTheory.RingedSiteDualityMaps
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
public import Sheaf.Algebra.Homology.SignedDoubleHomCone
public import Sheaf.CategoryTheory.ScalarLocalizationTriangulated
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.HomComplexGlobalHomotopy
import Sheaf.Algebra.Homology.KInjectiveHomComplex
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMap
import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
import Sheaf.Algebra.Homology.HomTensorTotal
import Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import WeilConjectures.Algebra.Homology.HomComplex
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.CategoryTheory.ScalarLocalization
import Sheaf.Algebra.Homology.HomComplexGlobalHomotopyOfUniverses

/-! # Coefficient biduality, triangles, restriction and scalar localization

Source: Stacks Project, sites-cohomology.tex, Tags 08JC, 0A97 and 08JB;
the signed double-Hom calculation in the DAG proof
(blueprint: lem-coef-rational-bidual-triangle-compatibility).

Stage-2 validation copy for group Q58.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r w w' a b t

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite TensorProduct

namespace CategoryTheory.CoefficientBidualTriangles

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (O : Sheaf J CommRingCat.{max c v r})

/-- The recorded module category, without changing its objects or morphisms.
Source: Stacks 08J7 (blueprint: lem-coef-rational-bidual-triangle-compatibility). -/
abbrev Modules := ringedSiteModules.{max c v r}
  ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj O)

/-- The full unbounded derived category in the chosen morphism universe.
Source: Stacks 08J7 (blueprint: lem-coef-rational-bidual-triangle-compatibility). -/
abbrev D [HasDerivedCategory.{w} (Modules.{c, v, r} J O)] := DerivedCategory (Modules.{c, v, r} J O)

/-- All integer cochain complexes, with no boundedness restriction.
Source: Stacks 0A8X (blueprint: lem-coef-rational-bidual-triangle-compatibility). -/
abbrev Complex := CochainComplex (Modules.{c, v, r} J O) ℤ

variable [HasDerivedCategory.{w} (Modules.{c, v, r} J O)]

/-- The coefficient dual, using exactly the recorded derived internal Hom and O[0].
Source: Stacks 08JD (blueprint: lem-coef-rational-bidual-triangle-compatibility). -/
def dual : (D.{c, v, r, w} J O)ᵒᵖ ⥤ D.{c, v, r, w} J O :=
  Prod.sectL _ (ringedSiteDualityUnit.{c, v, r, w} J O) ⋙
    derivedInternalHomOfUniverses.{c, v, r, w} J O

/-- The actual double coefficient dual, covariant on morphisms.
Source: Stacks 08JD (blueprint: lem-coef-rational-bidual-triangle-compatibility). -/
def bidual : D.{c, v, r, w} J O ⥤ D.{c, v, r, w} J O :=
  (dual.{c, v, r, w} J O).rightOp ⋙ dual.{c, v, r, w} J O

/-- The natural transformation whose components are the recorded evaluation transpose.
Source: Stacks 0A97 (blueprint: lem-coef-rational-bidual-triangle-compatibility). -/
def bidualMap (M : RingedSiteDualityModel.{c, v, r, w} J O) :
    𝟭 _ ⟶ bidual.{c, v, r, w} J O where
  app P := ringedSiteBidual M.closed M.symmetric (ringedSiteDualityUnit.{c, v, r, w} J O) P
  naturality _ _ f := ringedSiteBidual_naturality M.closed M.symmetric _ f

/-- Hom into the fixed K-injective resolution of the coefficient object.
Source: Stacks 079P (blueprint: lem-coef-rational-bidual-triangle-compatibility). -/
abbrev targetResolution : Complex.{c, v, r} J O :=
  (WeilConjectures.coefficientHomResolution.{r, c, v} J O).obj
    (ringedSiteDualityUnitComplex.{c, v, r} J O)

/-- The canonical double-Hom representative comparison. Both factors are the actual
localization factorization of the recorded derived Hom, rather than chosen isomorphisms.
Source: Stacks 0A95 (blueprint: lem-coef-rational-bidual-triangle-compatibility). -/
def modelMap (E : Complex.{c, v, r} J O) :
    DerivedCategory.Q.obj
      ((SignedDoubleHomCone.doubleDual.{c, v, r, max c v r} (R := O) (targetResolution.{c, v, r} J
        O)).obj E) ⟶
        (bidual.{c, v, r, w} J O).obj (DerivedCategory.Q.obj E) :=
  (WeilConjectures.coefficientHomResolutionIso.{r, c, v, w} J O
    (homComplex.{c, v, max c v r, max c v r} (R := O) E (targetResolution.{c, v, r} J O))
      (ringedSiteDualityUnitComplex.{c, v, r} J O)).inv ≫
  (derivedInternalHomOfUniverses.{c, v, r, w} J O).map
    (Prod.mkHom
      (WeilConjectures.coefficientHomResolutionIso.{r, c, v, w} J O E
        (ringedSiteDualityUnitComplex.{c, v, r} J O)).hom.op (𝟙 _))

/-- The normalized signed shift comparison for Hom into the fixed resolution.
The first witness of the recorded comparison theorem is uniquely specified by its
product-component formula (-1)^(m*q), so no unspecified comparison is chosen.
Source: Stacks 08JC (blueprint: lem-coef-rational-bidual-triangle-compatibility). -/
def signedHomShift (E : Complex.{c, v, r} J O) (m : ℤ) :=
  (SignedDoubleHomCone.comparison.{c, v, r, max c v r} (R := O)
    (targetResolution.{c, v, r} J O)).choose E m

/-- The signed comparison chi from the recorded cone calculation, constructed
as minus s_(T(E),-1) after T(s_(E,1)) inverse. In particular its section formula
is (chi g)(y)=(-1)^(deg g+deg y) g(y), with the required leading minus.
Source: Stacks 08JC (blueprint: lem-coef-rational-bidual-triangle-compatibility). -/
def signedModelShift (E : Complex.{c, v, r} J O) :=
  -((SignedDoubleHomCone.dual.{c, v, r, max c v r} (R := O)
      (targetResolution.{c, v, r} J O)).mapIso
      (signedHomShift.{c, v, r} J O E 1).symm.op ≪≫
    signedHomShift.{c, v, r} J O
      (homComplex.{c, v, max c v r, max c v r} (R := O) E
        (targetResolution.{c, v, r} J O)) (-1))

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Shift and triangle compatibility of the canonical evaluation-defined biduality map.
Source: Stacks 08JC and 0A97, with the explicit signed cone comparison
(blueprint: lem-coef-rational-bidual-triangle-compatibility).

Proof (DAG steps 1--8 and 13): fix the K-injective coefficient resolution I. Hom(-,I)
inverts quasi-isomorphisms, twice, so T² descends to the recorded double derived Hom.
K-flat tensor representatives and K-injective Hom representatives identify currying
with g(x tensor y)=g(x)(y), with no extra sign. The chain map b_E(x)(f)=(-1)^(pq)f(x)
commutes with the Hom differential and is natural. On a flat resolution P and a
K-flat resolution L of T(P), evaluation after symmetry is x tensor l ↦ (-1)^(pq)r(l)(x).
Its curry is T(r)b_P. Inverting T(r) and then the resolution of E identifies Qb_E
with the specified evaluation transpose on every E. The signed cone lemma gives
chi=-s_(T(E),-1) T(s_(E,1))^(-1), and its cone comparison identifies all three cone
arrows, including -pi. Hence its descent is exact. For x in E[1]^p and y in T(E)^t,
chi b_(E[1]) evaluates with exponent p+t+p(t+1), equal modulo 2 to (p+1)t.
Thus d commutes with shift one, and iteration and inverse shifts give all integers.
Naturality at the first two arrows gives the first two triangle squares; naturality
at the connecting arrow followed by this shift equality gives the third. Apply the
recorded triangle two-out-of-three lemma to this morphism of distinguished triangles.
An invertible shift comparison and the shift equivalence give closure under every shift.
-/
theorem compatibility (M : RingedSiteDualityModel.{c, v, r, w} J O) :
    ∃ cs : (bidual.{c, v, r, w} J O).CommShift ℤ,
      (fun [comm : (bidual.{c, v, r, w} J O).CommShift ℤ] ↦
        (bidual.{c, v, r, w} J O).IsTriangulated ∧
        NatTrans.CommShift (bidualMap.{c, v, r, w} J O M) ℤ ∧
        (∀ E : Complex.{c, v, r} J O,
          DerivedCategory.Q.map (signedModelShift.{c, v, r} J O E).hom ≫
              ((DerivedCategory.Q).commShiftIso (1 : ℤ)).hom.app _ ≫
              (modelMap.{c, v, r, w} J O E)⟦(1 : ℤ)⟧' =
            modelMap.{c, v, r, w} J O (E⟦(1 : ℤ)⟧) ≫
              (bidual.{c, v, r, w} J O).map (((DerivedCategory.Q).commShiftIso (1 : ℤ)).hom.app E) ≫
              ((bidual.{c, v, r, w} J O).commShiftIso (1 : ℤ)).hom.app (DerivedCategory.Q.obj E)) ∧
        (∀ T : Triangle (D.{c, v, r, w} J O), T ∈ distTriang _ →
          ∃ f : T ⟶ (bidual.{c, v, r, w} J O).mapTriangle.obj T,
            f.hom₁ = (bidualMap.{c, v, r, w} J O M).app T.obj₁ ∧
            f.hom₂ = (bidualMap.{c, v, r, w} J O M).app T.obj₂ ∧
            f.hom₃ = (bidualMap.{c, v, r, w} J O M).app T.obj₃) ∧
        (∀ (V : D.{c, v, r, w} J O) (n : ℤ),
          IsIso ((bidualMap.{c, v, r, w} J O M).app (V⟦n⟧)) ↔ IsIso ((bidualMap.{c, v, r, w} J O
            M).app V)) ∧
        (∀ T : Triangle (D.{c, v, r, w} J O), T ∈ distTriang _ →
          (IsIso ((bidualMap.{c, v, r, w} J O M).app T.obj₁) →
            IsIso ((bidualMap.{c, v, r, w} J O M).app T.obj₂) → IsIso ((bidualMap.{c, v, r, w} J O
              M).app T.obj₃)) ∧
          (IsIso ((bidualMap.{c, v, r, w} J O M).app T.obj₁) →
            IsIso ((bidualMap.{c, v, r, w} J O M).app T.obj₃) → IsIso ((bidualMap.{c, v, r, w} J O
              M).app T.obj₂)) ∧
          (IsIso ((bidualMap.{c, v, r, w} J O M).app T.obj₂) →
            IsIso ((bidualMap.{c, v, r, w} J O M).app T.obj₃) → IsIso ((bidualMap.{c, v, r, w} J O
              M).app T.obj₁))))
        (comm := cs) := by
  sorry

/-- The shift structure determined by the signed representative normalization above.
The normalization specifies every component after the essentially surjective Q, and
therefore determines this structure, rather than selecting an unspecified duality.
Source: Stacks 08JC (blueprint: lem-coef-rational-bidual-triangle-compatibility). -/
@[instance_reducible]
def canonicalCommShift (M : RingedSiteDualityModel.{c, v, r, w} J O) :
    (bidual.{c, v, r, w} J O).CommShift ℤ :=
  (compatibility.{c, v, r, w} J O M).choose

/-- Exact slice restriction carries the same bidual triangle morphism, including its
connecting square, to the slice. The displayed formula for beta is precisely the
iterated internal-Hom comparison with the restricted coefficient object.
Source: Stacks 08JB and 0A97
(blueprint: lem-coef-rational-bidual-triangle-compatibility).

Proof (DAG steps 9--10): restriction of Hom complexes is the sectionwise identification
of families of module maps, preserving the differential and product projections.
The exact extension-by-zero adjunction proves that a restricted K-injective complex
is K-injective. Thus these identifications compute derived restriction. The signs in
s and chi, including chi's leading minus, restrict unchanged. Changing the fixed
K-injective target commutes with evaluation, precomposition and all these signs;
quasi-isomorphism invariance identifies different fixed resolutions. The iterated
Hom comparison beta therefore commutes with the signed shifts, and with d by the
recorded duality-map restriction lemma. Exact restriction takes distinguished
triangles to distinguished triangles. The componentwise beta squares compare the
three bidual triangle components; for the last square use shift compatibility of
beta, followed by the original connecting-square equality. -/
theorem restriction (M : RingedSiteDualityModel.{c, v, r, w} J O) (U : C)
    [HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    [HasDerivedCategory.{w'} (Modules.{max c v, v, r} (J.over U) (O.over U))]
    (MU : RingedSiteDualityModel.{max c v, v, r, w'} (J.over U) (O.over U)) :
    (fun [comm : (bidual.{c, v, r, w} J O).CommShift ℤ]
        [commU : (bidual.{max c v, v, r, w'} (J.over U) (O.over U)).CommShift ℤ] ↦
      ∃ F : D.{c, v, r, w} J O ⥤ D.{max c v, v, r, w'} (J.over U) (O.over U),
      ∃ fc : F.CommShift ℤ,
        (fun [fcomm : F.CommShift ℤ] ↦
          F.IsTriangulated ∧
          Nonempty (DerivedCategory.Q ⋙ F ≅
            ringedSiteDualityRestrictionComplex.{c, v, r} J O U ⋙ DerivedCategory.Q.{w'}) ∧
          ∃ (tensor : M.closed.tensor ⋙ F ≅ (F.prod F) ⋙ MU.closed.tensor)
            (h : derivedInternalHomOfUniverses.{c, v, r, w} J O ⋙ F ≅
            (F.op.prod F) ⋙
              derivedInternalHomOfUniverses.{max c v, v, r, w'} (J.over U) (O.over U))
            (o : F.obj (ringedSiteDualityUnit.{c, v, r, w} J O) ≅
              ringedSiteDualityUnit.{max c v, v, r, w'} (J.over U) (O.over U))
            (beta : bidual.{c, v, r, w} J O ⋙ F ≅
              F ⋙ bidual.{max c v, v, r, w'} (J.over U) (O.over U)),
            (∀ P N : D.{c, v, r, w} J O,
              F.map (M.closed.evaluation P N) =
                tensor.hom.app ((derivedInternalHomOfUniverses.{c, v, r, w} J O).obj
                  (op P, N), P) ≫
                  MU.closed.tensor.map (Prod.mkHom (h.hom.app (op P, N)) (𝟙 _)) ≫
                  MU.closed.evaluation (F.obj P) (F.obj N)) ∧
            NatTrans.CommShift beta.hom ℤ ∧
            (∀ V : D.{c, v, r, w} J O,
              beta.hom.app V =
                h.hom.app (op ((dual.{c, v, r, w} J O).obj (op V)),
                  ringedSiteDualityUnit.{c, v, r, w} J O) ≫
                (derivedInternalHomOfUniverses.{max c v, v, r, w'}
                  (J.over U) (O.over U)).map (Prod.mkHom
                    (h.inv.app (op V, ringedSiteDualityUnit.{c, v, r, w} J O)).op o.hom) ≫
                (derivedInternalHomOfUniverses.{max c v, v, r, w'}
                  (J.over U) (O.over U)).map (Prod.mkHom
                    ((derivedInternalHomOfUniverses.{max c v, v, r, w'}
                      (J.over U) (O.over U)).map
                        (Prod.mkHom (𝟙 (op (F.obj V))) o.inv)).op (𝟙 _))) ∧
            (∀ V : D.{c, v, r, w} J O,
              F.map ((bidualMap.{c, v, r, w} J O M).app V) ≫ beta.hom.app V =
                (bidualMap.{max c v, v, r, w'} (J.over U) (O.over U) MU).app (F.obj V)) ∧
            (∀ T : Triangle (D.{c, v, r, w} J O), T ∈ distTriang _ →
              F.map ((bidualMap.{c, v, r, w} J O M).app T.obj₃ ≫
                  (bidual.{c, v, r, w} J O).map T.mor₃ ≫
                  ((bidual.{c, v, r, w} J O).commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫
                (F.commShiftIso (1 : ℤ)).hom.app _ ≫
                (beta.hom.app T.obj₁)⟦(1 : ℤ)⟧' =
              (bidualMap.{max c v, v, r, w'} (J.over U) (O.over U) MU).app (F.obj T.obj₃) ≫
                (bidual.{max c v, v, r, w'} (J.over U) (O.over U)).map
                  (F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫
                ((bidual.{max c v, v, r, w'} (J.over U) (O.over U)).commShiftIso
                  (1 : ℤ)).hom.app (F.obj T.obj₁))) (fcomm := fc))
      (comm := canonicalCommShift.{c, v, r, w} J O M)
      (commU := canonicalCommShift.{max c v, v, r, w'} (J.over U) (O.over U) MU) := by
  sorry

/-- Restriction of the actual double dual to a full subcategory preserved by duality.
Source: blueprint rational coefficient evaluation
(blueprint: lem-coef-rational-bidual-triangle-compatibility). -/
abbrev subBidual (T : ObjectProperty (D.{c, v, r, w} J O))
    (hT : ∀ V, T V → T ((dual.{c, v, r, w} J O).obj (op V))) :
    T.FullSubcategory ⥤ T.FullSubcategory :=
  T.lift (T.ι ⋙ bidual.{c, v, r, w} J O)
    (fun V ↦ hT _ (hT _ V.property))

/-- The same coefficient biduality components, regarded as arrows in the full subcategory.
Source: blueprint rational coefficient evaluation
(blueprint: lem-coef-rational-bidual-triangle-compatibility). -/
def subBidualMap (M : RingedSiteDualityModel.{c, v, r, w} J O)
    (T : ObjectProperty (D.{c, v, r, w} J O))
    (hT : ∀ V, T V → T ((dual.{c, v, r, w} J O).obj (op V))) :
    𝟭 T.FullSubcategory ⟶ subBidual.{c, v, r, w} J O T hT where
  app V := ObjectProperty.homMk ((bidualMap.{c, v, r, w} J O M).app V.obj)
  naturality _ _ f := ObjectProperty.hom_ext T
    ((bidualMap.{c, v, r, w} J O M).naturality f.hom)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The central action on sections determines the module category's linear structure.
Source: Stacks 0A8X, O-linear composition of sheaf maps
(blueprint: lem-coef-rational-bidual-triangle-compatibility).

Proof: multiply a module morphism sectionwise by rho(U,a). Naturality of rho and
semilinearity of restriction make this a sheaf morphism. Ring-map identities and
the module laws on sections give the module laws on Hom. Sectionwise composition
is bilinear. Finally the displayed equation determines every scalar multiple;
all remaining fields are proofs, so it uniquely determines the Linear structure.
-/
theorem coefficientLinear_existsUnique (A : Type a) [CommRing A]
    (rho : ∀ U : Cᵒᵖ, A →+* O.obj.obj U)
    (hnat : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (a : A),
      O.obj.map f (rho U a) = rho V a) :
    ∃! L : Linear A (Modules.{c, v, r} J O),
      (fun [lin : Linear A (Modules.{c, v, r} J O)] ↦
        ∀ (V W : Modules.{c, v, r} J O) (f : V ⟶ W) (a : A)
          (U : Cᵒᵖ) (x : V.val.obj U),
          ((a • f).val.app U) x = (rho U a) • (f.val.app U x)) (lin := L) := by
  sorry

/-- The unique sectionwise central-scalar structure; only its laws are postponed.
Source: Stacks 0A8X (blueprint: lem-coef-rational-bidual-triangle-compatibility). -/
@[instance_reducible]
def coefficientLinear (A : Type a) [CommRing A]
    (rho : ∀ U : Cᵒᵖ, A →+* O.obj.obj U)
    (hnat : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (a : A),
      O.obj.map f (rho U a) = rho V a) : Linear A (Modules.{c, v, r} J O) :=
  (coefficientLinear_existsUnique.{c, v, r, w, a} J O A rho hnat).exists.choose

/-- Central coefficient scalars make the restricted double dual additive and linear.
The section formula specifies the induced module-category action, so the Linear
instance is an encoding of that action and is not an assumption that duality is linear.
Source: Stacks 0A8X and scalar localization of the blueprint coefficient categories
(blueprint: lem-coef-rational-bidual-triangle-compatibility).

Proof (DAG step 11): on complexes, precomposition by r*f is r times precomposition
by f, since r acts centrally on the coefficient sheaf. The Hom differential and
homotopies respect this equality. Twice applying Hom gives the same equality.
Localization at quasi-isomorphisms computes a morphism as a roof; move the scalar
to its numerator. Common denominators prove additivity. Full-subcategory inclusion
is faithful and its Hom modules have the inherited action, proving both assertions.
-/
theorem subBidual_linear (A : Type a) [CommRing A]
    (rho : ∀ U : Cᵒᵖ, A →+* O.obj.obj U)
    (hnat : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (a : A),
      O.obj.map f (rho U a) = rho V a)
    [Linear A (Modules.{c, v, r} J O)]
    (hact : ∀ (V W : Modules.{c, v, r} J O) (f : V ⟶ W) (a : A)
      (U : Cᵒᵖ) (x : V.val.obj U),
      ((a • f).val.app U) x = (rho U a) • (f.val.app U x))
    (T : ObjectProperty (D.{c, v, r, w} J O))
    (hT : ∀ V, T V → T ((dual.{c, v, r, w} J O).obj (op V))) :
    (subBidual.{c, v, r, w} J O T hT).Additive ∧
      (subBidual.{c, v, r, w} J O T hT).Linear A := by
  sorry

/-- Descent to the raw scalar localization, with the original subcategory's exact
triangles and the induced shift. The structural binders and the two normalizations
are exactly the structures supplied by exists_triangulated_scalarLocalization.
Pure-tensor equations pin down the descended functor, transformation and shift map.
Source: scalar localization and blueprint lem-coef-rational-retract-evaluation,
proof paragraph 3 (blueprint: lem-coef-rational-bidual-triangle-compatibility).

Proof (DAG steps 11--13): subBidual_linear proves linearity before extending scalars.
Extend the double-dual functor by a tensor f ↦ a tensor F(f), and d and its signed
shift comparison by tensoring with one. The balancing relation holds by linearity;
composition, naturality and shift compatibility follow on pure tensors and extend
by additivity. Every distinguished triangle in the raw localization is isomorphic
to the localization of an original distinguished triangle. Its image is therefore
distinguished, and the original three naturality squares tensored with one give
its bidual triangle morphism. Transport across the triangle isomorphism gives the
same assertion for arbitrary fraction arrows. Apply triangle two-out-of-three to
this exact functor and the identity. Applying an invertible shift comparison in
each direction proves shift closure. No idempotent completion and no invertibility
of a general biduality component is used. -/
theorem scalarCompatibility (M : RingedSiteDualityModel.{c, v, r, w} J O)
    (A : Type a) [CommRing A]
    (rho : ∀ U : Cᵒᵖ, A →+* O.obj.obj U)
    (hnat : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (a : A),
      O.obj.map f (rho U a) = rho V a)
    : (fun [lin : Linear A (Modules.{c, v, r} J O)] ↦
      ∀ (T : ObjectProperty (D.{c, v, r, w} J O)) [T.IsTriangulated]
    (hT : ∀ V, T V → T ((dual.{c, v, r, w} J O).obj (op V)))
    [(shiftFunctor T.FullSubcategory (1 : ℤ)).Linear A] (s : A)
    [HasZeroObject (ScalarLocalization A T.FullSubcategory s)]
    [HasShift (ScalarLocalization A T.FullSubcategory s) ℤ]
    [∀ n : ℤ, (shiftFunctor (ScalarLocalization A T.FullSubcategory s) n).Additive]
    [Pretriangulated (ScalarLocalization A T.FullSubcategory s)]
    [IsTriangulated (ScalarLocalization A T.FullSubcategory s)]
    [(ScalarLocalization.localization A T.FullSubcategory s).CommShift ℤ]
    [(ScalarLocalization.localization A T.FullSubcategory s).IsTriangulated]
    (hshift : shiftFunctor (ScalarLocalization A T.FullSubcategory s) (1 : ℤ) =
      ScalarLocalization.map A T.FullSubcategory s (shiftFunctor T.FullSubcategory (1 : ℤ)))
    (hQ : ∀ V : T.FullSubcategory,
      HEq (((ScalarLocalization.localization A T.FullSubcategory s).commShiftIso
        (1 : ℤ)).hom.app V)
        (𝟙 ((ScalarLocalization.localization A T.FullSubcategory s).obj (V⟦(1 : ℤ)⟧))))
    (hdist : ∀ B : Triangle (ScalarLocalization A T.FullSubcategory s),
      B ∈ distTriang _ ↔ ∃ B' : Triangle T.FullSubcategory, B' ∈ distTriang _ ∧
        Nonempty (B ≅ (ScalarLocalization.localization A T.FullSubcategory s).mapTriangle.obj B')),
    (fun [comm : (bidual.{c, v, r, w} J O).CommShift ℤ] ↦
      ∃ F : ScalarLocalization A T.FullSubcategory s ⥤ ScalarLocalization A T.FullSubcategory s,
      ∃ d : 𝟭 _ ⟶ F,
      ∃ cs : F.CommShift ℤ,
        (fun [fcomm : F.CommShift ℤ] ↦
          F.IsTriangulated ∧ NatTrans.CommShift d ℤ ∧
          (∀ V : ScalarLocalization A T.FullSubcategory s,
            F.obj V = ⟨(subBidual.{c, v, r, w} J O T hT).obj V.obj⟩) ∧
          (∀ (V W : T.FullSubcategory) (f : V ⟶ W) (a : Localization.Away s),
            HEq (F.map (a ⊗ₜ[A] f :
                (ScalarLocalization.localization A T.FullSubcategory s).obj V ⟶
                  (ScalarLocalization.localization A T.FullSubcategory s).obj W))
              (a ⊗ₜ[A] (subBidual.{c, v, r, w} J O T hT).map f)) ∧
          (∀ V : T.FullSubcategory,
            HEq (d.app ((ScalarLocalization.localization A T.FullSubcategory s).obj V))
              ((1 : Localization.Away s) ⊗ₜ[A]
                (subBidualMap.{c, v, r, w} J O M T hT).app V)) ∧
          (∀ V : T.FullSubcategory,
            HEq ((F.commShiftIso (1 : ℤ)).hom.app
              ((ScalarLocalization.localization A T.FullSubcategory s).obj V))
              ((1 : Localization.Away s) ⊗ₜ[A]
                ((subBidual.{c, v, r, w} J O T hT).commShiftIso (1 : ℤ)).hom.app V)) ∧
          (∀ B : Triangle (ScalarLocalization A T.FullSubcategory s), B ∈ distTriang _ →
            ∃ f : B ⟶ F.mapTriangle.obj B,
              f.hom₁ = d.app B.obj₁ ∧ f.hom₂ = d.app B.obj₂ ∧ f.hom₃ = d.app B.obj₃) ∧
          (∀ (V : ScalarLocalization A T.FullSubcategory s) (n : ℤ),
            IsIso (d.app (V⟦n⟧)) ↔ IsIso (d.app V)) ∧
          (∀ B : Triangle (ScalarLocalization A T.FullSubcategory s), B ∈ distTriang _ →
            (IsIso (d.app B.obj₁) → IsIso (d.app B.obj₂) → IsIso (d.app B.obj₃)) ∧
            (IsIso (d.app B.obj₁) → IsIso (d.app B.obj₃) → IsIso (d.app B.obj₂)) ∧
            (IsIso (d.app B.obj₂) → IsIso (d.app B.obj₃) → IsIso (d.app B.obj₁))))
          (fcomm := cs)) (comm := canonicalCommShift.{c, v, r, w} J O M))
      (lin := coefficientLinear.{c, v, r, w, a} J O A rho hnat) := by
  sorry

end CategoryTheory.CoefficientBidualTriangles
