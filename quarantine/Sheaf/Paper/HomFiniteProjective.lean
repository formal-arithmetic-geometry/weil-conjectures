/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Sheaf.Paper.SixFunctorDatum
public import Sheaf.Paper.SitePerfectComplex
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.Algebra.Homology.HomComplexProjections

/-!
# Internal Hom out of locally finite projective coefficient modules

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-sf-rf-shriek-preservation/lem-sf-hom-finite-projective;
Stacks Project, sites-cohomology.tex, Tag 08JJ
(blueprint: lem-sf-hom-finite-projective).

The predicates express the degree-zero cases of the recorded site-perfect local
models. Rational splittings are taken after localization; common-stage objects may
have any isomorphic finite-stage representative. All arrows are the published
normalized evaluation transposes of the given six-functor datum.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u c v r w a b
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

/-- Covering sieves supply finite-free retractions of the restricted module sheaf.
Ranks may vary and may be zero. Source: blueprint local sheaf convention; Stacks 08JJ
(blueprint: lem-sf-hom-finite-projective). -/
def IsLocallyFiniteProjectiveCoefficientSheaf
    {T : Type c} [Category.{v} T] {J : GrothendieckTopology T}
    (R : Sheaf J RingCat.{max c v r}) (P : SheafOfModules.{max c v r} R) : Prop :=
  ∀ V : T, ∃ S : Sieve V, S ∈ J V ∧
    ∀ (U : T) (f : U ⟶ V), S f → ∃ m : ℕ,
      ∃ (i : (SheafOfModules.overFunctor R U).obj P ⟶
          ∏ᶜ fun _ : Fin m ↦ SheafOfModules.unit (R.over U))
        (p : (∏ᶜ fun _ : Fin m ↦ SheafOfModules.unit (R.over U)) ⟶
          (SheafOfModules.overFunctor R U).obj P), i ≫ p = 𝟙 _

/-- The degree-zero essential image of the locally finite-projective module sheaves.
Source: blueprint degree-zero convention (blueprint: lem-sf-hom-finite-projective). -/
def IsFiniteProjectiveCoefficientDegreeZero
    {T : Type c} [Category.{v} T] {J : GrothendieckTopology T}
    (R : Sheaf J RingCat.{max c v r})
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r} R)]
    (K : DerivedCategory (SheafOfModules.{max c v r} R)) : Prop :=
  ∃ P : SheafOfModules.{max c v r} R, IsLocallyFiniteProjectiveCoefficientSheaf.{c, v, r} R P ∧
    Nonempty (K ≅ (DerivedCategory.singleFunctor _ 0).obj P)

/-- Degree-zero rational local models, with splittings after localization.
Neither the splitting nor the degree-zero representative must lift integrally.
Source: def-weil-site-perfect-complex in degree zero
(blueprint: lem-sf-hom-finite-projective). -/
def IsRationalFiniteProjectiveCoefficient (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (K : sfRationalConstructibleCategory l E X) : Prop :=
  ∀ V : X.ProEt, ∃ S : Sieve V, S ∈ Scheme.ProEt.topology X V ∧
    ∀ (U : X.ProEt) (f : U ⟶ V), S f →
      ∃ P : integralTowerModules l E U.left,
        IsRationalFiniteProjectiveTerm l E U.left P ∧
        Nonempty ((ScalarLocalization.mk
          ((integralDerivedPullback l E U.hom).obj K.obj.obj) :
            sitePerfectRationalAmbient l E U.left) ≅
          ScalarLocalization.mk ((DerivedCategory.singleFunctor _ 0).obj P))

/-- A common-stage object has a degree-zero finite-projective representative at some
finite coefficient field, up to isomorphism in the actual common-stage category.
Source: def-weil-site-perfect-complex (blueprint: lem-sf-hom-finite-projective). -/
def IsCommonStageFiniteProjectiveCoefficient (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (X : Scheme.{u}) (K : generalAlgebraicallyClosedConstructibleCategory l Ω X) : Prop :=
  ∃ E : AlgebraicallyClosedCoefficients.Index l Ω,
    ∃ P : GeneralAlgebraicallyClosedCoefficients.Stage l Ω X E,
      IsRationalFiniteProjectiveCoefficient l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) X P ∧
      Nonempty (K ≅ (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := Ω) (Y := X) E).obj P)

/-- Invertibility of the specified canonical bidual and evaluation transformation,
with contravariant naturality in the first variable. The natural transformation
already includes covariant naturality in every second variable.
Source: blueprint arrows and naturality clause (blueprint: lem-sf-hom-finite-projective). -/
def FiniteProjectiveCoefficientHomFormula
    {B : Type a} [Category.{b} B] {H : Bᵒᵖ × B ⥤ B}
    (M : CoefficientClosedStructure H) (s : @SymmetricCategory B _ M.monoidal)
    (F : ObjectProperty B) : Prop :=
  (∀ P : B, F P →
    IsIso (ringedSiteBidual M s M.monoidal.tensorUnit P) ∧
    IsIso (ringedSiteDualEvaluationLeftNatTrans M s M.monoidal.tensorUnit (Iso.refl _) P)) ∧
  ∀ (P P' : B), F P → F P' → ∀ (f : P' ⟶ P) (N : B),
    M.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 M.monoidal.tensorUnit))) (𝟙 N)) ≫
        ringedSiteDualEvaluationLeft M s M.monoidal.tensorUnit (Iso.refl _) P' N =
      ringedSiteDualEvaluationLeft M s M.monoidal.tensorUnit (Iso.refl _) P N ≫
        H.map (Prod.mkHom f.op (𝟙 N))

namespace FiniteProjectiveOrdinaryDual

variable {T : Type c} [Category.{v} T] {J : GrothendieckTopology T}
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

/-- The modules over the recorded coefficient ring, with independent site universes.
Source: Stacks 08JJ, proof step 1 (blueprint: lem-sf-hom-finite-projective). -/
abbrev Modules (R : Sheaf J CommRingCat.{max c v r}) := SheafOfModules.{max c v r}
  ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)

/-- Ordinary sheaf dual, using the declaration of def-pur-sheaf-hom.
Source: Stacks 08JJ, proof steps 2--5 (blueprint: lem-sf-hom-finite-projective). -/
abbrev dual (P : Modules.{c, v, r} R) :=
  SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R) P (SheafOfModules.unit _)

/-- Degree-zero complex of the actual module sheaf.
Source: Stacks 08JJ, proof step 5 (blueprint: lem-sf-hom-finite-projective). -/
abbrev single (P : Modules.{c, v, r} R) := (CochainComplex.singleFunctor _ (0 : ℤ)).obj P

/-- Evaluation uniquely determines the ordinary bidual map on every slice.
The equal-universe upstream SheafOfModules.bidual has this same formula; here
site objects and morphisms retain their independent universes.
Source: Stacks 08JJ, proof steps 2--3 (blueprint: lem-sf-hom-finite-projective).
Proof: send x to the local functional phi |-> phi(x). Restriction of x to each
slice and evaluation at its identity object commute with further restriction.
Linearity in phi and x follows from the module-map laws. These formulas give a
module-sheaf map. Extensionality on all slice sections proves uniqueness. -/
theorem bidual_existsUnique (P : Modules.{c, v, r} R) :
    ∃! d : P ⟶ dual.{c, v, r} R (dual.{c, v, r} R P),
      ∀ (U : Tᵒᵖ) (x : P.val.obj U) (W : (Over U.unop)ᵒᵖ)
        (φ : (dual.{c, v, r} R P).val.obj (op W.unop.left)),
        (((d.val.app U).hom x).app W).hom φ =
          (φ.app (op (Over.mk (𝟙 W.unop.left)))).hom
            (P.val.map W.unop.hom.op x) := by
  sorry

/-- The ordinary bidual arrow specified by evaluation, not a derived bidual.
Source: Stacks 08JJ, proof step 3 (blueprint: lem-sf-hom-finite-projective). -/
def bidual (P : Modules.{c, v, r} R) : P ⟶ dual.{c, v, r} R (dual.{c, v, r} R P) :=
  (bidual_existsUnique.{c, v, r} R P).choose

/-- Projection onto the ordinary (0,0) factor of the Hom complex.
Source: Stacks 0A8X and 08JJ, proof step 5
(blueprint: lem-sf-hom-finite-projective). -/
def zeroProjection (P : Modules.{c, v, r} R) :
    (homComplex.{c, v, max c v r, max c v r} (R := R)
      (single.{c, v, r} R P) (single.{c, v, r} R (SheafOfModules.unit _))).X 0 ⟶
      SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R) ((single.{c, v, r} R P).X 0)
        ((single.{c, v, r} R (SheafOfModules.unit _)).X 0) :=
  (homComplex_projections_exists.{c, v, max c v r, max c v r}
    (C := T) (J := J) (R := R)).choose
    (single.{c, v, r} R P) (single.{c, v, r} R (SheafOfModules.unit _)) 0 0 0 rfl

/-- The unique inclusion of ordinary evaluation into the degree-zero Hom complex.
It sends a local functional to that same functional in the (0,0) factor.
Source: Stacks 0A8X and 08JJ, proof step 5
(blueprint: lem-sf-hom-finite-projective).
Proof: in degree zero the product has only its (0,0) factor nonzero; insert the
functional there and zero into all other factors. In every other total degree
all factors vanish. The product universal property gives the map and its
uniqueness. Both single-complex differentials vanish, so it is a chain map. -/
theorem singleHomMap_existsUnique (P : Modules.{c, v, r} R) :
    ∃! e : single.{c, v, r} R (dual.{c, v, r} R P) ⟶
        homComplex.{c, v, max c v r, max c v r} (R := R)
          (single.{c, v, r} R P) (single.{c, v, r} R (SheafOfModules.unit _)),
      e.f 0 ≫ zeroProjection.{c, v, r} R P =
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (dual.{c, v, r} R P)).hom ≫
          SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R)
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 P).hom
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
              (SheafOfModules.unit _)).inv := by
  sorry

/-- The evaluation-normalized inclusion, uniquely fixed by its ordinary Hom factor.
Source: Stacks 08JJ, proof step 5 (blueprint: lem-sf-hom-finite-projective). -/
def singleHomMap (P : Modules.{c, v, r} R) : single.{c, v, r} R (dual.{c, v, r} R P) ⟶
    homComplex.{c, v, max c v r, max c v r} (R := R)
      (single.{c, v, r} R P) (single.{c, v, r} R (SheafOfModules.unit _)) :=
  (singleHomMap_existsUnique.{c, v, r} R P).choose

variable [HasDerivedCategory.{w} (Modules.{c, v, r} R)]

/-- Ordinary dual to derived dual: insert evaluation into the Hom complex and then
postcompose with the fixed K-injective augmentation of the coefficient unit.
The final map transports a specified degree-zero presentation of K and the
specified coefficient-unit isomorphism of the ringed-site model.
Source: Stacks 08JJ, proof step 5 (blueprint: lem-sf-hom-finite-projective). -/
def comparison (M : RingedSiteDualityModel.{c, v, r, w} J R)
    (P : Modules.{c, v, r} R) (K : DerivedCategory (Modules.{c, v, r} R))
    (e : K ≅ DerivedCategory.Q.obj (single.{c, v, r} R P)) :
    DerivedCategory.Q.obj (single.{c, v, r} R (dual.{c, v, r} R P)) ⟶
      (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj
        (op K, M.closed.monoidal.tensorUnit) :=
  DerivedCategory.Q.map (singleHomMap.{c, v, r} R P) ≫
    ringedSiteOrdinaryHomComparison.{c, v, r, w} J R
      (single.{c, v, r} R P) (single.{c, v, r} R (SheafOfModules.unit _)) ≫
    (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
      (Prod.mkHom e.hom.op M.unitIso.inv)

/-- The ordinary bidual and the canonical ordinary-to-derived comparison are
invertible for each locally finite-projective degree-zero presentation in F.
The target of comparison is the actual ambient RHom into the model's unit.
Source: Stacks 08JJ, proof steps 3--5 (blueprint: lem-sf-hom-finite-projective). -/
def Formula {B : Type a} [Category.{b} B]
    (M : RingedSiteDualityModel.{c, v, r, w} J R)
    (F : B ⥤ DerivedCategory (Modules.{c, v, r} R)) : Prop :=
  ∀ (K : B) (P : Modules.{c, v, r} R),
    IsLocallyFiniteProjectiveCoefficientSheaf.{c, v, r} _ P →
    ∀ e : F.obj K ≅ DerivedCategory.Q.obj (single.{c, v, r} R P),
      IsIso (bidual.{c, v, r} R P) ∧ IsIso (comparison.{c, v, r, w} R M P (F.obj K) e)

end FiniteProjectiveOrdinaryDual

/-- Finite-projective evaluation and biduality at all four coefficient stages.
Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-sf-rf-shriek-preservation/lem-sf-hom-finite-projective; Stacks 08JJ
(blueprint: lem-sf-hom-finite-projective).

Proof:
1. Restrict ordinary and derived tensor-Hom to slices, using exact module
   restriction, the pullback tensor comparison, K-flat pullback, and internal-Hom
   restriction. Cohomology sheaves detect isomorphisms on covers by separatedness.
2. For R^m, evaluation on the standard basis identifies both sides with N^m.
   Its inverse is h |-> sum_j e_j-dual tensor h(e_j). Biduality is the identity
   in the double-dual bases, including m=0.
3. A local splitting i,p splits dual tensor and Hom contravariantly. The inverse
   evaluation is A(i) c_F^(-1) H(p); the bidual inverse is p delta_F^(-1) D^2(i).
   Both inverse equations reduce to i followed by p = id.
4. These finite-summand calculations show exactness of Hom(P,-) and flatness of
   P and its ordinary dual. Tensoring their degree-zero complexes with an acyclic
   complex is locally an acyclic finite-sum retract. Thus they are K-flat.
5. Take a flat-term K-flat representative M of N and a K-injective resolution
   M -> I. Termwise evaluation identifies dual(P) tensor M with Hom(P,M).
   Exactness makes Hom(P,M) -> Hom(P,I) a quasi-isomorphism. This is exactly the
   adjunction transpose of evaluation, identifying ordinary and derived duals.
   The helper singleHomMap inserts the ordinary functional into the (0,0) factor;
   comparison composes its derived image with the fixed K-injective augmentation.
   Formula asserts this specific map invertible and ordinary evaluation biduality
   for every finite or integral degree-zero presentation.
6. Both naturality composites send phi tensor m to x |-> phi(u(x)) v(m).
   Localization preserves the equality, including morphisms represented by roofs.
7. For completed integral coefficients finite sums and retractions commute with
   the products and 1-shift cone computing Rlim. The canonical completion map of
   N is invertible by completeness. On a free slice its finite sum identifies
   completed and ordinary dual-tensor; insertion of i,p gives the summand case.
   The strict reductions send phi tensor m and x to phi(x)m at every level,
   commuting with the product and cone maps, so the canonical evaluations agree.
8. At rational coefficients use the actual localized splittings in the same
   inverse formulas. No integral splitting is required. For local detection,
   finite type over k gives Noetherianity, finite dimension and ell invertible.
   The integral stratified-perfect characterization identifies the recorded
   integral category with that of the fully faithful continuous E realization.
   Scalar extension of restricted K-flat representatives commutes with restriction;
   the resulting image maps are locally invertible sheaf-derived maps, hence
   invertible by the cohomology sheaf test. Full faithfulness reflects inverses.
   At the algebraically closed stage put all objects and morphisms over a common
   finite field. Scalar comparisons preserve evaluation, retractions and the two
   inverse equations; directed Hom colimits preserve those equations and naturality.
   These are the normalized operations of the six-functor datum throughout. -/
theorem hom_finiteProjective
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorDatum D C E n hn) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom] :
    FiniteProjectiveCoefficientHomFormula (S.finiteClosed X).closed
      (S.finiteClosed X).symmetric
      (fun P ↦ IsFiniteProjectiveCoefficientDegreeZero.{u+1, u, u+1, u+2} _ P.obj.obj) ∧
    FiniteProjectiveOrdinaryDual.Formula _ (S.finiteModel X)
      ((S.toSixFunctorOperationDatum.finiteTorDomain X).ι ⋙
        (Scheme.intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι) ∧
    FiniteProjectiveCoefficientHomFormula (S.integralClosed X).closed
      (S.integralClosed X).symmetric
      (fun P ↦ IsFiniteProjectiveCoefficientDegreeZero.{u+1, u, u+1, u+2} _ P.obj.obj) ∧
    FiniteProjectiveOrdinaryDual.Formula _ (S.integralModel X)
      ((S.toSixFunctorOperationDatum.integralFiniteTorDomain X).ι ⋙
        (sfIntegralConstructible C.l E X.obj.left).ι) ∧
    FiniteProjectiveCoefficientHomFormula (S.rationalClosed X).closed
      (S.rationalClosed X).symmetric
      (fun P ↦ IsRationalFiniteProjectiveCoefficient C.l E X.obj.left P.obj) ∧
    FiniteProjectiveCoefficientHomFormula (S.commonClosed X).closed
      (S.commonClosed X).symmetric
      (fun P ↦ IsCommonStageFiniteProjectiveCoefficient C.l C.Qbar X.obj.left P.obj) := by
  sorry

end WeilConjectures
