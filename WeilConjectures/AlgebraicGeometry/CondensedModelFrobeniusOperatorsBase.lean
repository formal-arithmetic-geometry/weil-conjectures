/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
public import WeilConjectures.SixFunctors.SchemeFrobenius
public import WeilConjectures.AlgebraicGeometry.CondensedFrobeniusLinearTrivialization
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleConeCounterexample
public import WeilConjectures.SixFunctors.DerivedConstructibleLowerShriek
public import WeilConjectures.AlgebraicGeometry.CondensedOpenProperPasting
public import WeilConjectures.TraceFormula.CompactCohomology
public import WeilConjectures.TraceFormula.Statement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence


/-! # Model and semilinear Frobenius operators

Source: literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/
sk-p-dl-a1-some-weight/lem-fd-realness-pushforward.proof.md, Step 1
(blueprint: lem-fd-condensed-model-frobenius-operators).

The helpers write the canonical maps on the ordinary derived module categories.
Compact-support operators are compared through the published compactification independence
isomorphism, before taking cohomology or traces.

## Main definitions and statement

* `kappa`, `modelStructure`: the canonical linearized model structures.
* `compactReturn`, `stalkReturn`: the semilinear global and local returns.
* `condensed_model_frobenius_operators`: equality with the published model operators.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.ModelSemilinearComparison

open CondensedOpenProper

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Iteration with the actual pullback compositors, including the identity unitor.
Source: source Step 1, iteration of theta
(blueprint: lem-fd-condensed-model-frobenius-operators). -/
def iterateStructure {T : Scheme.{u}} (f : End T) {K : D Λ T}
    (θ : (P Λ f).obj K ≅ K) : (m : ℕ) → (P Λ (f ^ m)).obj K ≅ K
  | 0 => (pId Λ T).app K
  | m + 1 =>
    (eqToIso (congrArg (fun h : End T ↦ (P Λ h).obj K) (pow_succ f m))) ≪≫
      (pComp Λ f (f ^ m)).app K ≪≫ (P Λ f).mapIso (iterateStructure f θ m) ≪≫ θ

/-- The specified module-linear kappa, using the equality of scheme maps and the
termwise absolute-Frobenius trivialization; its data involve no choice of an isomorphism.
Source: source Step 1, displayed kappa
(blueprint: lem-fd-condensed-model-frobenius-operators). -/
def kappa {T : Scheme.{u}} (p : ℕ) (hp : p.Prime) (hT : (p : Γ(T, ⊤)) = 0)
    (b : ℕ) (g φ : T ⟶ T) (w : φ = T.iterateFrobenius hp hT b ≫ g) :
    P Λ φ ≅ P Λ g :=
  eqToIso (congrArg (P Λ) w) ≪≫
    pComp Λ (T.iterateFrobenius hp hT b) g ≪≫
    Functor.isoWhiskerLeft (P Λ g)
      (Functor.mapDerivedCategoryNatIso (upperStarIterateFrobeniusIso Λ hp hT b) ≪≫
        Functor.mapDerivedCategoryIdIso _) ≪≫ Functor.rightUnitor _

/-- Canonical point reparametrization on modules, localized termwise.
Source: source Step 1, point normalization
(blueprint: lem-fd-condensed-model-frobenius-operators). -/
def pointReparametrization {k : Type u} [Field k] [IsSepClosed k]
    (g : Spec (.of k) ⟶ Spec (.of k)) : P Λ g ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryNatIso (upperStarIsoIdOfIsSepClosed Λ g) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- The proper exchange is the mate of the specified pullback square comparison.
Source: source Step 1, proper-mate calculation
(blueprint: lem-fd-condensed-model-frobenius-operators). -/
def properExchange {Z S : Scheme.{u}} (p : Z ⟶ S) (gZ : Z ⟶ Z) (gS : S ⟶ S)
    (w : gZ ≫ p = p ≫ gS) : R Λ p ⋙ P Λ gS ⟶ P Λ gZ ⋙ R Λ p :=
  Adjunction.exchangeRight
    (upperStarLowerStarAdjunction Λ p).mapDerivedCategoryRightDerivedAdjunction
    (upperStarLowerStarAdjunction Λ p).mapDerivedCategoryRightDerivedAdjunction
    ((pComp Λ p gS).symm ≪≫ eqToIso (congrArg (P Λ) w.symm) ≪≫ pComp Λ gZ p)

/-- The canonical compact exchange in a Frobenius-stable compactification is proper
exchange followed by inverse open mate. The total inverse is the existing operation;
the open mate is invertible on the present Cartesian automorphism squares.
Source: source Step 1, compactification recipe e_m
(blueprint: lem-fd-condensed-model-frobenius-operators). -/
def compactExchange {X Z S : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (p : Z ⟶ S) (gX : X ⟶ X) (gZ : Z ⟶ Z) (gS : S ⟶ S)
    (wj : gX ≫ j = j ≫ gZ) (wp : gZ ≫ p = p ≫ gS) :
    (J Λ j ⋙ R Λ p) ⋙ P Λ gS ⟶ P Λ gX ⋙ (J Λ j ⋙ R Λ p) :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (J Λ j) (properExchange Λ p gZ gS wp) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (comparisonInverse (openMap Λ (CommSq.mk wj))) (R Λ p) ≫
    (Functor.associator _ _ _).hom

/-- Semilinear compact-support return, with point reparametrization first.
Source: source Step 1, definition of F_g,c
(blueprint: lem-fd-condensed-model-frobenius-operators). -/
def compactReturn {X Z : Scheme.{u}} {k : Type u} [Field k] [IsSepClosed k]
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Spec (.of k))
    (gX : X ⟶ X) (gZ : Z ⟶ Z) (gS : Spec (.of k) ⟶ Spec (.of k))
    (wj : gX ≫ j = j ≫ gZ) (wp : gZ ≫ p = p ≫ gS)
    {K : D Λ X} (θ : (P Λ gX).obj K ⟶ K) :
    End ((J Λ j ⋙ R Λ p).obj K) :=
  (pointReparametrization Λ gS).inv.app ((J Λ j ⋙ R Λ p).obj K) ≫
    (compactExchange Λ j p gX gZ gS wj wp).app K ≫ (J Λ j ⋙ R Λ p).map θ

/-- The local return is the pullback-square comparison followed by the Weil structure.
Source: source Step 1, local return
(blueprint: lem-fd-condensed-model-frobenius-operators). -/
def stalkReturn {X : Scheme.{u}} {k : Type u} [Field k] [IsSepClosed k]
    (x : Spec (.of k) ⟶ X) (gX : X ⟶ X)
    (gS : Spec (.of k) ⟶ Spec (.of k)) (w : x ≫ gX = gS ≫ x)
    {K : D Λ X} (θ : (P Λ gX).obj K ⟶ K) : End ((P Λ x).obj K) :=
  (pointReparametrization Λ gS).inv.app ((P Λ x).obj K) ≫
    (pComp Λ gS x).inv.app K ≫
    (eqToIso (congrArg (fun f ↦ (P Λ f).obj K) w.symm)).hom ≫
    (pComp Λ x gX).hom.app K ≫ (P Λ x).map θ

end AlgebraicGeometry.ProEtale.CondensedRing.ModelSemilinearComparison

namespace AlgebraicGeometry.ProEtale.CondensedRing.ModelSemilinearComparison

open CondensedOpenProper

/-- Characteristic supplied by the finite-field datum, with no extra characteristic assumption.
Source: source Step 1, finite-field conventions
(blueprint: lem-fd-condensed-model-frobenius-operators). -/
instance datumCharP (D : WeilConjectures.FiniteFieldDatum.{u}) : CharP D.k D.p :=
  letI := Fintype.ofFinite D.k₀
  letI : Fact D.p.Prime := ⟨D.prime⟩
  letI : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card).symm.trans (D.card_base.trans D.cardinality_eq))
  charP_of_injective_algebraMap' D.k₀ D.p

/-- The prime characteristic instance used by the published model-operator interface.
Source: source Step 1, finite-field conventions
(blueprint: lem-fd-condensed-model-frobenius-operators). -/
instance datumPrime (D : WeilConjectures.FiniteFieldDatum.{u}) :
    Fact (ringChar D.k).Prime :=
  ⟨(ringChar.eq D.k D.p).symm ▸ D.prime⟩

/-- The coefficient-characteristic inequality in the published interface.
Source: source Step 1, ell different from p
(blueprint: lem-fd-condensed-model-frobenius-operators). -/
instance datumDifferent (D : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ)
    [Fact (ell ≠ D.p)] : Fact (ringChar D.k ≠ ell) :=
  ⟨(ringChar.eq D.k D.p).symm ▸ (Fact.out : ell ≠ D.p).symm⟩

/-- Separable closedness furnished by the specified algebraic closure.
Source: source Step 1, geometric coefficient point
(blueprint: lem-fd-condensed-model-frobenius-operators). -/
instance datumSepClosed (D : WeilConjectures.FiniteFieldDatum.{u}) : IsSepClosed D.k :=
  letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  inferInstance

/-- The standard finite-type base-change instance for the geometric fiber.
Source: source Step 1, geometric fiber
(blueprint: lem-fd-condensed-model-frobenius-operators). -/
instance geometricFiberLft (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    LocallyOfFiniteType (D.geometricFiber X₀).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd X₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- The standard quasi-compact base-change instance for the geometric fiber.
Source: source Step 1, geometric fiber
(blueprint: lem-fd-condensed-model-frobenius-operators). -/
instance geometricFiberQc (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    QuasiCompact (D.geometricFiber X₀).hom :=
  inferInstanceAs (QuasiCompact (pullback.snd X₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- The standard separated base-change instance for the geometric fiber.
Source: source Step 1, geometric fiber
(blueprint: lem-fd-condensed-model-frobenius-operators). -/
instance geometricFiberSep (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom] : IsSeparated (D.geometricFiber X₀).hom :=
  inferInstanceAs (IsSeparated (pullback.snd X₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- The recorded model Frobenius, bundled as an endomorphism over the geometric point.
Source: source Step 1, Phi_X (blueprint: lem-fd-condensed-model-frobenius-operators). -/
@[irreducible] def modelEnd (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    End (D.geometricFiber X₀) :=
  Over.homMk (D.schemeFrobenius X₀) (D.relativeFrobenius_projections X₀).2

/-- A model compactification, base changed to the geometric point.
Source: source Step 1, compactification paragraph
(blueprint: lem-fd-condensed-model-frobenius-operators). -/
def geometricCompactification (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (c₀ : Compactification X₀.hom) : Compactification (D.geometricFiber X₀).hom :=
  c₀.baseChange (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))

/-- The ambient structure of a strict finite-Tor pair, through the full inclusion.
Source: source Step 1, strict pair (blueprint: lem-fd-condensed-model-frobenius-operators). -/
def ambientStructure (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {T : Scheme.{u}} {g : T ≅ T}
    (K : StrictWeil.Complex Λ g) : (P Λ g.hom).obj K.carrier.obj ≅ K.carrier.obj :=
  (ObjectProperty.ι _).mapIso K.str

section ModelOperators

variable (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]

/-- Restriction of the specified ambient model structure through the full inclusion.
The exact-to-total-derived comparison is inserted before u.
Source: source Step 1, model Weil object
(blueprint: lem-fd-condensed-model-frobenius-operators). -/
def modelObject (φ : X ⟶ X)
    (B : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ell) X.left))
    (uφ : (P (Profinite.padicAlgClRingObj ell) φ.left).obj B.obj ≅ B.obj) :
    WeilBoundedConstructible ell φ :=
  CategoryTheory.Endofunctor.IsoAlgebra.mk B
    (ObjectProperty.isoMk _
      ((boundedConstructibleUpperStarCompatibility
        (Profinite.padicAlgClRingObj ell) ell φ).app B ≪≫
        (leftDerivedUpperStarIsoMapDerivedCategory
          (Profinite.padicAlgClRingObj ell) φ.left).app B.obj ≪≫ uφ))

/-- The model globalOperator of degree one for the pair with structure u_m, in the
ambient category. Its existing definition uses the relative unit and shriek composition.
Source: source Step 1, model globalOperator
(blueprint: lem-fd-condensed-model-frobenius-operators). -/
def modelGlobal (φ : X ⟶ X) (hfin : IsFinite φ.left)
    (huh : IsUniversalHomeomorphism φ.left) (B : WeilBoundedConstructible ell φ) :=
  letI := hfin
  letI := huh
  letI : IsFinite (frobeniusIterate φ 1).left :=
    (congrArg (fun f : X ⟶ X ↦ IsFinite f.left) (frobeniusIterate_one φ)).symm ▸ hfin
  letI : IsUniversalHomeomorphism (frobeniusIterate φ 1).left :=
    (congrArg (fun f : X ⟶ X ↦ IsUniversalHomeomorphism f.left)
      (frobeniusIterate_one φ)).symm ▸ huh
  (B.globalOperator 1).hom

/-- The canonical identification of chosen compact supports with any supplied
compactification: the published common-refinement comparison, then ambient compatibility.
Source: source Step 1, choice independence
(blueprint: lem-fd-condensed-model-frobenius-operators). -/
def compactIdentification (c : Compactification X.hom)
    (B : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ell) X.left)) :
    ((boundedConstructibleLowerShriek ell (toPoint X)).obj B).obj ≅
      (rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj ell) c).obj B.obj :=
  let d : Compactification (toPoint X).left := c.copy (toPoint_left X)
  let e : (boundedConstructibleLowerShriek ell (toPoint X)).obj B ≅
      (boundedConstructibleLowerShriekOfCompactification ell d).obj B :=
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ell
      (compactificationOverField (toPoint X)) d).app B
  (ObjectProperty.ι _).mapIso e ≪≫
    (boundedConstructibleLowerShriekOfCompactificationCompatibility ell d).app B

/-- Model local Frobenius at a fixed rational point, in the ambient module category.
Source: source Step 1, stalkFrobenius (blueprint: lem-fd-condensed-model-frobenius-operators). -/
def modelLocal (φ : X ⟶ X) (B : WeilBoundedConstructible ell φ)
    (x : RationalPoint X) (hx : x ≫ φ = x) :=
  (((weilStalk ell φ x hx).obj B).frobenius.hom).hom

end ModelOperators

end AlgebraicGeometry.ProEtale.CondensedRing.ModelSemilinearComparison

namespace AlgebraicGeometry.ProEtale.CondensedRing.ModelSemilinearComparison

open CondensedOpenProper

variable (D₀ : WeilConjectures.FiniteFieldDatum.{u})
  (X₀ : Over (Spec (.of D₀.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- The factorization equality only transports between specified scheme maps. It is
proof-irrelevant; no comparison isomorphism is supplied as arbitrary input.
Source: source Step 1, Phi^m = g^m H_m
(blueprint: lem-fd-condensed-model-frobenius-operators). -/
abbrev Factorization := ∀ m : ℕ,
  (frobeniusIterate (modelEnd D₀ X₀) m).left =
    (D₀.geometricFiber X₀).left.iterateFrobenius D₀.prime
      (D₀.model_characteristic
        (pullback.fst X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D₀.k₀ D₀.k))) ≫
          X₀.hom)) (D₀.a * m) ≫
      (End.of (StrictWeil.modelFrobenius D₀ X₀).hom) ^ m

/-- Kappa followed by the canonical iterate of the strict semilinear structure.
Source: source Step 1, u_m (blueprint: lem-fd-condensed-model-frobenius-operators). -/
def modelStructure (ell : ℕ) [Fact ell.Prime]
    (K : StrictWeil.Complex (Profinite.padicAlgClRingObj ell)
      (StrictWeil.modelFrobenius D₀ X₀)) (w : Factorization D₀ X₀) (m : ℕ) :
    (P (Profinite.padicAlgClRingObj ell) (frobeniusIterate (modelEnd D₀ X₀) m).left).obj
      K.carrier.obj ≅ K.carrier.obj :=
  (kappa (Profinite.padicAlgClRingObj ell) D₀.p D₀.prime
    (D₀.model_characteristic
      (pullback.fst X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D₀.k₀ D₀.k))) ≫ X₀.hom))
    (D₀.a * m) ((End.of (StrictWeil.modelFrobenius D₀ X₀).hom) ^ m)
    (frobeniusIterate (modelEnd D₀ X₀) m).left (w m)).app K.carrier.obj ≪≫
    iterateStructure (Profinite.padicAlgClRingObj ell)
      (End.of (StrictWeil.modelFrobenius D₀ X₀).hom) (ambientStructure _ K) m

/-- Degree one of u, with the canonical equality Phi^1 = Phi inserted.
Source: source Step 1, u_1 (blueprint: lem-fd-condensed-model-frobenius-operators). -/
def modelOne (ell : ℕ) [Fact ell.Prime]
    (K : StrictWeil.Complex (Profinite.padicAlgClRingObj ell)
      (StrictWeil.modelFrobenius D₀ X₀)) (w : Factorization D₀ X₀) :
    (P (Profinite.padicAlgClRingObj ell) (modelEnd D₀ X₀).left).obj K.carrier.obj ≅
      K.carrier.obj :=
  eqToIso (congrArg
    (fun f : End (D₀.geometricFiber X₀) ↦
      (P (Profinite.padicAlgClRingObj ell) f.left).obj K.carrier.obj)
    (frobeniusIterate_one (modelEnd D₀ X₀)).symm) ≪≫ modelStructure D₀ X₀ ell K w 1

/-- Iteration of u_1 with the equality between over-category and scheme powers inserted.
Source: source Step 1, canonical associators
(blueprint: lem-fd-condensed-model-frobenius-operators). -/
def modelIterate (ell : ℕ) [Fact ell.Prime]
    (K : StrictWeil.Complex (Profinite.padicAlgClRingObj ell)
      (StrictWeil.modelFrobenius D₀ X₀)) (w : Factorization D₀ X₀) (m : ℕ) :
    (P (Profinite.padicAlgClRingObj ell) (frobeniusIterate (modelEnd D₀ X₀) m).left).obj
      K.carrier.obj ≅ K.carrier.obj :=
  eqToIso (congrArg
    (fun f ↦ (P (Profinite.padicAlgClRingObj ell) f).obj K.carrier.obj)
    (frobeniusIterate_left (modelEnd D₀ X₀) m)) ≪≫
    iterateStructure (Profinite.padicAlgClRingObj ell) (modelEnd D₀ X₀).left
      (modelOne D₀ X₀ ell K w) m

/-- The local full-subcategory and exact-descent identifications.
Source: source Step 1, derived stalk comparison
(blueprint: lem-fd-condensed-model-frobenius-operators). -/
def localIdentification (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom]
    (B : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ell) X.left))
    (x : RationalPoint X) :
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ell) ell x).obj B).obj ≅
      (P (Profinite.padicAlgClRingObj ell) x.left).obj B.obj :=
  (boundedConstructibleUpperStarCompatibility (Profinite.padicAlgClRingObj ell) ell x).app B ≪≫
    (leftDerivedUpperStarIsoMapDerivedCategory (Profinite.padicAlgClRingObj ell) x.left).app B.obj

end AlgebraicGeometry.ProEtale.CondensedRing.ModelSemilinearComparison
