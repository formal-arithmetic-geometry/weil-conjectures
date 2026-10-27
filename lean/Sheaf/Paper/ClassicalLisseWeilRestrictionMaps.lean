/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.Paper.ClassicalLisseWeilRestrictionData

/-! # Classical Weil restriction along finite-field frontiers

Source: blueprint `thm-zl-real-mixed-by-curves`, proof paragraphs 6--7;
BS 6.8.4, 6.8.14, 6.8.15
(blueprint: def-zl-classical-lisse-restriction-maps).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ZlFrontier
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]
variable (Ω : Type (u + 1)) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- Common-stage restriction on a literal finite representative is the recorded equality.
Source: blueprint common-stage convention
(blueprint: def-zl-classical-lisse-restriction-maps). -/
def stagePull {X Y : PerAdic.Base D.k} (f : X.scheme ⟶ Y.scheme)
    (E : Padic.FiniteCoefficientFields l Ω)
    (K : sfRationalConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) Y.scheme) :
    (pull D l Ω f).obj ((GeneralAlgebraicallyClosedCoefficients.inclusion E).obj K) ≅
      (GeneralAlgebraicallyClosedCoefficients.inclusion E).obj
        ((LisseRealization.pull D l (Fact.out : l ≠ D.p)
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
          (X := realizationBase D l X) (Y := realizationBase D l Y) f).obj K) :=
  eqToIso ((commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.1 _)

/-- The common-stage comparison is the finite quotient-normalized comparison, conjugated
by the specified stage identifications; it is not an arbitrary comparison.
Source: BS 6.8.4(4), 6.8.15
(blueprint: def-zl-classical-lisse-restriction-maps). -/
def RestrictionComparison.iso {R : Realization D l Ω}
    {S : ProEtale.CompletedLisse.System.{u} l}
    {A : LisseRealization.Family D l (Fact.out : l ≠ D.p)}
    (C : RestrictionComparison D l Ω R S A)
    {X Y : PerAdic.Base D.k} (f : X.scheme ⟶ Y.scheme)
    (E : Padic.FiniteCoefficientFields l Ω)
    (F : ProEtale.CompletedLisse.RawRational l (completedBase D l Ω Y E)) :
    (R.functor D l Ω X).obj ((model D l Ω X E).obj
      ((restriction D l Ω S f E).obj F)) ≅
        (pull D l Ω f).obj ((R.functor D l Ω Y).obj ((model D l Ω Y E).obj F)) :=
  (C.bridge X E).stage.app ((restriction D l Ω S f E).obj F) ≪≫
    (GeneralAlgebraicallyClosedCoefficients.inclusion E).mapIso
      ((C.finitePull X Y f E).app F).symm ≪≫
    (stagePull D l Ω f E ((C.bridge Y E).finite.obj F)).symm ≪≫
    (pull D l Ω f).mapIso ((C.bridge Y E).stage.app F).symm

/-- The restriction of a supplied realization, using the actual completed compositor.
Source: blueprint real-mixed-by-curves, paragraphs 6--7
(blueprint: def-zl-classical-lisse-restriction-maps). -/
def restrictIdentification {R : Realization D l Ω}
    {S : ProEtale.CompletedLisse.System.{u} l}
    {A : LisseRealization.Family D l (Fact.out : l ≠ D.p)}
    (C : RestrictionComparison D l Ω R S A)
    {X Y Z : PerAdic.Base D.k} (h : X.scheme ⟶ Y.scheme) (i : Y.scheme ⟶ Z.scheme)
    (E : Padic.FiniteCoefficientFields l Ω)
    (F : ProEtale.CompletedLisse.RawRational l (completedBase D l Ω Y E))
    (M : sfCommonStageHeart l Z.scheme Ω)
    (ρ : (R.functor D l Ω Y).obj ((model D l Ω Y E).obj F) ≅ (pull D l Ω i).obj M.obj) :
    (R.functor D l Ω X).obj
      ((model D l Ω X E).obj ((restriction D l Ω S h E).obj F)) ≅
        (pull D l Ω (h ≫ i)).obj M.obj :=
  C.iso D l Ω h E F ≪≫ (pull D l Ω h).mapIso ρ ≪≫
    ((zlPullComp l Ω h i).app M.obj).symm

/-- The geometric fibre with its actual finite-type structure map.
Source: blueprint fixed finite-field convention
(blueprint: def-zl-classical-lisse-restriction-maps). -/
def fiberBase (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom]
    [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom] : PerAdic.Base D.k where
  scheme := (D.geometricFiber Y₀).left
  «over» := ⟨(D.geometricFiber Y₀).hom⟩
  finiteTypeLocal := by
    change LocallyOfFiniteType (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    infer_instance
  finiteTypeCompact := by
    change QuasiCompact (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    infer_instance
  separated := by
    change IsSeparated (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    infer_instance

/-- Either the geometric fibre or its actual nilradical subscheme.
Source: blueprint real-mixed-by-curves, paragraph 6
(blueprint: def-zl-classical-lisse-restriction-maps). -/
def supportBase (Y : PerAdic.Base D.k) (reduced : Bool) : PerAdic.Base D.k :=
  if reduced then
    { scheme := Y.scheme.nilradical.subscheme
      «over» := ⟨Y.scheme.nilradical.subschemeι ≫ (Y.scheme ↘ Spec (.of D.k))⟩
      finiteTypeLocal := inferInstanceAs (LocallyOfFiniteType
        (Y.scheme.nilradical.subschemeι ≫ (Y.scheme ↘ Spec (.of D.k))))
      finiteTypeCompact := inferInstanceAs (QuasiCompact
        (Y.scheme.nilradical.subschemeι ≫ (Y.scheme ↘ Spec (.of D.k))))
      separated := inferInstanceAs (IsSeparated
        (Y.scheme.nilradical.subschemeι ≫ (Y.scheme ↘ Spec (.of D.k)))) }
  else Y

/-- The canonical locally closed stratum with its induced k-structure.
Source: blueprint real-mixed-by-curves, paragraph 6
(blueprint: def-zl-classical-lisse-restriction-maps). -/
def stratumBase (T : PerAdic.Base D.k)
    (P : Scheme.FiniteLocallyClosedStratification T.scheme) (ν : Fin P.n) :
    PerAdic.Base D.k :=
  letI : IsImmersion (P.immersion ν) := P.isImmersion ν
  letI : TopologicalSpace.NoetherianSpace (P.domain ν) :=
    (P.immersion ν).isEmbedding.isInducing.noetherianSpace
  { scheme := P.domain ν
    «over» := ⟨P.immersion ν ≫ (T.scheme ↘ Spec (.of D.k))⟩
    finiteTypeLocal := inferInstanceAs (LocallyOfFiniteType
      (P.immersion ν ≫ (T.scheme ↘ Spec (.of D.k))))
    finiteTypeCompact := inferInstanceAs (QuasiCompact
      (P.immersion ν ≫ (T.scheme ↘ Spec (.of D.k))))
    separated := inferInstanceAs (IsSeparated
      (P.immersion ν ≫ (T.scheme ↘ Spec (.of D.k)))) }

/-- A supplied partition and its chosen finite-field lattices, realizing exactly M.
Source: blueprint real-mixed-by-curves, paragraph 6; BS 6.8.4
(blueprint: def-zl-classical-lisse-restriction-maps). -/
structure PartitionData (R : Realization D l Ω) (T : PerAdic.Base D.k)
    (M : sfCommonStageHeart l T.scheme Ω) where
  partition : Scheme.FiniteLocallyClosedStratification T.scheme
  reduced : ∀ ν : Fin partition.n, IsReduced (partition.domain ν)
  field : Padic.FiniteCoefficientFields l Ω
  lattice : ∀ ν : Fin partition.n, ProEtale.CompletedLisse.RawRational l
    (completedBase D l Ω (stratumBase D T partition ν) field)
  classical : ∀ ν : Fin partition.n,
    LisseAlgebraicSheaf l (stratumBase D T partition ν).scheme Ω
  localization : ∀ ν : Fin partition.n,
    (model D l Ω (stratumBase D T partition ν) field).obj (lattice ν) ≅ classical ν
  realization : ∀ ν : Fin partition.n,
    (R.functor D l Ω (stratumBase D T partition ν)).obj (classical ν) ≅
      (pull D l Ω (X := stratumBase D T partition ν) (Y := T)
        (partition.immersion ν)).obj M.obj

/-- Realize the supplied localization identification and then its supplied restriction
identification, retaining the given classical system and lattice.
Source: blueprint real-mixed-by-curves, paragraph 6
(blueprint: def-zl-classical-lisse-restriction-maps). -/
def PartitionData.identification {R : Realization D l Ω} {T : PerAdic.Base D.k}
    {M : sfCommonStageHeart l T.scheme Ω} (P : PartitionData D l Ω R T M)
    (ν : Fin P.partition.n) :=
  (R.functor D l Ω (stratumBase D T P.partition ν)).mapIso (P.localization ν) ≪≫
    P.realization ν

/-- The actual ambient Weil restriction, with its prescribed compositor.
The square is j followed by ambient g = local h followed by j.
Source: blueprint real-mixed-by-curves, paragraph 7
(blueprint: def-zl-classical-lisse-restriction-maps). -/
def ambientRestriction {X Y : PerAdic.Base D.k} (j : X.scheme ⟶ Y.scheme)
    (g : Y.scheme ⟶ Y.scheme) (h : X.scheme ⟶ X.scheme)
    (square : j ≫ g = h ≫ j)
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω Y.scheme)
    (θ : (pull D l Ω g).obj M ≅ M) :
    (pull D l Ω h).obj ((pull D l Ω j).obj M) ≅ (pull D l Ω j).obj M :=
  ((zlPullComp l Ω h j).app M).symm ≪≫
    eqToIso (congrArg (fun f ↦ (pull D l Ω f).obj M) square.symm) ≪≫
    (zlPullComp l Ω j g).app M ≪≫ (pull D l Ω j).mapIso θ

/-- A literal coefficient-pair enlargement; its fibre is the recorded scalar extension.
Source: Weil II (1.1.1)d)
(blueprint: def-zl-classical-lisse-restriction-maps). -/
def enlargedPair (X : PerAdic.Base D.k) (P : LisseCoefficientPairs l X.scheme Ω)
    (F : Padic.FiniteCoefficientFields l Ω) (h : P.base ≤ F) :
    LisseCoefficientPairs l X.scheme Ω :=
  { base := F
    fiber := ((lisseCoefficientDiagramData l X.scheme Ω).diagram.map
      (homOfLE h).toLoc).toFunctor.obj P.fiber }

/-- The canonical scalar-extension arrow, inverted by the prescribed localization.
Source: Weil II (1.1.1)d)
(blueprint: def-zl-classical-lisse-restriction-maps). -/
def enlargementArrow (X : PerAdic.Base D.k) (P : LisseCoefficientPairs l X.scheme Ω)
    (F : Padic.FiniteCoefficientFields l Ω) (h : P.base ≤ F) :
    P ⟶ enlargedPair D l Ω X P F h := ⟨homOfLE h, 𝟙 _⟩

/-- One common finite coefficient field represents a map and inverse and both equations.
The equalities use canonical coefficient arrows, so the finite maps represent the given
maps rather than arbitrary isomorphic objects. The diagram's map_eq identifies these
objects with scalar extensions of the original chosen integral models.
Source: Weil II (1.1.1)c)--d)
(blueprint: def-zl-classical-lisse-restriction-maps). -/
structure FinitePairRepresentation (X : PerAdic.Base D.k)
    (E : Padic.FiniteCoefficientFields l Ω) (P Q : LisseCoefficientPairs l X.scheme Ω)
    (u : (lisseCoefficientCocartesian l X.scheme Ω).Q.obj P ≅
      (lisseCoefficientCocartesian l X.scheme Ω).Q.obj Q) where
  field : Padic.FiniteCoefficientFields l Ω
  enlarges : E ≤ field
  source_le : P.base ≤ field
  target_le : Q.base ≤ field
  pair : (enlargedPair D l Ω X P field source_le).fiber ≅
    (enlargedPair D l Ω X Q field target_le).fiber
  hom_equation :
    u.hom ≫ (lisseCoefficientCocartesian l X.scheme Ω).Q.map
      (enlargementArrow D l Ω X Q field target_le) =
    (lisseCoefficientCocartesian l X.scheme Ω).Q.map
      (enlargementArrow D l Ω X P field source_le) ≫
    (lisseCoefficientCocartesian l X.scheme Ω).Q.map
      ({ base := 𝟙 field,
          fiber := (((lisseCoefficientDiagramData l X.scheme Ω).diagram.mapId
            ⟨field⟩).hom.toNatTrans.app _) ≫
            pair.hom } :
        enlargedPair D l Ω X P field source_le ⟶
          enlargedPair D l Ω X Q field target_le)
  inv_equation :
    u.inv ≫ (lisseCoefficientCocartesian l X.scheme Ω).Q.map
      (enlargementArrow D l Ω X P field source_le) =
    (lisseCoefficientCocartesian l X.scheme Ω).Q.map
      (enlargementArrow D l Ω X Q field target_le) ≫
    (lisseCoefficientCocartesian l X.scheme Ω).Q.map
      ({ base := 𝟙 field,
          fiber := (((lisseCoefficientDiagramData l X.scheme Ω).diagram.mapId
            ⟨field⟩).hom.toNatTrans.app _) ≫
            pair.inv } :
        enlargedPair D l Ω X Q field target_le ⟶
          enlargedPair D l Ω X P field source_le)

/-- The ordinary etale pullback comparison with literal automorphism reindexing.
Source: Stacks 03Q1(3)
(blueprint: def-zl-classical-lisse-restriction-maps). -/
def finiteAutomorphismComparison (X : PerAdic.Base D.k) (g : X.scheme ≅ X.scheme)
    (E : Padic.FiniteCoefficientFields l Ω)
    (F : Sheaf X.scheme.smallEtaleTopology
      (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E.val))) :
    (Etale.upperStar (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E.val))
      g.hom).obj F ≅ (automorphismModuleSheafPullback g
        (Padic.coefficientExtensionIntegers l E.val)).obj F :=
  ((GrothendieckTopology.upperStarIsoLocalizationRestriction
    (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E.val)) @Etale @Etale
      le_rfl g.hom (inferInstance : Etale g.hom)).app F) ≪≫
    ObjectProperty.isoMk _ (Iso.refl _)

/-- The ordinary-unit map into the reindexed system.
Source: Stacks 03Q1(3), BS 6.8.4(1)
(blueprint: def-zl-classical-lisse-restriction-maps). -/
def finiteAutomorphismUnit (X : PerAdic.Base D.k) (g : X.scheme ≅ X.scheme)
    (E : Padic.FiniteCoefficientFields l Ω)
    (F : Sheaf X.scheme.smallEtaleTopology
      (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E.val))) :=
  (sheafCompose _ (forget₂ (ModuleCat.{u + 1}
    (Padic.coefficientExtensionIntegers l E.val)) AddCommGrpCat)).map
      ((Etale.upperStarLowerStarAdjunction
        (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E.val)) g.hom).unit.app F ≫
        (Etale.lowerStar (ModuleCat.{u + 1}
          (Padic.coefficientExtensionIntegers l E.val)) g.hom).map
            (finiteAutomorphismComparison D l Ω X g E F).hom)

/-- The comparison is pinned on finite quotient units, then rationalized with no scalar
or lattice twist. In particular it asserts no Frobenius action on the chosen lattice.
Source: BS 6.8.4(1),(4), 6.8.15
(blueprint: def-zl-classical-lisse-restriction-maps). -/
structure AutomorphismComparison (S : ProEtale.CompletedLisse.System.{u} l)
    (X : PerAdic.Base D.k) (g : X.scheme ≅ X.scheme)
    (E : Padic.FiniteCoefficientFields l Ω)
    (F : ProEtale.CompletedLisse.RawRational l (completedBase D l Ω X E)) where
  integral : (lisseIntegralAutomorphismPullback g l E.val).obj F.obj.integral ≅
    ((restriction D l Ω S g.hom E).obj F).obj.integral
  unit_normalized : ∀ n : ℕ,
    HEq (finiteAutomorphismUnit D l Ω X g E (F.obj.integral.obj.obj (op n)) ≫
      (Etale.lowerStar AddCommGrpCat.{u + 1} g.hom).map
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1}
          (Padic.coefficientExtensionIntegers l E.val)) AddCommGrpCat)).map
            (integral.hom.hom.app (op n))))
      ((S.operation (systemArrow D l Ω g.hom E E (AlgHom.id _ _))).etale.unit l
        ⟨F.obj.integral, F.property⟩ n ≫
        (Etale.lowerStar AddCommGrpCat.{u + 1} g.hom).map
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1}
            (Padic.coefficientExtensionIntegers l E.val)) AddCommGrpCat)).map
              (((S.operation (systemArrow D l Ω g.hom E E
                (AlgHom.id _ _))).rawIntegral F).inv.hom.app (op n))))
  algebraic : (lisseAlgebraicAutomorphismPullback g l Ω).obj
      ((model D l Ω X E).obj F) ≅
    (model D l Ω X E).obj ((restriction D l Ω S g.hom E).obj F)
  algebraic_normalized : HEq algebraic.hom
    (lisseAlgebraicModelMap l X.scheme Ω E
      (lisseCoherence_rationalizeIsoRaw l E.val X.scheme
        ((lisseRationalAutomorphismPullback g l E.val).obj F.obj)
        ((restriction D l Ω S g.hom E).obj F).obj integral).hom)

/-- A lift of the actual restricted Weil map, including its inverse at the same stage.
Source: blueprint real-mixed-by-curves, paragraph 7; BS 6.8.4(4)
(blueprint: def-zl-classical-lisse-restriction-maps). -/
structure WeilLift (R : Realization D l Ω)
    (S : ProEtale.CompletedLisse.System.{u} l)
    (A : LisseRealization.Family D l (Fact.out : l ≠ D.p))
    (C : RestrictionComparison D l Ω R S A)
    (X : PerAdic.Base D.k) (g : X.scheme ≅ X.scheme)
    (E : Padic.FiniteCoefficientFields l Ω)
    (F : ProEtale.CompletedLisse.RawRational l (completedBase D l Ω X E))
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω X.scheme)
    (ρ : (R.functor D l Ω X).obj ((model D l Ω X E).obj F) ≅ M)
    (α : (pull D l Ω g.hom).obj M ≅ M) where
  comparison : AutomorphismComparison D l Ω S X g E F
  classical : (lisseAlgebraicAutomorphismPullback g l Ω).obj
    ((model D l Ω X E).obj F) ≅ (model D l Ω X E).obj F
  realizes : (R.functor D l Ω X).mapIso classical =
    (R.functor D l Ω X).mapIso comparison.algebraic ≪≫ C.iso D l Ω g.hom E F ≪≫
      (pull D l Ω g.hom).mapIso ρ ≪≫ α ≪≫ ρ.symm
  realizes_inverse : (R.functor D l Ω X).mapIso classical.symm =
    ρ ≪≫ α.symm ≪≫ (pull D l Ω g.hom).mapIso ρ.symm ≪≫
      (C.iso D l Ω g.hom E F).symm ≪≫
        (R.functor D l Ω X).mapIso comparison.algebraic.symm
  finite : FinitePairRepresentation D l Ω X E
    (lisseAlgebraicPair l X.scheme Ω
      ((lisseAlgebraicAutomorphismPullback g l Ω).obj ((model D l Ω X E).obj F)))
    (lisseAlgebraicPair l X.scheme Ω ((model D l Ω X E).obj F)) classical

/-- Successive restrictions retain the completed family's specified raw compositor.
Source: BS 6.8.4(1),(4), 6.8.15
(blueprint: def-zl-classical-lisse-restriction-maps). -/
def restrictionComposite (S : ProEtale.CompletedLisse.System.{u} l)
    {X Y Z : PerAdic.Base D.k} (f : X.scheme ⟶ Y.scheme) (g : Z.scheme ⟶ X.scheme)
    (E : Padic.FiniteCoefficientFields l Ω)
    (F : ProEtale.CompletedLisse.RawRational l (completedBase D l Ω Y E)) :
    (restriction D l Ω S g E).obj ((restriction D l Ω S f E).obj F) ≅
      (restriction D l Ω S (g ≫ f) E).obj F :=
  (S.rawComp (systemArrow D l Ω f E E (AlgHom.id _ _))
    (systemArrow D l Ω g E E (AlgHom.id _ _))).app F

/-- Coefficient enlargement of a restricted chosen lattice uses the same normalized
operation as pullback; reconstruction and fraction squares are retained in the family.
Source: Weil II (1.1.1)d), BS 6.8.4(4)
(blueprint: def-zl-classical-lisse-restriction-maps). -/
def scalarOperation (S : ProEtale.CompletedLisse.System.{u} l) (X : PerAdic.Base D.k)
    (E F : Padic.FiniteCoefficientFields l Ω) (h : E ≤ F) :=
  (S.operation (systemArrow D l Ω (𝟙 X.scheme) E F (IntermediateField.inclusion h))).raw

end WeilConjectures.ZlFrontier
