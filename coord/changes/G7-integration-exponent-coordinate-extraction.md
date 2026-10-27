# Integration exponent coordinates: module extraction

## Reason

The item needs separate projective, affine and projection-naturality steps. Each
step mentions the item's existing coordinate definitions. Keeping these definitions
in the item would make their modules import their own consumer. Extract the common
coordinates into `Sheaf.Paper.IntegrationExponentTransposeData` and publicly import
that module from the original item. All existing declaration names, universes,
signatures and bodies remain verbatim. The extraction comparison was checked byte
for byte after removing the one newly added forward-square predicate.

No target statement changes. The extraction preserves the meaning of every
existing definition. The new `IntegrationDecompositionSquare` is only the first
conjunct of `IntegrationDecompositionEquations`, used to separate geometric input
from the inverse and trace cancellation proved in the item.

## Old

The following declaration block was in
`lean/Sheaf/Paper/IntegrationExponentTransposeTransport.lean`:

```lean
section Generic
variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The ordinary module derived category, with its published coefficient convention.
Source: ordinary constant modules (blueprint: lem-pur-integration-exponent-transpose-transport).
-/
abbrev integrationEtale (T : Scheme.{u}) := Etale.DerivedCategoryModule A T

/-- The pro-etale module derived category, with the original site universes.
Source: ordinary constant modules (blueprint: lem-pur-integration-exponent-transpose-transport).
-/
abbrev integrationPro (T : Scheme.{u}) :=
  DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))

/-- The fixed ordinary bundle support functor, independent of the exponent.
Source: vector integration (blueprint: lem-pur-integration-exponent-transpose-transport). -/
abbrev integrationLower (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] :
    integrationEtale A (VectorBundleZeroSection.scheme S d F) ⥤ integrationEtale A S :=
  Etale.vectorBundlePurityLower A S d F

/-- The fixed pro-etale bundle support functor, independent of the exponent.
Source: vector integration (blueprint: lem-pur-integration-exponent-transpose-transport). -/
abbrev integrationProLower (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] :
    integrationPro A (VectorBundleZeroSection.scheme S d F) ⥤ integrationPro A S :=
  rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
    (Etale.vectorBundlePurityCompactification S d F)

/-- The bounded-origin target of the transpose, using the actual derived direct image.
Source: Stacks 099R, 0B65 (blueprint: lem-pur-integration-exponent-transpose-transport). -/
abbrev integrationRightTarget (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] (K : integrationEtale A S) :
    integrationPro A (VectorBundleZeroSection.scheme S d F) :=
  (comparison A _).obj ((genericVectorExceptional A S d F).obj
    ((comparisonLowerStar (ModuleCat.{u + 1} A) S).rightDerivedFunctor.obj
      ((comparison A S).obj K)))

/-- Canonical tensor integration data and the isomorphisms of its actual transposes.
The rho arrow is the comparison unit, and the inverse formula is literal.
Source: Stacks 0B65; vector-bundle purity
(blueprint: lem-pur-integration-exponent-transpose-transport). -/
structure IntegrationTransposeData
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] (K : integrationEtale A S)
    (t : genericVectorSource A N hA S d F ⟶ unit A S)
    (e : genericVectorSource A N hA S d F ≅
      (comparison A S).obj (Etale.vectorIntegrationSource A N hA S d F)) where
  data : TensorCompatibilityData A N hN hA S hS d F K t e
  right_plus : DerivedCategory.TStructure.t.plus ((genericVectorExceptional A S d F).obj K)
  etaE : Etale.vectorBundlePurityTwistedPullback A N hA S d F K ≅
    (genericVectorExceptional A S d F).obj K
  rho : (comparison A _).obj ((genericVectorExceptional A S d F).obj K) ≅
    integrationRightTarget A S d F K
  etaP : (comparison A _).obj
    (Etale.vectorBundlePurityTwistedPullback A N hA S d F K) ≅
      integrationRightTarget A S d F K
  etaE_formula : etaE.hom = (Etale.vectorBundlePurityAdjunction A S d F).homEquiv _ K data.ae
  rho_formula : rho.hom = boundedSiteRho A (genericVectorExceptional A S d F) K
  etaP_formula : etaP.hom = boundedSiteTranspose A
    (Etale.vectorBundlePurityCompactification S d F) (genericVectorExceptional A S d F)
    (Etale.vectorBundlePurityAdjunction A S d F) ⟨_, data.hM⟩ ((comparison A S).obj K) data.ap
  transpose : etaP.hom = (comparison A _).map etaE.hom ≫ rho.hom
  inverse : etaP.inv = rho.inv ≫ (comparison A _).map etaE.inv

/-- Equality after the prescribed coefficient transition of both integration arrows,
transposes and inverse purity maps. No unconstrained map is used as a transition.
Source: Stacks 0B65, Hom naturality
(blueprint: lem-pur-integration-exponent-transpose-transport). -/
structure IntegrationTensorTransitionEquations
    (N M : ℕ) (hN : 0 < N) (hM : 0 < M) (hA : (N : A) = 0) (hB : (M : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (N : Γ(S, ⊤))) (hS' : IsUnit (M : Γ(S, ⊤))) (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] (K : integrationEtale A S)
    (t : genericVectorSource A N hA S d F ⟶ unit A S)
    (e : genericVectorSource A N hA S d F ≅
      (comparison A S).obj (Etale.vectorIntegrationSource A N hA S d F))
    (t' : genericVectorSource A M hB S d F ⟶ unit A S)
    (e' : genericVectorSource A M hB S d F ≅
      (comparison A S).obj (Etale.vectorIntegrationSource A M hB S d F))
    (i : Etale.vectorBundlePurityTwistedPullback A M hB S d F K ≅
      Etale.vectorBundlePurityTwistedPullback A N hA S d F K) : Prop where
  compatible : ∃ (D : IntegrationTransposeData A N hN hA S hS d F K t e)
      (D' : IntegrationTransposeData A M hM hB S hS' d F K t' e'),
    (integrationLower A S d F).map i.hom ≫ D.data.ae = D'.data.ae ∧
    (integrationProLower A S d F).map ((comparison A _).map i.hom) ≫
      D.data.ap = D'.data.ap ∧
    i.hom ≫ D.etaE.hom = D'.etaE.hom ∧
    (comparison A _).map i.hom ≫ D.etaP.hom = D'.etaP.hom ∧
    D.etaE.inv ≫ i.inv = D'.etaE.inv ∧
    D.etaP.inv ≫ (comparison A _).map i.inv = D'.etaP.inv

end Generic

/-- Shifted root-power transition, fixed by finite Tate descent.
Source: Stacks 03PK (blueprint: lem-pur-integration-exponent-transpose-transport). -/
def integrationLineTransition (T : Scheme.{u}) (hT : IsUnit (l : Γ(T, ⊤)))
    (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) :
    (Etale.ordinaryFiniteLine (Scheme.finiteTateCoefficient l E n)
      (l ^ (s + 1)) hs T)⟦(2 : ℤ)⟧ ≅
    (Etale.ordinaryFiniteLine (Scheme.finiteTateCoefficient l E n)
      (l ^ (r + 1)) hr T)⟦(2 : ℤ)⟧ :=
  (shiftFunctor _ (2 : ℤ)).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso
    (exponentTransition l E n T hT r s hrs hr hs 1))

/-- The actual coefficient transition on W, with its explicit source and target.
Source: root transition and ordered tensor powers
(blueprint: lem-pur-integration-exponent-transpose-transport). -/
def integrationVectorTransition (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] :
    Etale.vectorIntegrationCoefficient (Scheme.finiteTateCoefficient l E n)
      (l ^ (s + 1)) hs S d F ≅
    Etale.vectorIntegrationCoefficient (Scheme.finiteTateCoefficient l E n)
      (l ^ (r + 1)) hr S d F :=
  (Etale.ordinaryFinitePullback (Scheme.finiteTateCoefficient l E n)
    (VectorBundleZeroSection.π S d F)).mapIso
      (baseExponentComparison l E n S hS r s hrs hr hs d)

/-- The root transition on J, identity on the pulled-back coefficient.
Source: coefficient-first tensor convention
(blueprint: lem-pur-integration-exponent-transpose-transport). -/
def integrationTensorTransition (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (K : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) S) :
    vectorTwisted l E n S s hs d F K ≅ vectorTwisted l E n S r hr d F K :=
  ((Etale.derivedTensor (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
    (VectorBundleZeroSection.scheme S d F)).obj
      ((Etale.ordinaryFinitePullback (Scheme.finiteTateCoefficient l E n)
        (VectorBundleZeroSection.π S d F)).obj K)).mapIso
          (integrationVectorTransition l E n S hS r s hrs hr hs d F)

/-- Ordered tower transition through the existing coefficient descent.
Source: finite Tate descent and ordered affine coordinates
(blueprint: lem-pur-integration-exponent-transpose-transport). -/
def integrationTowerTransition (T : Scheme.{u}) (hT : IsUnit (l : Γ(T, ⊤)))
    (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (d : ℕ) :
    (Etale.affineTraceRight (Scheme.finiteTateCoefficient l E n) (l ^ (s + 1)) hs T d).obj
      (Etale.ordinaryFiniteUnit _ T) ≅
    (Etale.affineTraceRight (Scheme.finiteTateCoefficient l E n) (l ^ (r + 1)) hr T d).obj
      (Etale.ordinaryFiniteUnit _ T) :=
  Etale.affineLinearCoefficientDescent _ (l ^ (s + 1)) hs
    (Etale.projectiveLineTraceTransport (l ^ (s + 1))
      (pow_pos (Fact.out : l.Prime).pos _) _ hs) T
    (by simpa only [Nat.cast_pow] using hT.pow (s + 1)) d ≪≫
  (Etale.ordinaryFinitePullback _ (affineTraceProjection T d)).mapIso
    (baseExponentComparison l E n T hT r s hrs hr hs d) ≪≫
  (Etale.affineLinearCoefficientDescent _ (l ^ (r + 1)) hr
    (Etale.projectiveLineTraceTransport (l ^ (r + 1))
      (pow_pos (Fact.out : l.Prime).pos _) _ hr) T
    (by simpa only [Nat.cast_pow] using hT.pow (r + 1)) d).symm

/-- The ordinary ordered trace is the counit of the specified ordinary tower.
Source: vector integration, ordered affine trace
(blueprint: lem-pur-integration-exponent-transpose-transport). -/
abbrev integrationOrdinaryOrdered (T : Scheme.{u}) [IsNoetherian T]
    (hT : IsUnit (l : Γ(T, ⊤))) (r : ℕ)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (d : ℕ) :=
  (Etale.affineTraceAdjunction _ (l ^ (r + 1)) hr
    (Etale.projectiveLineTraceTransport (l ^ (r + 1))
      (pow_pos (Fact.out : l.Prime).pos _) _ hr)
    (fun Y _ hY ↦ Etale.projectiveLineTraceDatum (l ^ (r + 1))
      (pow_pos (Fact.out : l.Prime).pos _) _ hr Y hY)
    T (by simpa only [Nat.cast_pow] using hT.pow (r + 1)) d).counit.app
      (Etale.ordinaryFiniteUnit _ T)

/-- Generic two-component decomposition and inverse trace transport, on actual arrows.
Source: inverse-decomposition cancellation, Stacks 03PK
(blueprint: lem-pur-integration-exponent-transpose-transport). -/
def IntegrationDecompositionEquations {C : Type v} [Category.{w} C]
    [HasZeroMorphisms C] [HasBinaryBiproducts C]
    {Lr Ls U Rr Rs : C} (e : Ls ⟶ Lr) (q : Rs ⟶ Rr)
    (br : (Lr ⊞ U) ≅ Rr) (bs : (Ls ⊞ U) ≅ Rs) : Prop :=
  bs.hom ≫ q = biprod.map e (𝟙 U) ≫ br.hom ∧
  q ≫ br.inv = bs.inv ≫ biprod.map e (𝟙 U) ∧
  q ≫ br.inv ≫ biprod.snd = bs.inv ≫ biprod.snd

/-- Exponent transport of the actual ordinary and supported pro-etale decompositions.
Source: Stacks 03PK, supported projective Kummer normalization
(blueprint: lem-pur-integration-exponent-transpose-transport). -/
def IntegrationProjectiveEquations (T : Scheme.{u}) [IsNoetherian T]
    (hT : IsUnit (l : Γ(T, ⊤))) (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) : Prop :=
  IntegrationDecompositionEquations
    (integrationLineTransition l E n T hT r s hrs hr hs).hom
    ((Etale.ordinaryFinitePushforward _ (ProjectiveLine T ↘ T)).map
      (integrationLineTransition l E n (ProjectiveLine T)
        (by simpa using hT.map (ProjectiveLine T ↘ T).appTop.hom) r s hrs hr hs).hom)
    (kummerTraceOrdinaryDatum l E n T hT r hr).decomposition
    (kummerTraceOrdinaryDatum l E n T hT s hs).decomposition ∧
  ∃ (br : (line l E n r hr T ⊞ unit (Scheme.finiteTateCoefficient l E n) T) ≅
      (lowerStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
        (ProjectiveLine T ↘ T)).rightDerivedFunctor.obj (line l E n r hr (ProjectiveLine T)))
    (bs : (line l E n s hs T ⊞ unit (Scheme.finiteTateCoefficient l E n) T) ≅
      (lowerStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
        (ProjectiveLine T ↘ T)).rightDerivedFunctor.obj (line l E n s hs (ProjectiveLine T))),
    br.hom = projectiveB l E n T hT (infinityCartier T) r hr ∧
    bs.hom = projectiveB l E n T hT (infinityCartier T) s hs ∧
    IntegrationDecompositionEquations
      ((comparison (Scheme.finiteTateCoefficient l E n) T).map
        (integrationLineTransition l E n T hT r s hrs hr hs).hom)
      ((lowerStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
        (ProjectiveLine T ↘ T)).rightDerivedFunctor.map
          ((comparison (Scheme.finiteTateCoefficient l E n) (ProjectiveLine T)).map
            (integrationLineTransition l E n (ProjectiveLine T)
              (by simpa using hT.map (ProjectiveLine T ↘ T).appTop.hom)
              r s hrs hr hs).hom)) br bs

/-- Open-chart restrictions and every ordered affine trace commute with root transition.
Source: naturality of the open counit and ordered tower recursion
(blueprint: lem-pur-integration-exponent-transpose-transport). -/
def IntegrationAffineEquations (T : Scheme.{u}) [IsNoetherian T]
    (hT : IsUnit (l : Γ(T, ⊤))) (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) : Prop :=
  (Etale.ordinaryFinitePushforward _ (ProjectiveLine T ↘ T)).map
    ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
      (ProjectiveLine.affineChart T)).mapDerivedCategory.map
        ((Etale.upperStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
          (ProjectiveLine.affineChart T)).leftDerivedFunctor.map
            (integrationLineTransition l E n (ProjectiveLine T)
              (by simpa using hT.map (ProjectiveLine T ↘ T).appTop.hom)
              r s hrs hr hs).hom)) ≫ kummerTraceEtaleAffine l E n T hT r hr =
    kummerTraceEtaleAffine l E n T hT s hs ∧
  (lowerStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
    (ProjectiveLine T ↘ T)).rightDerivedFunctor.map
      ((openImmersionLowerShriek (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
        (ProjectiveLine.affineChart T)).mapDerivedCategory.map
          ((upperStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
            (ProjectiveLine.affineChart T)).leftDerivedFunctor.map
              ((comparison (Scheme.finiteTateCoefficient l E n) (ProjectiveLine T)).map
                (integrationLineTransition l E n (ProjectiveLine T)
                  (by simpa using hT.map (ProjectiveLine T ↘ T).appTop.hom)
                  r s hrs hr hs).hom))) ≫ kummerTraceProAffine l E n T hT r hr =
    kummerTraceProAffine l E n T hT s hs ∧
  ∀ d : ℕ,
    (Etale.affineTraceLeft _ T d).map
      (integrationTowerTransition l E n T hT r s hrs hr hs d).hom ≫
        integrationOrdinaryOrdered l E n T hT r hr d =
      integrationOrdinaryOrdered l E n T hT s hs d ∧
    (comparison (Scheme.finiteTateCoefficient l E n) T).map
      ((Etale.affineTraceLeft _ T d).map
        (integrationTowerTransition l E n T hT r s hrs hr hs d).hom) ≫
      orderedIntegration l E n T hT r hr d = orderedIntegration l E n T hT s hs d

/-- The hypothesis comparing the independent vector trace with ordinary integration.
Source: exponent transport statement, first hypothesis
(blueprint: lem-pur-integration-exponent-transpose-transport). -/
def IntegrationTraceComparison (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] : Prop :=
  ∀ (r : ℕ)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0),
    (vectorSite l E n S r hr d F hS).inv ≫ vectorIntegration l E n S r hr d F hS =
      (comparison (Scheme.finiteTateCoefficient l E n) S).map
        (Etale.vectorBundleIntegration (l ^ (r + 1))
          (pow_pos (Fact.out : l.Prime).pos _) _ hr S
          (by simpa only [Nat.cast_pow] using hS.pow (r + 1)) d F)

/-- The tensor comparison and exponent equations at a finite-Tor coefficient.
Source: vector integration, Stacks 0B65
(blueprint: lem-pur-integration-exponent-transpose-transport). -/
def IntegrationTensorEquations (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (K : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) S) : Prop :=
  IntegrationTensorTransitionEquations (Scheme.finiteTateCoefficient l E n)
    (l ^ (r + 1)) (l ^ (s + 1))
    (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _) hr hs S
    (by simpa only [Nat.cast_pow] using hS.pow (r + 1))
    (by simpa only [Nat.cast_pow] using hS.pow (s + 1)) d F K
    (vectorIntegration l E n S r hr d F hS) (vectorSite l E n S r hr d F hS)
    (vectorIntegration l E n S s hs d F hS) (vectorSite l E n S s hs d F hS)
    (integrationTensorTransition l E n S hS r s hrs hr hs d F K)

/-- Equality of both independently fixed global vector integrations after root transition.
Source: ordered frame integration and degree-zero gluing
(blueprint: lem-pur-integration-exponent-transpose-transport). -/
def IntegrationVectorEquations (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] : Prop :=
  (integrationLower (Scheme.finiteTateCoefficient l E n) S d F).map
    (integrationVectorTransition l E n S hS r s hrs hr hs d F).hom ≫
      Etale.vectorBundleIntegration (l ^ (r + 1))
        (pow_pos (Fact.out : l.Prime).pos _) _ hr S
        (by simpa only [Nat.cast_pow] using hS.pow (r + 1)) d F =
      Etale.vectorBundleIntegration (l ^ (s + 1))
        (pow_pos (Fact.out : l.Prime).pos _) _ hs S
        (by simpa only [Nat.cast_pow] using hS.pow (s + 1)) d F ∧
  (integrationProLower (Scheme.finiteTateCoefficient l E n) S d F).map
    ((comparison (Scheme.finiteTateCoefficient l E n) _).map
      (integrationVectorTransition l E n S hS r s hrs hr hs d F).hom) ≫
    vectorIntegration l E n S r hr d F hS = vectorIntegration l E n S s hs d F hS

/-- All exponent equations for the finite coefficient level in the fixed field setting.
Noetherianity is derived from finite type; the prime's invertibility is concluded.
Source: main-20261015 vector-bundle purity and Stacks 03PK, 099R, 0B65
(blueprint: lem-pur-integration-exponent-transpose-transport). -/
def IntegrationExponentTransposeConclusion (P : WeilConjectures.PurityFiniteSetting.{u})
    (S : Scheme.{u}) (aS : S ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] : Prop :=
  letI : IsNoetherian S := isNoetherian_of_locallyOfFiniteType aS
  ∃ hS : IsUnit (P.coefficients.l : Γ(S, ⊤)),
    IntegrationTraceComparison P.coefficients.l P.extension (P.level - 1) S hS d F →
    ∀ (r s : ℕ) (hrs : r ≤ s)
      (hr : ((P.coefficients.l ^ (r + 1) : ℕ) :
        Scheme.finiteTateCoefficient P.coefficients.l P.extension (P.level - 1)) = 0)
      (hs : ((P.coefficients.l ^ (s + 1) : ℕ) :
        Scheme.finiteTateCoefficient P.coefficients.l P.extension (P.level - 1)) = 0),
      IntegrationProjectiveEquations P.coefficients.l P.extension (P.level - 1)
        S hS r s hrs hr hs ∧
      IntegrationAffineEquations P.coefficients.l P.extension (P.level - 1)
        S hS r s hrs hr hs ∧
      IntegrationVectorEquations P.coefficients.l P.extension (P.level - 1)
        S hS r s hrs hr hs d F ∧
      ∀ (K : Etale.DerivedCategoryModule
        (Scheme.finiteTateCoefficient P.coefficients.l P.extension (P.level - 1)) S),
        Etale.DerivedCategory.constructibleFiniteTor
          (ModuleCat.{u + 1}
            (Scheme.finiteTateCoefficient P.coefficients.l P.extension (P.level - 1))) S K →
        IntegrationTensorEquations P.coefficients.l P.extension (P.level - 1)
          S hS r s hrs hr hs d F K
```

## New

The same block, verbatim, is now in
`lean/Sheaf/Paper/IntegrationExponentTransposeData.lean`. The original module
re-exports it with:

```lean
public import Sheaf.Paper.IntegrationExponentTransposeData
```

The new module preserves all original public imports. It additionally defines:

```lean
/-- The forward square for a two-component projective decomposition.
Source: Kummer functoriality (blueprint: def-pur-integration-exponent-transport-data). -/
def IntegrationDecompositionSquare {C : Type v} [Category.{w} C]
    [HasZeroMorphisms C] [HasBinaryBiproducts C]
    {Lr Ls U Rr Rs : C} (e : Ls ⟶ Lr) (q : Rs ⟶ Rr)
    (br : (Lr ⊞ U) ≅ Rr) (bs : (Ls ⊞ U) ≅ Rs) : Prop :=
  bs.hom ≫ q = biprod.map e (𝟙 U) ≫ br.hom
```

## Users

`tools/downstream.py Sheaf.Paper.IntegrationExponentTransposeTransport --uses
integrationExponentTransposeTransport` reports zero downstream modules. Searching
all `lean/` and `quarantine/` files for direct imports also reports none. No existing
consumer needs adaptation or compilation against the extraction. The theorem in
the original module and the following new modules use the re-exported coordinates.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegrationExponentTransposeTransport | G7 | Same public theorem signature; imports and uses extracted coordinates |
| Sheaf.Paper.IntegrationExponentTransposeData | G7, new | Holds the unchanged definitions and new forward-square predicate |
| Sheaf.Paper.IntegrationProjectiveExponentSquare | G7, new | Uses common coordinates |
| Sheaf.Paper.IntegrationAffineExponentTransport | G7, new | Uses common coordinates |
| Sheaf.Paper.IntegrationCoefficientProjectionNaturality | G7, new | Uses common coordinates |

No other existing Lean module is changed. The parent DAG attachment is narrowed
to the theorem; the data declarations have their own new definition node.

## Status

landed 20261026T195212-L-2863799 2026-10-26 (merge of deliver/G7/Sheaf.Paper.IntegrationExponentTransposeTransport)
