# WeilConjectures.CoefVerdierWeil data-module extraction

## Reason

The proof now uses separate one-scheme normalized duality and normalized left-exchange
results. Their statements use the existing records. Extracting the record interface
into CoefVerdierWeilData avoids an import cycle with the theorem proving their existence.
The original module publicly imports the extracted definitions, preserving visibility.
This is an interface extraction for the proof decomposition, not a file split to evade a
compile limit. The three geometric record families now specialize generic containers, and their
large endpoint types and compatibility predicates have named definitions. They retain
the same fields and equations, including every normalization. `finiteMu`, `commonMu`
and `scalarFrobenius` have explicit endpoint types in the published pullback/tensor
and coefficient-transition functors; their bodies remain the same canonical
comparisons. `fiberInclusion` caches the unchanged finite-to-common inclusion.
The finite and common left-exchange types and normalization predicates are shared
between the left-only and exceptional interfaces. The exceptional normalization
predicates apply these same left predicates to the left projections. This avoids
comparing separately expanded realization equations, while retaining every equation.
The finite endpoints use the definitionally equal raw rational category
to avoid repeated inference of its coefficient instances. The left-exchange and
exceptional-comparison specializations explicitly supply their category arguments. This prevents conversion from unfolding the entire common
coefficient tensor construction. The mate expression explicitly uses `TwoSquare.mk`;
this is definitionally the same natural transformation. No additional mathematical
hypothesis or conclusion is introduced.

## Old

The following block was in lean/Sheaf/SixFunctors/CoefVerdierWeilEquivariance.lean.

```lean
namespace WeilConjectures.CoefVerdierWeil

/-- The induced dual Frobenius is c_K followed by D(theta_K inverse).
Source: blueprint proof paragraph 1 (blueprint: cor-coef-verdier-weil-equivariance). -/
def dualStructure {C : Type a} [Category.{b} C] (P : C ⥤ C) (V : Cᵒᵖ ⥤ C)
    (c : V ⋙ P ≅ P.op ⋙ V) (K : IsoAlgebra P) :
    P.obj (V.obj (op K.carrier)) ≅ V.obj (op K.carrier) :=
  c.app (op K.carrier) ≪≫ V.mapIso K.str.symm.op

/-- The equations for the canonical dual Frobenius, evaluation and actual biduality.
The first equation normalizes c by evaluation; the remaining equations explicitly
state functoriality on Weil arrows, evaluation equivariance, and delta equivariance.
Source: blueprint proof paragraphs 1--2
(blueprint: cor-coef-verdier-weil-equivariance). -/
structure Duality {C : Type a} [Category.{b} C]
    (P : C ⥤ C) (V : Cᵒᵖ ⥤ C) (T : C × C ⥤ C) (omega : C)
    (evaluation : ∀ K : C, T.obj (K, V.obj (op K)) ⟶ omega)
    (delta : 𝟭 C ≅ V.rightOp ⋙ V)
    (mu : ∀ K M : C, P.obj (T.obj (K, M)) ≅ T.obj (P.obj K, P.obj M)) where
  omegaStructure : P.obj omega ≅ omega
  comparison : V ⋙ P ≅ P.op ⋙ V
  comparison_evaluation (K : C) :
    (mu K (V.obj (op K))).hom ≫
      T.map (Prod.mkHom (𝟙 (P.obj K)) (comparison.hom.app (op K))) ≫
      evaluation (P.obj K) = P.map (evaluation K) ≫ omegaStructure.hom
  morphism {K M : IsoAlgebra P} (f : K ⟶ M) :
    (dualStructure P V comparison M).hom ≫ V.map f.hom.f.op =
      P.map (V.map f.hom.f.op) ≫ (dualStructure P V comparison K).hom
  evaluation_equivariant (K : IsoAlgebra P) :
    (mu K.carrier (V.obj (op K.carrier))).hom ≫
      T.map (Prod.mkHom K.str.hom (dualStructure P V comparison K).hom) ≫
      evaluation K.carrier = P.map (evaluation K.carrier) ≫ omegaStructure.hom
  biduality_equivariant (K : IsoAlgebra P) :
    K.str.hom ≫ delta.hom.app K.carrier =
      P.map (delta.hom.app K.carrier) ≫
        (dualStructure P V comparison
          (IsoAlgebra.mk (V.obj (op K.carrier)) (dualStructure P V comparison K))).hom

/-- Exceptional Frobenius comparison and equivariance of the specified adjunction.
The right comparison is the mate of the inverse left comparison. Thus the unit
and counit are those of the original constructible adjunction.
Source: blueprint proof paragraph 1, explicit mate in DAG step 3
(blueprint: cor-coef-verdier-weil-equivariance). -/
structure Exceptional {C : Type a} {C' : Type a'}
    [Category.{b} C] [Category.{b'} C'] (P : C ⥤ C) (Q : C' ⥤ C')
    {F : C ⥤ C'} {G : C' ⥤ C} (adj : F ⊣ G) where
  left : F ⋙ Q ≅ P ⋙ F
  right : G ⋙ P ≅ Q ⋙ G
  mate : right.hom = (mateEquiv adj adj left.inv).natTrans
  unit (K : IsoAlgebra P) :
    K.str.hom ≫ adj.unit.app K.carrier =
      P.map (adj.unit.app K.carrier) ≫ right.hom.app (F.obj K.carrier) ≫
        G.map (left.hom.app K.carrier) ≫ G.map (F.map K.str.hom)
  counit (M : IsoAlgebra Q) :
    left.hom.app (G.obj M.carrier) ≫ F.map (right.hom.app M.carrier) ≫
      F.map (G.map M.str.hom) ≫ adj.counit.app M.carrier =
        Q.map (adj.counit.app M.carrier) ≫ M.str.hom

/-- Normalization of the dualizing Frobenius by the actual exceptional mate.
The constant object's structure is fixed by the tensor unit equation.
Source: blueprint proof step 3 (blueprint: cor-coef-verdier-weil-equivariance). -/
@[irreducible] def DualizingMate {C : Type a} {C' : Type a'}
    [Category.{b} C] [Category.{b'} C'] (P : C ⥤ C) (Q : C' ⥤ C')
    (G : C' ⥤ C) (right : G ⋙ P ≅ Q ⋙ G) (omega : C)
    (omegaTheta : P.obj omega ≅ omega) (unit : C') (T : C' × C' ⥤ C')
    (mu : ∀ K M : C', Q.obj (T.obj (K, M)) ≅ T.obj (Q.obj K, Q.obj M))
    (unitor : ∀ M : C', T.obj (unit, M) ≅ M) : Prop :=
  ∃ constant : Q.obj unit ≅ unit,
    (∀ M : C',
      (mu unit M).hom ≫ T.map (Prod.mkHom constant.hom (𝟙 (Q.obj M))) ≫
        (unitor (Q.obj M)).hom = Q.map (unitor M).hom) ∧
    ∃ identification : omega ≅ G.obj unit,
      omegaTheta.hom ≫ identification.hom =
        P.map identification.hom ≫ right.hom.app unit ≫ G.map constant.hom

/-- A scalar or inclusion comparison is equivariant with the specified Frobenius maps.
Source: blueprint proof paragraph 3 (blueprint: cor-coef-verdier-weil-equivariance). -/
def IsEquivariant {C : Type a} {C' : Type a'}
    [Category.{b} C] [Category.{b'} C'] (P : C ⥤ C) (Q : C' ⥤ C')
    (L : C ⥤ C') (s : L ⋙ Q ≅ P ⋙ L)
    {K : C} {M : C'} (theta : P.obj K ≅ K) (psi : Q.obj M ≅ M)
    (f : L.obj K ⟶ M) : Prop :=
  s.hom.app K ≫ L.map theta.hom ≫ f = Q.map f ≫ psi.hom



/-- The Weil structure transported by a functor with its specified Frobenius comparison.
Source: blueprint proof step 7 (blueprint: cor-coef-verdier-weil-equivariance). -/
def transportedStructure {C : Type a} {C' : Type a'}
    [Category.{b} C] [Category.{b'} C'] (P : C ⥤ C) (Q : C' ⥤ C')
    (L : C ⥤ C') (s : L ⋙ Q ≅ P ⋙ L) (K : IsoAlgebra P) :
    Q.obj (L.obj K.carrier) ≅ L.obj K.carrier :=
  s.app K.carrier ≪≫ L.mapIso K.str

/-- Equivariance of the actual dualizing and duality comparison arrows. Evaluation
and biduality diagrams use these same arrows and the specified equivariant maps.
Source: blueprint proof step 7 (blueprint: cor-coef-verdier-weil-equivariance). -/
structure DualityComparison {C : Type a} {C' : Type a'}
    [Category.{b} C] [Category.{b'} C']
    {P : C ⥤ C} {Q : C' ⥤ C'} {V : Cᵒᵖ ⥤ C} {V' : C'ᵒᵖ ⥤ C'}
    {T : C × C ⥤ C} {T' : C' × C' ⥤ C'} {omega : C} {omega' : C'}
    {evaluation : ∀ K : C, T.obj (K, V.obj (op K)) ⟶ omega}
    {evaluation' : ∀ K : C', T'.obj (K, V'.obj (op K)) ⟶ omega'}
    {delta : 𝟭 C ≅ V.rightOp ⋙ V} {delta' : 𝟭 C' ≅ V'.rightOp ⋙ V'}
    {mu : ∀ K M : C, P.obj (T.obj (K, M)) ≅ T.obj (P.obj K, P.obj M)}
    {mu' : ∀ K M : C', Q.obj (T'.obj (K, M)) ≅ T'.obj (Q.obj K, Q.obj M)}
    (W : Duality P V T omega evaluation delta mu)
    (W' : Duality Q V' T' omega' evaluation' delta' mu')
    (L : C ⥤ C') (s : L ⋙ Q ≅ P ⋙ L)
    (u : L.obj omega ≅ omega') (beta : V ⋙ L ≅ L.op ⋙ V') : Prop where
  omega : IsEquivariant P Q L s W.omegaStructure W'.omegaStructure u.hom
  dual (K : IsoAlgebra P) :
    IsEquivariant P Q L s (dualStructure P V W.comparison K)
      (dualStructure Q V' W'.comparison
        (IsoAlgebra.mk (L.obj K.carrier) (transportedStructure P Q L s K)))
      (beta.hom.app (op K.carrier))

/-- Equivariance of canonical scalar or stage-inclusion comparisons for both
exceptional functors. Their compatibility diagrams retain the original units and counits.
Source: blueprint proof steps 3 and 7
(blueprint: cor-coef-verdier-weil-equivariance). -/
structure ExceptionalComparison {C : Type a} {C' : Type a'}
    {B : Type b} {B' : Type b'}
    [Category C] [Category C'] [Category B] [Category B']
    {P : C ⥤ C} {P' : C' ⥤ C'} {Q : B ⥤ B} {Q' : B' ⥤ B'}
    {F : C ⥤ B} {G : B ⥤ C} {F' : C' ⥤ B'} {G' : B' ⥤ C'}
    {adj : F ⊣ G} {adj' : F' ⊣ G'}
    (W : Exceptional P Q adj) (W' : Exceptional P' Q' adj')
    (L : C ⥤ C') (M : B ⥤ B') (s : L ⋙ P' ≅ P ⋙ L) (t : M ⋙ Q' ≅ Q ⋙ M)
    (alpha : F ⋙ M ≅ L ⋙ F') (beta : G ⋙ L ≅ M ⋙ G') : Prop where
  left (K : IsoAlgebra P) :
    IsEquivariant Q Q' M t (transportedStructure P Q F W.left K)
      (transportedStructure P' Q' F' W'.left
        (IsoAlgebra.mk (L.obj K.carrier) (transportedStructure P P' L s K)))
      (alpha.hom.app K.carrier)
  right (K : IsoAlgebra Q) :
    IsEquivariant P P' L s (transportedStructure Q P G W.right K)
      (transportedStructure Q' P' G' W'.right
        (IsoAlgebra.mk (M.obj K.carrier) (transportedStructure Q Q' M t K)))
      (beta.hom.app K.carrier)

/-- Conjugate a specified Frobenius exchange by a realization of its left functor.
Source: blueprint proof steps 2--3 (blueprint: cor-coef-verdier-weil-equivariance). -/
@[irreducible] def realizedExchangeAt {C : Type a} {B : Type b} [Category C] [Category B]
    {P : C ⥤ C} {Q : B ⥤ B} {F H : C ⥤ B}
    (e : F ≅ H) (w : F ⋙ Q ≅ P ⋙ F) (K : C) :
    Q.obj (H.obj K) ⟶ H.obj (P.obj K) :=
  Q.map (e.inv.app K) ≫ w.hom.app K ≫ e.hom.app (P.obj K)

/-- The same conjugation after the specified stage-inclusion comparisons.
Source: blueprint proof steps 3 and 8 (blueprint: cor-coef-verdier-weil-equivariance). -/
@[irreducible] def realizedStageExchangeAt {C : Type a} {C' : Type a'} {B : Type b} {B' : Type b'}
    [Category C] [Category C'] [Category B] [Category B']
    {P : C ⥤ C} {P' : C' ⥤ C'} {Q : B ⥤ B} {Q' : B' ⥤ B'}
    {F H : C ⥤ B} {F' : C' ⥤ B'} {L : C ⥤ C'} {M : B ⥤ B'}
    (e : F ≅ H) (beta : F ⋙ M ≅ L ⋙ F')
    (s : ∀ K : C, P'.obj (L.obj K) ≅ L.obj (P.obj K))
    (t : ∀ N : B, Q'.obj (M.obj N) ≅ M.obj (Q.obj N))
    (w : F' ⋙ Q' ≅ P' ⋙ F') (K : C) :
    M.obj (Q.obj (H.obj K)) ⟶ M.obj (H.obj (P.obj K)) :=
  M.map (Q.map (e.inv.app K)) ≫ (t (F.obj K)).inv ≫
    Q'.map (beta.hom.app K) ≫ w.hom.app (L.obj K) ≫
    F'.map ((s K).hom) ≫ beta.inv.app (P.obj K) ≫ M.map (e.hom.app (P.obj K))

/-- The structure morphism of the geometric fiber inherits local finite type.
Source: blueprint geometric-fiber convention, Stacks 01T0
(blueprint: cor-coef-verdier-weil-equivariance). -/
abbrev fiberStructureLocallyFiniteType (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
  (FrobeniusExchange.fiber_finiteType D X₀).1

/-- The structure morphism of the geometric fiber inherits quasi-compactness.
Source: blueprint geometric-fiber convention, Stacks 01T0
(blueprint: cor-coef-verdier-weil-equivariance). -/
abbrev fiberStructureQuasiCompact (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
  (FrobeniusExchange.fiber_finiteType D X₀).2

/-- Separatedness is inherited by the actual geometric fiber structure morphism.
Source: blueprint separated finite-type convention, Stacks 01KH
(blueprint: cor-coef-verdier-weil-equivariance). -/
abbrev fiberStructureSeparated (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom]
    [QuasiCompact X₀.hom] [IsSeparated X₀.hom] :
    IsSeparated ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
  MorphismProperty.baseChange_obj (P := @IsSeparated) _ X₀ inferInstance

/-- The geometric map inherits separatedness from the descended morphism.
Source: blueprint exceptional clause, Stacks 01KH
(blueprint: cor-coef-verdier-weil-equivariance). -/
abbrev fiberMapSeparated (D : FiniteFieldDatum.{u})
    {X₀ Y₀ : Over (Spec (.of D.k₀))} (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left] :
    IsSeparated (FrobeniusExchange.fiberMap D f₀) :=
  MorphismProperty.overPullbackMap (P := @IsSeparated) _ f₀ inferInstance

/-- The geometric map inherits local finite type from the descended morphism.
Source: blueprint exceptional clause, Stacks 01T0
(blueprint: cor-coef-verdier-weil-equivariance). -/
abbrev fiberMapLocallyFiniteType (D : FiniteFieldDatum.{u})
    {X₀ Y₀ : Over (Spec (.of D.k₀))} (f₀ : X₀ ⟶ Y₀) [LocallyOfFiniteType f₀.left] :
    LocallyOfFiniteType (FrobeniusExchange.fiberMap D f₀) :=
  MorphismProperty.overPullbackMap (P := @LocallyOfFiniteType) _ f₀ inferInstance

/-- The geometric map inherits quasi-compactness from the descended morphism.
Source: blueprint exceptional clause, Stacks 01T0
(blueprint: cor-coef-verdier-weil-equivariance). -/
abbrev fiberMapQuasiCompact (D : FiniteFieldDatum.{u})
    {X₀ Y₀ : Over (Spec (.of D.k₀))} (f₀ : X₀ ⟶ Y₀) [QuasiCompact f₀.left] :
    QuasiCompact (FrobeniusExchange.fiberMap D f₀) :=
  MorphismProperty.overPullbackMap (P := @QuasiCompact) _ f₀ inferInstance

section Geometric
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion transition)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom]
  [QuasiCompact X₀.hom] [IsSeparated X₀.hom]

/-- The actual duality type on the geometric fiber, with inherited structure-map instances.
Source: blueprint geometric-fiber convention
(blueprint: cor-coef-verdier-weil-equivariance). -/
abbrev FiberDuality :=
  letI := fiberStructureLocallyFiniteType D X₀
  letI := fiberStructureQuasiCompact D X₀
  letI := fiberStructureSeparated D X₀
  CoefQbarVerdier.Duality D l hl Ω (D.geometricFiber X₀).left


/-- The actual internal-Hom identification, on the same geometric fiber.
Source: blueprint duality clause (blueprint: cor-coef-verdier-weil-equivariance). -/
abbrev FiberInternalHom (B : FiberDuality D l hl Ω X₀) :=
  letI := fiberStructureLocallyFiniteType D X₀
  letI := fiberStructureQuasiCompact D X₀
  letI := fiberStructureSeparated D X₀
  CoefQbarVerdier.InternalHom D l hl Ω (D.geometricFiber X₀).left B


/-- The specified exceptional-unit identification of the dualizing object.
Source: blueprint dualizing clause (blueprint: cor-coef-verdier-weil-equivariance). -/
def FiberDualizing (B : FiberDuality D l hl Ω X₀) : Prop :=
  letI := fiberStructureLocallyFiniteType D X₀
  letI := fiberStructureQuasiCompact D X₀
  letI := fiberStructureSeparated D X₀
  CoefQbarVerdier.Dualizing D l hl Ω (D.geometricFiber X₀).left B


/-- The actual Frobenius pullback-tensor comparison at a finite coefficient stage.
Source: blueprint proof steps 2 and 4
(blueprint: cor-coef-verdier-weil-equivariance). -/
def finiteMu (E : Index l Ω) :=
  @canonicalRationalPullbackTensor l _ (Coefficient.{u} l Ω E) _ _ _ _ _
    (D.geometricFrobenius X₀).hom
    (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)
    (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)


/-- The actual common-stage Frobenius pullback-tensor comparison.
Source: blueprint proof steps 2 and 8
(blueprint: cor-coef-verdier-weil-equivariance). -/
def commonMu :=
  @canonicalCommonStagePullbackTensor l _ Ω _ _ _ _ _
    (D.geometricFrobenius X₀).hom
    (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)
    (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)


/-- The inverse canonical pullback/scalar comparison, in the convention L P' ≅ P L.
Source: blueprint proof steps 6--7
(blueprint: cor-coef-verdier-weil-equivariance). -/
def scalarFrobenius (E L : Index l Ω) (h : E ≤ L) :=
  (@rationalPullbackScalarComparison l _ (Coefficient.{u} l Ω E) _ _ _
    (Coefficient.{u} l Ω L) _ _ _ (coefficientInclusion l Ω E L h) _ _
    (D.geometricFrobenius X₀).hom
    (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)
    (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)).symm


/-- Weil structures on the actual finite and common-stage Verdier functors, with
all canonical scalar and inclusion arrows equivariant. The finite-stage parameters
range over every finite subextension, including identity extensions.
Source: blueprint all duality and coefficient clauses, proof steps 1--8
(blueprint: cor-coef-verdier-weil-equivariance). -/
structure Coefficients (B : FiberDuality D l hl Ω X₀) where
  finite (E : Index l Ω) :
    letI := fiberStructureLocallyFiniteType D X₀
    letI := fiberStructureQuasiCompact D X₀
    letI := fiberStructureSeparated D X₀
    Duality (sfWeilFrobeniusPullback D l hl X₀ (Coefficient.{u} l Ω E))
      (B.finite.datum E).dual (RationalVerdier.tensor D l hl _ (Coefficient.{u} l Ω E))
      ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) _).obj
        (B.finite.omega E).omega)
      (B.finite.datum E).evaluation (B.finite.datum E).bidual (finiteMu D l hl Ω X₀ E)
  common :
    letI := fiberStructureLocallyFiniteType D X₀
    letI := fiberStructureQuasiCompact D X₀
    letI := fiberStructureSeparated D X₀
    Duality (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω) B.duality.dual
      (CoefQbarTensor D l hl Ω _) B.omega B.evaluation B.duality.bidual (commonMu D l hl Ω X₀)
  scalar (E L : Index l Ω) (h : E ≤ L) :
    letI := fiberStructureLocallyFiniteType D X₀
    letI := fiberStructureQuasiCompact D X₀
    letI := fiberStructureSeparated D X₀
    DualityComparison (finite E) (finite L) (transition l Ω _ E L h)
      (scalarFrobenius D l hl Ω X₀ E L h)
      (B.finite.scalar E L h).omega (B.finite.beta E L h)
  stageFrobenius (E : Index l Ω) :
    inclusion E ⋙ sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω ≅
      sfWeilFrobeniusPullback D l hl X₀ (Coefficient.{u} l Ω E) ⋙ inclusion E
  stageNormalized (E : Index l Ω) (K : Stage l Ω (D.geometricFiber X₀).left E) :
    (stageFrobenius E).app K = sfWeilStagePullbackIdentification D l hl X₀ Ω E K
  stage (E : Index l Ω) :
    letI := fiberStructureLocallyFiniteType D X₀
    letI := fiberStructureQuasiCompact D X₀
    letI := fiberStructureSeparated D X₀
    DualityComparison (finite E) common (inclusion E) (stageFrobenius E)
      (B.omegaComparison E) (B.comparison E)

section ExceptionalGeometry
variable {Y₀ : Over (Spec (.of D.k₀))} [LocallyOfFiniteType Y₀.hom]
  [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
  (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left]
  [QuasiCompact f₀.left] (c : Compactification (FrobeniusExchange.fiberMap D f₀))


/-- The actual exceptional record, with inherited fiber instances.
Source: blueprint exceptional clause (blueprint: cor-coef-verdier-weil-equivariance). -/
abbrev FiberExceptional :=
  letI := fiberStructureLocallyFiniteType D X₀
  letI := fiberStructureQuasiCompact D X₀
  letI := fiberStructureSeparated D X₀
  letI := fiberStructureLocallyFiniteType D Y₀
  letI := fiberStructureQuasiCompact D Y₀
  letI := fiberStructureSeparated D Y₀
  letI := fiberMapSeparated D f₀
  letI := fiberMapLocallyFiniteType D f₀
  letI := fiberMapQuasiCompact D f₀
  CoefQbarVerdier.Exceptional (Y := (D.geometricFiber Y₀).left)
    D l hl Ω (D.geometricFiber X₀).left
    (FrobeniusExchange.fiberMap D f₀) c


/-- The actual finite-stage adjunction, with inherited fiber instances.
Source: blueprint exceptional clause (blueprint: cor-coef-verdier-weil-equivariance). -/
abbrev fiberAdjunction (A : FiberExceptional D l hl Ω X₀ f₀ c) (E : Index l Ω) :=
  letI := fiberStructureLocallyFiniteType D X₀
  letI := fiberStructureQuasiCompact D X₀
  letI := fiberStructureSeparated D X₀
  letI := fiberStructureLocallyFiniteType D Y₀
  letI := fiberStructureQuasiCompact D Y₀
  letI := fiberStructureSeparated D Y₀
  letI := fiberMapSeparated D f₀
  letI := fiberMapLocallyFiniteType D f₀
  letI := fiberMapQuasiCompact D f₀
  CoefQbarVerdier.finiteAdjunction (Y := (D.geometricFiber Y₀).left)
    D l hl Ω (D.geometricFiber X₀).left (FrobeniusExchange.fiberMap D f₀) c A.system E


/-- The specified finite exceptional functor, with inherited geometric instances.
Source: blueprint proof step 3 (blueprint: cor-coef-verdier-weil-equivariance). -/
abbrev fiberRight (A : FiberExceptional D l hl Ω X₀ f₀ c) (E : Index l Ω) :=
  letI := fiberStructureLocallyFiniteType D X₀
  letI := fiberStructureQuasiCompact D X₀
  letI := fiberStructureSeparated D X₀
  letI := fiberStructureLocallyFiniteType D Y₀
  letI := fiberStructureQuasiCompact D Y₀
  letI := fiberStructureSeparated D Y₀
  letI := fiberMapSeparated D f₀
  letI := fiberMapLocallyFiniteType D f₀
  letI := fiberMapQuasiCompact D f₀
  CoefQbarVerdier.finiteRight (Y := (D.geometricFiber Y₀).left)
    D l hl Ω (D.geometricFiber X₀).left (FrobeniusExchange.fiberMap D f₀) c A.system E


/-- The actual compact-support coefficient comparison, with inherited fiber instances.
Source: blueprint exceptional clause (blueprint: cor-coef-verdier-weil-equivariance). -/
abbrev fiberLeftScalar (A : FiberExceptional D l hl Ω X₀ f₀ c) (E L : Index l Ω) (h : E ≤ L) :=
  letI := fiberStructureLocallyFiniteType D X₀
  letI := fiberStructureQuasiCompact D X₀
  letI := fiberStructureSeparated D X₀
  letI := fiberStructureLocallyFiniteType D Y₀
  letI := fiberStructureQuasiCompact D Y₀
  letI := fiberStructureSeparated D Y₀
  letI := fiberMapSeparated D f₀
  letI := fiberMapLocallyFiniteType D f₀
  letI := fiberMapQuasiCompact D f₀
  CoefQbarVerdier.finiteLeftScalar (Y := (D.geometricFiber Y₀).left)
    D l hl Ω (D.geometricFiber X₀).left (FrobeniusExchange.fiberMap D f₀) c A.system E L h


/-- The actual exceptional coefficient comparison, with inherited fiber instances.
Source: blueprint exceptional clause (blueprint: cor-coef-verdier-weil-equivariance). -/
abbrev fiberRightScalar (A : FiberExceptional D l hl Ω X₀ f₀ c) (E L : Index l Ω) (h : E ≤ L) :=
  letI := fiberStructureLocallyFiniteType D X₀
  letI := fiberStructureQuasiCompact D X₀
  letI := fiberStructureSeparated D X₀
  letI := fiberStructureLocallyFiniteType D Y₀
  letI := fiberStructureQuasiCompact D Y₀
  letI := fiberStructureSeparated D Y₀
  letI := fiberMapSeparated D f₀
  letI := fiberMapLocallyFiniteType D f₀
  letI := fiberMapQuasiCompact D f₀
  CoefQbarVerdier.finiteRightScalar (Y := (D.geometricFiber Y₀).left)
    D l hl Ω (D.geometricFiber X₀).left (FrobeniusExchange.fiberMap D f₀) c A.system E L h


/-- The specified realization of the finite compact-support functor.
Source: blueprint proof steps 2--3 (blueprint: cor-coef-verdier-weil-equivariance). -/
def fiberLeftIdentification (A : FiberExceptional D l hl Ω X₀ f₀ c) (E : Index l Ω) :=
  letI := fiberStructureLocallyFiniteType D X₀
  letI := fiberStructureQuasiCompact D X₀
  letI := fiberStructureSeparated D X₀
  letI := fiberStructureLocallyFiniteType D Y₀
  letI := fiberStructureQuasiCompact D Y₀
  letI := fiberStructureSeparated D Y₀
  letI := fiberMapSeparated D f₀
  letI := fiberMapLocallyFiniteType D f₀
  letI := fiberMapQuasiCompact D f₀
  A.system.ring.rationalLeft c (CoefQbarVerdier.fieldStage l Ω E)

/-- The actual exceptional-duality identification, with inherited fiber instances.
Source: blueprint exceptional clause (blueprint: cor-coef-verdier-weil-equivariance). -/
abbrev FiberExceptionalFormula (BX : FiberDuality D l hl Ω X₀)
    (BY : FiberDuality D l hl Ω Y₀) (A : FiberExceptional D l hl Ω X₀ f₀ c) :=
  letI := fiberStructureLocallyFiniteType D X₀
  letI := fiberStructureQuasiCompact D X₀
  letI := fiberStructureSeparated D X₀
  letI := fiberStructureLocallyFiniteType D Y₀
  letI := fiberStructureQuasiCompact D Y₀
  letI := fiberStructureSeparated D Y₀
  letI := fiberMapSeparated D f₀
  letI := fiberMapLocallyFiniteType D f₀
  letI := fiberMapQuasiCompact D f₀
  CoefQbarVerdier.ExceptionalFormula (Y := (D.geometricFiber Y₀).left)
    D l hl Ω (D.geometricFiber X₀).left (FrobeniusExchange.fiberMap D f₀) BX BY c A

end ExceptionalGeometry


/-- Exceptional adjunctions on the same finite and common-stage categories, with
canonical coefficient comparisons equivariant and the actual unit and counit retained.
Source: blueprint exceptional clause, proof steps 2--3 and 6--8
(blueprint: cor-coef-verdier-weil-equivariance). -/
structure FrobeniusAdjunctions
    {Y₀ : Over (Spec (.of D.k₀))} [LocallyOfFiniteType Y₀.hom]
    [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left]
    [QuasiCompact f₀.left] (c₀ : Compactification f₀.left)
    (A : FiberExceptional D l hl Ω X₀ f₀
      (FrobeniusExchange.geometricCompactification D f₀ c₀))
    where
  finite (E : Index l Ω) :
    Exceptional (sfWeilFrobeniusPullback D l hl X₀ (Coefficient.{u} l Ω E))
      (sfWeilFrobeniusPullback D l hl Y₀ (Coefficient.{u} l Ω E))
      (fiberAdjunction D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) A E)
  common : Exceptional (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω)
    (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω) A.adjunction
  finiteNormalized (E : Index l Ω) (K : Stage l Ω (D.geometricFiber X₀).left E) :
    HEq
      (realizedExchangeAt
        (fiberLeftIdentification D l hl Ω X₀ f₀
          (FrobeniusExchange.geometricCompactification D f₀ c₀) A E) (finite E).left K)
      ((FrobeniusExchange.frobeniusRational D l hl (Coefficient.{u} l Ω E) f₀
        (FrobeniusExchange.frobeniusCompactModel D f₀ c₀)).app K)
  commonNormalized (E : Index l Ω) (K : Stage l Ω (D.geometricFiber X₀).left E) :
    HEq
      (realizedStageExchangeAt
        (fiberLeftIdentification D l hl Ω X₀ f₀
          (FrobeniusExchange.geometricCompactification D f₀ c₀) A E)
        (A.leftComparison E)
        (sfWeilStagePullbackIdentification D l hl X₀ Ω E)
        (sfWeilStagePullbackIdentification D l hl Y₀ Ω E)
        common.left K)
      ((FrobeniusExchange.frobeniusCommonStage D l hl f₀
        (FrobeniusExchange.frobeniusCompactModel D f₀ c₀) Ω).app ((inclusion E).obj K))

/-- Scalar and inclusion equivariance for the pinned Frobenius adjunctions.
Source: blueprint proof steps 3 and 7
(blueprint: cor-coef-verdier-weil-equivariance). -/
structure Adjunctions
    {Y₀ : Over (Spec (.of D.k₀))} [LocallyOfFiniteType Y₀.hom]
    [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left]
    [QuasiCompact f₀.left] (c₀ : Compactification f₀.left)
    (A : FiberExceptional D l hl Ω X₀ f₀
      (FrobeniusExchange.geometricCompactification D f₀ c₀))
    {BX : FiberDuality D l hl Ω X₀} {BY : FiberDuality D l hl Ω Y₀}
    (WX : Coefficients D l hl Ω X₀ BX) (WY : Coefficients D l hl Ω Y₀ BY)
    extends FrobeniusAdjunctions D l hl Ω X₀ f₀ c₀ A where
  scalar (E L : Index l Ω) (h : E ≤ L) :
    ExceptionalComparison (finite E) (finite L)
      (transition l Ω _ E L h) (transition l Ω _ E L h)
      (scalarFrobenius D l hl Ω X₀ E L h) (scalarFrobenius D l hl Ω Y₀ E L h)
      (fiberLeftScalar D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) A E L h)
      (fiberRightScalar D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) A E L h)
  stage (E : Index l Ω) :
    ExceptionalComparison (finite E) common (inclusion E) (inclusion E)
      (WX.stageFrobenius E) (WY.stageFrobenius E)
      (A.leftComparison E) (A.rightComparison E)


/-- The finite-field point in the retained model category.
Source: blueprint proof step 3 (blueprint: cor-coef-verdier-weil-equivariance). -/
abbrev pointModel (D : FiniteFieldDatum.{u}) : Over (Spec (.of D.k₀)) :=
  Over.mk (𝟙 (Spec (.of D.k₀)))

/-- The finite-field point has the identity structure map and inherits its properties.
Source: blueprint proof step 3 (blueprint: cor-coef-verdier-weil-equivariance). -/
instance pointModelLocallyFiniteType : LocallyOfFiniteType (pointModel D).hom :=
  inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of D.k₀))))

/-- The finite-field point's identity structure map is quasi-compact.
Source: blueprint proof step 3 (blueprint: cor-coef-verdier-weil-equivariance). -/
instance pointModelQuasiCompact : QuasiCompact (pointModel D).hom :=
  inferInstanceAs (QuasiCompact (𝟙 (Spec (.of D.k₀))))

/-- The finite-field point's identity structure map is separated.
Source: blueprint proof step 3 (blueprint: cor-coef-verdier-weil-equivariance). -/
instance pointModelSeparated : IsSeparated (pointModel D).hom :=
  inferInstanceAs (IsSeparated (𝟙 (Spec (.of D.k₀))))

/-- The geometric fibre of the finite-field point has separated structure map.
Source: blueprint proof step 3 (blueprint: cor-coef-verdier-weil-equivariance). -/
abbrev pointFiberSeparated :
    IsSeparated ((D.geometricFiber (pointModel D)).left ↘ Spec (.of D.k)) :=
  fiberStructureSeparated D (pointModel D)

/-- The structure morphism before geometric base change.
Source: blueprint proof step 3 (blueprint: cor-coef-verdier-weil-equivariance). -/
abbrev structureModel : X₀ ⟶ pointModel D := Over.homMk X₀.hom

/-- The model structure map inherits separatedness from X₀.
Source: blueprint proof step 3 (blueprint: cor-coef-verdier-weil-equivariance). -/
instance structureModelSeparated : IsSeparated (structureModel D X₀).left :=
  inferInstanceAs (IsSeparated X₀.hom)

/-- The model structure map inherits local finite type from X₀.
Source: blueprint proof step 3 (blueprint: cor-coef-verdier-weil-equivariance). -/
instance structureModelLocallyFiniteType : LocallyOfFiniteType (structureModel D X₀).left :=
  inferInstanceAs (LocallyOfFiniteType X₀.hom)

/-- The model structure map inherits quasi-compactness from X₀.
Source: blueprint proof step 3 (blueprint: cor-coef-verdier-weil-equivariance). -/
instance structureModelQuasiCompact : QuasiCompact (structureModel D X₀).left :=
  inferInstanceAs (QuasiCompact X₀.hom)

/-- The completed constant rank-one object at a finite coefficient field.
Source: blueprint proof step 3 (blueprint: cor-coef-verdier-weil-equivariance). -/
def finiteUnit (E : Index l Ω) :=
  @pullbackTensorRationalUnit l _ (Coefficient.{u} l Ω E) _ _ _
    (D.geometricFiber X₀).left (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)

/-- The specified left unitor for the finite constant coefficient object.
Source: blueprint proof step 3 (blueprint: cor-coef-verdier-weil-equivariance). -/
def finiteUnitor (E : Index l Ω) :
    ∀ M : Stage l Ω (D.geometricFiber X₀).left E,
      (@rationalDerivedTensor l _ (Coefficient.{u} l Ω E) _ _ _
        (D.geometricFiber X₀).left (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)).obj
          (finiteUnit D l hl Ω X₀ E, M) ≅ M :=
  @pullbackTensorRationalLeftUnitor l _ (Coefficient.{u} l Ω E) _ _ _
    (D.geometricFiber X₀).left (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)

/-- The same constant coefficient object in the common-stage category.
Source: blueprint proof steps 3 and 8 (blueprint: cor-coef-verdier-weil-equivariance). -/
def commonUnit :=
  @pullbackTensorCommonUnit l _ Ω _ _ _ (D.geometricFiber X₀).left
    (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)

/-- The specified common-stage left unitor for that coefficient object.
Source: blueprint proof steps 3 and 8 (blueprint: cor-coef-verdier-weil-equivariance). -/
def commonUnitor :
    ∀ M : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left,
      (@commonStageDerivedTensor l _ Ω _ _ _ (D.geometricFiber X₀).left
        (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)).obj
          (commonUnit D l hl Ω X₀, M) ≅ M :=
  @pullbackTensorCommonLeftUnitor l _ Ω _ _ _ (D.geometricFiber X₀).left
    (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)

/-- Both dualizing Weil structures come from the canonical structure-morphism exchange,
its actual adjunction mate, and the constant object's unit-normalized identification.
Source: blueprint proof steps 3 and 8 (blueprint: cor-coef-verdier-weil-equivariance). -/
def DualizingNormalization (B : FiberDuality D l hl Ω X₀)
    (W : Coefficients D l hl Ω X₀ B) : Prop :=
  letI := fiberStructureLocallyFiniteType D X₀
  letI := fiberStructureQuasiCompact D X₀
  letI := fiberStructureSeparated D X₀
  letI := pointFiberSeparated D
  ∀ c₀ : Compactification (structureModel D X₀).left,
    ∃ A : FiberExceptional D l hl Ω X₀ (structureModel D X₀)
        (FrobeniusExchange.geometricCompactification D (structureModel D X₀) c₀),
    ∃ Z : FrobeniusAdjunctions D l hl Ω X₀ (structureModel D X₀) c₀ A,
    (∀ E : Index l Ω,
      (DualizingMate
        (sfWeilFrobeniusPullback D l hl X₀ (Coefficient.{u} l Ω E))
        (sfWeilFrobeniusPullback D l hl (pointModel D) (Coefficient.{u} l Ω E))
        (fiberRight D l hl Ω X₀ (structureModel D X₀)
          (FrobeniusExchange.geometricCompactification D (structureModel D X₀) c₀) A E)
        (Z.finite E).right
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) _).obj
          (B.finite.omega E).omega) (W.finite E).omegaStructure
        (finiteUnit D l hl Ω (pointModel D) E)
        (@rationalDerivedTensor l _ (Coefficient.{u} l Ω E) _ _ _
          (D.geometricFiber (pointModel D)).left
          (fun x ↦ sfWeilPrimeInvertible D l hl (pointModel D) x))
        (finiteMu D l hl Ω (pointModel D) E) (finiteUnitor D l hl Ω (pointModel D) E))) ∧
    (DualizingMate (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω)
      (sfCommonStageWeilFrobeniusPullback D l hl (pointModel D) Ω)
      A.right Z.common.right B.omega W.common.omegaStructure
      (commonUnit D l hl Ω (pointModel D))
      (@commonStageDerivedTensor l _ Ω _ _ _ (D.geometricFiber (pointModel D)).left
        (fun x ↦ sfWeilPrimeInvertible D l hl (pointModel D) x))
      (commonMu D l hl Ω (pointModel D)) (commonUnitor D l hl Ω (pointModel D)))


/-- Every geometric fiber has the asserted duality, and every descended morphism
has the asserted exceptional adjunction, simultaneously at finite coefficients and Ω.
The underlying maps are fixed by the published duality, internal-Hom, dualizing,
scalar-extension and exceptional-formula interfaces.
Source: blueprint cor-coef-verdier-weil-equivariance, all clauses
(blueprint: cor-coef-verdier-weil-equivariance). -/
def Conclusion : Prop :=
  ∃ (BX : FiberDuality D l hl Ω X₀),
    Nonempty (FiberInternalHom D l hl Ω X₀ BX) ∧
    FiberDualizing D l hl Ω X₀ BX ∧
    ∃ WX : Coefficients D l hl Ω X₀ BX,
    DualizingNormalization D l hl Ω X₀ BX WX ∧
    ∀ (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom]
      [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
      (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left]
      [QuasiCompact f₀.left],
      ∀ (c₀ : Compactification f₀.left),
      ∃ (BY : FiberDuality D l hl Ω Y₀)
        (A : FiberExceptional D l hl Ω X₀ f₀
          (FrobeniusExchange.geometricCompactification D f₀ c₀)),
        Nonempty (FiberInternalHom D l hl Ω Y₀ BY) ∧
        FiberDualizing D l hl Ω Y₀ BY ∧
        Nonempty (FiberExceptionalFormula D l hl Ω X₀ f₀
          (FrobeniusExchange.geometricCompactification D f₀ c₀) BX BY A) ∧
        ∃ WY : Coefficients D l hl Ω Y₀ BY,
          DualizingNormalization D l hl Ω Y₀ BY WY ∧
          Nonempty (Adjunctions D l hl Ω X₀ f₀ c₀ A WX WY)

end Geometric
end WeilConjectures.CoefVerdierWeil
```

## New

The record declarations live in `Sheaf.SixFunctors.CoefVerdierWeilData`, which the
original module publicly imports. Finite and common comparison endpoints are explicit;
`fiberLeft` is defined before the adjunction that uses it. The raw finite category and
its `Stage` abbreviation are definitionally equal. This avoids repeatedly unfolding
coefficient-field structure instances during elaboration and kernel checking.
The generic containers retain all the old fields and every normalization equation.

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.Paper.SixFunctorOperationDatum
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.SixFunctors.CoefQbarVerdier
public import Sheaf.Paper.FrobeniusGeometricExchange
public import Sheaf.SixFunctors.RationalVerdier
public import Sheaf.SixFunctors.RationalOperations
public import Sheaf.Paper.DerivedPullbackTensorIso

/-! # Weil equivariance of completed coefficient duality

Source: Weil blueprint main-20261015, sec-six-functors/sk-thm-sf-package,
cor-coef-verdier-weil-equivariance, statement and proof paragraphs 1--3
(blueprint: cor-coef-verdier-weil-equivariance).
The extracted record interface is (blueprint: def-coef-verdier-weil-data).

The records package conclusions about the actual coefficient-passage operations.
All structure isomorphisms act on rational objects themselves.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option maxRecDepth 10000
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v a b a' b' i w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.Endofunctor (IsoAlgebra)

namespace WeilConjectures.CoefVerdierWeil

/-- A pair of indexed data families pinned by their prescribed component maps.
Source: blueprint normalized Frobenius adjunctions
(blueprint: def-coef-verdier-weil-data). -/
structure PinnedFrobeniusAdjunctions {I : Type w} (F : I → Type a) (C : Type b)
    (finiteNorm : (∀ i, F i) → Prop) (commonNorm : C → Prop) where
  finite (i : I) : F i
  common : C
  finiteNormalized : finiteNorm finite
  commonNormalized : commonNorm common


/-- Coefficient laws on a fixed family of Frobenius adjunctions.
Source: blueprint proof paragraph 3 (blueprint: def-coef-verdier-weil-data). -/
structure CompatibleFrobeniusAdjunctions (Z : Type a)
    (scalarLaw stageLaw : Z → Prop) where
  toFrobeniusAdjunctions : Z
  scalar : scalarLaw toFrobeniusAdjunctions
  stage : stageLaw toFrobeniusAdjunctions

/-- A family of coefficient structures with its prescribed scalar and stage laws.
Source: blueprint coefficient descent (blueprint: def-coef-verdier-weil-data). -/
structure CoefficientStructures {I : Type i} [Preorder I]
    (F : I → Type a) (C : Type b) (S : I → Type a')
    (scalarLaw : ∀ i j, i ≤ j → F i → F j → Prop)
    (stageNormalization : ∀ i, S i → Prop)
    (stageLaw : ∀ i, F i → C → S i → Prop) where
  finite (i : I) : F i
  common : C
  scalar (i j : I) (h : i ≤ j) : scalarLaw i j h (finite i) (finite j)
  stageFrobenius (i : I) : S i
  stageNormalized (i : I) : stageNormalization i (stageFrobenius i)
  stage (i : I) : stageLaw i (finite i) common (stageFrobenius i)

/-- The induced dual Frobenius is c_K followed by D(theta_K inverse).
Source: blueprint proof paragraph 1 (blueprint: cor-coef-verdier-weil-equivariance). -/
def dualStructure {C : Type a} [Category.{b} C] (P : C ⥤ C) (V : Cᵒᵖ ⥤ C)
    (c : V ⋙ P ≅ P.op ⋙ V) (K : IsoAlgebra P) :
    P.obj (V.obj (op K.carrier)) ≅ V.obj (op K.carrier) :=
  c.app (op K.carrier) ≪≫ V.mapIso K.str.symm.op

/-- The equations for the canonical dual Frobenius, evaluation and actual biduality.
The first equation normalizes c by evaluation; the remaining equations explicitly
state functoriality on Weil arrows, evaluation equivariance, and delta equivariance.
Source: blueprint proof paragraphs 1--2
(blueprint: cor-coef-verdier-weil-equivariance). -/
structure Duality {C : Type a} [Category.{b} C]
    (P : C ⥤ C) (V : Cᵒᵖ ⥤ C) (T : C × C ⥤ C) (omega : C)
    (evaluation : ∀ K : C, T.obj (K, V.obj (op K)) ⟶ omega)
    (delta : 𝟭 C ≅ V.rightOp ⋙ V)
    (mu : ∀ K M : C, P.obj (T.obj (K, M)) ≅ T.obj (P.obj K, P.obj M)) where
  omegaStructure : P.obj omega ≅ omega
  comparison : V ⋙ P ≅ P.op ⋙ V
  comparison_evaluation (K : C) :
    (mu K (V.obj (op K))).hom ≫
      T.map (Prod.mkHom (𝟙 (P.obj K)) (comparison.hom.app (op K))) ≫
      evaluation (P.obj K) = P.map (evaluation K) ≫ omegaStructure.hom
  morphism {K M : IsoAlgebra P} (f : K ⟶ M) :
    (dualStructure P V comparison M).hom ≫ V.map f.hom.f.op =
      P.map (V.map f.hom.f.op) ≫ (dualStructure P V comparison K).hom
  evaluation_equivariant (K : IsoAlgebra P) :
    (mu K.carrier (V.obj (op K.carrier))).hom ≫
      T.map (Prod.mkHom K.str.hom (dualStructure P V comparison K).hom) ≫
      evaluation K.carrier = P.map (evaluation K.carrier) ≫ omegaStructure.hom
  biduality_equivariant (K : IsoAlgebra P) :
    K.str.hom ≫ delta.hom.app K.carrier =
      P.map (delta.hom.app K.carrier) ≫
        (dualStructure P V comparison
          (IsoAlgebra.mk (V.obj (op K.carrier)) (dualStructure P V comparison K))).hom

/-- Exceptional Frobenius comparison and equivariance of the specified adjunction.
The right comparison is the mate of the inverse left comparison. Thus the unit
and counit are those of the original constructible adjunction.
Source: blueprint proof paragraph 1, explicit mate in DAG step 3
(blueprint: cor-coef-verdier-weil-equivariance). -/
structure Exceptional {C : Type a} {C' : Type a'}
    [Category.{b} C] [Category.{b'} C'] (P : C ⥤ C) (Q : C' ⥤ C')
    {F : C ⥤ C'} {G : C' ⥤ C} (adj : F ⊣ G) where
  left : F ⋙ Q ≅ P ⋙ F
  right : G ⋙ P ≅ Q ⋙ G
  mate : right.hom = (mateEquiv adj adj (TwoSquare.mk _ _ _ _ left.inv)).natTrans
  unit (K : IsoAlgebra P) :
    K.str.hom ≫ adj.unit.app K.carrier =
      P.map (adj.unit.app K.carrier) ≫ right.hom.app (F.obj K.carrier) ≫
        G.map (left.hom.app K.carrier) ≫ G.map (F.map K.str.hom)
  counit (M : IsoAlgebra Q) :
    left.hom.app (G.obj M.carrier) ≫ F.map (right.hom.app M.carrier) ≫
      F.map (G.map M.str.hom) ≫ adj.counit.app M.carrier =
        Q.map (adj.counit.app M.carrier) ≫ M.str.hom

/-- Normalization of the dualizing Frobenius by the actual exceptional mate.
The constant object's structure is fixed by the tensor unit equation.
Source: blueprint proof step 3 (blueprint: cor-coef-verdier-weil-equivariance). -/
@[irreducible] def DualizingMate {C : Type a} {C' : Type a'}
    [Category.{b} C] [Category.{b'} C'] (P : C ⥤ C) (Q : C' ⥤ C')
    (G : C' ⥤ C) (right : G ⋙ P ≅ Q ⋙ G) (omega : C)
    (omegaTheta : P.obj omega ≅ omega) (unit : C') (T : C' × C' ⥤ C')
    (mu : ∀ K M : C', Q.obj (T.obj (K, M)) ≅ T.obj (Q.obj K, Q.obj M))
    (unitor : ∀ M : C', T.obj (unit, M) ≅ M) : Prop :=
  ∃ constant : Q.obj unit ≅ unit,
    (∀ M : C',
      (mu unit M).hom ≫ T.map (Prod.mkHom constant.hom (𝟙 (Q.obj M))) ≫
        (unitor (Q.obj M)).hom = Q.map (unitor M).hom) ∧
    ∃ identification : omega ≅ G.obj unit,
      omegaTheta.hom ≫ identification.hom =
        P.map identification.hom ≫ right.hom.app unit ≫ G.map constant.hom

/-- A scalar or inclusion comparison is equivariant with the specified Frobenius maps.
Source: blueprint proof paragraph 3 (blueprint: cor-coef-verdier-weil-equivariance). -/
def IsEquivariant {C : Type a} {C' : Type a'}
    [Category.{b} C] [Category.{b'} C'] (P : C ⥤ C) (Q : C' ⥤ C')
    (L : C ⥤ C') (s : L ⋙ Q ≅ P ⋙ L)
    {K : C} {M : C'} (theta : P.obj K ≅ K) (psi : Q.obj M ≅ M)
    (f : L.obj K ⟶ M) : Prop :=
  s.hom.app K ≫ L.map theta.hom ≫ f = Q.map f ≫ psi.hom



/-- The Weil structure transported by a functor with its specified Frobenius comparison.
Source: blueprint proof step 7 (blueprint: cor-coef-verdier-weil-equivariance). -/
def transportedStructure {C : Type a} {C' : Type a'}
    [Category.{b} C] [Category.{b'} C'] (P : C ⥤ C) (Q : C' ⥤ C')
    (L : C ⥤ C') (s : L ⋙ Q ≅ P ⋙ L) (K : IsoAlgebra P) :
    Q.obj (L.obj K.carrier) ≅ L.obj K.carrier :=
  s.app K.carrier ≪≫ L.mapIso K.str

/-- Equivariance of the actual dualizing and duality comparison arrows. Evaluation
and biduality diagrams use these same arrows and the specified equivariant maps.
Source: blueprint proof step 7 (blueprint: cor-coef-verdier-weil-equivariance). -/
structure DualityComparison {C : Type a} {C' : Type a'}
    [Category.{b} C] [Category.{b'} C']
    {P : C ⥤ C} {Q : C' ⥤ C'} {V : Cᵒᵖ ⥤ C} {V' : C'ᵒᵖ ⥤ C'}
    {T : C × C ⥤ C} {T' : C' × C' ⥤ C'} {omega : C} {omega' : C'}
    {evaluation : ∀ K : C, T.obj (K, V.obj (op K)) ⟶ omega}
    {evaluation' : ∀ K : C', T'.obj (K, V'.obj (op K)) ⟶ omega'}
    {delta : 𝟭 C ≅ V.rightOp ⋙ V} {delta' : 𝟭 C' ≅ V'.rightOp ⋙ V'}
    {mu : ∀ K M : C, P.obj (T.obj (K, M)) ≅ T.obj (P.obj K, P.obj M)}
    {mu' : ∀ K M : C', Q.obj (T'.obj (K, M)) ≅ T'.obj (Q.obj K, Q.obj M)}
    (W : Duality P V T omega evaluation delta mu)
    (W' : Duality Q V' T' omega' evaluation' delta' mu')
    (L : C ⥤ C') (s : L ⋙ Q ≅ P ⋙ L)
    (u : L.obj omega ≅ omega') (beta : V ⋙ L ≅ L.op ⋙ V') : Prop where
  omega : IsEquivariant P Q L s W.omegaStructure W'.omegaStructure u.hom
  dual (K : IsoAlgebra P) :
    IsEquivariant P Q L s (dualStructure P V W.comparison K)
      (dualStructure Q V' W'.comparison
        (IsoAlgebra.mk (L.obj K.carrier) (transportedStructure P Q L s K)))
      (beta.hom.app (op K.carrier))

/-- Equivariance of canonical scalar or stage-inclusion comparisons for both
exceptional functors. Their compatibility diagrams retain the original units and counits.
Source: blueprint proof steps 3 and 7
(blueprint: cor-coef-verdier-weil-equivariance). -/
structure ExceptionalComparison {C : Type a} {C' : Type a'}
    {B : Type b} {B' : Type b'}
    [Category C] [Category C'] [Category B] [Category B']
    {P : C ⥤ C} {P' : C' ⥤ C'} {Q : B ⥤ B} {Q' : B' ⥤ B'}
    {F : C ⥤ B} {G : B ⥤ C} {F' : C' ⥤ B'} {G' : B' ⥤ C'}
    {adj : F ⊣ G} {adj' : F' ⊣ G'}
    (W : Exceptional P Q adj) (W' : Exceptional P' Q' adj')
    (L : C ⥤ C') (M : B ⥤ B') (s : L ⋙ P' ≅ P ⋙ L) (t : M ⋙ Q' ≅ Q ⋙ M)
    (alpha : F ⋙ M ≅ L ⋙ F') (beta : G ⋙ L ≅ M ⋙ G') : Prop where
  left (K : IsoAlgebra P) :
    IsEquivariant Q Q' M t (transportedStructure P Q F W.left K)
      (transportedStructure P' Q' F' W'.left
        (IsoAlgebra.mk (L.obj K.carrier) (transportedStructure P P' L s K)))
      (alpha.hom.app K.carrier)
  right (K : IsoAlgebra Q) :
    IsEquivariant P P' L s (transportedStructure Q P G W.right K)
      (transportedStructure Q' P' G' W'.right
        (IsoAlgebra.mk (M.obj K.carrier) (transportedStructure Q Q' M t K)))
      (beta.hom.app K.carrier)

/-- Conjugate a specified Frobenius exchange by a realization of its left functor.
Source: blueprint proof steps 2--3 (blueprint: cor-coef-verdier-weil-equivariance). -/
@[irreducible] def realizedExchangeAt {C : Type a} {B : Type b} [Category C] [Category B]
    {P : C ⥤ C} {Q : B ⥤ B} {F H : C ⥤ B}
    (e : F ≅ H) (w : F ⋙ Q ≅ P ⋙ F) (K : C) :
    Q.obj (H.obj K) ⟶ H.obj (P.obj K) :=
  Q.map (e.inv.app K) ≫ w.hom.app K ≫ e.hom.app (P.obj K)

/-- The same conjugation after the specified stage-inclusion comparisons.
Source: blueprint proof steps 3 and 8 (blueprint: cor-coef-verdier-weil-equivariance). -/
@[irreducible] def realizedStageExchangeAt {C : Type a} {C' : Type a'} {B : Type b} {B' : Type b'}
    [Category C] [Category C'] [Category B] [Category B']
    {P : C ⥤ C} {P' : C' ⥤ C'} {Q : B ⥤ B} {Q' : B' ⥤ B'}
    {F H : C ⥤ B} {F' : C' ⥤ B'} {L : C ⥤ C'} {M : B ⥤ B'}
    (e : F ≅ H) (beta : F ⋙ M ≅ L ⋙ F')
    (s : ∀ K : C, P'.obj (L.obj K) ≅ L.obj (P.obj K))
    (t : ∀ N : B, Q'.obj (M.obj N) ≅ M.obj (Q.obj N))
    (w : F' ⋙ Q' ≅ P' ⋙ F') (K : C) :
    M.obj (Q.obj (H.obj K)) ⟶ M.obj (H.obj (P.obj K)) :=
  M.map (Q.map (e.inv.app K)) ≫ (t (F.obj K)).inv ≫
    Q'.map (beta.hom.app K) ≫ w.hom.app (L.obj K) ≫
    F'.map ((s K).hom) ≫ beta.inv.app (P.obj K) ≫ M.map (e.hom.app (P.obj K))

/-- The structure morphism of the geometric fiber inherits local finite type.
Source: blueprint geometric-fiber convention, Stacks 01T0
(blueprint: cor-coef-verdier-weil-equivariance). -/
abbrev fiberStructureLocallyFiniteType (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
  (FrobeniusExchange.fiber_finiteType D X₀).1

/-- The structure morphism of the geometric fiber inherits quasi-compactness.
Source: blueprint geometric-fiber convention, Stacks 01T0
(blueprint: cor-coef-verdier-weil-equivariance). -/
abbrev fiberStructureQuasiCompact (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
  (FrobeniusExchange.fiber_finiteType D X₀).2

/-- Separatedness is inherited by the actual geometric fiber structure morphism.
Source: blueprint separated finite-type convention, Stacks 01KH
(blueprint: cor-coef-verdier-weil-equivariance). -/
abbrev fiberStructureSeparated (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom]
    [QuasiCompact X₀.hom] [IsSeparated X₀.hom] :
    IsSeparated ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
  MorphismProperty.baseChange_obj (P := @IsSeparated) _ X₀ inferInstance

/-- The geometric map inherits separatedness from the descended morphism.
Source: blueprint exceptional clause, Stacks 01KH
(blueprint: cor-coef-verdier-weil-equivariance). -/
abbrev fiberMapSeparated (D : FiniteFieldDatum.{u})
    {X₀ Y₀ : Over (Spec (.of D.k₀))} (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left] :
    IsSeparated (FrobeniusExchange.fiberMap D f₀) :=
  MorphismProperty.overPullbackMap (P := @IsSeparated) _ f₀ inferInstance

/-- The geometric map inherits local finite type from the descended morphism.
Source: blueprint exceptional clause, Stacks 01T0
(blueprint: cor-coef-verdier-weil-equivariance). -/
abbrev fiberMapLocallyFiniteType (D : FiniteFieldDatum.{u})
    {X₀ Y₀ : Over (Spec (.of D.k₀))} (f₀ : X₀ ⟶ Y₀) [LocallyOfFiniteType f₀.left] :
    LocallyOfFiniteType (FrobeniusExchange.fiberMap D f₀) :=
  MorphismProperty.overPullbackMap (P := @LocallyOfFiniteType) _ f₀ inferInstance

/-- The geometric map inherits quasi-compactness from the descended morphism.
Source: blueprint exceptional clause, Stacks 01T0
(blueprint: cor-coef-verdier-weil-equivariance). -/
abbrev fiberMapQuasiCompact (D : FiniteFieldDatum.{u})
    {X₀ Y₀ : Over (Spec (.of D.k₀))} (f₀ : X₀ ⟶ Y₀) [QuasiCompact f₀.left] :
    QuasiCompact (FrobeniusExchange.fiberMap D f₀) :=
  MorphismProperty.overPullbackMap (P := @QuasiCompact) _ f₀ inferInstance

section Geometric
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion transition)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom]
  [QuasiCompact X₀.hom] [IsSeparated X₀.hom]

/-- The existing stage inclusion, with raw category endpoints cached.
Source: blueprint coefficient descent (blueprint: def-coef-verdier-weil-data). -/
def fiberInclusion (E : Index l Ω) :
    sfRationalConstructibleCategory l (Coefficient.{u} l Ω E)
      (D.geometricFiber X₀).left ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left :=
  inclusion E

/-- The actual duality type on the geometric fiber, with inherited structure-map instances.
Source: blueprint geometric-fiber convention
(blueprint: cor-coef-verdier-weil-equivariance). -/
def FiberDuality :=
  letI := fiberStructureLocallyFiniteType D X₀
  letI := fiberStructureQuasiCompact D X₀
  letI := fiberStructureSeparated D X₀
  CoefQbarVerdier.Duality D l hl Ω (D.geometricFiber X₀).left


/-- The actual internal-Hom identification, on the same geometric fiber.
Source: blueprint duality clause (blueprint: cor-coef-verdier-weil-equivariance). -/
def FiberInternalHom (B : FiberDuality D l hl Ω X₀) :=
  letI := fiberStructureLocallyFiniteType D X₀
  letI := fiberStructureQuasiCompact D X₀
  letI := fiberStructureSeparated D X₀
  CoefQbarVerdier.InternalHom D l hl Ω (D.geometricFiber X₀).left B


/-- The specified exceptional-unit identification of the dualizing object.
Source: blueprint dualizing clause (blueprint: cor-coef-verdier-weil-equivariance). -/
def FiberDualizing (B : FiberDuality D l hl Ω X₀) : Prop :=
  letI := fiberStructureLocallyFiniteType D X₀
  letI := fiberStructureQuasiCompact D X₀
  letI := fiberStructureSeparated D X₀
  CoefQbarVerdier.Dualizing D l hl Ω (D.geometricFiber X₀).left B


/-- The actual Frobenius pullback-tensor comparison at a finite coefficient stage.
Source: blueprint proof steps 2 and 4
(blueprint: cor-coef-verdier-weil-equivariance). -/
def finiteMu (E : Index l Ω)
    (K M : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E)
      (D.geometricFiber X₀).left) :
    (sfWeilFrobeniusPullback D l hl X₀ (Coefficient.{u} l Ω E)).obj
      ((RationalVerdier.tensor D l hl _ (Coefficient.{u} l Ω E)).obj (K, M)) ≅
    (RationalVerdier.tensor D l hl _ (Coefficient.{u} l Ω E)).obj
      ((sfWeilFrobeniusPullback D l hl X₀ (Coefficient.{u} l Ω E)).obj K,
       (sfWeilFrobeniusPullback D l hl X₀ (Coefficient.{u} l Ω E)).obj M) :=
  @canonicalRationalPullbackTensor l _ (Coefficient.{u} l Ω E) _ _ _ _ _
    (D.geometricFrobenius X₀).hom
    (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)
    (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x) K M


/-- The actual common-stage Frobenius pullback-tensor comparison.
Source: blueprint proof steps 2 and 8
(blueprint: cor-coef-verdier-weil-equivariance). -/
def commonMu
    (K M : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left) :
    (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω).obj
      ((CoefQbarTensor D l hl Ω (D.geometricFiber X₀).left).obj (K, M)) ≅
    (CoefQbarTensor D l hl Ω (D.geometricFiber X₀).left).obj
      ((sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω).obj K,
       (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω).obj M) :=
  @canonicalCommonStagePullbackTensor l _ Ω _ _ _ _ _
    (D.geometricFrobenius X₀).hom
    (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)
    (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x) K M


/-- The inverse canonical pullback/scalar comparison, in the convention L P' ≅ P L.
Source: blueprint proof steps 6--7
(blueprint: cor-coef-verdier-weil-equivariance). -/
def scalarFrobenius (E L : Index l Ω) (h : E ≤ L) :
    transition l Ω (D.geometricFiber X₀).left E L h ⋙
      sfWeilFrobeniusPullback D l hl X₀ (Coefficient.{u} l Ω L) ≅
    sfWeilFrobeniusPullback D l hl X₀ (Coefficient.{u} l Ω E) ⋙
      transition l Ω (D.geometricFiber X₀).left E L h :=
  (@rationalPullbackScalarComparison l _ (Coefficient.{u} l Ω E) _ _ _
    (Coefficient.{u} l Ω L) _ _ _ (coefficientInclusion l Ω E L h) _ _
    (D.geometricFrobenius X₀).hom
    (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)
    (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)).symm


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A cached finite-stage duality type. Source: the normalized duality clause
(blueprint: def-coef-verdier-weil-data). -/
def finiteDualityType (B : FiberDuality D l hl Ω X₀) (E : Index l Ω) :=
    letI := fiberStructureLocallyFiniteType D X₀
    letI := fiberStructureQuasiCompact D X₀
    letI := fiberStructureSeparated D X₀
    Duality (sfWeilFrobeniusPullback D l hl X₀ (Coefficient.{u} l Ω E))
      (B.finite.datum E).dual (RationalVerdier.tensor D l hl _ (Coefficient.{u} l Ω E))
      ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) _).obj
        (B.finite.omega E).omega)
      (B.finite.datum E).evaluation (B.finite.datum E).bidual (finiteMu D l hl Ω X₀ E)

/-- A cached common-stage duality type. Source: the normalized duality clause
(blueprint: def-coef-verdier-weil-data). -/
def commonDualityType (B : FiberDuality D l hl Ω X₀) :=
    letI := fiberStructureLocallyFiniteType D X₀
    letI := fiberStructureQuasiCompact D X₀
    letI := fiberStructureSeparated D X₀
    Duality (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω) B.duality.dual
      (CoefQbarTensor D l hl Ω _) B.omega B.evaluation B.duality.bidual (commonMu D l hl Ω X₀)

/-- A cached inclusion Frobenius comparison type. Source: coefficient descent
(blueprint: def-coef-verdier-weil-data). -/
def stageFrobeniusType (E : Index l Ω) :=
    fiberInclusion D l Ω X₀ E ⋙ sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω ≅
      sfWeilFrobeniusPullback D l hl X₀ (Coefficient.{u} l Ω E) ⋙ fiberInclusion D l Ω X₀ E

/-- The prescribed scalar compatibility. Source: coefficient descent
(blueprint: def-coef-verdier-weil-data). -/
def scalarDualityLaw (B : FiberDuality D l hl Ω X₀)
    (E L : Index l Ω) (h : E ≤ L)
    (x : finiteDualityType D l hl Ω X₀ B E)
    (y : finiteDualityType D l hl Ω X₀ B L) : Prop :=
    letI := fiberStructureLocallyFiniteType D X₀
    letI := fiberStructureQuasiCompact D X₀
    letI := fiberStructureSeparated D X₀
    DualityComparison x y (transition l Ω _ E L h)
      (scalarFrobenius D l hl Ω X₀ E L h)
      (B.finite.scalar E L h).omega (B.finite.beta E L h)

/-- The prescribed inclusion components. Source: coefficient descent
(blueprint: def-coef-verdier-weil-data). -/
def stageFrobeniusLaw (E : Index l Ω)
    (z : stageFrobeniusType D l hl Ω X₀ E) : Prop :=
  ∀ (K : Stage l Ω (D.geometricFiber X₀).left E),
    z.app K = sfWeilStagePullbackIdentification D l hl X₀ Ω E K

/-- Compatibility of finite and common duality. Source: coefficient descent
(blueprint: def-coef-verdier-weil-data). -/
def stageDualityLaw (B : FiberDuality D l hl Ω X₀) (E : Index l Ω)
    (x : finiteDualityType D l hl Ω X₀ B E)
    (y : commonDualityType D l hl Ω X₀ B)
    (z : stageFrobeniusType D l hl Ω X₀ E) : Prop :=
    letI := fiberStructureLocallyFiniteType D X₀
    letI := fiberStructureQuasiCompact D X₀
    letI := fiberStructureSeparated D X₀
    DualityComparison x y (fiberInclusion D l Ω X₀ E) z
      (B.omegaComparison E) (B.comparison E)

/-- Weil structures at finite and common coefficients, with the prescribed scalar
and stage equations. Source: blueprint coefficient descent
(blueprint: def-coef-verdier-weil-data). -/
abbrev Coefficients (B : FiberDuality D l hl Ω X₀) :=
  CoefficientStructures (finiteDualityType D l hl Ω X₀ B)
    (commonDualityType D l hl Ω X₀ B) (stageFrobeniusType D l hl Ω X₀)
    (scalarDualityLaw D l hl Ω X₀ B) (stageFrobeniusLaw D l hl Ω X₀)
    (stageDualityLaw D l hl Ω X₀ B)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section ExceptionalGeometry
variable {Y₀ : Over (Spec (.of D.k₀))} [LocallyOfFiniteType Y₀.hom]
  [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
  (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left]
  [QuasiCompact f₀.left] (c : Compactification (FrobeniusExchange.fiberMap D f₀))


/-- The actual exceptional record, with inherited fiber instances.
Source: blueprint exceptional clause (blueprint: cor-coef-verdier-weil-equivariance). -/
def FiberExceptional :=
  letI := fiberStructureLocallyFiniteType D X₀
  letI := fiberStructureQuasiCompact D X₀
  letI := fiberStructureSeparated D X₀
  letI := fiberStructureLocallyFiniteType D Y₀
  letI := fiberStructureQuasiCompact D Y₀
  letI := fiberStructureSeparated D Y₀
  letI := fiberMapSeparated D f₀
  letI := fiberMapLocallyFiniteType D f₀
  letI := fiberMapQuasiCompact D f₀
  CoefQbarVerdier.Exceptional (Y := (D.geometricFiber Y₀).left)
    D l hl Ω (D.geometricFiber X₀).left
    (FrobeniusExchange.fiberMap D f₀) c


/-- The given finite compact-support functor, with the inherited geometric instances.
Source: blueprint exceptional coefficient clause
(blueprint: def-coef-verdier-weil-data). -/
def fiberLeft (A : FiberExceptional D l hl Ω X₀ f₀ c) (E : Index l Ω) :
    sfRationalConstructibleCategory l (Coefficient.{u} l Ω E)
      (D.geometricFiber X₀).left ⥤
      sfRationalConstructibleCategory l (Coefficient.{u} l Ω E)
      (D.geometricFiber Y₀).left :=
  letI := fiberStructureLocallyFiniteType D X₀
  letI := fiberStructureQuasiCompact D X₀
  letI := fiberStructureSeparated D X₀
  letI := fiberStructureLocallyFiniteType D Y₀
  letI := fiberStructureQuasiCompact D Y₀
  letI := fiberStructureSeparated D Y₀
  letI := fiberMapSeparated D f₀
  letI := fiberMapLocallyFiniteType D f₀
  letI := fiberMapQuasiCompact D f₀
  CoefQbarVerdier.finiteLeft (Y := (D.geometricFiber Y₀).left)
    D l hl Ω (D.geometricFiber X₀).left (FrobeniusExchange.fiberMap D f₀) c A.system E

/-- The specified finite exceptional functor, with inherited geometric instances.
Source: blueprint proof step 3 (blueprint: cor-coef-verdier-weil-equivariance). -/
def fiberRight (A : FiberExceptional D l hl Ω X₀ f₀ c) (E : Index l Ω) :
    sfRationalConstructibleCategory l (Coefficient.{u} l Ω E)
      (D.geometricFiber Y₀).left ⥤
      sfRationalConstructibleCategory l (Coefficient.{u} l Ω E)
      (D.geometricFiber X₀).left :=
  letI := fiberStructureLocallyFiniteType D X₀
  letI := fiberStructureQuasiCompact D X₀
  letI := fiberStructureSeparated D X₀
  letI := fiberStructureLocallyFiniteType D Y₀
  letI := fiberStructureQuasiCompact D Y₀
  letI := fiberStructureSeparated D Y₀
  letI := fiberMapSeparated D f₀
  letI := fiberMapLocallyFiniteType D f₀
  letI := fiberMapQuasiCompact D f₀
  CoefQbarVerdier.finiteRight (Y := (D.geometricFiber Y₀).left)
    D l hl Ω (D.geometricFiber X₀).left (FrobeniusExchange.fiberMap D f₀) c A.system E


/-- The actual finite-stage adjunction, with inherited fiber instances.
Source: blueprint exceptional clause (blueprint: cor-coef-verdier-weil-equivariance). -/
def fiberAdjunction (A : FiberExceptional D l hl Ω X₀ f₀ c) (E : Index l Ω) :
    fiberLeft D l hl Ω X₀ f₀ c A E ⊣
    fiberRight D l hl Ω X₀ f₀ c A E :=
  letI := fiberStructureLocallyFiniteType D X₀
  letI := fiberStructureQuasiCompact D X₀
  letI := fiberStructureSeparated D X₀
  letI := fiberStructureLocallyFiniteType D Y₀
  letI := fiberStructureQuasiCompact D Y₀
  letI := fiberStructureSeparated D Y₀
  letI := fiberMapSeparated D f₀
  letI := fiberMapLocallyFiniteType D f₀
  letI := fiberMapQuasiCompact D f₀
  CoefQbarVerdier.finiteAdjunction (Y := (D.geometricFiber Y₀).left)
    D l hl Ω (D.geometricFiber X₀).left (FrobeniusExchange.fiberMap D f₀) c A.system E


/-- The actual compact-support coefficient comparison, with inherited fiber instances.
Source: blueprint exceptional clause (blueprint: cor-coef-verdier-weil-equivariance). -/
def fiberLeftScalar (A : FiberExceptional D l hl Ω X₀ f₀ c) (E L : Index l Ω) (h : E ≤ L) :
    fiberLeft D l hl Ω X₀ f₀ c A E ⋙
      transition l Ω (D.geometricFiber Y₀).left E L h ≅
      transition l Ω (D.geometricFiber X₀).left E L h ⋙
    fiberLeft D l hl Ω X₀ f₀ c A L :=
  letI := fiberStructureLocallyFiniteType D X₀
  letI := fiberStructureQuasiCompact D X₀
  letI := fiberStructureSeparated D X₀
  letI := fiberStructureLocallyFiniteType D Y₀
  letI := fiberStructureQuasiCompact D Y₀
  letI := fiberStructureSeparated D Y₀
  letI := fiberMapSeparated D f₀
  letI := fiberMapLocallyFiniteType D f₀
  letI := fiberMapQuasiCompact D f₀
  CoefQbarVerdier.finiteLeftScalar (Y := (D.geometricFiber Y₀).left)
    D l hl Ω (D.geometricFiber X₀).left (FrobeniusExchange.fiberMap D f₀) c A.system E L h


/-- The actual exceptional coefficient comparison, with inherited fiber instances.
Source: blueprint exceptional clause (blueprint: cor-coef-verdier-weil-equivariance). -/
def fiberRightScalar (A : FiberExceptional D l hl Ω X₀ f₀ c) (E L : Index l Ω) (h : E ≤ L) :
    fiberRight D l hl Ω X₀ f₀ c A E ⋙
      transition l Ω (D.geometricFiber X₀).left E L h ≅
      transition l Ω (D.geometricFiber Y₀).left E L h ⋙
    fiberRight D l hl Ω X₀ f₀ c A L :=
  letI := fiberStructureLocallyFiniteType D X₀
  letI := fiberStructureQuasiCompact D X₀
  letI := fiberStructureSeparated D X₀
  letI := fiberStructureLocallyFiniteType D Y₀
  letI := fiberStructureQuasiCompact D Y₀
  letI := fiberStructureSeparated D Y₀
  letI := fiberMapSeparated D f₀
  letI := fiberMapLocallyFiniteType D f₀
  letI := fiberMapQuasiCompact D f₀
  CoefQbarVerdier.finiteRightScalar (Y := (D.geometricFiber Y₀).left)
    D l hl Ω (D.geometricFiber X₀).left (FrobeniusExchange.fiberMap D f₀) c A.system E L h


/-- The specified realization of the finite compact-support functor.
Source: blueprint proof steps 2--3 (blueprint: cor-coef-verdier-weil-equivariance). -/
def fiberLeftIdentification (A : FiberExceptional D l hl Ω X₀ f₀ c) (E : Index l Ω) :
    letI := fiberStructureLocallyFiniteType D X₀
    letI := fiberStructureQuasiCompact D X₀
    letI := fiberStructureSeparated D X₀
    letI := fiberStructureLocallyFiniteType D Y₀
    letI := fiberStructureQuasiCompact D Y₀
    letI := fiberStructureSeparated D Y₀
    letI := fiberMapSeparated D f₀
    letI := fiberMapLocallyFiniteType D f₀
    letI := fiberMapQuasiCompact D f₀
    fiberLeft D l hl Ω X₀ f₀ c A E ≅
      sfCompactSupportFiniteFunctor
        (X := (D.geometricFiber X₀).left) (Y := (D.geometricFiber Y₀).left)
        l D.k (PurCompactSupport.coefficientPrimeUnit l D hl) c (Coefficient.{u} l Ω E) :=
  letI := fiberStructureLocallyFiniteType D X₀
  letI := fiberStructureQuasiCompact D X₀
  letI := fiberStructureSeparated D X₀
  letI := fiberStructureLocallyFiniteType D Y₀
  letI := fiberStructureQuasiCompact D Y₀
  letI := fiberStructureSeparated D Y₀
  letI := fiberMapSeparated D f₀
  letI := fiberMapLocallyFiniteType D f₀
  letI := fiberMapQuasiCompact D f₀
  A.system.ring.rationalLeft c (CoefQbarVerdier.fieldStage l Ω E)

/-- The actual exceptional-duality identification, with inherited fiber instances.
Source: blueprint exceptional clause (blueprint: cor-coef-verdier-weil-equivariance). -/
def FiberExceptionalFormula (BX : FiberDuality D l hl Ω X₀)
    (BY : FiberDuality D l hl Ω Y₀) (A : FiberExceptional D l hl Ω X₀ f₀ c) :=
  letI := fiberStructureLocallyFiniteType D X₀
  letI := fiberStructureQuasiCompact D X₀
  letI := fiberStructureSeparated D X₀
  letI := fiberStructureLocallyFiniteType D Y₀
  letI := fiberStructureQuasiCompact D Y₀
  letI := fiberStructureSeparated D Y₀
  letI := fiberMapSeparated D f₀
  letI := fiberMapLocallyFiniteType D f₀
  letI := fiberMapQuasiCompact D f₀
  CoefQbarVerdier.ExceptionalFormula (Y := (D.geometricFiber Y₀).left)
    D l hl Ω (D.geometricFiber X₀).left (FrobeniusExchange.fiberMap D f₀) BX BY c A

/-- Cached common-stage projection of the unchanged exceptional datum.
Source: blueprint exceptional coefficient clause
(blueprint: def-coef-verdier-weil-data). -/
def fiberCommonLeft (A : FiberExceptional D l hl Ω X₀ f₀ c) :
    generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left :=
  letI := fiberStructureLocallyFiniteType D X₀
  letI := fiberStructureQuasiCompact D X₀
  letI := fiberStructureSeparated D X₀
  letI := fiberStructureLocallyFiniteType D Y₀
  letI := fiberStructureQuasiCompact D Y₀
  letI := fiberStructureSeparated D Y₀
  letI := fiberMapSeparated D f₀
  letI := fiberMapLocallyFiniteType D f₀
  letI := fiberMapQuasiCompact D f₀
  A.left

/-- Cached common-stage projection of the unchanged exceptional datum.
Source: blueprint exceptional coefficient clause
(blueprint: def-coef-verdier-weil-data). -/
def fiberCommonRight (A : FiberExceptional D l hl Ω X₀ f₀ c) :
    generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left :=
  letI := fiberStructureLocallyFiniteType D X₀
  letI := fiberStructureQuasiCompact D X₀
  letI := fiberStructureSeparated D X₀
  letI := fiberStructureLocallyFiniteType D Y₀
  letI := fiberStructureQuasiCompact D Y₀
  letI := fiberStructureSeparated D Y₀
  letI := fiberMapSeparated D f₀
  letI := fiberMapLocallyFiniteType D f₀
  letI := fiberMapQuasiCompact D f₀
  A.right

/-- Cached common-stage projection of the unchanged exceptional datum.
Source: blueprint exceptional coefficient clause
(blueprint: def-coef-verdier-weil-data). -/
def fiberCommonAdjunction (A : FiberExceptional D l hl Ω X₀ f₀ c) :
    fiberCommonLeft D l hl Ω X₀ f₀ c A ⊣ fiberCommonRight D l hl Ω X₀ f₀ c A :=
  letI := fiberStructureLocallyFiniteType D X₀
  letI := fiberStructureQuasiCompact D X₀
  letI := fiberStructureSeparated D X₀
  letI := fiberStructureLocallyFiniteType D Y₀
  letI := fiberStructureQuasiCompact D Y₀
  letI := fiberStructureSeparated D Y₀
  letI := fiberMapSeparated D f₀
  letI := fiberMapLocallyFiniteType D f₀
  letI := fiberMapQuasiCompact D f₀
  A.adjunction

/-- Cached common-stage projection of the unchanged exceptional datum.
Source: blueprint exceptional coefficient clause
(blueprint: def-coef-verdier-weil-data). -/
def fiberLeftComparison (A : FiberExceptional D l hl Ω X₀ f₀ c) (E : Index l Ω) :
    fiberLeft D l hl Ω X₀ f₀ c A E ⋙
      fiberInclusion D l Ω Y₀ E ≅ fiberInclusion D l Ω X₀ E ⋙ fiberCommonLeft D l hl Ω X₀ f₀ c A :=
  letI := fiberStructureLocallyFiniteType D X₀
  letI := fiberStructureQuasiCompact D X₀
  letI := fiberStructureSeparated D X₀
  letI := fiberStructureLocallyFiniteType D Y₀
  letI := fiberStructureQuasiCompact D Y₀
  letI := fiberStructureSeparated D Y₀
  letI := fiberMapSeparated D f₀
  letI := fiberMapLocallyFiniteType D f₀
  letI := fiberMapQuasiCompact D f₀
  A.leftComparison E

/-- Cached common-stage projection of the unchanged exceptional datum.
Source: blueprint exceptional coefficient clause
(blueprint: def-coef-verdier-weil-data). -/
def fiberRightComparison (A : FiberExceptional D l hl Ω X₀ f₀ c) (E : Index l Ω) :
    fiberRight D l hl Ω X₀ f₀ c A E ⋙ fiberInclusion D l Ω X₀ E ≅
      fiberInclusion D l Ω Y₀ E ⋙ fiberCommonRight D l hl Ω X₀ f₀ c A :=
  letI := fiberStructureLocallyFiniteType D X₀
  letI := fiberStructureQuasiCompact D X₀
  letI := fiberStructureSeparated D X₀
  letI := fiberStructureLocallyFiniteType D Y₀
  letI := fiberStructureQuasiCompact D Y₀
  letI := fiberStructureSeparated D Y₀
  letI := fiberMapSeparated D f₀
  letI := fiberMapLocallyFiniteType D f₀
  letI := fiberMapQuasiCompact D f₀
  A.rightComparison E

end ExceptionalGeometry


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section PinnedGeometry
variable {Y₀ : Over (Spec (.of D.k₀))} [LocallyOfFiniteType Y₀.hom]
    [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left]
    [QuasiCompact f₀.left] (c₀ : Compactification f₀.left)
    (A : FiberExceptional D l hl Ω X₀ f₀
      (FrobeniusExchange.geometricCompactification D f₀ c₀))

/-- The finite compact-support exchange type with cached endpoints.
Source: blueprint left exchange (blueprint: def-coef-verdier-weil-data). -/
def finiteLeftExchangeType (E : Index l Ω) :=
  fiberLeft D l hl Ω X₀ f₀
    (FrobeniusExchange.geometricCompactification D f₀ c₀) A E ⋙
      sfWeilFrobeniusPullback D l hl Y₀ (Coefficient.{u} l Ω E) ≅
    sfWeilFrobeniusPullback D l hl X₀ (Coefficient.{u} l Ω E) ⋙
      fiberLeft D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) A E

/-- The common compact-support exchange type with cached endpoints.
Source: blueprint left exchange (blueprint: def-coef-verdier-weil-data). -/
def commonLeftExchangeType :=
  fiberCommonLeft D l hl Ω X₀ f₀
    (FrobeniusExchange.geometricCompactification D f₀ c₀) A ⋙
      sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω ≅
    sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω ⋙
      fiberCommonLeft D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) A

/-- The finite exceptional lift type. Source: blueprint exceptional coefficient clause
(blueprint: def-coef-verdier-weil-data). -/
def finiteExceptionalType (E : Index l Ω) :=
    Exceptional (sfWeilFrobeniusPullback D l hl X₀ (Coefficient.{u} l Ω E))
      (sfWeilFrobeniusPullback D l hl Y₀ (Coefficient.{u} l Ω E))
      (fiberAdjunction D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) A E)

/-- The common exceptional lift type. Source: blueprint exceptional coefficient clause
(blueprint: def-coef-verdier-weil-data). -/
def commonExceptionalType :=
    Exceptional (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω)
    (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω) (fiberCommonAdjunction D l hl Ω X₀ f₀
      (FrobeniusExchange.geometricCompactification D f₀ c₀) A)

/-- The prescribed finite exceptional realization. Source: blueprint exceptional coefficient clause
(blueprint: def-coef-verdier-weil-data). -/
def finiteLeftExchangeLaw
    (finite : ∀ E, finiteLeftExchangeType D l hl Ω X₀ f₀ c₀ A E) : Prop :=
  ∀ (E : Index l Ω) (K : Stage l Ω (D.geometricFiber X₀).left E),
    HEq
      (realizedExchangeAt
        (fiberLeftIdentification D l hl Ω X₀ f₀
          (FrobeniusExchange.geometricCompactification D f₀ c₀) A E) (finite E) K)
      ((FrobeniusExchange.frobeniusRational D l hl (Coefficient.{u} l Ω E) f₀
        (FrobeniusExchange.frobeniusCompactModel D f₀ c₀)).app K)

/-- The prescribed common exceptional realization. Source: blueprint exceptional coefficient clause
(blueprint: def-coef-verdier-weil-data). -/
def commonLeftExchangeLaw
    (common : commonLeftExchangeType D l hl Ω X₀ f₀ c₀ A) : Prop :=
  ∀ (E : Index l Ω) (K : Stage l Ω (D.geometricFiber X₀).left E),
    HEq
      (realizedStageExchangeAt
        (fiberLeftIdentification D l hl Ω X₀ f₀
          (FrobeniusExchange.geometricCompactification D f₀ c₀) A E)
        (fiberLeftComparison D l hl Ω X₀ f₀
      (FrobeniusExchange.geometricCompactification D f₀ c₀) A E)
        (sfWeilStagePullbackIdentification D l hl X₀ Ω E)
        (sfWeilStagePullbackIdentification D l hl Y₀ Ω E)
        common K)
      ((FrobeniusExchange.frobeniusCommonStage D l hl f₀
        (FrobeniusExchange.frobeniusCompactModel D f₀ c₀) Ω).app ((inclusion E).obj K))

/-- The finite realization law on the left components of exceptional lifts.
Source: blueprint exceptional normalization (blueprint: def-coef-verdier-weil-data). -/
def finiteExceptionalLaw
    (finite : ∀ E, finiteExceptionalType D l hl Ω X₀ f₀ c₀ A E) : Prop :=
  finiteLeftExchangeLaw D l hl Ω X₀ f₀ c₀ A (fun E ↦ (finite E).left)

/-- The common realization law on the left component of an exceptional lift.
Source: blueprint exceptional normalization (blueprint: def-coef-verdier-weil-data). -/
def commonExceptionalLaw
    (common : commonExceptionalType D l hl Ω X₀ f₀ c₀ A) : Prop :=
  commonLeftExchangeLaw D l hl Ω X₀ f₀ c₀ A common.left

/-- The pinned exceptional adjunction family. Source: blueprint exceptional coefficient clause
(blueprint: def-coef-verdier-weil-data). -/
abbrev FrobeniusAdjunctions :=
  PinnedFrobeniusAdjunctions (finiteExceptionalType D l hl Ω X₀ f₀ c₀ A)
    (commonExceptionalType D l hl Ω X₀ f₀ c₀ A)
    (finiteExceptionalLaw D l hl Ω X₀ f₀ c₀ A)
    (commonExceptionalLaw D l hl Ω X₀ f₀ c₀ A)

end PinnedGeometry

/-- The finite coefficient square for two fixed exceptional lifts.
Source: blueprint coefficient descent (blueprint: def-coef-verdier-weil-data). -/
def scalarExceptionalComparison
    {Y₀ : Over (Spec (.of D.k₀))} [LocallyOfFiniteType Y₀.hom]
    [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left]
    [QuasiCompact f₀.left] (c₀ : Compactification f₀.left)
    (A : FiberExceptional D l hl Ω X₀ f₀
      (FrobeniusExchange.geometricCompactification D f₀ c₀))
    (E L : Index l Ω) (h : E ≤ L)
    (x : finiteExceptionalType D l hl Ω X₀ f₀ c₀ A E)
    (y : finiteExceptionalType D l hl Ω X₀ f₀ c₀ A L) : Prop :=
    @ExceptionalComparison
      (sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) (D.geometricFiber X₀).left)
      (sfRationalConstructibleCategory l (Coefficient.{u} l Ω L) (D.geometricFiber X₀).left)
      (sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) (D.geometricFiber Y₀).left)
      (sfRationalConstructibleCategory l (Coefficient.{u} l Ω L) (D.geometricFiber Y₀).left)
      _ _ _ _
      (sfWeilFrobeniusPullback D l hl X₀ (Coefficient.{u} l Ω E))
      (sfWeilFrobeniusPullback D l hl X₀ (Coefficient.{u} l Ω L))
      (sfWeilFrobeniusPullback D l hl Y₀ (Coefficient.{u} l Ω E))
      (sfWeilFrobeniusPullback D l hl Y₀ (Coefficient.{u} l Ω L))
      (fiberLeft D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) A E)
      (fiberRight D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) A E)
      (fiberLeft D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) A L)
      (fiberRight D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) A L)
      (fiberAdjunction D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) A E)
      (fiberAdjunction D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) A L)
      x y
      (transition l Ω _ E L h) (transition l Ω _ E L h)
      (scalarFrobenius D l hl Ω X₀ E L h) (scalarFrobenius D l hl Ω Y₀ E L h)
      (fiberLeftScalar D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) A E L h)
      (fiberRightScalar D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) A E L h)

/-- The inclusion square for two fixed exceptional lifts.
Source: blueprint coefficient descent (blueprint: def-coef-verdier-weil-data). -/
def stageExceptionalComparison
    {Y₀ : Over (Spec (.of D.k₀))} [LocallyOfFiniteType Y₀.hom]
    [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left]
    [QuasiCompact f₀.left] (c₀ : Compactification f₀.left)
    (A : FiberExceptional D l hl Ω X₀ f₀
      (FrobeniusExchange.geometricCompactification D f₀ c₀))
    {BX : FiberDuality D l hl Ω X₀} {BY : FiberDuality D l hl Ω Y₀}
    (WX : Coefficients D l hl Ω X₀ BX) (WY : Coefficients D l hl Ω Y₀ BY)
    (E : Index l Ω) (x : finiteExceptionalType D l hl Ω X₀ f₀ c₀ A E)
    (y : commonExceptionalType D l hl Ω X₀ f₀ c₀ A) : Prop :=
    @ExceptionalComparison
      (sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) (D.geometricFiber X₀).left)
      (generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left)
      (sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) (D.geometricFiber Y₀).left)
      (generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left)
      _ _ _ _
      (sfWeilFrobeniusPullback D l hl X₀ (Coefficient.{u} l Ω E))
      (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω)
      (sfWeilFrobeniusPullback D l hl Y₀ (Coefficient.{u} l Ω E))
      (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω)
      (fiberLeft D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) A E)
      (fiberRight D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) A E)
      (fiberCommonLeft D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) A)
      (fiberCommonRight D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) A)
      (fiberAdjunction D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) A E)
      (fiberCommonAdjunction D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) A)
      x y
      (fiberInclusion D l Ω X₀ E) (fiberInclusion D l Ω Y₀ E)
      (WX.stageFrobenius E) (WY.stageFrobenius E)
      (fiberLeftComparison D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) A E)
      (fiberRightComparison D l hl Ω X₀ f₀
      (FrobeniusExchange.geometricCompactification D f₀ c₀) A E)

/-- Scalar and inclusion equivariance for the pinned Frobenius adjunctions.
Source: blueprint proof steps 3 and 7
(blueprint: cor-coef-verdier-weil-equivariance). -/
abbrev Adjunctions
    {Y₀ : Over (Spec (.of D.k₀))} [LocallyOfFiniteType Y₀.hom]
    [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left]
    [QuasiCompact f₀.left] (c₀ : Compactification f₀.left)
    (A : FiberExceptional D l hl Ω X₀ f₀
      (FrobeniusExchange.geometricCompactification D f₀ c₀))
    {BX : FiberDuality D l hl Ω X₀} {BY : FiberDuality D l hl Ω Y₀}
    (WX : Coefficients D l hl Ω X₀ BX) (WY : Coefficients D l hl Ω Y₀ BY) :=
  CompatibleFrobeniusAdjunctions
    (FrobeniusAdjunctions D l hl Ω X₀ f₀ c₀ A)
    (fun Z ↦ ∀ E L h,
      scalarExceptionalComparison D l hl Ω X₀ f₀ c₀ A E L h (Z.finite E) (Z.finite L))
    (fun Z ↦ ∀ E,
      stageExceptionalComparison D l hl Ω X₀ f₀ c₀ A WX WY E (Z.finite E) Z.common)


/-- The finite-field point in the retained model category.
Source: blueprint proof step 3 (blueprint: cor-coef-verdier-weil-equivariance). -/
abbrev pointModel (D : FiniteFieldDatum.{u}) : Over (Spec (.of D.k₀)) :=
  Over.mk (𝟙 (Spec (.of D.k₀)))

/-- The finite-field point has the identity structure map and inherits its properties.
Source: blueprint proof step 3 (blueprint: cor-coef-verdier-weil-equivariance). -/
instance pointModelLocallyFiniteType : LocallyOfFiniteType (pointModel D).hom :=
  inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of D.k₀))))

/-- The finite-field point's identity structure map is quasi-compact.
Source: blueprint proof step 3 (blueprint: cor-coef-verdier-weil-equivariance). -/
instance pointModelQuasiCompact : QuasiCompact (pointModel D).hom :=
  inferInstanceAs (QuasiCompact (𝟙 (Spec (.of D.k₀))))

/-- The finite-field point's identity structure map is separated.
Source: blueprint proof step 3 (blueprint: cor-coef-verdier-weil-equivariance). -/
instance pointModelSeparated : IsSeparated (pointModel D).hom :=
  inferInstanceAs (IsSeparated (𝟙 (Spec (.of D.k₀))))

/-- The geometric fibre of the finite-field point has separated structure map.
Source: blueprint proof step 3 (blueprint: cor-coef-verdier-weil-equivariance). -/
abbrev pointFiberSeparated :
    IsSeparated ((D.geometricFiber (pointModel D)).left ↘ Spec (.of D.k)) :=
  fiberStructureSeparated D (pointModel D)

/-- The structure morphism before geometric base change.
Source: blueprint proof step 3 (blueprint: cor-coef-verdier-weil-equivariance). -/
abbrev structureModel : X₀ ⟶ pointModel D := Over.homMk X₀.hom

/-- The model structure map inherits separatedness from X₀.
Source: blueprint proof step 3 (blueprint: cor-coef-verdier-weil-equivariance). -/
instance structureModelSeparated : IsSeparated (structureModel D X₀).left :=
  inferInstanceAs (IsSeparated X₀.hom)

/-- The model structure map inherits local finite type from X₀.
Source: blueprint proof step 3 (blueprint: cor-coef-verdier-weil-equivariance). -/
instance structureModelLocallyFiniteType : LocallyOfFiniteType (structureModel D X₀).left :=
  inferInstanceAs (LocallyOfFiniteType X₀.hom)

/-- The model structure map inherits quasi-compactness from X₀.
Source: blueprint proof step 3 (blueprint: cor-coef-verdier-weil-equivariance). -/
instance structureModelQuasiCompact : QuasiCompact (structureModel D X₀).left :=
  inferInstanceAs (QuasiCompact X₀.hom)

/-- The completed constant rank-one object at a finite coefficient field.
Source: blueprint proof step 3 (blueprint: cor-coef-verdier-weil-equivariance). -/
def finiteUnit (E : Index l Ω) :=
  @pullbackTensorRationalUnit l _ (Coefficient.{u} l Ω E) _ _ _
    (D.geometricFiber X₀).left (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)

/-- The specified left unitor for the finite constant coefficient object.
Source: blueprint proof step 3 (blueprint: cor-coef-verdier-weil-equivariance). -/
def finiteUnitor (E : Index l Ω) :
    ∀ M : Stage l Ω (D.geometricFiber X₀).left E,
      (@rationalDerivedTensor l _ (Coefficient.{u} l Ω E) _ _ _
        (D.geometricFiber X₀).left (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)).obj
          (finiteUnit D l hl Ω X₀ E, M) ≅ M :=
  @pullbackTensorRationalLeftUnitor l _ (Coefficient.{u} l Ω E) _ _ _
    (D.geometricFiber X₀).left (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)

/-- The same constant coefficient object in the common-stage category.
Source: blueprint proof steps 3 and 8 (blueprint: cor-coef-verdier-weil-equivariance). -/
def commonUnit :=
  @pullbackTensorCommonUnit l _ Ω _ _ _ (D.geometricFiber X₀).left
    (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)

/-- The specified common-stage left unitor for that coefficient object.
Source: blueprint proof steps 3 and 8 (blueprint: cor-coef-verdier-weil-equivariance). -/
def commonUnitor :
    ∀ M : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left,
      (@commonStageDerivedTensor l _ Ω _ _ _ (D.geometricFiber X₀).left
        (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)).obj
          (commonUnit D l hl Ω X₀, M) ≅ M :=
  @pullbackTensorCommonLeftUnitor l _ Ω _ _ _ (D.geometricFiber X₀).left
    (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)

/-- Both dualizing Weil structures come from the canonical structure-morphism exchange,
its actual adjunction mate, and the constant object's unit-normalized identification.
Source: blueprint proof steps 3 and 8 (blueprint: cor-coef-verdier-weil-equivariance). -/
def DualizingNormalization (B : FiberDuality D l hl Ω X₀)
    (W : Coefficients D l hl Ω X₀ B) : Prop :=
  letI := fiberStructureLocallyFiniteType D X₀
  letI := fiberStructureQuasiCompact D X₀
  letI := fiberStructureSeparated D X₀
  letI := pointFiberSeparated D
  ∀ c₀ : Compactification (structureModel D X₀).left,
    ∃ A : FiberExceptional D l hl Ω X₀ (structureModel D X₀)
        (FrobeniusExchange.geometricCompactification D (structureModel D X₀) c₀),
    ∃ Z : FrobeniusAdjunctions D l hl Ω X₀ (structureModel D X₀) c₀ A,
    (∀ E : Index l Ω,
      (DualizingMate
        (sfWeilFrobeniusPullback D l hl X₀ (Coefficient.{u} l Ω E))
        (sfWeilFrobeniusPullback D l hl (pointModel D) (Coefficient.{u} l Ω E))
        (fiberRight D l hl Ω X₀ (structureModel D X₀)
          (FrobeniusExchange.geometricCompactification D (structureModel D X₀) c₀) A E)
        (Z.finite E).right
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) _).obj
          (B.finite.omega E).omega) (W.finite E).omegaStructure
        (finiteUnit D l hl Ω (pointModel D) E)
        (@rationalDerivedTensor l _ (Coefficient.{u} l Ω E) _ _ _
          (D.geometricFiber (pointModel D)).left
          (fun x ↦ sfWeilPrimeInvertible D l hl (pointModel D) x))
        (finiteMu D l hl Ω (pointModel D) E) (finiteUnitor D l hl Ω (pointModel D) E))) ∧
    (DualizingMate (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω)
      (sfCommonStageWeilFrobeniusPullback D l hl (pointModel D) Ω)
      (fiberCommonRight D l hl Ω X₀ (structureModel D X₀)
      (FrobeniusExchange.geometricCompactification D (structureModel D X₀) c₀) A)
      Z.common.right B.omega W.common.omegaStructure
      (commonUnit D l hl Ω (pointModel D))
      (@commonStageDerivedTensor l _ Ω _ _ _ (D.geometricFiber (pointModel D)).left
        (fun x ↦ sfWeilPrimeInvertible D l hl (pointModel D) x))
      (commonMu D l hl Ω (pointModel D)) (commonUnitor D l hl Ω (pointModel D)))


/-- Every geometric fiber has the asserted duality, and every descended morphism
has the asserted exceptional adjunction, simultaneously at finite coefficients and Ω.
The underlying maps are fixed by the published duality, internal-Hom, dualizing,
scalar-extension and exceptional-formula interfaces.
Source: blueprint cor-coef-verdier-weil-equivariance, all clauses
(blueprint: cor-coef-verdier-weil-equivariance). -/
def Conclusion : Prop :=
  ∃ (BX : FiberDuality D l hl Ω X₀),
    Nonempty (FiberInternalHom D l hl Ω X₀ BX) ∧
    FiberDualizing D l hl Ω X₀ BX ∧
    ∃ WX : Coefficients D l hl Ω X₀ BX,
    DualizingNormalization D l hl Ω X₀ BX WX ∧
    ∀ (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom]
      [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
      (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left]
      [QuasiCompact f₀.left],
      ∀ (c₀ : Compactification f₀.left),
      ∃ (BY : FiberDuality D l hl Ω Y₀)
        (A : FiberExceptional D l hl Ω X₀ f₀
          (FrobeniusExchange.geometricCompactification D f₀ c₀)),
        Nonempty (FiberInternalHom D l hl Ω Y₀ BY) ∧
        FiberDualizing D l hl Ω Y₀ BY ∧
        Nonempty (FiberExceptionalFormula D l hl Ω X₀ f₀
          (FrobeniusExchange.geometricCompactification D f₀ c₀) BX BY A) ∧
        ∃ WY : Coefficients D l hl Ω Y₀ BY,
          DualizingNormalization D l hl Ω Y₀ BY WY ∧
          Nonempty (Adjunctions D l hl Ω X₀ f₀ c₀ A WX WY)

end Geometric
end WeilConjectures.CoefVerdierWeil
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed when rechecked | Same mathematical interface; compiled unchanged. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed when rechecked | Same mathematical interface; compiled unchanged. |
| Sheaf.Paper.WeilChosenDualityExchangeData | unclaimed when rechecked | Same mathematical interface; compiled unchanged. |
| Sheaf.Paper.WeilChosenExchangeConstruction | unclaimed when rechecked | Same mathematical interface; compiled unchanged. |
| Sheaf.Paper.WeilChosenTransposeNaturality | unclaimed when rechecked | Same mathematical interface; compiled unchanged. |
| Sheaf.SixFunctors.WeilChosenDualityHom | unclaimed when rechecked | Same mathematical interface; compiled unchanged. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | V3 | Proof now assembles the component results. |

The wrappers were checked with `tools/downstream.py --uses`. The six current
downstream modules are listed above; direct record users are the exceptional
coherence realization, chosen exchange data, and chosen duality Hom modules.
The exchange, exchange construction and transpose naturality modules inherit that
interface. The former concrete record types now specialize generic containers;
projection notation retains the same fields, while generated constructor namespaces
change. No current consumer uses those constructor namespaces. No consumer
adaptation is proposed. The predicate owner
`def-pod-verdier-weil-conclusion` is updated to the new defining module. Targets that
use Conclusion retain exactly its meaning. Targets using these definitions
nevertheless reopen the statement review under AGENTS.md §4; the reader should
verify the explicit result types, generic-container specializations and
reducibility changes against the original definitions.

## Status

landed 20261026T003041-L-142554 2026-10-26 (merge of deliver/V3/Sheaf.SixFunctors.CoefVerdierWeilEquivariance)
