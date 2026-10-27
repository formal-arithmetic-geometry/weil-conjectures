# WeilConjectures.ZlFrontier auxiliary frontier restriction data

## Reason

The original assembly theorem contains the interfaces its separate argument steps need.
Move those interfaces verbatim to a data module and publicly reexport that module, so
new proof modules can import the data without forming a cycle. This is an argument
decomposition, not a change to any mathematical statement or definition. Existing
signatures, field order, attributes, names, universes and definition bodies are preserved.
The extraction is for proof dependency direction, not a workaround for a compile timeout.

## Old

The following declarations were in Sheaf.Paper.ClassicalLisseWeilFrontierRestriction:

```lean
/-- A locally closed finite-field model and its actual geometric factorization.
No Frobenius stability of the original stratum is required.
Source: blueprint real-mixed-by-curves, paragraphs 6--7
(blueprint: lem-zl-classical-lisse-weil-frontier-restriction). -/
structure RestrictionModel (R : Realization D l Ω)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom]
    [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (T : PerAdic.Base D.k) (M : sfCommonStageHeart l T.scheme Ω)
    (P : PartitionData D l Ω R T M) (m : ℕ) (hm : 1 ≤ m) where
  scheme : Over (Spec (.of (D.extensionSubfield m hm)))
  [finiteType : LocallyOfFiniteType scheme.hom]
  [quasiCompact : QuasiCompact scheme.hom]
  [separated : IsSeparated scheme.hom]
  inclusion : scheme ⟶ constantExtensionModel D m hm Y₀
  immersion : IsImmersion inclusion.left
  stratum : Fin P.partition.n
  factor : (@FiniteFieldDatum.geometricFiber (constantExtensionDatum D m hm)
    scheme finiteType quasiCompact).left ⟶
    (stratumBase D T P.partition stratum).scheme
  factor_immersion : IsImmersion factor
  intoSupport : (@FiniteFieldDatum.geometricFiber (constantExtensionDatum D m hm)
    scheme finiteType quasiCompact).left ⟶ T.scheme
  factorization : factor ≫ P.partition.immersion stratum = intoSupport

attribute [instance] RestrictionModel.finiteType RestrictionModel.quasiCompact
  RestrictionModel.separated

/-- Canonical geometric inclusion, with the prescribed associativity of base change.
Source: blueprint real-mixed-by-curves, paragraph 7
(blueprint: lem-zl-classical-lisse-weil-frontier-restriction). -/
def RestrictionModel.geometricMap {R : Realization D l Ω}
    {Y₀ : Over (Spec (.of D.k₀))} [LocallyOfFiniteType Y₀.hom]
    [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    {T : PerAdic.Base D.k} {M : sfCommonStageHeart l T.scheme Ω}
    {P : PartitionData D l Ω R T M} {m : ℕ} {hm : 1 ≤ m}
    (V : RestrictionModel D l Ω R Y₀ T M P m hm) :=
  (zlFiberMap (constantExtensionDatum D m hm) V.inclusion) ≫
    (constantExtensionFiberIso D m hm Y₀).hom

/-- The geometric base with its inherited finiteness structures made explicit.
Source: blueprint finite-field convention
(blueprint: lem-zl-classical-lisse-weil-frontier-restriction). -/
def RestrictionModel.base {R : Realization D l Ω}
    {Y₀ : Over (Spec (.of D.k₀))} [LocallyOfFiniteType Y₀.hom]
    [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    {T : PerAdic.Base D.k} {M : sfCommonStageHeart l T.scheme Ω}
    {P : PartitionData D l Ω R T M} {m : ℕ} {hm : 1 ≤ m}
    (V : RestrictionModel D l Ω R Y₀ T M P m hm) : PerAdic.Base D.k :=
  @fiberBase (constantExtensionDatum D m hm) V.scheme
    V.finiteType V.quasiCompact V.separated

/-- Geometric Frobenius over the finite model, with explicit inherited structures.
Source: blueprint paragraph 7
(blueprint: lem-zl-classical-lisse-weil-frontier-restriction). -/
def RestrictionModel.frobenius {R : Realization D l Ω}
    {Y₀ : Over (Spec (.of D.k₀))} [LocallyOfFiniteType Y₀.hom]
    [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    {T : PerAdic.Base D.k} {M : sfCommonStageHeart l T.scheme Ω}
    {P : PartitionData D l Ω R T M} {m : ℕ} {hm : 1 ≤ m}
    (V : RestrictionModel D l Ω R Y₀ T M P m hm) :
    (V.base D l Ω).scheme ≅ (V.base D l Ω).scheme :=
  @FiniteFieldDatum.geometricFrobenius (constantExtensionDatum D m hm) V.scheme
    V.finiteType V.quasiCompact

/-- The restricted chosen lattice, with its quotient-normalized finite-level pullback.
Source: BS 6.8.4(1)
(blueprint: lem-zl-classical-lisse-weil-frontier-restriction). -/
def RestrictionModel.lattice {R : Realization D l Ω}
    {Y₀ : Over (Spec (.of D.k₀))} [LocallyOfFiniteType Y₀.hom]
    [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    {T : PerAdic.Base D.k} {M : sfCommonStageHeart l T.scheme Ω}
    {P : PartitionData D l Ω R T M} {m : ℕ} {hm : 1 ≤ m}
    (V : RestrictionModel D l Ω R Y₀ T M P m hm)
    [LocallyOfFiniteType V.scheme.hom] [QuasiCompact V.scheme.hom]
    [IsSeparated V.scheme.hom]
    (S : ProEtale.CompletedLisse.System.{u} l) :=
  (restriction D l Ω S
    (X := V.base D l Ω)
    (Y := stratumBase D T P.partition V.stratum) V.factor P.field).obj (P.lattice V.stratum)

/-- Its normalized realization identification, for the actual factorized inclusion.
Source: blueprint real-mixed-by-curves, paragraph 7
(blueprint: lem-zl-classical-lisse-weil-frontier-restriction). -/
def RestrictionModel.identification {R : Realization D l Ω}
    {S : ProEtale.CompletedLisse.System.{u} l}
    {A : LisseRealization.Family D l (Fact.out : l ≠ D.p)}
    (C : RestrictionComparison D l Ω R S A)
    {Y₀ : Over (Spec (.of D.k₀))} [LocallyOfFiniteType Y₀.hom]
    [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    {T : PerAdic.Base D.k} {M : sfCommonStageHeart l T.scheme Ω}
    {P : PartitionData D l Ω R T M} {m : ℕ} {hm : 1 ≤ m}
    (V : RestrictionModel D l Ω R Y₀ T M P m hm)
    [LocallyOfFiniteType V.scheme.hom] [QuasiCompact V.scheme.hom]
    [IsSeparated V.scheme.hom] :
    (R.functor D l Ω (V.base D l Ω)).obj
      ((model D l Ω (V.base D l Ω) P.field).obj
        (V.lattice D l Ω S)) ≅
    (pull D l Ω (X := V.base D l Ω) (Y := T)
      V.intoSupport).obj M.obj :=
  restrictIdentification D l Ω C
    (X := V.base D l Ω) (Y := stratumBase D T P.partition V.stratum) (Z := T) V.factor
    (P.partition.immersion V.stratum)
    P.field (P.lattice V.stratum) M (P.identification D l Ω V.stratum) ≪≫
      eqToIso (congrArg (fun f ↦ (pull D l Ω f).obj M.obj) V.factorization)

/-- The lifted classical fixed pair has exactly the chosen restricted carrier.
Source: Weil II (1.1.1), blueprint paragraph 7
(blueprint: lem-zl-classical-lisse-weil-frontier-restriction). -/
def WeilLift.classicalWeil {R : Realization D l Ω}
    {S : ProEtale.CompletedLisse.System.{u} l}
    {A : LisseRealization.Family D l (Fact.out : l ≠ D.p)}
    {C : RestrictionComparison D l Ω R S A}
    {X : PerAdic.Base D.k} {g : X.scheme ≅ X.scheme}
    {E : Padic.FiniteCoefficientFields l Ω}
    {F : ProEtale.CompletedLisse.RawRational l (completedBase D l Ω X E)}
    {N : generalAlgebraicallyClosedConstructibleCategory l Ω X.scheme}
    {ρ : (R.functor D l Ω X).obj ((model D l Ω X E).obj F) ≅ N}
    {α : (pull D l Ω g.hom).obj N ≅ N}
    (L : WeilLift D l Ω R S A C X g E F N ρ α) : EtaleLisseWeilSheaf l Ω g :=
  CategoryTheory.Endofunctor.IsoAlgebra.mk ((model D l Ω X E).obj F) L.classical

/-- The canonical restriction realizes the actual ambient theta^[m], not a separately
chosen descent map. All positive local geometric-Frobenius iterates are compared on
one finite model by the recorded completed-section and classical adic fibre interface.
Source: blueprint real-mixed-by-curves, paragraph 7; BS 6.8.4(4), 6.8.14(2), 6.8.15
(blueprint: lem-zl-classical-lisse-weil-frontier-restriction). -/
structure WeilRestrictionResult (R : Realization D l Ω)
    (S : ProEtale.CompletedLisse.System.{u} l)
    (A : LisseRealization.Family D l (Fact.out : l ≠ D.p))
    (C : RestrictionComparison D l Ω R S A)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom]
    [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (M : sfCommonStageHeart l (fiberBase D Y₀).scheme Ω)
    (P : PartitionData D l Ω R (fiberBase D Y₀) M)
    (K : sfCommonStageWeilComplex D l (Fact.out : l ≠ D.p) Y₀ Ω)
    (hK : K.carrier = M.obj) (m : ℕ) (hm : 1 ≤ m)
    (V : RestrictionModel D l Ω R Y₀ (fiberBase D Y₀) M P m hm)
    (hj : V.intoSupport = V.geometricMap D l Ω)
    [LocallyOfFiniteType V.scheme.hom] [QuasiCompact V.scheme.hom]
    [IsSeparated V.scheme.hom] where
  square : V.intoSupport ≫ localPositivePower (D.geometricFrobenius Y₀).hom (m - 1) =
    (V.frobenius D l Ω).hom ≫ V.intoSupport
  lift : WeilLift D l Ω R S A C
    (V.base D l Ω)
    (V.frobenius D l Ω)
    P.field (V.lattice D l Ω S)
    ((pull D l Ω (X := V.base D l Ω) (Y := fiberBase D Y₀) V.intoSupport).obj M.obj)
    (V.identification D l Ω C)
    (ambientRestriction D l Ω (X := V.base D l Ω) (Y := fiberBase D Y₀)
      V.intoSupport
      (localPositivePower (D.geometricFrobenius Y₀).hom (m - 1))
      (V.frobenius D l Ω).hom square M.obj
      (eqToIso (congrArg (pull D l Ω (X := fiberBase D Y₀) (Y := fiberBase D Y₀)
        (localPositivePower (D.geometricFrobenius Y₀).hom (m - 1))).obj hK.symm) ≪≫
        constantExtensionWeilIterate D l (Fact.out : l ≠ D.p) Ω Y₀ K (m - 1) ≪≫
          eqToIso hK))
  pointField : Padic.FiniteCoefficientFields l Ω
  contains : lift.finite.field ≤ pointField
  pointModel : @sfWeilComplex (constantExtensionDatum D m hm) l _
    (Fact.out : l ≠ D.p) V.scheme V.finiteType V.quasiCompact
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω pointField) _ _ _
  realizedPointModel : @sfWeilStageObject (constantExtensionDatum D m hm) l _
    (Fact.out : l ≠ D.p) V.scheme V.finiteType V.quasiCompact
    Ω _ _ _ pointField pointModel ≅
      CategoryTheory.Endofunctor.IsoAlgebra.mk
        ((pull D l Ω (X := V.base D l Ω) (Y := fiberBase D Y₀) V.intoSupport).obj M.obj)
        (
        ambientRestriction D l Ω (X := V.base D l Ω) (Y := fiberBase D Y₀)
      V.intoSupport
          (localPositivePower (D.geometricFrobenius Y₀).hom (m - 1))
          (V.frobenius D l Ω).hom square M.obj
          (eqToIso (congrArg (pull D l Ω (X := fiberBase D Y₀) (Y := fiberBase D Y₀)
            (localPositivePower (D.geometricFrobenius Y₀).hom (m - 1))).obj hK.symm) ≪≫
            constantExtensionWeilIterate D l (Fact.out : l ≠ D.p) Ω Y₀ K (m - 1) ≪≫
              eqToIso hK))
  finitePoints : @ZlClassicalFibreComparison (constantExtensionDatum D m hm) l _
    (Fact.out : l ≠ D.p) Ω _ _ _ V.scheme V.finiteType V.quasiCompact V.separated
    (stalkUnits D l (V.base D l Ω)) pointField pointModel (lift.classicalWeil D l Ω)
  /-- Pin the comparison that carries the actual sf localFrobeniusCohomology
  operators, rather than imposing an equation on a transported classical operator. -/
  points :
    letI := V.finiteType
    letI := V.quasiCompact
    letI := V.separated
    let Q := @sfWeilStageObject (constantExtensionDatum D m hm) l _
      (Fact.out : l ≠ D.p) V.scheme V.finiteType V.quasiCompact
      Ω _ _ _ pointField pointModel
    let ρ := V.identification D l Ω C ≪≫
      (CategoryTheory.Endofunctor.IsoAlgebra.forget _).mapIso realizedPointModel.symm
    ∀ x : Spec (.of D.k) ⟶ (V.base D l Ω).scheme,
      @ZlClassicalFibreComparison.fibre (constantExtensionDatum D m hm) l _
        (Fact.out : l ≠ D.p) Ω _ _ _ V.scheme V.finiteType V.quasiCompact V.separated
        (stalkUnits D l (V.base D l Ω)) pointField pointModel
        (lift.classicalWeil D l Ω) finitePoints x =
        finiteRealizationFibreIso D l Ω R (V.base D l Ω) pointField pointModel.carrier x ≪≫
          R.identifiedFiber D l Ω (V.base D l Ω) D.k x
            ((model D l Ω (V.base D l Ω) P.field).obj (V.lattice D l Ω S)) Q.carrier ρ

/-- The actual immersion of the support into the geometric fibre.
Source: blueprint reduction convention
(blueprint: lem-zl-classical-lisse-weil-frontier-restriction). -/
def supportInclusion (Y : PerAdic.Base D.k) (reduced : Bool) :
    (supportBase D Y reduced).scheme ⟶ Y.scheme :=
  if h : reduced = true then
    eqToHom (congrArg (fun b ↦ (supportBase D Y b).scheme) h) ≫ Y.scheme.nilradical.subschemeι
  else
    eqToHom (congrArg (fun b ↦ (supportBase D Y b).scheme) (Bool.eq_false_iff.mpr h))

/-- The complete frontier diagram over one finite extension. The start and finish are
isomorphisms over the field, allowing the empty scheme to have a length-zero chain.
All pieces are genuine locally closed restrictions of the original partition.
Source: Stacks 0B8X, 06LH, 01ZM; blueprint real-mixed-by-curves, paragraphs 6--7
(blueprint: lem-zl-classical-lisse-weil-frontier-restriction). -/
structure Frontier (R : Realization D l Ω)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom]
    [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (T : PerAdic.Base D.k) (M : sfCommonStageHeart l T.scheme Ω)
    (P : PartitionData D l Ω R T M)
    (iT : T.scheme ⟶ (fiberBase D Y₀).scheme) where
  degree : ℕ
  positive : 1 ≤ degree
  length : ℕ
  closed : Fin (length + 1) → Over (Spec (.of (D.extensionSubfield degree positive)))
  reduced : ∀ a, IsReduced (closed a).left
  start : closed 0 ≅ Over.mk
    ((constantExtensionModel D degree positive Y₀).left.nilradical.subschemeι ≫
      (constantExtensionModel D degree positive Y₀).hom)
  finish : closed (Fin.last length) ≅ Over.mk
    (Scheme.emptyTo (Spec (.of (D.extensionSubfield degree positive))))
  empty_length : IsEmpty Y₀.left → length = 0
  inclusion : ∀ a : Fin length, closed a.succ ⟶ closed a.castSucc
  inclusion_closed : ∀ a, IsClosedImmersion (inclusion a).left
  ambient : ∀ a, closed a ⟶ constantExtensionModel D degree positive Y₀
  start_ambient : (ambient 0).left = start.hom.left ≫
    (constantExtensionModel D degree positive Y₀).left.nilradical.subschemeι
  ambient_composition : ∀ a, ambient a.succ = inclusion a ≫ ambient a.castSucc
  difference : Fin length → Over (Spec (.of (D.extensionSubfield degree positive)))
  difference_inclusion : ∀ a, difference a ⟶ closed a.castSucc
  difference_open : ∀ a, IsOpenImmersion (difference_inclusion a).left
  difference_range : ∀ a, Set.range (difference_inclusion a).left =
    (Set.range (inclusion a).left)ᶜ
  count : Fin length → ℕ
  piece : ∀ a, Fin (count a) → RestrictionModel D l Ω R Y₀ T M P degree positive
  piece_into_difference : ∀ a b, (piece a b).scheme ⟶ difference a
  piece_ambient : ∀ a b, (piece a b).inclusion =
    piece_into_difference a b ≫ difference_inclusion a ≫ ambient a.castSucc
  geometric_piece : ∀ a b, (piece a b).intoSupport ≫ iT =
    (piece a b).geometricMap D l Ω
  nonempty : ∀ a b, Nonempty (piece a b).scheme.left
  affine : ∀ a b, IsAffine (piece a b).scheme.left
  smooth_dimension : ∀ (a : Fin length) (_b : Fin (count a)), ℕ
  smooth : ∀ a b, SmoothOfRelativeDimension (smooth_dimension a b) (piece a b).scheme.hom
  connected : ∀ a b, GeometricallyConnected (piece a b).scheme.hom
  clopen : ∀ a b, IsOpenImmersion (piece_into_difference a b).left ∧
    IsClosedImmersion (piece_into_difference a b).left
  cover : ∀ a, ⋃ b : Fin (count a), Set.range (piece_into_difference a b).left = Set.univ
  disjoint : ∀ a (b c : Fin (count a)), b ≠ c →
    Disjoint (Set.range (piece_into_difference a b).left)
      (Set.range (piece_into_difference a c).left)
  zero_dimension : ∀ a b, smooth_dimension a b = 0 →
    Nonempty ((piece a b).scheme ≅ Over.mk (𝟙 _))

/-- Preservation includes successive locally closed restrictions, with the actual
completed raw compositor and the actual common-stage derived compositor.
Source: BS 6.8.4(1),(4), 6.8.15; blueprint paragraph 7
(blueprint: lem-zl-classical-lisse-weil-frontier-restriction). -/
def SuccessiveRestrictions (R : Realization D l Ω)
    (S : ProEtale.CompletedLisse.System.{u} l)
    (A : LisseRealization.Family D l (Fact.out : l ≠ D.p))
    (C : RestrictionComparison D l Ω R S A)
    (T : PerAdic.Base D.k) (M : sfCommonStageHeart l T.scheme Ω)
    (P : PartitionData D l Ω R T M) : Prop :=
  ∀ (ν : Fin P.partition.n) (W W' : PerAdic.Base D.k)
    (h : W.scheme ⟶ (stratumBase D T P.partition ν).scheme) [IsImmersion h]
    (a : W'.scheme ⟶ W.scheme) [IsImmersion a],
    C.iso D l Ω (X := W') (Y := stratumBase D T P.partition ν)
      (a ≫ h) P.field (P.lattice ν) =
    (R.functor D l Ω W').mapIso
      ((model D l Ω W' P.field).mapIso
        (restrictionComposite D l Ω S h a P.field (P.lattice ν)).symm) ≪≫
      C.iso D l Ω (X := W') (Y := W) a P.field
        ((restriction D l Ω S h P.field).obj (P.lattice ν)) ≪≫
      (pull D l Ω (X := W') (Y := W) a).mapIso
        (C.iso D l Ω (X := W) (Y := stratumBase D T P.partition ν)
          h P.field (P.lattice ν)) ≪≫
      ((zlPullComp l Ω a h).app
        ((R.functor D l Ω (stratumBase D T P.partition ν)).obj
          ((model D l Ω (stratumBase D T P.partition ν) P.field).obj
            (P.lattice ν)))).symm

/-- The two conclusions are uniform in the supplied normalized realization and partition.
Source: blueprint real-mixed-by-curves, paragraphs 6--7
(blueprint: lem-zl-classical-lisse-weil-frontier-restriction). -/
def RestrictionConclusion (R : Realization D l Ω)
    (S : ProEtale.CompletedLisse.System.{u} l)
    (A : LisseRealization.Family D l (Fact.out : l ≠ D.p))
    (C : RestrictionComparison D l Ω R S A)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom]
    [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom] : Prop :=
  (∀ (M : sfCommonStageHeart l (fiberBase D Y₀).scheme Ω)
    (P : PartitionData D l Ω R (fiberBase D Y₀) M)
    (K : sfCommonStageWeilComplex D l (Fact.out : l ≠ D.p) Y₀ Ω)
    (hK : K.carrier = M.obj) (m : ℕ) (hm : 1 ≤ m)
    (V : RestrictionModel D l Ω R Y₀ (fiberBase D Y₀) M P m hm)
    (hj : V.intoSupport = V.geometricMap D l Ω),
    Nonempty (WeilRestrictionResult D l Ω R S A C Y₀ M P K hK m hm V hj)) ∧
  (∀ (reduced : Bool)
    (M : sfCommonStageHeart l (supportBase D (fiberBase D Y₀) reduced).scheme Ω)
    (P : PartitionData D l Ω R (supportBase D (fiberBase D Y₀) reduced) M),
    SuccessiveRestrictions D l Ω R S A C
      (supportBase D (fiberBase D Y₀) reduced) M P ∧
    ∃ H : Frontier D l Ω R Y₀ (supportBase D (fiberBase D Y₀) reduced) M P
      (supportInclusion D (fiberBase D Y₀) reduced),
      ∀ (a : Fin H.length) (b : Fin (H.count a)),
      Nonempty ((R.functor D l Ω ((H.piece a b).base D l Ω)).obj
        ((model D l Ω ((H.piece a b).base D l Ω) P.field).obj
          ((H.piece a b).lattice D l Ω S)) ≅
        (pull D l Ω (X := (H.piece a b).base D l Ω)
          (Y := supportBase D (fiberBase D Y₀) reduced)
          (H.piece a b).intoSupport).obj M.obj)) ∧
  (∀ (M : sfCommonStageHeart l (fiberBase D Y₀).scheme Ω)
    (P : PartitionData D l Ω R (fiberBase D Y₀) M),
    ∃ H : Frontier D l Ω R Y₀ (fiberBase D Y₀) M P (𝟙 _),
      ∀ (K : sfCommonStageWeilComplex D l (Fact.out : l ≠ D.p) Y₀ Ω)
        (hK : K.carrier = M.obj) (a : Fin H.length) (b : Fin (H.count a)),
      Nonempty (WeilRestrictionResult D l Ω R S A C Y₀ M P K hK
        H.degree H.positive (H.piece a b)
        ((Category.comp_id (H.piece a b).intoSupport).symm.trans (H.geometric_piece a b))))

```

The original module publicly imported ClassicalLisseWeilRestrictionMaps and
NormalizedFiniteRealizationFibre directly.

## New

The exact declarations above now live in Sheaf.Paper.ClassicalLisseWeilFrontierData.
That module has the identical two public imports. The original module publicly imports
ClassicalLisseWeilFrontierData, preserving every old reexport, and privately imports the
three new argument modules ClassicalWeilRestrictionExistence, ClassicalFrontierExistence,
and ClassicalSuccessiveRestrictions. Its theorem signature is unchanged. Definitions
used by targets retain their exact mathematical content; normal independent statement
review applies to the relocation.

## Users

`python3 tools/downstream.py Sheaf.Paper.ClassicalLisseWeilFrontierRestriction --uses
RestrictionModel WeilRestrictionResult RestrictionConclusion` reports zero downstream
modules at the delivery base. Textual uses occur only in the item itself. No quarantined
source is withdrawn, and all DAG parent attachments remain usable through its reexport.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ClassicalLisseWeilFrontierRestriction | G4 | Same theorem signature and reexported data; proof assembled from proper steps. |
| Sheaf.Paper.ClassicalLisseWeilFrontierData | new | Owns unchanged interfaces and definitions. |
| Sheaf.Paper.ClassicalWeilRestrictionExistence | new | One-model Weil lift and point-compatibility step. |
| Sheaf.Paper.ClassicalFrontierExistence | new | Geometric frontier step, independent of Weil structures. |
| Sheaf.Paper.ClassicalSuccessiveRestrictions | new | Restriction-composition step, independent of frontier geometry. |

## Status

landed 20261025T123002-L-1822144 2026-10-25 (merge of deliver/G4/Sheaf.Paper.ClassicalLisseWeilFrontierRestriction)
