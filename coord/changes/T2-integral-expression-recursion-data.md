# WeilConjectures.IntegralSystemRealization.ExpressionRecursion

## Reason

Restore the quarantined item and separate its specification data from the assembly
proof so independently provable component theorems can import those definitions
without creating an import cycle. This is a relocation of existing declarations,
not a mathematical change to a definition or a statement. All 19 existing data
and specification declarations keep their names, universes, signatures, visibility,
attributes and bodies verbatim. The original module keeps its two original public
imports and publicly reexports the new data module. No source-library module changes.
The target statements and all definitions occurring in them retain their meanings.

The new coefficientTransformation is built by whiskering and composing the given
primitive transformations, including a product of the two child transformations
at tensor. transposeComparison is the explicit adjunction transpose. Their new
irreducible attributes prevent elaboration from repeatedly unfolding a large tree;
coefficientTransformation_app and transposeComparison_coefficient form the API.
These attributes are on new definitions only.

## Old

The following declarations were in `Sheaf.SixFunctors.IntegralExpressionRecursion`:

```lean
/-- A single unary constructor, with precisely the permitted arrow hypotheses.
Source: fix-prop-coherence, expression-tree refinement
(blueprint: lem-sf-integral-expression-recursion). -/
inductive Unary (B : Scheme.{u}) : Over B → Over B → Type (u + 1) where
  | pull {U V : Over B} (f : U ⟶ V) (hs : IsSeparated f.left)
      (hft : LocallyOfFiniteType f.left) (hqc : QuasiCompact f.left) : Unary B V U
  | push {U V : Over B} (p : U ⟶ V) (hp : IsProper p.left) : Unary B U V
  | shriek {U V : Over B} (j : U ⟶ V) (hj : IsOpenImmersion j.left)
      (hqc : QuasiCompact j.left) : Unary B U V

/-- The actual system functor of a unary constructor.
Source: fix-prop-coherence (blueprint: lem-sf-integral-expression-recursion). -/
def Unary.system (o : Operations l E) {B : Scheme.{u}} {U V : Over B} :
    Unary B U V → System l E U.left ⥤ System l E V.left
  | .pull f _ _ _ => IntegralSystemRealization.pull l E f.left
  | .push p _ => Operations.push l E o p.left
  | .shriek j hj _ =>
    letI := hj
    Operations.shriek l E o j.left

/-- The prescribed completed/integral interpretation of the same constructor.
Source: fix-prop-coherence (blueprint: lem-sf-integral-expression-recursion). -/
def Unary.integral {B : Scheme.{u}} {U V : Over B} :
    Unary B U V → Integral l E U.left ⥤ Integral l E V.left
  | .pull f _ _ _ => integralDerivedPullback l E f.left
  | .push p _ => ringedPush l E p.left
  | .shriek j hj _ =>
    letI := hj
    ringedOpen l E j.left

/-- The prescribed primitive realization map before restricting its domain.
The actual inverse is used on the complete domain; its ambient value is irrelevant.
Source: fix-prop-coherence, primitive comparison refinement
(blueprint: lem-sf-integral-expression-recursion). -/
def Unary.primitiveHom (o : Operations l E) (model : RealizationModel l E o)
    {B : Scheme.{u}} {U V : Over B} (a : Unary B U V) (K : Integral l E U.left) :
    (coefficientSequenceLimit l E V.left).obj
      ((a.system l E o).obj ((calculus l E U.left).reduction.obj K)) ⟶
        (a.integral l E).obj K :=
  match a with
  | .pull f _ _ _ => (pullbackTensorIntegralPullbackModel l E f.left).inv.app K
  | .push p _ =>
    (model.push l E p.left).hom.app ((calculus l E U.left).reduction.obj K) ≫
      (ringedPush l E p.left).map
        (GeneratorReduction.inverseOrZero ((calculus l E U.left).adjunction.unit.app K))
  | .shriek j hj _ =>
    letI := hj
    (coefficientSequenceLimit l E V.left).map ((model.openReduction l E j.left).app K) ≫
      GeneratorReduction.inverseOrZero
        ((calculus l E V.left).adjunction.unit.app ((ringedOpen l E j.left).obj K))

/-- The given natural primitive comparisons d_A and r_A, and their assumed whole-system
transpose identities. The compactification comparison is pinned by the recorded
Roos projections and finite scalar-adjunction mates, as in basic realization.
Source: fix-prop-coherence, hypotheses of the expression-tree refinement
(blueprint: lem-sf-integral-expression-recursion). -/
structure Primitives (D : FiniteFieldDatum.{u}) (o : Operations l E) where
  model : RealizationModel l E o
  unary : ∀ {U V : Over (Spec (.of D.k))} (a : Unary _ U V)
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom],
    basicUnarySource l E U.left V.left (a.system l E o) ≅
      basicUnaryTarget l E U.left V.left (a.system l E o) (a.integral l E)
  unary_spec : ∀ {U V : Over (Spec (.of D.k))} (a : Unary _ U V)
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
    (K : (basicUnaryDomain l E U.left V.left (a.system l E o)).FullSubcategory),
    (unary a).hom.app K = a.primitiveHom l E o model K.obj
  unaryReduction : ∀ {U V : Over (Spec (.of D.k))} (a : Unary _ U V),
    a.integral l E ⋙ (calculus l E V.left).reduction ⟶
      (calculus l E U.left).reduction ⋙ a.system l E o
  unaryTranspose : ∀ {U V : Over (Spec (.of D.k))} (a : Unary _ U V)
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
    (K : (basicUnaryDomain l E U.left V.left (a.system l E o)).FullSubcategory),
    (unaryReduction a).app K.obj =
      (calculus l E V.left).reduction.map ((unary a).inv.app K) ≫
        (calculus l E V.left).adjunction.counit.app
          ((a.system l E o).obj ((calculus l E U.left).reduction.obj K.obj))
  tensor : ∀ (W : Over (Spec (.of D.k)))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom],
    (basicTensorDomain l E W.left).ι ⋙
        (calculus l E W.left).reduction.prod (calculus l E W.left).reduction ⋙
          (calculus l E W.left).systemClosed.tensor ⋙ coefficientSequenceLimit l E W.left ≅
      (basicTensorDomain l E W.left).ι ⋙ integralCompletedTensor l E W.left
  tensor_spec : ∀ (W : Over (Spec (.of D.k)))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom],
    tensor W = Functor.isoWhiskerLeft (basicTensorDomain l E W.left).ι
      (pullbackTensorIntegralTensorModel l E W.left).symm
  tensorReduction : ∀ (W : Over (Spec (.of D.k))),
    integralCompletedTensor l E W.left ⋙ (calculus l E W.left).reduction ⟶
      (calculus l E W.left).reduction.prod (calculus l E W.left).reduction ⋙
        (calculus l E W.left).systemClosed.tensor
  tensorTranspose : ∀ (W : Over (Spec (.of D.k)))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
    (K : (basicTensorDomain l E W.left).FullSubcategory),
    (tensorReduction W).app K.obj =
      (calculus l E W.left).reduction.map ((tensor W).inv.app K) ≫
        (calculus l E W.left).adjunction.counit.app
          ((calculus l E W.left).systemClosed.tensor.obj
            ((calculus l E W.left).reduction.obj K.obj.1,
              (calculus l E W.left).reduction.obj K.obj.2))

/-- Exactly the assumed domain closure and invertibility of the actual unit and counit.
Source: fix-prop-coherence, hypotheses before a_A
(blueprint: lem-sf-integral-expression-recursion). -/
structure Reconstruction (D : FiniteFieldDatum.{u}) : Prop where
  reduction : ∀ (W : Over (Spec (.of D.k)))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] (K : Integral l E W.left),
    sfIntegralConstructible l E W.left K → Good l E W.left ((calculus l E W.left).reduction.obj K)
  limit : ∀ (W : Over (Spec (.of D.k)))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] (M : System l E W.left),
    Good l E W.left M →
      sfIntegralConstructible l E W.left ((coefficientSequenceLimit l E W.left).obj M)
  unit : ∀ (W : Over (Spec (.of D.k)))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] (K : Integral l E W.left),
    sfIntegralConstructible l E W.left K → IsIso ((calculus l E W.left).adjunction.unit.app K)
  counit : ∀ (W : Over (Spec (.of D.k)))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] (M : System l E W.left),
    Good l E W.left M → IsIso ((calculus l E W.left).adjunction.counit.app M)

/-- Transport d_A across the actual counit, exactly as in the displayed definition of a_A.
Source: fix-prop-coherence, unary counit substitution
(blueprint: lem-sf-integral-expression-recursion). -/
def unaryA {D : FiniteFieldDatum.{u}} {o : Operations l E}
    (d : Primitives l E D o) {U V : Over (Spec (.of D.k))} (a : Unary _ U V)
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] (M : System l E U.left)
    (h : basicUnaryDomain l E U.left V.left (a.system l E o)
      ((coefficientSequenceLimit l E U.left).obj M)) :=
  GeneratorReduction.inverseOrZero ((coefficientSequenceLimit l E V.left).map
    ((a.system l E o).map ((calculus l E U.left).adjunction.counit.app M))) ≫
      (d.unary a).hom.app ⟨(coefficientSequenceLimit l E U.left).obj M, h⟩

/-- The two-input version, using the tensor of the two actual counits.
Source: fix-prop-coherence, binary counit substitution
(blueprint: lem-sf-integral-expression-recursion). -/
def tensorA {D : FiniteFieldDatum.{u}} {o : Operations l E}
    (d : Primitives l E D o) (W : Over (Spec (.of D.k)))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] (M N : System l E W.left)
    (h : basicTensorDomain l E W.left
      ((coefficientSequenceLimit l E W.left).obj M,
        (coefficientSequenceLimit l E W.left).obj N)) :=
  GeneratorReduction.inverseOrZero ((coefficientSequenceLimit l E W.left).map
    ((calculus l E W.left).systemClosed.tensor.map
      (Prod.mkHom ((calculus l E W.left).adjunction.counit.app M)
        ((calculus l E W.left).adjunction.counit.app N)))) ≫
    (d.tensor W).hom.app
      ⟨((coefficientSequenceLimit l E W.left).obj M,
        (coefficientSequenceLimit l E W.left).obj N), h⟩

/-- Full input-family natural realization comparisons. The finite expression can
reuse any variable, including in both tensor branches.
Source: fix-prop-coherence (blueprint: lem-sf-integral-expression-recursion). -/
abbrev Comparisons (D : FiniteFieldDatum.{u}) (o : Operations l E) :=
  ∀ {I : Type u} [Finite I] {X : I → Over (Spec (.of D.k))}
    {W : Over (Spec (.of D.k))} (e : Expression _ I X W) (_g : e.geometric),
    e.realizationSource l E o ≅ e.realizationTarget l E o

/-- Coefficient maps are constructed on the finite tree, beginning with identity.
The compact-support abbreviation uses the same open/proper composite.
Source: fix-prop-coherence, displayed recursion for r_V
(blueprint: lem-sf-integral-expression-recursion). -/
def coefficientMap {D : FiniteFieldDatum.{u}} {o : Operations l E}
    (d : Primitives l E D o) {I : Type u} {X : I → Over (Spec (.of D.k))}
    {W : Over (Spec (.of D.k))} (e : Expression _ I X W) (g : e.geometric)
    (K : ∀ i, Integral l E (X i).left) :
    (calculus l E W.left).reduction.obj ((e.evaluate (integralInterpretation l E)).obj K) ⟶
      (e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K) :=
  match e, g with
  | .var _, _ => 𝟙 _
  | .pull f e, g =>
    (d.unaryReduction (.pull f g.2.2.1 g.the project server g.the project server.1)).app
        ((e.evaluate (integralInterpretation l E)).obj K) ≫
      (IntegralSystemRealization.pull l E f.left).map (coefficientMap d e g.the project server.2 K)
  | .push p hp e, g =>
    (d.unaryReduction (.push p hp)).app ((e.evaluate (integralInterpretation l E)).obj K) ≫
      (Operations.push l E o p.left).map (coefficientMap d e g.2.2 K)
  | .shriek j hj hqc e, g =>
    letI := hj
    (d.unaryReduction (.shriek j hj hqc)).app ((e.evaluate (integralInterpretation l E)).obj K) ≫
      (Operations.shriek l E o j.left).map (coefficientMap d e g.2.2 K)
  | .tensor e t, g =>
    (d.tensorReduction W).app
        ((e.evaluate (integralInterpretation l E)).obj K,
          (t.evaluate (integralInterpretation l E)).obj K) ≫
      (calculus l E W.left).systemClosed.tensor.map
        (Prod.mkHom (coefficientMap d e g.2.2.1 K) (coefficientMap d t g.2.2.2 K))
  | .compactSupport f c e, g =>
    let Z : Over (Spec (.of D.k)) := Over.mk (c.g ≫ W.hom)
    let j : _ ⟶ Z := Over.homMk c.i
      ((Category.assoc c.i c.g W.hom).symm.trans
        ((congrArg (fun z ↦ z ≫ W.hom) c.comm.symm).trans f.w))
    let p : Z ⟶ W := Over.homMk c.g rfl
    (d.unaryReduction (.push p (inferInstance : IsProper c.g))).app
        ((ringedOpen l E c.i).obj ((e.evaluate (integralInterpretation l E)).obj K)) ≫
      (Operations.push l E o c.g).map
        ((d.unaryReduction (.shriek j (inferInstance : IsOpenImmersion c.i)
          (compactOpenQuasiCompact c g.the project server.1))).app
            ((e.evaluate (integralInterpretation l E)).obj K) ≫
          (Operations.shriek l E o c.i).map (coefficientMap d e g.the project server.2 K))


/-- The chosen compactification expression, with one integral input variable.
Its interpretation is literally S_p J_j, retaining the hidden open intermediate.
Source: fix-prop-coherence, direct compactification clause
(blueprint: lem-sf-integral-expression-recursion). -/
def supportExpression {B : Scheme.{u}} {U V : Over B} (f : U ⟶ V)
    (c : Compactification f.left) : Expression B PUnit.{u + 1} (fun _ ↦ U) V :=
  .compactSupport f c (.var PUnit.unit)

/-- The specified direct compactification comparisons, as a dependent family.
Source: basic realization, compact-support comparison
(blueprint: lem-sf-integral-expression-recursion). -/
abbrev DirectComparisonFamily (D : FiniteFieldDatum.{u}) (o : Operations l E) :=
  ∀ {U V : Over (Spec (.of D.k))} (f : U ⟶ V)
    [LocallyOfFiniteType (U.left ↘ Spec (.of D.k))]
    [QuasiCompact (U.left ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (V.left ↘ Spec (.of D.k))]
    [QuasiCompact (V.left ↘ Spec (.of D.k))]
    [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (hl : IsUnit (l : D.k)) (c : Compactification f.left),
    (basicSupportDomain l E o c).ι ⋙ (calculus l E U.left).reduction ⋙
        Operations.shriek l E o c.i ⋙ Operations.push l E o c.g ⋙
          coefficientSequenceLimit l E V.left ≅
      basicSupportInput l E o c ⋙ sfCompactSupportFiniteIntegralFunctor l D.k hl c E ⋙
        (sfIntegralConstructible l E V.left).ι

/-- The direct comparison has the prescribed open/proper normalization.
Source: basic realization, compactification formula
(blueprint: lem-sf-integral-expression-recursion). -/
def DirectNormalization (D : FiniteFieldDatum.{u}) (o : Operations l E)
    (model : RealizationModel l E o) (comparison : DirectComparisonFamily l E D o) : Prop :=
  ∀ {U V : Over (Spec (.of D.k))} (f : U ⟶ V)
    [LocallyOfFiniteType (U.left ↘ Spec (.of D.k))]
    [QuasiCompact (U.left ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (V.left ↘ Spec (.of D.k))]
    [QuasiCompact (V.left ↘ Spec (.of D.k))]
    [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (hl : IsUnit (l : D.k)) (c : Compactification f.left)
    (K : (basicSupportDomain l E o c).FullSubcategory),
    (comparison f hl c).hom.app K =
      (model.push l E c.g).hom.app
          ((Operations.shriek l E o c.i).obj ((calculus l E U.left).reduction.obj K.obj)) ≫
        (ringedPush l E c.g).map
          ((coefficientSequenceLimit l E c.Z).map ((model.openReduction l E c.i).app K.obj) ≫
            GeneratorReduction.inverseOrZero
              ((calculus l E c.Z).adjunction.unit.app ((ringedOpen l E c.i).obj K.obj))) ≫
        (sfQcqsCompactSupportRealization l E D.k hl c).hom.app
          ((basicSupportInput l E o c).obj K)

/-- Every finite scalar-adjunction mate is the actual tower projection.
Source: basic realization, compactification projection formula
(blueprint: lem-sf-integral-expression-recursion). -/
def DirectProjection (D : FiniteFieldDatum.{u}) (o : Operations l E)
    (comparison : DirectComparisonFamily l E D o) : Prop :=
  ∀ {U V : Over (Spec (.of D.k))} (f : U ⟶ V)
    [LocallyOfFiniteType (U.left ↘ Spec (.of D.k))]
    [QuasiCompact (U.left ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (V.left ↘ Spec (.of D.k))]
    [QuasiCompact (V.left ↘ Spec (.of D.k))]
    [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (hl : IsUnit (l : D.k)) (c : Compactification f.left)
    (K : (basicSupportDomain l E o c).FullSubcategory) (n : ℕ),
    (scalarReductionDerivedExtension l E V.left n).map ((comparison f hl c).hom.app K) ≫
      (sfCompactSupportFiniteReductionIso l D.k hl c E
        ((basicSupportInput l E o c).obj K) n).hom =
    ((derivedScalarExtensionRestrictionAdjunction l E V.left n).choose.homEquiv _ _).symm
      ((coefficientSequenceProjection l E V.left n).app
          ((Operations.push l E o c.g).obj
            ((Operations.shriek l E o c.i).obj ((calculus l E U.left).reduction.obj K.obj))) ≫
        (scalarReductionDerivedRestriction l E V.left n).map
          ((supportEvaluation l E o c n).hom.app ((calculus l E U.left).reduction.obj K.obj) ≫
            (sfAmbientCompactSupportCandidate
              (Padic.coefficientExtensionRing l E (n + 1)) c).map
                (((calculus l E U.left).reductionEvaluation n).hom.app K.obj)))

/-- The given direct d_c with its prescribed maps and every finite projection.
Source: basic realization, compactification comparison
(blueprint: lem-sf-integral-expression-recursion). -/
structure DirectComparisons (D : FiniteFieldDatum.{u}) (o : Operations l E)
    (model : RealizationModel l E o) where
  comparison : DirectComparisonFamily l E D o
  normalization : DirectNormalization l E D o model comparison
  projection : DirectProjection l E D o comparison

/-- Read the root's two geometric hypotheses without imposing a constructor on its tree.
This is just projection from the recorded recursive domain, by cases.
Source: fix-prop-coherence, geometric domain
(blueprint: lem-sf-integral-expression-recursion). -/
abbrev geometricRoot {B : Scheme.{u}} {I : Type u} {X : I → Over B} {W : Over B}
    (e : Expression B I X W) (g : e.geometric) :
    LocallyOfFiniteType W.hom ∧ QuasiCompact W.hom :=
  match e, g with
  | .var _, g => ⟨g.1, g.2.1⟩
  | .pull _ _, g => ⟨g.1, g.2.1⟩
  | .push _ _ _, g => ⟨g.1, g.2.1⟩
  | .shriek _ _ _ _, g => ⟨g.1, g.2.1⟩
  | .tensor _ _, g => ⟨g.1, g.2.1⟩
  | .compactSupport _ _ _, g => ⟨g.1, g.2.1⟩

/-- The displayed leaf, unary and binary equations, recursively at every child.
The existential domain proofs merely license d_A(L M); the maps themselves are
specified by unaryA and tensorA. The compact-support constructor expands to S_p J_j.
Source: fix-prop-coherence, tree induction
(blueprint: lem-sf-integral-expression-recursion). -/
def Equations {D : FiniteFieldDatum.{u}} {o : Operations l E}
    (d : Primitives l E D o) (c : Comparisons l E D o)
    {I : Type u} [Finite I] {X : I → Over (Spec (.of D.k))} :
    {W : Over (Spec (.of D.k))} → (e : Expression _ I X W) →
    (g : e.geometric) → (K : (e.domain l E o).FullSubcategory) → Prop
  | _, .var i, g, K =>
    (c (.var i) g).hom.app K =
      GeneratorReduction.inverseOrZero ((calculus l E (X i).left).adjunction.unit.app (K.obj i))
  | W, .pull f e, g, K =>
    letI := g.1
    letI := g.2.1
    letI := (geometricRoot e g.the project server.2).1
    letI := (geometricRoot e g.the project server.2).2
    ∃ h : basicUnaryDomain l E _ W.left
      ((Unary.system l E o (.pull f g.2.2.1 g.the project server g.the project server.1)))
      ((coefficientSequenceLimit l E _).obj
        ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))),
      (c (.pull f e) g).hom.app K =
        unaryA l E d (.pull f g.2.2.1 g.the project server g.the project server.1)
          ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj)) h ≫
        (Unary.integral l E (.pull f g.2.2.1 g.the project server g.the project server.1)).map
          ((c e g.the project server.2).hom.app ⟨K.obj, K.property.1, K.property.2.2⟩) ∧
      IsIso (unaryA l E d (.pull f g.2.2.1 g.the project server g.the project server.1)
        ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj)) h) ∧
      Equations d c e g.the project server.2 ⟨K.obj, K.property.1, K.property.2.2⟩
  | W, .push f hp e, g, K =>
    letI := g.1
    letI := g.2.1
    letI := (geometricRoot e g.2.2).1
    letI := (geometricRoot e g.2.2).2
    ∃ h : basicUnaryDomain l E _ W.left
      ((Unary.system l E o (.push f hp)))
      ((coefficientSequenceLimit l E _).obj
        ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))),
      (c (.push f hp e) g).hom.app K =
        unaryA l E d (.push f hp)
          ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj)) h ≫
        (Unary.integral l E (.push f hp)).map
          ((c e g.2.2).hom.app ⟨K.obj, K.property.1, K.property.2.2⟩) ∧
      IsIso (unaryA l E d (.push f hp)
        ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj)) h) ∧
      Equations d c e g.2.2 ⟨K.obj, K.property.1, K.property.2.2⟩
  | W, .shriek f hj hqc e, g, K =>
    letI := g.1
    letI := g.2.1
    letI := (geometricRoot e g.2.2).1
    letI := (geometricRoot e g.2.2).2
    ∃ h : basicUnaryDomain l E _ W.left
      ((Unary.system l E o (.shriek f hj hqc)))
      ((coefficientSequenceLimit l E _).obj
        ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))),
      (c (.shriek f hj hqc e) g).hom.app K =
        unaryA l E d (.shriek f hj hqc)
          ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj)) h ≫
        (Unary.integral l E (.shriek f hj hqc)).map
          ((c e g.2.2).hom.app ⟨K.obj, K.property.1, K.property.2.2⟩) ∧
      IsIso (unaryA l E d (.shriek f hj hqc)
        ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj)) h) ∧
      Equations d c e g.2.2 ⟨K.obj, K.property.1, K.property.2.2⟩
  | W, .tensor e t, g, K =>
    letI := g.1
    letI := g.2.1
    ∃ h : basicTensorDomain l E W.left
      ((coefficientSequenceLimit l E W.left).obj
          ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj)),
        (coefficientSequenceLimit l E W.left).obj
          ((t.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))),
      (c (.tensor e t) g).hom.app K =
        tensorA l E d W
          ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))
          ((t.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj)) h ≫
        (integralCompletedTensor l E W.left).map
          (Prod.mkHom
            ((c e g.2.2.1).hom.app ⟨K.obj, K.property.1, K.property.2.2.1⟩)
            ((c t g.2.2.2).hom.app ⟨K.obj, K.property.1, K.property.2.2.2⟩)) ∧
      IsIso (tensorA l E d W
        ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))
        ((t.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj)) h) ∧
      Equations d c e g.2.2.1 ⟨K.obj, K.property.1, K.property.2.2.1⟩ ∧
      Equations d c t g.2.2.2 ⟨K.obj, K.property.1, K.property.2.2.2⟩
  | W, .compactSupport f cf e, g, K =>
    let Z : Over (Spec (.of D.k)) := Over.mk (cf.g ≫ W.hom)
    let j : _ ⟶ Z := Over.homMk cf.i
      ((Category.assoc cf.i cf.g W.hom).symm.trans
        ((congrArg (fun z ↦ z ≫ W.hom) cf.comm.symm).trans f.w))
    let p : Z ⟶ W := Over.homMk cf.g rfl
    let aj : Unary _ _ Z := .shriek j (inferInstance : IsOpenImmersion cf.i)
      (compactOpenQuasiCompact cf g.the project server.1)
    let ap : Unary _ Z W := .push p (inferInstance : IsProper cf.g)
    letI := g.1
    letI := g.2.1
    letI := (geometricRoot e g.the project server.2).1
    letI := (geometricRoot e g.the project server.2).2
    letI : LocallyOfFiniteType Z.hom := inferInstanceAs
      (LocallyOfFiniteType (cf.g ≫ W.hom))
    letI : QuasiCompact Z.hom := inferInstanceAs (QuasiCompact (cf.g ≫ W.hom))
    ∃ hj : basicUnaryDomain l E _ cf.Z (aj.system l E o)
      ((coefficientSequenceLimit l E _).obj
        ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))),
    ∃ hp : basicUnaryDomain l E cf.Z W.left (ap.system l E o)
      ((coefficientSequenceLimit l E cf.Z).obj
        ((Operations.shriek l E o cf.i).obj
          ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj)))),
      (c (.compactSupport f cf e) g).hom.app K =
        unaryA l E d ap
          ((Operations.shriek l E o cf.i).obj
            ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))) hp ≫
        (ringedPush l E cf.g).map
          (unaryA l E d aj
            ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj)) hj ≫
          (ringedOpen l E cf.i).map
            ((c e g.the project server.2).hom.app ⟨K.obj, K.property.1, K.property.2.2.1⟩)) ∧
      Equations d c e g.the project server.2 ⟨K.obj, K.property.1, K.property.2.2.1⟩


/-- The direct primitive domain supplies exactly the single-input expression domain.
This only rearranges its defining conjunctions.
Source: fix-prop-coherence, compactification domain
(blueprint: lem-sf-integral-expression-recursion). -/
def supportInput {D : FiniteFieldDatum.{u}} (o : Operations l E)
    {U V : Over (Spec (.of D.k))} (f : U ⟶ V) (cf : Compactification f.left)
    (K : (basicSupportDomain l E o cf).FullSubcategory) :
    ((supportExpression f cf).domain l E o).FullSubcategory :=
  ⟨fun _ ↦ K.obj, (fun _ ↦ ⟨K.property.1.1, K.property.1.2.1⟩),
    K.property.1.2.2, ⟨K.property.1.2.1, True.intro⟩, K.property.2⟩

/-- The prescribed direct d_c agrees with c for the S_p J_j expression, as an equality
of natural-comparison components before finite evaluation. The last factor is the
recorded, projection-normalized identification with the integral compact-support functor.
Source: fix-prop-coherence, direct compactification agreement
(blueprint: lem-sf-integral-expression-recursion). -/
def SupportAgreement {D : FiniteFieldDatum.{u}} {o : Operations l E}
    (d : Primitives l E D o) (dc : DirectComparisons l E D o d.model)
    (c : Comparisons l E D o) : Prop :=
  ∀ {U V : Over (Spec (.of D.k))} (f : U ⟶ V)
    [LocallyOfFiniteType (U.left ↘ Spec (.of D.k))]
    [QuasiCompact (U.left ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (V.left ↘ Spec (.of D.k))]
    [QuasiCompact (V.left ↘ Spec (.of D.k))]
    [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (hl : IsUnit (l : D.k)) (cf : Compactification f.left)
    (g : (supportExpression f cf).geometric)
    (K : (basicSupportDomain l E o cf).FullSubcategory),
    (c (supportExpression f cf) g).hom.app (supportInput l E o f cf K) ≫
        (sfQcqsCompactSupportRealization l E D.k hl cf).hom.app
          ((basicSupportInput l E o cf).obj K) =
      (dc.comparison f hl cf).hom.app K
```

## New

The block above is preserved byte for byte in
`Sheaf.SixFunctors.IntegralExpressionRecursionData`. The original module reexports it:

```lean
public import Sheaf.SixFunctors.IntegralBasicRealization
public import Sheaf.SixFunctors.GeneratorReductionStatement
public import Sheaf.SixFunctors.IntegralExpressionRecursionData
```

The original theorem has its verbatim original type. Its proof constructs the
canonical comparison as the inverse of the explicit transpose and applies the
three component obligations. The coefficient identity itself is proved by the
inverse law for the actual adjunction hom-set equivalence. No arbitrary witness
of a mere existence theorem is chosen; the sole proof used in constructing an
inverse is IsIso of a specified, explicitly defined natural transformation.

The new data node owns the relocated declarations and the explicit coefficient
transformation/transpose with their proved component equations. The original node
retains the theorem attachment and adds the data node as a statement dependency.
Neither its natural-language statement nor its Lean type changes.

## Users

The direct importers are IntegralRealizationAssemblyData and
IntegralComparisonRecursionLaws. Both compiled unchanged against this set with no
warnings using lcompile.py. Their temporary sandbox copies were removed; no
adaptation is required by the preserved public interface. The complete source
scan below includes current and quarantined modules; it conservatively lists every
transitive importer, not only declarations with textual occurrences. Claim holders
are not available from the local claim records, and no consumer is edited.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ProperOpenRefinementMatePlusCompatibility | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdicActualSystemsNormalized | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdicCompletedProjectionShift | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdicExceptionalShiftCoherence | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdicNormalizedPuritySystems | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdicProjectionShiftCoherence | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdicProjectionShiftData | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdicProperAdjunctionRealization | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturality | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdicPuritySourceFiniteness | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdicPuritySourceNormalization | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdicPuritySourceTransitionSquare | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdicQbarConstructibleRealization | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdicTraceTensorShift | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdicTraceTransposeData | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.AffineSpaceLastFactorProduct | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.AffineSpaceProductDomain | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceContractionProduct | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceFactorization | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceProductData | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceSuccessorContraction | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CochainLocalizationTensorIso | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CoefficientGammaRepresentatives | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CommonStageSmoothOperationIdentification | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CompactSupportCoefficientModels | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CompactSupportCoefficientModelsOrdinaryExistence | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CompactSupportCompletedScalarArrow | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CompactSupportLimitEquationData | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CompactSupportLimitEquationRealization | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CompactSupportPathReductionSquare | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionFieldStages | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionFormula | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionIntegralStages | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CompactSupportRealizationFactorNormalization | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CompactSupportRealizationFactorization | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CompactSupportScalarLimitReduction | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CompactSupportScalarProjectionIdentification | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CompactSupportScalarShiftNormalization | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CompactSupportScalarShiftStructures | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CompactSupportScalarShiftWitness | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CompactSupportStrictScalarComposition | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CompactSupportStrictScalarMate | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CompactSupportStrictScalarRefinement | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CompactificationBOrdinaryProjectionSquare | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CompactificationBProjectionData | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CompactificationBProjectionDomains | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CompactificationBProjectionReduction | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CompleteProjectionDescentMaps | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CompleteProjectionMateDescent | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CompleteProjectionReductionSquare | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CompletedScalarAssociatorLocalization | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CompletedScalarExactLocalization | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CompositionComparisons | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CompositionIteratedMateExpansion | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CompositionModelOrientationDefinitions | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CompositionModelOrientationDescent | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CompositionSingleMatePresentation | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CompositionTensorMate | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CondensedOpenCoefficientModels | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitComparisons | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitRealization | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitRealizationSupport | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitUnits | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CondensedOpenUnitComparison | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.ConstantCompletedOrdinaryAssociativity | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.ConstantCompletedScalarAssociativity | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CoordinateCartierBoundarySign | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CoordinateSectionProjectiveTrace | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CoordinateSectionSiteTransport | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CoordinateSectionTensorTrace | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.CoprojectionCompositionMate | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.DerivedPoincarePairing | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.EtaleOrientationLocality | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.EvenLineBinaryProductNormalization | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.EvenLineCoefficientProjectionNaturality | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.EvenLineCoordinateIntertwining | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.EvenLineProductIntegrationMaps | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.EvenLineProductIntegrationSymmetry | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.EvenTateLineSelfSymmetry | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.ExactProperOpenProjectionMate | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.ExceptionalBaseChangeIntegralComparisons | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.ExceptionalBaseChangeIntegralMaps | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.ExceptionalIntegralScalarMates | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.ExceptionalRefinementMates | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FieldExtensionCompletedStrictLimit | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FieldExtensionComposition | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FieldExtensionIntegralComparisons | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FieldExtensionIntegralCoordinates | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FieldExtensionIntegralDescent | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FieldExtensionIntegralModels | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FieldExtensionLimitEquations | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FieldExtensionRationalComparisons | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FieldExtensionRationalDescent | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FieldExtensionRationalModels | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FieldExtensionReductionDescent | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FieldExtensionReductionLimits | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FieldExtensionStrictLimits | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FieldExtensionSystemCoordinates | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FieldExtensionTowers | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FieldOrientedExchangeSquares | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FieldProjectionRefinementSquare | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteDiagonalBaseChangeReduction | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteDiagonalDncReduction | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationAssembly | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteDiagonalVectorReduction | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteFirstRootChart | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteForwardCompactifiedSwap | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteForwardProductCoordinates | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteForwardProductSymmetry | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteGeometricPurityMate | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteOrientationScalarPresentation | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FinitePositiveChartFrameExt | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FinitePositiveChartRecursion | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FinitePositiveRootChartPower | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FinitePositiveRootCharts | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteProductCompactification | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteProductOpenRestrictionPasting | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteProductOrdinaryNaturality | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteProductReductionComparisons | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteProductScalarPresentation | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteProjectionExchangeData | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteProjectionExchangeTransposes | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteProjectionIdentityNormalization | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteProjectionOpenAssembly | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteProjectionRefinementLeft | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteProjectionTensorSquare | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FinitePublishedRootChartPower | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FinitePurityCounitSystem | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionBaseChangeSource | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionExceptionalFiniteModel | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionLineChartScalars | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionLineInputConstructible | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionPositiveLineComparison | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionReassociation | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionShiftedPullbackCube | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionSourceChartIndependence | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionTensorFactors | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionTensorPurity | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionTensorSource | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionThetaFactor | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteRootLinePowerTransition | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteRootTensorPresentation | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteScalarCochainComparisonIso | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteScalarMonoidalRepresentative | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteScalarRepresentativeIso | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteScalarTensorData | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteScalarTensorSource | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteSignedTwistProducts | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteSourceChartPowerTransition | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteSourceChartScalarTransition | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteSupportedReductionEquation | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteTateSourceMap | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteTateSourceStructuralCoherence | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorComparisonEquations | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorFixedComparisons | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorLineChartReduction | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorLineDerivedExistence | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorLineDerivedExistenceWitness | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorPresentationReduction | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorProductFrameExt | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorProductMap | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorProductMapIsIso | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorPullbackCompositionReduction | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorPullbackTensorReduction | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorReductionData | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorSemilinearReduction | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorShiftCoherence | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorShiftFirst | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorShiftSecond | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorSignedReduction | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorSymmetryCoherence | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteTripleProductDefinitions | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FiniteTripleProductNormalForms | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.FixProjectionCompactificationComparison | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.ForwardProductCoordinateTransport | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.GlobalIdentityNormalization | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.GlobalVerdierDualityData | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.HomChainPairingNaturality | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.IntegralAdjunctionBijection | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.IntegralAdjunctionReconstruction | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.IntegralAdjunctionSourceComparison | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.IntegralCoefficientModelComparison | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.IntegralCompositorLimitRealization | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.IntegralOrientationReductionInjectivity | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.IntegralOrientationShiftedSheafModels | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.IntegralOrientedExchangeSquares | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.IntegralProjectionRefinementSquare | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.IntegralProjectionSystemCoordinates | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.IntegralPurityComparisonCocycles | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.IntegralPurityCounitReduction | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.IntegralReconstructionComparisonData | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.IntegralSmoothAdjunctionPresentation | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.IntegralTowerProjectionMates | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.IteratedPurityScalarPasting | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.IteratedTateSourceComposite | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.LocallyFiniteAdicCompactSupportRealization | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.ModelAffineIntegrationOrientation | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.ModelChartOrientationAssembly | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.ModelOrientationChartDescent | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.ModelOrientationSourceNaturality | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.ModelOrientationTateDetection | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.NativeConstantRestrictionAcyclicity | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.NativeConstantSupportModel | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.NativeGeometricBrownConstructibleComparison | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.NativeProperCoefficientOperations | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.NativeProperTensorComparison | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.NativeReductionCounitKFlat | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.NativeWeilScalarCounitCategories | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.NativeWeilScalarCounitData | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.NormalizedFieldPurityTrace | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.NormalizedFieldPurityTraceCommonStage | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.NormalizedFieldPurityTraceData | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.NormalizedOrientationPerfectDuality | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.NormalizedSmoothOrientationUnits | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.OrdinaryScalarBalancingLevel | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.OrdinaryScalarReductionGenerators | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.OrientationScalarTowerTransport | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.OriginalScalarMateShift | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.PfRefinementCompatibility | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.PodCtfAdjunctions | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.PodCtfPairingMaps | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.PodHomChainCounitFormula | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.PodHomChainCtfDomains | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.PodHomChainUncurriedTransport | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.PoincareDualityConventions | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.ProductCompositionCoordinateComparison | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.ProductExchangeCoordinateDefinitions | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.ProductExchangeCounitCoordinates | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.ProductHorizontalExchangeFactorization | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.ProductOpenAdjunctionNormalization | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.ProductOpenCounitNormalization | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.ProductOpenSupportNormalization | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.ProductOpenTensorProjection | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.ProductOpenTensorProjectionData | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.ProjectionFormulaCoherence | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.ProjectionReductionPresentation | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.PurRepresentingPairFiniteScalar | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.PurityCompactSupportTransport | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.PurityFiniteTateSourceComparisonCalculus | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.PurityKappaStages | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.PurityTateDatum | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.PurityTensorMapNaturality | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.PurityWitnessedMateNormalization | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.RationalExceptionalFinalEquations | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.RationalPurityCoherenceDescent | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.RationalPurityComparisonDescent | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.RationalPurityScalarLocalization | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.RationalPuritySourceLocalization | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonData | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.RationalizationOrientedExchangeSquare | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.RationalizedSmoothAdjunctionDiagrams | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.RelativeKunneth | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.RelativeKunnethCubeFactorTransport | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.RelativeProductBaseChangeFactorSquares | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.RelativeProductInputDomains | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.ScalarLimitConstraintShift | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.ScalarLimitTensorComposition | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.ScalarLimitTensorRestriction | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.ScalarReductionTowerBalancing | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.ScalarRefinementOriginsE | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.ScalarRefinementOriginsF | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.ScalarSourceCounitUniversal | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.ScalarTargetCounitUniversal | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.SixFunctorMixedSupportCupProduct | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientComparisons | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientModels | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.SmoothOperationDescentSpecification | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.SmoothOperationIdentificationSpecification | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.SmoothOrientationCoefficientFamily | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.SmoothOrientationPuritySquares | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.SmoothOrientationStageExchange | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.SmoothOrientedExchangeComparisons | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityBaseChangeFactors | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityFieldExtension | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerExceptionalBaseChange | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.SpecifiedIntegralUnitOrientation | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.StrictRefinementRestrictionSquares | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.StrictScalarMateEvaluationData | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.StrictScalarMateFiniteEvaluation | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.StrictScalarMateShift | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.SystemClopenMateIdentification | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.SystemCompositorRefinementSquare | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.SystemProjectionChangeCompatibility | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.SystemProjectionTriangleCompatibility | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.SystemScalarBasisDistributivity | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.SystemScalarProjectionData | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.SystemScalarProjectionIdentification | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.SystemScalarRefinementRestriction | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.SystemScalarTensorConstituents | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.SystemTensorPresentationCoreExistence | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.SystemTensorPresentationData | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.SystemTensorPresentationIdentification | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.SystemTensorSemilinearRealization | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.TensorHomCoefficientTransposes | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.TensorHomExchange | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.TensorMapPresentationIndependent | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.TensorMateInvertibleInput | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.TowerGeometricPurityMate | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.TowerOrientationEvaluation | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.TowerPurityRealizedData | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.TowerPurityRealizedNormalization | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.TowerPurityRealizedTranspose | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.TowerTraceCanonicalIntegral | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.TowerTraceNormalizedPresentations | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.TowerTraceOrientationUniqueness | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.TowerTracePurityComparison | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.TowerTracePurityComparisonData | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.TowerTraceScalarCounit | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionCartier | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionCoprojection | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionCore | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionMaps | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionNormalization | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionOrdinary | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionProjective | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionSign | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicIdentification | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackCoefficientCoherence | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcPullback | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcTwist | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarPrimitives | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarShifts | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareMaps | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareScalars | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.VectorBundleThom | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.VectorBundleThomMaps | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.VectorBundleThomProduct | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.VerdierCoefficientRealization | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.VerdierExchange | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.VerdierHomChainComposition | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.VerdierHomChainCompositionData | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.VerdierIdentityProjection | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.VerdierOrdinaryTensorTransport | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.VerdierProjectionExceptionalPaste | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchange | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchangeData | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.WeilChosenExchangeConstruction | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.Paper.WeilChosenTransposeNaturality | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SecSmoothPurity.NestedAffineChartFormulas | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SecSmoothPurity.NestedAffineFormulaData | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SecSmoothPurity.NestedAffineIntegrationRegrouping | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SecSmoothPurity.NestedAffineNormalizedInputs | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SecSmoothPurity.NestedAffineOrientation | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SecSmoothPurity.NestedAffineOrientationCoordinates | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.AmbientExactClopenComparison | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.AmbientExactClopenData | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.AmbientOrdinaryClopenLocalization | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.AmbientProperOpenCalculus | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.AmbientSystemBetaLocalization | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.AmbientSystemClopenLocalization | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.AmbientUnderivedClopenPasting | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.BasicRealizationShiftSquare | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.CartesianCompactSupportCompositor | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.CompletedProjectionExchangeData | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.CompletedProjectionExchangeDomains | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.CompletedProjectionExchangePaths | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.CompletedProjectionExchangeRealization | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.CompletedProjectionExchangeSystem | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.CompletedShriekCompositionLaws | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.CompositionProjectionData | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.CompositionProjectionMate | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.ConstantOrdinaryCompactificationComparison | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralCanonicalAmbientModels | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeWords | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonData | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationOrdinaryComposition | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralComparisonRecursionLaws | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralExpressionCoefficientSquares | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralNormalizedRefinementPasting | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationAssemblyData | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralRefinementDiagramAdmissibility | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.KappaCoefficientCoherence | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.KappaGeometricComparisons | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.KappaMixedCoherence | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.KunnethSecondOpenSubstitution | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.OpenAdjunctionShift | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.OpenSupportStepBounds | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.OrdinaryAmbientProperOpenLaws | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.OrdinaryProperOpenInvertibility | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.ProductNormalizationRealizationTransport | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.ProductSystemUniformRealizationDomain | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.ProjectionCompatibleTriangleAssembly | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.ProjectionIntegralCoherenceRealization | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.ProjectionRefinementDescent | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.ProjectionSystemCoherence | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.PublishedSystemTensorComposition | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.RamifiedScalarExceptionalLimit | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.RealizationAdjunctionInsertionShift | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.RealizationTreeShiftTransport | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.RefinementProjectionCounit | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.RefinementProjectionLocalTensor | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.RefinementProjectionProperComposition | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.RefinementProjectionWords | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.SemilinearOrdinaryCompactificationComparison | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.StrictCompactificationProjectionShift | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.SystemAdjunctionOpenMapShift | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.SystemProperOpenProjectionShift | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.SystemProperOpenSupport | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.ThreeCellCompositor | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.TriangleProjectionCompositorContraction | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.TriangleProjectionNormalForm | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SixFunctors.TriangleProjectionSystemNormalForm | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SmoothPurity.OrdinaryBinaryProductTranspose | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SmoothPurity.OrdinaryProductTransposeData | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SmoothPurity.OrdinaryTripleLeftComparison | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SmoothPurity.OrdinaryTripleProductTranspose | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.SmoothPurity.OrdinaryTripleRightComparison | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.WeilSheaf.DualRealizationComparison | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.WeilSheaf.NativeBidualEvaluationRealization | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.WeilSheaf.NativeDualRealizationComparisonData | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalForgetful | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalForgetfulData | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalLeftModels | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalPointUnit | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalStructuralTransport | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.WeilSheaf.NativeSectionClosedForgetful | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.WeilSheaf.OrdinaryClosedPresentation | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |
| Sheaf.WeilSheaf.StructuralOmegaHomPairs | not recorded locally | Same original public declarations and definition bodies through public reexport; no adaptation. |

## Status

landed 20261026T201708-L-3409391 2026-10-26 (merge of deliver/T2/Sheaf.SixFunctors.IntegralExpressionRecursion)
