# Realization-tree shift data

## Reason

The selected-generator context lemma needs the existing TreeSynchronizedPair relation,
while the main theorem must import that lemma. Move the eleven existing data declarations
into Sheaf.SixFunctors.RealizationTreeShiftData and publicly re-export them from the
original module to avoid an import cycle. Names, universes, signatures, visibility,
constructor arguments and definition bodies are unchanged. All eight original public
imports remain. The new module is attached to def-pur-realization-tree-shift-data;
the old theorem node retains the theorem attachment. There is no mathematical
statement or data change and no target meaning is changed.

## Old

In lean/Sheaf/SixFunctors/RealizationTreeShiftTransport.lean:

```lean
open Classical in
/-- The actual system expression shift, before applying total limit. This first
uses reduction's designated mate, then follows the selected context with its fixed
left or signed right tensor comparison. Its total limit, followed by limitShift,
is exactly the sourceShift already defined by the dependency.
Source: coefficient-comparison sentence, proof steps 2 and 7
(blueprint: lem-pur-realization-tree-shift-transport). -/
def treeSystemShift {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (o : Operations l E) {W : Over B} (e : IndependentExpression B I X W)
    (K : ∀ i, Integral l E (X i).left) (i : I) (r : ℤ) :
    e.val.systemObj l E o ((inputReduction l E X).obj
        (Function.update K i ((K i)⟦r⟧))) ≅
      (e.val.systemObj l E o ((inputReduction l E X).obj K))⟦r⟧ :=
  (eqToIso (e.reductionContext_evaluate l E o K i ((K i)⟦r⟧))).symm ≪≫
    (e.variableContext (systemInterpretation l E o)
      ((inputReduction l E X).obj K) i).evaluate.mapIso
        ((Functor.commShiftIso ((calculus l E (X i).left).reduction)
          (self := reductionShift l E (X i).left) r).app (K i)) ≪≫
    (e.variableContext (systemInterpretation l E o)
      ((inputReduction l E X).obj K) i).shift (systemShifts l E o) r
        ((calculus l E (X i).left).reduction.obj (K i)) ≪≫
    (shiftFunctor (System l E W.left) r).mapIso
      (eqToIso (e.variableContext_evaluate (systemInterpretation l E o)
        ((inputReduction l E X).obj K) i
        ((calculus l E (X i).left).reduction.obj (K i))).2)

open Classical in
/-- Both shift squares and both actual realization intertwining equations at two
families. The first square is in D(S), not merely after derived evaluation or limit.
The intertwining equation is written without cancellation as L(s)c_T=c_V v;
since the c's are isomorphisms it is exactly v=c_T L(s)c_V inverse in functional order.
Source: inherited-equations sentence, proof steps 5--8
(blueprint: lem-pur-realization-tree-shift-transport). -/
def TreeMapTransport (D : FiniteFieldDatum.{u}) (o : Operations l E)
    (R : Realizations l E D o) {I : Type u} [Finite I]
    {X : I → Over (Spec (.of D.k))} {W : Over (Spec (.of D.k))}
    (e t : IndependentExpression _ I X W) (ge : e.val.geometric) (gt : t.val.geometric)
    (K : ∀ i, Integral l E (X i).left) (i : I) (r : ℤ)
    (he : e.val.domain l E o K) (ht : t.val.domain l E o K)
    (heNew : e.val.domain l E o (Function.update K i ((K i)⟦r⟧)))
    (htNew : t.val.domain l E o (Function.update K i ((K i)⟦r⟧)))
    (s : e.val.systemObj l E o ((inputReduction l E X).obj K) ⟶
      t.val.systemObj l E o ((inputReduction l E X).obj K))
    (v : (e.val.evaluate (integralInterpretation l E)).obj K ⟶
      (t.val.evaluate (integralInterpretation l E)).obj K)
    (sNew : e.val.systemObj l E o ((inputReduction l E X).obj
        (Function.update K i ((K i)⟦r⟧))) ⟶
      t.val.systemObj l E o ((inputReduction l E X).obj
        (Function.update K i ((K i)⟦r⟧))))
    (vNew : (e.val.evaluate (integralInterpretation l E)).obj
        (Function.update K i ((K i)⟦r⟧)) ⟶
      (t.val.evaluate (integralInterpretation l E)).obj
        (Function.update K i ((K i)⟦r⟧))) : Prop :=
  sNew ≫ (treeSystemShift l E o t K i r).hom =
      (treeSystemShift l E o e K i r).hom ≫ s⟦r⟧' ∧
    vNew ≫ (t.integralShift l E K i r).hom =
      (e.integralShift l E K i r).hom ≫ v⟦r⟧' ∧
    (coefficientSequenceLimit l E W.left).map s ≫
        (R.comparison t.val gt).hom.app ⟨K, ht⟩ =
      (R.comparison e.val ge).hom.app ⟨K, he⟩ ≫ v ∧
    (coefficientSequenceLimit l E W.left).map sNew ≫
        (R.comparison t.val gt).hom.app
          ⟨Function.update K i ((K i)⟦r⟧), htNew⟩ =
      (R.comparison e.val ge).hom.app
          ⟨Function.update K i ((K i)⟦r⟧), heNew⟩ ≫ vNew

section SelectedGenerators
variable (o : Operations l E) (c : Compositors l E o) (a : OpenComparisons l E o c)
  (bridge : CanonicalBridge l E o) (h : ProperOpenCoherence l E o c a bridge)
  (d : RingedModels l E) (b : RingedOpenComparisons l E d)
  (q : RingedProperOpen l E d b)
  {B : Scheme.{u}} {I : Type u} {X : I → Over B}
  (M : ∀ i, System l E (X i).left) (K : ∀ i, Integral l E (X i).left)
  (MNew : ∀ i, System l E (X i).left) (KNew : ∀ i, Integral l E (X i).left)

/-- Select a collection of specified generators, retaining each actual constructor
and all its geometric parameters at both input families. This is a predicate on
SynchronizedBasic witnesses, not an arbitrary map supplied in place of a generator.
Source: the collection of generators in proof steps 5--7
(blueprint: lem-pur-realization-tree-shift-transport). -/
abbrev TreeGeneratorSelection :=
  ∀ {W : Over B} {e t : Expression B I X W}
    {s : e.systemObj l E o M ⟶ t.systemObj l E o M}
    {v : e.ringedObj l E d K ⟶ t.ringedObj l E d K}
    {sNew : e.systemObj l E o MNew ⟶ t.systemObj l E o MNew}
    {vNew : e.ringedObj l E d KNew ⟶ t.ringedObj l E d KNew},
    SynchronizedBasic l E o c a bridge h d b q M K MNew KNew e t s v sNew vNew → Prop

/-- The subrelation generated by a chosen collection of synchronized basic maps.
Its constructors are exactly the existing synchronized identity, composition and
unary/binary contexts; only its basic constructor requires membership in G.
Thus a hypothesis on a collection is never replaced by a hypothesis on all generators.
Source: the finite compositions and expression contexts of proof steps 5--7
(blueprint: lem-pur-realization-tree-shift-transport). -/
inductive TreeSynchronizedPair (G : TreeGeneratorSelection l E o c a bridge h d b q
    M K MNew KNew) : {W : Over B} → (e t : Expression B I X W) →
    (e.systemObj l E o M ⟶ t.systemObj l E o M) →
    ((e.evaluate (integralInterpretation l E)).obj K ⟶
      (t.evaluate (integralInterpretation l E)).obj K) →
    (e.systemObj l E o MNew ⟶ t.systemObj l E o MNew) →
    ((e.evaluate (integralInterpretation l E)).obj KNew ⟶
      (t.evaluate (integralInterpretation l E)).obj KNew) → Prop where
  | basic {W : Over B} {e t : Expression B I X W}
      {s : e.systemObj l E o M ⟶ t.systemObj l E o M}
      {sNew : e.systemObj l E o MNew ⟶ t.systemObj l E o MNew}
      {r : e.ringedObj l E d K ⟶ t.ringedObj l E d K}
      {rNew : e.ringedObj l E d KNew ⟶ t.ringedObj l E d KNew}
      (g : SynchronizedBasic l E o c a bridge h d b q M K MNew KNew e t s r sNew rNew)
      (_selected : G g)
      (he : IsIso (e.completionMap l E d K))
      (heNew : IsIso (e.completionMap l E d KNew)) :
    TreeSynchronizedPair G e t s
      (@inv _ _ _ _ (e.completionMap l E d K) he ≫ r ≫ t.completionMap l E d K)
      sNew
      (@inv _ _ _ _ (e.completionMap l E d KNew) heNew ≫ rNew ≫ t.completionMap l E d KNew)
  | identity {W : Over B} (e : Expression B I X W) : TreeSynchronizedPair G e e (𝟙 _) (𝟙 _)
      (𝟙 _)
      (𝟙 _)
  | comp {W : Over B} {e t v : Expression B I X W}
      {s₁ : e.systemObj l E o M ⟶ t.systemObj l E o M}
      {s₁New : e.systemObj l E o MNew ⟶ t.systemObj l E o MNew}
      {s₂ : t.systemObj l E o M ⟶ v.systemObj l E o M}
      {s₂New : t.systemObj l E o MNew ⟶ v.systemObj l E o MNew}
      {r₁ : (e.evaluate (integralInterpretation l E)).obj K ⟶
        (t.evaluate (integralInterpretation l E)).obj K}
      {r₁New : (e.evaluate (integralInterpretation l E)).obj KNew ⟶
        (t.evaluate (integralInterpretation l E)).obj KNew}
      {r₂ : (t.evaluate (integralInterpretation l E)).obj K ⟶
        (v.evaluate (integralInterpretation l E)).obj K}
      {r₂New : (t.evaluate (integralInterpretation l E)).obj KNew ⟶
        (v.evaluate (integralInterpretation l E)).obj KNew}
      (_gt : t.geometric) (_independent : Function.Injective t.occurrenceLabel)
      (_ht : t.admissible l E o M) (_htNew : t.admissible l E o MNew) :
    TreeSynchronizedPair G e t s₁ r₁
      s₁New
      r₁New → TreeSynchronizedPair G t v s₂ r₂
      s₂New
      r₂New →
      TreeSynchronizedPair G e v (s₁ ≫ s₂) (r₁ ≫ r₂)
      (s₁New ≫ s₂New)
      (r₁New ≫ r₂New)
  | pull {U V : Over B} (f : U ⟶ V)
      {e t : Expression B I X V}
      {s : e.systemObj l E o M ⟶ t.systemObj l E o M}
      {sNew : e.systemObj l E o MNew ⟶ t.systemObj l E o MNew}
      {r : (e.evaluate (integralInterpretation l E)).obj K ⟶
        (t.evaluate (integralInterpretation l E)).obj K}
      {rNew : (e.evaluate (integralInterpretation l E)).obj KNew ⟶
        (t.evaluate (integralInterpretation l E)).obj KNew} :
    TreeSynchronizedPair G e t s r
      sNew
      rNew → TreeSynchronizedPair G (.pull f e) (.pull f t) ((pull l E f.left).map s)
        ((integralDerivedPullback l E f.left).map r)
      ((pull l E f.left).map sNew)
      ((integralDerivedPullback l E f.left).map rNew)
  | push {U V : Over B} (f : U ⟶ V) (hf : IsProper f.left)
      {e t : Expression B I X U}
      {s : e.systemObj l E o M ⟶ t.systemObj l E o M}
      {sNew : e.systemObj l E o MNew ⟶ t.systemObj l E o MNew}
      {r : (e.evaluate (integralInterpretation l E)).obj K ⟶
        (t.evaluate (integralInterpretation l E)).obj K}
      {rNew : (e.evaluate (integralInterpretation l E)).obj KNew ⟶
        (t.evaluate (integralInterpretation l E)).obj KNew} :
    TreeSynchronizedPair G e t s r
      sNew
      rNew → TreeSynchronizedPair G (.push f hf e) (.push f hf t)
      ((Operations.push l E o f.left).map s)
        ((ringedPush l E f.left).map r)
      ((Operations.push l E o f.left).map sNew)
      ((ringedPush l E f.left).map rNew)
  | shriek {U V : Over B} (f : U ⟶ V) [hf : IsOpenImmersion f.left] (hq : QuasiCompact f.left)
      {e t : Expression B I X U}
      {s : e.systemObj l E o M ⟶ t.systemObj l E o M}
      {sNew : e.systemObj l E o MNew ⟶ t.systemObj l E o MNew}
      {r : (e.evaluate (integralInterpretation l E)).obj K ⟶
        (t.evaluate (integralInterpretation l E)).obj K}
      {rNew : (e.evaluate (integralInterpretation l E)).obj KNew ⟶
        (t.evaluate (integralInterpretation l E)).obj KNew} :
    TreeSynchronizedPair G e t s r
      sNew
      rNew → TreeSynchronizedPair G (.shriek f hf hq e) (.shriek f hf hq t)
      ((Operations.shriek l E o
        f.left).map s) ((ringedOpen l E f.left).map r)
      ((Operations.shriek l E o f.left).map sNew)
      ((ringedOpen l E f.left).map rNew)
  | compactSupport {U V : Over B} (f : U ⟶ V) (cf : Compactification f.left)
      {e t : Expression B I X U}
      {s : e.systemObj l E o M ⟶ t.systemObj l E o M}
      {sNew : e.systemObj l E o MNew ⟶ t.systemObj l E o MNew}
      {r : (e.evaluate (integralInterpretation l E)).obj K ⟶
        (t.evaluate (integralInterpretation l E)).obj K}
      {rNew : (e.evaluate (integralInterpretation l E)).obj KNew ⟶
        (t.evaluate (integralInterpretation l E)).obj KNew} :
    TreeSynchronizedPair G e t s r
      sNew
      rNew → TreeSynchronizedPair G (.compactSupport f cf e) (.compactSupport f cf t)
      ((Operations.shriek
        l E o cf.i ⋙ Operations.push l E o cf.g).map s) ((PurCompactSupport.image
        (PurCompactSupport.completed l E) cf).map r)
      ((Operations.shriek l E o cf.i ⋙ Operations.push l E o cf.g).map sNew)
      ((PurCompactSupport.image (PurCompactSupport.completed l E) cf).map rNew)
  | tensor {W : Over B} {e t v z : Expression B I X W}
      {s₁ : e.systemObj l E o M ⟶ t.systemObj l E o M}
      {s₁New : e.systemObj l E o MNew ⟶ t.systemObj l E o MNew}
      {s₂ : v.systemObj l E o M ⟶ z.systemObj l E o M}
      {s₂New : v.systemObj l E o MNew ⟶ z.systemObj l E o MNew}
      {r₁ : (e.evaluate (integralInterpretation l E)).obj K ⟶
        (t.evaluate (integralInterpretation l E)).obj K}
      {r₁New : (e.evaluate (integralInterpretation l E)).obj KNew ⟶
        (t.evaluate (integralInterpretation l E)).obj KNew}
      {r₂ : (v.evaluate (integralInterpretation l E)).obj K ⟶
        (z.evaluate (integralInterpretation l E)).obj K}
      {r₂New : (v.evaluate (integralInterpretation l E)).obj KNew ⟶
        (z.evaluate (integralInterpretation l E)).obj KNew} :
    TreeSynchronizedPair G e t s₁ r₁
      s₁New
      r₁New → TreeSynchronizedPair G v z s₂ r₂
      s₂New
      r₂New →
      TreeSynchronizedPair G (.tensor e v) (.tensor t z)
        ((calculus l E W.left).systemClosed.tensor.map
        (Prod.mkHom s₁ s₂)) ((integralCompletedTensor l E W.left).map (Prod.mkHom r₁ r₂))
      ((calculus l E W.left).systemClosed.tensor.map (Prod.mkHom s₁New s₂New))
      ((integralCompletedTensor l E W.left).map (Prod.mkHom r₁New r₂New))

end SelectedGenerators

/-- A collection of the dependency's specified generators at every two input families.
Source: the specified collection in the conditional statement
(blueprint: lem-pur-realization-tree-shift-transport). -/
structure TreeGenerators (D : FiniteFieldDatum.{u}) (o : Operations l E)
    (R : Realizations l E D o) where
  selected : ∀ {I : Type u} {X : I → Over (Spec (.of D.k))}
    (M : ∀ i, System l E (X i).left) (K : ∀ i, Integral l E (X i).left)
    (MNew : ∀ i, System l E (X i).left) (KNew : ∀ i, Integral l E (X i).left),
    TreeGeneratorSelection l E o R.compositors R.openComparisons R.canonicalBridge
      R.properOpen R.ringedModels R.ringedOpenComparisons R.ringedProperOpen M K MNew KNew

open Classical in
/-- Context comparison before total limit for a subtree that may use only some
of the global input labels. The equality witnesses identify the actual context
endpoints; they supply no map. This avoids requiring unused labels to occur in
both operands of a tensor. At the root it is treeSystemShift.
Source: the unique selected path, proof steps 2--4 and 7
(blueprint: lem-pur-realization-tree-shift-transport). -/
def treeSubexpressionShift {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (o : Operations l E) {W : Over B} (e : Expression B I X W)
    (K : ∀ i, Integral l E (X i).left) (i : I) (r : ℤ)
    (c : Expression.SlotContext (systemInterpretation l E o) (X i) W)
    (_hc : e.variableContext (systemInterpretation l E o)
      ((inputReduction l E X).obj K) i = some c)
    (hOld : c.evaluate.obj ((calculus l E (X i).left).reduction.obj (K i)) =
      e.systemObj l E o ((inputReduction l E X).obj K))
    (hNew : c.evaluate.obj ((calculus l E (X i).left).reduction.obj ((K i)⟦r⟧)) =
      e.systemObj l E o ((inputReduction l E X).obj
        (Function.update K i ((K i)⟦r⟧)))) :
    e.systemObj l E o ((inputReduction l E X).obj
        (Function.update K i ((K i)⟦r⟧))) ≅
      (e.systemObj l E o ((inputReduction l E X).obj K))⟦r⟧ :=
  (eqToIso hNew).symm ≪≫
    c.evaluate.mapIso ((Functor.commShiftIso ((calculus l E (X i).left).reduction)
      (self := reductionShift l E (X i).left) r).app (K i)) ≪≫
    c.shift (systemShifts l E o) r ((calculus l E (X i).left).reduction.obj (K i)) ≪≫
    (shiftFunctor (System l E W.left) r).mapIso (eqToIso hOld)

open Classical in
/-- The assumed squares for a chosen collection of local system generators.
Subexpressions may omit global labels; their selected label occurs at most once.
The context is the dependency's explicit variableContext search. Integral maps
are required only to intertwine the actual realizations at the two families;
the integral shift square is a conclusion, not a hypothesis.
Source: inherited-equations sentence, proof steps 5--8
(blueprint: lem-pur-realization-tree-shift-transport). -/
def TreeGeneratorShiftLaws (D : FiniteFieldDatum.{u}) (o : Operations l E)
    (R : Realizations l E D o) (G : TreeGenerators l E D o R) : Prop :=
  ∀ {I : Type u} [Finite I] {X : I → Over (Spec (.of D.k))}
    {W : Over (Spec (.of D.k))} (e t : Expression _ I X W)
    (_ei : Function.Injective e.occurrenceLabel) (_ti : Function.Injective t.occurrenceLabel)
    (ge : e.geometric) (gt : t.geometric)
    (K : ∀ i, Integral l E (X i).left) (i : I) (r : ℤ)
    (he : e.domain l E o K) (ht : t.domain l E o K)
    (heNew : e.domain l E o (Function.update K i ((K i)⟦r⟧)))
    (htNew : t.domain l E o (Function.update K i ((K i)⟦r⟧)))
    (s : e.systemObj l E o ((inputReduction l E X).obj K) ⟶
      t.systemObj l E o ((inputReduction l E X).obj K))
    (v : e.ringedObj l E R.ringedModels K ⟶ t.ringedObj l E R.ringedModels K)
    (sNew : e.systemObj l E o ((inputReduction l E X).obj
        (Function.update K i ((K i)⟦r⟧))) ⟶
      t.systemObj l E o ((inputReduction l E X).obj
        (Function.update K i ((K i)⟦r⟧))))
    (vNew : e.ringedObj l E R.ringedModels (Function.update K i ((K i)⟦r⟧)) ⟶
      t.ringedObj l E R.ringedModels (Function.update K i ((K i)⟦r⟧)))
    (g : SynchronizedBasic l E o R.compositors R.openComparisons R.canonicalBridge
      R.properOpen R.ringedModels R.ringedOpenComparisons R.ringedProperOpen
      ((inputReduction l E X).obj K) K
      ((inputReduction l E X).obj (Function.update K i ((K i)⟦r⟧)))
      (Function.update K i ((K i)⟦r⟧)) e t s v sNew vNew),
    G.selected ((inputReduction l E X).obj K) K
      ((inputReduction l E X).obj (Function.update K i ((K i)⟦r⟧)))
      (Function.update K i ((K i)⟦r⟧)) g →
    (c : Expression.SlotContext (systemInterpretation l E o) (X i) W) →
    (hc : e.variableContext (systemInterpretation l E o)
      ((inputReduction l E X).obj K) i = some c) →
    (hOld : c.evaluate.obj ((calculus l E (X i).left).reduction.obj (K i)) =
      e.systemObj l E o ((inputReduction l E X).obj K)) →
    (hNew : c.evaluate.obj ((calculus l E (X i).left).reduction.obj ((K i)⟦r⟧)) =
      e.systemObj l E o ((inputReduction l E X).obj
        (Function.update K i ((K i)⟦r⟧)))) →
    (d : Expression.SlotContext (systemInterpretation l E o) (X i) W) →
    (hd : t.variableContext (systemInterpretation l E o)
      ((inputReduction l E X).obj K) i = some d) →
    (kOld : d.evaluate.obj ((calculus l E (X i).left).reduction.obj (K i)) =
      t.systemObj l E o ((inputReduction l E X).obj K)) →
    (kNew : d.evaluate.obj ((calculus l E (X i).left).reduction.obj ((K i)⟦r⟧)) =
      t.systemObj l E o ((inputReduction l E X).obj
        (Function.update K i ((K i)⟦r⟧)))) →
    sNew ≫ (treeSubexpressionShift l E o t K i r d hd kOld kNew).hom =
      (treeSubexpressionShift l E o e K i r c hc hOld hNew).hom ≫ s⟦r⟧' ∧
    (coefficientSequenceLimit l E W.left).map s ≫
        (R.comparison t gt).hom.app ⟨K, ht⟩ =
      (R.comparison e ge).hom.app ⟨K, he⟩ ≫
        (GeneratorReduction.inverseOrZero (e.completionMap l E R.ringedModels K) ≫
          v ≫ t.completionMap l E R.ringedModels K) ∧
    (coefficientSequenceLimit l E W.left).map sNew ≫
        (R.comparison t gt).hom.app ⟨Function.update K i ((K i)⟦r⟧), htNew⟩ =
      (R.comparison e ge).hom.app ⟨Function.update K i ((K i)⟦r⟧), heNew⟩ ≫
        (GeneratorReduction.inverseOrZero (e.completionMap l E R.ringedModels
            (Function.update K i ((K i)⟦r⟧))) ≫
          vNew ≫ t.completionMap l E R.ringedModels (Function.update K i ((K i)⟦r⟧)))

open Classical in
/-- Apply a finite list of single-leaf updates in its displayed order.
Source: proof step 8, independent input changes
(blueprint: lem-pur-realization-tree-shift-transport). -/
def treeShiftInputs {B : Scheme.{u}} {I : Type u} (X : I → Over B) :
    List (I × ℤ) → (∀ i, Integral l E (X i).left) → ∀ i, Integral l E (X i).left
  | [], K => K
  | (i, r) :: q, K => treeShiftInputs X q (Function.update K i ((K i)⟦r⟧))

/-- The matching ordered sequence of output shifts, without identifying different
orders by an unstated coherence convention.
Source: proof step 8 (blueprint: lem-pur-realization-tree-shift-transport). -/
def treeOutputShifts (W : Scheme.{u}) {I : Type u} :
    List (I × ℤ) → Integral l E W ⥤ Integral l E W
  | [] => 𝟭 _
  | (_, r) :: q => shiftFunctor _ r ⋙ treeOutputShifts W q

open Classical in
/-- The finite source comparison is the successive single-slot comparison itself.
Source: proof step 8 (blueprint: lem-pur-realization-tree-shift-transport). -/
def treeSourceShifts {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (o : Operations l E) {W : Over B} (e : IndependentExpression B I X W) :
    (q : List (I × ℤ)) → (K : ∀ i, Integral l E (X i).left) →
    (e.source l E o).obj (treeShiftInputs l E X q K) ≅
      (treeOutputShifts l E W.left q).obj ((e.source l E o).obj K)
  | [], _ => Iso.refl _
  | (i, r) :: q, K => treeSourceShifts o e q (Function.update K i ((K i)⟦r⟧)) ≪≫
    (treeOutputShifts l E W.left q).mapIso (e.sourceShift l E o K i r)

open Classical in
/-- The finite integral comparison uses precisely the same successive slots.
Source: proof step 8 (blueprint: lem-pur-realization-tree-shift-transport). -/
def treeIntegralShifts {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    {W : Over B} (e : IndependentExpression B I X W) :
    (q : List (I × ℤ)) → (K : ∀ i, Integral l E (X i).left) →
    (e.val.evaluate (integralInterpretation l E)).obj (treeShiftInputs l E X q K) ≅
      (treeOutputShifts l E W.left q).obj
        ((e.val.evaluate (integralInterpretation l E)).obj K)
  | [], _ => Iso.refl _
  | (i, r) :: q, K => treeIntegralShifts e q (Function.update K i ((K i)⟦r⟧)) ≪≫
    (treeOutputShifts l E W.left q).mapIso (e.integralShift l E K i r)

```

## New

The exact same declarations above are in
lean/Sheaf/SixFunctors/RealizationTreeShiftData.lean. The original module adds:

```lean
public import Sheaf.SixFunctors.RealizationTreeShiftData
```

The five former private proof imports are removed from the item. They provide no
symbols to its new proof. The lower single-leaf node retains the mathematical
dependencies for constructibility, normalization, origins and Tor bounds.

The item node lem-pur-realization-tree-shift-transport now lists
def-pur-realization-tree-shift-data among its stmt_deps, since its unchanged statement
uses the moved TreeGenerators, TreeGeneratorShiftLaws, TreeSynchronizedPair,
TreeMapTransport and finite-list constructions, which that node now owns (reviewer fix).

## Users

`tools/downstream.py Sheaf.SixFunctors.RealizationTreeShiftTransport --uses` followed
by all eleven moved names reports zero downstream Lean modules. Each name occurs
only in the item module. There are consequently zero direct importers to compile.
The parent's DAG dependency on the original theorem is retained; none is withdrawn.

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctors.RealizationTreeShiftTransport | B4 | Exact data re-export; theorem statement unchanged. |
| Sheaf.SixFunctors.RealizationTreeSingleShift | new in B4 | Uses the same definitions below the main theorem. |
| Sheaf.SixFunctors.RealizationTreeSystemSquare | new in B4 | Uses the same selected-generator relation below the main theorem. |

## Status

landed 20261027T012809-L-2332243 2026-10-27 (merge of deliver/B4/Sheaf.SixFunctors.RealizationTreeShiftTransport)
