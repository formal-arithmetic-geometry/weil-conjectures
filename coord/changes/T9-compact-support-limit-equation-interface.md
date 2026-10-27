# CompactSupportLimit normalized path interface

## Reason

The two independently stated proof obligations need the existing corner and path definitions.
Extract those definitions into CompactSupportLimitEquationData to prevent an import cycle.
This extraction is independent of compile performance. The original module publicly reexports
all declarations; names, signatures, visibility, attributes and bodies remain identical.
The source-library tree and the five target signatures are untouched.

## Old

The following complete declaration blocks were in CompactSupportLimitEquationRealization,
with its three original public imports:

```lean
/-- The unary compact-support words, using the existing typed expression syntax.
Compact support means its supplied open/proper factorization, not an additional operation.
Source: node statement, word sentence
(blueprint: lem-pur-compact-support-limit-equation-realization). -/
def IsWord {B : Scheme.{u}} {I : Type u} {X : I → Over B} :
    {T : Over B} → Expression B I X T → Prop
  | _, .var _ => True
  | _, .pull _ e | _, .push _ _ e | _, .shriek _ _ _ e => IsWord e
  | _, .compactSupport _ c e => QuasiCompact c.i ∧ IsWord e
  | _, .tensor _ _ => False

/-- Separation over the fixed base at every intermediate scheme of a word.
Source: node statement, compact-support domain sentence
(blueprint: lem-pur-compact-support-limit-equation-realization). -/
def SeparatedWord {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    {T : Over B} (e : Expression B I X T) : Prop :=
  IsSeparated T.hom ∧ match e with
  | .var _ => True
  | .pull _ e | .push _ _ e | .shriek _ _ _ e => SeparatedWord e
  | .compactSupport _ c e => IsSeparated (c.g ≫ T.hom) ∧ SeparatedWord e
  | .tensor e f => SeparatedWord e ∧ SeparatedWord f

/-- The integral intermediate-object domain: each output and each open prefix of a
supplied compactification is complete, constructible and has uniform finite Tor bounds.
The compatible origin witnesses and strict-system bounds are retained by Expression.domain.
Source: node statement, domain proviso
(blueprint: lem-pur-compact-support-limit-equation-realization). -/
def IntegralDomain {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    {T : Over B} (e : Expression B I X T)
    (K : ∀ i, Integral l E (X i).left) : Prop :=
  finiteTorConstructibleIntegral l E T.left
      ((e.evaluate (integralInterpretation l E)).obj K) ∧ match e with
  | .var _ => True
  | .pull _ e | .push _ _ e | .shriek _ _ _ e => IntegralDomain e K
  | .compactSupport _ c e => IntegralDomain e K ∧
    finiteTorConstructibleIntegral l E c.Z
      ((ringedOpen l E c.i).obj ((e.evaluate (integralInterpretation l E)).obj K))
  | .tensor e f => IntegralDomain e K ∧ IntegralDomain f K

variable (D : FiniteFieldDatum.{u}) (o : Operations l E) (r : Realizations l E D o)
  {I : Type u} [Finite I] {X : I → Over (Spec (CommRingCat.of D.k))}
  {T : Over (Spec (CommRingCat.of D.k))}

/-- The normalized strict constant-ring word on the whole reduced input system.
Its scalar action and all transitions are retained before localization.
Source: Stacks 0941; node proof Steps 1--2
(blueprint: lem-pur-compact-support-limit-equation-realization). -/
def towerObject (e : Expression _ I X T) (K : ∀ i, Integral l E (X i).left) :=
  (GeneratorReduction.U l E T.left).obj (e.systemObj l E o ((inputReduction l E X).obj K))

/-- Reduction of the completed output to the normalized constant strict word.
The first factor is the K-flat-normalized constant/completed reduction comparison;
the second is the recursive reduction comparison of the operation word.
Source: node proof Steps 1--2, common-quotient normalization
(blueprint: lem-pur-compact-support-limit-equation-realization). -/
def reductionComparison (e : Expression _ I X T) (g : e.geometric)
    (K : (e.domain l E o).FullSubcategory) :
    (GeneratorReduction.constantReduction l E T.left).obj
        ((GeneratorReduction.H l E T.left).obj
          ((e.evaluate (integralInterpretation l E)).obj K.obj)) ≅
      towerObject l E D o e K.obj :=
  (GeneratorReduction.rho l E T.left).symm.app _ ≪≫
    (GeneratorReduction.U l E T.left).mapIso ((r.reduction e g).symm.app K)

/-- The specified corner is eta followed by total limit of the recursive strict reduction
comparison. This definition precedes every asserted equation or invertibility result.
Source: node proof Step 2; Stacks 099N
(blueprint: lem-pur-compact-support-limit-equation-realization). -/
def corner (e : Expression _ I X T) (g : e.geometric)
    (K : (e.domain l E o).FullSubcategory) :
    (GeneratorReduction.H l E T.left).obj ((e.evaluate (integralInterpretation l E)).obj K.obj) ⟶
      (GeneratorReduction.constantLimit l E T.left).obj (towerObject l E D o e K.obj) :=
  ((sfCbcSite T.left).unit _ (sfCbcModelIdeal (GeneratorReduction.constantDatum l E))).app _ ≫
    (GeneratorReduction.constantLimit l E T.left).map (reductionComparison l E D o r e g K).hom

/-- The corresponding constant-tower path is exact scalar restriction of the actual
whole-system path, rather than a lift of its finite evaluated components.
The system proper exchange is the prescribed counit-tensor mate and the open factor
is the adjunction-normalized beta in CanonicalPair.
Source: node statement, strict path sentence; proof Steps 3--6
(blueprint: lem-pur-compact-support-limit-equation-realization). -/
def towerMap {e t : Expression _ I X T} (K : ∀ i, Integral l E (X i).left)
    (s : e.systemObj l E o ((inputReduction l E X).obj K) ⟶
      t.systemObj l E o ((inputReduction l E X).obj K)) :
    towerObject l E D o e K ⟶ towerObject l E D o t K := (GeneratorReduction.U l E T.left).map s

/-- The normalized strict refinement mate, including its identity and proper compositors.
Source: node proof Steps 5--6; Stacks 0F7B--0F7D
(blueprint: lem-pur-compact-support-limit-equation-realization). -/
def systemRefinement {U V : Scheme.{u}} {f : U ⟶ V}
    {c d : Compactification f} [QuasiCompact c.i] [QuasiCompact d.i]
    (z : c.Refinement d) (M : System l E U) :
    ((systemInterpretation l E o).compactSupport f d).obj M ⟶
      ((systemInterpretation l E o).compactSupport f c).obj M :=
  let idIso := r.canonicalBridge.push l E (𝟙 U) ≪≫
    ProEtale.SemilinearProperOpen.sId (scalarRings l E) (scalarTransitions l E) U
  (Operations.push l E o d.g).map
    ((Operations.shriek l E o d.i).map (idIso.inv.app M) ≫
      (r.properOpen.gamma c.i (𝟙 U) z.hom d.i
        (z.i_hom.trans (Category.id_comp _).symm)).app M) ≫
    (r.compositors.pushComp l E z.hom d.g).hom.app _ ≫
    (eqToIso (congrArg (Operations.push l E o) z.hom_g)).hom.app _

/-- The completed refinement uses the published unique open-unit-normalized mate.
The explicit over-scheme instances are just the structure maps of the word's indices.
Source: node proof Steps 5--6; Stacks 0F7B
(blueprint: lem-pur-compact-support-limit-equation-realization). -/
def integralRefinement (hl : l ≠ D.p)
    {U V : Over (Spec (CommRingCat.of D.k))} (f : U ⟶ V)
    (hu : LocallyOfFiniteType U.hom ∧ QuasiCompact U.hom ∧ IsSeparated U.hom)
    (hv : LocallyOfFiniteType V.hom ∧ QuasiCompact V.hom ∧ IsSeparated V.hom)
    (hf : IsSeparated f.left ∧ LocallyOfFiniteType f.left ∧ QuasiCompact f.left)
    {c d : Compactification f.left} (z : c.Refinement d) (M : Integral l E U.left)
    (hM : finiteTorConstructibleIntegral l E U.left M) :
    ((integralInterpretation l E).compactSupport f.left c).obj M ≅
      ((integralInterpretation l E).compactSupport f.left d).obj M :=
  letI : U.left.Over (Spec (CommRingCat.of D.k)) := ⟨U.hom⟩
  letI : V.left.Over (Spec (CommRingCat.of D.k)) := ⟨V.hom⟩
  letI : LocallyOfFiniteType (U.left ↘ Spec (CommRingCat.of D.k)) := hu.1
  letI : QuasiCompact (U.left ↘ Spec (CommRingCat.of D.k)) := hu.2.1
  letI : IsSeparated (U.left ↘ Spec (CommRingCat.of D.k)) := hu.2.2
  letI : LocallyOfFiniteType (V.left ↘ Spec (CommRingCat.of D.k)) := hv.1
  letI : QuasiCompact (V.left ↘ Spec (CommRingCat.of D.k)) := hv.2.1
  letI : IsSeparated (V.left ↘ Spec (CommRingCat.of D.k)) := hv.2.2
  letI : f.left.IsOver (Spec (CommRingCat.of D.k)) := ⟨f.w⟩
  letI := hf.1
  letI := hf.2.1
  letI := hf.2.2
  PurCompactSupport.refinementComparison l E D hl f.left z M hM

/-- The published completion-unit transport of a localized ringed-site arrow.
The inverse is used only where the source completion comparison is invertible;
that invertibility is part of the recorded compact-support realization domain.
Source: node proof Steps 1, 3--4
(blueprint: lem-pur-compact-support-limit-equation-realization). -/
def completedMap {U : Over (Spec (CommRingCat.of D.k))}
    (e t : Expression _ I X U) (K : ∀ i, Integral l E (X i).left)
    (a : e.ringedObj l E r.ringedModels K ⟶ t.ringedObj l E r.ringedModels K) :
    (e.evaluate (integralInterpretation l E)).obj K ⟶
      (t.evaluate (integralInterpretation l E)).obj K :=
  GeneratorReduction.inverseOrZero (e.completionMap l E r.ringedModels K) ≫ a ≫
    t.completionMap l E r.ringedModels K

variable (hl : l ≠ D.p) (K : ∀ i, Integral l E (X i).left)

/-- Finite paths use exactly compact-support exchanges, pullback compositors,
refinement maps, identity factorization expansions, and their inverses.
Composition retains the full intermediate domain.
Whiskering is interpreted by the actual completed and strict system functors.
Source: node statement, path and whiskering sentences
(blueprint: lem-pur-compact-support-limit-equation-realization). -/
inductive Path : {T : Over (Spec (CommRingCat.of D.k))} →
    (e t : Expression _ I X T) →
    (e.systemObj l E o ((inputReduction l E X).obj K) ⟶
      t.systemObj l E o ((inputReduction l E X).obj K)) →
    ((e.evaluate (integralInterpretation l E)).obj K ⟶
      (t.evaluate (integralInterpretation l E)).obj K) → Prop where
  | identity {T : Over (Spec (CommRingCat.of D.k))} (e : Expression _ I X T) :
    Path e e (𝟙 _) (𝟙 _)
  | pullComp {U V W : Over (Spec (CommRingCat.of D.k))}
      (f : U ⟶ V) (g : V ⟶ W) (e : Expression _ I X W) :
    Path (.pull (f ≫ g) e) (.pull f (.pull g e))
      ((r.compositors.pullComp f.left g.left).hom.app
        (e.systemObj l E o ((inputReduction l E X).obj K)))
      (completedMap l E D o r (.pull (f ≫ g) e) (.pull f (.pull g e)) K
        ((ringedPullComp l E f.left g.left).hom.app
          (e.ringedObj l E r.ringedModels K)))
  | exchange {U V U' V' : Over (Spec (CommRingCat.of D.k))}
      (f : U ⟶ V) (f' : U' ⟶ V') (cf : Compactification f.left)
      (cf' : Compactification f'.left) (x : U' ⟶ U) (y : V' ⟶ V)
      (z : cf'.Z ⟶ cf.Z)
      (wi : x.left ≫ cf.i = cf'.i ≫ z) (wp : z ≫ cf.g = cf'.g ≫ y.left)
      (hi : IsPullback x.left cf'.i cf.i z)
      (_hp : IsPullback z cf'.g cf.g y.left) (e : Expression _ I X U) :
    Path (.pull y (.compactSupport f cf e)) (.compactSupport f' cf' (.pull x e))
      ((compactificationExchange l E o r.compositors r.openComparisons
        cf cf' x.left y.left z wi wp hi).app
          (e.systemObj l E o ((inputReduction l E X).obj K)))
      (completedMap l E D o r (.pull y (.compactSupport f cf e))
        (.compactSupport f' cf' (.pull x e)) K
        ((ringedCompactificationExchange l E r.ringedModels r.ringedOpenComparisons
          cf cf' x.left y.left z wi wp hi).app (e.ringedObj l E r.ringedModels K)))
  | expansion {U V : Over (Spec (CommRingCat.of D.k))}
      (f : U ⟶ V) (cf : Compactification f.left) (hq : QuasiCompact cf.i)
      (e : Expression _ I X U) :
    Path (.compactSupport f cf e)
      (.push (compactProper (f := f) cf) (inferInstance : IsProper cf.g)
        (.shriek (compactOpen (f := f) cf) (inferInstance : IsOpenImmersion cf.i) hq e)) (𝟙 _) (𝟙 _)
  | refinement {U V : Over (Spec (CommRingCat.of D.k))} (f : U ⟶ V)
      (hu : LocallyOfFiniteType U.hom ∧ QuasiCompact U.hom ∧ IsSeparated U.hom)
      (hv : LocallyOfFiniteType V.hom ∧ QuasiCompact V.hom ∧ IsSeparated V.hom)
      (hf : IsSeparated f.left ∧ LocallyOfFiniteType f.left ∧ QuasiCompact f.left)
      {c d : Compactification f.left} [QuasiCompact c.i] [QuasiCompact d.i]
      (z : c.Refinement d) (e : Expression _ I X U)
      (hM : finiteTorConstructibleIntegral l E U.left
        ((e.evaluate (integralInterpretation l E)).obj K)) :
    Path (.compactSupport f d e) (.compactSupport f c e)
      (systemRefinement l E D o r z (e.systemObj l E o ((inputReduction l E X).obj K)))
      (integralRefinement l E D hl f hu hv hf z
        ((e.evaluate (integralInterpretation l E)).obj K) hM).inv
  | inverse {T : Over (Spec (CommRingCat.of D.k))} {e t : Expression _ I X T}
      {s : e.systemObj l E o ((inputReduction l E X).obj K) ⟶
        t.systemObj l E o ((inputReduction l E X).obj K)}
      {a : (e.evaluate (integralInterpretation l E)).obj K ⟶
        (t.evaluate (integralInterpretation l E)).obj K} :
    IsIso s → IsIso a → Path e t s a → Path t e (GeneratorReduction.inverseOrZero s)
      (GeneratorReduction.inverseOrZero a)
  | comp {T : Over (Spec (CommRingCat.of D.k))} {e t v : Expression _ I X T}
      {s : e.systemObj l E o ((inputReduction l E X).obj K) ⟶
        t.systemObj l E o ((inputReduction l E X).obj K)}
      {s' : t.systemObj l E o ((inputReduction l E X).obj K) ⟶
        v.systemObj l E o ((inputReduction l E X).obj K)}
      {a : (e.evaluate (integralInterpretation l E)).obj K ⟶
        (t.evaluate (integralInterpretation l E)).obj K}
      {a' : (t.evaluate (integralInterpretation l E)).obj K ⟶
        (v.evaluate (integralInterpretation l E)).obj K}
      (_gt : t.geometric) (_ht : t.domain l E o K)
      (_wt : IsWord t) (_st : SeparatedWord t) (_it : IntegralDomain l E t K) :
    Path e t s a → Path t v s' a' → Path e v (s ≫ s') (a ≫ a')
  | pull {U V : Over (Spec (CommRingCat.of D.k))} (f : U ⟶ V)
      {e t : Expression _ I X V}
      {s : e.systemObj l E o ((inputReduction l E X).obj K) ⟶
        t.systemObj l E o ((inputReduction l E X).obj K)}
      {r : (e.evaluate (integralInterpretation l E)).obj K ⟶
        (t.evaluate (integralInterpretation l E)).obj K} :
    Path e t s r → Path (.pull f e) (.pull f t)
      ((pull l E f.left).map s) ((integralDerivedPullback l E f.left).map r)
  | push {U V : Over (Spec (CommRingCat.of D.k))} (f : U ⟶ V) (hf : IsProper f.left)
      {e t : Expression _ I X U}
      {s : e.systemObj l E o ((inputReduction l E X).obj K) ⟶
        t.systemObj l E o ((inputReduction l E X).obj K)}
      {r : (e.evaluate (integralInterpretation l E)).obj K ⟶
        (t.evaluate (integralInterpretation l E)).obj K} :
    Path e t s r → Path (.push f hf e) (.push f hf t)
      ((Operations.push l E o f.left).map s) ((ringedPush l E f.left).map r)
  | shriek {U V : Over (Spec (CommRingCat.of D.k))} (f : U ⟶
        V) [hf : IsOpenImmersion f.left] (hq : QuasiCompact f.left)
      {e t : Expression _ I X U}
      {s : e.systemObj l E o ((inputReduction l E X).obj K) ⟶
        t.systemObj l E o ((inputReduction l E X).obj K)}
      {r : (e.evaluate (integralInterpretation l E)).obj K ⟶
        (t.evaluate (integralInterpretation l E)).obj K} :
    Path e t s r → Path (.shriek f hf hq e) (.shriek f hf hq t)
      ((Operations.shriek l E o f.left).map s) ((ringedOpen l E f.left).map r)
  | compactSupport {U V : Over (Spec (CommRingCat.of D.k))} (f : U ⟶
        V) (cf : Compactification f.left)
      {e t : Expression _ I X U}
      {s : e.systemObj l E o ((inputReduction l E X).obj K) ⟶
        t.systemObj l E o ((inputReduction l E X).obj K)}
      {r : (e.evaluate (integralInterpretation l E)).obj K ⟶
        (t.evaluate (integralInterpretation l E)).obj K} :
    Path e t s r → Path (.compactSupport f cf e) (.compactSupport f cf t)
      ((Operations.shriek l E o cf.i ⋙ Operations.push l E o cf.g).map s)
      ((PurCompactSupport.image (PurCompactSupport.completed l E) cf).map r)

/-- The displayed square and the consequence for two parallel whole-tower paths.
Path retains the specified generators, their inverse isomorphisms, finite
composition, and every pull/proper/open/compact-support whiskering. Refinement maps
are the normalized proper/open gamma composites and their inverses, not arbitrary maps.
Source: node statement, displayed equation and final sentences
(blueprint: lem-pur-compact-support-limit-equation-realization). -/
def EquationLaws : Prop :=
  ∀ (e t : Expression _ I X T) (ge : e.geometric) (gt : t.geometric),
    IsWord e → IsWord t → SeparatedWord e → SeparatedWord t →
    ∀ (K : (e.domain l E o).FullSubcategory) (ht : t.domain l E o K.obj),
      IntegralDomain l E e K.obj → IntegralDomain l E t K.obj →
      IsIso (corner l E D o r e ge K) ∧
      IsIso (corner l E D o r t gt ⟨K.obj, ht⟩) ∧
      (∀ (s : e.systemObj l E o ((inputReduction l E X).obj K.obj) ⟶
            t.systemObj l E o ((inputReduction l E X).obj K.obj))
          (a : (e.evaluate (integralInterpretation l E)).obj K.obj ⟶
            (t.evaluate (integralInterpretation l E)).obj K.obj),
        Path l E D o r hl K.obj e t s a →
        (GeneratorReduction.H l E T.left).map a ≫ corner l E D o r t gt ⟨K.obj, ht⟩ =
          corner l E D o r e ge K ≫
            (GeneratorReduction.constantLimit l E T.left).map (towerMap l E D o K.obj s)) ∧
      (∀ (s s' : e.systemObj l E o ((inputReduction l E X).obj K.obj) ⟶
            t.systemObj l E o ((inputReduction l E X).obj K.obj))
          (a a' : (e.evaluate (integralInterpretation l E)).obj K.obj ⟶
            (t.evaluate (integralInterpretation l E)).obj K.obj),
        Path l E D o r hl K.obj e t s a →
        Path l E D o r hl K.obj e t s' a' →
        towerMap l E D o K.obj s = towerMap l E D o K.obj s' → a = a')

```

## New

Those exact blocks, including all docstrings, are in
Sheaf.Paper.CompactSupportLimitEquationData with the same three public imports:

```lean
public import Sheaf.SixFunctors.IntegralCompactificationSystemRealization
public import Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison
public import Sheaf.Paper.IntegralCompactSupportCoefficientComparison
```

The original module now uses:

```lean
public import Sheaf.Paper.CompactSupportLimitEquationData
import Sheaf.Paper.CompleteIntegralConstantRestriction
import Sheaf.Paper.CompactSupportPathReductionSquare
```

Its theorem signature remains verbatim and its proof is now complete relative to the two
named obligations. The data module has no holes. All original exported dependencies remain
publicly available through the reexport. The new lemmas have their own modules and nodes.

## Users

The read-only downstream.py inventory found zero current Lean importers of the assigned
module. The DAG still has unfinished mathematical parents; no withdrawal or pruning of
the item or those parent dependencies is proposed. New consumers are listed explicitly.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CompactSupportLimitEquationRealization | T9 | Public reexport of identical data; complete proof from two named obligations. |
| Sheaf.Paper.CompactSupportLimitEquationData | T9, new | Owns the unchanged definition blocks. |
| Sheaf.Paper.CompactSupportPathReductionSquare | T9, new | Imports the data directly; no cycle. |
| Sheaf.Paper.CompleteIntegralConstantRestriction | T9, new | Uses existing scalar data; no dependency on the item. |

## Status

landed 20261025T203307-L-2801491 2026-10-25 (merge of deliver/T9/Sheaf.Paper.CompactSupportLimitEquationRealization)
