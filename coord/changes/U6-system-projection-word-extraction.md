# WeilConjectures.SystemProjectionFormula: specified geometric words

## Reason

The refinement and compatible-triangle obligations must refer to the existing concrete
words without importing the theorem that consumes them. Extract their definitions to
`Sheaf.Paper.SystemProjectionFormulaMaps`; reexport that module publicly from the
original module. This breaks the would-be proof import cycle. It is not a timing split.
Every existing declaration name, signature and visibility is preserved. Eight bodies
are preserved verbatim; compositor factors its identical word through compositorAlong. No
meaning of a target changes, and no source-library module is edited.

## Old

The following declarations were in `Sheaf.Paper.SystemProjectionFormulaCoherence`:

```lean
def inverseOnDomain {C : Type v} [Category.{w} C] [HasZeroMorphisms C]
    {K M : C} (b : K ⟶ M) : M ⟶ K :=
  open Classical in
  if h : IsIso b then @inv _ _ _ _ b h else 0

/-- Compact support in the specified simultaneous geometric section presentation.
Source: Zheng 4.1, 4.10; Stacks 0F7J
(blueprint: lem-pur-system-level-projection-formula-coherence). -/
abbrev support (o : Operations l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) := Operations.shriek l E o c.i ⋙ Operations.push l E o c.g

/-- Reverse refinement: the intrinsic proper/open mate and direct-image compositor.
Source: Stacks 0F7J; the node's specified geometric compact-support comparison
(blueprint: lem-pur-system-level-projection-formula-coherence). -/
def refinement (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) (b : CanonicalBridge l E o)
    (q : ProperOpenCoherence l E o c a b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {d e : Compactification f} (r : d.Refinement e) : support l E o e ⟶ support l E o d :=
  haveI := d.quasiCompact_openImmersion inferInstance
  haveI := e.quasiCompact_openImmersion inferInstance
  Functor.whiskerRight
    ((Functor.leftUnitor _).inv ≫
      Functor.whiskerRight
        (b.push l E (𝟙 X) ≪≫ ProEtale.SemilinearProperOpen.sId
          (scalarRings l E) (scalarTransitions l E) X).inv (Operations.shriek l E o e.i) ≫
      q.gamma d.i (𝟙 X) r.hom e.i (r.i_hom.trans (Category.id_comp _).symm))
      (Operations.push l E o e.g) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (Operations.shriek l E o d.i)
      ((c.pushComp l E r.hom e.g).hom ≫
        eqToHom (congrArg (Operations.push l E o) r.hom_g))

/-- Transport through the canonical graph common refinement, taking the actual inverse
on the comparison's isomorphism domain. Source: Stacks 0F7J and 0ATU
(blueprint: lem-pur-system-level-projection-formula-coherence). -/
def change (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) (b : CanonicalBridge l E o)
    (q : ProperOpenCoherence l E o c a b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (d e : Compactification f) (M : System l E X) :
    (support l E o d).obj M ⟶ (support l E o e).obj M :=
  (refinement l E o c a b q (Compactification.infFst d e)).app M ≫
    inverseOnDomain
      ((refinement l E o c a b q (Compactification.infSnd d e)).app M)

/-- The actual proper/open word in a compatible triangle, including its equality casts.
Source: Stacks 0F7J; compatible-triangle compositor normalization
(blueprint: lem-pur-system-level-projection-formula-coherence). -/
def triangleWord (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) (b : CanonicalBridge l E o)
    (q : ProperOpenCoherence l E o c a b)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g] (T : Compactification.Triangle f g) :
    support l E o T.cf ⋙ support l E o T.cg ⟶ support l E o T.cfg :=
  haveI := T.cf.quasiCompact_openImmersion inferInstance
  haveI := T.cg.quasiCompact_openImmersion inferInstance
  haveI : QuasiCompact T.q := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    T.isPullback inferInstance
  (Functor.associator _ _ _).symm.hom ≫
    Functor.whiskerRight ((Functor.associator _ _ _).hom) _ ≫
    Functor.whiskerRight (Functor.whiskerLeft (Operations.shriek l E o T.cf.i)
      (q.gamma T.q T.cf.g T.p T.cg.i T.isPullback.w.symm)) _ ≫
    Functor.whiskerRight (Functor.associator _ _ _).inv _ ≫
    Functor.whiskerRight (Functor.whiskerRight ((c.openComp l E T.cf.i T.q).hom ≫
      (openCongr l E o T.i_q).hom) _) _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (Operations.shriek l E o T.cfg.i)
      ((c.pushComp l E T.p T.cg.g).hom ≫
        eqToHom (congrArg (Operations.push l E o) T.p_g))

/-- The specified geometric compositor for arbitrary supplied compactifications.
The auxiliary triangle and all three transports are canonical geometric constructions.
Source: Stacks 0F7J; thm-sf-comp-composition in simultaneous section models
(blueprint: lem-pur-system-level-projection-formula-coherence). -/
def compositor (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) (b : CanonicalBridge l E o)
    (q : ProperOpenCoherence l E o c a b)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))
    (M : System l E X) :
    (support l E o cg).obj ((support l E o cf).obj M) ⟶ (support l E o cfg).obj M :=
  letI := cg.hasCompactification
  letI := cfg.hasCompactification
  let T := Compactification.Triangle.ofHasCompactification f g
  (support l E o cg).map (change l E o c a b q cf T.cf M) ≫
    change l E o c a b q cg T.cg ((support l E o T.cf).obj M) ≫
    (triangleWord l E o c a b q T).app M ≫ change l E o c a b q T.cfg cfg M

/-- The proper counit projection followed by the open tensor comparison, in the same
simultaneous geometric section model. No independently chosen finite lift occurs.
Source: def-exchange-projection; Stacks 0B56, 0E8I
(blueprint: lem-pur-system-level-projection-formula-coherence). -/
def projection (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (d : Compactification f)
    (M : System l E X) (N : System l E Y) :=
  compactificationProjection l E o c a d M N

/-- The left projection word, with the canonical last pullback identification.
The compositor is the published proper/open word transported by graph refinements.
Source: the node's displayed composition identity; Stacks 0F7J
(blueprint: lem-pur-system-level-projection-formula-coherence). -/
def leftMap (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) (b : CanonicalBridge l E o)
    (q : ProperOpenCoherence l E o c a b)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))
    (M : System l E X) (N : System l E Z) :=
  projection l E o c a cg ((support l E o cf).obj M) N ≫
    (support l E o cg).map (projection l E o c a cf M ((pull l E g).obj N)) ≫
    compositor l E o c a b q
      cf cg cfg ((calculus l E X).systemClosed.tensor.obj
        (M, (pull l E f).obj ((pull l E g).obj N))) ≫
    (support l E o cfg).map ((calculus l E X).systemClosed.tensor.map
      (Prod.mkHom (𝟙 M) ((c.pullComp f g).inv.app N)))

/-- The right projection word, with exactly the same source and target as leftMap.
Source: the node's displayed composition identity; Stacks 0F7J
(blueprint: lem-pur-system-level-projection-formula-coherence). -/
def rightMap (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) (b : CanonicalBridge l E o)
    (q : ProperOpenCoherence l E o c a b)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))
    (M : System l E X) (N : System l E Z) :=
  (calculus l E Z).systemClosed.tensor.map
      (Prod.mkHom (compositor l E o c a b q cf cg cfg M) (𝟙 N)) ≫
    projection l E o c a cfg M N
```

## New

The new maps module imports `IntegralCompactificationRealizationData` and
`WeilConjectures.Compactification.Triangle`, the interfaces those definitions use.

The declarations above are in `Sheaf.Paper.SystemProjectionFormulaMaps`, in
the same namespace and with the same section parameters and options. Eight bodies
are unchanged. To prevent type checking the algebraic word from unfolding the large
canonical compactification construction, compositor now calls compositorAlong with
that same canonical triangle. The new helper has exactly the old four factors:

```lean
def compositorAlong (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) (b : CanonicalBridge l E o)
    (q : ProperOpenCoherence l E o c a b)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))
    (T : Compactification.Triangle f g) (M : System l E X) :
    (support l E o cg).obj ((support l E o cf).obj M) ⟶ (support l E o cfg).obj M :=
  (support l E o cg).map (change l E o c a b q cf T.cf M) ≫
    change l E o c a b q cg T.cg ((support l E o T.cf).obj M) ≫
    (triangleWord l E o c a b q T).app M ≫ change l E o c a b q T.cfg cfg M

/-- The specified geometric compositor for arbitrary supplied compactifications.
The auxiliary triangle and all three transports are canonical geometric constructions.
Source: Stacks 0F7J; thm-sf-comp-composition in simultaneous section models
(blueprint: def-pur-system-projection-formula-maps). -/
def compositor (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) (b : CanonicalBridge l E o)
    (q : ProperOpenCoherence l E o c a b)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))
    (M : System l E X) :
    (support l E o cg).obj ((support l E o cf).obj M) ⟶ (support l E o cfg).obj M :=
  letI := cg.hasCompactification
  letI := cfg.hasCompactification
  compositorAlong l E o c a b q cf cg cfg
    (Compactification.Triangle.ofHasCompactification f g) M
```

Unfolding compositorAlong recovers the old compositor body definitionally. This
introduces no additional choice, no hypothesis, and no change of the maps. The
calculation is proved for a triangle parameter in the original module, then
specialized; no source-library module is modified and no module is split for timing.
Only docstring blueprint attachments now name the new maps node. The original
module adds:

```lean
public import Sheaf.Paper.SystemProjectionFormulaMaps
```

Its two theorem signatures, existing joint naturality signature, and all remaining
finite-map definitions are unchanged. Its DAG attachment retains those declarations;
the extracted definitions attach to the new definition node. The node's `stmt_deps`
adds that node to record the extracted definitions it uses.

## Users

`tools/downstream.py Sheaf.Paper.SystemProjectionFormulaCoherence` reports these two
consumers. Reading their actual uses shows that public reexport preserves their types
and unfolding equations; no adaptation is necessary.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ExceptionalRefinementMates | unclaimed | Uses support, inverseOnDomain and refinement; identical definitions remain public. |
| Sheaf.Paper.SystemScalarProjectionIdentification | V8 | Uses inverseOnDomain; identical definition remains public. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | U6 | Public reexport; proof uses extracted words unchanged. |

The two new proof modules publicly import the maps module for their statement types.
They do not change any existing consumer or statement.

## Status

landed 20261025T213040-L-278775 2026-10-25 (merge of deliver/U6/Sheaf.Paper.SystemProjectionFormulaCoherence)
