# projectionSystemPushIdentity, projectionSystemPullIdentity, projectionSystemSupportIdentity, projectionSystemCompositor, projectionSystemRefinement, ProjectionCoherenceRoutes

## Reason

The integral realization proof needs the generating system equations before applying total
limit. Move its five concrete comparison definitions and its route inductive into a module
that states those equations, avoiding a circular import. The original module publicly imports
the new module, preserving all six public names. There is no mathematical definition or
statement change: signatures, universes, instances, constructors, attributes and data bodies
are unchanged. Only blueprint docstring references identify their new attachment.
Both original theorem signatures remain byte-identical. No target meaning changes.

## Old

Location: lean/Sheaf/SixFunctors/ProjectionIntegralCoherenceRealization.lean.

```lean
/-- The specified identity comparison for system direct image, through the canonical
sectionwise bridge. Source: Stacks 07A7; integral coherence, proof step 4
(blueprint: lem-sf-projection-integral-coherence-realization). -/
def projectionSystemPushIdentity (o : Operations l E) (b : CanonicalBridge l E o)
    (W : Scheme.{u}) : Operations.push l E o (𝟙 W) ≅ 𝟭 (System l E W) :=
  b.push l E (𝟙 W) ≪≫
    ProEtale.SemilinearProperOpen.sId (scalarRings l E) (scalarTransitions l E) W

/-- The specified pullback identity. Source: Stacks 07A7; integral coherence, step 4
(blueprint: lem-sf-projection-integral-coherence-realization). -/
def projectionSystemPullIdentity (o : Operations l E) (b : CanonicalBridge l E o)
    (W : Scheme.{u}) : pull l E (𝟙 W) ≅ 𝟭 (System l E W) :=
  b.pull l E (𝟙 W) ≪≫
    ProEtale.SemilinearProperOpen.pId (scalarRings l E) (scalarTransitions l E) W

/-- Identity compact support is open identity followed by proper identity, with their
specified normalizations. Source: integral coherence, proof step 4
(blueprint: lem-sf-projection-integral-coherence-realization). -/
def projectionSystemSupportIdentity (o : Operations l E) (b : CanonicalBridge l E o)
    (W : Scheme.{u}) :
    Operations.shriek l E o (𝟙 W) ⋙ Operations.push l E o (𝟙 W) ≅
      𝟭 (System l E W) :=
  Functor.isoWhiskerRight
    (b.shriek l E (𝟙 W) ≪≫
      ProEtale.SemilinearProperOpen.jId (scalarRings l E) (scalarTransitions l E) W) _ ≪≫
    Functor.leftUnitor _ ≪≫ projectionSystemPushIdentity l E o b W

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The raw binary compact-support compositor: the actual proper/open map, followed
by the proper and open compositors. No invertibility of this raw map is assumed.
Source: integral coherence, step 4; lem-sf-projection-compatible-triangle-assembly
(blueprint: lem-sf-projection-integral-coherence-realization). -/
def projectionSystemCompositor (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) (b : CanonicalBridge l E o)
    (q : ProperOpenCoherence l E o c a b)
    {B : Scheme.{u}} {U V W : Over B} {f : U ⟶ V} {g : V ⟶ W}
    (cf : Compactification f.left) (cg : Compactification g.left)
    (d : Compactification (cf.overG ≫ cg.overI).left)
    [QuasiCompact cf.i] [QuasiCompact cg.i] [QuasiCompact d.i]
    (M : System l E U.left) :
    (Operations.shriek l E o cg.i ⋙ Operations.push l E o cg.g).obj
      ((Operations.shriek l E o cf.i ⋙ Operations.push l E o cf.g).obj M) ⟶
    (Operations.shriek l E o (Compactification.overComp cf cg d).i ⋙
      Operations.push l E o (Compactification.overComp cf cg d).g).obj M :=
  letI : IsOpenImmersion cf.i := cf.isOpenImmersion
  letI : IsOpenImmersion cg.i := cg.isOpenImmersion
  letI : IsOpenImmersion d.i := d.isOpenImmersion
  (Operations.push l E o cg.g).map
      ((q.gamma d.i cf.g d.g cg.i d.comm.symm).app
        ((Operations.shriek l E o cf.i).obj M)) ≫
    (c.pushComp l E d.g cg.g).hom.app
      ((Operations.shriek l E o d.i).obj ((Operations.shriek l E o cf.i).obj M)) ≫
    (Operations.push l E o (d.g ≫ cg.g)).map
      ((c.openComp l E cf.i d.i).hom.app M)

/-- The directed refinement map, using the inverse of the actual non-Cartesian
proper/open comparison, direct-image composition, and the normalized identity image.
The two inverse witnesses specify only the inverses that occur in this construction.
Source: integral coherence, step 4; lem-sf-projection-refinement-descent
(blueprint: lem-sf-projection-integral-coherence-realization). -/
def projectionSystemRefinement (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) (b : CanonicalBridge l E o)
    (q : ProperOpenCoherence l E o c a b)
    {U V : Scheme.{u}} {f : U ⟶ V}
    (c₁ c₂ : Compactification f) (v : c₁.Refinement c₂)
    [QuasiCompact c₁.i] [QuasiCompact c₂.i]
    (w : c₁.i ≫ v.hom = (𝟙 U) ≫ c₂.i) (M : System l E U)
    (hM : IsIso ((q.gamma c₁.i (𝟙 U) v.hom c₂.i w).app M)) :
    (Operations.shriek l E o c₁.i ⋙ Operations.push l E o c₁.g).obj M ⟶
      (Operations.shriek l E o c₂.i ⋙ Operations.push l E o c₂.g).obj M :=
  eqToHom (congrArg (fun z : c₁.Z ⟶ V ↦
      (Operations.push l E o z).obj ((Operations.shriek l E o c₁.i).obj M))
        v.hom_g.symm) ≫
    (c.pushComp l E v.hom c₂.g).inv.app ((Operations.shriek l E o c₁.i).obj M) ≫
    (Operations.push l E o c₂.g).map
      (@inv _ _ _ _ ((q.gamma c₁.i (𝟙 U) v.hom c₂.i w).app M) hM ≫
        (Operations.shriek l E o c₂.i).map
          ((projectionSystemPushIdentity l E o b U).hom.app M))

/-- The concrete system equations whose integral realizations are asserted below.
Each constructor fixes both routes by formulas in the published operations; none
accepts an equality of system maps. Context constructors retain the actual functors.
The three-cell constructor is the expanded binary-compositor associativity equation;
its contextual and transitive closure includes the nested associativity pentagon.
Source: integral coherence, proof step 4 and its five cited system lemmas
(blueprint: lem-sf-projection-integral-coherence-realization). -/
inductive ProjectionCoherenceRoutes (D : FiniteFieldDatum.{u}) (o : Operations l E)
    (ρ : Realizations l E D o) : {W : Scheme.{u}} → {A B : System l E W} →
    (A ⟶ B) → (A ⟶ B) → Prop where
  | composition {U V W : Over (Spec (CommRingCat.of D.k))}
      (f : U ⟶ V) (g : V ⟶ W)
      (cf : Compactification f.left) (cg : Compactification g.left)
      (d : Compactification (cf.overG ≫ cg.overI).left)
      [QuasiCompact cf.i] [QuasiCompact cg.i] [QuasiCompact d.i]
      (_sq : IsPullback cf.g d.i cg.i d.g)
      (M : System l E U.left) (N : System l E W.left) :
    ProjectionCoherenceRoutes D o ρ
      (compactificationProjection l E o ρ.compositors ρ.openComparisons cg
          ((Operations.shriek l E o cf.i ⋙ Operations.push l E o cf.g).obj M) N ≫
        (Operations.shriek l E o cg.i ⋙ Operations.push l E o cg.g).map
          (compactificationProjection l E o ρ.compositors ρ.openComparisons cf M
            ((pull l E g.left).obj N)) ≫
        projectionSystemCompositor l E o ρ.compositors ρ.openComparisons
          ρ.canonicalBridge ρ.properOpen cf cg d
          ((calculus l E U.left).systemClosed.tensor.obj
            (M, (pull l E f.left).obj ((pull l E g.left).obj N))) ≫
        (Operations.shriek l E o (Compactification.overComp cf cg d).i ⋙
          Operations.push l E o (Compactification.overComp cf cg d).g).map
          ((calculus l E U.left).systemClosed.tensor.map
            (Prod.mkHom (𝟙 M) ((ρ.compositors.pullComp f.left g.left).inv.app N))))
      ((calculus l E W.left).systemClosed.tensor.map
          (Prod.mkHom (projectionSystemCompositor l E o ρ.compositors ρ.openComparisons
            ρ.canonicalBridge ρ.properOpen cf cg d M) (𝟙 N)) ≫
        compactificationProjection l E o ρ.compositors ρ.openComparisons
          (Compactification.overComp cf cg d) M N)
  | properOpen {U V W Z : Over (Spec (CommRingCat.of D.k))}
      (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
      [IsOpenImmersion k.left] [IsOpenImmersion i.left]
      [QuasiCompact k.left] [QuasiCompact i.left]
      [IsProper r.left] [IsProper p.left]
      (h : k.left ≫ p.left = r.left ≫ i.left)
      (M : System l E U.left) (N : System l E Z.left) :
    ProjectionCoherenceRoutes D o ρ
      ((ρ.openComparisons.projection i.left).hom.app
          ((Operations.push l E o r.left).obj M, N) ≫
        (Operations.shriek l E o i.left).map
          (((properProjection l E o r.left).app M).app ((pull l E i.left).obj N)) ≫
        (Operations.shriek l E o i.left).map ((Operations.push l E o r.left).map
          ((calculus l E U.left).systemClosed.tensor.map
            (Prod.mkHom (𝟙 M) ((ρ.compositors.square l E k.left r.left p.left i.left h).hom.app
              N)))) ≫
        (ρ.properOpen.gamma k.left r.left p.left i.left h).app
          ((calculus l E U.left).systemClosed.tensor.obj
            (M, (pull l E k.left).obj ((pull l E p.left).obj N))))
      ((calculus l E Z.left).systemClosed.tensor.map
          (Prod.mkHom ((ρ.properOpen.gamma k.left r.left p.left i.left h).app M) (𝟙 N)) ≫
        ((properProjection l E o p.left).app
          ((Operations.shriek l E o k.left).obj M)).app N ≫
        (Operations.push l E o p.left).map
          ((ρ.openComparisons.projection k.left).hom.app (M, (pull l E p.left).obj N)))
  | refinement {U V : Over (Spec (CommRingCat.of D.k))} (f : U ⟶ V)
      (c₁ c₂ : Compactification f.left) (v : c₁.Refinement c₂)
      [QuasiCompact c₁.i] [QuasiCompact c₂.i]
      (w : c₁.i ≫ v.hom = (𝟙 U.left) ≫ c₂.i)
      (M : System l E U.left) (N : System l E V.left)
      (hM : IsIso ((ρ.properOpen.gamma c₁.i (𝟙 U.left) v.hom c₂.i w).app M))
      (hT : IsIso ((ρ.properOpen.gamma c₁.i (𝟙 U.left) v.hom c₂.i w).app
        ((calculus l E U.left).systemClosed.tensor.obj (M, (pull l E f.left).obj N)))) :
    ProjectionCoherenceRoutes D o ρ
      (compactificationProjection l E o ρ.compositors ρ.openComparisons c₁ M N ≫
        projectionSystemRefinement l E o ρ.compositors ρ.openComparisons
          ρ.canonicalBridge ρ.properOpen c₁ c₂ v w
          ((calculus l E U.left).systemClosed.tensor.obj (M, (pull l E f.left).obj N)) hT)
      ((calculus l E V.left).systemClosed.tensor.map
          (Prod.mkHom (projectionSystemRefinement l E o ρ.compositors ρ.openComparisons
            ρ.canonicalBridge ρ.properOpen c₁ c₂ v w M hM) (𝟙 N)) ≫
        compactificationProjection l E o ρ.compositors ρ.openComparisons c₂ M N)
  | identity (W : Over (Spec (CommRingCat.of D.k)))
      (M N : System l E W.left) :
    ProjectionCoherenceRoutes D o ρ
      (compactificationProjection l E o ρ.compositors ρ.openComparisons
        (Compactification.ofIsProper (𝟙 W.left)) M N)
      ((calculus l E W.left).systemClosed.tensor.map
          (Prod.mkHom ((projectionSystemSupportIdentity l E o ρ.canonicalBridge W.left).hom.app
            M) (𝟙 N)) ≫
        (calculus l E W.left).systemClosed.tensor.map
          (Prod.mkHom (𝟙 M)
            ((projectionSystemPullIdentity l E o ρ.canonicalBridge W.left).inv.app N)) ≫
        (projectionSystemSupportIdentity l E o ρ.canonicalBridge W.left).inv.app
          ((calculus l E W.left).systemClosed.tensor.obj
            (M, (pull l E (𝟙 W.left)).obj N)))
  | vertical {A C F B V H : Over (Spec (CommRingCat.of D.k))}
      (k : A ⟶ B) (i : C ⟶ V) (j : F ⟶ H)
      (r₁ : A ⟶ C) (r₂ : C ⟶ F) (p₁ : B ⟶ V) (p₂ : V ⟶ H)
      [IsOpenImmersion k.left] [IsOpenImmersion i.left] [IsOpenImmersion j.left]
      [QuasiCompact k.left] [QuasiCompact i.left] [QuasiCompact j.left]
      [IsProper r₁.left] [IsProper r₂.left] [IsProper p₁.left] [IsProper p₂.left]
      (h₁ : k.left ≫ p₁.left = r₁.left ≫ i.left)
      (h₂ : i.left ≫ p₂.left = r₂.left ≫ j.left)
      (h : k.left ≫ (p₁.left ≫ p₂.left) = (r₁.left ≫ r₂.left) ≫ j.left)
      (M : System l E A.left) :
    ProjectionCoherenceRoutes D o ρ
      ((Operations.shriek l E o j.left).map
          ((ρ.compositors.pushComp l E r₁.left r₂.left).hom.app M) ≫
        (ρ.properOpen.gamma k.left (r₁.left ≫ r₂.left) (p₁.left ≫ p₂.left) j.left h).app
          M ≫
        (ρ.compositors.pushComp l E p₁.left p₂.left).inv.app
          ((Operations.shriek l E o k.left).obj M))
      ((ρ.properOpen.gamma i.left r₂.left p₂.left j.left h₂).app
          ((Operations.push l E o r₁.left).obj M) ≫
        (Operations.push l E o p₂.left).map
          ((ρ.properOpen.gamma k.left r₁.left p₁.left i.left h₁).app M))
  | horizontal {A C F B V H : Over (Spec (CommRingCat.of D.k))}
      (k : A ⟶ B) (ll : B ⟶ F) (i : C ⟶ V) (j : V ⟶ H)
      (r : A ⟶ C) (p : B ⟶ V) (q : F ⟶ H)
      [IsOpenImmersion k.left] [IsOpenImmersion ll.left]
      [IsOpenImmersion i.left] [IsOpenImmersion j.left]
      [QuasiCompact k.left] [QuasiCompact ll.left]
      [QuasiCompact i.left] [QuasiCompact j.left]
      [IsProper r.left] [IsProper p.left] [IsProper q.left]
      (h₁ : k.left ≫ p.left = r.left ≫ i.left)
      (h₂ : ll.left ≫ q.left = p.left ≫ j.left)
      (h : (k.left ≫ ll.left) ≫ q.left = r.left ≫ (i.left ≫ j.left))
      (M : System l E A.left) :
    ProjectionCoherenceRoutes D o ρ
      ((ρ.compositors.openComp l E i.left j.left).hom.app
          ((Operations.push l E o r.left).obj M) ≫
        (ρ.properOpen.gamma (k.left ≫ ll.left) r.left q.left (i.left ≫ j.left) h).app M ≫
        (Operations.push l E o q.left).map
          ((ρ.compositors.openComp l E k.left ll.left).inv.app M))
      ((Operations.shriek l E o j.left).map
          ((ρ.properOpen.gamma k.left r.left p.left i.left h₁).app M) ≫
        (ρ.properOpen.gamma ll.left p.left q.left j.left h₂).app
          ((Operations.shriek l E o k.left).obj M))
  | threeCell {U V X Y W Z T H : Over (Spec (CommRingCat.of D.k))}
      (a : U ⟶ V) (b : V ⟶ X) (d : Y ⟶ W) (k : W ⟶ Z) (i : T ⟶ H)
      (m : U ⟶ Y) (r : V ⟶ W) (p : X ⟶ Z) (q : W ⟶ T) (v : Z ⟶ H)
      [IsOpenImmersion a.left] [IsOpenImmersion b.left]
      [IsOpenImmersion d.left] [IsOpenImmersion k.left] [IsOpenImmersion i.left]
      [QuasiCompact a.left] [QuasiCompact b.left]
      [QuasiCompact d.left] [QuasiCompact k.left] [QuasiCompact i.left]
      [IsProper m.left] [IsProper r.left] [IsProper p.left]
      [IsProper q.left] [IsProper v.left]
      (ha : a.left ≫ r.left = m.left ≫ d.left)
      (hb : b.left ≫ p.left = r.left ≫ k.left)
      (hc : k.left ≫ v.left = q.left ≫ i.left)
      (_sa : IsPullback a.left m.left r.left d.left)
      (_sb : IsPullback b.left r.left p.left k.left)
      (_sc : IsPullback k.left q.left v.left i.left)
      (M : System l E U.left) :
    ProjectionCoherenceRoutes D o ρ
      ((Operations.shriek l E o i.left).map ((Operations.push l E o q.left).map
          ((ρ.properOpen.gamma a.left m.left r.left d.left ha).app M)) ≫
        (ρ.properOpen.gamma k.left q.left v.left i.left hc).app
          ((Operations.push l E o r.left).obj ((Operations.shriek l E o a.left).obj M)) ≫
        (Operations.push l E o v.left).map
          ((ρ.properOpen.gamma b.left r.left p.left k.left hb).app
            ((Operations.shriek l E o a.left).obj M)))
      ((ρ.properOpen.gamma k.left q.left v.left i.left hc).app
          ((Operations.shriek l E o d.left).obj ((Operations.push l E o m.left).obj M)) ≫
        (Operations.push l E o v.left).map ((Operations.shriek l E o k.left).map
          ((ρ.properOpen.gamma a.left m.left r.left d.left ha).app M)) ≫
        (Operations.push l E o v.left).map
          ((ρ.properOpen.gamma b.left r.left p.left k.left hb).app
            ((Operations.shriek l E o a.left).obj M)))
  | refl {W : Scheme.{u}} {A B : System l E W} (s : A ⟶ B) :
      ProjectionCoherenceRoutes D o ρ s s
  | symm {W : Scheme.{u}} {A B : System l E W} {s t : A ⟶ B} :
      ProjectionCoherenceRoutes D o ρ s t → ProjectionCoherenceRoutes D o ρ t s
  | trans {W : Scheme.{u}} {A B : System l E W} {s t v : A ⟶ B} :
      ProjectionCoherenceRoutes D o ρ s t → ProjectionCoherenceRoutes D o ρ t v →
        ProjectionCoherenceRoutes D o ρ s v
  | comp {W : Scheme.{u}} {A B C : System l E W}
      {s t : A ⟶ B} {v w : B ⟶ C} :
      ProjectionCoherenceRoutes D o ρ s t → ProjectionCoherenceRoutes D o ρ v w →
        ProjectionCoherenceRoutes D o ρ (s ≫ v) (t ≫ w)
  | pull {U V : Scheme.{u}} (f : U ⟶ V) {A B : System l E V} {s t : A ⟶ B} :
      ProjectionCoherenceRoutes D o ρ s t →
        ProjectionCoherenceRoutes D o ρ ((pull l E f).map s) ((pull l E f).map t)
  | push {U V : Scheme.{u}} (f : U ⟶ V) {A B : System l E U} {s t : A ⟶ B} :
      ProjectionCoherenceRoutes D o ρ s t →
        ProjectionCoherenceRoutes D o ρ
          ((Operations.push l E o f).map s) ((Operations.push l E o f).map t)
  | shriek {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j]
      {A B : System l E U} {s t : A ⟶ B} :
      ProjectionCoherenceRoutes D o ρ s t →
        ProjectionCoherenceRoutes D o ρ
          ((Operations.shriek l E o j).map s) ((Operations.shriek l E o j).map t)
  | compactSupport {U V : Scheme.{u}} {f : U ⟶ V} (cf : Compactification f)
      {A B : System l E U} {s t : A ⟶ B} :
      ProjectionCoherenceRoutes D o ρ s t → ProjectionCoherenceRoutes D o ρ
        ((Operations.shriek l E o cf.i ⋙ Operations.push l E o cf.g).map s)
        ((Operations.shriek l E o cf.i ⋙ Operations.push l E o cf.g).map t)
  | tensor {W : Scheme.{u}} {A B C F : System l E W} {s t : A ⟶ B} {v w : C ⟶ F} :
      ProjectionCoherenceRoutes D o ρ s t → ProjectionCoherenceRoutes D o ρ v w →
        ProjectionCoherenceRoutes D o ρ
          ((calculus l E W).systemClosed.tensor.map (Prod.mkHom s v))
          ((calculus l E W).systemClosed.tensor.map (Prod.mkHom t w))
```

## New

Location: lean/Sheaf/SixFunctors/ProjectionSystemCoherence.lean, publicly reexported by
lean/Sheaf/SixFunctors/ProjectionIntegralCoherenceRealization.lean.

```lean
/-- The specified identity comparison for system direct image, through the canonical
sectionwise bridge. Source: Stacks 07A7; integral coherence, proof step 4
(blueprint: lem-sf-projection-system-generating-equations). -/
def projectionSystemPushIdentity (o : Operations l E) (b : CanonicalBridge l E o)
    (W : Scheme.{u}) : Operations.push l E o (𝟙 W) ≅ 𝟭 (System l E W) :=
  b.push l E (𝟙 W) ≪≫
    ProEtale.SemilinearProperOpen.sId (scalarRings l E) (scalarTransitions l E) W

/-- The specified pullback identity. Source: Stacks 07A7; integral coherence, step 4
(blueprint: lem-sf-projection-system-generating-equations). -/
def projectionSystemPullIdentity (o : Operations l E) (b : CanonicalBridge l E o)
    (W : Scheme.{u}) : pull l E (𝟙 W) ≅ 𝟭 (System l E W) :=
  b.pull l E (𝟙 W) ≪≫
    ProEtale.SemilinearProperOpen.pId (scalarRings l E) (scalarTransitions l E) W

/-- Identity compact support is open identity followed by proper identity, with their
specified normalizations. Source: integral coherence, proof step 4
(blueprint: lem-sf-projection-system-generating-equations). -/
def projectionSystemSupportIdentity (o : Operations l E) (b : CanonicalBridge l E o)
    (W : Scheme.{u}) :
    Operations.shriek l E o (𝟙 W) ⋙ Operations.push l E o (𝟙 W) ≅
      𝟭 (System l E W) :=
  Functor.isoWhiskerRight
    (b.shriek l E (𝟙 W) ≪≫
      ProEtale.SemilinearProperOpen.jId (scalarRings l E) (scalarTransitions l E) W) _ ≪≫
    Functor.leftUnitor _ ≪≫ projectionSystemPushIdentity l E o b W

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The raw binary compact-support compositor: the actual proper/open map, followed
by the proper and open compositors. No invertibility of this raw map is assumed.
Source: integral coherence, step 4; lem-sf-projection-compatible-triangle-assembly
(blueprint: lem-sf-projection-system-generating-equations). -/
def projectionSystemCompositor (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) (b : CanonicalBridge l E o)
    (q : ProperOpenCoherence l E o c a b)
    {B : Scheme.{u}} {U V W : Over B} {f : U ⟶ V} {g : V ⟶ W}
    (cf : Compactification f.left) (cg : Compactification g.left)
    (d : Compactification (cf.overG ≫ cg.overI).left)
    [QuasiCompact cf.i] [QuasiCompact cg.i] [QuasiCompact d.i]
    (M : System l E U.left) :
    (Operations.shriek l E o cg.i ⋙ Operations.push l E o cg.g).obj
      ((Operations.shriek l E o cf.i ⋙ Operations.push l E o cf.g).obj M) ⟶
    (Operations.shriek l E o (Compactification.overComp cf cg d).i ⋙
      Operations.push l E o (Compactification.overComp cf cg d).g).obj M :=
  letI : IsOpenImmersion cf.i := cf.isOpenImmersion
  letI : IsOpenImmersion cg.i := cg.isOpenImmersion
  letI : IsOpenImmersion d.i := d.isOpenImmersion
  (Operations.push l E o cg.g).map
      ((q.gamma d.i cf.g d.g cg.i d.comm.symm).app
        ((Operations.shriek l E o cf.i).obj M)) ≫
    (c.pushComp l E d.g cg.g).hom.app
      ((Operations.shriek l E o d.i).obj ((Operations.shriek l E o cf.i).obj M)) ≫
    (Operations.push l E o (d.g ≫ cg.g)).map
      ((c.openComp l E cf.i d.i).hom.app M)

/-- The directed refinement map, using the inverse of the actual non-Cartesian
proper/open comparison, direct-image composition, and the normalized identity image.
The two inverse witnesses specify only the inverses that occur in this construction.
Source: integral coherence, step 4; lem-sf-projection-refinement-descent
(blueprint: lem-sf-projection-system-generating-equations). -/
def projectionSystemRefinement (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) (b : CanonicalBridge l E o)
    (q : ProperOpenCoherence l E o c a b)
    {U V : Scheme.{u}} {f : U ⟶ V}
    (c₁ c₂ : Compactification f) (v : c₁.Refinement c₂)
    [QuasiCompact c₁.i] [QuasiCompact c₂.i]
    (w : c₁.i ≫ v.hom = (𝟙 U) ≫ c₂.i) (M : System l E U)
    (hM : IsIso ((q.gamma c₁.i (𝟙 U) v.hom c₂.i w).app M)) :
    (Operations.shriek l E o c₁.i ⋙ Operations.push l E o c₁.g).obj M ⟶
      (Operations.shriek l E o c₂.i ⋙ Operations.push l E o c₂.g).obj M :=
  eqToHom (congrArg (fun z : c₁.Z ⟶ V ↦
      (Operations.push l E o z).obj ((Operations.shriek l E o c₁.i).obj M))
        v.hom_g.symm) ≫
    (c.pushComp l E v.hom c₂.g).inv.app ((Operations.shriek l E o c₁.i).obj M) ≫
    (Operations.push l E o c₂.g).map
      (@inv _ _ _ _ ((q.gamma c₁.i (𝟙 U) v.hom c₂.i w).app M) hM ≫
        (Operations.shriek l E o c₂.i).map
          ((projectionSystemPushIdentity l E o b U).hom.app M))

/-- The concrete system equations whose integral realizations are asserted below.
Each constructor fixes both routes by formulas in the published operations; none
accepts an equality of system maps. Context constructors retain the actual functors.
The three-cell constructor is the expanded binary-compositor associativity equation;
its contextual and transitive closure includes the nested associativity pentagon.
Source: integral coherence, proof step 4 and its five cited system lemmas
(blueprint: lem-sf-projection-system-generating-equations). -/
inductive ProjectionCoherenceRoutes (D : FiniteFieldDatum.{u}) (o : Operations l E)
    (ρ : Realizations l E D o) : {W : Scheme.{u}} → {A B : System l E W} →
    (A ⟶ B) → (A ⟶ B) → Prop where
  | composition {U V W : Over (Spec (CommRingCat.of D.k))}
      (f : U ⟶ V) (g : V ⟶ W)
      (cf : Compactification f.left) (cg : Compactification g.left)
      (d : Compactification (cf.overG ≫ cg.overI).left)
      [QuasiCompact cf.i] [QuasiCompact cg.i] [QuasiCompact d.i]
      (_sq : IsPullback cf.g d.i cg.i d.g)
      (M : System l E U.left) (N : System l E W.left) :
    ProjectionCoherenceRoutes D o ρ
      (compactificationProjection l E o ρ.compositors ρ.openComparisons cg
          ((Operations.shriek l E o cf.i ⋙ Operations.push l E o cf.g).obj M) N ≫
        (Operations.shriek l E o cg.i ⋙ Operations.push l E o cg.g).map
          (compactificationProjection l E o ρ.compositors ρ.openComparisons cf M
            ((pull l E g.left).obj N)) ≫
        projectionSystemCompositor l E o ρ.compositors ρ.openComparisons
          ρ.canonicalBridge ρ.properOpen cf cg d
          ((calculus l E U.left).systemClosed.tensor.obj
            (M, (pull l E f.left).obj ((pull l E g.left).obj N))) ≫
        (Operations.shriek l E o (Compactification.overComp cf cg d).i ⋙
          Operations.push l E o (Compactification.overComp cf cg d).g).map
          ((calculus l E U.left).systemClosed.tensor.map
            (Prod.mkHom (𝟙 M) ((ρ.compositors.pullComp f.left g.left).inv.app N))))
      ((calculus l E W.left).systemClosed.tensor.map
          (Prod.mkHom (projectionSystemCompositor l E o ρ.compositors ρ.openComparisons
            ρ.canonicalBridge ρ.properOpen cf cg d M) (𝟙 N)) ≫
        compactificationProjection l E o ρ.compositors ρ.openComparisons
          (Compactification.overComp cf cg d) M N)
  | properOpen {U V W Z : Over (Spec (CommRingCat.of D.k))}
      (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
      [IsOpenImmersion k.left] [IsOpenImmersion i.left]
      [QuasiCompact k.left] [QuasiCompact i.left]
      [IsProper r.left] [IsProper p.left]
      (h : k.left ≫ p.left = r.left ≫ i.left)
      (M : System l E U.left) (N : System l E Z.left) :
    ProjectionCoherenceRoutes D o ρ
      ((ρ.openComparisons.projection i.left).hom.app
          ((Operations.push l E o r.left).obj M, N) ≫
        (Operations.shriek l E o i.left).map
          (((properProjection l E o r.left).app M).app ((pull l E i.left).obj N)) ≫
        (Operations.shriek l E o i.left).map ((Operations.push l E o r.left).map
          ((calculus l E U.left).systemClosed.tensor.map
            (Prod.mkHom (𝟙 M) ((ρ.compositors.square l E k.left r.left p.left i.left h).hom.app
              N)))) ≫
        (ρ.properOpen.gamma k.left r.left p.left i.left h).app
          ((calculus l E U.left).systemClosed.tensor.obj
            (M, (pull l E k.left).obj ((pull l E p.left).obj N))))
      ((calculus l E Z.left).systemClosed.tensor.map
          (Prod.mkHom ((ρ.properOpen.gamma k.left r.left p.left i.left h).app M) (𝟙 N)) ≫
        ((properProjection l E o p.left).app
          ((Operations.shriek l E o k.left).obj M)).app N ≫
        (Operations.push l E o p.left).map
          ((ρ.openComparisons.projection k.left).hom.app (M, (pull l E p.left).obj N)))
  | refinement {U V : Over (Spec (CommRingCat.of D.k))} (f : U ⟶ V)
      (c₁ c₂ : Compactification f.left) (v : c₁.Refinement c₂)
      [QuasiCompact c₁.i] [QuasiCompact c₂.i]
      (w : c₁.i ≫ v.hom = (𝟙 U.left) ≫ c₂.i)
      (M : System l E U.left) (N : System l E V.left)
      (hM : IsIso ((ρ.properOpen.gamma c₁.i (𝟙 U.left) v.hom c₂.i w).app M))
      (hT : IsIso ((ρ.properOpen.gamma c₁.i (𝟙 U.left) v.hom c₂.i w).app
        ((calculus l E U.left).systemClosed.tensor.obj (M, (pull l E f.left).obj N)))) :
    ProjectionCoherenceRoutes D o ρ
      (compactificationProjection l E o ρ.compositors ρ.openComparisons c₁ M N ≫
        projectionSystemRefinement l E o ρ.compositors ρ.openComparisons
          ρ.canonicalBridge ρ.properOpen c₁ c₂ v w
          ((calculus l E U.left).systemClosed.tensor.obj (M, (pull l E f.left).obj N)) hT)
      ((calculus l E V.left).systemClosed.tensor.map
          (Prod.mkHom (projectionSystemRefinement l E o ρ.compositors ρ.openComparisons
            ρ.canonicalBridge ρ.properOpen c₁ c₂ v w M hM) (𝟙 N)) ≫
        compactificationProjection l E o ρ.compositors ρ.openComparisons c₂ M N)
  | identity (W : Over (Spec (CommRingCat.of D.k)))
      (M N : System l E W.left) :
    ProjectionCoherenceRoutes D o ρ
      (compactificationProjection l E o ρ.compositors ρ.openComparisons
        (Compactification.ofIsProper (𝟙 W.left)) M N)
      ((calculus l E W.left).systemClosed.tensor.map
          (Prod.mkHom ((projectionSystemSupportIdentity l E o ρ.canonicalBridge W.left).hom.app
            M) (𝟙 N)) ≫
        (calculus l E W.left).systemClosed.tensor.map
          (Prod.mkHom (𝟙 M)
            ((projectionSystemPullIdentity l E o ρ.canonicalBridge W.left).inv.app N)) ≫
        (projectionSystemSupportIdentity l E o ρ.canonicalBridge W.left).inv.app
          ((calculus l E W.left).systemClosed.tensor.obj
            (M, (pull l E (𝟙 W.left)).obj N)))
  | vertical {A C F B V H : Over (Spec (CommRingCat.of D.k))}
      (k : A ⟶ B) (i : C ⟶ V) (j : F ⟶ H)
      (r₁ : A ⟶ C) (r₂ : C ⟶ F) (p₁ : B ⟶ V) (p₂ : V ⟶ H)
      [IsOpenImmersion k.left] [IsOpenImmersion i.left] [IsOpenImmersion j.left]
      [QuasiCompact k.left] [QuasiCompact i.left] [QuasiCompact j.left]
      [IsProper r₁.left] [IsProper r₂.left] [IsProper p₁.left] [IsProper p₂.left]
      (h₁ : k.left ≫ p₁.left = r₁.left ≫ i.left)
      (h₂ : i.left ≫ p₂.left = r₂.left ≫ j.left)
      (h : k.left ≫ (p₁.left ≫ p₂.left) = (r₁.left ≫ r₂.left) ≫ j.left)
      (M : System l E A.left) :
    ProjectionCoherenceRoutes D o ρ
      ((Operations.shriek l E o j.left).map
          ((ρ.compositors.pushComp l E r₁.left r₂.left).hom.app M) ≫
        (ρ.properOpen.gamma k.left (r₁.left ≫ r₂.left) (p₁.left ≫ p₂.left) j.left h).app
          M ≫
        (ρ.compositors.pushComp l E p₁.left p₂.left).inv.app
          ((Operations.shriek l E o k.left).obj M))
      ((ρ.properOpen.gamma i.left r₂.left p₂.left j.left h₂).app
          ((Operations.push l E o r₁.left).obj M) ≫
        (Operations.push l E o p₂.left).map
          ((ρ.properOpen.gamma k.left r₁.left p₁.left i.left h₁).app M))
  | horizontal {A C F B V H : Over (Spec (CommRingCat.of D.k))}
      (k : A ⟶ B) (ll : B ⟶ F) (i : C ⟶ V) (j : V ⟶ H)
      (r : A ⟶ C) (p : B ⟶ V) (q : F ⟶ H)
      [IsOpenImmersion k.left] [IsOpenImmersion ll.left]
      [IsOpenImmersion i.left] [IsOpenImmersion j.left]
      [QuasiCompact k.left] [QuasiCompact ll.left]
      [QuasiCompact i.left] [QuasiCompact j.left]
      [IsProper r.left] [IsProper p.left] [IsProper q.left]
      (h₁ : k.left ≫ p.left = r.left ≫ i.left)
      (h₂ : ll.left ≫ q.left = p.left ≫ j.left)
      (h : (k.left ≫ ll.left) ≫ q.left = r.left ≫ (i.left ≫ j.left))
      (M : System l E A.left) :
    ProjectionCoherenceRoutes D o ρ
      ((ρ.compositors.openComp l E i.left j.left).hom.app
          ((Operations.push l E o r.left).obj M) ≫
        (ρ.properOpen.gamma (k.left ≫ ll.left) r.left q.left (i.left ≫ j.left) h).app M ≫
        (Operations.push l E o q.left).map
          ((ρ.compositors.openComp l E k.left ll.left).inv.app M))
      ((Operations.shriek l E o j.left).map
          ((ρ.properOpen.gamma k.left r.left p.left i.left h₁).app M) ≫
        (ρ.properOpen.gamma ll.left p.left q.left j.left h₂).app
          ((Operations.shriek l E o k.left).obj M))
  | threeCell {U V X Y W Z T H : Over (Spec (CommRingCat.of D.k))}
      (a : U ⟶ V) (b : V ⟶ X) (d : Y ⟶ W) (k : W ⟶ Z) (i : T ⟶ H)
      (m : U ⟶ Y) (r : V ⟶ W) (p : X ⟶ Z) (q : W ⟶ T) (v : Z ⟶ H)
      [IsOpenImmersion a.left] [IsOpenImmersion b.left]
      [IsOpenImmersion d.left] [IsOpenImmersion k.left] [IsOpenImmersion i.left]
      [QuasiCompact a.left] [QuasiCompact b.left]
      [QuasiCompact d.left] [QuasiCompact k.left] [QuasiCompact i.left]
      [IsProper m.left] [IsProper r.left] [IsProper p.left]
      [IsProper q.left] [IsProper v.left]
      (ha : a.left ≫ r.left = m.left ≫ d.left)
      (hb : b.left ≫ p.left = r.left ≫ k.left)
      (hc : k.left ≫ v.left = q.left ≫ i.left)
      (_sa : IsPullback a.left m.left r.left d.left)
      (_sb : IsPullback b.left r.left p.left k.left)
      (_sc : IsPullback k.left q.left v.left i.left)
      (M : System l E U.left) :
    ProjectionCoherenceRoutes D o ρ
      ((Operations.shriek l E o i.left).map ((Operations.push l E o q.left).map
          ((ρ.properOpen.gamma a.left m.left r.left d.left ha).app M)) ≫
        (ρ.properOpen.gamma k.left q.left v.left i.left hc).app
          ((Operations.push l E o r.left).obj ((Operations.shriek l E o a.left).obj M)) ≫
        (Operations.push l E o v.left).map
          ((ρ.properOpen.gamma b.left r.left p.left k.left hb).app
            ((Operations.shriek l E o a.left).obj M)))
      ((ρ.properOpen.gamma k.left q.left v.left i.left hc).app
          ((Operations.shriek l E o d.left).obj ((Operations.push l E o m.left).obj M)) ≫
        (Operations.push l E o v.left).map ((Operations.shriek l E o k.left).map
          ((ρ.properOpen.gamma a.left m.left r.left d.left ha).app M)) ≫
        (Operations.push l E o v.left).map
          ((ρ.properOpen.gamma b.left r.left p.left k.left hb).app
            ((Operations.shriek l E o a.left).obj M)))
  | refl {W : Scheme.{u}} {A B : System l E W} (s : A ⟶ B) :
      ProjectionCoherenceRoutes D o ρ s s
  | symm {W : Scheme.{u}} {A B : System l E W} {s t : A ⟶ B} :
      ProjectionCoherenceRoutes D o ρ s t → ProjectionCoherenceRoutes D o ρ t s
  | trans {W : Scheme.{u}} {A B : System l E W} {s t v : A ⟶ B} :
      ProjectionCoherenceRoutes D o ρ s t → ProjectionCoherenceRoutes D o ρ t v →
        ProjectionCoherenceRoutes D o ρ s v
  | comp {W : Scheme.{u}} {A B C : System l E W}
      {s t : A ⟶ B} {v w : B ⟶ C} :
      ProjectionCoherenceRoutes D o ρ s t → ProjectionCoherenceRoutes D o ρ v w →
        ProjectionCoherenceRoutes D o ρ (s ≫ v) (t ≫ w)
  | pull {U V : Scheme.{u}} (f : U ⟶ V) {A B : System l E V} {s t : A ⟶ B} :
      ProjectionCoherenceRoutes D o ρ s t →
        ProjectionCoherenceRoutes D o ρ ((pull l E f).map s) ((pull l E f).map t)
  | push {U V : Scheme.{u}} (f : U ⟶ V) {A B : System l E U} {s t : A ⟶ B} :
      ProjectionCoherenceRoutes D o ρ s t →
        ProjectionCoherenceRoutes D o ρ
          ((Operations.push l E o f).map s) ((Operations.push l E o f).map t)
  | shriek {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j]
      {A B : System l E U} {s t : A ⟶ B} :
      ProjectionCoherenceRoutes D o ρ s t →
        ProjectionCoherenceRoutes D o ρ
          ((Operations.shriek l E o j).map s) ((Operations.shriek l E o j).map t)
  | compactSupport {U V : Scheme.{u}} {f : U ⟶ V} (cf : Compactification f)
      {A B : System l E U} {s t : A ⟶ B} :
      ProjectionCoherenceRoutes D o ρ s t → ProjectionCoherenceRoutes D o ρ
        ((Operations.shriek l E o cf.i ⋙ Operations.push l E o cf.g).map s)
        ((Operations.shriek l E o cf.i ⋙ Operations.push l E o cf.g).map t)
  | tensor {W : Scheme.{u}} {A B C F : System l E W} {s t : A ⟶ B} {v w : C ⟶ F} :
      ProjectionCoherenceRoutes D o ρ s t → ProjectionCoherenceRoutes D o ρ v w →
        ProjectionCoherenceRoutes D o ρ
          ((calculus l E W).systemClosed.tensor.map (Prod.mkHom s v))
          ((calculus l E W).systemClosed.tensor.map (Prod.mkHom t w))
```

## Users

Each of the six downstream.py --uses checks reports zero downstream modules and only the
item itself as a name user. A source-tree search agrees. There are no adapted consumer files.
The new module is owned by this delivery; the original item is held by D2.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.ProjectionIntegralCoherenceRealization | D2 | Publicly imports the moved declarations and uses the new system equations in its private soundness proof. |
| Sheaf.SixFunctors.ProjectionSystemCoherence | D2, new | Contains the unchanged data and a standalone generating-equations theorem. |

## Status

landed 20261025T095015-L-3282411 2026-10-25 (merge of deliver/D2/Sheaf.SixFunctors.ProjectionIntegralCoherenceRealization)
