# AlgebraicGeometry.ProEtale.SpTowerShriek.Geometry

## Reason

The old Geometry ordinaryPullTransition is expressed through generic inverse-image
underlying-sheaf identifications. Those identifications are freely supplied natural
isomorphisms. At f=id one can conjugate the horizontal system functors by a different
central scalar unit at each level, modify moduleUnderlying and levelPushUnderlying
by reciprocal scalars, and transport the tensor and derived data accordingly. Every
old normalization survives, including identity carrier evaluation comparisons and the
fixed finite adjunctions. For l=3, take signs +1 at level 0 and -1 at level 1 on a
scheme with all 3-power roots: the actual line transition then acquires a minus sign,
whereas the normalized finite comparisons at f=id are the canonical identity-pullback comparisons. Thus the archived
horizontal theorem is false under that inadequate interface.

More explicitly, after identifying the identity-map finite functors canonically,
choose central units s_n and put (T_s M)_{m,n} = s_n^(-1) M_{m,n} s_m.
Take pull = T_s, push = T_s^(-1), identity component evaluation comparisons,
moduleUnderlying_n = s_n and levelPushUnderlying_n = s_n^(-1).
The restriction comparison is multiplication by s_n^(-1) s_m. These satisfy
ordinaryPullTransition and restrictionPullback_underlying; the two scalars cancel
in level_unit_underlying. Transport the remaining derived/tensor comparisons
through T_s (the ordinary tensor comparison at n is multiplied by s_n^(-1)).
At s_0 = 1 and s_1 = -1, the transition from level 1 to level 0 changes sign.
A primitive ninth root on an algebraically closed characteristic-zero scheme
maps to a nonzero third-root tensor over the level-zero F_3 coefficient ring.
The canonical identity-pullback finite comparisons leave that tensor unchanged,
so their components cannot form the old claimed horizontal square.

Repair the definition by requiring the compatibility of the ACTUAL finite adjunction
units with horizontal restriction, on every system and every chart section. This law
holds for the termwise geometric inverse image: before sheafification the finite
unit sends x to 1 tensor x, and the transition sends that generator to
1 tensor transition(x), since the quotient coefficient map preserves one. Naturality
of the inverse-image presheaf map and of sheafification gives the same identity on
all sheaf sections. The prescribed pull-evaluation isomorphisms transport exactly
this identity. Its formulation is independent of the generic moduleUnderlying choices. It is not a root-line theorem or a disguised
hypothesis of the assigned square: it refers to no Chern data, root, tensor generator,
finite root-line comparison, or resulting system isomorphism. Its formula is separately defined
as OrdinaryUnitTransition, marked irreducible to keep the dependent Geometry structure
small during kernel checking. Its formula is expressed by OrdinaryUnitTransitionModel
with abstract evaluations and coefficient restrictions, then specialized to the actual
ones. The auxiliary section y and its HEq premise express the unchanged carrier of
restriction without unfolding scalar actions; at the actual restriction choose y to
be the transitioned section; the HEq premise only records its carrier. No new
object is chosen. The structure adds one proof field and preserves all existing
fields, names, types, universes, visibility and public imports.

The later-landed explicit constructor exists_sectionGeometry is adapted in the same
delivery. Its existing finite transpose normalization and inverse-system restriction
identity prove the new unit law by adjunction naturality; its signature and ordinary
and derived constructions remain unchanged. It adds no hole.

For kernel performance, B directly names proEtaleConstantRing T (R n), instead
of evaluating the computed spCoefficientCommRings tower. These are definitionally
the same constant commutative-ring sheaf (the tower is Functor.ofOpSequence of
exactly these values); no scalar, transition, index, universe or instance changes.
This removes repeated normalization of the computed tower objects when they are
compared with the canonical finite functor domains.

The assigned horizontal theorem retains its original complete signature. Its proof
uses this actual-unit law together with scalar-extension-unit naturality and the
actual coefficient/root direct-image maps. No parent theorem signature changes.

Because Geometry is part of definitions used downstream, the target-statement meaning
review must be reopened for every affected target under AGENTS.md section 4. The added
law restores the intended actual operations, rather than replacing them by weaker
objects; Lean comparator target statements themselves are unchanged.

## Old

```lean
abbrev B (T : Scheme.{u}) (n : ℕ) :
    Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1} :=
  (spCoefficientCommRings.{u, u} l E T).obj (op n)

structure Geometry (b : Base l E) {X Y : Scheme.{u}} (f : X ⟶ Y) where
  /-- The source of the normalization, on the actual small pro-etale topoi. -/
  generic : SemilinearSections.Geometry.{u + 1, u, u + 1}
    (Scheme.ProEt.topology Y) (B l E Y) (tau l E Y) (b.calculus Y)
    (Scheme.ProEt.topology X)
    (proEtaleSheafInverseImage f (Type (u + 1)))
    (proEtaleSheafDirectImage f (Type (u + 1)))
    (proEtaleSheafAdjunction f (Type (u + 1)))
  /-- The specified counit-mate coefficient transitions for total direct image. -/
  transitionFormula : generic.TransitionFormula
    (Scheme.ProEt.topology Y) (B l E Y) (tau l E Y) (b.calculus Y)
    (Scheme.ProEt.topology X)
    (proEtaleSheafInverseImage f (Type (u + 1)))
    (proEtaleSheafDirectImage f (Type (u + 1)))
    (proEtaleSheafAdjunction f (Type (u + 1)))
  /-- The inverse-image transition uses the same coefficient comparison. -/
  pullTransitionFormula : generic.PullTransitionFormula
    (Scheme.ProEt.topology Y) (B l E Y) (tau l E Y) (b.calculus Y)
    (Scheme.ProEt.topology X)
    (proEtaleSheafInverseImage f (Type (u + 1)))
    (proEtaleSheafDirectImage f (Type (u + 1)))
    (proEtaleSheafAdjunction f (Type (u + 1)))
  /-- Projection evaluation is the generic normalized counit-transpose equation. -/
  projectionEvaluation : generic.ProjectionEvaluation
    (Scheme.ProEt.topology Y) (B l E Y) (tau l E Y) (b.calculus Y)
    (Scheme.ProEt.topology X)
    (proEtaleSheafInverseImage f (Type (u + 1)))
    (proEtaleSheafDirectImage f (Type (u + 1)))
    (proEtaleSheafAdjunction f (Type (u + 1)))
  /-- Inverse image of the constant ring is identified by its constant sections. -/
  coefficients : generic.coefficients = B l E X
  /-- The identifications retain the quotient homomorphisms. -/
  transitions : HEq generic.coefficientTransition (tau l E X)
  /-- The target tensor is the same fixed K-flat tensor. -/
  target : HEq generic.target (b.calculus X)
  /-- Ordinary inverse image of systems. -/
  pull : S l E Y ⥤ S l E X
  /-- Ordinary direct image of systems. -/
  push : S l E X ⥤ S l E Y
  /-- The coordinate changes above transport the actual generic inverse image. -/
  pull_eq : HEq pull generic.pull
  /-- They transport the actual generic direct image. -/
  push_eq : HEq push generic.push
  /-- Exact additive inverse image. -/
  [pullAdditive : pull.Additive]
  /-- Preservation of kernels. -/
  [pullLimits : PreservesFiniteLimits pull]
  /-- Preservation of cokernels. -/
  [pullColimits : PreservesFiniteColimits pull]
  /-- Additive direct image. -/
  [pushAdditive : push.Additive]
  /-- The ordinary normalized geometric adjunction. -/
  ordinaryAdjunction : pull ⊣ push
  /-- No second choice of the adjunction is made. -/
  ordinaryAdjunction_eq : HEq ordinaryAdjunction generic.ordinaryAdjunction
  /-- Its derived adjunction is the canonical localization of this ordinary pair. -/
  derivedAdjunction_eq :
    HEq ordinaryAdjunction.mapDerivedCategoryRightDerivedAdjunction generic.adjunction
  /-- Ordinary component comparison, retaining the generic section normalization. -/
  ordinaryPullEvaluation : ∀ n : ℕ, pull ⋙ ev l E X n ≅
    ev l E Y n ⋙ proEtaleConstantRingPullback (R l E n) f
  ordinaryPullEvaluation_eq : ∀ n : ℕ,
    HEq (ordinaryPullEvaluation n) (generic.ordinaryPullEvaluation n)
  /-- Exact inverse-image evaluation. -/
  pullEvaluation : ∀ n : ℕ,
    pull.mapDerivedCategory ⋙ Ev l E X n ≅
      Ev l E Y n ⋙ proEtaleConstantRingDerivedPullback (R l E n) f
  /-- The specified generic comparison is retained. -/
  pullEvaluation_eq : ∀ n : ℕ, HEq (pullEvaluation n) (generic.pullEvaluation n)
  /-- Ordinary direct image retains the sectionwise generic realization. -/
  ordinaryPushEvaluation : ∀ n : ℕ, push ⋙ ev l E Y n ≅
    ev l E X n ⋙ proEtaleConstantRingPushforward (R l E n) f
  ordinaryPushEvaluation_eq : ∀ n : ℕ,
    HEq (ordinaryPushEvaluation n) (generic.ordinaryPushEvaluation n)
  /-- Both level functors and their adjunction are the specified constant-section
  operations. Bundling the functors retains their identities under coefficient transport. -/
  levelAdjunction_eq : ∀ n : ℕ,
    HEq
      (⟨(generic.inverseImage n).modules, generic.levelPush n, generic.levelAdjunction n⟩ :
        Σ L : SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology Y) (B l E Y n) ⥤
          SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology X) (generic.coefficients n),
        Σ P : SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology X) (generic.coefficients n) ⥤
          SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology Y) (B l E Y n), L ⊣ P)
      (⟨proEtaleConstantRingPullback (R l E n) f,
        proEtaleConstantRingPushforward (R l E n) f,
        proEtaleConstantRingAdjunction (R l E n) f⟩ :
        Σ L : SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology Y) (B l E Y n) ⥤
          SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology X) (B l E X n),
        Σ P : SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology X) (B l E X n) ⥤
          SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology Y) (B l E Y n), L ⊣ P)
  /-- Total right derived direct image evaluation, including on D+. -/
  pushEvaluation : ∀ n : ℕ,
    push.rightDerivedFunctor ⋙ Ev l E Y n ≅
      Ev l E X n ⋙ (proEtaleConstantRingPushforward (R l E n) f).rightDerivedFunctor
  /-- This is the generic comparison normalized by the derived adjunction. -/
  pushEvaluation_eq : ∀ n : ℕ, HEq (pushEvaluation n) (generic.pushEvaluation n)
  /-- Derived inverse image preserves the actual derived tensor. -/
  tensorPullback : tensor l E b Y ⋙ pull.mapDerivedCategory ≅
    (pull.mapDerivedCategory.prod pull.mapDerivedCategory) ⋙ tensor l E b X
  /-- Its pure-tensor and signed representative normalization is the generic one. -/
  tensorPullback_eq : HEq tensorPullback generic.tensorPullback
```

## New

A real predicate OrdinaryUnitTransition defines the section formula shown below.

```lean
abbrev B (T : Scheme.{u}) (n : ℕ) :
    Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1} :=
  Scheme.proEtaleConstantRing T (R l E n)

@[irreducible] def OrdinaryUnitTransitionModel {X Y : Scheme.{u}}
    (P : ∀ n : ℕ, SemilinearSections.Mod.{u + 1, u, u + 1}
      (Scheme.ProEt.topology Y) (B l E Y n) ⥤
        SemilinearSections.Mod.{u + 1, u, u + 1}
          (Scheme.ProEt.topology X) (B l E X n))
    (Q : ∀ n : ℕ, SemilinearSections.Mod.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (B l E X n) ⥤
        SemilinearSections.Mod.{u + 1, u, u + 1}
          (Scheme.ProEt.topology Y) (B l E Y n))
    (adj : ∀ n : ℕ, P n ⊣ Q n)
    (EY : ∀ n : ℕ, S l E Y ⥤ SemilinearSections.Mod.{u + 1, u, u + 1}
      (Scheme.ProEt.topology Y) (B l E Y n))
    (EX : ∀ n : ℕ, S l E X ⥤ SemilinearSections.Mod.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (B l E X n))
    (RY : ∀ {m n : ℕ} (_h : n ≤ m),
      SemilinearSections.Mod.{u + 1, u, u + 1}
        (Scheme.ProEt.topology Y) (B l E Y n) ⥤
      SemilinearSections.Mod.{u + 1, u, u + 1}
        (Scheme.ProEt.topology Y) (B l E Y m))
    (RX : ∀ {m n : ℕ} (_h : n ≤ m),
      SemilinearSections.Mod.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X) (B l E X n) ⥤
      SemilinearSections.Mod.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X) (B l E X m))
    (tY : ∀ {m n : ℕ} (h : n ≤ m), EY m ⟶ EY n ⋙ RY h)
    (tX : ∀ {m n : ℕ} (h : n ≤ m), EX m ⟶ EX n ⋙ RX h)
    (F : S l E Y ⥤ S l E X)
    (e : ∀ n : ℕ, F ⋙ EX n ≅ EY n ⋙ P n) : Prop :=
  ∀ (M : S l E Y) {m n : ℕ} (h : n ≤ m)
    (U : Y.ProEtᵒᵖ) (x : ((EY m).obj M).val.obj U)
    (y : ((EY n).obj M).val.obj U),
    HEq (((tY h).app M).val.app U x) y →
    HEq ((((adj m).homEquiv _ _)
      ((e m).inv.app M ≫ (tX h).app (F.obj M) ≫
        (RX h).map ((e n).hom.app M))).val.app U x)
      (((adj n).unit.app ((EY n).obj M)).val.app U y)

/-- The horizontal compatibility of the actual constant-ring finite adjunction units.
The generic formula is specialized to the specified finite functors and adjunctions,
not to arbitrarily supplied underlying-sheaf identifications.
Source: actual termwise inverse image (blueprint: def-sp-tower-shriek-data). -/
@[irreducible] def OrdinaryUnitTransition {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : S l E Y ⥤ S l E X)
    (e : ∀ n : ℕ, F ⋙ ev l E X n ≅
      ev l E Y n ⋙ proEtaleConstantRingPullback (R l E n) f) : Prop :=
  OrdinaryUnitTransitionModel l E
    (fun n ↦ proEtaleConstantRingPullback (R l E n) f)
    (fun n ↦ proEtaleConstantRingPushforward (R l E n) f)
    (fun n ↦ proEtaleConstantRingAdjunction (R l E n) f)
    (ev l E Y) (ev l E X)
    (fun h ↦ SemilinearSections.res.{u + 1, u, u + 1}
      (SemilinearSections.coefficientMap.{u + 1, u, u + 1}
        (Scheme.ProEt.topology Y) (B l E Y) (tau l E Y) h))
    (fun h ↦ SemilinearSections.res.{u + 1, u, u + 1}
      (SemilinearSections.coefficientMap.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X) (B l E X) (tau l E X) h))
    (fun h ↦ SemilinearSections.transition.{u + 1, u, u + 1}
      (Scheme.ProEt.topology Y) (B l E Y) (tau l E Y) h)
    (fun h ↦ SemilinearSections.transition.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (B l E X) (tau l E X) h) F e

structure Geometry (b : Base l E) {X Y : Scheme.{u}} (f : X ⟶ Y) where
  /-- The source of the normalization, on the actual small pro-etale topoi. -/
  generic : SemilinearSections.Geometry.{u + 1, u, u + 1}
    (Scheme.ProEt.topology Y) (B l E Y) (tau l E Y) (b.calculus Y)
    (Scheme.ProEt.topology X)
    (proEtaleSheafInverseImage f (Type (u + 1)))
    (proEtaleSheafDirectImage f (Type (u + 1)))
    (proEtaleSheafAdjunction f (Type (u + 1)))
  /-- The specified counit-mate coefficient transitions for total direct image. -/
  transitionFormula : generic.TransitionFormula
    (Scheme.ProEt.topology Y) (B l E Y) (tau l E Y) (b.calculus Y)
    (Scheme.ProEt.topology X)
    (proEtaleSheafInverseImage f (Type (u + 1)))
    (proEtaleSheafDirectImage f (Type (u + 1)))
    (proEtaleSheafAdjunction f (Type (u + 1)))
  /-- The inverse-image transition uses the same coefficient comparison. -/
  pullTransitionFormula : generic.PullTransitionFormula
    (Scheme.ProEt.topology Y) (B l E Y) (tau l E Y) (b.calculus Y)
    (Scheme.ProEt.topology X)
    (proEtaleSheafInverseImage f (Type (u + 1)))
    (proEtaleSheafDirectImage f (Type (u + 1)))
    (proEtaleSheafAdjunction f (Type (u + 1)))
  /-- Projection evaluation is the generic normalized counit-transpose equation. -/
  projectionEvaluation : generic.ProjectionEvaluation
    (Scheme.ProEt.topology Y) (B l E Y) (tau l E Y) (b.calculus Y)
    (Scheme.ProEt.topology X)
    (proEtaleSheafInverseImage f (Type (u + 1)))
    (proEtaleSheafDirectImage f (Type (u + 1)))
    (proEtaleSheafAdjunction f (Type (u + 1)))
  /-- Inverse image of the constant ring is identified by its constant sections. -/
  coefficients : generic.coefficients = B l E X
  /-- The identifications retain the quotient homomorphisms. -/
  transitions : HEq generic.coefficientTransition (tau l E X)
  /-- The target tensor is the same fixed K-flat tensor. -/
  target : HEq generic.target (b.calculus X)
  /-- Ordinary inverse image of systems. -/
  pull : S l E Y ⥤ S l E X
  /-- Ordinary direct image of systems. -/
  push : S l E X ⥤ S l E Y
  /-- The coordinate changes above transport the actual generic inverse image. -/
  pull_eq : HEq pull generic.pull
  /-- They transport the actual generic direct image. -/
  push_eq : HEq push generic.push
  /-- Exact additive inverse image. -/
  [pullAdditive : pull.Additive]
  /-- Preservation of kernels. -/
  [pullLimits : PreservesFiniteLimits pull]
  /-- Preservation of cokernels. -/
  [pullColimits : PreservesFiniteColimits pull]
  /-- Additive direct image. -/
  [pushAdditive : push.Additive]
  /-- The ordinary normalized geometric adjunction. -/
  ordinaryAdjunction : pull ⊣ push
  /-- No second choice of the adjunction is made. -/
  ordinaryAdjunction_eq : HEq ordinaryAdjunction generic.ordinaryAdjunction
  /-- Its derived adjunction is the canonical localization of this ordinary pair. -/
  derivedAdjunction_eq :
    HEq ordinaryAdjunction.mapDerivedCategoryRightDerivedAdjunction generic.adjunction
  /-- Ordinary component comparison, retaining the generic section normalization. -/
  ordinaryPullEvaluation : ∀ n : ℕ, pull ⋙ ev l E X n ≅
    ev l E Y n ⋙ proEtaleConstantRingPullback (R l E n) f
  ordinaryPullEvaluation_eq : ∀ n : ℕ,
    HEq (ordinaryPullEvaluation n) (generic.ordinaryPullEvaluation n)
  /-- The actual finite adjunction units commute with horizontal restrictions,
  independently of the auxiliary generic underlying-sheaf comparisons. -/
  ordinaryUnitTransition : OrdinaryUnitTransition l E f pull ordinaryPullEvaluation
  /-- Exact inverse-image evaluation. -/
  pullEvaluation : ∀ n : ℕ,
    pull.mapDerivedCategory ⋙ Ev l E X n ≅
      Ev l E Y n ⋙ proEtaleConstantRingDerivedPullback (R l E n) f
  /-- The specified generic comparison is retained. -/
  pullEvaluation_eq : ∀ n : ℕ, HEq (pullEvaluation n) (generic.pullEvaluation n)
  /-- Ordinary direct image retains the sectionwise generic realization. -/
  ordinaryPushEvaluation : ∀ n : ℕ, push ⋙ ev l E Y n ≅
    ev l E X n ⋙ proEtaleConstantRingPushforward (R l E n) f
  ordinaryPushEvaluation_eq : ∀ n : ℕ,
    HEq (ordinaryPushEvaluation n) (generic.ordinaryPushEvaluation n)
  /-- Both level functors and their adjunction are the specified constant-section
  operations. Bundling the functors retains their identities under coefficient transport. -/
  levelAdjunction_eq : ∀ n : ℕ,
    HEq
      (⟨(generic.inverseImage n).modules, generic.levelPush n, generic.levelAdjunction n⟩ :
        Σ L : SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology Y) (B l E Y n) ⥤
          SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology X) (generic.coefficients n),
        Σ P : SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology X) (generic.coefficients n) ⥤
          SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology Y) (B l E Y n), L ⊣ P)
      (⟨proEtaleConstantRingPullback (R l E n) f,
        proEtaleConstantRingPushforward (R l E n) f,
        proEtaleConstantRingAdjunction (R l E n) f⟩ :
        Σ L : SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology Y) (B l E Y n) ⥤
          SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology X) (B l E X n),
        Σ P : SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology X) (B l E X n) ⥤
          SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology Y) (B l E Y n), L ⊣ P)
  /-- Total right derived direct image evaluation, including on D+. -/
  pushEvaluation : ∀ n : ℕ,
    push.rightDerivedFunctor ⋙ Ev l E Y n ≅
      Ev l E X n ⋙ (proEtaleConstantRingPushforward (R l E n) f).rightDerivedFunctor
  /-- This is the generic comparison normalized by the derived adjunction. -/
  pushEvaluation_eq : ∀ n : ℕ, HEq (pushEvaluation n) (generic.pushEvaluation n)
  /-- Derived inverse image preserves the actual derived tensor. -/
  tensorPullback : tensor l E b Y ⋙ pull.mapDerivedCategory ≅
    (pull.mapDerivedCategory.prod pull.mapDerivedCategory) ⋙ tensor l E b X
  /-- Its pure-tensor and signed representative normalization is the generic one. -/
  tensorPullback_eq : HEq tensorPullback generic.tensorPullback
```

## Users

SmoothPurityTowerShriekData is unclaimed; the assigned module is held by F5.
The complete downstream inventory is recorded below; all 16 direct importers are
compiled individually against the changed dependency before delivery.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ClosedTowerDirectImageExact | unclaimed | Direct importer: single-file compatibility check; no existing field or declaration signature removed. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.DiagonalCompleteScalarRestriction | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.DiagonalCompletedChernLift | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.DiagonalCompletedLineComplete | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.DiagonalCompletedLineCompleteAux | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.DiagonalCompletionCoefficientTransport | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.DiagonalTowerTraceModels | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.DiagonalTowerTracePresentations | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.DiagonalTraceChernTwistExistence | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.DiagonalTraceCoefficientIdentification | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.DiagonalTraceCoefficientProjection | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.DiagonalTraceCoefficientRestriction | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.DiagonalTraceCompletedHomBijection | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.DiagonalTraceCompletedScalarSquare | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.DiagonalTraceDiagonalPic | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.DiagonalTraceDivisorChernAdjoint | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.DiagonalTraceFiniteAdjunctionFactorization | D8 | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.DiagonalTraceFiniteCartierChern | E7 | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.DiagonalTraceFiniteDivisorAdjoint | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.DiagonalTraceFinitePretraceComponents | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.DiagonalTraceFiniteUnitCohomology | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.DiagonalTraceGeometricModelExistence | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.DiagonalTraceLineIdentification | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.DiagonalTraceOrdinaryLimitEpi | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.DiagonalTraceOrdinaryScalars | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.DiagonalTraceResidueRestriction | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.DiagonalTraceSingleFaithful | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.DiagonalTraceSources | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.DiagonalTraceSupportedSourceExistence | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.DiagonalTraceUnitArrowComparison | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.DiagonalTraceUnitComparisonIso | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.DiagonalTraceVaryingScalarSquare | E8 | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.FiniteTateLineUniversal | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.IntegralDirectImageTowerData | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.IntegralTowerCompactificationCoherence | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.IntegralTowerGeometryLimits | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.IntegralTowerPullTensorConstructible | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.IntegralTowerScalarPresentation | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.IntegralUnitReduction | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.KummerLineTwisting | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.KummerReductionUnit | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.KummerRootRankOne | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.NormalizedChernFiniteBoundary | E5 | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.NormalizedKummerReduction | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.NormalizedKummerTarget | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.PowerSystemAcyclicResolution | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.PowerSystemOrdinaryCokernel | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.PowerSystemReductionTriangle | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.SingleBoundaryNormalization | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.SmoothPurityFiniteLevelProjectionCriterion | unclaimed | Direct importer: single-file compatibility check; no existing field or declaration signature removed. |
| Sheaf.Paper.SmoothPurityStrictBaseCoordinates | unclaimed | Direct importer: single-file compatibility check; no existing field or declaration signature removed. |
| Sheaf.Paper.SmoothPurityStrictCompactificationComparisonData | unclaimed | Direct importer: single-file compatibility check; no existing field or declaration signature removed. |
| Sheaf.Paper.SmoothPurityStrictCompactificationComparisonRealization | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.SmoothPurityStrictCoordinatesExistence | unclaimed | Direct importer: single-file compatibility check; no existing field or declaration signature removed. |
| Sheaf.Paper.SmoothPurityStrictFiniteWordIdentification | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.SmoothPurityStrictGeometricCoordinates | unclaimed | Direct importer: single-file compatibility check; no existing field or declaration signature removed. |
| Sheaf.Paper.SmoothPurityStrictOpenTensorCoordinates | unclaimed | Direct importer: single-file compatibility check; no existing field or declaration signature removed. |
| Sheaf.Paper.SmoothPurityStrictOpenWordEvaluation | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.SmoothPurityStrictPlusComparisonsRealization | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.SmoothPurityStrictPlusEvaluationRealization | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.SmoothPurityStrictSystemGeometricRealization | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.SmoothPurityTowerBinaryCtfFibre | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.SmoothPurityTowerClasses | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.SmoothPurityTowerExchange | unclaimed | Direct importer: single-file compatibility check; no existing field or declaration signature removed. |
| Sheaf.Paper.SmoothPurityTowerFibreProjections | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.SmoothPurityTowerLocalization | unclaimed | Direct importer: single-file compatibility check; no existing field or declaration signature removed. |
| Sheaf.Paper.SmoothPurityTowerOrdinaryLocalization | unclaimed | Direct importer: single-file compatibility check; no existing field or declaration signature removed. |
| Sheaf.Paper.SmoothPurityTowerOrdinaryUnitEvaluation | unclaimed | Direct importer: single-file compatibility check; no existing field or declaration signature removed. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | unclaimed | Direct importer: single-file compatibility check; no existing field or declaration signature removed. |
| Sheaf.Paper.TowerChernOrdinaryScalarPullback | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerChernPullback | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerChernPullbackData | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerChernRealizationPullback | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerChernReductionPullback | U2 | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerChernScalarPullback | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerChernScalarUnit | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerClassChern | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerClassCoefficients | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerClassDiagonal | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerClassFinite | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerClassFiniteDiagonal | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerClassFiniteLineComparisons | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerClassFiniteSectionInverseImages | unclaimed | Direct importer: single-file compatibility check; no existing field or declaration signature removed. |
| Sheaf.Paper.TowerClassFiniteUnit | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerClassLinePullbackExistence | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerClassLinePullbackHorizontal | F5 | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerClassPositiveUnitSquare | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerClassProjective | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerClassPullback | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerClassReduction | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerClassSectionAdjoint | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerClassSectionAdjointFaithful | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerClassSectionAdjointNaturality | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerClassSectionGeometryExistence | unclaimed | Direct importer adapted: prove the new ordinaryUnitTransition field in the explicit Geometry constructor from its existing finite transpose normalization and inverse-system restriction identity; signature unchanged. |
| Sheaf.Paper.TowerClassSystems | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerClassTensorAdjointEvaluation | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerClassTensorComparison | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerClassTensorComparisonCoordinates | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerClassTensorComparisonNormalization | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerClassTensorComparisonSections | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerClassTensorGeometryExistence | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerClassTensorLevelCoordinates | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerClassTensorPullback | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerClassTensorUnitCoordinates | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerClassTwisting | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerClassUnitLevelCoordinates | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerClassUnitSuccessorCompatibility | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerForgetEvaluation | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerGeometryAdjunctionEvaluation | unclaimed | Direct importer: single-file compatibility check; no existing field or declaration signature removed. |
| Sheaf.Paper.TowerIntegralClassPullback | G9 | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerIntegralCoefficientPullbackExistence | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerLineBundleClassAdditive | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerLineBundleEtaleClassAdditive | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerLineEvaluationUniversal | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerOpenAdjunctionEvaluation | unclaimed | Direct importer: single-file compatibility check; no existing field or declaration signature removed. |
| Sheaf.Paper.TowerOperationsGroundFieldRetagging | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerOrdinaryScalarAssociation | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerProjectionDomainEvaluation | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerScalarCounitNormalization | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerScalarPullbackCounitLift | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |
| Sheaf.Paper.TowerScalarSingleCounit | unclaimed | Indirect importer: old fields and operations retained; actual finite-unit normalization now explicit. |

## Status

landed 20261027T151703-L-1192563 2026-10-27 (merge of deliver/F5/Sheaf.Paper.TowerClassLinePullbackHorizontal)
