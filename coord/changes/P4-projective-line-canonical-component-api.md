# SpP1 family and canonical component interfaces

## Reason

The assigned proof repeatedly exceeded the 60-second single-file check. Prefix probes
isolated the expansion of nested family and normalization propositions, including
unused clauses, before the diagonal calculation. This is a definition/API repair:
three one-field structures store the same three functions, a generic five-field
proposition stores the same five normalization clauses, and a shared kernel
structure packages the canonical diagonal arrows. Named canonical maps avoid
repeating their entire derived-functor expressions. No proof was moved to a new
file merely to evade the limit. SpP1CartierCompatibility now lives in the shared
component module: both the component theorem's premise and the parent's
predicate use it, and retaining it in the parent would create an import cycle.
Its qualified name, signature and body are unchanged. The DAG attachment follows
the shared module; the target proof route records the canonical kernel API dependency. The parent publicly imports
the component module, preserving its existing public interface. The component
premise uses this shared predicate instead of expanding its same Ext equation.
The final existential witness is assembled with a proved generic constructor in
the same main file, avoiding repeated elaboration of dependent constructors.

The family constructor and `map` projection are inverse, by structure eta and
function reflexivity. The generic normalization proposition is equivalent to the
old fivefold conjunction, by its five projections and constructor. Its single-base
specialization fixes exactly the old Chern, invertibility, decomposition, unit and
Chern-component conditions. The named unit and Chern maps have the old expressions
as their literal bodies. Thus no family, normalization or base-change condition is
added or dropped. The base-change, rational-point and Chern-trace predicates retain
their old formulas, applied to the structure's underlying function.

The specialized diagonal predicate retains the supported boundary, Ext comparison,
exact derived realization, both source identifications, canonical trace formulas
and both integral identities. The shared `geoP1DiagonalKernelData` stores the
literal canonical source isomorphisms, Cartier arrow and chart maps. Every map
is stored with its actual type. `DiagonalKernelRealization` requires HEq from
each stored value to a typed representative, so every representative is uniquely
fixed. Its `DiagonalIntegralFormula` retains both composite identities. Source
invertibility is retained by storing the constructed composition isomorphisms;
their homs are exactly the old canonical source arrows. No source isomorphism is
chosen from a mere existence theorem. The Cartier and chart expressions now
retain their inferred Hom types, instead of repeatedly checking an equivalent
printed Hom type at each definition. The typed realization requires HEq from
those exact expressions to arrows in the original prescribed Hom types, just
as the original predicate did. Thus type inference changes no value or condition. `DiagonalIntegralCondition`
retains the supplied trace by HEq to a representative in the kernel's Hom type;
that representative is uniquely determined. This preserves the original interface's
heterogeneous equalities without choosing an independently normalized trace.
The old existential
alpha, delta and tau arrows are uniquely determined by their displayed equations;
eliminating them is equivalent to substituting these canonical arrows. The
existential exactness witness hE is retained. Moving it before the canonical
substitution changes no condition, and its proof arguments are proof-irrelevant.
Eliminating the old existential canonical arrows gives the typed canonical
composite formula; that generic equivalence compiled in a diagnostic file (4.1 s).
The new typed realization and integral predicate were checked against this same
typed formula, including source invertibility (3.8 s). The two equivalences
therefore recover the original canonical-arrow formulation.
The new source is the hom of the inverse component of the composite natural isomorphism;
NatIso.trans expands it to exactly the old composite of inverse components.
Unfolding the Cartier definition gives the old formula. The typed realization
and its integral formula were checked against the canonical typed-map formula,
including source invertibility. The chart uses the
adjunction unit at the twist instead of its hom-equivalence applied to the
identity; these agree by Adjunction.homEquiv_id. The additional component data
stores the actual unit and Chern maps with their types, and its predicate requires
HEq to correctly typed representatives. These representatives are uniquely fixed,
so it imposes the same two component equations. The generic HEq trace wrapper
is equivalent to the typed integral formula. These identities were checked in
the diagnostic compile. The chart/trace formula also uses associativity:
`(f ≫ g ≫ h) ≫ t = f ≫ g ≫ h ≫ t`; this identity was checked in the same file.
The three family constructor/projection inverses and the five-condition
proposition/conjunction equivalence also passed a diagnostic compile (3.8 s).
There is no replacement object, chosen comparison isomorphism or weakened equation.

Only the assigned item and the unclaimed system module are adapted. Every adopted
WeilConjectures source is unchanged. Every existing theorem signature in the item
retains its text. Challenge.lean is unchanged. The statement-meaning review is reopened for targets
reaching these definitions. The reviewer should check the equivalences below.
Any statement-meaning review that
covers these definitions should verify the constructor/projection bijections and
the displayed formula expansions; they preserve the paper's exact conditions.

## Old

```lean
/-- Exact comparison of the supported and Cartier Ext classes.
Source: det-sp-p1-trace, clause 3 (blueprint: det-sp-p1-trace). -/
def SpP1CartierCompatibility {C : Type uC} [Category.{vC} C] [Abelian C]
    [HasExt.{wC} C] {D : Type uD} [Category.{vD} D] [Abelian D] [HasExt.{wD} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X L : C} {Y : D} (σ : F.obj X ⟶ Y) (κ : Ext X L 2) (c : Ext Y (F.obj L) 2) :
    Prop := (Ext.mk₀ σ).comp c (zero_add 2) = κ.mapExactFunctor F

/-- The Chern arrows over all bases; their Kummer normalization is a clause of the
statement, rather than an assumption or a choice of generators.
Source: det-sp-p1-trace, clauses 1--2 (blueprint: def-sp-p1-proetale-trace-system). -/
abbrev SpP1ChernFamily (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0) :=
  ∀ (S : Scheme.{u}) (_hS : IsUnit (N : Γ(S, ⊤))),
    Etale.ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (Etale.ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧

/-- A family of twisted isomorphisms; their two components are fixed
in the statement. The trace is always the existing `geoP1Trace`.
Source: det-sp-p1-trace, clause 2 (blueprint: def-sp-p1-proetale-trace-system). -/
abbrev SpP1TwistedFamily (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0) :=
  ∀ (S : Scheme.{u}) (_hS : IsUnit (N : Γ(S, ⊤))),
    (geoP1Twist A N hA S 1 2 ⊞ geoP1Unit A S) ≅
      (geoP1Pushforward A (ProjectiveLine S ↘ S)).obj
        (geoP1Twist A N hA (ProjectiveLine S) 1 2)

/-- The untwisted decomposition arrows on all bases.
Source: det-sp-p1-trace, clause 1 (blueprint: def-sp-p1-proetale-trace-system). -/
abbrev SpP1DecompositionFamily (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) :=
  ∀ (S : Scheme.{u}) (_hS : IsUnit (N : Γ(S, ⊤))),
    (geoP1Unit A S ⊞ geoP1Twist A N hA S (-1) (-2)) ⟶
      (geoP1Pushforward A (ProjectiveLine S ↘ S)).obj (geoP1Unit A (ProjectiveLine S))

/-- The exact unit-and-Kummer formula, its invertibility, and the twisted components.
Source: det-sp-p1-trace, clauses 1--2 (blueprint: def-sp-p1-proetale-trace-system). -/
def SpP1NormalizedDecompositions (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (c : SpP1ChernFamily A N hA) (b : SpP1TwistedFamily A N hA)
    (d : SpP1DecompositionFamily A N hA) : Prop :=
  ∀ (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))),
    Etale.ordinaryFiniteP1ChernSpec A N hA S
      ((map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
        hS.map (ProjectiveLine S ↘ S).appTop.hom) (c S hS) ∧
    IsIso (d S hS) ∧
    HEq (d S hS)
      (geoP1SumComparison A S (Etale.ordinaryFiniteUnit A S)
          (Etale.p1DecompositionTwist A N hA S (-1) (-2)) ≫
          (geoP1Comparison A S).map (Etale.p1DecompositionMap A N hN hA S hS (c S hS)) ≫
          geoP1PushComparison A (ProjectiveLine S ↘ S)
            (Etale.ordinaryFiniteUnit A (ProjectiveLine S))) ∧
    HEq (biprod.inl ≫ (b S hS).hom)
      ((geoP1Comparison A S).map
            (Etale.ordinaryFiniteP1Unit A N hA
              (Etale.projectiveLineTraceTransport N hN A hA) S hS) ≫
          geoP1PushComparison A (ProjectiveLine S ↘ S)
            ((Etale.ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)) ∧
    HEq (biprod.inr ≫ (b S hS).hom)
      ((geoP1Comparison A S).map
            (Etale.ordinaryFiniteP1ChernPushforward A N hA S (c S hS)) ≫
          geoP1PushComparison A (ProjectiveLine S ↘ S)
            ((Etale.ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧))

/-- The canonical source, diagonal-class, and projection-trace formulas, and both
integral identities. The canonical formulas uniquely determine every arrow.
Source: det-sp-p1-trace, clause 3 (blueprint: det-sp-p1-trace). -/
@[irreducible]
def SpP1DiagonalIntegrals (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (b : SpP1TwistedFamily A N hA) : Prop :=
  ∀ (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))),
    ∃ (hI : (pullback.diagonal (ProjectiveLine S ↘ S)).ker.IsInvertible)
      (κ : Ext
        ((Etale.lowerStar (ModuleCat.{u + 1} A)
          (pullback.diagonal (ProjectiveLine S ↘ S))).obj
            (Etale.ordinaryFiniteConstant A (ProjectiveLine S)))
        (Scheme.finiteEtaleTateLine
          (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) 2)
      (cΔ : GeoCartierClass A N hA (pullback.diagonal (ProjectiveLine S ↘ S)))
      (α : ∀ a : Bool, geoP1Unit A (ProjectiveLine S) ⟶
        (geoP1Pushforward A (Etale.projectiveLineDiagonalProjection S a)).obj
          ((geoP1Pushforward A (pullback.diagonal (ProjectiveLine S ↘ S))).obj
            (geoP1Unit A (ProjectiveLine S))))
      (δ : (geoP1Pushforward A (pullback.diagonal (ProjectiveLine S ↘ S))).obj
          (geoP1Unit A (ProjectiveLine S)) ⟶
        geoP1Twist A N hA
          (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) 1 2)
      (τ : ∀ a : Bool,
        (geoP1Pushforward A (Etale.projectiveLineDiagonalProjection S a)).obj
          (geoP1Twist A N hA
            (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) 1 2) ⟶
          geoP1Unit A (ProjectiveLine S)),
      Etale.SupportedKummerBoundary A N hA (pullback.diagonal (ProjectiveLine S ↘ S)) hI
        ((map_natCast ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
          (ProjectiveLine S ↘ S)).appTop.hom N) ▸
            hS.map ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
              (ProjectiveLine S ↘ S)).appTop.hom) κ ∧
      SpP1CartierCompatibility
        (comparisonUpperStar (ModuleCat.{u + 1} A)
          (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))
        (geoCartierSourceComparison A (pullback.diagonal (ProjectiveLine S ↘ S))) κ cΔ ∧
      (∃ hE : PreservesFiniteColimits
          (lowerStar (ModuleCat.{u + 1} A) (pullback.diagonal (ProjectiveLine S ↘ S))),
        CartierDerivedCompatibility (hF := hE)
          (lowerStar (ModuleCat.{u + 1} A) (pullback.diagonal (ProjectiveLine S ↘ S)))
          (geoCartierConstant A (ProjectiveLine S))
          (geoCartierLine A N hA
            (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))
          (cartierUnitSingleIso A (ProjectiveLine S))
          (cartierShiftSingleIso
            (comparisonUpperStar (ModuleCat.{u + 1} A)
              (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))
            (Scheme.finiteEtaleTateLine
              (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA))
          cΔ δ) ∧
      HEq (α false)
        ((rightDerivedLowerStarId (ModuleCat.{u + 1} A) (ProjectiveLine S)).inv.app
            (geoP1Unit A (ProjectiveLine S)) ≫
          (rightDerivedLowerStarFactor (ModuleCat.{u + 1} A)
            (pullback.diagonal_fst (ProjectiveLine S ↘ S))).inv.app
              (geoP1Unit A (ProjectiveLine S))) ∧
      HEq (α true)
        ((rightDerivedLowerStarId (ModuleCat.{u + 1} A) (ProjectiveLine S)).inv.app
            (geoP1Unit A (ProjectiveLine S)) ≫
          (rightDerivedLowerStarFactor (ModuleCat.{u + 1} A)
            (pullback.diagonal_snd (ProjectiveLine S ↘ S))).inv.app
              (geoP1Unit A (ProjectiveLine S))) ∧
      ∀ a : Bool,
        IsIso (α a) ∧
        HEq (τ a)
          ((geoP1Pushforward A (Etale.projectiveLineDiagonalProjection S a)).map
                ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
                  (Etale.projectiveLineDiagonalChart S a).val.hom).homEquiv
                    (geoP1Twist A N hA
                      (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) 1 2)
                    ((geoP1Pullback A (Etale.projectiveLineDiagonalChart S a).val.hom).obj
                      (geoP1Twist A N hA
                        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) 1 2)) (𝟙 _)) ≫
              (rightDerivedLowerStarFactor (ModuleCat.{u + 1} A)
                (Etale.projectiveLineDiagonalChart S a).property).hom.app
                  ((geoP1Pullback A (Etale.projectiveLineDiagonalChart S a).val.hom).obj
                    (geoP1Twist A N hA
                      (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) 1 2)) ≫
              (geoP1Pushforward A (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)).map
                (geoP1TwistPullback A N hN hA (Etale.projectiveLineDiagonalChart S a).val.hom
                  ((map_natCast ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
                    (ProjectiveLine S ↘ S)).appTop.hom N) ▸
                      hS.map ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
                        (ProjectiveLine S ↘ S)).appTop.hom) 1 2).hom ≫
              geoP1Trace A N hA (ProjectiveLine S)
                (b (ProjectiveLine S)
                  ((map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
                    hS.map (ProjectiveLine S ↘ S).appTop.hom))) ∧
        HEq (α a ≫
          (geoP1Pushforward A (Etale.projectiveLineDiagonalProjection S a)).map δ ≫ τ a)
          (𝟙 (geoP1Unit A (ProjectiveLine S)))
```

## New

```lean
/-- Exact comparison of the supported and Cartier Ext classes.
Source: det-sp-p1-trace, clause 3
(blueprint: lem-sp-p1-diagonal-comparison-components). -/
def SpP1CartierCompatibility {C : Type uC} [Category.{vC} C] [Abelian C]
    [HasExt.{wC} C] {D : Type uD} [Category.{vD} D] [Abelian D] [HasExt.{wD} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X L : C} {Y : D} (σ : F.obj X ⟶ Y) (κ : Ext X L 2) (c : Ext Y (F.obj L) 2) :
    Prop := (Ext.mk₀ σ).comp c (zero_add 2) = κ.mapExactFunctor F

/-- The Chern arrows over all bases; their Kummer normalization is a clause of the
statement, rather than an assumption or a choice of generators.
Source: det-sp-p1-trace, clauses 1--2 (blueprint: def-sp-p1-proetale-trace-system). -/
structure SpP1ChernFamily (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0) where
  map :
    ∀ (S : Scheme.{u}) (_hS : IsUnit (N : Γ(S, ⊤))),
      Etale.ordinaryFiniteUnit A (ProjectiveLine S) ⟶
        (Etale.ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧

instance (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0) :
    CoeFun (SpP1ChernFamily A N hA) (fun _ ↦
        ∀ (S : Scheme.{u}) (_hS : IsUnit (N : Γ(S, ⊤))),
          Etale.ordinaryFiniteUnit A (ProjectiveLine S) ⟶
            (Etale.ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) := ⟨SpP1ChernFamily.map⟩

/-- A family of twisted isomorphisms; their two components are fixed
in the statement. The trace is always the existing `geoP1Trace`.
Source: det-sp-p1-trace, clause 2 (blueprint: def-sp-p1-proetale-trace-system). -/
structure SpP1TwistedFamily (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0) where
  map :
    ∀ (S : Scheme.{u}) (_hS : IsUnit (N : Γ(S, ⊤))),
      (geoP1Twist A N hA S 1 2 ⊞ geoP1Unit A S) ≅
        (geoP1Pushforward A (ProjectiveLine S ↘ S)).obj
          (geoP1Twist A N hA (ProjectiveLine S) 1 2)

instance (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0) :
    CoeFun (SpP1TwistedFamily A N hA) (fun _ ↦
        ∀ (S : Scheme.{u}) (_hS : IsUnit (N : Γ(S, ⊤))),
          (geoP1Twist A N hA S 1 2 ⊞ geoP1Unit A S) ≅
            (geoP1Pushforward A (ProjectiveLine S ↘ S)).obj
              (geoP1Twist A N hA (ProjectiveLine S) 1 2)) := ⟨SpP1TwistedFamily.map⟩

/-- The untwisted decomposition arrows on all bases.
Source: det-sp-p1-trace, clause 1 (blueprint: def-sp-p1-proetale-trace-system). -/
structure SpP1DecompositionFamily (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) where
  map :
    ∀ (S : Scheme.{u}) (_hS : IsUnit (N : Γ(S, ⊤))),
      (geoP1Unit A S ⊞ geoP1Twist A N hA S (-1) (-2)) ⟶
        (geoP1Pushforward A (ProjectiveLine S ↘ S)).obj (geoP1Unit A (ProjectiveLine S))

instance (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0) :
    CoeFun (SpP1DecompositionFamily A N hA) (fun _ ↦
        ∀ (S : Scheme.{u}) (_hS : IsUnit (N : Γ(S, ⊤))),
          (geoP1Unit A S ⊞ geoP1Twist A N hA S (-1) (-2)) ⟶
            (geoP1Pushforward A (ProjectiveLine S ↘ S)).obj
              (geoP1Unit A (ProjectiveLine S))) := ⟨SpP1DecompositionFamily.map⟩

/-- The canonical comparison image of the twisted adjunction unit.
Source: det-sp-p1-trace, clause 2 (blueprint: def-sp-p1-proetale-trace-system). -/
def geoP1TwistedUnit (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) :
    geoP1Twist A N hA S 1 2 ⟶
      (geoP1Pushforward A (ProjectiveLine S ↘ S)).obj
        (geoP1Twist A N hA (ProjectiveLine S) 1 2) :=
  (geoP1Comparison A S).map
    (Etale.ordinaryFiniteP1Unit A N hA
      (Etale.projectiveLineTraceTransport N hN A hA) S hS) ≫
    geoP1PushComparison A (ProjectiveLine S ↘ S)
      ((Etale.ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)

/-- The canonical comparison image of the Chern adjunct.
Source: det-sp-p1-trace, clause 2 (blueprint: def-sp-p1-proetale-trace-system). -/
def geoP1ChernPushforward (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (S : Scheme.{u})
    (c : Etale.ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (Etale.ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) :
    geoP1Unit A S ⟶ (geoP1Pushforward A (ProjectiveLine S ↘ S)).obj
      (geoP1Twist A N hA (ProjectiveLine S) 1 2) :=
  (geoP1Comparison A S).map (Etale.ordinaryFiniteP1ChernPushforward A N hA S c) ≫
    geoP1PushComparison A (ProjectiveLine S ↘ S)
      ((Etale.ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)

/-- The five normalization conditions, kept abstract for kernel sharing.
Source: det-sp-p1-trace, clauses 1--2 (blueprint: def-sp-p1-proetale-trace-system). -/
structure SpP1NormalizationClauses (p q r s t : Prop) : Prop where
  chern : p
  decomposition_iso : q
  decomposition_eq : r
  twisted_unit : s
  twisted_chern : t

/-- The five canonical normalization clauses over a single base.
Source: det-sp-p1-trace, clauses 1--2 (blueprint: def-sp-p1-proetale-trace-system). -/
def SpP1NormalizedAt (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (c : SpP1ChernFamily A N hA) (b : SpP1TwistedFamily A N hA)
    (d : SpP1DecompositionFamily A N hA) (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) : Prop :=
  SpP1NormalizationClauses
    (Etale.ordinaryFiniteP1ChernSpec A N hA S
        ((map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
          hS.map (ProjectiveLine S ↘ S).appTop.hom) (c S hS))
    (IsIso (d S hS))
    (HEq (d S hS)
        (geoP1SumComparison A S (Etale.ordinaryFiniteUnit A S)
            (Etale.p1DecompositionTwist A N hA S (-1) (-2)) ≫
            (geoP1Comparison A S).map (Etale.p1DecompositionMap A N hN hA S hS (c S hS)) ≫
            geoP1PushComparison A (ProjectiveLine S ↘ S)
              (Etale.ordinaryFiniteUnit A (ProjectiveLine S))))
    (HEq (biprod.inl ≫ (b S hS).hom) (geoP1TwistedUnit A N hN hA S hS))
    (HEq (biprod.inr ≫ (b S hS).hom)
    (geoP1ChernPushforward A N hA S (c S hS)))

/-- The exact unit-and-Kummer formula, its invertibility, and the twisted components.
Source: det-sp-p1-trace, clauses 1--2 (blueprint: def-sp-p1-proetale-trace-system). -/
def SpP1NormalizedDecompositions (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (c : SpP1ChernFamily A N hA) (b : SpP1TwistedFamily A N hA)
    (d : SpP1DecompositionFamily A N hA) : Prop :=
  ∀ (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))),
    SpP1NormalizedAt A N hN hA c b d S hS

/-- The canonical supported diagonal integrals over one Noetherian base.
Source: det-sp-p1-trace, clause 3 (blueprint: det-sp-p1-trace). -/
def SpP1DiagonalIntegralsAt (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (b : SpP1TwistedFamily A N hA) (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (N : Γ(S, ⊤))) : Prop :=
  ∃ (hI : (pullback.diagonal (ProjectiveLine S ↘ S)).ker.IsInvertible)
    (κ : Ext
      ((Etale.lowerStar (ModuleCat.{u + 1} A)
        (pullback.diagonal (ProjectiveLine S ↘ S))).obj
          (Etale.ordinaryFiniteConstant A (ProjectiveLine S)))
      (Scheme.finiteEtaleTateLine
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) 2)
    (cΔ : GeoCartierClass A N hA (pullback.diagonal (ProjectiveLine S ↘ S))),
    (Etale.SupportedKummerBoundary A N hA (pullback.diagonal (ProjectiveLine S ↘ S)) hI
      ((map_natCast ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
        (ProjectiveLine S ↘ S)).appTop.hom N) ▸
          hS.map ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
            (ProjectiveLine S ↘ S)).appTop.hom) κ) ∧
    (SpP1CartierCompatibility
      (comparisonUpperStar (ModuleCat.{u + 1} A)
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))
      (geoCartierSourceComparison A (pullback.diagonal (ProjectiveLine S ↘ S))) κ cΔ) ∧
    ∃ hE : PreservesFiniteColimits
        (lowerStar (ModuleCat.{u + 1} A) (pullback.diagonal (ProjectiveLine S ↘ S))),
      DiagonalIntegralCondition
        (@geoP1DiagonalKernelData A inferInstance N hN hA S hS hE cΔ)
        (geoP1Trace A N hA (ProjectiveLine S)
          (b (ProjectiveLine S)
            ((map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
              hS.map (ProjectiveLine S ↘ S).appTop.hom)))

/-- The canonical source, diagonal-class, and projection-trace formulas, and both
integral identities. The canonical formulas uniquely determine every arrow.
Source: det-sp-p1-trace, clause 3 (blueprint: det-sp-p1-trace). -/
@[irreducible]
def SpP1DiagonalIntegrals (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (b : SpP1TwistedFamily A N hA) : Prop :=
  ∀ (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))),
    SpP1DiagonalIntegralsAt A N hN hA b S hS
```

## Users

Read-only `tools/downstream.py` was run for all three family names and for the
item's diagonal predicate. The system's sole existing downstream module is the
assigned item. Its family consumers are the defining module and that item. The
item has zero downstream modules and is its diagonal predicate's sole consumer.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTraceSystem | unclaimed | Store the same functions and five normalization conditions through the interfaces above. |
| Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTrace | P4, assigned | Preserve theorem signatures; construct and project the canonical data through the new interfaces. |
| Sheaf.AlgebraicGeometry.SpP1NormalizedFamilyCore | P4, new | Wrap the constructed ordinary family and two explicitly constructed comparison families. Prove the same five conditions. |
| Sheaf.AlgebraicGeometry.SpP1RationalPointChern | P4, new | Select the named Chern-specification field. |
| Sheaf.AlgebraicGeometry.SpP1BaseChangeOfNormalized | P4, new | State the arbitrary-base exchange consequence of the same five conditions. |
| Sheaf.AlgebraicGeometry.ProEtaleP1DiagonalComponents | P4, new | Share the unchanged Ext comparison predicate; store the literal canonical maps with HEq to uniquely fixed typed representatives in the pre-trace component data. |

No module held by another group is adapted. Compilation results are recorded in
report.md. The original unit routes and all adopted source declarations remain.

## Status

landed 20261021T023317-L-2947720 2026-10-21 (merge of deliver/P4/Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTrace)
