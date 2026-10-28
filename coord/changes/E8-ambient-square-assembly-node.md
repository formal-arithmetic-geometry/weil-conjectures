# AlgebraicGeometry.ProEtale.RationalP1.ambient_square_assembly

## Reason

Close the categorical square-assembly hole by a private lemma using only
associativity and cancellation of a natural isomorphism.

The original explicit derived-functor expressions fail to synthesize the
fourfold graded-tensor instance with transparency controls enabled. Replacing
only those expressions by moduleObjectDerivedPullback still gives deterministic
kernel timeouts. The existing typed interface QuotientChange.L and
scalarPullbackComposition, explicit nested source types, and the defining
composite for the square comparison make the complete proof check in seconds.
All functors and compositors retain their published canonical definitions.

The node prose was copied verbatim from
lem-sfb-rational-tate-line-comparison-composition, although its existing Lean
attachment and docstring describe categorical square assembly. Correct that
prose and record both citers in statement_change. The separate Tate-line
composition theorem remains an obligation of the parents.

## Old


```lean
theorem ambient_square_assembly
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)
    {A : DerivedCategory (Modules Λ Y)} {B : DerivedCategory (Modules Λ X)}
    {B' : DerivedCategory (Modules Λ Y')} {Q : DerivedCategory (Modules Λ X')}
    (e : (moduleObjectDerivedPullback Λ f).obj A ⟶ B)
    (j : (moduleObjectDerivedPullback Λ g).obj A ⟶ B')
    (d : (moduleObjectDerivedPullback Λ g').obj B ⟶ Q)
    (e₂ : (moduleObjectDerivedPullback Λ f').obj B' ⟶ Q)
    (s₁ : (CondensedRing.upperStar Λ (g' ≫ f)).leftDerivedFunctor.obj A ⟶ Q)
    (s₂ : (CondensedRing.upperStar Λ (f' ≫ g)).leftDerivedFunctor.obj A ⟶ Q)
    (h₁ : (CondensedRing.leftDerivedUpperStarComp Λ g' f).hom.app A ≫
      (moduleObjectDerivedPullback Λ g').map e ≫ d = s₁)
    (h₂ : (CondensedRing.leftDerivedUpperStarComp Λ f' g).hom.app A ≫
      (moduleObjectDerivedPullback Λ f').map j ≫ e₂ = s₂)
    (he : (eqToIso (congrArg (fun a : X' ⟶ Y ↦ (CondensedRing.upperStar Λ a).leftDerivedFunctor)
      sq.toCommSq.w.symm)).hom.app A ≫ s₁ = s₂) :
    (condensedAmbientPullbackComparison Λ sq).hom.app A ≫
      (moduleObjectDerivedPullback Λ g').map e ≫ d =
      (moduleObjectDerivedPullback Λ f').map j ≫ e₂
```

Original imports:

```lean
public import Sheaf.Paper.DerivedExchangeExactNormalization
public import Sheaf.Paper.CondensedAmbientExchange
public import Sheaf.Paper.RationalTatePullback
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
```

Old node statement, verbatim:

For a prime l, a finite rational coefficient index c or the algebraic-closure index, and composable scheme arrows f:X→Y and g:Y→Z with l invertible in every residue field of X,Y,Z, let Λ=(coefficient l c).X and L_A=line l c A as in [def-sfb-rational-tate-pullback-comparison]. Then the canonical underived internal-module compositor c_f,g:(f≫g)*≅g*⋙f*, followed by f* of lineComparison(g) and lineComparison(f), equals lineComparison(f≫g). This is an equality of unshifted module maps, before taking degree-zero complexes, derived functors, shifts, exchange mates or adjunction units.

## New

```lean
theorem ambient_square_assembly
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)
    {A : DerivedCategory (QuotientChange.Modules Λ Y)}
    {B : DerivedCategory (QuotientChange.Modules Λ X)}
    {B' : DerivedCategory (QuotientChange.Modules Λ Y')}
    {Q : DerivedCategory (QuotientChange.Modules Λ X')}
    (e : (QuotientChange.L Λ f).obj A ⟶ B)
    (j : (QuotientChange.L Λ g).obj A ⟶ B')
    (d : (QuotientChange.L Λ g').obj B ⟶ Q)
    (e₂ : (QuotientChange.L Λ f').obj B' ⟶ Q)
    (s₁ : (QuotientChange.L Λ (g' ≫ f)).obj A ⟶ Q)
    (s₂ : (QuotientChange.L Λ (f' ≫ g)).obj A ⟶ Q)
    (h₁ : (QuotientChange.scalarPullbackComposition Λ g' f).hom.app A ≫
      (show (QuotientChange.L Λ g').obj
        ((QuotientChange.L Λ f).obj A) ⟶ Q from
          (QuotientChange.L Λ g').map e ≫ d) = s₁)
    (h₂ : (QuotientChange.scalarPullbackComposition Λ f' g).hom.app A ≫
      (show (QuotientChange.L Λ f').obj
        ((QuotientChange.L Λ g).obj A) ⟶ Q from
          (QuotientChange.L Λ f').map j ≫ e₂) = s₂)
    (he : (eqToIso (congrArg (fun a : X' ⟶ Y ↦ QuotientChange.L Λ a)
      sq.toCommSq.w.symm)).hom.app A ≫ s₁ = s₂) :
    ((QuotientChange.scalarPullbackComposition Λ f' g).symm ≪≫
      eqToIso (congrArg (fun a : X' ⟶ Y ↦ QuotientChange.L Λ a)
        sq.toCommSq.w.symm) ≪≫
      QuotientChange.scalarPullbackComposition Λ g' f).hom.app A ≫
      (show (QuotientChange.L Λ g').obj
        ((QuotientChange.L Λ f).obj A) ⟶ Q from
          (QuotientChange.L Λ g').map e ≫ d) =
      (show (QuotientChange.L Λ f').obj
        ((QuotientChange.L Λ g).obj A) ⟶ Q from
          (QuotientChange.L Λ f').map j ≫ e₂)
```

QuotientChange.Modules and DiagonalCoefficients.Modules both expand to the same
Mod category over condensedRingObj. QuotientChange.L is exactly
CondensedRing.moduleObjectDerivedPullback, whose body is the original
(upperStar Λ f).leftDerivedFunctor. scalarPullbackComposition is exactly
leftDerivedUpperStarComp with that interface exposed. These are existing
published definitions, not new choices or assumptions.

The comparison in the conclusion is written as the defining expression of
scalarPullbackSquare. Unfolding those same existing aliases gives precisely the
original condensedAmbientPullbackComparison. The show expressions only specify
the already intended nested source of each composite map. Thus no mathematical
hypothesis or conclusion changes. No target or shared definition is edited.

The single public import is Sheaf.Paper.ScalarPullbackSquareCoherence, which
supplies the definitions in the statement. The proof does not use that module's
coherence theorem. All four old direct imports are removed.

The corrected node statement is:

Let Λ be a commutative condensed ring and let sq be a chosen cartesian square of schemes with arrows g′:X′→X, f′:X′→Y′, f:X→Y and g:Y′→Y, as in [def-weil-pbc-cartesian-square]. Write D(T)=D(QuotientChange.Modules Λ T) and P(a)=QuotientChange.L Λ a for the canonical internal-module derived categories and total derived pullbacks of [def-sfb-internal-derived-scalar-comparisons]. Let A∈D(Y), B∈D(X), B′∈D(Y′), Q∈D(X′), and maps e:P(f)A→B, j:P(g)A→B′, d:P(g′)B→Q, e₂:P(f′)B′→Q be given. Let c₁:P(g′≫f)≅P(f)⋙P(g′) and c₂:P(f′≫g)≅P(g)⋙P(f′) be the canonical compositors scalarPullbackComposition of [def-sfb-scalar-pullback-square-data]. Let t:P(f′≫g)≅P(g′≫f) be transport along the equality of the two composites given by sq. Suppose maps s₁:P(g′≫f)A→Q and s₂:P(f′≫g)A→Q satisfy c₁.hom_A≫P(g′)(e)≫d=s₁, c₂.hom_A≫P(f′)(j)≫e₂=s₂, and t.hom_A≫s₁=s₂. Then (c₂.symm≪≫t≪≫c₁).hom_A≫P(g′)(e)≫d=P(f′)(j)≫e₂. The displayed composite is exactly the defining expression of scalarPullbackSquare and hence the same canonical ambient pullback comparison of [def-weil-pbc-ambient-ringed-exchange]. This is categorical assembly from the supplied leg equations, without an additional geometric compatibility assumption.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.AmbientSquareAssembly | E8 | Close its single proof hole. |
| Sheaf.Paper.ShiftedLineSquare | F8 | Same mathematical assembly statement; compile unchanged. |
| Sheaf.Paper.ScalarP1UnitMateComponent | unclaimed | Same mathematical assembly statement; compile unchanged. |
| Sheaf.Paper.ScalarComponentFromTrace | F6 | Its node still cites the same categorical assembly step. |

The citing nodes are lem-sfb-rational-p1-scalar-chern-base-change-unit-component-core
and lem-sfb-scalar-component-from-trace. Their geometric obligations stay
separately stated. downstream.py --uses ambient_square_assembly finds no current
consumer application. Both direct importers publicly import
RationalP1ScalarChernMaps, through which they retain the old public imports.
Compile results against the delivered module are recorded in report.md.

## Status

landed 20261028T072405-L-1941985 2026-10-28 (merge of deliver/E8/Sheaf.Paper.AmbientSquareAssembly)
