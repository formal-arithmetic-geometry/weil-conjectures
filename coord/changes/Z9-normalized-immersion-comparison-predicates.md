# AlgebraicGeometry.Scheme.ImmersionComparisonRings.Functors and Functors.Normalized

## Reason

The complete proof encountered a deterministic kernel definitional-equality bottleneck when
specializing the arbitrary-category binary normalization theorem to six derived categories.
Profiling isolated it to `normalized_composite`: repeated comparison of the expanded
normalization and q-composition equations unfolded the derived-category instance towers.
A diagnostic kernel heartbeat bound of 20000 exposed this bottleneck; full attempts reached
the existing 60-second file timeout. Neither the timeout nor the production heartbeat budget
is raised.

Name the two equations over arbitrary categories, in new CategoryTheory modules, and use
those same predicate applications in both the generic proof and the scheme interface.
Unfolding each predicate gives exactly the original equation with the original quantifiers.
The supplied data, identity coherence, comparison composite, and all theorem signatures are
unchanged. There is no weakening, new hypothesis, chosen datum, or unproved property.
The full candidate compiled in 18.2 seconds; the final three module boundaries compiled
in 1.0, 0.9 and 19.9 seconds, respectively, with no warnings. After removing an unused
private helper, the final item compiled in 29.7 seconds, and the unchanged sole downstream
importer compiled in 59.2 seconds against it; both compiled without warnings.

The existing node's mathematical statement is unchanged. Its statement dependencies now
also name the two definition nodes, and its first proof step records the derived-normalization
bridge used by the implementation. No `statement_change` is needed because no mathematical
statement changed. All source-library declarations and modules remain unchanged.

The proof also locally gives the small reduction-category instance priority, locally marks
`mapDerivedCategory` and `proEtaleRingModulePullback` irreducible, and disables let-to-have
cleanup and elaborates the new proofs synchronously (`Elab.async false`).
These commands control proof elaboration only;
the new public predicate definitions and the pre-existing public definitions precede them.

## Old

```lean
def Functors (E : LocallyClosedExtensionData.{u}) (D : E.DerivedCoherence)
    (hG : G.Cartesian) :=
  { data : (Σ functor :
      ∀ (r s : I) (X : ImmersionComparisonBase.{u}), G.category r X ⥤ G.category s X,
      ∀ (r s : I) {S X : ImmersionComparisonBase.{u}}
    (a : S.val ⟶ X.val) [IsImmersion a],
    functor r s X ⋙ G.pull s a ≅ G.pull r a ⋙ functor r s S) //
    (∀ (r s : I) (X : ImmersionComparisonBase.{u}) (M : G.category r X),
    (data.2 r s (𝟙 X.val)).hom.app M ≫
        (data.1 r s X).map ((G.pullId E D hG r X).hom.app M) =
      (G.pullId E D hG s X).hom.app ((data.1 r s X).obj M)) ∧
    (∀ (r s : I) {S X T : ImmersionComparisonBase.{u}}
    (a : S.val ⟶ X.val) (b : T.val ⟶ S.val) [IsImmersion a] [IsImmersion b]
    (M : G.category r X),
    (data.2 r s (b ≫ a)).hom.app M ≫
        (data.1 r s T).map ((G.pullComp hG r a b).hom.app M) =
      (G.pullComp hG s a b).hom.app ((data.1 r s X).obj M) ≫
        (G.pull s b).map ((data.2 r s a).hom.app M) ≫
          (data.2 r s b).hom.app ((G.pull r a).obj M)) }

def Normalized {r s : I} {S X : ImmersionComparisonBase.{u}} {a : S.val ⟶ X.val}
    [IsImmersion a] (d : F.Comparison r s a) : Prop :=
  ∀ M : G.category r S,
    (G.pull s a).map (d.hom.app M) ≫
        (D.restriction (G.arrow s a)).hom.app ((F.functor r s S).obj M) =
      (F.q r s a).hom.app ((G.extend E r a).obj M) ≫
        (F.functor r s S).map ((D.restriction (G.arrow r a)).hom.app M)
```

## New

```lean
def Functors (E : LocallyClosedExtensionData.{u}) (D : E.DerivedCoherence)
    (hG : G.Cartesian) :=
  { data : (Σ functor :
      ∀ (r s : I) (X : ImmersionComparisonBase.{u}), G.category r X ⥤ G.category s X,
      ∀ (r s : I) {S X : ImmersionComparisonBase.{u}}
    (a : S.val ⟶ X.val) [IsImmersion a],
    functor r s X ⋙ G.pull s a ≅ G.pull r a ⋙ functor r s S) //
    (∀ (r s : I) (X : ImmersionComparisonBase.{u}) (M : G.category r X),
    (data.2 r s (𝟙 X.val)).hom.app M ≫
        (data.1 r s X).map ((G.pullId E D hG r X).hom.app M) =
      (G.pullId E D hG s X).hom.app ((data.1 r s X).obj M)) ∧
    (∀ (r s : I) {S X T : ImmersionComparisonBase.{u}}
    (a : S.val ⟶ X.val) (b : T.val ⟶ S.val) [IsImmersion a] [IsImmersion b],
    immersionComparisonComposition
      (G.pull r a) (G.pull r b) (G.pull r (b ≫ a))
      (G.pull s a) (G.pull s b) (G.pull s (b ≫ a))
      (G.pullComp hG r a b) (G.pullComp hG s a b)
      (data.1 r s X) (data.1 r s S) (data.1 r s T)
      (data.2 r s a) (data.2 r s b) (data.2 r s (b ≫ a))) }

def Normalized {r s : I} {S X : ImmersionComparisonBase.{u}} {a : S.val ⟶ X.val}
    [IsImmersion a] (d : F.Comparison r s a) : Prop :=
  immersionComparisonNormalized (G.pull r a) (G.pull s a)
    (G.extend E r a) (G.extend E s a)
    (D.restriction (G.arrow r a)) (D.restriction (G.arrow s a))
    (F.functor r s X) (F.functor r s S) (F.q r s a) d
```

The new predicate bodies are the equations shown under Old, with the arbitrary categories,
functors, counit isomorphisms, and q-isomorphisms supplied as explicit parameters. They are
`CategoryTheory.immersionComparisonNormalized` in
`Sheaf.CategoryTheory.ImmersionComparisonNormalized` and
`CategoryTheory.immersionComparisonComposition` in
`Sheaf.CategoryTheory.ImmersionComparisonComposition`; each has its own definition node.
The item publicly imports them because its public definition bodies refer to them.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.NormalizedImmersionComparisonCoherence
--uses Functors Normalized` lists one downstream module. Its name matches occur only
in the changed item; the downstream module imports the theorem privately and has no use
of either changed definition. It has been read in full and compiled unchanged against the delivered modules. The equations are definitionally
unchanged for every consumer, including the targets; no target statement acquires a
changed mathematical meaning. The maintainer's independent review should recheck this
fact as part of the definition review.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.NormalizedImmersionComparisonCoherence | Z9 | Own item: same normalization and q-composition equations, now named generically; proof completed. |
| Sheaf.Paper.SupportedCommonFieldScalarModels | unclaimed | Sole downstream importer; no reference to the changed definitions; no adaptation required. |

## Status

landed 20261024T191853-L-528293 2026-10-24 (merge of deliver/Z9/Sheaf.AlgebraicGeometry.NormalizedImmersionComparisonCoherence)
