# Compact-support normalization graph construction and helper relocation

## Reason

The explicit graph map must be available to the three strictly smaller property modules
without importing the theorem that uses them. Move the eight existing helper declarations
into a public data module, then publicly reexport that module from the original module.
Every original helper's signature and body, the full normalization structure, its field
order and the original theorem signature are unchanged. There is no definition repair or
claim of semantic change: this is a module dependency refactoring for a proof reduction.

All new data are actual constructions: a pullback graph, the clopen projection via the
canonical extension-to-direct-image isomorphism, adjunction transpose, localization
preimage, and the inverse of a specified isomorphism. The inverse is uniquely determined;
no arbitrary witness is selected from a holed mere-existence theorem.

## Old

The following public signatures occurred in
`Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization`:

```lean
noncomputable def compactificationSheafToDirectImage
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}} {f : U ⟶ X}
    (c : Compactification f) :
    openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
      lowerStar (ModuleCat.{u + 1} A) c.g ⟶ lowerStar (ModuleCat.{u + 1} A) f

noncomputable def exactEtaleSumExchange
    (A : Type (u + 1)) [CommRing A] {U X X' : Scheme.{u}}
    (f : U ⟶ X) [Etale f] (g : X' ⟶ X) :
    (etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ≅
      (upperStar (ModuleCat.{u + 1} A) (pullback.snd g f)).mapDerivedCategory ⋙
        (etaleLowerShriek (ModuleCat.{u + 1} A) (pullback.fst g f)
          inferInstance).mapDerivedCategory

noncomputable def exactCompactSupportExchange
    (A : Type (u + 1)) [CommRing A] {U X X' : Scheme.{u}}
    {f : U ⟶ X} (c : Compactification f) (g : X' ⟶ X) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ⟶
      (upperStar (ModuleCat.{u + 1} A) (pullback.snd g f)).mapDerivedCategory ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
          (c.ofIsPullback (IsPullback.of_hasPullback g f).flip)

noncomputable def exactCompactSupportExchangeSquare
    (A : Type (u + 1)) [CommRing A] {U X X' : Scheme.{u}}
    {f : U ⟶ X} (c : Compactification f) (g : X' ⟶ X)

noncomputable def exactEtaleSumExchangeSquare
    (A : Type (u + 1)) [CommRing A] {U X X' : Scheme.{u}}
    (f : U ⟶ X) [Etale f] (g : X' ⟶ X)

noncomputable def compactSupportComparisonOnHomotopy
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}} (f : U ⟶ X) [Etale f]
    (c : Compactification f)
    (a : etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g)
    (K : HomotopyCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
      (ComplexShape.up ℤ)) :
    (etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance).mapDerivedCategory.obj
        (DerivedCategory.Qh.obj K) ⟶
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
        (DerivedCategory.Qh.obj K)

def refinementOpenCompactification
    {U X : Scheme.{u}} {f : U ⟶ X} {c d : Compactification f}
    (r : c.Refinement d) : Compactification d.i

noncomputable def identityEtaleCompactSupportComparison
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (Compactification.ofIsProper (𝟙 X)) ≅
      (etaleLowerShriek (ModuleCat.{u + 1} A) (𝟙 X) inferInstance).mapDerivedCategory
```

## New

The identical signatures and bodies occur in
`Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalizationData`, and the original module
publicly imports it. All old fully qualified declaration names remain available to every
old importer. The original structure is byte-for-byte identical. No target meaning changes.

```lean
public import Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalizationData
```

## Users

`tools/downstream.py --uses` was rerun for all eight relocated helpers on the repair
base. It lists `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality` as the one downstream
module and as a user of `compactificationSheafToDirectImage` (two occurrences). The other
seven helpers are mentioned only by the original item module. The public reexport preserves
all eight declarations, including the unchanged body of `compactificationSheafToDirectImage`.
The consumer's private monomorphism and comparison-uniqueness proofs therefore keep their
statements and proofs unchanged. No existing consumer requires adaptation. The five new
property modules are also recorded below.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization | J4 | Public data import; unchanged structure and theorem signature, real constructor proof. |
| Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality | unclaimed; unchanged | Uses compactificationSheafToDirectImage twice; identical definition publicly reexported; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalizationData | J4, new | Eight old bodies preserved; explicit graph construction and component formula. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphSheafNormalization | J4, new | Property of the explicit sheaf map. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportFiniteGraphIso | J4, new | Proved finite-etale specialization, with no new holes. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphGeometricBaseChange | J4, new | Forward-map identity at geometric base changes. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphDerivedIso | J4, new | Proved general isomorphism property; its unique inverse defines the canonical core. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphCoherence | J4, new | Three remaining equations for that canonical core. |

## Status

landed 20261018T091405-L-3255847 2026-10-18 (merge of deliver/J4/Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization)

## Repair C5 (reviewer C-fef35)

The earlier delivery duplicated the canonical graph map from
`def-f7-etale-compactification-graph-map`. The data module now publicly imports
`Sheaf.AlgebraicGeometry.EtaleCompactificationGraphMap`; the seven duplicate graph and
projection declarations are removed, while the refinement and identity helpers remain.
The four property modules are forced adaptations of this J4 item and replace every use of
`compactSupportGraphSheafComparison A` by `etaleCompactificationGraphMap A`; their theorem
signatures are otherwise unchanged. The definition node now describes `Da` built from F7's
`a_c`, adds the F7 dependency and same-as reference, and records
`compactSupportDerivedComparison` as its Lean declaration. The four dependent nodes record
the F7 statement dependency. This is a definition relocation/duplication repair and does
not alter any target statement.

## Repair C-30a0f: source-complete canonical graph dependency

The preceding reviewed head 30a0f75ae imported the canonical F7 map, but the
landing base lacks both its source and definition node. The repair includes
`lean/Sheaf/AlgebraicGeometry/EtaleCompactificationGraphMap.lean` itself, with its
unchanged explicit construction, and `def-f7-etale-compactification-graph-map`.
The canonical map remains the only definition of this notion. Its direct new
consumer is EtaleCompactSupportNormalizationData, and the graph sheaf, finite
isomorphism, derived isomorphism and geometric-base-change modules use its name
through that public import. No existing consumer requires an adaptation for
adding this absent source. Server compilation checks the full eight-module set.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleCompactificationGraphMap | unclaimed at current base; retained F7 source | Bundled canonical definition, no holes or interface change relative to the reviewed return. |
