## Worker report

The delivery states `AlgebraicGeometry.reducedAffineInjectiveFactor_stalkComparison` in
`Sheaf.AlgebraicGeometry.ReducedAffineInjectiveFactorStalkComparison`. Its sole proof is
`sorry`; no definitions, auxiliary assertions, or additional nodes are introduced. The
node copy changes only `lean`.

Source read: `literature/stacks-project/varieties.tex`, Tag 09NI,
`lemma-points-in-affine`, lines 8952 onwards, especially the middle paragraph introducing
the image subring R', the generic-point lifts, and the three local rings. The item is
the extracted intermediate comparison, not the full affine-neighbourhood lemma. Its
eight-step proof is reproduced in the theorem docstring, including the local-spectrum
lifting argument and the reduced-localization kernel argument.

Hypotheses, objects, and conclusions matched against the node:

- The commutative rings are `(R B : Type u) [CommRing R] [CommRing B]`. The instances
  `[_root_.IsReduced R] [_root_.IsReduced B]` say that their nilpotent elements vanish.
  The root qualifier distinguishes reduced rings from the scheme predicate.
- The injective unital ring homomorphism u is `(φ : B →+* R)` with
  `(hφ : Function.Injective φ)`. `RingHom` includes preservation of one.
- T and Y are written out as `Spec (CommRingCat.of R)` and `Spec (CommRingCat.of B)`.
  The canonical h is always `Spec.map (CommRingCat.ofHom φ)`. It is not an arbitrary
  morphism having the same effect on points. The target is `(X : Scheme.{u})` and
  `(g : Spec (CommRingCat.of B) ⟶ X)`. The composite f is written as `h ≫ g`.
- T⁰, Y⁰, X⁰ use Mathlib's existing `genericPoints`. Its definition in
  `Mathlib.Topology.Sober` is `{x | closure {x} ∈ irreducibleComponents _}`. Thus x is
  precisely an `IsGenericPoint` of a component: `IsGenericPoint x Z` means
  `closure {x} = Z`. The recorded generic-point and component definitions are used
  without making another definition or choosing a generic point.
- Finite T⁰ is `(hfinite : (genericPoints (Spec (CommRingCat.of R))).Finite)`. It is
  retained even though the explicit proof of the comparison does not need finiteness.
- The condition f(T⁰) ⊆ X⁰ is `hgeneric : Set.MapsTo (h ≫ g) T⁰ X⁰`.
- Injectivity of f on T⁰ is `hinjective : Set.InjOn (h ≫ g) T⁰`.
- The first conclusion is `Set.BijOn h T⁰ Y⁰`: h maps into Y⁰, is injective there,
  and has image all of Y⁰. This expresses a bijection induced by h itself.
- The second conclusion is `Set.MapsTo g Y⁰ X⁰ ∧ Set.InjOn g Y⁰`, expressing both
  that g's generic images lie in X⁰ and that its restriction is injective.
- The stalk conclusion quantifies `∀ t : Spec (CommRingCat.of R)`. The point y is
  written as `h t`; x is `g (h t)`, also the value of the canonical composite.
  The antecedent is `IsIso (g.stalkMap (h t) ≫ h.stalkMap t)`. Diagrammatic composition
  gives exactly O(X,x) → O(Y,y) → O(T,t). It is a hypothesis about this specific
  composite, not the existence of some isomorphism between the rings.
- The stalk conclusions are `Function.Injective (h.stalkMap t).hom`,
  `IsIso (g.stalkMap (h t))`, and `IsIso (h.stalkMap t)`, in that order. The `.hom`
  is the underlying ring homomorphism; categorical `IsIso` here means isomorphism
  in `CommRingCat`, equivalently an invertible unital ring homomorphism.

Statement dependency declarations read and used:

- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`; both definitions and signatures were read.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom` in the same module;
  morphisms are written using its category notation.
- `def-sc-generic-point`: `IsGenericPoint`, `Mathlib.Topology.Sober`; the equivalent
  component-point predicate is the existing `genericPoints` in that same module,
  whose definition and `genericPoints.isGenericPoint` were read.
- `def-weil-irreducible-components`: the recorded Mathlib match `irreducibleComponents`,
  `Mathlib.Topology.Irreducible`, occurs in `genericPoints`' definition. This dependency
  has no `lean` field; its usable `mathlib_match` is sufficient.
- `def-weil-pbc-module-stalk`: `PresheafOfModules.moduleStalkFunctor` and the associated
  `stalkObj`/`stalkMap`, `WeilConjectures.Topology.PresheafModuleStalkFunctor`. Its module
  is imported publicly as recorded. The item's stalks are structure-ring stalks,
  rather than stalks of an arbitrary module; they use the same Mathlib presheaf stalk
  construction, and the canonical morphism is `AlgebraicGeometry.Scheme.Hom.stalkMap`
  from `Mathlib.AlgebraicGeometry.Scheme`, whose signature and docstring were read.

All recorded proof-dependency modules that have declarations are also imported. The
Mathlib leaves are covered by `Mathlib.AlgebraicGeometry.Properties`,
`Mathlib.AlgebraicGeometry.AffineScheme`, `Mathlib.AlgebraicGeometry.Stalk`,
`Mathlib.RingTheory.Ideal.MinimalPrime.Localization`,
`Mathlib.RingTheory.Ideal.Operations`, `Mathlib.RingTheory.LocalProperties.Reduced`,
and `Mathlib.RingTheory.Spectrum.Prime.Topology`. The additional recorded upstream
dependency is `AlgebraicGeometry.Scheme.fromSpecStalk_local_properties` in
`WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism`, imported for the
proof. Its source and full signature were read. Statement imports are public;
imports used only in the future proof are plain imports.

Edge cases checked before writing:

- The zero ring is allowed: there is no `Nontrivial` or nonempty-spectrum hypothesis.
  If R is zero, injectivity of φ forces B to be zero. Both generic sets are empty,
  `BijOn` is the empty bijection, and there are no selected t for the stalk assertion.
- No surjectivity onto X⁰ is asserted: g only maps Y⁰ injectively into it.
- The stalk statement is conditional separately at each t. There is no assumption
  that the composite is a stalk isomorphism at every point.
- Generic, closed, and nonclosed selected points all satisfy the same quantifier.
  There is no noetherian, finite-type, separatedness, or quasi-separatedness assumption.
- With φ the identity, h and its stalk maps are the identity; the last implication
  reduces to the assumed isomorphism for g at t. Rings with several components are
  admitted, with injectivity required on all component generic points, not all points.
- The arbitrary universe u is explicit and `autoImplicit` is disabled. The schemes and
  rings share Mathlib's scheme universe convention; no independent smaller test universe
  or extra universe equality is imposed.

Searches actually run (Q46/item-qualified `msearch.py` on 2026-10-24):

- LeanFinder: "Injective ring map between reduced rings, finite generic points,
  factorization of scheme morphism injective on generic points, composite stalk map
  isomorphism implies both stalk maps isomorphisms". Eight results, including
  `spread_out_of_isGermInjective`, `stalkMap_injective_of_isAffine`, and
  `stalkMap_injective_of_isOpenMap_of_injective`. None states this comparison;
  they require germ-injectivity, a kernel condition, or openness and pointwise
  injectivity, respectively.
- Loogle: `AlgebraicGeometry.Scheme.Hom.stalkMap, Function.Injective`. Three results:
  `IsAffineOpen.stalkMap_injective`, `stalkMap_injective_of_isAffine`, and
  `stalkMap_injective_of_isOpenMap_of_injective`; none has the node's hypotheses
  or its generic-point conclusions.
- Mathlib grep: `stalkMap_injective|def genericPoints|reduced_affine`. Six results;
  the three stalk-injectivity interfaces above and `genericPoints` in
  `Mathlib/Topology/Sober.lean:277`. The latter is reused directly.
- LeanSearch: "An injective homomorphism of reduced rings induces a bijection on
  generic points if a composite scheme morphism is injective on component generic
  points, and factors a stalk isomorphism into two isomorphisms". Eight results,
  including the canonical affine stalk-map identification and open-immersion stalk
  isomorphisms, but no full comparison statement.
- `rg` over the upstream `lean/WeilConjectures` and project `lean/Sheaf` for
  `reduced_affine|injective_factor|lem-trf-reduced-affine-injective-factor-stalk-comparison|stalkMap_injective`
  found specialized dense-etale and punctured-DVR stalk results, unrelated reduced-affine
  constructions, and the consumer's proof-docstring citation. No duplicate statement.
- `grep -rn` for the exact item id in upstream `lean/WeilConjectures` returned no hits.
  `rg` for the proposed declaration name in Mathlib, upstream, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` returned no hits.

No statement correction, missing dependency, or mathematical dispute was found.

Validation: `scompile.py Q46 lem-trf-reduced-affine-injective-factor-stalk-comparison`
compiled the delivered file successfully in both sandbox mode (3.5 seconds) and its
library module mode (1.5 seconds), with no errors or unexpected warnings. The only
postponed proof is the item's theorem. The prescribed `deliver2.py --no-push`
completed with `OK (dry run)`: the preflight passed and the module compiled.

## Second reading by Q46

This is the author's second reading; the dispatcher brief assigns independent review
to the maintainer and prohibits starting other agents. I reopened the node and the
complete Lean file after compilation. The binders include both reducedness assumptions,
the injective unital ring map, arbitrary X and g, finite T⁰, the generic-image condition,
and injectivity of the composite on T⁰. `BijOn` includes the maps-to part and both
injectivity and surjectivity of h; the two subsequent set predicates give exactly
injectivity into X⁰ for g, without making g surjective. The final implication uses
the canonical g and h stalk maps at h(t) and t in the correct contravariant order.
It concludes injectivity of the second map and isomorphisms of both maps; there is
no replacement by an arbitrary isomorphism or extra local hypothesis. No nonempty
assumption excludes the empty case. Mathlib's `genericPoints` exactly combines the
recorded definitions of generic point and irreducible component. No mismatches were
found and no statement changes were needed on this second reading.
