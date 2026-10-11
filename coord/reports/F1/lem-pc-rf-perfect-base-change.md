## Worker report

`Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange` states
`AlgebraicGeometry.perfect_derivedDirectImage_baseChange`, with a `sorry` proof only.
The earlier attempt used Mathlib's abstract module pullback and an unpinned
`Nonempty` isomorphism. Both mismatches are repaired: the target is the shared tensor
pullback, and the conclusion is invertibility of the actual canonical map.

Hypothesis and clause correspondence:
- S and X schemes: `{X S : Scheme.{uPF}}`.
- f a morphism: `f : X ⟶ S`.
- f proper: `[IsProper f]`.
- f of finite presentation: `[LocallyOfFinitePresentation f]`, `[QuasiCompact f]`,
  `[QuasiSeparated f]`, exactly the project's recorded convention. The last two also
  follow from properness; they add no geometric restriction.
- G an O_X-module: `G : X.Modules`.
- G finitely presented: `[SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) G]`.
- G flat over S: `hG : G.IsFlatOver f`, the upstream affine-section predicate, not
  flatness over O_X and not flatness of f.
- Rf_*G uses `schemeDerivedDirectImage f` applied to `DerivedCategory.singleFunctor`
  on the shared `SheafOfModules` category at degree zero.
- Perfectness: `Scheme.IsPerfect S` of this derived object, the recorded local
  bounded finite-projective model definition.
- Every morphism g: `∀ {T : Scheme.{uPF}} (g : T ⟶ S)`; no flatness, reducedness,
  Noetherianity, affineness or nonemptiness is imposed on T or g.
- The canonical map is invertible: `IsIso (derivedModuleBaseChangeMap f g G)`.
  Its source is Lg^*(Rf_*G[0]); its target is R(pullback.snd)_* of the degree-zero
  module `(Scheme.Modules.tensorPullback (pullback.fst f g)).obj G`.
- The localization family for every scheme and the localization instances for the
  opens of S supply the categories used by these definitions; they impose no
  additional mathematical hypothesis. No injective-resolution assumptions remain.

Dependencies read and used: `BaseChangeConventions` fixes `pullback f g`, with fst to
X and snd to T, and uses `Scheme.Modules.tensorPullback` for module base change;
`DerivedCategory.schemeDerivedCategory` is the derived category on the shared
`SheafOfModules` instance; `SchemeDerivedDirectImage.schemeDerivedDirectImage`
is the unbounded ringed-space K-injective derived direct image;
`DerivedPullback.derivedPullback` has the left-derived universal property and K-flat
computation; `PerfectComplex.Scheme.IsPerfect` is the recorded perfectness predicate.
The morphism-conventions dependency has no declaration of its own and names the
Mathlib classes used above. Upstream `DirectImage.Basic.Scheme.Modules.IsFlatOver`
is relative flatness on affine sections. The general comparison is
`SchemeDerivedBaseChangeMap.schemeDerivedBaseChangeMap` and uses the canonical
composition data of `DerivedPullbackComposition.exists_derivedPullbackComposition`.
The module comparison uses `TensorPullbackAdjunction.exists_tensorPullbackAdjunction`
and the Hom equivalence in `SchemeDerivedAdjunction.exists_schemeDerivedAdjunction`.

Edge cases checked: zero G gives the zero canonical map between zero derived objects;
identity g gives the usual identity comparison under the unit identifications; empty
X or T is allowed. A closed immersion need not be flat; no `[Flat f]` is imposed.
G is embedded at degree zero, independent of derived cohomological conventions.
The same arbitrary universe uPF covers all schemes in each base-change square.

Searches: msearch LeanFinder for "proper finite presentation flat finitely presented
module perfect derived direct image arbitrary base change" returned ring smoothness,
module projectivity and faithfully-flat ring facts, no scheme-derived theorem.
Loogle for "IsProper, LocallyOfFinitePresentation" returned unknown identifier
IsProper. Mathlib grep for "perfect|derived.*[Bb]ase[Cc]hange" in AlgebraicGeometry
returned six perfect-field smoothness hits only. LeanSearch for the canonical map
was unavailable (Internal Server Error). `rg` in WeilConjectures for this node's id
and perfect/baseChange combinations found no matching theorem; upstream DirectImage
encodes finite free complexes and higher direct images, not this unbounded statement.
The new node's `mathlib_searches` includes the raw missing-map search results.
No statement is disputed.

Source checked directly: https://stacks.math.columbia.edu/tag/0B91, clause (2), and
https://stacks.math.columbia.edu/tag/08HY. The proof docstring carries both steps
of the node, including all support/properness and tensor-unit ingredients.

## New nodes

`def-pc-derived-module-base-change-map` defines the comparison for degree-zero modules
with the ordinary tensor-pullback target. The helper `derivedModulePullbackComparison`
is the derived-adjunction transpose of the ordinary tensor-pullback unit followed by
the right-derived direct-image unit, using Mathlib's single-complex functor comparison.
`derivedModuleBaseChangeMap` is general derived base change followed by Rf_T applied
to that comparison. Both definitions have full data, without sorry. Source: Stacks
08HY and the ordinary pullback target of 0B91(2). Searches of DAG nodes and blueprint
references found no definition of this degree-zero map; FlatComplexDerivedPullback
is an invertibility theorem for a different flatness hypothesis. LeanFinder returned
underived sheaf pullback/free-module maps, Loogle no expected-name hit, Mathlib grep
no match, and source/project rg no definition with these signatures.

## Dependency modules

`def-pc-derived-base-change-map` has no Lean record on the base. Its module defines the
canonical counit mate of the derived pullback composition comparison, as in 08HY,
equivalently the unit/direct-image-composition construction in its node. It accepts
any commutative square, including the prescribed restriction to an open and its
inverse image. The chosen derived adjunctions are pinned to the same left-derived
counits and right-derived units; arbitrary adjunction twists are excluded.

`lem-pc-ringed-spaces-derived-adjoint` now has the bare-existence record
`DerivedAdjoint.nonempty_derivedPullbackAdjunction` on the base. It cannot pin the
canonical map relative to the comparison counits and units. The dependency module states
the unbounded scheme derived adjunction, with the canonical compatibility equation
for the Hom equivalence on homotopy representatives. The additive instance binders
for the Scheme.Modules and shared SheafOfModules presentations are supplied from
exists_derivedPullbackComposition. The equation ensures the module comparison is the
canonical derived-to-ordinary map rather than a transpose under an arbitrary twist.

The previously missing SchemeDerivedDirectImage object is now available on the server.
Its temporary copy was removed; the original recorded dependency is imported.

## Statement corrected

The original mathematical hypotheses and conclusions agree with 0B91(2). Its list
of dependencies named both functors but no construction of their canonical comparison
with ordinary module pullback as target. Merely asserting existence of an isomorphism
between these objects would weaken its canonical-map claim. The statement now names
the general canonical map, its degree-zero specialization, and the derived adjunction.
This only specifies the source's comparison: no hypothesis or conclusion changes.
The node's `statement_change.old_statement` retains the original text verbatim.
Source: Stacks 0B91(2) and 08HY. The following are every stmt_deps/proof_deps citer:

- lem-pd-degree-locally-constant: holds true; The proper finite-presentation, relatively flat module, perfectness and arbitrary canonical base-change conclusions are unchanged; only the previously unnamed comparison construction is specified.

- thm-pc-semicontinuity-base-change: holds true; The proper finite-presentation, relatively flat module, perfectness and arbitrary canonical base-change conclusions are unchanged; only the previously unnamed comparison construction is specified.

- lem-pc-flat-rf-open: holds true; The proper finite-presentation, relatively flat module, perfectness and arbitrary canonical base-change conclusions are unchanged; only the previously unnamed comparison construction is specified.

- lem-sc-picard-h1-multiple-locus: holds true; The proper finite-presentation, relatively flat module, perfectness and arbitrary canonical base-change conclusions are unchanged; only the previously unnamed comparison construction is specified.

- lem-sc-proper-flat-global-sections-criterion: holds true; The proper finite-presentation, relatively flat module, perfectness and arbitrary canonical base-change conclusions are unchanged; only the previously unnamed comparison construction is specified.

- lem-sc-picard-diagonal-locally-closed: holds true; The proper finite-presentation, relatively flat module, perfectness and arbitrary canonical base-change conclusions are unchanged; only the previously unnamed comparison construction is specified.

- lem-sc-valuation-proper-coherent-higher-direct-images: holds true; The proper finite-presentation, relatively flat module, perfectness and arbitrary canonical base-change conclusions are unchanged; only the previously unnamed comparison construction is specified.

## Second reading by F1

I independently read the node, its Stacks source, every dependency record, and all four
Lean modules in this delivery. The source (Stacks Tag 0B91, clause (2)) introduces a scheme
S, a proper finite-presentation morphism f : X → S, and an O_X-module G finite presentation
and flat over S; it concludes that Rf_*G is perfect and that for every g : T → S the
canonical map Lg^*Rf_*G → Rf_{T,*}G_T is an isomorphism. Remark 08HY specifies this as the
canonical unbounded-derived base-change construction.

The Lean renders S and X as `{X S : Scheme.{uPF}}`, f as `f : X ⟶ S`, properness,
finite presentation, quasi-compactness and quasi-separatedness as the four typeclass
binders, and G as `G : X.Modules` with finite presentation and `hG : G.IsFlatOver f`.
The derived object is `schemeDerivedDirectImage f` applied to the degree-zero
`DerivedCategory.singleFunctor` object. The first conjunct is
`Scheme.IsPerfect S` of that object. The second conjunct quantifies exactly over
`{T : Scheme.{uPF}} (g : T ⟶ S)` and asserts `IsIso (derivedModuleBaseChangeMap f g G)`.
The map's source is derived pullback of Rf_*G and its target is derived direct image of
the degree-zero tensor pullback module along the fibre-product projection, matching G_T
under the flatness hypothesis. The local-open derived-category instance is required by
the
project's `Scheme.IsPerfect` encoding and imposes no geometric condition; analogous
landed statements use the same binder.

The dependency modules render `schemeDerivedBaseChangeMap` from the canonical derived
adjunction and composition comparison, `derivedModuleBaseChangeMap` by composing that map
with the derived-to-ordinary tensor-pullback comparison, and the pinned derived adjunction
with its compatibility equation. Their declarations and node records agree verbatim.
No hollow definition or private copy was found; only the theorem proof is `sorry`.

Edge cases checked: arbitrary (including empty) T and X are allowed; g may be an identity,
closed immersion, or non-flat map; G may be zero; the degree is fixed at zero; no
Noetherian, reduced, affine, or nonemptiness hypothesis is added; all schemes in a square
share the same universe. The characteristic is unrestricted.

Searches were repeated with `rg` over Mathlib, WeilConjectures, and lean/Sheaf, with
LeanFinder/Loogle queries for proper finite-presentation derived pushforward perfectness
and canonical base change, and with the recorded LeanSearch query. No existing declaration
matches these notions; the newly added map and adjunction nodes are therefore necessary.
The Stacks pages were checked directly at tags 0B91 and 08HY.

The only repair made in this second reading was to keep the explicit local-open
`HasDerivedCategory` binder in the main theorem and its node signature: removing it makes
`Scheme.IsPerfect` fail to synthesize its required localization instances. This is a
formalization instance requirement already used by the project's landed perfectness
statements, not a mathematical hypothesis. No source clause or edge case is omitted.
