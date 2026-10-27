## Worker report

The delivery states `AlgebraicGeometry.exists_keelMori_stabilizer_preserving_etale`
in `Sheaf.AlgebraicGeometry.KeelMoriStabilizerPreservingEtale`. There is one postponed theorem. This repair adds the bookkeeping definition
node `def-sfb-moduli-inertia-comparison` with `existing: true`; it records the
plain definitions `CategoryTheory.moduliInertiaMap` and
`CategoryTheory.moduliInertiaComparison` already present in the landed module. The statement of the DAG node is unchanged.
I read Stacks 0DUV, `lemma-etale-separated-over-keel-mori`, in
`literature/stacks-project/stacks-more-morphisms.tex`, including the comparison
squares and final universal-closedness argument. Its conclusion transports from
the constructed categorical spaces to the supplied categorical spaces by inverse
universal factorizations, as the node explicitly explains.

Hypothesis and clause correspondence:

- A field k: `(k : Type u) [Field k]`. All objects and maps are over `Spec (.of k)`.
- The two stacks: `X₁`, `X₂` are `BasedCategory` objects over `Over (Spec (.of k))`,
  with independent object and morphism universes; `hX₁`, `hX₂` assert exactly
  `IsDeligneMumfordModuliStack`. No finite-type or quasi-compactness assumption is added.
- Inertia: the existing `moduliInertiaProjection` forgets a vertical automorphism;
  `ModuliInertiaObject` and its category have exactly the objects and commuting
  arrows described in the statement. `hfinite₁`, `hfinite₂` use
  `IsRepresentableFiniteModuliMap` on the two inertia projections. This requires
  a scheme representing every scheme base change, finite over the test scheme,
  with its actual first projection identified by a vertical natural isomorphism.
- The map h: `h : BasedFunctor X₁ X₂`, and `hrep` is
  `IsRepresentableByAlgebraicSpaces h`.
- Etaleness of h: `het` quantifies over every scheme base change presented by
  `HasSpaceBaseChange`; `SpaceMapIsEtale` tests every etale scheme chart using
  Mathlib `Etale`.
- Separatedness of h: `hsep` asks that the relative diagonal of every such space
  base change is `AlgebraicSpace.IsRepresentableWith` scheme property `IsProper`.
  For a representable map, this is precisely properness of the relative diagonal;
  no properness assumption on h itself is made.
- Stabilizer preservation: `hstab` is `Functor.IsEquivalence` of
  `moduliInertiaComparison h`, the existing canonical functor
  `I_X₁ → X₁ ×[X₂] I_X₂`. Isomorphism of stacks is equivalence over the base,
  not equality of chosen total-category representatives.
- Categorical spaces: `M₁ M₂ : AlgebraicSpace (Spec (.of k))`, with the given
  maps `p₁`, `p₂` into their discrete moduli categories. `hp₁`, `hp₂` quantify
  over every algebraic space Z over k and assert bijectivity of composition
  with the given map. There is no geometric-points or base-change compatibility
  assumption on these categorical maps.
- The induced map: `∃ hbar : M₁.obj.obj ⟶ M₂.obj.obj` is an actual map of the
  algebraic-space presheaves over k. The first conjunct states exactly
  `p₁.comp (discreteModuliMap hbar) = h.comp p₂`; the second gives uniqueness
  among every map b satisfying this same equation. A natural transformation
  of the underlying space presheaves is precisely a map of the full subcategory
  of algebraic spaces; it does not require an additional sheaf condition.
- Etaleness of the induced map: `AlgebraicSpace.IsEtale hbar`, the recorded
  scheme-base-change definition.
- Separatedness of the induced map: its actual presheaf diagonal is
  `AlgebraicSpace.IsRepresentableWith (fun _ _ f ↦ IsClosedImmersion f.left)`.
  Mathlib closed immersion uses the usual local surjection on affine rings.
- Cartesian comparison: the final `e` is an equivalence into
  `moduliTwoFiberProduct (discreteModuliMap hbar) p₂`, with first projection
  exactly p₁ and second projection exactly h. This is the factor-swapped
  presentation of `X₂ ×[M₂] M₁`. These projection requirements specify the
  natural comparison: in the discrete target there is at most one vertical
  comparison isomorphism, so the existential e is not an unrelated equivalence.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (the field dependency's mathlib_match).
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.BasedFunctor` framework; `IsDeligneMumfordModuliStack`,
  `IsRepresentableByAlgebraicSpaces`, `HasSpaceBaseChange`, `SpaceMapIsEtale`,
  `discreteModuli`, `discreteModuliMap`, `moduliTwoFiberProduct`, `moduliTwoFiberFst`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsEtale`, `AlgebraicSpace.IsRepresentableWith`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`,
  through the representable-finite predicate.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Sheaf.AlgebraicGeometry.ModuliInertia`: `CategoryTheory.moduliInertiaProjection`.
- `Sheaf.AlgebraicGeometry.FiniteStackSchemeTests`:
  `CategoryTheory.IsRepresentableFiniteModuliMap`.
- `Sheaf.AlgebraicGeometry.DmStabilizerIsomorphismOpenLocus`:
  `CategoryTheory.moduliInertiaMap` and `CategoryTheory.moduliInertiaComparison`,
  now recorded by the repair definition node `def-sfb-moduli-inertia-comparison`.
  The canonical constructions, not the open-locus theorem, are used. The theorem
  node is no longer cited as a statement dependency. No dependency record is repaired.

Every recorded proof-dependency module is imported privately, except those already
public for the statement. The source module records all ten DAG proof steps.
Unstated proof dependencies have no import to add yet:
`lem-sfb-dm-etale-atlas-calculus`, `lem-sfb-etale-local-moduli-gluing`,
`lem-sfb-etale-space-single-cover-effective-descent`,
`lem-sfb-etale-stabilizer-preserving-affine-moduli`,
`lem-sfb-finite-inertia-etale-affine-charts`,
`lem-sfb-space-separated-diagonal-closed`. The size dependency is a metatheoretic
convention. The scheme-coproduct dependency currently has no Lean record.

Edge cases checked before writing: empty X₂ forces empty X₁ and yields the empty
cartesian square; the identity h gives identity map and comparison. For a map
between schemes the inertias are identities and the conclusion is the usual
cartesian square for the spaces themselves. A nontrivial finite etale group G
makes `Spec k → BG` a representable etale map, but the canonical inertia
comparison fails to be an equivalence; this necessary exclusion is retained.
The inertia hypothesis tests all scheme bases, including nonreduced tests;
it is not replaced by a condition on finite geometric automorphism groups. Non-quasi-compact DM stacks, arbitrary characteristic,
empty atlases, and independent stack universes remain allowed.

Searches for an existing statement:

- `msearch.py ... leanfinder`: "Stabilizer preserving separated etale maps of
  Deligne Mumford stacks induce cartesian squares of categorical moduli spaces".
  Eight hits, all generic scheme etale/separated calculus; no stack comparison.
- `msearch.py ... loogle`: "IsDeligneMumfordModuliStack,
  IsRepresentableByAlgebraicSpaces". Zero hits; the project identifier is not
  indexed by the external Loogle service.
- `msearch.py ... grep`: "inertia|stabilizer" in Mathlib/AlgebraicGeometry.
  Zero hits.
- `msearch.py ... leansearch`: "Categorical moduli spaces of Deligne Mumford
  stacks stabilizer preserving etale map cartesian square". Eight hits: general
  bicartesian squares, cartesian functor calculus and scheme etale objects;
  no matching moduli theorem.
- `rg` in `lean/WeilConjectures` for the item id: no match. Key-name searches for
  Keel--Mori and stabilizer-etale comparisons found no matching theorem upstream.
- `rg` in `lean/Sheaf/AlgebraicGeometry` located the inertia module, the canonical
  inertia comparison in DmStabilizerIsomorphismOpenLocus, and the affine-stack
  comparison theorem. The latter assumes an affine target with a finite flat
  affine cover and a uniform categorical map; it is only a proof input and does
  not state the present theorem for arbitrary categorical algebraic spaces.

No statement dispute or source correction is needed.

## Second reading by NX

This is a separate rereading by the same dispatcher-started worker; the brief
forbids starting other agents, and the maintainer supplies the independent review.
I compared the final signature against every sentence of the node. Both finite
inertia assumptions are present; etaleness and proper relative diagonal of h
are independent assumptions; stabilizer preservation uses the actual canonical
comparison. Both categorical properties quantify over all spaces over k, with
no flat-base-change property added. The induced-map uniqueness only assumes the
commuting-square equation. The two conclusions use the distinct proper-diagonal
and closed-immersion-diagonal conventions required by the node. Finally, both
projections of the equivalence are retained, ruling out an arbitrary equivalence
with the fibre product. I checked that swapping its factors gives precisely the
fibre product displayed in the node. No mismatch or statement change was found.
The repair also confirms that the item cites the definition node owning the
canonical inertia map and comparison, rather than citing the downstream theorem
that happens to be in the same source module.

Validation: `scompile.py NX lem-sfb-keel-mori-stabilizer-preserving-etale`
compiled the delivered statement against the current server sources with no
errors or unexpected warnings (58.9 seconds, two threads, 60-second limit).
The wrapper first reported a timeout in its published-build attempt and
confirmed the clean result against current sources.

## New nodes

`def-sfb-moduli-inertia-comparison` is an existing:true definition node. It records
the already-landed declarations `CategoryTheory.moduliInertiaMap` and
`CategoryTheory.moduliInertiaComparison` in
`Sheaf.AlgebraicGeometry.DmStabilizerIsomorphismOpenLocus`. The declarations are
plain canonical constructions: the first maps an inertia object and commuting
arrow through a based functor, and the second maps it to the actual two-fibre
product with identity comparison. The node cites the scheme, size convention,
fibred-groupoid, and absolute-inertia definitions used by their signatures.
Searches used LeanSearch, LeanFinder, grep of Mathlib and WeilConjectures, and
grep of the DAG; no Mathlib/source duplicate and no prior DAG node exists. The
item's `stmt_deps` now cites this definition node in place of
`lem-sfb-dm-stabilizer-isomorphism-open-locus`.
