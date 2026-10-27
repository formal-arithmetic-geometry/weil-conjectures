## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpacePerfectWeakGenerator` states
`AlgebraicGeometry.AlgebraicSpace.exists_perfect_weak_generator`, with its entire
proof postponed by `sorry`. No definition or other theorem is introduced. The
source is Stacks Project, Derived Categories of Spaces, Tag 09IY,
`theorem-bondal-van-den-Bergh`, read in `literature/stacks-project/spaces-perfect.tex`
from the theorem through the end of its proof. The docstring carries all seven
steps of the accepted DAG proof, including the canonical-unit descent argument
omitted in the source.

The inherited BLOCKED ending concerned the already accepted stage-1 split. I read
the current node, its seven statement dependencies and all proof steps. The node
has no Lean record, occurs as a stage-2 `state` item in `coord/queue.tsv`, and has no
repair note. The stage-handoff paragraph of `coord/brief-stage2.md` explicitly
permits formalizing this accepted split. Its statement, proof, proof dependencies
and reviewed split are unchanged.

Hypotheses and clauses, matched against the node:

- The size convention is rendered by explicit `universe u w`. Scheme, ring
  sections, and modules use the existing universe `u`; localization morphisms
  have the independent universe `w`. There are no auto-bound variables.
- A scheme S and algebraic space X over it are `{S : Scheme.{u}}` and
  `(X : AlgebraicSpace S)`. This is the recorded fppf-sheaf definition with a
  representable diagonal and a surjective etale scheme atlas. S has no finiteness
  or separation hypothesis.
- The small etale site and its regular-functions structure sheaf are represented
  by the already recorded small affine model, `X.smallStructureSheaf`. Its
  `SmallModules` category is the existing `ringedSiteModules` specialization.
  The explicit equivalence `X.smallModuleEquivalence : X.Modules ≌ X.SmallModules`
  is restriction to the affine basis, with no coefficient lift or altered ring.
- `D(O_X)` is `X.DerivedModules`, definitionally `DerivedCategory X.SmallModules`,
  under `[HasDerivedCategory.{w} X.SmallModules]`. This is the chosen localization
  interface of the node's size convention, not a geometric assumption. It does
  not impose boundedness or require a chosen resolution of E.
- `C_X` is the existing `X.DerivedQCoh`, the full subcategory for
  `X.derivedQCohProperty`. For every integer its homology sheaf, transported back
  by `X.smallModuleEquivalence.inverse`, satisfies Mathlib's
  `SheafOfModules.IsQuasicoherent`. Thus this is the full subcategory of the
  ambient derived category with quasi-coherent cohomology, as required.
- Quasi-compactness (every open cover has a finite subcover) is precisely
  `(hqc : CompactSpace (Point X.obj.obj))`, with the existing atlas topology.
- Quasi-separatedness is `(hqs : IsAbsolutelyQuasiSeparated X)`, the recorded
  affine-test criterion equivalent to quasi-compactness of the absolute diagonal
  (Stacks 0AHR). This is absolute quasi-separatedness of X, even if S itself is
  not quasi-separated.
- There exists one P belonging to C_X: `∃ P : X.DerivedQCoh`. Its perfectness is
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
    X.smallStructureSheaf P.obj`. The recorded predicate means a derived object
  represented by a complex locally admitting bounded quasi-isomorphic models
  whose terms split off finite free sheaves. Bounds and ranks can vary with
  each member of the cover. The affine-basis equivalence preserves this local
  condition, so this is the original etale perfectness of the node.
- For every E in C_X is `∀ E : X.DerivedQCoh`; there is no extra constraint on E.
- E is isomorphic to zero is `IsZero E.obj`. The ambient derived category has a
  zero object, so these formulations agree.
- The equivalence, in both directions, is the displayed `↔`.
- All integer shifts are `∀ n : ℤ`, including zero and negative shifts. The
  shifted object is the source `P.obj⟦n⟧`, exactly as in the node.
- Vanishing of the ambient Hom group is `Subsingleton (P.obj⟦n⟧ ⟶ E.obj)`.
  In this additive category it says every morphism equals the zero morphism;
  the Hom types belong to the ambient derived category, not to a different
  derived category of QCoh modules.

Recorded dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `EtaleSite`, `etaleTopology`, `structureSheaf`, `Modules`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  the underlying Mathlib `SheafOfModules` is used through the existing category.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh`, with the
  unchanged Mathlib predicate `SheafOfModules.IsQuasicoherent`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory` and the localization functor `DerivedCategory.Q`.
- `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`:
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses`; its definition was read
  together with `IsLocallyStrictPerfectComplexOfUniverses` and its package.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`: `DerivedModules`,
  `derivedQCohProperty`, `DerivedQCoh`; these use the existing `SmallModules`,
  `smallStructureSheaf` and `smallModuleEquivalence` of
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `IsAbsolutelyQuasiSeparated`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `pointTopologicalSpace` on the existing `Point` classes.

The item's `stmt_deps` gains the three already landed nodes
`def-sfb-space-derived-module-calculus`, `def-sfb-space-absolute-quasi-separated`,
and `def-a1-space-point-topology`. Section 5's STMT_DEPS MAY GAIN LANDED NODES rule
permits naming these exact shared interfaces. None is newly defined or repaired
in this delivery; the same mathematical objects were already specified in the
item. The original seven dependency ids are retained.

Proof-only imports are the recorded modules
`WeilConjectures.AlgebraicGeometry.PerfectGeneratorExists`,
`WeilConjectures.CategoryTheory.WeakTriangulatedGenerator`,
`WeilConjectures.AlgebraicGeometry.KoszulRestrictionZero`, and
`WeilConjectures.AlgebraicGeometry.KoszulOpenOrthogonality`. Their declarations
`exists_perfect_generator`, `IsWeakTriangulatedGenerator`,
`isZero_restrict_shift_koszul`, and `koszul_open_orthogonality` were read. The
remaining proof-only space nodes currently have no Lean record or published
declaration recorded on their nodes, so there is no corresponding import to add.
The strict-perfect package is already a public statement import.

Edge cases checked before writing: X can be empty (the zero object is a perfect
weak generator there); E can be zero (all its incoming Hom groups are zero);
P can be zero only when all quasi-coherent objects are zero; all integers,
including negative and zero shifts, are tested. No connectedness, nonemptiness,
nonzero-ring, finite-dimensionality, Noetherianity or separated-base requirement
is inserted. In the proof plan W can be empty (the empty Koszul list) or equal to
V (the Koszul object is acyclic); neither is excluded by this statement. The
small-model and derived localization universes are kept explicit and independent.

Searches for an exact pre-existing statement:

- `msearch.py leanfinder`: “A quasi compact quasi separated algebraic space has a
  perfect weak generator detecting zero by all shifted Hom groups”. Eight hits:
  `CategoryTheory.hasExt_iff`, small-localized-shifted-Hom and derived t-structure
  results; none states perfect generation of algebraic spaces.
- `msearch.py loogle`: `AlgebraicSpace, IsPerfectOnRingedSiteOfUniverses,
  IsCompactGenerator`. Zero hits, unknown identifier `AlgebraicSpace` in its
  Mathlib index.
- `msearch.py leansearch`: “A quasi compact quasi separated algebraic space
  admits a perfect weak generator”. Eight hits, all on scheme quasi-separatedness
  or quasi-compactness; no exact theorem.
- `msearch.py grep`: `weak[Gg]enerator|weak_generator|perfect.*generator`,
  Mathlib subdirectory `CategoryTheory`: zero hits.
- Direct `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `weakGenerator|weak_generator|WeakGenerator`, `exists_perfect_weak_generator`,
  and `perfect.*generator|generator.*perfect`; direct `grep -rn` for this node id
  in `lean/WeilConjectures`. The exact new name and blueprint-tagged theorem do
  not exist. The scheme generator theorem is the recorded proof input.
  `AlgebraicSpaceCompactPerfectGenerator.exists_compact_perfect_generator`
  is the separate, stronger node with compactness and coproduct existence in its
  conclusion; its proof explicitly invokes this weak-generator node. It is not
  an exact existing match and is not imported to avoid reversing the DAG route.
  Existing derived-module, point-topology and absolute quasi-separatedness
  definitions were located and reused instead of copied.

No statement dispute, correction, new node, dependency repair, or hollow
construction is needed. The file has no line over 100 characters and explicitly
sets `autoImplicit false`. Its recorded signature is extracted verbatim from the
file, from `theorem` to immediately before `:=`.

Validation: prescribed `scompile.py` compiled the file both as its sandbox module
and at its library module path, cleanly (1.9 s and 2.0 s respectively); only the
postponed theorem proof is present. Delivery dry-run and push results follow.

Delivery dry-run: `deliver2.py Q20 lem-sfb-space-perfect-weak-generator --no-push`
printed `OK (dry run): commit 24bf012b763 passes the preflight and compiles;
nothing pushed`. No preflight repairs were required.

## Second reading by Q20

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
