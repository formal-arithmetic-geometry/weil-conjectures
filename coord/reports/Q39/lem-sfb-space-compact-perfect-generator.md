## Worker report

Stage 2, Q39, lem-sfb-space-compact-perfect-generator. The previous BLOCKED ending
mistook a passing stage-1 split for completion of stage 2. The live node has no
Lean attachment, is queued at stage 2, and has no released repair note. The Q67
stage-1 proof and its independent review are preserved unchanged.

The new module `Sheaf.AlgebraicGeometry.AlgebraicSpaceCompactPerfectGenerator`
states `AlgebraicGeometry.AlgebraicSpace.exists_compact_perfect_generator`.
Its sole theorem proof is `sorry`. No definitions, auxiliary theorems, new nodes,
or dependency repairs are needed. Every object and predicate is already defined.

Sources read: Stacks `spaces-perfect.tex`, theorem-bondal-van-den-Bergh (09IY),
lines 3674 onwards, and proposition-compact-is-perfect (09M8), lines 3879 onwards.
The former gives one perfect generator and the zero-detection equivalence; the
latter gives compactness in D_QCoh. For the intrinsic quasi-separatedness hypothesis
I also read Properties of Spaces, lemma-characterize-quasi-separated (0AHR),
lines 133-165. This equates the absolute diagonal condition with quasi-compactness
of U x_X V for every pair of affine scheme maps. The theorem deliberately uses
this exact affine-pair criterion, as does the landed
`AlgebraicSpace.coherentSubobjects_filtered_colimit`; it does not replace the
absolute diagonal by the relative diagonal over a potentially non-qseparated S.

Hypothesis and clause correspondence:

- Fixed sizes: explicit `universe u w`; schemes, rings, module sections, the small
  affine site and small coproduct indices use u; the localization morphism universe
  w is independent. `[HasDerivedCategory.{w} X.SmallModules]` is the recorded
  localization interface, not a geometric restriction on X.
- A scheme S: `{S : Scheme.{u}}` uses the recorded Mathlib scheme type.
- An algebraic space over S: `(X : AlgebraicSpace S)` uses the recorded fppf-sheaf
  full subcategory, including its representable diagonal and etale atlas.
- Small etale structure sheaf and module category: `X.SmallModules` is the recorded
  module category on the small affine ringed model. Its regular-functions rings
  and `X.smallModuleEquivalence : X.Modules ≌ X.SmallModules` identify it with the
  original small etale ringed topos, in the same section universe. The derived
  category is the localization of this abelian module category, not D(QCoh(X)).
- D_QCoh: `X.DerivedQCoh` is the already recorded full subcategory of
  `X.DerivedModules` with quasi-coherent cohomology; `derivedQCohProperty` transports
  cohomology back along the inverse of the same module equivalence before testing
  Mathlib's `SheafOfModules.IsQuasicoherent`.
- Quasi-compactness: `hqc : CompactSpace (Point X.obj.obj)` says exactly that every
  open cover of the recorded point space has a finite subcover.
- Absolute quasi-separatedness: `hqs` quantifies over all `U V : Over S`, all maps
  `a : yoneda.obj U ⟶ X.obj.obj` and `b : yoneda.obj V ⟶ X.obj.obj`, and assumes
  `IsAffine U.left` and `IsAffine V.left`. It concludes
  `CompactSpace (Point (Limits.pullback a b))`. These are all affine scheme maps,
  not only etale maps. This is exactly criterion (3) of 0AHR, equivalent to the
  absolute diagonal being quasi-compact. The pullback is the actual sheaf fibre
  product; the existing point topology is the atlas topology of this algebraic
  space. No separatedness or quasi-separatedness of S is assumed.
- Existence of P in D_QCoh: the existential `(P : X.DerivedQCoh)` includes its
  quasi-coherent cohomology witness.
- Perfectness: `SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u,u,u,w}
  X.smallStructureSheaf P.obj` is the existing general-site predicate, not a new
  algebraic-space predicate. Expanding it gives a cochain representative and,
  on covering sieves, bounded complexes mapping quasi-isomorphically to its
  restrictions. `StrictPerfectCoefficientPackageOnSite` gives degreewise
  retractions from finite sums of the structure module. Bounds and ranks may
  vary with the covering member. A finite product of the unit in this abelian
  category is also its finite direct sum. Restriction to the small affine basis
  preserves these local presentations and finite free splittings.
- Compactness: `@IsCompactObject.{u} X.DerivedQCoh _ _ hcoprod P` uses the
  recorded definition verbatim. It is bijectivity of `DirectSum.toAddMonoid`
  formed from composition with the coprojections, for every `I : Type u` and
  `E : I → X.DerivedQCoh`. Thus the map is the canonical map in the node.
  `hcoprod : HasCoproducts.{u} X.DerivedQCoh` is existentially concluded rather
  than assumed; this supplies the categorical structure presupposed by the node
  and avoids an additional hypothesis. Both the coproduct and compactness are
  in D_QCoh, not the whole ambient derived category.
- Zero detection for every E: `∀ E : X.DerivedQCoh, IsZero E.obj ↔ ...` is the
  zero-object condition in D(O_X), equivalently in its full subcategory. It has
  both directions and quantifies over every object with quasi-coherent cohomology.
- Every integer shift and vanishing Hom group:
  `∀ n : ℤ, Subsingleton (P.obj⟦n⟧ ⟶ E.obj)` uses the ambient derived shift and
  Hom. In a preadditive category, a subsingleton Hom group is exactly the zero
  group. Fullness identifies this with the required Hom groups. The same P
  occurs in the perfectness, compactness and generator clauses.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `etaleTopology`, `structurePresheaf`, `structureSheaf`, `Modules`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the transparent abbreviation for Mathlib `SheafOfModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and
  Mathlib `SheafOfModules.IsQuasicoherent`, used by the existing derived predicate.
- `WeilConjectures.CategoryTheory.CompactObject`: `CategoryTheory.IsCompactObject`.
  The old example file `Sheaf/CategoryTheory/CompactObject.lean` is now withdrawn;
  its node points to this upstream definition, which is the import used here.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`;
  `Point` is the field-valued point quotient from its recorded dependency.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`: `DerivedModules`,
  `derivedQCohProperty`, `DerivedQCoh`. Its small-model declarations are those of
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel`:
  `SmallModules`, `smallStructureSheaf`, `smallModuleEquivalence`.
- `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`:
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses`, with its recorded local model
  and finite-free splitting package, read together with StrictPerfectPackageOnSite.

The node gains only `lean` and the already-landed statement dependencies
`def-sfb-space-derived-module-calculus`, `def-a1-space-point-topology`, and
`def-weil-pbc-strict-perfect-coefficient-package`. All original dependency ids stay.
Both proof dependencies currently have no Lean record, so their imports cannot
be added yet. Their names and the complete three-step argument are in the theorem
docstring; the maintainer can add their imports when those declarations land.

Edge cases checked before stating: X empty allows P = 0 and the zero derived
category; X = Spec A allows P = O_X, including A = 0; an empty coproduct family
has the map from zero to zero; zero targets satisfy both sides; n = 0, positive
and negative shifts are all included; no Noetherian, characteristic, base
quasi-separatedness, or separatedness assumption has been introduced. Perfectness
has local bounds and no uniform global bound. Infinite families are included.

Searches made with the prescribed wrapper (outputs retained in searches.jsonl):

- LeanFinder, 'A quasi compact quasi separated algebraic space has a compact
  perfect generator of its derived category of quasi coherent modules': eight
  hits, all scheme topological compactness/quasi-separatedness, no target match.
- Loogle, `"IsCompactObject", "DerivedCategory"`: zero hits.
- Mathlib grep, `compact.*perfect|perfect.*generator|bondal|van.den.bergh`:
  two bibliography hits in Triangulated/Generators.lean, no space theorem.
- LeanSearch, 'A quasi compact quasi separated algebraic space has a compact
  perfect generator of the derived category of quasi coherent modules': eight
  hits about scheme quasi-separatedness and compactness, no target match.
- Project ripgrep over WeilConjectures and Sheaf for compact/perfect/generator,
  and the exact item id: no declaration of this node. The nearby
  `WeilConjectures/AlgebraicGeometry/SupportedPerfectGenerator.lean` is a scheme
  theorem with support, and `PerfectObjectCompact.lean` is compactness on schemes;
  neither states the algebraic-space theorem. Read the exact general-site
  perfectness and compact-object definitions instead of duplicating them.

Validation: prescribed scompile.py server check completed cleanly for the sole
module, with no compiler errors or warnings. No statement fault or disputed claim
was found. No source or library file was edited; all writes are in the sandbox.

## Second reading by Q39

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
