## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceProperNoetherianApproximation`
states `AlgebraicGeometry.AlgebraicSpace.exists_proper_noetherian_approximation`.
Its only theorem has proof `sorry`. The helper `baseSchemeProjection` constructs the
canonical structure map to the base scheme using `Over.mkIdTerminal`, preservation
of terminal objects by Yoneda, and the actual full-subcategory morphism. It contains
no postponed proof and chooses no arbitrary map or geometric object.

The source was read in `literature/stacks-project/spaces-limits.tex`,
lemma-proper-limit-of-proper-finite-presentation-noetherian, lines 2967 onward;
`literature/stacks-project/tags/tags` identifies it with Tag 0A0X. This is the
source's result specialized to a scheme target, with its stated qcqs consequences.
No statement correction is needed.

Hypothesis and clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| T is a scheme | `(T : Scheme.{u})` |
| T is quasi-compact | `[CompactSpace T]` |
| T is quasi-separated | `[QuasiSeparatedSpace T]` |
| X is an algebraic space over Spec Z | `X : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))` |
| Given map f to the scheme T over Z | `f : X ⟶ schemeSpace (Over.mk (specULiftZIsTerminal.from T))` |
| f proper | `hf : MapIsProper f` |
| Separated means closed-immersion diagonal | `MapIsProper` includes `MapIsSeparated`, whose definition is `IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)` on `pullback.diagonal` |
| Finite type means qc and chartwise lft | `MapIsProper` includes `MapIsFiniteType`, defined as `MapIsQuasiCompact` and `MapIsLocally (@LocallyOfFiniteType)` |
| Universally closed after every base change | `MapIsProper` includes `MapIsUniversallyClosed`, with every space base change and the closedness of its point projection |
| Small nonempty directed set | `∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))` |
| Inverse system of arrows f_i : X_i to T_i | `Xs Ts : Iᵒᵖ ⥤ AlgebraicSpace ...`, `fs : Xs ⟶ Ts`; naturality of fs is the compatibility of the arrows |
| Both transition morphisms affine | `∀ (i j : Iᵒᵖ) (a : i ⟶ j), MapIsAffine (Xs.map a) ∧ MapIsAffine (Ts.map a)` |
| Affine means representable with affine source on affine tests | Existing `MapIsAffine` supplies an actual affine scheme and representing pullback square for every affine scheme test; affineness is local on the test so this is the representable affine condition |
| Each f_i proper | `∀ i, MapIsProper (fs.app i)` |
| Each f_i finitely presented | `MapIsLocallyOfFinitePresentation (fs.app i)`, `MapIsQuasiCompact (fs.app i).hom.hom`, and `MapIsQuasiCompact (pullback.diagonal (fs.app i).hom.hom)` |
| Each T_i finitely presented over Spec Z | The same three predicates on `baseSchemeProjection (Ts.obj i)` |
| fp uses finitely presented chart ring maps | `MapIsLocallyOfFinitePresentation` is `MapIsLocally (@LocallyOfFinitePresentation)`, so all compatible etale scheme charts use Mathlib's actual scheme finite-presentation predicate |
| Limit source is X | `Nonempty (IsLimit (Cone.mk X πX))` |
| Limit target is the given scheme T | `Nonempty (IsLimit (Cone.mk (schemeSpace (Over.mk (specULiftZIsTerminal.from T))) πT))` |
| Limit arrow is f | `∀ i, πX.app i ≫ fs.app i = f ≫ πT.app i`; together with the two limit universal properties this is exactly the limit in the arrow category |
| Stage sources quasi-compact, by atlas definition | For every i, an explicit `U : Over (Spec ...)`, `a : yoneda.obj U ⟶ (Xs.obj i).obj.obj`, and `CompactSpace U.left ∧ IsEtale a ∧ IsSurjective a` |
| Stage targets quasi-compact, by atlas definition | The corresponding explicit V,b atlas of `Ts.obj i` |
| Both stages quasi-separated | `IsAbsolutelyQuasiSeparated (Xs.obj i)` and `IsAbsolutelyQuasiSeparated (Ts.obj i)`, the existing absolute affine-test diagonal criterion of Stacks 0AHR |
| Quasi-compact maps tested on affine schemes | Existing `MapIsQuasiCompact` tests actual pullbacks to all affine schemes with the existing algebraic-space point topology; compactness of the point space is equivalent to the qc etale atlas definition |

Dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`, full signatures
  and docstrings read in Mathlib's `Scheme.lean`.
- `def-trf-algebraic-space`: `Sheaf.AlgebraicGeometry.AlgebraicSpace`, declarations
  `AlgebraicGeometry.AlgebraicSpace`, `IsRepresentableWith`, `IsEtale`,
  `IsSurjective` and `IsAlgebraicSpace`; uses the actual fppf sheaf category and
  representable etale scheme charts.
- Added landed dependency `def-trf-scheme-algebraic-space`:
  `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`,
  `AlgebraicGeometry.AlgebraicSpace.schemeSpace` and its named property theorem;
  its data are the actual Yoneda sheaf. This is needed for the given scheme base.
- Added landed dependency `def-sfb-space-morphism-properties`:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`,
  `MapIsProper`, `MapIsLocallyOfFinitePresentation`, `MapIsLocally` and their
  components. Its public dependency `Sheaf.AlgebraicGeometry.ProperCurveModuli`
  supplies the shared `MapIsQuasiCompact` and `mapPoint`.
- Added landed dependency `def-sfb-space-affine-quasifinite-properties`:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite`, `MapIsAffine`.
- Added landed dependency `def-sfb-space-absolute-quasi-separated`:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`,
  `IsAbsolutelyQuasiSeparated`.
- Mathlib `AlgebraicGeometry.specULiftZIsTerminal` in
  `Mathlib.AlgebraicGeometry.Limits` supplies the actual Z-structure on T;
  `Over.mkIdTerminal` and `Limits.IsTerminal.isTerminalObj` construct the canonical
  structure map of every stage. `Mathlib.CategoryTheory.Limits.Yoneda` supplies
  Yoneda's limit-preservation instance.

Only the item's `lean` and `stmt_deps` change. The four extra statement dependencies
are already landed definition nodes and prevent private copies of their notions.
No new nodes or dependency repairs are required. Every currently recorded proof
module is imported privately: scheme Noetherian approximation, directed reindexing
(including its other recorded Mathlib files), Noetherian finite-presentation and
quasi-separatedness facts, space flat/proper/fp locality, closed immersions and
space fibre products. Proof dependencies with no declaration/module yet are not
invented or imported. All seven steps of the DAG proof are preserved in the theorem
docstring, including the cofiltered category of models and its universal property.

Edge cases checked before writing: empty T and empty X remain allowed; the stage
atlas scheme may be empty, with no `Nonempty` restriction. The index is nonempty,
but its stages need not have points. A singleton diagram is allowed when f is
already finitely presented over a finitely presented integer base. There is no
separatedness hypothesis on T beyond quasi-separatedness, and no finite-presentation,
flatness, schematicity, projectivity, surjectivity or nonemptiness hypothesis on X
or f. No countability or finiteness restriction is imposed on I. Its universe is
`Type u`, matching the scheme/ring size, and every universe and variable is explicit;
`set_option autoImplicit false` is enabled. `ULift.{u} ℤ` represents the same integer
base in this universe, with its terminal-object structure, and does not fix a
characteristic. The X_i and T_i remain algebraic spaces; T_i are not required to be
schemes. Absolute quasi-separatedness uses the existing 0AHR criterion rather than
confusing a relative diagonal over an arbitrary non-separated base with the absolute one.

Searches (2026-10-24):

- `msearch.py ... leanfinder "A proper algebraic space over a qcqs scheme is an inverse limit of proper finitely presented algebraic spaces over finitely presented integer bases with affine transitions"`:
  8 scheme-only hits, including `isProper_eq`, `Scheme.compactSpace_of_isLimit`,
  scheme Hom limit lemmas and `Scheme.nonempty_of_isLimit`; no algebraic-space match.
- `msearch.py ... loogle "AlgebraicGeometry.AlgebraicSpace, IsProper"`:
  0 hits; Loogle reports unknown identifier `AlgebraicGeometry.AlgebraicSpace`.
- `msearch.py ... leansearch "algebraic space proper morphism inverse limit noetherian finite presentation"`:
  8 proper-scheme hits (`IsProper`, `IsProper.mk`, `isProper_eq`, `isProper_iff`,
  proper finite morphisms and properness of a factor); none states the item.
- `msearch.py ... grep "NoetherianApproximation|proper.*approximation|approximation.*proper" AlgebraicGeometry`:
  0 Mathlib hits.
- Local `rg` over `lean/WeilConjectures` for Noetherian approximation / proper
  Noetherian limits found `AlgebraicGeometry.exists_proper_limit_noetherian` in
  `WeilConjectures.AlgebraicGeometry.ProperLimitNoetherian`. Its full theorem was
  read: it concerns schemes, so is not the space theorem. Its affine refinement is
  also extra data not requested here. `grep -rn` for the item id returned no hits.
- Local `rg` over `lean/Sheaf` for the same concepts found no statement of the item;
  searches for morphism properties found the existing modules reused above.
  Searches for `baseSchemeProjection` in Mathlib, WeilConjectures and Sheaf found
  no existing declaration. No notion was independently redefined.

Validation: the required `scompile.py Q24 lem-sfb-space-proper-noetherian-approximation`
compiled both its sandbox and actual library-module forms cleanly on the server,
1.9 seconds each, with no errors or warnings. Dry-run and final delivery results
are recorded below after execution.

## Second reading by Q24

A separate second pass reread the item and the complete module, following the
clause table above. This is the worker's own second pass; the dispatcher prohibits
starting another agent, and the maintainer supplies the independent review.
The two explicit cones have exactly X and the Yoneda space of T as vertices,
and their component square uses the given f. Natural transformations supply
compatibility of each projection family and of the maps f_i. Both transition
families are affine, all required finite-presentation clauses occur for f_i and
for the canonical integer structure map of T_i, and both stages have the stated
qc atlases and absolute quasi-separatedness. Empty atlases and arbitrary directed
sets are retained. The helper uses terminality to define the unique base projection,
with real data and no existence choice. No mathematical mismatch, hidden extra
assumption or statement correction was found. No changes were needed in this pass.

Delivery validation: `deliver2.py Q24 lem-sfb-space-proper-noetherian-approximation
--no-push` printed `OK (dry run): commit c63e0de0a33 passes the preflight and
compiles; nothing pushed`. It staged exactly this report, the item's node copy,
and the one statement module. A local text check also confirmed that all Lean
lines are at most 100 characters, the signature record is extracted verbatim,
and the sole postponed proof is the named item theorem.
