## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceHilbertRepresentability` states
`AlgebraicGeometry.AlgebraicSpace.hilbert_representability`, with its proof `sorry`.
It also constructs the ambient projection, family set and ambient base-change map
needed to spell out the node's own Hilbert functor. These are helpers of this
node, listed in `lean.declarations`; their data are actual constructions, not
choices of unspecified objects. No new definition node or dependency repair is
needed. The node's natural-language statement, source and accepted proof remain
unchanged. Four already-landed definition nodes were added to `stmt_deps` to
record ownership of the notions used.

Source read: `literature/stacks-project/quot.tex`, Situation 0CZY
(`situation-hilb`, lines 2436ff.) and Proposition 0D01 (`proposition-hilb`,
lines 2573ff.). These impose finite presentation and separatedness on a, and
properness, flatness and finite presentation on the closed families. They impose
neither properness nor flatness on a. Proposition 0D01 proves algebraicity and
local finite presentation via Hilbert--Quot and Quot representability.

Clause-by-clause correspondence:

- Base scheme, size convention and algebraic spaces over it: explicit
  `universe u`, `{S : Scheme.{u}}`, `{A B : AlgebraicSpace S}` and `(a : A ⟶ B)`.
  Scheme test objects are `T : Over S` equipped with `t : schemeSpace T ⟶ B`.
  Thus a scheme over the space B is not incorrectly replaced by a scheme over
  a scheme base. All tests lie in the same scheme universe as S and its atlases.
- Separatedness of a: `hsep : MapIsSeparated a`, the existing predicate saying
  its relative diagonal is representable by scheme closed immersions.
- Finite presentation of a: `hlfp : MapIsLocallyOfFinitePresentation a`,
  `hqc : MapIsQuasiCompact a.hom.hom`, and
  `hqs : MapIsQuasiCompact (pullback.diagonal a.hom.hom)`. This spells out
  local finite presentation, quasi-compactness and quasi-separatedness exactly
  as the node. The latter follows from separatedness but is retained as the
  explicitly specified constituent, not an extra condition beyond the node.
- Fibre products: `enlargedFibreProduct a t`, whose underlying object is
  `Limits.pullback a.hom t.hom`, the actual fppf sheaf fibre product. Its second
  projection `hilbertAmbientProjection a t` is `pullback.snd` bundled into the
  full subcategory. Only the algebraic-space Prop is supplied by the existing
  fibre-product theorem; the fibre-product data are real.
- Closed subspaces up to isomorphism over the ambient space:
  `C : ClosedSubspace (enlargedFibreProduct a t)`. This is the project's
  subtype of `Subobject` with representability by closed immersions, so it
  retains full scheme structure and identifies exactly the presentations in
  the node. It is not the set of closed subsets of the underlying space.
- The family structure map is `C.val.arrow ≫ hilbertAmbientProjection a t`.
  `hilbertFamilies a t` requires `MapIsProper`, `MapIsFlat`,
  `MapIsLocallyOfFinitePresentation`, `MapIsQuasiCompact` and
  quasi-compactness of that map's diagonal. The last three are precisely finite
  presentation. `MapIsFlat` and `MapIsLocallyOfFinitePresentation` use compatible
  representable etale scheme charts and the recorded Mathlib scheme predicates.
  `MapIsProper` is separated, finite type and universally closed, with all
  algebraic-space base changes, exactly as defined in the node.
- Transition maps are inverse images: `hilbertAmbientBaseChange a t g` is
  the canonical sheaf pullback map, constructed with `pullback.lift` from the
  identity on A and `yoneda.map g` on the scheme factor. Its compatibility
  proof is just `pullback.condition` and associativity. No geometric theorem
  is proved in this definition. The final `IsPullback` condition says that
  the two closed inclusions are inverse images along this exact map.
- Representing object: `∃ (H : AlgebraicSpace S) (p : H ⟶ B),
  MapIsLocallyOfFinitePresentation p ∧ ...`.
- The required bijections: `e T t` is the equivalence from
  `{h : schemeSpace T ⟶ H // h ≫ p = t}` (precisely `Hom_B(T,H)`) to
  `hilbertFamilies a t`. The equivalence is not between arbitrary larger
  collections of presentations.
- Naturality: quantify over every `g : T' ⟶ T` and maps h and h' to H over the
  appropriate base maps. Whenever `h' = yoneda(g) ≫ h`, there is a morphism d
  between the chosen subobject domains whose square with their inclusions and
  `hilbertAmbientBaseChange a t g` is `IsPullback`. This says exactly that the
  family of the restricted map is the inverse-image family. Pullbacks of mono
  inclusions are unique up to the ambient isomorphism identified by Subobject;
  hence it is equivalent to equality with the canonical transition map.
  Conversely, the usual natural representing equivalences give that square.
  No arbitrary map or arbitrary base-change operation substitutes for the
  canonical map, and no flatness restriction on g is present.
- There are no properness, flatness, nonemptiness, noetherianity, projectivity
  or scheme-representability hypotheses on A or B.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its `Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsAlgebraicSpace`, `IsRepresentableWith` and `IsEtale`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace` (used through the existing bundled product).
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`;
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType` and `QuasiCompact`;
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`,
  `IsSeparated` and `UniversallyClosed`. Their full signatures/docstrings were
  checked. These scheme properties are used by the canonical space predicates,
  without trying to apply the scheme predicates directly to a space map.
- Added landed dependency `def-sfb-space-morphism-properties`:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`, `MapIsSeparated`,
  `MapIsFlat`, `MapIsLocallyOfFinitePresentation`, `MapIsProper`. The
  `MapIsQuasiCompact` used by them is the recorded construction from
  `Sheaf.AlgebraicGeometry.ProperCurveModuli` (quasi-compact scheme-test
  pullbacks in the point topology).
- Added `def-sfb-space-closed-subspace`:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedSubspace`, `ClosedSubspace`.
- Added `def-sfb-space-sheaf-fibre-product` and
  `def-trf-scheme-algebraic-space`:
  `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`, `enlargedFibreProduct` and
  `schemeSpace`. Both ownership nodes record existing canonical constructions.
- `def-weil-size-convention` is metatheoretic (no declaration/module); it is
  rendered by explicit universe binders and the existing space framework.
- The accepted proof dependencies `lem-sfb-space-hilbert-is-quot` and
  `lem-sfb-space-quot-representability` currently have no Lean record. There is
  consequently no recorded proof module to import. Their exact proof roles
  are preserved in the theorem docstring and the unchanged DAG proof. They are
  not needed to type this statement. No blanket dependency interface was added.

Edge checks before writing: empty S and empty A/B/T are permitted; no inhabitant
is demanded. Over an empty test scheme the unique empty closed family is
allowed. Arbitrary dimension, nonproper and nonflat a, nonnoetherian bases and
nonflat changes of test scheme are included. Closed subspaces are subobjects,
so different isomorphic presentations do not become distinct points. The family
predicate does not add reducedness, nonemptiness or a fixed Hilbert polynomial.
No independent smaller test universe makes the chart or scheme tests vacuous.
The extra proper/qc/qs predicates on a family are the node's own finite
presentation constituents, even though properness already forces qc and qs.

Searches for existing statements/notions:

- `msearch.py ... leanfinder`: "The Hilbert functor of proper flat finitely
  presented closed subspaces of a separated finitely presented algebraic space
  is an algebraic space locally of finite presentation". Eight results concern
  affine space, local finite presentation and openness; no Hilbert statement.
- `msearch.py ... loogle`: `HilbertFunctor, IsRepresentable`; zero hits,
  unknown identifier HilbertFunctor.
- `msearch.py ... grep`: `HilbertFunctor|ProperHilbert|hilbert.*represent`;
  two unrelated analytic Hilbert-space representation comments.
- `msearch.py ... leansearch`: "Hilbert functor representability for algebraic
  spaces". Eight hits on general Yoneda/representability and locally represented
  schemes; no Hilbert functor theorem.
- `rg` on `lean/WeilConjectures` for Hilbert and the item ID: Hilbert polynomial,
  Hilbert 90, and scheme fixed-degree Hilbert material, no exact statement.
  The exact item-ID search and proposed new declaration names have no hits.
- `rg` on `lean/Sheaf` for Hilbert and morphism predicates found
  `ProperHilbertPresheaf` for scheme maps only, and finite-degree Hilbert
  groupoids, neither the arbitrary-space Hilbert functor. The same search found
  the existing space morphism-property and closed-subspace modules reused here.
  DAG searches for their declarations identified their landed definition owners.

Validation: prescribed `scompile.py N8 lem-sfb-space-hilbert-representability`
compiled both the sandbox and named library module cleanly (2.9 s and 2.7 s).
The only postponed theorem is the item itself; every helper has real data.
No statement correction, STATEMENT-DISPUTED flag or node fault.

## Second reading by N8

This is the dispatcher's single worker, not an independent second agent; no
independent reading is claimed. The maintainer's independent review remains
required. In a separate self-check, I reopened the node and final module and
matched the base scheme and spaces, separatedness, all three finite-presentation
constituents, quotient by ambient isomorphism, the family's three properties,
locally finitely presented representing space, every scheme test and arbitrary
base-change naturality as detailed above. In particular the pullback condition
is in the sheaf category and uses the canonical ambient map, not an arbitrary
comparison. The compiler fix explicitly typed the scheme map as an algebraic-
space map before taking its sheaf map, avoiding an expensive ambiguous instance
search; it changed no mathematical condition.
