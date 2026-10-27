## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteInertiaEtaleAffineCharts` states
`CategoryTheory.finite_inertia_etale_affine_charts`, with one `sorry` and no
new definitions. It follows Stacks Tag 0DUE, all four conclusions, and the
finite-flat affine presentation of Tags 0DUL and 0DUM. I read those source
statements and the full proof in literature/stacks-project/stacks-more-morphisms.tex
(lines 3110ff and 3581ff). The supplied DAG statement needs no correction.

Hypotheses and conclusions, clause by clause:

- The field is `(k : Type u) [Field k]`; the base is `Spec (CommRingCat.of k)`.
- The stack over this base is `F : BasedCategory.{v, w} (Over (Spec ...))`,
  with `hF : IsAlgebraicModuliStack F`. This is the general algebraic-stack
  predicate, not its Deligne--Mumford specialization.
- The inertia category is the existing `moduliInertia F`, with vertical
  automorphisms as objects; `hI : IsRepresentableFiniteModuliMap
  (moduliInertiaProjection F)` says every scheme base change is a finite scheme
  with its actual projection identified over the base.
- `∃ (J : Type (max u w)) (X : J → BasedCategory...) (g : ∀ j, BasedFunctor (X j) F)`
  gives the small family and the actual maps. The chart object/morphism bounds
  `max (u+1) w` and `max u v` contain both the scheme category and the original
  category's bounds. The point set is a quotient of field objects in the given
  object universe, so the index bound includes it.
- Joint surjectivity is exactly `∀ x : ModuliPoints F, ∃ j y,
  moduliPointMap (g j) y = x`, the first conclusion of Tag 0DUE.
- Each `X j` satisfies `IsAlgebraicModuliStack`.
- `IsRepresentableByAlgebraicSpaces (g j)` gives representability on every
  scheme test; `ModuliSpaceTest (@Etale) (g j)` tests étaleness on all étale
  scheme charts of the actual base changes.
- `ModuliSchemeTest (@IsProper) (moduliRelativeDiagonal (g j))` is separatedness
  of the map, not separatedness of the target. Since the map is representable
  étale, its relative diagonal is an immersion, and requiring proper scheme
  tests expresses its proper relative diagonal exactly. No smooth-inertia or
  proper-target hypothesis is used.
- For each scheme `T` and each `x : Functor.Fiber (X j).p T`, bijectivity of
  `fun α : x ≅ x ↦ (moduliFiberMap (g j) T).mapIso α` is the canonical
  isomorphism on automorphism sheaves. It gives the inertia comparison, not an
  arbitrary equivalence of inertia categories. Quantification over every object
  in every scheme fibre includes every restriction and every nonreduced test;
  consequently it expresses the full scheme-theoretic stabilizer isomorphism,
  not just equality on geometric point sets.
- The affine scheme is `U : Over (Spec ...)`, with `IsAffine U.left`, and its
  map is `a : BasedFunctor (discreteModuli (yoneda.obj U)) (X j)`.
- `ModuliSchemeTest (fun _ _ f ↦ IsFinite f ∧ Flat f ∧
  LocallyOfFinitePresentation f ∧ Surjective f) a` says this map is
  representable surjective finite flat finitely presented. A finite scheme
  morphism is quasi-compact and separated, so local finite presentation here
  is equivalent to finite presentation; no finite-presentation clause is lost.
- `R`, `s`, `t`, `e`, `i`, and `c : pullback s.left t.left ⟶ R.left` specify
  the whole scheme groupoid. `IsAffine R.left` and both
  `s.left.IsFiniteLocallyFree`, `t.left.IsFiniteLocallyFree` are explicit.
- `IsSchemeStackDiagonalPresentation a a s t` identifies `R` with the actual
  two-fibre product, retaining both projections up to vertical natural
  isomorphisms. The existing two-fibre product retains its specified comparison
  isomorphism; it is not an ordinary set fibre product.
- `Nonempty (SchemeGroupoidQuotientPresentation s t e i c (X j) a)` supplies
  the recorded groupoid laws, original arrow identifications and composition,
  fppf descent and local essential surjectivity. By its definition this is
  exactly `X j ≃ [U/R]`, the fppf stackification, up to equivalence over the base.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: `Field`; Mathlib.AlgebraicGeometry.Scheme:
  `Scheme`, `Spec`; Mathlib.AlgebraicGeometry.Sites.Fpqc: `fppfTopology`.
- Mathlib.AlgebraicGeometry.Morphisms.Finite, Flat, FinitePresentation,
  Etale and Proper: `IsFinite`, `Flat`, `LocallyOfFinitePresentation`,
  `Etale`, `IsProper`. Their full class signatures and source docstrings were
  read. The degree clause of the finite-locally-free dependency is unused.
- WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree:
  `Scheme.Hom.IsFiniteLocallyFree` (finite, flat, locally finitely presented).
- Sheaf.AlgebraicGeometry.AlgebraicSpace: `AlgebraicSpace`,
  `AlgebraicSpace.IsEtale`, its representable-chart definitions.
- Sheaf.AlgebraicGeometry.AlgebraicModuliStack: `IsAlgebraicModuliStack`;
  Sheaf.AlgebraicGeometry.AdequateModuliSpace: the recorded definition was
  inspected and its module imported, but adequacy is not a hypothesis here.
- Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids: `BasedCategory`-based
  interfaces `discreteModuli`, `moduliFiberMap`, `moduliTwoFiberProduct`,
  `IsRepresentableByAlgebraicSpaces`, and the projection-retaining base changes.
- Sheaf.AlgebraicGeometry.ModuliInertia: `moduliInertiaProjection` and its
  explicit automorphism construction.
- Sheaf.AlgebraicGeometry.FiniteStackSchemeTests:
  `IsRepresentableFiniteModuliMap`.
- Sheaf.AlgebraicGeometry.DmStackMorphismProperties: `ModuliPoints`,
  `moduliPointMap`, `ModuliSchemeTest`, `ModuliSpaceTest`, `moduliRelativeDiagonal`.
  These declarations bind arbitrary based categories, so use imposes no DM
  hypothesis despite the owning module's historical name.
- Sheaf.AlgebraicGeometry.SchemeGroupoidLaws: `Scheme.IsGroupoid`;
  Sheaf.AlgebraicGeometry.SchemeGroupoidQuotientPresentation:
  `SchemeGroupoidQuotientPresentation`;
  Sheaf.AlgebraicGeometry.SchemeStackDiagonalPresentation:
  `IsSchemeStackDiagonalPresentation`.

The five extra owning definition nodes already exist and are landed; they were
added to stmt_deps under the rule allowing landed statement dependencies. No
new nodes or dependency modules are needed. Already stated proof dependencies
are imported nonpublicly: StackChartwiseSmoothEtaleCalculus, StackPointTopology,
Mathlib's Proj scheme, QuasiFinite, and the finite/proper permanence interfaces
already publicly imported. The other proof-dependency nodes have no Lean record
or usable Mathlib match yet and introduce no missing statement-level notion;
they are referenced step by step in the theorem's proof docstring.

Edge cases checked before writing:

- Empty F: J can be empty; there is no Nonempty binder or required chart.
- Empty schemes and degree-zero finite locally free morphisms are allowed.
- No finite type, quasi-compactness, or separatedness of F is assumed.
- In positive characteristic, infinitesimal finite stabilizers are allowed:
  testing all schemes and fibre automorphisms does not discard nilpotents.
- The index and chart universes include the point set and scheme category;
  no unrelated too-small universe makes scheme tests vacuous.
- The map on inertia and the relation's projections are the canonical ones.

Searches for a pre-existing statement (2026-10-24):

- msearch.py leanfinder, query "Algebraic stack with finite inertia has
  stabilizer preserving separated etale charts with finite flat affine covers":
  eight hits, all scheme étale/related properties; none states this result.
- msearch.py leansearch, query "finite inertia algebraic stack etale finite flat
  affine charts": eight hits, scheme/étale-ring/flatness facts, no stack chart theorem.
- msearch.py loogle, query "IsAlgebraicModuliStack,
  IsRepresentableFiniteModuliMap": zero hits (unknown project identifier).
- msearch.py grep, query "well.nigh|finite.inertia|stabilizer.preserving": zero hits.
- rg in lean/WeilConjectures for finite inertia and this declaration, and
  grep -rn for the exact node id: no matching statement (one unrelated ring
  inertia comment). rg in lean/Sheaf finds consumers and the different
  AffineStackStabilizerEtaleComparison theorem. The latter assumes DM and an
  already given pair of maps/quotient, and does not assert existence of charts.
- rg in dag/lean_names_upstream.json, Mathlib, WeilConjectures and Sheaf for
  finite_inertia_etale_affine_charts: no declaration exists.

Validation: scompile.py compiled this file both in its private sandbox and at
its library module name, with exit code 0, no errors or warnings (39.0 s and
13.1 s). autoImplicit is explicitly disabled. All source lines are at most
100 characters. The node signature is copied verbatim from theorem through
its type before `:=`. No statement dispute or source fault was found.

## Second reading by Q156

I reopened the node and the completed module for a separate clause-by-clause
self-audit; no second agent was started, as the dispatcher explicitly prohibits
it. The maintainer's independent review remains the independent reading.
The audit checked the actual inertia projection, joint point surjectivity,
general algebraicity, representability, relative proper diagonal and chartwise
étaleness, automorphism maps on all schemes, affine finite flat presentations,
both finite locally free projections, and the fppf quotient presentation.
No mismatch or statement correction was needed. In particular I checked that
separatedness is relative to F and that the automorphism clause tests every
scheme, not just geometric fields. Both projections are retained separately
in the diagonal presentation. The direct dependencies initially omitted the
five already landed owning definition nodes used to express these clauses;
those were added to stmt_deps without changing any existing statement.
