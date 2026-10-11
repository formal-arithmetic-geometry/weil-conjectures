## Worker report

The module `Sheaf.AlgebraicGeometry.ConstantGroupSchemeMorphismsClopen` states
`AlgebraicGeometry.constantGroupSchemeMorphismsClopen`, with its entire proof `sorry`.
No definition or proof is added. Its docstring gives all seven steps of the node's proof.

Hypotheses and objects:

- `T U : Scheme.{u}` and `s : U ⟶ T` render the base scheme and an arbitrary
  T-scheme. This uses the node's final generality clause, so no etale assumption is
  imposed. It applies in particular to objects of `T.Etale`, whose structure morphism
  has exactly this type. The small site is not used in the statement after this
  explicitly permitted generalization.
- `E : Type v` with `[AddCommGroup E]` renders an arbitrary abelian group.
  `[Small.{u} E]` is the size condition of the recorded constant-scheme declaration:
  the index set must fit in the universe of schemes for its coproduct to exist there.
  The two explicit universes allow enlarging the scheme universe for any index set;
  there is no countability, finiteness, or cardinal bound independent of universes.
- `ConstantGroupSchemePoint T E s` is precisely the subtype of maps `f` with
  `f ≫ constantGroupSchemeProjection T E = s`. All points, components, coprojections,
  sums, and canonical points are the dependency's existing declarations.

Clause-by-clause correspondence:

- The first existential equivalence `b` identifies points with indexed clopen
  decompositions, using the already landed `IsClopenDecomposition U E P`:
  its entries are open subschemes `P e : U.Opens`, pairwise disjoint, with supremum
  the whole scheme. The separate `IsClopen` clause explicitly asserts closedness.
- `((b f).1 e : Set U) = f.1 ⁻¹' constantGroupSchemeComponent T E e`
  is exactly the specified forward map, including its component labels.
- `(P.1 e).ι ≫ (b.symm P).1 = ((P.1 e).ι ≫ s) ≫ constantGroupSchemeIncl T E e`
  is the inverse's restriction formula on the open subscheme. The subsequent `∃! f`
  clause says this formula uniquely determines the point for every decomposition.
- `IsCompact (Set.univ : Set U) → Set.Finite {e | (P.1 e : Set U).Nonempty}`
  renders quasi-compactness and the finite number of nonempty pieces. Mathlib's
  topological `IsCompact` does not require Hausdorffness, and hence is the intended
  quasi-compactness for schemes.
- For every function `φ : U → E`, the equivalence between all fibres being open
  and all fibres being clopen is stated explicitly.
- The equivalence `Φ` has target `LocallyConstant U E`, Mathlib's bundled maps with
  open fibres; its `IsLocallyConstant.iff_isOpen_fiber` is the exact identification.
  `Φ f x = e ↔ f.1 x ∈ constantGroupSchemeComponent T E e` gives the prescribed
  label map `φ_f`. Bijectivity is part of `AddEquiv`, and the label condition ties
  this equivalence to the same decomposition as `b`.
- The canonical point's decomposition is `if e = e₀ then ⊤ else ⊥`.
  Its image under `Φ` is separately stated to be `LocallyConstant.const U e`.
- There is an `AddCommGroup` structure `a` on the existing point type, and its
  addition is required to equal `constantGroupSchemePointAdd T E s` on every pair.
  This avoids silently replacing the sum by an unrelated transported operation.
  With that local instance, `Φ : ... ≃+ LocallyConstant U E` is the claimed group
  isomorphism, and the explicit pointwise formula for the given sum is included.
- Finally, `c : E →+ ConstantGroupSchemePoint T E s` with
  `c e = constantGroupSchemeCanonicalMap T E s e` states that the existing canonical
  map is a group homomorphism. Mathlib's locally constant algebra is pointwise.

Dependencies read and used:

- `Sheaf.AlgebraicGeometry.ConstantGroupScheme`: `constantGroupScheme`,
  `constantGroupSchemeIncl`, `constantGroupSchemeProjection`,
  `constantGroupSchemeComponent`, `ConstantGroupSchemePoint`,
  `constantGroupSchemePointAdd`, `constantGroupSchemeCanonicalMap`.
  Its multiplication uses the named existence theorem, not hollow data.
- `Sheaf.AlgebraicGeometry.CoproductCopiesMorphismsClopen`:
  `AlgebraicGeometry.IsClopenDecomposition`. Its carrying node
  `lem-galois-coproduct-copies-morphisms-clopen` is added to `stmt_deps`, as allowed
  for already landed notions by brief-stage2 section 5. This module already covers
  the non-group correspondence but does not state the additional group-law and
  quasi-compact finiteness clauses, so it is not an existing match for this item.
- Mathlib dependency records: `AlgebraicGeometry.Scheme` and `Scheme.Hom`
  (`Mathlib.AlgebraicGeometry.Scheme`); `Scheme.Over` and `Hom.IsOver`
  (`Mathlib.AlgebraicGeometry.Over`); `Scheme.smallEtaleTopology` and `Scheme.Etale`
  (`Mathlib.AlgebraicGeometry.Sites.Etale` and `Morphisms.Etale`);
  `AlgebraicGeometry.IsOpenImmersion` (`Mathlib.AlgebraicGeometry.OpenImmersion`);
  `AlgebraicGeometry.IsClosedImmersion` (`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`).
  Their full signatures and docstrings were read. Open subschemes use Mathlib's
  `Scheme.Opens` and `.ι`. No separate closed-immersion predicate is needed for
  the clopen open subschemes, and no unused closed-immersion or site import is added.
- `Mathlib.Topology.LocallyConstant.Algebra`: `LocallyConstant`, `LocallyConstant.const`,
  the pointwise additive group instance, and the fibre characterizations from Basic.

Edge cases checked before writing:

The empty domain has exactly one point, decomposition and locally constant map;
all fibres are empty and the canonical map need not be injective (none is claimed).
The empty base forces an empty domain. The trivial group gives a single component
and a singleton point group. An empty group is excluded by `AddCommGroup` itself,
exactly as in the node, rather than by an additional inhabitance hypothesis.
Infinite groups and non-quasi-compact domains are allowed, with no finite-image
claim in that case. Quasi-compact non-Hausdorff schemes are allowed. No field,
characteristic, reducedness, connectedness, or separation assumptions are introduced.

Searches for existing declarations:

- `msearch.py ... leansearch "scheme morphisms into a coproduct of copies of the base
  correspond to locally constant maps"`: service unavailable, Internal Server Error.
- `msearch.py ... leanfinder "Morphisms to a constant group scheme correspond to
  locally constant maps and clopen decompositions"`: eight hits; condensed-space
  locally constant APIs, a Galois-category lemma, and `AffineSpace.homOverEquiv`;
  none gives the statement.
- `msearch.py ... loogle "LocallyConstant, AlgebraicGeometry.Scheme"`: zero hits.
- `msearch.py ... grep "constantGroupScheme|clopen.*[Ee]quiv|[Ee]quiv.*clopen"`:
  seventeen hits, on idempotents, Boolean clopens, discrete quotients and connected
  components; none is the constant-group-scheme statement.
- `rg -n 'constant-group|constantGroup|LocallyConstant'` in the upstream
  `WeilConjectures/AlgebraicGeometry` and the project's `lean/Sheaf/AlgebraicGeometry`:
  existing constant-scheme definitions and the clopen-decomposition module found;
  no group-scheme point equivalence. Other locally constant uses concern Picard
  degrees, torsors, constructible sheaves or cohomology.
- `grep -rn 'lem-weil-pbc-constant-group-scheme-morphism-clopen'` in upstream
  `WeilConjectures/`: no match. Full proposed declaration name searched in the
  upstream source, Mathlib, project Lean, and `dag/lean_names_upstream.json`: no collision.

Source checking: the local Stacks TeX files are absent on this machine, so read
[Stacks 03P5](https://stacks.math.columbia.edu/tag/03P5) and
[Stacks 03YW](https://stacks.math.columbia.edu/tag/03YW) directly. They identify
constant-group-scheme points with Zariski locally constant maps for any scheme
and identify the multiplication by componentwise group addition. The extended
restriction and clopen claims are the node's seven-step elaboration of this fact.
No statement fault, correction, or disputed claim was found.

## Second reading by K1

Independent verdict: the Lean says exactly what the node says. No mathematical,
statement, signature, or module repair was needed; only this review was appended.

Source read independently: Stacks TeX `groupoids.tex`,
`example-constant-group` (Tag 03YW), and `etale-cohomology.tex`,
`remark-constant-locally-constant-maps` (Tag 03P5), fetched from the Stacks
source repository because this clone has no local TeX. The former explicitly
allows any base scheme and any scheme over it; the latter imposes no
Noetherian, finite-group, characteristic, or separation assumptions.
[03YW](https://stacks.math.columbia.edu/tag/03YW) gives componentwise
multiplication and the functor of locally constant maps;
[03P5](https://stacks.math.columbia.edu/tag/03P5) identifies the representing
constant group scheme. The node specializes the abstract group to an abelian
one and spells out this correspondence. No statement correction is present.

Objects, hypotheses and conclusion checklist, written from the node before
checking the Lean:

- Base scheme T: `T : Scheme.{u}`. Exact, arbitrary scheme.
- Abelian group E: `E : Type v`, `[AddCommGroup E]`. Exact; no finite or
  countable assumption. `[Small.{u} E]` is the same universe requirement as
  the recorded coproduct definition. Every set-sized group is covered by
  choosing a common sufficiently large universe for it and the schemes.
- Constant scheme, inclusions, components and projection: the imported
  `constantGroupScheme`, `constantGroupSchemeIncl`,
  `constantGroupSchemeComponent`, `constantGroupSchemeProjection` are the
  coproduct, coprojections, their ranges and codiagonal, respectively.
  I opened their actual bodies in `ConstantGroupScheme.lean`; exact.
- T-scheme U with structure map s: `U : Scheme.{u}`, `s : U ⟶ T`.
  No etale instance is required because the node expressly includes every
  T-scheme. In particular this covers each small-etale-site object; exact.
- Morphisms over T: `ConstantGroupSchemePoint T E s` is the existing subtype
  with equation `f ≫ constantGroupSchemeProjection T E = s`; exact.
- Bijection with pairwise disjoint open-and-closed subschemes covering U:
  the first `∃ b : ... ≃ {P // IsClopenDecomposition U E P}`. I opened
  the latter definition: distinct entries are disjoint and their supremum
  is top. `U.Opens` gives the induced open subscheme, with no extra scheme
  structure chosen. The explicit `∀ P e, IsClopen ...` records closedness;
  it is already implied by disjointness and covering. Exact.
- Forward assignment: `((b f).1 e : Set U) = f.1 ⁻¹'
  constantGroupSchemeComponent T E e`. Exact labelled inverse images.
- Inverse assignment: `(P.1 e).ι ≫ (b.symm P).1 =
  ((P.1 e).ι ≫ s) ≫ constantGroupSchemeIncl T E e`.
  The additional `∃! f` clause asserts uniqueness for those restrictions;
  exact, with composition in Lean's diagrammatic order.
- Quasi-compact finiteness: `IsCompact (Set.univ : Set U) →
  Set.Finite {e | (P.1 e : Set U).Nonempty}` for every decomposition.
  Mathlib compactness has no Hausdorff requirement; exact.
- Equivalent maps with open or clopen fibres: the `∀ φ : U → E` iff,
  and the target `LocallyConstant U E` of `Φ`. I read its structure and
  `IsLocallyConstant.iff_isOpen_fiber`; no topology on E is required.
  `Φ f x = e ↔ f.1 x ∈ constantGroupSchemeComponent T E e`
  pins down precisely the node's label map, hence ties Φ to b; exact.
- Canonical map: the b formula with `if e = e₀ then ⊤ else ⊥` and
  `Φ (constantGroupSchemeCanonicalMap T E s e) = LocallyConstant.const U e`.
  I read the existing canonical point: it is `s ≫ ...Incl ... e`; exact.
- Sum and group isomorphism: `∃ a : AddCommGroup ...`, local instance a,
  `f + g = constantGroupSchemePointAdd ... f g`, and `Φ : ... ≃+ ...`.
  I read the existing sum's pullback pairing and chosen multiplication,
  including the named existence theorem supporting that choice. The
  explicit formula for `Φ (constantGroupSchemePointAdd ... f g) x`
  gives pointwise addition for the specified sum; exact, not an unrelated
  transported operation. LocallyConstant's algebra instances are pointwise.
- Canonical map is additive: `∃ c : E →+ ...`, with `∀ e, c e =
  constantGroupSchemeCanonicalMap T E s e`. Exact group homomorphism claim.

I also opened the dependency nodes and the signatures/docstrings for
`Scheme`, `Scheme.Hom`, `Scheme.Over`, `Hom.IsOver`,
`Scheme.smallEtaleTopology`, `IsOpenImmersion` and `IsClosedImmersion`.
The explicit structure map and commuting subtype are the recorded over-base
notion. Clopen open subsets have their induced open subscheme structure;
no arbitrary closed subscheme or private definition is substituted.
The added dependency `lem-galois-coproduct-copies-morphisms-clopen` is landed
and its existing `IsClopenDecomposition` has the exact needed meaning.
Its theorem lacks the present finite-support and specified group-law clauses,
so it cannot replace this item with an existing declaration.
There are no new definition nodes or dependency modules in this delivery.

Edge cases: an empty U gives the unique empty function and decomposition and
one morphism, so its point group is trivial; different constants may coincide,
and no injectivity of the canonical map is claimed. An empty T forces U empty.
For the trivial E only one piece is possible. An empty E is not an abelian
group, so the node does not quantify over it. Infinite E and non-quasi-compact
U are allowed; finiteness is conditional only. No n, field, or characteristic
occurs. Non-Hausdorff schemes are covered. Universes u and v are explicitly
bound, and every other variable is bound by the signature or a quantifier.

Independent searches, using different phrasing from the first reader:

- LeanFinder via msearch: "Sections of a discrete constant scheme over a base
  scheme are locally constant functions with pointwise group operation".
  Eight hits, including condensed locally constant modules, Scheme global
  sections and nonabelian zero cochains; no scheme-point equivalence.
- Loogle via msearch: `LocallyConstant, AddEquiv`: zero hits.
- `rg` for `constantGroupScheme|IsClopenDecomposition|locally.constant.*scheme|
  scheme.*locally.constant` over upstream WeilConjectures, project Sheaf and
  Mathlib AlgebraicGeometry: the existing dependency modules and sheaf,
  rank and Picard results, no complete matching theorem. I additionally
  opened upstream `AlgebraicGeometry/Sites/ConstantSheafSections.lean`:
  its theorem assumes connectedness and concerns sheaf sections, so is not
  this correspondence for arbitrary U.

H5/H6/H8/H9: the delivery introduces no definition and has one theorem with
exactly `by sorry`. Its docstring includes the source and blueprint identifier
and all seven proof steps. All three imports serve the signature; namespace
and file convention, line widths and explicit binders are correct.
The node's `lean.statement` was compared verbatim with the file signature:
identical. Server compilation by scompile completed cleanly in 1.7 seconds,
exit code 0, with no warnings. No mismatch was found; no correct text was rewritten.
