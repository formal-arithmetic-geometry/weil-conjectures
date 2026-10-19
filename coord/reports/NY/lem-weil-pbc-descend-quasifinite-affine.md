## Worker report

The module `Sheaf.AlgebraicGeometry.DescendQuasiFiniteAffine` states
`AlgebraicGeometry.descend_isQuasiFinite_affine`, with `sorry` as the entire proof.
No definitions, new nodes, dependency modules, or statement corrections are needed.
The node copy changes only `lean`.

The statement matches the node clause by clause:

- A small nonempty directed partially ordered index set is `{I : Type u}` with
  `[PartialOrder I] [IsDirected I (· ≤ ·)] [Nonempty I]`.
- The directed system of commutative rings is `A : I ⥤ CommRingCat.{u}`. The preorder
  category gives exactly the transition maps associated to inequalities.
- The colimit ring and its canonical structure maps are `c.pt` and `c.ι.app i`,
  for `c : Cocone A` and `hc : IsColimit c`. This allows any colimit with its legs,
  rather than restricting the statement to a particular chosen representative.
  The index and ring universes are the same, as required by the limit convention.
- The fixed initial index is `i₀ : I`.
- The initial algebra is the ring `B₀ : CommRingCat.{u}` with structure map
  `b₀ : A.obj i₀ ⟶ B₀`. Its finite presentation is `hfp : b₀.hom.FinitePresentation`.
  By its read definition this is precisely `Algebra.FinitePresentation` for
  `b₀.hom.toAlgebra`; it imposes no extra condition.
- The tensor product `A ⊗[Aᵢ₀] B₀` is represented by the commutative-ring pushout
  `pushout (c.ι.app i₀) b₀`. Its structure map from the limit ring is
  `pushout.inl (c.ι.app i₀) b₀`. This is exactly the pushout formulation explicitly
  given by the node. `CommRingCat.pushoutCoconeIsColimit` identifies it with the
  tensor product and its left inclusion, and `pullbackSpecIso` identifies its
  spectrum with the affine fibre product. No extra tensor-product notion is defined.
- Quasi-finiteness at the limit is `hqf : Scheme.Hom.IsQuasiFinite
  (Spec.map (pushout.inl (c.ι.app i₀) b₀))`.
- The eventual index and inequality are `∃ (i : I) (hi : i₀ ≤ i)`.
- The stage algebra is `pushout (A.map (homOfLE hi)) b₀`, exactly
  `Aᵢ ⊗[Aᵢ₀] B₀`; the conclusion applies the same `IsQuasiFinite` predicate to
  `Spec.map` of its left inclusion.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Limits.HasLimits`: `CategoryTheory.Limits.colimit`,
  its cocone/legs, and the universal-property encoding `Cocone` and `IsColimit`
  (their full declarations were read in `Cones` and `IsLimit`). The statement uses
  a specified colimit cocone rather than the chosen colimit object.
- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation` and
  `RingHom.FinitePresentation`, whose definition reduces to the former for the
  given structure map.
- `Mathlib.AlgebraicGeometry.Pullbacks`: `AlgebraicGeometry.pullbackSpecIso`,
  including its projection formulas. This justifies the node's pushout encoding.
  The explicit tensor-product pushout and universal property were also read in
  `Mathlib.Algebra.Category.Ring.Constructions`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`.
- `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`:
  `AlgebraicGeometry.Scheme.Hom.IsQuasiFinite`, defined as locally finite type,
  quasi-compact, and every source point isolated in its scheme-theoretic fibre.
  This is the recorded Stacks notion, including finite type.

The module imports all recorded available proof-dependency modules, without
`public` when needed only for the proof. These include affine morphism permanence,
finite type (already public through the statement imports), scheme fibres (already
public through QuasiFiniteMorphism), topological Krull dimension and dimension at a
point, and `Sheaf.AlgebraicGeometry.QuasiFiniteLocallyQuasiFinite`. The affine-limit
fibre-dimension bound and ring zero-fibre-dimension criterion have neither Lean
records nor Mathlib matches, hence have no modules to import. Their exact node ids
and uses remain in the theorem's complete four-step proof docstring.

Source checked: the local Stacks `limits.tex`, Situation 081D
(`situation-descent-property`) and Tag 094M (`lemma-descend-quasi-finite`).
In the affine specialization all schemes are quasi-compact and quasi-separated,
and finite presentation implies the locally-finite-type hypothesis of 094M.

Edge cases checked before writing: the zero base or zero algebra is allowed by
`CommRingCat`; the corresponding empty spectra and vacuous pointwise conditions
are retained. A one-element directed system is allowed, and the eventual stage
may be `i₀`. Nonempty is explicit; there is no restriction on characteristic,
Noetherianness, injectivity of transition maps, or faithful flatness. Neither
finite presentation nor quasi-finiteness is a hollow hypothesis: finitely
presented polynomial algebras of positive relative dimension fail the latter,
and arbitrary algebras need not satisfy the former.

Searches made with `msearch.py NY lem-weil-pbc-descend-quasifinite-affine`:

- LeanFinder: “Quasi finiteness of a finitely presented algebra descends along a
  directed colimit of rings”: eight hits on finite presentation and factorization
  through colimits, none stating quasi-finiteness descent.
- Loogle: `"QuasiFinite", "colimit"`: zero hits.
- Mathlib grep: `descend.*[Qq]uasi[Ff]inite|[Qq]uasi[Ff]inite.*(colimit|limit)`:
  zero hits.
- LeanSearch: “Quasi finiteness descends along filtered colimits of finitely
  presented algebras”: service unavailable, Internal Server Error.
- `rg` of the same expression and the exact node id in upstream
  `WeilConjectures` and the project's `lean/Sheaf`: no hits.
- `rg` of the proposed declaration name in upstream sources, the project sources,
  and `dag/lean_names_upstream.json`: no hits.

No statement dispute or node fault was found. The server-only `scompile.py`
check compiled the delivered file cleanly (1.3 seconds, nice 19, two threads,
60-second file limit). No local compiler or library build was run.


## Second reading by NY

I independently read the node, its five statement-dependency records and their
actual declarations, and Stacks limits.tex, Situation 081D and Lemma 094M.
No mismatch was found; the Lean module and node signature are unchanged.
The complete object/hypothesis/conclusion checklist is:

- Small nonempty directed poset: `{I : Type u}` with `PartialOrder I`,
  `IsDirected I (· ≤ ·)`, and `Nonempty I`. Exact.
- Directed commutative rings and transition maps: `A : I ⥤ CommRingCat.{u}`,
  with `A.map (homOfLE hi)` for an inequality. Exact; no injectivity assumed.
- Colimit ring with canonical legs: `c : Cocone A`, `hc : IsColimit c`,
  ring `c.pt`, maps `c.ι.app i`. The read `Cocone` fields encode compatible
  legs and `IsColimit.desc/fac/uniq` their universal property. Exact.
- Chosen starting index: `i₀ : I`. Exact.
- Finitely presented algebra at that index: `B₀ : CommRingCat.{u}`,
  `b₀ : A.obj i₀ ⟶ B₀`, and `hfp : b₀.hom.FinitePresentation`.
  The read RingHom definition is precisely Algebra.FinitePresentation for
  `b₀.hom.toAlgebra`, using the recorded dependency, with no extra algebra
  structure or finiteness assumption. Exact.
- Limit tensor algebra and morphism: the pushout of `c.ι.app i₀` and `b₀`,
  with `Spec.map (pushout.inl (c.ι.app i₀) b₀)`. Exact. I read
  `CommRingCat.pushoutCoconeIsColimit`, its tensor-product vertex and left
  inclusion, and `pullbackSpecIso` with both projection formulas. These
  identify the pushout and its particular structure map with the node's
  tensor product and affine fibre-product projection, rather than merely
  an unspecified isomorphic ring.
- Quasi-finiteness hypothesis: `hqf : Scheme.Hom.IsQuasiFinite (...)`.
  The dependency's actual definition is local finite type, quasi-compactness,
  and openness of every point singleton in its scheme-theoretic fibre.
  This is the node's finite-type, isolated-fibre-point notion. Exact; the
  weaker Mathlib predicate is not substituted.
- Eventual index with inequality: `∃ (i : I) (hi : i₀ ≤ i)`. Exact.
- Eventual algebra and conclusion: `Scheme.Hom.IsQuasiFinite
  (Spec.map (pushout.inl (A.map (homOfLE hi)) b₀))`. This uses the same
  canonical left structure map at the stage, with exactly the required
  existential quantifier order. Exact.

The source assumes quasi-compact, quasi-separated initial schemes and affine
transition morphisms. All schemes here are spectra, so these conditions follow
without extra hypotheses. The node explicitly specializes 094M to a finitely
presented initial algebra, which supplies the source's local finite type;
no correction to the node is warranted.

Edge cases: an empty index is excluded by the node itself and by both `i₀`
and Nonempty. Singleton systems and `i = i₀` are allowed. Zero rings and zero
algebras, hence empty spectra, are allowed: no Nontrivial instance is present.
Finite presentations with zero generators or relations are covered. There is
no characteristic, Noetherian, field, flatness, or transition-surjectivity
assumption. The shared universe for the small index and the rings is the
project's directed-colimit convention; arbitrary small data can be placed in
a common universe. All variables and universe parameters are explicitly bound.

Independent duplicate searches used different wording:

- LeanFinder via msearch.py: "A quasi-finite base change of a finitely presented
  ring algebra descends to an index in a filtered ring diagram". Eight hits,
  principally RingHom.EssFiniteType factorization through colimits,
  CommRingCat.isFinitelyPresentable_hom, and finite-presentation transitivity;
  none states quasi-finiteness descent.
- Loogle via msearch.py: `"QuasiFinite", "IsColimit"`: zero hits.
- Direct rg across Mathlib, upstream WeilConjectures, and project lean/Sheaf:
  `(quasi.?finite.*(filtered|directlimit|iscolimit|descend)|descend.*quasi.?finite)`
  case-insensitively. The upstream surjective-base-change descent theorem and
  a project quasi-finite-locus comment are the only hits. Neither is descent
  along a filtered ring colimit. No duplicate statement was found.

There are no new definition nodes, dependency modules, or statement corrections
in this delivery. I also read the recorded locally-quasi-finite equivalence
used in the proof plan. The four proof-docstring steps track the node's tail
colimit, dimension-zero fibres, eventual dimension bound, and pointwise
criterion plus quasi-compactness. The module contains one theorem with whole
proof `sorry`, no definitions, no private notation or local instances, and no
hollow assumptions. Source and blueprint docstrings and the verbatim node
signature are correct. Second reading changed only this report.

Validation: server-only scompile.py and deliver2.py preflight/compile checks;
no local compiler, global build, or upstream source modification.
