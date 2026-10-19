## Worker report

The module `Sheaf.AlgebraicGeometry.StrictLocalAlgebraicResidueModels` states
`AlgebraicGeometry.Scheme.exists_strictLocal_algebraicResidue_models`, with `sorry` only.
No definitions or proofs are added. The natural statement is unchanged.

Hypotheses and clauses, matched individually:

- The base field is `{K : Type u} [Field K]`.
- The finite type K-scheme is `(Y : Scheme.{u}) [Y.Over (Spec (.of K))]`, with
  `[LocallyOfFiniteType (Y ↘ Spec (.of K))] [QuasiCompact (Y ↘ Spec (.of K))]`.
- The geometric point is `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]`
  and `(s : Spec (.of Ω) ⟶ Y)`. Its underlying point y is
  `s (IsLocalRing.closedPoint Ω)`.
- The number b is inlined as `@Algebra.trdeg K (Y.residueField (s ...)) _ _ ...`;
  the explicit algebra is the canonical base-field residue map's `toAlgebra`.
  No arbitrary residue-field algebra structure is assumed.
- S is exactly `strictHenselizationScheme s`, the spectrum of the recorded strict
  henselization ring colimit, not a new model or an arbitrary local ring.
- The affine open neighbourhood is `∃ U : Y.Opens, s ... ∈ U ∧ IsAffineOpen U`.
- The coefficient extension is `∃ (L : Type u) (_ : Field L) (_ : Algebra K L)
  (_ : IsSepClosed L)`. Its transcendence degree is equated directly to that of κ(y),
  so introducing a separate natural-number b or a finiteness hypothesis is unnecessary.
- The small cofiltered system is `∃ (I : Type u) (_ : SmallCategory I)
  (_ : IsCofiltered I) (D : I ⥤ Over U.toScheme)`. Cofilteredness includes
  nonemptiness and is the dual of the node's filtered-opposite condition.
  Slice objects supply the V_i → U and slice arrows enforce their compatibility.
- `Nonempty (D.obj i).left` and `IsAffine (D.obj i).left` assert that every model
  is nonempty and affine. No monomorphism or subalgebra hypothesis is imposed.
- `p : ∀ i, (D.obj i).left ⟶ Spec (.of L)` gives each L-structure; both
  `LocallyOfFiniteType (p i)` and `QuasiCompact (p i)` assert finite type.
- The equation `(D.obj i).hom ≫ U.ι ≫ (Y ↘ Spec (.of K)) =
  p i ≫ Spec.map (CommRingCat.ofHom (algebraMap K L))` says precisely that
  V_i → U is a K-morphism with respect to the given L/K extension.
- `∀ (i j : I) (a : i ⟶ j), IsAffineHom (D.map a).left` asserts affine transitions.
- `(c : Cone D)` supplies the compatible maps over U, and `Nonempty (IsLimit c)`
  states their universal property in `Over U.toScheme`. The isomorphism
  `e : strictHenselizationScheme s ≅ c.pt.left` transports this universal property
  to S. `e.hom ≫ c.pt.hom ≫ U.ι = strictHenselizationStructuralMap s` ties the
  transported map to the canonical map S → Y, hence makes this the limit over U
  with the intended structural morphism, rather than an unrelated slice structure.
- For every `i` and `v : (D.obj i).left`, the final `@Algebra.IsAlgebraic` is over
  `U.toScheme.residueField ((D.obj i).hom v)` and on `(D.obj i).left.residueField v`,
  with the algebra explicitly induced by `((D.obj i).hom.residueFieldMap v).hom`.
  This is algebraicity for the actual induced residue extension at every point,
  not only points in the image of S and not a separately chosen field embedding.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Over`: `Scheme.Over` and `Over` (scheme over a base,
  morphisms over that base).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType` and
  `QuasiCompact` (the latter imported there from its defining QuasiCompact module).
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, `Scheme.SpecToEquivOfField`; geometric points are
  written inline as the recorded dependency prescribes. The residue map over the
  field is the existing `Scheme.Hom.residueFieldAlgebraMap` from
  `WeilConjectures.ZetaSeries`, whose full definition and docstring were read.
- `Mathlib.RingTheory.AlgebraicIndependent.Basic`: `Algebra.trdeg`.
- `Sheaf.AlgebraicGeometry.StrictHenselization`: `Scheme.strictHenselizationScheme`
  and its ring-colimit definition, read in full with its defining module.
- `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
- `Mathlib.CategoryTheory.Limits.HasLimits` and `Mathlib.CategoryTheory.Filtered.Basic`:
  `Cone`, `IsLimit`, `IsCofiltered` (dual universal property and filteredness).
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `IsAffineHom`.
- `Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap`:
  `Scheme.strictHenselizationStructuralMap` (the current landed dependency record).

The already stated proof dependencies are imported without `public`:
`Sheaf.RingTheory.StrictHenselizationTriples`,
`Sheaf.Paper.StrictHenselizationFunctoriality`, and
`Sheaf.AlgebraicGeometry.EtaleLocalRingTriples`.
The Mathlib definition proof dependencies are already publicly available from the
statement imports. The other proof dependencies have no recorded Lean declaration
and cannot yet be imported. No import cycle is introduced.

Source and edge cases: read the complete 0F0U proof and footnote, and the 0F0X
second-paragraph residue-field argument in `literature/stacks-project/etale-cohomology.tex`.
The docstring retains all nine DAG proof steps, including the finite-presentation
calculation, all filteredness axioms, tensor-model nonemptiness, the ring colimit
universal property, and residue algebraicity at every prime. For b = 0 the equality
of transcendence degrees still applies and no nonempty transcendence-basis type is
required. Positive characteristic and inseparable extensions are allowed: L is only
separably closed and residue extensions are only algebraic. The empty Y admits no s;
nonempty models and a nonempty indexing category are asserted as in the node. I and
all rings/schemes use the same u, so there is no too-small independent index universe.
An empty model is excluded exactly by the node. The cone is universal among all cones
in the slice, including nonaffine vertices. No finite-degree, injectivity-of-models,
or lifting-to-S hypothesis occurs.

Searches for reuse:

- msearch LeanFinder: "Strict henselization is an inverse limit of finite type schemes
  over a separably closed field with algebraic residue extensions": eight hits on
  henselian rings, field-valued points and an étale-algebra existence lemma; no match.
- msearch Loogle: "Algebra.trdeg, IsSepClosed": zero hits.
- msearch grep: "strictHensel|strict_hensel|strictlyHensel": zero Mathlib hits.
- msearch LeanSearch: "Strict localization finite type models separably closed field
  algebraic residue fields": unavailable (Internal Server Error).
- rg of upstream WeilConjectures and project lean/Sheaf for strict-local and
  algebraic-residue-model names found strict-local base change and the distinct smooth
  strict-local field model, not this assertion. The mandated grep of the item id in
  upstream WeilConjectures found no occurrences.
- rg of `dag/lean_names_upstream.json`, upstream WeilConjectures and lean/Sheaf for
  `exists_strictLocal_algebraicResidue_models|strictLocal.*[Mm]odel|algebraicResidue.*[Mm]odel`
  found no name collision or matching theorem (only projective-line comparison names).

Validation: server-only scompile.py compiled the delivered module in 1.7 seconds,
with nice 19, two threads, the 60-second per-file limit, and no errors or warnings.

## Landed dependency reused

The item's stmt_deps gains the already landed definition node
`def-weil-pbc-strict-henselization-structural-map`, making the canonical meaning
of “over U” explicit. Its current base record, repaired by NA on 2026-10-15,
already names `Scheme.strictHenselizationStructuralMap` in
`Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap`. The redundant stale
sandbox repair copy has therefore been removed: this delivery changes no dependency
record and adds no dependency module. Read the full construction and its
characterizing theorem, including the equality for every affine pointed
neighbourhood leg. No mathematical statement correction is needed.

## Worker revalidation (2026-10-15)

Rechecked the theorem against every hypothesis and conclusion of the current node,
the source proof and compatible-model footnote at Tag 0F0U, the residue-field
argument at Tag 0F0X, and the recorded dependency declarations. The Lean theorem
and its verbatim signature record require no changes. Removed obsolete reports of
the earlier admission blocker because the base now carries the required repair.
An independent second reading remains assigned to the next worker.

Final verification: the prescribed server-only `scompile.py` passed cleanly in
1.6 seconds (nice 19, two threads, 60 seconds per file). The prescribed
`deliver2.py --no-push` printed OK: compilation and preflight pass except for
the independent second reading, which the next reader supplies. Nothing was pushed.


## Second reading by NI

Independent second reader, 2026-10-15. Read the sandbox node and module, the
recorded statement dependency nodes and their declarations, the full constructions
in StrictHenselization and StrictHenselizationStructuralMap, and the Stacks source
at Tags 0F0U (lemma-strictly-henselian, including its compatible-triple footnote)
and 0F0X (lemma-interlude-I, second paragraph). No statement_change is present or
needed. No new definition node or dependency module is delivered.

The node's objects, hypotheses, and conclusions, matched individually:

1. Arbitrary field K: `{K : Type u} [Field K]`. Exact; no characteristic,
   perfection, algebraic closure, or finiteness restriction on K.
2. Finite type K-scheme Y: `(Y : Scheme.{u}) [Y.Over (Spec (.of K))]`,
   `[LocallyOfFiniteType (Y ↘ Spec (.of K))]` and
   `[QuasiCompact (Y ↘ Spec (.of K))]`. Exact conjunction in the recorded
   finite-type node. Read both Mathlib classes: finite type on affine opens
   and quasi-compact inverse images, respectively. No separatedness assumed.
3. Geometric point and its underlying point: `{Ω : Type u} [Field Ω]
   [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)` and
   `s (IsLocalRing.closedPoint Ω)`. Exact inline geometric-point convention;
   SpecToEquivOfField identifies this with the point and its residue embedding.
4. b = trdeg_K κ(y): the right side of the displayed `Algebra.trdeg` equality
   uses `Y.residueField (s (IsLocalRing.closedPoint Ω))` with the explicit algebra
   `((Y ↘ Spec (.of K)).residueFieldAlgebraMap ...).toAlgebra`. Exact; read
   ZetaSeries' definition, which composes the canonical field-to-Spec-residue
   identification with the actual induced residue map. There is no freely
   chosen algebra structure or extra natural-number finiteness assumption.
5. S = Spec of the strict henselization at s: `strictHenselizationScheme s`.
   Exact recorded dependency. Its body is Spec of the coordinate-ring colimit
   on the small model of affine pointed étale neighbourhoods, not an unrelated
   strict-local scheme. Read its coordinate diagram, cone, and properties.
6. Affine open neighbourhood U of y: `∃ U : Y.Opens, s ... ∈ U ∧ IsAffineOpen U`.
   Exact: membership and affineness are both present.
7. Separably closed extension L/K with trdeg_K L = b: existential `L : Type u`,
   `Field L`, `Algebra K L`, `IsSepClosed L`, and the trdeg equality above.
   Exact; an algebra over a field into a field gives the required embedding.
   IsSepClosed requires splitting of separable polynomials, not algebraic closure.
8. Small cofiltered inverse system over U: existential `I : Type u`,
   `SmallCategory I`, `IsCofiltered I`, and `D : I ⥤ Over U.toScheme`.
   Exact; read IsCofiltered's two cone axioms and its Nonempty field. Slice
   morphisms enforce commutation with the maps to U; no poset restriction.
9. Every V_i nonempty affine: `∀ i, Nonempty (D.obj i).left ∧
   IsAffine (D.obj i).left ∧ ...`. Exact, with no subalgebra or embedding claim.
10. Each V_i finite type over L: existential family `p : ∀ i,
    (D.obj i).left ⟶ Spec (.of L)` and both `LocallyOfFiniteType (p i)` and
    `QuasiCompact (p i)`. Exact, using the same finite-type convention as for Y.
11. V_i → U are K-morphisms: the equation
    `(D.obj i).hom ≫ U.ι ≫ (Y ↘ Spec (.of K)) =
    p i ≫ Spec.map (CommRingCat.ofHom (algebraMap K L))`.
    Exact structural compatibility with the selected L/K, not arbitrary maps.
12. Affine transitions over U: `∀ (i j : I) (a : i ⟶ j),
    IsAffineHom (D.map a).left`. Exact recorded affine-morphism predicate;
    the Over functor supplies the over-U compatibility automatically.
13. S is the inverse limit over U, with its intended structural map:
    existential `c : Cone D`, `e : strictHenselizationScheme s ≅ c.pt.left`,
    `Nonempty (IsLimit c)`, and
    `e.hom ≫ c.pt.hom ≫ U.ι = strictHenselizationStructuralMap s`.
    Exact: Cone gives compatible legs, IsLimit quantifies over every cone in
    the slice, and e transports these to S. The last equation makes the map
    S → U the factorization of its canonical map to Y. Read the structural
    map's existence theorem and definition: every representative limit leg
    has exactly this composite. It selects a determined morphism, not hollow data.
14. For every i and every v, κ(v)/κ(u) is algebraic for u its actual image:
    final `∀ (i : I) (v : (D.obj i).left), @Algebra.IsAlgebraic
    (U.toScheme.residueField ((D.obj i).hom v))
    ((D.obj i).left.residueField v) _ _
    (((D.obj i).hom.residueFieldMap v).hom.toAlgebra)`.
    Exact: read residueFieldMap and Algebra.IsAlgebraic; the latter means
    every element is killed by a nonzero polynomial. This covers all model
    points, without a lift to S, finite-degree assumption, or separability claim.

Source check: 0F0U assumes just a field and finite type scheme. Its proof embeds
K(t_1,...,t_b)^sep into the strict henselization and constructs tensor models
from compatible étale triples. 0F0X uses their algebraic residue control.
The node spells out that refined input; its nine-step proof justifies it without
assuming models inject into the colimit. The Lean docstring retains all nine
steps: affine chart and transcendence basis, coefficient embedding, étale ring
diagrams, finite-presentation factoring and eventual equality, all filteredness
axioms, tensor models and nonemptiness, the colimit universal property, residue
algebraicity at every prime, and affine transitions including b = 0. No omitted
source-wide Noetherian, separatedness, or characteristic assumption was found.

Edge cases: b = 0 is included by the same cardinal equality and the empty
transcendence basis in the proof. Empty Y admits no s, as mathematically required;
empty models and an empty index category are explicitly excluded by the node
and the Lean alike. Nonreduced schemes and positive characteristic remain allowed;
L is only separably closed and the residue extensions only algebraic. All objects
and the small index use the common universe u required by the recorded scheme
and strict-henselization APIs; no independently smaller universe makes a test
condition vacuous. Cone universality includes nonaffine test vertices. There is
no n or coefficient torsion restriction in this statement.

Independent reuse searches (different wording from the first worker):

- msearch LeanFinder: "Approximation of strict localization by affine schemes over
  separably closed fields with algebraic residue maps". Eight hits about affine
  neighbourhoods and ring-hom properties, none giving this statement.
- msearch Loogle: `IsSepClosed, Algebra.IsAlgebraic`. Two hits, both field-theoretic
  purely inseparable/separably closed extension facts, neither this theorem.
- msearch grep: `henselization|henselian`. Five hits in Mathlib's Henselian ring
  theory, no strict-local model theorem.
- msearch LeanSearch: "Strict localization inverse limit finite type separably
  closed coefficient field algebraic residue extensions". Service unavailable
  (Internal Server Error), recorded without a no-match verdict.
- Direct rg on Mathlib algebraic geometry, upstream WeilConjectures, project
  lean/Sheaf, and dag/lean_names_upstream.json using algebraicresidue/model,
  strictlocal/model and strict-local finite-type/separably-closed variants.
  Hits concern strict transforms, strictly henselian stalks, and projective-line
  model comparisons; no equivalent theorem. Upstream grep for this node id has
  no occurrences. Existing dependency notions are all reused.

Mismatches and changes: none found in the mathematical statement or its rendering.
Left the Lean module and node signature unchanged; appended this independent
reading to the worker report. No hollow definitions, private copies, local notation,
extra theorem, or proof was introduced. The sole theorem ends in sorry. All
variables and the universe are explicitly bound; no line exceeds 100 characters.
Checked the node's lean.statement is verbatim equal to the file's theorem signature.

Validation: prescribed server-only scompile.py passed cleanly in 1.6 seconds,
nice 19, two threads, 60 seconds per file. The prescribed deliver2.py --no-push
printed OK: compilation and preflight both pass with this second reading.
