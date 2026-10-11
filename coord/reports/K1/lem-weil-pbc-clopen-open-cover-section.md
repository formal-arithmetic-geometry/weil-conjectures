## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteClopenOpenCoverSection` states
`AlgebraicGeometry.exists_section_of_finite_clopen_open_cover`. It uses `Scheme`
for schemes and a morphism `p : V ⟶ Z`, with `[IsFinite p]` rendering finite and
`[Surjective p]` rendering surjective. The finite disjoint union is represented by
`Vi : Fin n → Scheme`, coproduct injections `k : ∀ i, Vi i ⟶ V`, and
`hcop : IsColimit (Cofan.mk V k)`. The phrase open and closed subschemes is rendered
by `hk : ∀ i, IsOpenImmersion (k i) ∧ IsClosedImmersion (k i)`. Restrictions are
`pi : ∀ i, Vi i ⟶ Z` with `hpi : ∀ i, pi i = k i ≫ p`, and each restriction is an
open immersion through `[∀ i, IsOpenImmersion (pi i)]`. The conclusion is exactly
`∃ s : Z ⟶ V, s ≫ p = 𝟙 Z`.

Dependencies used are Mathlib `AlgebraicGeometry.Scheme`,
`AlgebraicGeometry.IsFinite`, `AlgebraicGeometry.Surjective`, and
`AlgebraicGeometry.IsOpenImmersion`; `IsClosedImmersion` and the coproduct colimit
are also Mathlib declarations. No project dependency module was needed.

Edge cases checked: `n = 0` is admitted (surjectivity then forces the only possible
empty-source situation); `n = 1` is represented; empty schemes are not excluded;
`Fin n` permits every finite index cardinality.

Searches made: `msearch.py leanfinder` for a finite surjective morphism whose clopen
open-immersion components give a section (no match); `msearch.py loogle` for
`AlgebraicGeometry.IsFinite, AlgebraicGeometry.Surjective,
AlgebraicGeometry.IsOpenImmersion, CategoryTheory.IsSplitEpi` (no match for the
combined theorem); `rg` in `WeilConjectures/` and `lean/Sheaf/` for clopen section
and finite-cover section statements (no existing statement). Mathlib grep found
only the component declarations and coproduct building blocks.

## Earlier second reading (a previous round; superseded)

The node's finite and surjective hypotheses are the typeclass binders `[IsFinite p]`
and `[Surjective p]`. Its finite disjoint-union object is represented by `Fin n`,
`Vi`, `k`, and the explicit colimit hypothesis; open-and-closed inclusions are the
two conjuncts in `hk`. The restriction clause is the equality `hpi` together with
open-immersion instances for `pi`. The final section equation is rendered verbatim
as `s ≫ p = 𝟙 Z`. No mismatch was found.

## Second reading by K1

I independently opened the sandbox node and Lean module, all four statement-dependency
nodes, and their recorded Mathlib declarations. I read Stacks Tag 09ZA at
`/home/ubuntu/c1-stacks-review/etale-cohomology.tex`, lines 14390–14424, and checked
its label against that checkout's `tags/tags`. The repository's literature copy
is absent on this machine. The lemma first assumes an affine integral normal
ambient scheme with separably closed function field, a closed subscheme Z, and an
affine étale V. Its final paragraph isolates exactly the finite clopen decomposition
argument used by this node: those earlier hypotheses produce the decomposition;
the section argument uses only the decomposition, finiteness and surjectivity.
No extra ambient scheme, affine, normal, field or étale hypothesis belongs in
this extracted tool statement. There is no statement correction in this delivery.

Object/hypothesis/conclusion checklist, in the node's order:

- Scheme Z and scheme V: `(Z V : Scheme.{u})`. Exact. The dependency
  def-pc-scheme points to `AlgebraicGeometry.Scheme` and `Scheme.Hom` in
  Mathlib.AlgebraicGeometry.Scheme. I read its local-affine definition and its
  locally-ringed-space morphism structure, rather than substituting a topological
  space or an affine scheme.
- Morphism p from V to Z: `(p : V ⟶ Z)`. Exact scheme morphism in that category.
- Finite p: `[IsFinite p]`. Exact. The dependency
  def-weil-finite-integral-morphism records `AlgebraicGeometry.IsFinite` in
  Mathlib.AlgebraicGeometry.Morphisms.Finite: it extends IsAffineHom and requires
  the ring map on every affine open to be finite. The integral alternative in
  that dependency is not substituted for finite.
- Surjective p: `[Surjective p]`. Exact. The dependency
  def-weil-surjective-morphism records `AlgebraicGeometry.Surjective` in
  Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap, whose `surj` field is
  Function.Surjective on the underlying scheme map.
- Finite family indexed by 1,…,n: `{n : ℕ}` and `(Vi : Fin n → Scheme.{u})`.
  Exact after the harmless zero-based relabelling of the same finite set.
- Disjoint-union inclusions: `(k : ∀ i, Vi i ⟶ V)` and
  `(hcop : IsColimit (Cofan.mk V k))`. Exact. I read Cofan.mk in
  Mathlib.CategoryTheory.Limits.Shapes.Products and IsColimit in
  Mathlib.CategoryTheory.Limits.IsLimit: this is the coproduct universal property
  for the given injections, not an arbitrary cover. Scheme coproducts are
  disjoint unions; Mathlib.AlgebraicGeometry.Limits also has
  `nonempty_isColimit_cofanMk_of` for covering pairwise-disjoint open subschemes.
- Each component open and closed in V:
  `(hk : ∀ i, IsOpenImmersion (k i) ∧ IsClosedImmersion (k i))`. Exact. The
  closed-immersion declaration in Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
  requires a closed embedding and surjective stalk maps. An open subscheme with
  closed image is a closed immersion too, so this does not strengthen clopen.
- Restrictions p_i: `(pi : ∀ i, Vi i ⟶ Z)` and
  `(hpi : ∀ i, pi i = k i ≫ p)`. Exact; pi is determined by p and k, not an
  independently strengthened hypothesis.
- Each p_i an open immersion: `[∀ i, IsOpenImmersion (pi i)]`. Exact. The
  dependency def-weil-open-immersion records `AlgebraicGeometry.IsOpenImmersion`
  in Mathlib.AlgebraicGeometry.OpenImmersion, the locally-ringed-space open
  immersion notion. The imported Morphisms.OpenImmersion supplies the same
  notion, not a different one.
- A section exists with p composed after s equal to the identity:
  `∃ s : Z ⟶ V, s ≫ p = 𝟙 Z`. Exact, including order of composition and the
  existential quantifier after all objects and hypotheses.

Edge cases: n = 0 is allowed; hcop then makes V initial/empty and surjectivity
forces Z empty, where the section exists. Empty components, empty schemes and
n = 1 are allowed. No nonempty, field, characteristic, Noetherian, finiteness of
the schemes, or separatedness instance was added. The universe u is arbitrary;
all schemes in any finite configuration fit a common universe. The finite
index set needs no additional universe restriction. There is no module zero
object or characteristic parameter in this scheme statement. All variables,
including n and u, are explicitly bound.

Independent searches used different phrasing from the worker:

- LeanFinder via msearch.py: `finite covering by open immersions split
  epimorphism schemes`. Eight hits, including Scheme.OpenCover, sigmaOpenCover,
  cover joint-surjectivity and unrelated limit helpers. No section theorem.
- Loogle via msearch.py: `AlgebraicGeometry.IsFinite,
  CategoryTheory.IsSplitEpi`. Zero hits.
- LeanSearch via msearch.py: `A scheme morphism from finitely many disjoint
  clopen components, each mapping isomorphically onto an open subset, is split
  if finite and surjective`. Service unavailable (Internal Server Error);
  no no-match verdict is inferred from this failed service.
- rg over Mathlib/AlgebraicGeometry, the source WeilConjectures tree, and the
  repository lean/Sheaf tree for `section.*(clopen|coprod)`, `clopen.*section`,
  `exists_section_of_finite`, `IsSplitEpi`, plus section/split names in Finite,
  OpenImmersion, ClosedImmersion and Limits. No equivalent theorem. The source
  has split-epimorphism statements in unrelated categories, and the project has
  finite étale sheaf-section coproduct calculations, not this scheme section
  theorem. The proposed declaration name is absent from dag/lean_names_upstream.json.

Mismatch found: H8, the theorem docstring described the encoding but omitted
all four proof steps of the node. I added the closed covering images, the
nonempty-index clopen strata, local sections via inverse open immersions and
factorization, and gluing with its uniqueness equation, naming the same proof
nodes. I removed the unused universe declaration v. The theorem signature and
node statement are unchanged; lean.statement remains verbatim the file's
signature. There are no new nodes or dependency modules, no definitions (hollow
or otherwise), and the only proof is the required `by sorry`.

Validation: scompile.py compiled this single module on the server in 1.7 s,
exit code 0, with no warnings. The recorded signature was compared verbatim
with the Lean file; every Lean line is at most 100 characters.
