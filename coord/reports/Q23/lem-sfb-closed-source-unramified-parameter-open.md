## Worker report

The module `Sheaf.AlgebraicGeometry.ClosedSourceUnramifiedParameterOpen` states
`AlgebraicGeometry.exists_closedSourceUnramifiedParameterOpen` with `sorry`, and defines
no new notion. Source checked directly: `literature/stacks-project/spaces-more-morphisms.tex`,
`lemma-where-unramified` (Tag 05X8), including its proof's specified complement formula.
The scheme specialization and the local-finite-type conclusion are the node's statement.

Hypotheses and clauses, in order:

- The schemes A, B, C are `{A B C : Scheme.{u}}`; the three morphisms are
  `(p : A ⟶ B) (q : C ⟶ B) (f : A ⟶ C)`.
- The triangle condition q ∘ f = p is `(hf : f ≫ q = p)`.
- Local finite type of p is `[LocallyOfFiniteType p]`.
- Being closed on underlying spaces is `(hp : IsClosedMap p)`, using the underlying
  function of the scheme morphism. This is closedness, without universal closedness.
- The first conclusion is `LocallyOfFiniteType f`.
- The union U_f is written inline as
  `{z : A | ∃ O : A.Opens, z ∈ O ∧ IsUnramified (O.ι ≫ f)}`,
  exactly the union of the unramified source opens. This is the unfolding of the
  existing locus definition, without introducing another declaration.
- `∃ B₀ : B.Opens` supplies openness and the canonical open subscheme `B₀.toScheme`.
  Its specified underlying subset is the equality
  `(B₀ : Set B) =
  (p '' {z : A | ∃ O : A.Opens, z ∈ O ∧ IsUnramified (O.ι ≫ f)}ᶜ)ᶜ`.
- Every test scheme and morphism are `∀ (T : Scheme.{u}) (h : T ⟶ B)`.
- The induced morphism f_T is `pullback.map p h q h f (𝟙 T) (𝟙 B) ... ...`.
  Its two square equations follow explicitly from hf and the category identity laws;
  no arbitrary map is substituted for the induced morphism.
- Its unramifiedness is `IsUnramified` of this map, and the required `↔` has right
  side `∃ l : T ⟶ B₀.toScheme, l ≫ B₀.ι = h`, exactly factorization through the
  open inclusion. Uniqueness is automatic for an open immersion, and is not an
  extra conclusion here.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`, `locallyOfFiniteType_of_comp`,
  `locallyOfFiniteType_isStableUnderBaseChange` (the latter two are proof inputs).
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`,
  `IsOpenImmersion.lift`, `lift_fac`, `lift_uniq` (factorization proof inputs).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, `pullback.map`; scheme pullbacks come from
  `Mathlib.AlgebraicGeometry.Pullbacks`.
- `Sheaf.AlgebraicGeometry.UnramifiedMorphism`: `AlgebraicGeometry.IsUnramified`,
  the conjunction of local finite type and open-immersion diagonal.
- `Sheaf.AlgebraicGeometry.UnramifiedLocusBaseChange`:
  `AlgebraicGeometry.unramifiedLocus`, `unramifiedLocus_baseChange` (proof-only
  import; the set definition is unfolded in the statement).
- `Mathlib.AlgebraicGeometry.PullbackCarrier`: `Scheme.Pullback.carrierEquiv`,
  `carrierEquiv_symm_fst`, `carrierEquiv_symm_snd` (proof-only import).

The original five definition nodes are the entire stmt_deps list. The theorem node
`lem-trf-unramified-locus-base-change` remains in proof_deps only, and its module is
now a plain proof import. All recorded proof-dependency modules are imported; public
statement imports also cover any overlapping proof dependency. No new node or dependency
repair is needed. The informal statement and proof are unchanged, and no statement
correction or disputed statement is required.

Edge cases checked mathematically: A empty makes its bad locus and image empty, so B₀
is all of B and every induced empty-source morphism is unramified. T empty always factors
and its induced morphism is unramified. An everywhere unramified f gives B₀ = B. A
ramified source over a field gives B₀ empty; a nonempty test scheme has points above the
bad source point by the nonzero residue-field tensor product argument. No reducedness,
Noetherian, properness, separatedness or finite-presentation assumption is present.
All schemes use one arbitrary universe u, as do the established scheme pullback APIs;
a common larger universe accommodates any chosen collection of test schemes.

Searches on 2026-10-24 (msearch.py; exact records in sandbox searches.jsonl):

- LeanFinder: “An open subset of the base represents unramified base changes when the
  source morphism is locally of finite type and a closed map.” Eight results: formal
  unramified base-change stability, affine unramified locus openness, diagonal and
  affine criteria. None states the parameter-open assertion.
- Loogle: `AlgebraicGeometry.IsUnramified, IsClosedMap`: zero results, unknown identifier
  `AlgebraicGeometry.IsUnramified` in the search service. The declaration is supplied
  by the project's recorded module and was read there.
- Mathlib grep: `unramifiedLocus|unramified.*parameter|where.*unramified` under
  AlgebraicGeometry: zero results.
- LeanSearch: “A closed locally finite type source over a base gives an open of the
  base representing unramified base changes.” Eight results concerning affine loci,
  base change and diagonals; none is the parameter-open theorem.
- Direct rg searches of lean/WeilConjectures and lean/Sheaf for unramified loci and
  parameter-open names found the existing scheme locus module and the parent
  `UniversalUnramifiedRadicialOpen`, which adds a radicial condition and a second
  closedness hypothesis. It does not state this item. The upstream occurrence in
  Curve/FiniteMapToLine uses the affine ring locus only. The prescribed recursive
  search for this item id in lean/WeilConjectures returned no result.
- Direct name collision search for `exists_closedSourceUnramifiedParameterOpen` in
  Mathlib, WeilConjectures, Sheaf and dag/lean_names_upstream.json returned no result.

Validation: scompile.py compiled the repaired module in sandbox mode (1.6 s) and
at its library module name (1.9 s), with no errors or unexpected warnings.

## Second reading by Q23

Self-check only; no independent worker was started, as the dispatcher brief forbids it.
Reopened the node and the delivered signature: the triangle, both hypotheses, the local
finite type conclusion, the exact complement-of-image formula, the open subscheme and
all test morphisms are present. In particular the statement has no closedness assumption
on q and no second closedness assumption on the relative self-product. The induced map
uses p,h and q,h in that order, giving A ×_B T → C ×_B T. The right side factors h
through B₀ itself. The locus is now inline and stmt_deps has the five original definition
nodes. No mismatch in the mathematical statement was found.


## Repair of returned head 9503fbb98f0c

H2: The return rejected the added theorem node in stmt_deps. Applied the reviewer’s
second permitted correction: restore the five original statement dependencies and inline
`{z : A | ∃ O : A.Opens, z ∈ O ∧ IsUnramified (O.ι ≫ f)}` in the complement formula.
The locus theorem stays in proof_deps. Its module import is now plain, because the
signature no longer refers to any declaration from that module. The inline expression
is exactly the body of the existing locus definition, so the mathematical assertion is
unchanged. Updated lean.statement verbatim and removed the superseded dependency claim
from this report. The sandbox node was regenerated from current main, preserving all
main fields except lean, instead of carrying forward the rejected stmt_deps delta.
The returned signature and retained sandbox agreed before this repair; current main
still has the original five statement dependencies and no lean attachment.
