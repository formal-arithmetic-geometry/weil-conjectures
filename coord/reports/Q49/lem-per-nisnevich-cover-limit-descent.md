## Worker report

The module `Sheaf.AlgebraicGeometry.NisnevichCoverLimitDescent` states
`AlgebraicGeometry.exists_completelyDecomposedEtale_family_stage`, with the whole
proof `sorry`. No new definitions or dependency repairs are necessary. The item
node changes only in `lean`.

Source read: ILO, Travaux de Gabber, Exposé III Lemma 3.1.1 and its proof,
printed p. 38, in the supplied PDF (via pdftotext). Its finite closed filtration
with sections on successive differences is exactly the finite certificate used
by the DAG proof. A finite family is handled by its disjoint union.

Clause-by-clause correspondence:

- Directed system of commutative rings: `{I : Type u} [Preorder I]
  [IsDirected I (· ≤ ·)]` and `R : I ⥤ CommRingCat.{u}`. The index and rings share
  the size convention required for scheme limits; `i₀ : I` already makes the
  indexing set nonempty. A preorder does not impose antisymmetry absent in the node.
- Every stage is Noetherian: `[∀ i : I, IsNoetherianRing (R.obj i)]`.
- The specified direct limit ring is `c.pt` for `c : Cocone R` with
  `hc : IsColimit c`; `[IsNoetherianRing c.pt]` is the stated Noetherian-limit
  hypothesis. This is an arbitrary colimit cocone, with its actual structure maps,
  rather than an assumed extra comparison or a special presentation of the limit.
- The affine bases are `Spec (R.obj i₀)`, `Spec (R.obj i)`, and `Spec c.pt`.
  Their contravariant transition/projection maps are `Spec.map (R.map (homOfLE h))`
  and `Spec.map (c.ι.app i₀)`.
- The fixed finite-type scheme is `P₀ : Over (Spec (R.obj i₀))` with
  `[LocallyOfFiniteType P₀.hom] [QuasiCompact P₀.hom]`. These two properties are
  exactly finite type as recorded by def-weil-finite-type-morphism.
- The finitely many finite-type source models are `{J : Type v} [Finite J]`,
  `V₀ : J → Over (Spec (R.obj i₀))`, and the two corresponding property instances
  on every `(V₀ j).hom`.
- The specified arrows are `f₀ : ∀ j : J, V₀ j ⟶ P₀`. Being arrows in `Over`
  asserts precisely that they are over the same initial base.
- All base changes of objects and arrows are the actual Mathlib `Over.pullback`
  functor: its object is `Over.mk (pullback.snd model.hom baseMap)` and its arrow
  is the canonical map built with `pullback.lift` from the given arrow and the
  base projection. No arbitrary base-change map is supplied as a hypothesis.
- Étaleness of every limit arrow is `het : ∀ j, Etale (... .left)`.
- Complete decomposition at the limit is `hcd`: for every point `p` of the
  pulled-back target there exist `j` and a point `z` of the pulled-back source,
  with the arrow taking `z` to `p` and `IsIso (Scheme.Hom.residueFieldMap ... z)`.
  That map has source κ(f(z)); the preceding equality identifies it with κ(p).
  The condition refers to the canonical map, not an arbitrary field isomorphism.
- The conclusion chooses `i₁` and `h₀₁ : i₀ ≤ i₁`, then quantifies over every
  `i` and `h₁ : i₁ ≤ i`. At that stage the conjunction asserts étaleness for
  every member and the same pointwise canonical residue-field isomorphism
  condition for the whole family. The transition uses `h₀₁.trans h₁`.
- Empty cases are included: there is no `Nonempty J`, no nonempty target/source,
  no reducedness, separatedness, or quasi-excellence assumption.

All six statement-dependency records and the recorded signatures/docstrings
were read. Declarations used:

- def-weil-pbc-noetherian-ring: `IsNoetherianRing`,
  `Mathlib.RingTheory.Noetherian.Defs` (all ideals finitely generated).
- def-weil-affine-spectrum: `AlgebraicGeometry.Spec`, `Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`.
- def-weil-finite-type-morphism: `AlgebraicGeometry.LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, and
  `AlgebraicGeometry.QuasiCompact` (publicly exposed there through imports).
- def-pc-fibre-product: `CategoryTheory.Limits.pullback`, its projections and
  universal lift, `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`;
  used through `CategoryTheory.Over.pullback`,
  `Mathlib.CategoryTheory.Comma.Over.Pullback`.
- def-weil-etale-morphism: `AlgebraicGeometry.Etale`,
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- def-weil-residue-field: `AlgebraicGeometry.Scheme.residueField` and
  `AlgebraicGeometry.Scheme.Hom.residueFieldMap`,
  `Mathlib.AlgebraicGeometry.ResidueField`.

The available proof-dependency modules are imported without `public`: closed
and open immersions; residue-field isomorphisms; étale, closed and open descent;
finite-diagram lifting; joint-surjectivity descent; finite-presentation family
descent; affine inverse limits and base change of their cones. Mathlib proof
leaves use Noetherian, finite-presentation, coproduct and qcqs-permanence modules.
`lem-per-cd-finite-presentation-section-cover` has no Lean record or Mathlib
match yet and its import is omitted; its role is fully recorded in proof step 3.
This is a proof dependency, not a missing object needed to type this statement.
No omitted import closes an import cycle.

Edge checks before writing: if J is empty, hcd forces the limit target empty,
while the conclusion forces each sufficiently late target empty. This is the
empty-family case of the finite-certificate argument in steps 3 and 6, not an
extra assumption. If the limit target is empty but J is nonempty, het still
asks for étaleness of each limit arrow (whose source is then also empty), and
the same eventual assertion is retained. The zero ring and empty affine bases
are allowed. Noninjective ring transitions, a constant system, an initial stage
already satisfying the conclusion, and equivalent indices in a directed
preorder are all allowed. The finite family has an independent universe v,
so it is not restricted to a chosen `Fin n` or a chosen enumeration.

Searches made with the prescribed msearch wrapper:

- LeanFinder, “A finite completely decomposed etale covering descends along a
  filtered colimit of Noetherian rings”: 8 hits, including ring-level finite
  presentation/étale descent and finite products of étale algebras; none states
  complete decomposition of a scheme family at all later stages.
- Loogle, `AlgebraicGeometry.Etale, CategoryTheory.Limits.IsColimit`: 0 hits.
- grep, `Nisnevich|[Cc]ompletely[Dd]ecomposed|nisnevich`, Mathlib AlgebraicGeometry:
  0 hits.
- LeanSearch, “A finite completely decomposed etale covering descends to a stage
  of a directed limit of Noetherian rings”: 8 hits, principally ring-level étale
  descent and Noetherian affine criteria; no theorem for this node.
- Direct rg in Mathlib AlgebraicGeometry for `IsCompletelyDecomposed|completely
  decomposed|Nisnevich|nisnevich`: no match. Direct rg in WeilConjectures and
  Sheaf for `Nisnevich|nisnevich|[Cc]ompletely[Dd]ecomposed` and the node id:
  only `PrimeToEllAlterationTopology` has a named predicate. Its full signature
  and docstring were read: it is restricted to `Alt S`, hence does not accept
  the arbitrary possibly nonreduced finite-type models here. No new predicate
  is defined in this delivery; the node's explicit pointwise clauses are written
  inline, as in other landed family theorems.
- Direct rg for the chosen full declaration name and for potential names
  `nisnevich_cover|etale_family.*stage|completely_decomposed|nisnevichCover` in
  `dag/lean_names_upstream.json`, WeilConjectures and Sheaf: no existing theorem.

No statement correction, disputed assertion, or unusable statement dependency
was found. The old illustrative Sheaf CompactObject module has been withdrawn;
its node now records the upstream module, which was read for the current header
and source-docstring conventions.

## Second reading by Q49

Independent second reading (maintainer review service, 2026-10-24). The worker's
earlier "Second reading" was an author self-check. This section replaces it.

Node statement, item by item, against the Lean:

1. Directed system $(R_\alpha)$ of commutative Noetherian rings: `{I : Type u}
   [Preorder I] [IsDirected I (· ≤ ·)]`, `R : I ⥤ CommRingCat.{u}`,
   `[∀ i, IsNoetherianRing (R.obj i)]`. OK. `i₀ : I` makes I nonempty, as the node's
   "fix α₀" does. The index universe equals the ring universe, which is the
   convention of the cited toolkit (`Etale.exists_stage_of_inverseLimit` in
   EtaleInverseLimitDescent has `{I : Type u}` with `CommRingCat.{u}`). This is not
   a restriction of substance.
2. Noetherian direct limit R: `c : Cocone R`, `hc : IsColimit c`,
   `[IsNoetherianRing c.pt]`. OK. It is an arbitrary colimit cocone with its true
   structure maps.
3. $S_\alpha$, $S$ and the maps between them: `Spec (R.obj i)`, `Spec c.pt`,
   `Spec.map (R.map (homOfLE _))` and `Spec.map (c.ι.app i₀)` (def-weil-affine-spectrum). OK.
4. $P_{\alpha_0}$ of finite type over $S_{\alpha_0}$: `P₀ : Over (Spec (R.obj i₀))` with
   `LocallyOfFiniteType` and `QuasiCompact` on `P₀.hom`. This is exactly the
   def-weil-finite-type-morphism record. OK.
5. Finitely many $v_{j,\alpha_0}: V_{j,\alpha_0}\to P_{\alpha_0}$ with $V_j$ of finite type: `{J : Type v} [Finite J]`,
   `V₀ : J → Over _` with the same two instances, and `f₀ : ∀ j, V₀ j ⟶ P₀` as arrows over
   $S_{\alpha_0}$. These are the morphisms whose base changes the node takes. OK. Nonemptiness
   is not assumed.
6. Base changes to $S_\alpha$ and S: `Over.pullback` along the Spec maps, applied to objects
   and arrows. These are Mathlib's canonical `pullback.snd`/`pullback.lift` (def-pc-fibre-product). OK.
7. Hypothesis "each $v_j$ étale": `het`, with Mathlib `Etale` (def-weil-etale-morphism). OK.
8. Hypothesis "completely decomposed": `hcd` says ∀ p, ∃ j z with v_j z = p and
   `IsIso (Scheme.Hom.residueFieldMap v_j z)`. Here residueFieldMap : κ(v_j z) → κ(z),
   which is κ(p) → κ(z) by the equation. The map is canonical (def-weil-residue-field). OK.
9. Conclusion: `∃ i₁ (h₀₁ : i₀ ≤ i₁), ∀ i (h₁ : i₁ ≤ i)`, with both étaleness of every
   $v_{j,\alpha}$ and the same complete-decomposition clause at stage α
   (transition `homOfLE (h₀₁.trans h₁)`). The quantifier order and both clauses
   are the same as in the node: not weaker and not stronger. OK.

Edge cases. With J empty, hcd forces the limit target to be empty, and the
conclusion requires every late $P_\alpha$ to be empty. That is true, because qcqs
models of an empty limit are eventually empty, so the node's "empty family"
clause is covered. With the target empty and J nonempty, het and the conclusion
are vacuous for points and étaleness concerns empty sources. The zero ring and a
constant system are allowed. No reducedness, separatedness or excellence is
assumed.

Source. ILO, Travaux de Gabber, Exposé III, Lemme 3.1.1 (printed p. 38), which I
read in the PDF. A Nisnevich covering means étale plus a closed stratification
with sections on the strata. The conclusion follows from the permanence of models
(EGA IV 8.8.3, 8.10.5, 17.7.8). The node's finite-family and Noetherian form is
this lemma, and the Lean states the node.

Searches. rg in side-live lean/Sheaf and lean/WeilConjectures for
`ompletelyDecomposed` and the node id finds only PrimeToEllAlterationTopology
(restricted to `Alt S`, a different notion). Mathlib AlgebraicGeometry has no
"completely decomposed" statement. No duplicate.

Records. Against the base, only the item node's `lean` field changed.
`lean.statement` is verbatim the file's signature. The module and declaration
docstrings carry the source place and `(blueprint: lem-per-nisnevich-cover-limit-descent)`,
and the declaration docstring gives the 7 proof steps. The proof is `sorry` and
there are no definitions. All 9 project imports exist in side-live.

Mismatches found: none in the Lean or the node. Changed: this section only.

## Validation

Every compile uses the prescribed `scompile.py` wrapper, with module-mode headers
and explicit universes and `autoImplicit false`. The initial syntax error was
repaired before delivery. The corrected file compiled cleanly in sandbox mode
(10.8 s) and library mode (1.6 s), with no diagnostics. `deliver2.py --no-push`
returned OK: the generated commit passes preflight and per-file compilation.
The final push uses the same prescribed deliver2.py wrapper.
