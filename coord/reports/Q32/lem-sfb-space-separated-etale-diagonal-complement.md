## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceSeparatedEtaleDiagonalComplement` states
`AlgebraicGeometry.AlgebraicSpace.separated_etale_diagonal_clopen_and_isIso`.
Its only proof is `sorry`. No Lean definition or auxiliary theorem is introduced.
The repair adds a definition-node record for two already existing definitions.
The node's mathematical statement and accepted six-step split are unchanged.

Hypotheses and clauses, matched individually:

- The base scheme is `{S : Scheme.{u}}`, with an explicit universe `u` and
  `set_option autoImplicit false`. `U X : AlgebraicSpace S` are the recorded full
  subcategory of fppf sheaves with representable diagonal and a surjective étale atlas;
  `a : U ⟶ X` is its natural-transformation morphism.
- Separatedness is `hsep : IsSeparatedPresheafMap a.hom.hom`, exactly the existing
  scheme-test closed-immersion condition on `diagonalPresheafMap a.hom.hom`.
- Étaleness is `het : IsEtale a.hom.hom`, the dependency's representable scheme-test
  predicate, using Mathlib's `Etale p.left` on each represented projection.
- The diagonal is the existing `diagonalPresheafMap`, whose data are the canonical
  pullback lift of two identities. Its codomain is the presheaf fibre product.
  The corresponding sheaf fibre product is an algebraic space by
  `fibreProduct_isAlgebraicSpace`; evaluating its underlying presheaf gives the same
  pairs of matching sections. No arbitrary self-product or diagonal is supplied.
- The first conjunct asserts that every scheme test of that diagonal is an open
  immersion, through `IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left)`.
- The second conjunct asserts that every scheme test is a closed immersion, through
  `IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)`.
- The third conjunct supplies an actual `C : AlgebraicSpace S` and an inclusion
  `j : C.obj.obj ⟶ Limits.pullback a.hom.hom a.hom.hom`. The two immersion predicates
  make it open and closed on scheme tests. Its exact complement condition is
  `pointImage j = (pointImage (diagonalPresheafMap a.hom.hom))ᶜ`, on the dependency's
  field-valued point classes. Open immersions identify the actual subspace, including
  its induced structure, and the point-image equality specifies precisely its complement.
- The last conjunct is conditional, so none of its extra hypotheses is imposed on the
  unconditional diagonal/complement assertions. Surjectivity on point classes is
  `pointImage a.hom.hom = Set.univ`, not sectionwise surjectivity on every scheme.
- Each geometric point is quantified as `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]`,
  a structure map `s : Spec (CommRingCat.of Ω) ⟶ S`, and
  `x : yoneda.obj (Over.mk s) ⟶ X.obj.obj`. Yoneda identifies this with a map from
  the field spectrum to `X`. All such fields and maps in the fixed site universe are
  quantified; there is no independently smaller field universe.
- Its geometric fibre is the actual sheaf pullback, written on underlying presheaves
  as `Limits.pullback a.hom.hom x`. Exactly one underlying point is
  `∃ p : Point (Limits.pullback a.hom.hom x), ∀ q, q = p`.
  This uses point classes of the fibre, not a fibre of the map between point sets,
  and not uniqueness of field-valued sections as an extra assumption.
- The conclusion is `IsIso a` in the category of algebraic spaces over `S`.
- The preliminary sentences about quasi-compactness, quasi-separatedness and integral
  maps fix terminology for this family of nodes. This node assumes none of those
  properties and makes no claim about an integral map. Accordingly no such extra
  hypotheses occur in the Lean statement. The atlas topology is the recorded
  `pointTopologicalSpace`; all open/closed immersion conditions use scheme tests.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, scheme morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsEtale`, `AlgebraicSpace.IsRepresentableWith`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `AlgebraicSpace.pointImage`, `AlgebraicSpace.pointTopologicalSpace`; its recorded
  point-class dependency supplies `Point`, `PointRepresentative` and `schemePointMap`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicSpace.fibreProduct_isAlgebraicSpace` (sheaf pullback closure).
- `Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`:
  `AlgebraicSpace.diagonalPresheafMap`, `AlgebraicSpace.IsSeparatedPresheafMap`.
  These two definitions are now owned by the new definition node
  `def-sfb-presheaf-map-separated-diagonal`, recorded with `existing: true`.
  This replaces the theorem node `lem-trf-space-qc-separated-etale-local` in
  `stmt_deps`; no theorem is cited just to obtain these plain definitions.
  No declaration is duplicated or moved. The item also directly cites
  `def-a1-algebraic-space-point-classes` for `Point`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, with `Field` and `Spec`
  giving the inline geometric-point convention. Read also
  `Scheme.SpecToEquivOfField` in `Mathlib.AlgebraicGeometry.ResidueField`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- The integral/finite convention uses the existing Mathlib `IsIntegralHom`/`IsFinite`
  when needed, but neither occurs in this assertion. Their full signatures were read.
- Proof-only imports are `ChartwiseEtalePermanence` (`chartwise_etale_permanence`),
  `AlgebraicSpaceRepresentableEtaleSchemeTests` (`representable_etale_scheme_tests`),
  `AlgebraicSpaceEtaleOpenImage` (`openSubspace_points_orderIso`, `etale_open_image`),
  `UnramifiedFieldFibreDecomposition`
  (`unramified_iff_exists_iso_coproduct_spec_finite_separable`) and Mathlib's
  `IsAlgClosed.AlgebraicClosure` (`AlgebraicClosure`). The proof nodes
  `lem-sfb-space-diagonal-scheme-tests`, `lem-sfb-space-etale-monomorphism-open` and
  `lem-a1-space-point-open-calculus` currently have no recorded modules, so none can
  be imported for them. They remain in the unchanged proof plan.

Edge cases checked before writing:

- Empty target and source: geometric-point quantification is vacuous, point-image
  surjectivity holds, and the map is an isomorphism. No `Nonempty` hypothesis on
  either space is added; the complement can be empty.
- Empty source and nonempty target: the unconditional diagonal assertions hold,
  whereas point surjectivity and singleton fibres fail.
- Identity: its diagonal is an isomorphism, and the complementary space is empty.
- A proper open inclusion: the diagonal assertion still holds; the degree-one
  criterion requires surjectivity and nonempty singleton fibres at every point.
- A two-copy étale cover has two geometric-fibre points, so is excluded by the
  singleton hypothesis. A nontrivial finite separable field extension is likewise
  excluded after passage to an algebraic closure, even though its ordinary point
  map can be bijective. Nonreduced test schemes are not excluded.
- No quasi-compactness, quasi-separatedness, characteristic, finite-presentation
  bound beyond representable étaleness, or index-set restriction is imposed.

Sources read: `literature/stacks-project/spaces-morphisms.tex`,
`lemma-properties-diagonal` (03HK), `lemma-diagonal-unramified-morphism` (05W1),
`lemma-universally-injective` (040X), and
`lemma-etale-universally-injective-open` (05W5). These confirm that 03HK supplies
representability/monicity, while openness comes from 05W1. The node's full six-step
proof is included in the theorem docstring. No statement correction is required.

Searches performed:

- `msearch.py ... leanfinder "A separated etale map of algebraic spaces has clopen
  diagonal and is an isomorphism if surjective with singleton geometric fibres"`:
  eight results, all scheme-only (`IsEtale`, formally unramified diagonal openness,
  `isSeparated_iff`, etc.); no matching algebraic-space theorem.
- `msearch.py ... loogle "AlgebraicGeometry.Etale, CategoryTheory.IsIso"`:
  zero results.
- `msearch.py ... grep "AlgebraicSpace|[Ee]tale.*[Dd]iagonal" AlgebraicGeometry`:
  six hits in Mathlib Etale/WeaklyEtale, none a matching algebraic-space statement.
- `msearch.py ... leansearch "separated etale algebraic space morphism clopen
  diagonal singleton geometric fibres isomorphism"`: eight results on scheme
  separated diagonals and topological separated maps; no matching theorem.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for algebraic spaces, separatedness,
  diagonal complements, singleton geometric fibres, and the proposed declaration:
  found the existing interfaces cited above, but no matching theorem.
- Searched the item id in both Lean roots: no existing declaration.

Validation: prescribed `scompile.py` compiled both sandbox and library module forms
cleanly (2.1 s and 2.0 s); only the expected postponed theorem is introduced.
No disputed statement or unresolved node fault.

## New nodes

`def-sfb-presheaf-map-separated-diagonal` records, with `existing: true`,
`AlgebraicGeometry.AlgebraicSpace.diagonalPresheafMap` and
`AlgebraicGeometry.AlgebraicSpace.IsSeparatedPresheafMap` in
`Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal` (lines 49 and 56). The first
is the canonical map to the presheaf pullback with both projections identity;
the second says all scheme tests of that map are represented by closed
immersions. Source: Stacks `spaces-morphisms.tex`, 03HL(1), 03HK and 03KM.
The source defines separated algebraic-space maps by their closed diagonal;
the existing presheaf interface spells out exactly these scheme tests.
Its explicit S, G, F, g and universe u give every parameter in the new node.
No theorem or proof is required, and no Lean file is supplied for this node.

Fresh searches: LeanSearch for "A morphism of presheaves on schemes is
separated if its diagonal is representable by closed immersions" returned
eight scheme-only declarations; Loogle for
`CategoryTheory.Limits.pullback.lift, AlgebraicGeometry.IsClosedImmersion`
returned one scheme-only result; Mathlib grep for
`diagonalPresheafMap|IsSeparatedPresheafMap|isSeparated_iff` returned five
scheme separation hits. The raw wrapper results are in `mathlib_searches`.
Project grep found the exact definitions only in the existing Sheaf module,
with other occurrences being uses and no WeilConjectures occurrences.
DAG grep and inspection of every declaration/declarations record found no
owning definition node. `blueprint_refs.py search "separated diagonal"`
returned zero matches; `ancestor` returned None, preserved in the new node.
Thus this is a missing DAG owner for existing declarations, not a new notion
or a second definition. The item directly cites the new definition node.

## Second reading by Q32

The Q32 repair worker performed a fresh second reading of the retained packet,
opening the node, the full Lean statement and proof docstring, the new definition
node, both existing definitions and their docstrings (also checked with
`scompile.py --source Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`), and
`Point`, `pointImage`, `IsEtale`, and `IsRepresentableWith`. This is a second
reading in this repair session; no additional agent was started, as the
explicit dispatcher instruction forbids that.

Two record/report mismatches were found and repaired. The theorem dependency
only provided plain definitions: it is replaced by the definition node above,
with both existing names recorded. The old second-reading section documented
no actual reading: it is replaced by this completed check. The advisory direct
point-class citation is also added. No change to the Lean module is needed.

Clause-by-clause rereading: S is a scheme in u; U and X are algebraic spaces
over S; a is their morphism; hsep unfolds precisely to representability of its
canonical diagonal by closed immersions; het is representable étaleness on
scheme tests. The first two conjuncts separately assert open and closed
immersion of that diagonal. The existential C and j are an algebraic space
and a representable open-and-closed inclusion into its actual self-pullback;
pointImage equality fixes exactly the complementary subspace. The final
implication assumes point surjectivity and exactly one point of every fibre
at every algebraically closed Ω : Type u, with every base map and every
geometric point x quantified; its conclusion is IsIso a. This is a fibre
point condition, not injectivity of the ordinary point map. Yoneda converts
x to the required field-spectrum map. Every universe/variable is bound,
and autoImplicit is false. Only the named theorem proof is sorry; the reused
definitions have real data, with no choice of an unspecified object.

The new definition node was reread against both existing bodies: pullback.lift
of identity maps has the two required projections, and IsRepresentableWith
expands to a represented pullback square and a closed scheme projection,
exactly its statement. Its dependencies are exactly its bracket citations.
It introduces no quasi-compactness assumption or locality theorem.

The source definitions and Stacks 05W1(1), 03HK, 05W5, and 040X were reread.
An empty map to the empty space and the identity allow empty complements;
an empty source over a nonempty target fails the final hypotheses. A proper
open inclusion satisfies the unconditional clauses and fails surjectivity;
X ⊔ X → X fails singleton fibres. A nontrivial finite separable field
extension has multiple geometric fibre points and is excluded; a nontrivial
purely inseparable extension fails étaleness. No hidden quasi-compactness or
separatedness condition on the base occurs. The preliminary terminology
about integral/quasi-compact/quasi-separated maps introduces no assertion
requiring additional Lean clauses. The proof-only imports implement the
recorded future proof plan under stage-2 rule 7; the present statement uses
none of their theorem proofs. The hypothesis/clause mapping in the worker
report agrees with this reading. No mathematical mismatch, disputed statement,
or statement correction remains.

Repair validation: `scompile.py` compiled the retained module in sandbox and
library forms cleanly (2.1 s and 2.0 s). The first repaired dry run required
`import_flags` on the new node; the current server schema is followed with
`import_flags: []`. No mathematical or Lean change resulted.
