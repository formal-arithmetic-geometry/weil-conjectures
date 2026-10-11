## Worker report

The module `lean/Sheaf/AlgebraicGeometry/DualNumberSchemePushout.lean` states
`AlgebraicGeometry.existsUnique_dualNumberScheme_extension`, with its sole proof `by sorry`.
No result is proved and no data is postponed. The node statement is unchanged.

Hypotheses and clauses, individually:

- The field K is `(K : Type u) [Field K]`.
- The dual numbers K[epsilon] are Mathlib's `DualNumber K`, exactly as def-sc-dual-numbers.
- The positive natural number n is `(n : ℕ) (hn : 1 ≤ n)`.
- The algebra A_n with basis 1, epsilon_1, ..., epsilon_n and all infinitesimal products zero
  is `TrivSqZeroExt K (Fin n → K)`. Its elements are pairs `(a,b)` and multiplication is
  `(a,b)(a',b') = (a*a', a • b' + a' • b)`. The constant basis vector is `(1,0)`; the
  infinitesimal basis vectors are `(0, Pi.single i 1)`. This represents exactly the specified
  algebra, including cross products equal to zero, rather than iterated dual numbers.
- Indices 1 through n are reindexed by `Fin n`; no index is omitted.
- The map j_i is the `Spec.map` of the ring hom underlying
  `TrivSqZeroExt.map (LinearMap.proj i : (Fin n → K) →ₗ[K] K)`.
  This sends `(a,b)` to `(a,b i)` in `DualNumber K`, fixes constants, sends epsilon_i to
  epsilon, and sends the other infinitesimals to zero.
- The common map c is `Spec.map (CommRingCat.ofHom
  (TrivSqZeroExt.fstHom K K K).toRingHom)`; it sends epsilon to zero on rings.
- Every scheme X is `(X : Scheme.{u})`, with no affineness, separation, or base structure
  hypothesis. The common universe imposes no size restriction: any field and scheme can
  be considered together in a sufficiently large universe.
- The n morphisms are `(θ : Fin n → (Spec (.of (DualNumber K)) ⟶ X))`.
- Equality of their restrictions is the pairwise equality `hθ : ∀ i j : Fin n, c ≫ θ i =
  c ≫ θ j`. Since n ≥ 1, this is exactly the common restriction in the statement.
- Existence and uniqueness of the arbitrary scheme morphism is `∃! Θ : Spec (.of A_n) ⟶ X`.
- Every required factorization is `∀ i : Fin n, Spec.map (...) ≫ Θ = θ i`.
  This is the explicitly stated wide pushout universal property; the final 'that is' clause
  is a reformulation of this same existence and uniqueness, not a second property.

Dependencies read and used:

- def-sc-dual-numbers: `DualNumber` and `DualNumber.eps`, Mathlib.Algebra.DualNumber,
  read the abbreviation and docstring at lines 43–51. `DualNumber K = TrivSqZeroExt K K`.
- def-weil-affine-spectrum: `AlgebraicGeometry.Spec`, `Spec.map`, Mathlib.AlgebraicGeometry.Scheme,
  read their full signatures and docstrings at lines 469–495.
- def-weil-pbc-scheme-conventions: its convention record has no declaration and explicitly
  fixes no independent notion. Used the recorded underlying Mathlib `Scheme`; no convention
  imposes additional properties here.
- Added def-sc-trivial-square-zero-extension to the item's stmt_deps, recording Mathlib's
  existing `TrivSqZeroExt`. Read its definition and docstring in
  Mathlib/Algebra/TrivSqZeroExt/Basic.lean, and the full `fstHom` and `map` signatures and
  definitions there. Read `LinearMap.proj` in Mathlib/LinearAlgebra/Pi.lean.

Edge cases: n=1 gives the identity coordinate projection on one-dimensional square-zero
algebras and unrestricted θ. n=2 reproduces exactly the source's pushout. n=0 is excluded
by the node and by hn; including it would incorrectly assert this same universal property
for Spec K. Characteristic 2 and arbitrary positive characteristic cause no change: all
infinitesimal products vanish, with no division used. For empty X there are no θ families
when n≥1, so the implication has no instance. Non-affine and non-separated X remain allowed.
There is no disputed statement or node correction.

Source: the local literature checkout has no varieties.tex, so read
https://stacks.math.columbia.edu/tag/0B2B directly. Its proof identifies the two-coordinate
square-zero algebra and uses the description of morphisms from local spectra in Tag 01J6.
The node's explicit finite extension uses that same argument; the complete three-step
natural-language proof is in the theorem's docstring, naming its DAG proof dependencies.

Searches performed with msearch.py (saved in searches.jsonl):

- leanfinder: 'Spec of a finite square zero extension of a field is the wide pushout of dual
  number schemes': eight hits on ring pushouts giving scheme pullbacks, not this assertion.
- loogle: 'TrivSqZeroExt.map, LinearMap.proj': no hits.
- leansearch: 'finite square zero algebra with basis one and n epsilon directions': service
  unavailable (Internal Server Error).
- grep in AlgebraicGeometry: 'TrivSqZeroExt|isPushout.*Spec|pushout.*dualNumber': one unrelated
  flat-rank hit; no theorem match.
- leanfinder: 'trivial square zero extension ring R direct sum M multiplication
  (r,m)(s,n)=(rs,r n+s m)': eight hits including `TrivSqZeroExt`, its ring structure and
  multiplication formula.
- grep in Algebra/TrivSqZeroExt: 'def map|def fstHom|structure TrivSqZeroExt': fstHom and map
  found in Basic.lean.
- leansearch: 'trivial square zero extension of a commutative ring by a module': service
  unavailable (Internal Server Error).
- loogle: 'TrivSqZeroExt': twelve hits including the existing general construction,
  projections, inclusions and additive structures.
- rg in WeilConjectures and lean/Sheaf for DualNumber, TrivSqZeroExt and dual-number pushouts:
  source has dual-number thickenings and derivative constructions, no finite pushout theorem.
- rg for the item id in WeilConjectures: no hits. tools/lean_names_upstream.py show for the
  item gave no recorded declaration. rg for the proposed full theorem name in Mathlib,
  WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json: no hits.
- DAG rg for TrivSqZeroExt and square-zero algebras: mentions in proof searches, no definition
  node for the general construction. tools/blueprint_refs.py search 'square-zero' returned
  one unrelated Conrad setup. Its ancestor command gives lem-sc-degree-2g1-very-ample.

Server compilation via scompile.py: clean, exit code 0, 1.7 seconds. All variables and
universes are explicit. The delivery dry run is the final mechanical validation.

## New nodes

`def-sc-trivial-square-zero-extension` records the existing general Mathlib construction
`TrivSqZeroExt`, with its square-zero multiplication, constants, infinitesimals, projection
and functorial map. The finite coordinate algebra is a direct application with
`M = Fin n → K`, using the existing map on linear coordinate projections; no private
specialization is defined. Source: Stacks Tag 0B2B's square-zero algebra and Mathlib's
construction docstring. The searches above found this exact general construction in
Mathlib and no DAG node carrying it. Thus the new node has `existing: true` and no module,
as required for a missing DAG notion already present in Mathlib. Its general algebra
construction also handles n=0; only the pushout theorem needs n≥1. No dependency module
or statement correction is needed.

## Second reading by H1

Independent comparison with the item JSON, its full Lean module, and every statement
 dependency. Verdict: the Lean says exactly what the node says; its signature and proof
placeholder need no change. The only repair is removing the stray backslash before the
apostrophe in "Mathlib's" in the new definition node's prose.

Source read independently: fetched the Stacks `varieties.tex` into the sandbox scratchpad
and read `section-tangent-spaces`, `definition-dual-numbers`, and `lemma-tangent-space`
(lines 2912–2990). Also read [Tag 0B2B](https://stacks.math.columbia.edu/tag/0B2B)
and [Tag 01J6](https://stacks.math.columbia.edu/tag/01J6). The surrounding section introduces
a morphism of schemes and a point, but the pushout calculation itself is in schemes and
uses only the field. It does not assume Noetherian, separated, finite type, algebraically
closed, or any characteristic. The node explicitly generalizes the source's two factors
to positive finite n. The tuple/local-stalk argument in its proof justifies this extension.

Objects, hypotheses and conclusions, matched individually:

1. Field K: `(K : Type u) [Field K]`. Exact, no extra field hypothesis.
2. Dual numbers K[epsilon]: `DualNumber K`. Read def-sc-dual-numbers and Mathlib's
   abbreviation `DualNumber R := TrivSqZeroExt R R` and `DualNumber.eps := inr 1`
   in Algebra/DualNumber.lean:46–51. Exact two-dimensional square-zero algebra.
3. Positive finite n: `(n : ℕ) (hn : 1 ≤ n)`. Exact, indices 1,...,n are represented
   bijectively by `Fin n`, with no separate nonempty or decidable-equality assumption.
4. Algebra A_n, basis and all infinitesimal products: `TrivSqZeroExt K (Fin n → K)`.
   Read Basic.lean:63–70 and its multiplication instances: pairs `(a,b)` have the
   multiplication in the node, basis `(1,0)` and `(0,Pi.single i 1)`. Exact; this is
   not the polynomial algebra with only the individual epsilon squares killed.
5. j_i: `Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map
   (LinearMap.proj i : (Fin n → K) →ₗ[K] K)).toRingHom)`. Read the complete `map`
   definition at Basic.lean:1066–1073 and its inl/inr and fst/snd formulas, and the
   definition `LinearMap.proj` at Pi.lean:87. Constants are fixed, coordinate i is
   kept, other basis vectors vanish. Contravariance gives exactly the indicated j_i.
6. c: `Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom)`.
   Read `fstHom` at Basic.lean:881–890. It is the constant-coefficient ring map
   D → K, hence c goes from Spec K to Spec D. Exact.
7. Arbitrary scheme X: `(X : Scheme.{u})`. Read the conventions node, which fixes
   no additional notion, and the underlying `Scheme` declaration in Scheme.lean:42.
   No affine, base-field, separation, finiteness, or nonemptiness constraint is added.
8. Arbitrary scheme maps theta_i: `(θ : Fin n → (Spec (.of (DualNumber K)) ⟶ X))`.
   These are scheme morphisms, with no requirement to be morphisms over K. Exact.
9. Common restriction: `hθ : ∀ i j : Fin n, c ≫ θ i = c ≫ θ j`, with c expanded
   as above. Pairwise equality equals the node's chain of equal restrictions for n≥1.
10. Unique scheme map Theta: `∃! Θ : Spec (.of (TrivSqZeroExt K (Fin n → K))) ⟶ X`.
    Existence and uniqueness are both present, after X, theta and its compatibility.
11. Every prescribed restriction: `∀ i : Fin n, j_i ≫ Θ = θ i`, with j_i expanded
    as above. Composition order is correct for Lean's left-to-right composition.
12. Wide pushout: clauses 9–11 are precisely its universal property. The cone's
    common-point composites agree because `fstHom` composed with every coordinate
    projection is the same constant projection. The final "that is" clause introduces
    no additional independent assertion requiring a second Lean conjunct.

Read def-weil-affine-spectrum and its recorded declarations `AlgebraicGeometry.Spec`
and `Spec.map` in Scheme.lean:470 and :479, including their types and functoriality.
Their orientation and category are exactly the ones required. No dependency module is
needed and no existing dependency is being replaced. The theorem docstring follows the
node's three proof steps: tuple ring description and locality; common point, compatible
stalk maps and existence via 01J6; restriction and joint injectivity for uniqueness.
Its two named proof dependencies are retained in the prose.

Edge cases: n=0 is excluded explicitly on both sides and would otherwise lose uniqueness
on Spec K; n=1 imposes only tautological compatibility and the single projection is an
isomorphism; n=2 is the source calculation. The zero ring is excluded by Field, exactly
as in the node. An empty X admits no theta family for positive n, so no exceptional case
is omitted. All characteristics, including 2, are allowed; there is no division by n.
K and X use a common arbitrary universe u, as required by Mathlib's Scheme category;
any pair can be placed in a larger common universe. There is no fixed small-universe
restriction. All variables are explicitly bound, with only the field structure an input
instance; the finite function module and central scalar instances are canonical.

Independent searches (different wording from the worker):

- msearch leanfinder: "gluing infinitesimal tangent vectors into a scheme from the spectrum
  of a finite square zero ring". Eight hits: ideal-sheaf gluing, FormallyUnramified,
  liftQuotient and homInfinitesimal, none with this universal property.
- msearch loogle: "TrivSqZeroExt.fstHom". Three hits: fstHom, its evaluation and
  fstHom_comp_map; these confirm the existing projections, not a pushout theorem.
- msearch leansearch: "split extension ring by an ideal whose square is zero".
  Service unavailable (Internal Server Error), recorded without a mathematical verdict.
- rg for amalg, IsPushout/isPushout, square-zero and TrivSqZeroExt in Mathlib's
  AlgebraicGeometry, upstream WeilConjectures/AlgebraicGeometry, and project lean/Sheaf.
  Hits concern scheme pullbacks/ring pushouts or dual-number sheaf constructions, not
  this finite gluing theorem. Read the matching upstream DualNumbers.lean passages:
  they use the same existing Mathlib projections and define dual-number thickenings;
  they do not state this theorem.
- rg throughout Mathlib, WeilConjectures and project Sheaf for the proposed theorem
  name and combinations of Fin and TrivSqZeroExt: no hits.
- DAG searches for trivial/split square-zero extension and module square-zero algebras:
  no node carrying the general construction; the dual-number node carries only R ⊕ R.

The new node def-sc-trivial-square-zero-extension was read independently as a definition
node. Its general construction is genuinely already Mathlib's TrivSqZeroExt, recorded
with existing:true and no module, and absent as a general DAG notion. Its source includes
both the Stacks calculation it serves and Mathlib's general construction docstring.
The product, addition, multiplication, unit, constants, infinitesimals and projections
match the existing definitions, and its finite specialization matches the Stacks algebra.
No private or hollow definition is introduced. Checked its complete fields: definition,
split, empty proof/proof_deps, null proof_origin/mathlib_match, searches of all three kinds,
created worker/item/date/group, matching chapter/unit, null blueprint.is, the full ancestor
chain and same_as list, and both audit states none. The item cites the new node. No source
or node statement correction is necessary; there are no correction citers to check.

The sole theorem has only `by sorry`; no theorem is proved. Imports are all used,
namespace and topic path follow the contract, and module and declaration docstrings
carry the source and blueprint marker. Verified line lengths ≤100 and exact verbatim
agreement of the item's lean.statement with the declaration signature. Compilation and
preflight are run after this reading before delivery.
