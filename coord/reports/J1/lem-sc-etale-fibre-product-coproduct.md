## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleFibreProductCoproduct` states
`AlgebraicGeometry.etale_fibre_product_coproduct`, with its only proof `sorry`.
No definitions, new nodes, dependency modules, or statement corrections are needed.

Clause-by-clause correspondence:

- A scheme X is the explicit binder `X : Scheme.{u}`.
- The finite family is `I : Type v`, `[Finite I]`, `U : I → Scheme.{u}`,
  and `u : ∀ i : I, U i ⟶ X`. No etaleness, affineness, nonemptiness,
  separatedness, or extra hypothesis is imposed.
- Its disjoint union with induced map is `V := Over.mk (Sigma.desc u)`;
  its underlying scheme is exactly the chosen Scheme coproduct `∐ U`.
  `A i := Over.mk (u i)` is the corresponding scheme over X.
- Every integer p ≥ 0 is represented by `p : ℕ`. The p+1-fold fibre
  product of V is `Q p := ∏ᶜ fun _ : Fin (p + 1) => V` in `Over X`.
- Each indexed fibre product is `P p J := ∏ᶜ fun r => A (J r)` for
  `J : Fin (p + 1) → I`. This is precisely the tuple index set I^(p+1).
- The isomorphisms over X are `e : ∀ p : ℕ, (∐ P p) ≅ Q p`.
  An isomorphism in Over X is an isomorphism of schemes commuting with
  their structure morphisms. Orientation is the inverse of the display
  in the node, as in its proof's canonical morphism phi_p.
- Canonical means that on summand J its projection to the r-th copy of V
  is the projection to U_(J r) followed by that scheme's coprojection.
  The first conjunct is exactly this equation, with
  `c i := Over.homMk (Sigma.ι U i) (Sigma.ι_desc u i)`.
  This specifies the isomorphism uniquely by product and coproduct
  universality; it adds no mathematical hypothesis or stronger conclusion.
- The omitted-factor clause is the second conjunct. It uses all `p : ℕ`,
  all tuples of length p+2, and every `r : Fin (p + 2)`. Thus this covers
  exactly all omissions from lengths at least two, as in the node's proof.
  `r.succAbove : Fin (p + 1) → Fin (p + 2)` retains the other indices in
  order. The left `Pi.lift` omits factor r in Q; the right `Pi.lift` omits
  it in the indexed fibre product. The coprojection on the right goes to
  the summand `fun s => J (r.succAbove s)`, followed by `e p`.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  Mathlib.AlgebraicGeometry.Scheme (imported through Limits).
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, its projections,
  and `pullback.lift`, Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback.
  Iteration is expressed by Mathlib's existing finite products in Over X,
  rather than a private recursive definition. The binary construction in
  Mathlib.CategoryTheory.Limits.Constructions.Over.Products uses those same
  pullbacks, via `pullbackConeEquivBinaryFan`; its finite-product and
  finite-limit instances are imported through Constructions.Over.Basic.
  The finite product and a left-associated iterated pullback have the same
  universal property and are canonically isomorphic with identical projections.
  No bracketing is part of the node's statement.
- `lem-weil-pbc-scheme-coproduct-family`: the Mathlib Scheme coproduct
  instance in Mathlib.AlgebraicGeometry.Limits, `sigmaOpenCover`, and
  `disjoint_opensRange_sigmaι` were read in full. Its universal property is
  used via `Sigma.desc`, `Sigma.ι`, and `Sigma.ι_desc` from
  Mathlib.CategoryTheory.Limits.Shapes.Products.
  Mathlib.CategoryTheory.Limits.Over supplies coproducts in Over X by
  creation under its forgetful functor, so their underlying schemes are
  the Scheme coproducts up to the unique coprojection-compatible isomorphism.

Edge cases checked mathematically before writing: I empty gives an empty
coproduct and empty positive powers on both sides (there are no positive-length
empty tuples); p=0 gives one-factor products and the canonical identification
with V. A singleton I gives the corresponding indexed fibre product itself.
Empty schemes among the U_i and empty X remain allowed. All omitted positions,
including the first and last, are covered by succAbove. No characteristic is
assumed. Scheme universe u and index universe v are independent: finite types
are small, so `[Finite I]` does not impose a universe-size restriction. The
simultaneous family e is equivalent to existence at every p because its
canonical component equations uniquely determine each e.

Source checked: the local Stacks source was not present. Read the official
pages https://stacks.math.columbia.edu/tag/01JB (gluing mapping properties),
https://stacks.math.columbia.edu/tag/01JC (gluing schemes), and
https://stacks.math.columbia.edu/tag/01JO (Section 26.17, fibre-product universal
property). The theorem follows these constructions and the four proof steps
in the node; those steps are recorded in its declaration docstring.

Searches for an existing statement (via /home/ubuntu/weil-launcher/msearch.py):

- LeanSearch: "iterated fibre product of coproducts of schemes is coproduct
  over tuples with projections": service unavailable, Internal Server Error;
  no verdict drawn from its unavailability.
- LeanFinder: "iterated fibre products of a finite coproduct of schemes
  distribute over tuples and commute with omitted factor projections": eight
  hits, concerning scheme coproduct presheaf maps and Spec coproduct maps;
  none states the iterated isomorphisms with omission compatibility.
- Loogle: `CategoryTheory.Limits.Pi.lift, CategoryTheory.Limits.Sigma.desc`:
  three hits, concerning biproducts and opposite products, no exact statement.
- Mathlib grep through msearch: `(pullback|prod).*(coprod|sigma)|
  (coprod|sigma).*(pullback|prod)` in CategoryTheory/Limits: 25 hits including
  FormalCoproduct/Cech and independent product/coproduct results. Formal
  coproduct powers are not this Scheme distribution theorem.
- Direct rg in Mathlib CategoryTheory/Extensive found binary pullback
  distribution and universality of finite coproducts, supporting proof
  inputs but no exact iterated Scheme statement with omission compatibility.
- Direct rg in WeilConjectures/AlgebraicGeometry and CategoryTheory found
  various fibre-product constructions and products in Over (notably
  ChowLemma/Graph), but no matching declaration. Search of the item id in
  WeilConjectures returned no occurrence.
- Direct rg of `etale_fibre_product_coproduct|fibre.product.*coproduct|
  coproduct.*fibre.product` in dag/lean_names_upstream.json,
  WeilConjectures, and lean/Sheaf found only unrelated finite-Galois and
  fundamental-group comments. No name clash or equivalent existing statement.

Server compilation through scompile.py passed cleanly in 2.2 seconds, with
no errors and no warnings. No local compilation or manual git commands were run.

## Second reading by J1

I independently opened the node copy, its Lean module, all three statement
 dependency nodes and their Mathlib declarations. Verdict: the Lean states the
node exactly, through the standard universal-property identification of finite
products in `Over X` with iterated fibre products. No mathematical mismatch was
found; no Lean or node change was needed. This reading adds this report section.
There are no new nodes, dependency modules, or statement corrections to review.

Source reading: the repository has no local Stacks `.tex`. I downloaded the
official Stacks project's `schemes.tex` from
https://raw.githubusercontent.com/stacks/stacks-project/master/schemes.tex into
`scratchpad/schemes.tex` (not delivered), and read the setup of Section 26.14,
`lemma-glue` (01JB), `lemma-glue-schemes` (01JC), and the opening of Section
26.17 including `definition-fibre-product`. The gluing setup assumes locally
ringed spaces and open gluing data; taking diagonal overlaps to be the whole
piece and off-diagonal overlaps empty gives the disjoint coproduct. The second
lemma assumes the pieces are schemes. Section 26.17 introduces arbitrary
morphisms of schemes to a common target. Neither source imposes etaleness,
affineness, finiteness of type, Noetherianness, separatedness, a field, or a
characteristic. Thus the finite-family hypothesis in the node is sufficient;
no further ambient hypothesis is missing from the Lean.

Object/hypothesis/conclusion list, matched independently:

1. Scheme X: `X : Scheme.{u}`. PASS. Mathlib's `Scheme` at Scheme.lean:42
   is a locally ringed space locally isomorphic to spectra, and `Scheme.Hom`
   at line 74 is a morphism of locally ringed spaces. These are precisely
   the dependency `def-pc-scheme` declarations, not an affine specialization.
2. A finite indexing set and schemes U_i with morphisms u_i to X:
   `I : Type v`, `[Finite I]`, `U : I → Scheme.{u}` and
   `u : ∀ i : I, U i ⟶ X`. PASS. Finite is a property, with no chosen
   enumeration, decidable equality or nonemptiness as an extra input.
3. Disjoint coproduct V with induced map to X:
   `V := Over.mk (Sigma.desc u)`, whose underlying scheme is `∐ U`;
   `A i := Over.mk (u i)` and
   `c i := Over.homMk (Sigma.ι U i) (Sigma.ι_desc u i)`. PASS.
   I read Limits.lean:187-245: coproduct existence, disjointness of the
   coprojections' open images, and `sigmaOpenCover`. I also read
   `Sigma.desc`, `Sigma.ι_desc`, and `Sigma.hom_ext`. These are the
   declarations recorded by `lem-weil-pbc-scheme-coproduct-family`.
4. Every integer p >= 0 and exactly p+1 factors:
   `p : ℕ`, `Q p := ∏ᶜ fun _ : Fin (p + 1) => V`. PASS.
5. Every ordered tuple in I^(p+1), and its indexed fibre product:
   `J : Fin (p + 1) → I`, `P p J := ∏ᶜ fun r => A (J r)`.
   PASS. I read `pullback`, `pullback.fst`, `pullback.snd`, and
   `pullback.lift` in Shapes/Pullback/HasPullback.lean, the match for
   `def-pc-fibre-product`; Constructions/Over/Products.lean gives the cone
   equivalence and `prodLeftIsoPullback` with both projection equations.
   Its arbitrary-product cone equivalence identifies products in the slice
   with wide pullbacks. Hence this expresses the same chosen universal
   object up to its unique projection-compatible isomorphism, including the
   node proof's left-associated construction; it is no private definition.
6. Canonical isomorphisms of schemes over X:
   `∃ e : ∀ p : ℕ, (∐ P p) ≅ Q p` and the first conjunct. PASS.
   Reversing the displayed isomorphism is equivalent, and agrees with
   phi_p in proof step 1. The equations after each `Sigma.ι (P p) J`
   and `Pi.π ... r` say exactly that phi_J has projections
   `Pi.π ... r ≫ c (J r)`. Product and coproduct uniqueness determine
   e uniquely; simultaneous existence neither strengthens nor weakens the
   per-degree canonical existence. Limits/Over.lean:39-55 constructs
   coproducts in the slice and makes its forgetful functor create colimits,
   so `∐ P p` is the required scheme coproduct with its induced map to X.
7. Every omitted-factor projection restricts to its corresponding indexed
   projection: the second conjunct quantifies `p : ℕ`,
   `J : Fin (p + 2) → I`, and `r : Fin (p + 2)`. PASS.
   The left `Pi.lift` keeps projections indexed by `r.succAbove s`;
   the right one keeps the same indexed factors, followed by the
   coprojection labelled `fun s => J (r.succAbove s)` and `(e p).hom`.
   I read the definition of `Fin.succAbove` in Data/Fin/SuccPred.lean:
   it preserves order and skips exactly r. Thus first, middle, and last
   omitted factors are all covered. The index shift covers all lengths
   at least two, exactly as step 4 of the node specifies (p >= 1 there).

Edge cases: with I empty, positive-length tuples are empty, both sides are
empty schemes, and the component equations are vacuous. With singleton I
both sides are the same indexed fibre product up to the canonical isomorphism.
At p=0 there is one factor and no imposed omission to a nonexistent negative
degree. Empty U_i and empty X are allowed; there is no nonempty instance.
The zero ring's spectrum is an allowed empty scheme. No integer parameter
other than nonnegative p, and no characteristic condition, occurs. Universes
u and v are explicitly declared and independent. A finite index type is small
in every required universe, so no missing Small binder restricts the node.
Every variable in the signature is bound; the `u` morphism binder is distinct
from the universe level of the same spelling.

Independent searches (different wording from the first reader):

- msearch LeanFinder: "Cech nerve of disjoint union decomposition into
  products indexed by tuples" returned eight hits. The relevant ones are
  `CategoryTheory.Arrow.cechNerve`, its object/map descriptions, and
  `CategoryTheory.cechNerveTerminalFrom`; they construct Cech objects but do
  not state this decomposition of scheme coproduct powers or its compatibility.
- msearch Loogle: `CategoryTheory.Limits.sigmaComparison` returned eleven
  comparison-map/preservation lemmas; none states the iterated decomposition.
- msearch LeanSearch: "finite product of disjoint unions of schemes decomposes
  as disjoint union indexed by choices of components" was unavailable with
  Internal Server Error. No negative mathematical verdict is drawn from this.
- Direct rg of `distrib|coprod|sigma` in Mathlib's Extensive.lean, and
  `pi.*sigma|sigma.*pi|product.*coproduct|coproduct.*product|distrib`
  in Shapes/Products.lean and the distributive-category modules, found
  binary distributivity and `FinitaryPreExtensive.isPullback_sigmaDesc`.
  I opened that latter declaration: it concerns two finite families and a
  binary pullback, so is a proof input, not this all-degree statement.
  Monoidal left/right distribution similarly concerns binary coproducts.
- Direct rg of `(cech|iterat|tuple).*(coprod|disjoint)` and its reverse,
  plus the proposed name, in WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json found only the source's presheaf
  `CechComparison.lean`. I opened its `cechComplexFunctorπ` and differential
  formula: these concern presheaves on opens and FormalCoproducts, not the
  claimed Scheme isomorphism. No duplicate notion or statement was found.

H5-H9: there is no data definition with sorry; the only theorem has exactly
`by sorry`, with nothing proved. The declaration docstring includes all four
node proof steps, their named dependencies, source place, and blueprint tag;
the module docstring has the source/tag too. The namespace and topic path
follow the conventions. All three imports provide constructions used here.
The node's `lean.statement` was checked by exact string comparison against
the signature before `:= by`, and every line is at most 100 characters.
The independent server scompile.py run compiled cleanly in 2.2 seconds,
exit code 0, with no warnings. No global or local build was run.
