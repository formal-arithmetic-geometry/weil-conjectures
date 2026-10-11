## Worker report

The main module `Sheaf.CategoryTheory.Sites.ZariskiContractedPowerTorsor` states
`CategoryTheory.Sheaf.Torsor.nonempty_coherentContractedPowers` with proof `sorry`.
It asserts existence of a fully specified coherent signed-power system. The two supporting
modules define structures with all data and laws written out, without any `sorry`.
There is no statement correction and no disputed mathematical claim.

Hypotheses and clauses, with their exact Lean rendering:

- Scheme X: `(X : AlgebraicGeometry.Scheme.{uCT})`, with no geometric restrictions.
- Abelian sheaf G on the small Zariski site: `(G : Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{wCT})`. Objects are opens of X,
  morphisms are inclusions, and covering sieves cover every point.
- G-torsor T: `(T : Torsor G)`, using the source's sheaf torsor, not Mathlib's
  torsor of a nonempty set. It includes local nonemptiness and simple transitivity.
- Inverse torsor: `inverse_sheaf` identifies the underlying sheaf of `power (-1)` with
  `T.sheaf`; `inverse_vadd` gives exactly the action by `-g` through this equality.
- Positive n-fold contracted products and negative inverse products: `power : ℤ → Torsor G`
  and `product m n` present `power (m+n)` as the sheaf quotient of the two powers.
  Thus `product k 1` and `product (-k) (-1)` identify successive signed powers with
  the iterated contracted products. This is the universal-property specification of
  the iterated product; no arbitrary sectionwise orbit quotient is substituted.
- Degree zero: `zero : power 0 = trivial G`; degree one: `one : power 1 = T`.
- Clause (a): every `power n` has type `Torsor G`, including zero and negative n.
- Clause (b): `product m n : BinaryContractedProductPresentation X (power m)
  (power n) (power (m+n))`. A presentation uses the target as the chosen quotient
  object: its universal property specifies exactly the isomorphism from the
  antidiagonal sheaf quotient to `power (m+n)`. This avoids introducing a second,
  independently chosen quotient object just to express the same canonical isomorphism.
  `invariant` is the relation `(g·x,(-g)·y) ~ (x,y)`; `equivariant` makes the induced
  quotient isomorphism G-equivariant; `natural` and `universal` are the sheaf quotient
  universal property against every sheaf of sets, not only against torsors.
- Cancellation: `cancellation` says the degree `(1,-1)` quotient value h satisfies
  `T.vadd U h s = t`, after the specified degree/sheaf identifications. The unique h
  condition is supplied by `T.bijective_vadd`. The quotient universal property makes
  this an isomorphism onto the degree-zero torsor G, not just an invariant function.
- Both unit constraints: `left_unit` and `right_unit` say the quotient map is precisely
  the action, on every degree. In degree one, `one` identifies this with the original
  action of G on T, so the final clause about `G ∧ T` is included literally.
- Associativity: `associative` compares the two triple-product composites on all
  representatives, using the cast along `Int.add_assoc` to identify target indices.
- Commutativity: `commutative` swaps x,y and compares the degree `(n,m)` quotient
  with the degree `(m,n)` quotient, using `Int.add_comm` for the indices.
  Universality of the quotient presentations promotes these representative identities
  to the stated morphism identities, including the associator and swap constraints.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` (def-pc-scheme).
- `Mathlib.CategoryTheory.Sites.Spaces`: `Opens.grothendieckTopology`
  (def-sc-zariski-site). Also read `TopCat.Sheaf` in
  `Mathlib.Topology.Sheaves.Sheaf`: its definition is exactly `Sheaf` on this topology.
- `WeilConjectures.CategoryTheory.Sites.Torsor`: `CategoryTheory.Sheaf.Torsor`,
  `Torsor.trivial`, and `Torsor.Iso` (def-sc-gm-torsor).
- Read the complete signature and docstring of
  `CategoryTheory.Sheaf.nonempty_equiv_H_one_torsor` (lem-sc-torsor-h1) and the module
  TODO. This declaration classifies torsors, but does not define their contracted
  product. No cohomology term is needed in the present statement. The missing binary
  quotient notion is supplied explicitly by the first new definition node; we do not
  redefine or restate the existing H¹ classifier, nor assume its unimplemented group law.
- The main theorem imports `Sheaf.CategoryTheory.Sites.CoherentContractedPowers` and
  uses `CategoryTheory.Sheaf.Torsor.CoherentContractedPowers`. This imports the binary
  presentation module and uses `CategoryTheory.Sheaf.Torsor.BinaryContractedProductPresentation`.

Edge cases checked before writing: the empty scheme is allowed, and its sheaves have the
usual forced section over the empty open. No global section of T is assumed. G may be zero,
in which case local simple transitivity still supplies the appropriate trivial torsors.
Degree zero is G, degree one is T, degree minus one uses the negated action, and all
mixed-sign products are covered. No positivity, characteristic, field, Noetherian, or
separation assumption is imposed. The scheme universe and the section universe are explicit
and independent; every object/universe is bound. Casts express equality of indices, not
extra assumptions. Canonical isomorphisms are specified by quotient universal properties,
so no extra choice of product object is being imposed on the mathematics.

Searches performed using `/home/ubuntu/weil-launcher/msearch.py` (recorded in searches.jsonl):

- LeanFinder: `coherent integer contracted powers of an abelian sheaf torsor`, eight
  unrelated sheaf-cohomology/module hits, no contracted-power definition.
- Loogle: `Torsor`, twelve hits for ordinary type-level group torsors and their actions,
  none for sheaf torsor powers.
- Mathlib grep: `contracted|inverseTorsor|torsorPow`, two unrelated polynomial hits.
- LeanSearch: `integer powers of a sheaf torsor contracted product`, unavailable:
  Internal Server Error.
- LeanFinder: `sheaf quotient of a pair of torsors by the antidiagonal action universal property`,
  eight gluing and sections hits, no binary contracted-product presentation.
- Loogle: `"contracted"`, zero hits.
- LeanSearch: `sheaf quotient contracted product of torsors universal property`, unavailable:
  Internal Server Error.
- `rg` of the source repository for contracted products/powers: only the torsor module's
  TODO, docstrings, and unrelated geometric/Kummer uses. The source has no quotient notion.
- `rg` of `lean/Sheaf`: found `ContractedProductPresentation`, read in full. It is the
  étale change-of-group quotient of `T × G'` by G along a homomorphism; it cannot accept
  a second arbitrary G-torsor or a Zariski site. The new binary quotient is a distinct
  notion, rather than a copy of that specialized change-of-coefficients presentation.
- Searched DAG text and `tools/blueprint_refs.py search contracted`: existing nodes
  concern the torsor group law, change of coefficients, and the present power theorem;
  none defines a binary quotient presentation or a coherent system.
- `rg` for all three chosen declaration names in Mathlib, WeilConjectures, lean/Sheaf,
  and dag/lean_names_upstream.json: no collisions. Node-id search of WeilConjectures:
  no occurrence of the present item's id.

The cited blueprint source is absent from this machine's literature tree. Read it directly,
read-only over ssh, from the server's same repository path. Its group law is the
antidiagonal quotient of torsors and it explicitly includes the Zariski case. The item's
four-step proof gives the local signed-coordinate construction; this proof is carried
step by step in the theorem docstring. No Stacks tag is falsely credited with the
coherent integer-power construction.

## New nodes

`def-sc-binary-contracted-product-presentation` defines the universal sheaf quotient of two
Zariski G-torsors, with natural invariant quotient maps and the residual G-action. Its source
is the blueprint torsor group law cited by the item. LeanFinder, Loogle, LeanSearch and grep
searches above show that it is absent; the existing change-of-group presentation is étale
and takes `T × G'`, not two torsors. Its statement cites the existing scheme, site, and torsor
nodes, and its module contains only the full structure definition.

`def-sc-coherent-contracted-powers` defines the signed family of torsors, normalized zero,
one and inverse terms, and binary quotient presentations with both units, associativity,
commutativity and cancellation. Its source is the worker's integer-power construction in
the item's source record. The searches above find no existing notion in the DAG, Mathlib,
the source or lean/Sheaf. The definition cites the first new node and the existing scheme,
site, and torsor nodes. Its module contains only the full structure definition. Both new
nodes are cited directly in the item's added stmt_deps; the item's other fields are unchanged.

## Second reading by M1

I independently read the base node, all three delivered nodes and modules, the four
statement-dependency nodes and their recorded declarations. I read the source blueprint
`sec-curve-estimates/sk-prop-hilbert90/lem-sc-torsor-h1.md` directly on the server over
read-only ssh. It explicitly specifies the antidiagonal quotient and translation unit,
and explicitly extends the argument to the Zariski site. The integer-power argument is
in the item's four proof steps, as its source.place correctly says; it is not attributed
to a nonexistent Stacks construction. No statement_change is present or needed.

My object/hypothesis/conclusion checklist against the node is:

- Arbitrary scheme X: `X : AlgebraicGeometry.Scheme.{uCT}`. Read Mathlib's `Scheme`
  structure and local-affineness field. Exact; no field, finiteness or separatedness binder.
- Small Zariski site: `Opens.grothendieckTopology X`. Read `Spaces.lean:48`, whose
  covering-sieve condition covers every point, and `TopCat.Sheaf` at `Sheaf.lean:108`.
  Exact opens/inclusions/coverings, not the small etale site.
- Abelian sheaf G: `G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{wCT}`.
  Exact; commutativity is part of the value category and no stronger coefficient
  structure is assumed.
- G-torsor T: `T : CategoryTheory.Sheaf.Torsor G`. Read its full structure, especially
  `map_vadd`, `bijective_vadd` and `nonemptySieve_mem`. Exact sheaf action, simple
  transitivity whenever a section exists, and local sections; no global nonemptiness.
- Inverse torsor: `inverse_sheaf` and `inverse_vadd` preserve the underlying sheaf and
  change g to -g. Exact, including the restriction maps, since the equality is of sheaves.
- Positive iterated products: `power : ℤ → Torsor G`, `one` and `product k 1`
  recursively present the successive powers as the sheaf contracted products. Exact
  up to the canonical quotient identification intrinsic to choosing quotient objects.
- Negative iterated products: the inverse fields and `product (-k) (-1)` give the
  corresponding recursion from the inverse torsor. Exact; integers are unrestricted.
- Degree zero: `zero : power 0 = trivial G`. Read `trivial`: its sheaf is the underlying
  sheaf of G and its action is addition. Exact translation unit.
- Clause (a): the codomain of `power` is `Torsor G` for every integer. Exact; the
  existence theorem does not require the caller to supply any of these powers.
- Clause (b), all m,n: `product m n : BinaryContractedProductPresentation X
  (power m) (power n) (power (m+n))`. Its `quotient`, `natural`, `invariant` and
  `universal` fields are precisely the universal sheaf quotient of the antidiagonal
  action; `equivariant` supplies the residual G-action. Using the target as a quotient
  presentation records the canonical isomorphism without choosing a redundant second
  quotient. It tests all sheaves of sets in the ambient section universe, not only
  torsors. Exact.
- Cancellation T wedge inverse T to G: `cancellation` says h acts on s to give t,
  after the `one`, `zero` and `inverse_sheaf` identifications. Its h is the value of
  `product 1 (-1)`. Uniqueness follows from the dependency's `bijective_vadd`; quotient
  universality and local sections ensure the cancellation isomorphism. Exact sign.
- Degree-zero constraints: `left_unit` and `right_unit` give the original actions
  for every degree, not merely identity at the zero section. Exact both units.
- Associativity: `associative l m n` equates both triple-product composites, with the
  target cast along `Int.add_assoc`. The sheaf quotient universal property extends
  these representative identities to morphisms; local torsor sections also ensure
  representatives exist locally. Exact, including mixed signs.
- Commutativity and swap: `commutative m n` exchanges x and y and casts along
  `Int.add_comm n m` in the correct direction. Exact swap identity.
- Degree one and G wedge T: `one : power 1 = T` and `left_unit 1` give exactly the
  last clause, including the action on the original T. Exact.
- Existence/quantifier order: `nonempty_coherentContractedPowers X G T` returns
  `Nonempty (CoherentContractedPowers X T)` after the three input binders. All signed
  degrees and coherence laws are inside the supplied system, with no extra hypothesis.

The two new nodes are legitimate missing notions. I checked their source, statements,
fields, and structure fields separately. The binary node's natural quotient, invariance,
residual equivariance and universal factorization match its TeX one for one. The coherent
node's normalization, inverse action, all presentations, units, associativity, swap and
cancellation match its TeX one for one. Both have empty proofs, null mathlib_match,
three search kinds, worker creation records, the item's chapter/unit, and the ancestor
`lem-sc-pic-proper-ntorsion` confirmed with `tools/blueprint_refs.py ancestor`.
Their dependency lists are exactly the bracket citations; the item cites both new nodes.
There are no dependency modules. The recorded H1 declaration was opened: it only gives
an existence classifier, not a contracted-product construction; the new binary node
supplies that missing notion, and this theorem makes no claim about the H1 classifier.

Edge cases: empty X and empty opens are covered (sheafness forces the unique empty-open
section); an empty covering is admissible there. No indexing set or nonempty-open binder
is introduced. The zero abelian sheaf is allowed. Integers 0, 1, -1, arbitrary negative
and mixed-sign indices have all the required laws. No characteristic assumption occurs.
The scheme and section universes are separately bound and polymorphic; the quotient
universal property is in the same ambient sheaf category as the dependency's torsors.
There are no implicit unbound objects or universes.

Independent searches with different wording, recorded by msearch.py in searches.jsonl:
LeanFinder `tensor product of two principal homogeneous sheaves with integer powers`
returned eight Picard-group/module tensor hits, none a sheaf torsor product or power;
Loogle `"Torsor"` returned twelve ordinary type torsor/action hits, none the sheaf notion;
LeanSearch `quotient sheaf of two torsors by diagonal group action` was unavailable
(Internal Server Error, no verdict inferred). Independent rg of Mathlib's sites, the
source's Sites directory and lean/Sheaf/Sites for torsor with tensor/power/product/quotient
found the source's classification and TODO, and existing etale change-of-coefficients
presentations. I opened `ContractedProductPresentation.lean` in full: it takes a sheaf
homomorphism G to G', T times G', and the etale site, so is not this binary Zariski
quotient. DAG/blueprint searches likewise found the group-law and power statements,
not definitions of the two new notions. All three new declaration names have no
collision in Mathlib, WeilConjectures, lean/Sheaf or dag/lean_names_upstream.json.

No mathematical or signature mismatch was found; no Lean or node changes were made.
I added this independent reading only. All declaration/module docstrings name their
sources and blueprint nodes; the main theorem carries all four proof steps. The two
structures contain actual data and laws, no sorry; the sole theorem has exactly a sorry
proof. Lines are at most 100 characters, namespaces have no Sheaf prefix, imports are
used, and the three lean.statement records agree verbatim with their signatures.
All three modules compiled together in dependency order with scompile.py: exit 0,
2.2 seconds, no errors or warnings. Delivery preflight and final server compilation
are run by deliver2.py below.
