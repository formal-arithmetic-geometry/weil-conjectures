## Worker report

The module `Sheaf.CategoryTheory.InjectiveIffExtendsSubobjectGenerator` states
`CategoryTheory.injective_iff_extends_subobject_generator`, with a single `sorry` proof.
It defines no new notion and changes only the item's `lean` record.

The statement was checked against Stacks Project, Lemma 19.11.6, Tag 079G:
https://stacks.math.columbia.edu/tag/079G . The local literature source
`literature/stacks-project/injectives.tex` is absent on this machine, so the source lemma
and its proof were read on the official Stacks site. The node agrees with the source.

Hypothesis and clause correspondence:

- The category `𝒜` is `{C : Type u} [Category.{v} C]`, with both universes explicitly bound.
- Abelian is `[Abelian C]`. Grothendieck abelian is `[IsGrothendieckAbelian.{v} C]`,
  exactly the universe specialization recorded by `def-sp-grothendieck-abelian`.
  It supplies small colimits, exact filtered colimits, and a generator; local smallness
  at the hom universe is automatic, so no extra restriction is imposed.
- The specified generator and object are `(U I : C)`, with `(hU : IsSeparator U)`
  expressing that this particular `U` is a generator. The class's existence of some
  generator alone would not suffice to specify the generator occurring in the conclusion.
- Injectivity of `I` is `Injective I`, the first clause's recorded declaration in
  `def-sp-injective-resolutions.mathlib_match.how`.
- “If and only if” is `↔`.
- Every subobject `M ⊆ U` is `∀ (M : Subobject U)`; `(M : C)` uses Mathlib's underlying
  representative, and `M.arrow` is its monomorphism into `U`.
- Every morphism from that subobject into `I` is `(f : (M : C) ⟶ I)` under the same `∀`.
- Existence of an extension `U → I` is `∃ g : U ⟶ I`.
- Restriction to the original morphism is exactly `M.arrow ≫ g = f`.

Dependency declarations read and used:

- `def-sp-grothendieck-abelian`: `CategoryTheory.IsGrothendieckAbelian` in
  `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`, specialized at `w = v`
  as its record instructs; its complete class signature and docstring were read.
- `def-sp-injective-resolutions`: `CategoryTheory.Injective` in
  `Mathlib.CategoryTheory.Preadditive.Injective.Basic`. The node's record explicitly
  assigns `Injective` to its first clause and `InjectiveResolution` to its second clause.
  Both signatures and docstrings were read. Only injectivity is needed here; no resolution
  or enough-injectives assumption is introduced.
- `CategoryTheory.IsSeparator` in `Mathlib.CategoryTheory.Generator.Basic`, and
  `CategoryTheory.Subobject`, its coercion and `Subobject.arrow` in
  `Mathlib.CategoryTheory.Subobject.Basic`, come through the Grothendieck-category import.
  These are the existing notions used by the recorded Grothendieck class; no duplicate
  definitions or extra nodes are needed.

Edge cases checked: the bottom subobject has only the zero map and its extension is the
zero map; the top subobject permits every map to extend through its isomorphic inclusion.
The zero object `I` is injective and satisfies the extension condition. A zero generator
is possible only for a category in which all objects are zero up to isomorphism, where
both sides hold. Arbitrary subobjects, including these extreme cases, are quantified.
Object and hom universes remain independent. No nonzero, finiteness, countability or
projectivity condition on the generator is added. The docstring includes the empty-chain
upper bound separately, avoiding use of filteredness for the empty chain.

Searches made for an existing statement (actual results logged in `searches.jsonl`):

- `msearch.py leanfinder`: “An object in a Grothendieck abelian category with generator U
  is injective iff every morphism from a subobject of U extends to U”. Eight results,
  including enough injectives and `generatingMonomorphisms`; no exact criterion.
- `msearch.py loogle`: `CategoryTheory.Injective, CategoryTheory.IsSeparator`. Two hits,
  on an injective coseparator and a Gabriel–Popescu auxiliary result; neither states this.
- `msearch.py grep`: `injective_iff|generatingMonomorphisms_rlp|Baer` in `CategoryTheory`.
  Found general injectivity characterizations; direct reading of
  `GrothendieckCategory/EnoughInjectives.lean:311` confirmed the recorded partial match
  `IsGrothendieckAbelian.generatingMonomorphisms_rlp`. It compares lifting properties,
  rather than stating this injectivity equivalence by itself.
- `msearch.py leansearch`: “Baer criterion for injectivity using a generator in a
  Grothendieck abelian category”. Service unavailable (Internal Server Error), logged.
- `rg` in upstream `WeilConjectures`, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for Baer, injective equivalences involving generator,
  separator or subobject, and the item id: no matching statement (only unrelated Baer sum).
- Exact-name search `injective_iff_extends_subobject_generator` across Mathlib, upstream,
  project Lean and upstream name index: no collision.

No statement correction, dependency repair, new node, or disputed statement was needed.
Compilation and delivery dry-run results are recorded after validation below.

Validation: `scompile.py M1 lem-pur-kinjective-characterize-injective` compiled the
49-line module on the server in 1.1 seconds, exit code 0, with no warnings or errors.

## Second reading by M1

I independently opened the repository node, the sandbox node and Lean module, both
statement-dependency nodes, and the Mathlib declarations below. The statement matches
the node and source; no signature or mathematical correction is needed. The only change
is this independent review and its validation record. There are no new definition nodes,
dependency modules, or `statement_change` records to review.

Source check: the local literature checkout does not contain `injectives.tex`. I read
[Stacks Tag 079G](https://stacks.math.columbia.edu/tag/079G), then fetched the actual
[Stacks TeX source](https://raw.githubusercontent.com/stacks/stacks-project/master/injectives.tex)
into `scratchpad/injectives-source.tex` in this sandbox. I read
`lemma-characterize-injective` and the preceding `definition-grothendieck-conditions`
and section introduction. The source assumes an abelian category with AB5 and a generator;
there is no standing ring, field, characteristic, Noetherian, or finiteness hypothesis.
The generator detects proper subobjects. In an abelian category this is precisely the
separator condition: faithfulness detects the nonzero quotient morphism of a proper
subobject; conversely, a nonzero difference of two morphisms has a proper kernel and
is detected by a map from the generator.

Object, hypothesis, and conclusion checklist (each verdict: exact):

1. Category `𝒜`: `{C : Type u} [Category.{v} C]`. Both `u` and `v` are explicitly
   declared by `universe v u`; neither is identified with the other.
2. Abelian category: `[Abelian C]`. Grothendieck: `[IsGrothendieckAbelian.{v} C]`.
   I read its class fields in `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`:
   local smallness, filtered colimits, AB5, and a separator. The recorded dependency
   `def-sp-grothendieck-abelian.mathlib_match` explicitly specifies this `w = v`
   interpretation. Local smallness relative to the hom universe is automatic; the class's
   `hasColimits` instance supplies small colimits. No extra structure beyond the node's
   Grothendieck hypothesis is assumed.
3. Specified generator `U`: `(U I : C)` and `(hU : IsSeparator U)`. I read `IsSeparator`
   and `ObjectProperty.IsSeparating` in `Mathlib.CategoryTheory.Generator.Basic`:
   the singleton property means that `Hom(U, -)` is faithful. The hypothesis specifies
   this `U`, independently of the class's existence of some separator; it is required
   by the source, not an additional condition on its chosen generator.
4. Arbitrary object `I`: the second object in `(U I : C)`; no nonzero or injectivity
   instance is assumed for it.
5. Left conclusion, injectivity of `I`: `Injective I`. I read `Injective.factors` in
   `Mathlib.CategoryTheory.Preadditive.Injective.Basic`: every `X ⟶ I` extends along
   every mono `X ⟶ Y`. This is exactly the surjectivity of the restriction on Hom in
   the first clause of `def-sp-injective-resolutions`; the dependency's match explicitly
   assigns this clause to `Injective`, although its primary declaration names
   `InjectiveResolution`. I also read that resolution declaration; the theorem neither
   uses resolutions nor assumes enough injectives.
6. Equivalence: `↔`, covering both directions rather than only a sufficient criterion.
7. Every subobject `M ⊆ U`: `∀ (M : Subobject U)`. I read `Subobject` in
   `Mathlib.CategoryTheory.Subobject.Basic`: isomorphism classes of monomorphisms into
   `U`. Its coercion chooses an underlying object, and `M.arrow` is a mono to `U`.
   Quantifying over chosen representatives loses no monomorphisms: any other
   representative is isomorphic over `U`, and maps to `I` transport along that isomorphism.
8. Every morphism `M → I`: `(f : (M : C) ⟶ I)` in the same universal quantifier,
   after the chosen subobject. There is no restriction on `f`.
9. Existence of an extension `U → I`: `∃ g : U ⟶ I`, after `M` and `f`.
10. Commutativity/restriction: `M.arrow ≫ g = f`. This uses the actual inclusion
    of the chosen subobject and has the correct composition order; uniqueness is not
    asserted. Quantifier order is exactly `∀ M, ∀ f, ∃ g`.

Edge cases: bottom and top subobjects are included. For bottom, the unique map to `I`
extends by zero; for top, its inclusion is an isomorphism and every map extends.
A zero object `I` satisfies both sides. If `U` is zero and a separator, all morphisms
are equal, hence the abelian category is trivial up to isomorphism; this case is included.
There is no index set in the statement and no nonemptiness assumption. The proof docstring
handles the empty Zorn chain with the original pair, separately from nonempty filtered
chains. Schemes, a degree `n`, and characteristic are absent; categories arising from
empty schemes and arbitrary coefficient characteristics are not excluded. Arbitrary
object and hom universes are retained, with smallness measured exactly as in the recorded
Grothendieck definition. No small-category or small-subobject instance is added.

Independent searches, using different wording from the worker (logged in `searches.jsonl`):

- LeanFinder: `An injective object is characterized by extending maps defined on subobjects
  of a separating object` returned eight results (injective coseparators, separator tests
  for monos, presentations, and presentability); none states this criterion.
- Loogle: `CategoryTheory.Injective, CategoryTheory.Subobject` returned no hits.
- LeanSearch: `Injectivity detected by extending morphisms from subobjects of a separating
  generator` was unavailable with Internal Server Error, recorded as unavailable.
- `msearch.py grep` in Mathlib `CategoryTheory`:
  `Injective.*(IsSeparator|Subobject)|injective.*(generator|separating)|generatingMonomorphisms_rlp|injective_iff_rlp`.
  I opened `IsGrothendieckAbelian.generatingMonomorphisms_rlp` and
  `injective_iff_rlp_monomorphisms_zero`. The former equates right-lifting properties
  of morphisms for two families; the latter tests against all monomorphisms and does not
  mention a generator. Together they imply the node; neither is its exact declaration.
- Direct `rg` with `baer|injective_iff|injective.*separator|injective.*subobject|extends.*generator|generatingMonomorphisms_rlp`
  across Mathlib category theory, upstream `WeilConjectures`, and project `lean/Sheaf`
  found no exact statement. I opened the upstream near-hit
  `CategoryTheory/GrothendieckAbelian/SerpeSmallObject.lean`: it concerns the small object
  argument for monomorphic quasi-isomorphisms of complexes, not this object criterion.
  Exact declaration-name and node-id searches in `dag/lean_names_upstream.json` found
  no collision. All notions used already exist in the dependency declarations or Mathlib;
  no private definition or missing dependency module is needed.

Docstrings and conventions: the two imports supply the Grothendieck and injectivity
notions used. Module and theorem docstrings name Tag 079G and the exact blueprint id.
The theorem docstring covers all five node proof steps: immediate forward extension;
compatible partial extensions and the AB5/Zorn upper bound; generator detection of the
proper subobject and pullback; vanishing on the kernel, descent, agreement by the epic
restriction, and gluing; maximality and the final arbitrary-monomorphism conclusion.
There are no definitions, hollow data, or proved lemmas. The sole theorem proof is `sorry`.
Topic path, namespace, line widths and binders are correct, and `lean.statement` is
verbatim the signature before `:=`. No mismatch was found, so the Lean and node are kept.

Second-reader validation: `scompile.py` compiled the unchanged 49-line module on the
server in 1.1 seconds, exit code 0, with no errors or warnings. Delivery preflight and
push are performed by the prescribed `deliver2.py` helper after this reading.
