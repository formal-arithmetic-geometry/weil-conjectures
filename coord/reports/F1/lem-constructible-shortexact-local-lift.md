## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleShortExactLocalLift` states
`AlgebraicGeometry.Scheme.exists_etale_local_lift_of_shortExact`, with proof `sorry`.
It states local lifting of individual sections of the quotient of a short exact
sequence of module sheaves. No definitions, new nodes, dependency modules, or statement
corrections are needed. No STATEMENT-DISPUTED issue arises for this local-lifting assertion.

Hypothesis and clause correspondence:

- Scheme X: `(X : Scheme.{u})`, with no finiteness, separation, or nonemptiness assumptions.
- Ring Λ: `(Λ : Type u) [Ring Λ]`, allowing noncommutative rings and the zero ring.
  The constant coefficient ring sheaf is
  `(constantSheaf X.smallEtaleTopology RingCat.{u + 1}).obj
  (RingCat.of (ULift.{u + 1, u} Λ))`.
  ULift changes only universe placement, with the canonical ring isomorphism to Λ;
  it adds no mathematical hypothesis on the coefficients.
- The small etale site is `X.Etale` with `X.smallEtaleTopology`.
- Module sheaves M, E, N and maps M → E → N are respectively
  `S.X₁`, `S.X₂`, `S.X₃`, `S.f`, `S.g`, for `S : ShortComplex (SheafOfModules ... )`.
  The short complex carries the composite-zero condition, and `(hS : S.ShortExact)`
  asserts exactness, monicity of `S.f` and epicity of `S.g`, exactly the displayed
  sequence with zero terms at both ends.
- Every etale X-scheme U: `(U : X.Etale)` is an arbitrary input.
- Every section t of N on U: `(t : S.X₃.val.obj (op U))` is an arbitrary input.
- The covering family: existential `I : Type (u + 1)`, `V : I → X.Etale`,
  and `f : ∀ i : I, V i ⟶ U`, with
  `Sieve.ofArrows V f ∈ X.smallEtaleTopology U`.
  By the recorded dependency's `ofArrows_mem_smallEtaleTopology_iff`, this is precisely
  joint surjectivity of the underlying family of etale morphisms. Morphisms in
  `X.Etale` are automatically etale. Index universe u+1 suffices to index all
  arrows into U, hence excludes no local-lifting instance; it permits arbitrary
  infinite families as well as empty ones.
- Sections s_i: the existential dependent function
  `s : ∀ i : I, S.X₂.val.obj (op (V i))` chooses a section on each covering object.
- Lifting equality on every member: `∀ i : I,
  S.g.val.app (op (V i)) (s i) = S.X₃.val.map (f i).op t` is exactly π(s_i)=t|_{V_i}.

Dependencies read and used:

- `def-weil-pbc-etale-site`: `AlgebraicGeometry.Scheme.Etale` in
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`, and
  `AlgebraicGeometry.Scheme.smallEtaleTopology` and
  `AlgebraicGeometry.Scheme.ofArrows_mem_smallEtaleTopology_iff` in
  `Mathlib.AlgebraicGeometry.Sites.Etale`.
- `def-weil-pbc-etale-sheaves`: imported recorded module
  `Sheaf.AlgebraicGeometry.EtaleSheaves`. Its mixed declaration record explicitly
  identifies module sheaves as `SheafOfModules` of the constant ring sheaf and
  records `CategoryTheory.constantSheaf` and `SheafOfModules`. Those existing
  declarations are used directly, rather than the unrelated set-valued predicates.
  `constantSheaf` is in `Mathlib.CategoryTheory.Sites.ConstantSheaf`.
- `def-weil-sheaf-of-modules-category`: `SheafOfModules`, its `.val`, and morphisms
  `.val.app`, in `Mathlib.Algebra.Category.ModuleCat.Sheaf`; the underlying
  restrictions `.val.map` are from `Mathlib.Algebra.Category.ModuleCat.Presheaf`.
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian` supplies the abelian structure.
- `def-weil-pbc-exact-sequence`: `CategoryTheory.ShortComplex.ShortExact`,
  in `Mathlib.Algebra.Homology.ShortComplex.ShortExact`; its fields are exactness,
  monicity of the first arrow, and epicity of the second.

The theorem docstring carries all three proof steps, including forgetting to
abelian sheaves using the colimit/forgetful node before applying the abelian
local-surjectivity node. Nothing is proved in this delivery.

Source checked: the local literature checkout has only the literature indexes,
so I read the exact source markdown on the server using read-only SSH:
`literature/blueprint/master/blueprint/sec-proper-base-change/sk-thm-properbasechange/lemma-constructible-flc-serre.md`,
extension paragraph. The node extracts the true sentence about local surjectivity
of sections. Its source also claims local splitting, which this node does not assert.
The existing lead note already distinguishes these assertions. No source error
forces a change to this node's statement.

Edge cases checked before writing: the empty scheme and empty U allow the empty
cover and its empty family of sections; no Nonempty I assumption is present.
Identity quotient maps admit the singleton identity cover. Zero module sheaves
and the zero ring are allowed. Constant Z/4 → Z/2 provides lifts without requiring
a module-linear splitting; neither the theorem nor its conclusion requires one.
No characteristic, finite-ring, constructibility, or finite-stalk assumption is
used or imposed. All binders and the universe u are explicit.

Searches for existing declarations (2026-10-11):

- `msearch.py ... leansearch "A short exact sequence of sheaves of modules has local lifts of sections"`:
  service unavailable (Internal Server Error), recorded as unavailable, with no verdict inferred.
- `msearch.py ... leanfinder "A short exact sequence of sheaves of modules on the small etale site has local lifts of every section of the quotient"`:
  eight hits for `SheafOfModules.generatorsOfIsCokernelFree`, relations and
  quasicoherence; these concern presentations by free sheaves and do not state this lemma.
- `msearch.py ... loogle "Sheaf.IsLocallySurjective, ShortComplex.ShortExact"`:
  zero hits, unknown identifier `Sheaf.IsLocallySurjective` in that search service.
- `msearch.py ... grep "IsLocallySurjective|locallySurjective" Algebra/Category/ModuleCat/Sheaf`:
  four hits in ChangeOfRings and Localization, about change of scalars and localization,
  with no short-exact lifting theorem.
- `rg -n "local.*[Ll]ift|[Ll]ocallySurjective|shortExact"` in the project's
  `WeilConjectures/AlgebraicGeometry` and `lean/Sheaf`: generic abelian-sheaf local
  surjectivity uses, special results for Gm/constant integer sheaves, and unrelated
  exact sequences. None matches the arbitrary-ring module-sheaf statement.
- `grep -rn "lem-constructible-shortexact-local-lift"` in `WeilConjectures`: no match.
- `rg -n "exists_etale_local_lift_of_shortExact|lem-constructible-shortexact-local-lift"`
  in `dag/lean_names_upstream.json`, all of `WeilConjectures`, all Mathlib, and
  `lean/Sheaf`: no match, confirming no declaration-name collision or upstream attachment.
- Read `CategoryTheory.Presheaf.imageSieve` and `IsLocallySurjective` in
  `Mathlib.CategoryTheory.Sites.LocallySurjective`: these give the generic notion,
  not this specialized statement with its short-exact hypotheses.

Validation: `scompile.py F1 lem-constructible-shortexact-local-lift` compiled the
49-line module cleanly on the server in 2.2 seconds. Delivery dry run follows;
the independent second-reading section is reserved for the second reader.

## Second reading by F1

Independent reading of the node copy, the 49-line Lean module, all four statement
 dependency records, and their actual declarations (2026-10-11). Verdict: the Lean
states the node exactly; no statement, module, or dependency repair was needed.

Object/hypothesis/conclusion checklist, written from the node before comparing:

1. An arbitrary scheme X: `(X : Scheme.{u})`. MATCH. There is no Noetherian,
   separated, quasi-compact, characteristic, or nonemptiness hypothesis.
2. An arbitrary ring Lambda: `(Λ : Type u) [Ring Λ]`. MATCH. In particular the
   declaration does not assume CommRing, Field, Finite, or Nontrivial. The
   coefficient sheaf is the existing `constantSheaf` in RingCat, applied to
   `RingCat.of (ULift.{u + 1, u} Λ)`; this is sheafification of the constant
   presheaf of rings, not the constant presheaf itself. ULift preserves the ring.
3. Sheaves M, E, N of Lambda-modules on X_et: `S.X₁`, `S.X₂`, `S.X₃` in
   `SheafOfModules` of that coefficient sheaf. MATCH. I opened
   ModuleCat/Sheaf.lean:33 and Presheaf.lean:43: the underlying values are modules,
   restrictions are semilinear, and the underlying abelian presheaf is a sheaf.
   This is precisely the dependency's notion, not a private ModuleCat-valued copy.
   The mixed EtaleSheaves record explicitly lists `constantSheaf` and
   `SheafOfModules`; its unrelated set-valued predicates are not being used.
4. A short exact sequence 0 -> M -> E -> N -> 0, with quotient map pi:
   `S : ShortComplex ...`, `S.f`, `S.g`, and `(hS : S.ShortExact)`. MATCH.
   I opened ShortComplex/ShortExact.lean:35: its fields are Exact, Mono S.f,
   and Epi S.g; the short complex already carries the zero composite.
   These are the four equivalent conditions in def-weil-pbc-exact-sequence.
5. Every etale X-scheme U: `(U : X.Etale)`. MATCH. I opened
   Morphisms/Etale.lean:158: these are etale maps to X, with X-morphisms as arrows;
   the instance immediately below proves every such arrow is itself etale.
6. Every section t of N on U: `(t : S.X₃.val.obj (op U))`. MATCH, universally
   quantified after U and before the existential cover, as in the node.
7. There exists an etale covering family of U: `∃ (I : Type (u + 1))
   (V : I → X.Etale) (f : ∀ i : I, V i ⟶ U)` and
   `Sieve.ofArrows V f ∈ X.smallEtaleTopology U`. MATCH. I read
   Sites/Etale.lean:51 and :61: this condition is equivalent to
   `⋃ i, Set.range (f i).left = Set.univ`, exactly joint surjectivity.
8. A section s_i of E on every member: the existential dependent function
   `(s : ∀ i : I, S.X₂.val.obj (op (V i)))`. MATCH. It can depend on t and the cover.
9. For each i, pi(s_i) equals the restriction of t: the final `∀ i : I,
   S.g.val.app (op (V i)) (s i) = S.X₃.val.map (f i).op t`. MATCH.
   I read the presheaf map and morphism component declarations; these are the
   actual restriction and module-linear quotient component, with the right variance.

Source reading: I independently fetched, read-only over SSH, the entire recorded
blueprint source `lemma-constructible-flc-serre.md`, including its statement and
extension proof. This node has a blueprint markdown source, not a Stacks tag.
The parent works with a finite ring and finite locally constant outer sheaves,
but the extracted assertion that surjections of sheaves locally lift sections
uses none of those restrictions, as already recorded in the node's lead note.
The node does not assert the parent's erroneous inference to local splitting.
No source correction, new definition node, or dependency module is needed;
there is no `statement_change` in this delivery.

Edge cases: I may be empty when U is empty; joint surjectivity rules out an
empty cover for nonempty U. The empty scheme, zero objects, the zero ring,
and identity quotient maps are all included. For constant Z/4 -> Z/2, sections
lift locally without a module-linear splitting; the conclusion asks for no
splitting and no compatibility between chosen lifts. There is no n parameter,
positive characteristic restriction, or assumption on finite stalks. Universe u
is explicitly bound and polymorphic: a common ambient universe houses the scheme
and coefficient ring, and u+1 houses the small-etale objects, module values and
cover indices. No fixed universe level, Fintype index, or finite-module condition
is imposed. All arrows into U can be indexed in u+1, so the existential index
universe suffices. The ULift on coefficients adds no algebraic hypothesis.

Independent searches, using different descriptions from the first worker:

- LeanSearch: "Sections of a quotient sheaf of modules admit preimages after
  passing to a covering". HTTP Internal Server Error; recorded as unavailable,
  with no mathematical verdict inferred.
- LeanFinder: "An epimorphism of module sheaves is locally surjective: sections
  of the target have preimages on a covering family". Eight hits, including
  `Sheaf.isLocallySurjective_iff_epi'`, `Sheaf.isLocallySurjective_iff_epi`, and
  presheaf-module epi/componentwise-surjectivity results. I opened the generic
  sheaf theorem in EpiMono.lean:124 and imageSieve/localPreimage in
  LocallySurjective.lean. They give general tools, not this statement for
  ShortComplex of SheafOfModules with an explicit etale covering family.
- Loogle: `ShortComplex.ShortExact`. Service reports unknown identifier;
  not evidence of absence. The successful semantic and source searches suffice.
- Logged Mathlib grep: `imageSieve|local.*surj|epi_iff` in Algebra/Category/ModuleCat.
  Hits concern presheaf-module surjectivity, sheafification, localization,
  and change of rings. No exact duplicate.
- Direct rg with `exists.*lift|local.*surj|imageSieve` throughout
  WeilConjectures and lean/Sheaf, and a focused search in ConstructibleSheaf.
  I opened the nearby Integral/Exact.lean stalk-surjectivity theorem and
  ProEtale/Adic/Extension.lean's `exists_cover_unit_lift`: the former has an
  integral morphism and stalk conclusion, the latter is on the pro-etale site
  with specific Weil coefficients and a unit-object map. Neither states this node.

H5/H6/H8/H9: there are no new definitions or hollow data; the only theorem's
proof is `sorry`. Both docstrings name the source and blueprint id. The theorem
proof text carries all three node steps, including the module-to-abelian
forgetful functor and its cokernel preservation. Imports use the recorded
etale-sheaf dependency, the abelian module-sheaf structure and ShortExact API.
No unbound variable or universe is present. The node's lean.statement is
verbatim the theorem signature, excluding `:=`. No mismatch was found and
nothing correct was rewritten. The second reading adds this report section only.
