## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteTypeFieldPushforwardEmbedding` states
`AlgebraicGeometry.Etale.exists_mono_finite_pushforward_of_finiteType_field` with a `sorry`
proof. There are no new definitions, dependency replacements, or statement corrections.

Hypotheses and clauses:

- The base field is `(k : Type u) [Field k]`; the scheme over that field is
  `(X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]`.
- Finite type is exactly the two properties `LocallyOfFiniteType` and `QuasiCompact`
  on the structural map `X ↘ Spec (CommRingCat.of k)`. No separatedness, smoothness,
  algebraic closedness, or characteristic restriction is imposed.
- The finite coefficient ring Z/N is `ULift.{u + 1} (ZMod N)` with `(N : ℕ) [NeZero N]`.
  ZMod 0 is infinite (the integers), so the finite coefficient condition excludes it.
  N = 1 is allowed. ULift changes no ring structure and fits the recorded predicate's
  coefficient universe `Type (u + 1)`.
- A sheaf of Z/N-modules is
  `F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N)))`.
  Its constructibility is exactly `hF : Scheme.IsConstructibleEtaleModuleSheaf F`.
- The finite family is `n : ℕ`, indexed by `Fin n`; its sources are
  `Y : Fin n → Scheme.{u}` and maps `h : ∀ i : Fin n, Y i ⟶ X`.
  Finiteness of every map is `∀ i : Fin n, IsFinite (h i)`.
- The values are `M : Fin n → ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N))` with
  `∀ i : Fin n, Finite (M i)`. ModuleCat objects have additive commutative groups;
  the Z/N action makes N annihilate every element, since N is zero in ZMod N.
  Conversely an abelian group annihilated by N has its canonical Z/N-module action;
  no additional condition on the groups has been imposed.
- The constant sheaves are `(constantSheaf (Y i).smallEtaleTopology
  (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N)))).obj (M i)`.
  Applying `(lowerStar ... (h i)).obj` is the recorded direct image with module values.
- The finite direct sum is the biproduct `⨁ fun i : Fin n ↦ ...`.
  The morphism `φ : F ⟶ ...` is a module-sheaf morphism, and `Mono φ` is injectivity
  as a sheaf map. In this sheaf category it is equivalent to sectionwise injectivity.

Dependency declarations read and reused:

- `def-weil-pbc-scheme-conventions` explicitly introduces no declaration. Its finite-type
  conventions use Mathlib's `AlgebraicGeometry.LocallyOfFiniteType`, `QuasiCompact` and
  `AlgebraicGeometry.IsFinite`; their full class definitions were read in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.Finite`.
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`,
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`: read the full definition
  with finite locally closed constructible strata and finite locally constant module values.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`, `CategoryTheory.constantSheaf`:
  read its docstring and definition as sheafification of the constant presheaf.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`,
  `AlgebraicGeometry.Etale.lowerStar`: read its full signature and objectwise fibre-product
  formula; its coefficient category is arbitrary Grothendieck abelian, so ModuleCat is
  already covered and no replacement of the dependency is needed.

All recorded proof-dependency modules are imported (without `public` when proof-only).
The conventional scheme node has no module. The two Mathlib Noetherian leaves are covered
by `Mathlib.AlgebraicGeometry.Noetherian`. The upstream finite-pushforward module supplies
its global finite-biproduct instance; no local instance or notation is introduced.
The docstring follows all seven proof steps, including finite normalization over a field,
the two linear adjunctions, the counit equation, geometric stalk restriction, and finite
selection. It does not replace that route by approximation.

Edge cases checked: empty X and zero F allow n = 0 and the empty biproduct; no nonempty
index hypothesis is present. N = 1 has the zero coefficient ring and zero modules and is
included. N = 0 is excluded exactly by the stated finite-ring condition. Arbitrary fields,
all characteristics, and nonseparated finite-type schemes are included. Scheme and field
universes agree; module values live in the recorded `u + 1` universe.

Searches (all semantic/Mathlib queries run through msearch.py with logs in this sandbox):

- LeanSearch: "A constructible etale sheaf of ZMod N modules on a finite type scheme over
  a field embeds into a finite direct sum of finite pushforwards of finite constant module
  sheaves". Service returned Internal Server Error; recorded unavailable.
- LeanFinder: "constructible etale module sheaf embeds into finite direct sum finite
  pushforward constant sheaves". Eight hits concern finite presentation/type of
  SheafOfModules; none is this embedding.
- Loogle: `CategoryTheory.Mono, CategoryTheory.constantSheaf`. No hits.
- Mathlib grep: `constructible.*(embedding|mono)|finite.*pushforward`.
  Seven hits about constructible subsets and other pushforwards; no matching statement.
- rg on upstream WeilConjectures and project lean/Sheaf:
  `finite_type.*(embedding|mono)|exists.*mono.*(biproduct|constant)|lem-fin-finite-type-pushforward-embedding`.
  Found upstream `ConstructibleSheaf/FinitePushforward.lean` and project
  `ConstructibleModuleFinitePushforwardNoetherian.lean` and
  `ConstructibleModuleFinitePushforwardEmbedding.lean`. Their signatures/docstrings were
  read: upstream uses a different `IsConstructibleSheaf` predicate; the project theorems
  assume Noetherian or quasi-compact quasi-separated schemes and general finite coefficient
  rings; the latter additionally requires locally finitely presented maps in its conclusion.
  None has this node's hypotheses and conclusion exactly. Their definitions and biproduct
  machinery are reused; no notion is duplicated.
- rg on `dag/lean_names_upstream.json`, source, and project for
  `fin.finite.type.pushforward|finiteType.*pushforward`: no matching declaration;
  unrelated results concern pushforwards of quasicoherent modules.

No node fault or STATEMENT-DISPUTED issue was found.

## Second reading by NV

I independently read the sandbox node and Lean module, the blueprint source at
`sec-smooth-purity/sk-prop-sf-cbc/lem-fin-finite-type-pushforward-embedding.md`, and
Stacks `etale-cohomology.tex`, lemma `lemma-constructible-maps-into-constant`
(Tag 09Z6), including its statement, proof and Nagata footnote. Stacks assumes a
Noetherian scheme and, in (3), a Noetherian coefficient ring. Finite type over a
field implies the former; finite Z/N implies the latter. Neither source requires
separatedness, invertibility of N, or an algebraically closed base field. The
additional irreducibility/reducedness refinement in Stacks is not a clause of
this blueprint node and correctly is not added to this statement.

The node's objects, hypotheses and conclusion, in order, match as follows:

1. A field and a scheme over it: `(k : Type u) [Field k]`, `(X : Scheme.{u})`
   and `[X.Over (Spec (CommRingCat.of k))]` introduce exactly these objects and
   the structural morphism. Verdict: matches.
2. Finite type of that structural morphism:
   `[LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]` together with
   `[QuasiCompact (X ↘ Spec (CommRingCat.of k))]`. I read the convention node
   and Mathlib's `LocallyOfFiniteType` and `IsFinite` class definitions, not
   just their names. These are the convention's finite-type and finite-map
   notions. There is no extra Noetherian or separated instance. Verdict: matches.
3. The finite coefficient ring Z/N: `(N : ℕ) [NeZero N]` and
   `ULift.{u + 1} (ZMod N)`. This ring is canonically Z/N; the lift affects
   only its universe. ZMod 0 is the integers and is not among the finite
   coefficient rings in the node. Verdict: matches.
4. A module sheaf on the small etale site:
   `F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N)))`.
   These are sheaves of modules over the constant coefficient ring sheaf,
   with module-linear morphisms, as the dependency convention specifies.
   Verdict: matches.
5. Constructibility: `hF : Scheme.IsConstructibleEtaleModuleSheaf F`.
   I opened the dependency node and the full definition in
   `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`: it chooses a finite
   locally closed scheme stratification, requires constructible strata, and
   etale local trivializations with finite module values. This is the node's
   recorded predicate, rather than upstream's different `IsConstructibleSheaf`.
   Verdict: matches; no stronger constructibility condition is substituted.
6. Finitely many finite maps: `∃ (n : ℕ) (Y : Fin n → Scheme.{u})`
   `(h : ∀ i : Fin n, Y i ⟶ X), (∀ i : Fin n, IsFinite (h i)) ∧ ...`.
   Each source and map is existential and arbitrary subject to finiteness;
   no etaleness, surjectivity or presentation condition is added. Verdict: matches.
7. Finite abelian groups killed by N: existential
   `M : Fin n → ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N))` and
   `∀ i : Fin n, Finite (M i)`. A module's additive group is abelian and
   is annihilated by N because N times the ring unit is zero. Conversely every
   abelian group killed by N has the canonical Z/N action, transported through
   ULift. Thus using modules neither loses nor adds group values. Verdict: matches.
8. The constant sheaves and direct images are exactly
   `(constantSheaf (Y i).smallEtaleTopology (ModuleCat ...)).obj (M i)` and
   `(lowerStar (ModuleCat ...) (h i)).obj` of those objects. I opened Mathlib's
   `constantSheaf` (constant presheaf followed by sheafification), and upstream
   `Etale.lowerStar` with its surrounding coefficient/category binders and
   objectwise formula. It evaluates on the base-changed etale object, for any
   scheme map, and applies directly to ModuleCat. Verdict: matches both
   recorded dependencies, including the module-valued direct-image clause.
9. An injective module-sheaf map into their finite direct sum:
   `∃ (φ : F ⟶ ⨁ fun i : Fin n ↦ ...), Mono φ`.
   The finite biproduct is the finite direct sum in this abelian sheaf category;
   `Mono` is the usual injective sheaf-map condition. All target data precedes
   the map existential, just as in the node. Verdict: matches every conclusion.

Edge cases: n = 0 is admitted without a nonempty-family assumption. This covers
empty X and zero F via the zero biproduct. N = 1 is admitted (the zero ring and
zero modules); N = 0 is excluded precisely because the coefficient ring must
be finite. There is no restriction on the base characteristic or its relation
to N. Nonseparated finite-type schemes are included. The universe `u` is
explicitly declared, all objects and variables are bound, and ModuleCat lives
in the `u + 1` universe of the dependency predicate and small-etale machinery.
The finite values impose no additional universe restriction: finite groups
can be represented there. No independent test-object universe can make any
hypothesis vacuous.

Independent searches, using different wording from the worker:

- LeanFinder via msearch: "torsion constructible sheaf injection finite morphisms
  constant finite modules over field". Eight hits concerned finite-type module
  sheaves or condensed constant-module functors, not this statement.
- Loogle via msearch: `CategoryTheory.Mono, AlgebraicGeometry.Etale.lowerStar`.
  No hits; the service does not index the project identifier `lowerStar`.
- LeanSearch via msearch: "finite type scheme over field constructible torsion
  sheaf embeds into finite direct sum of constant sheaf pushforwards".
  The service returned Internal Server Error and was unavailable; no conclusion
  is drawn from that failure.
- Independent rg searches in Mathlib, upstream WeilConjectures, project
  `lean/Sheaf` and `dag/lean_names_upstream.json` used
  `finiteType.*(mono|pushforward)`, `finite.*constant.*embedd`,
  `embedd.*finite.*constant`, and the proposed declaration name. No exact
  declaration exists. I also read the full signatures of upstream
  `exists_mono_biproduct_lowerStar_of_isNoetherian`, project
  `exists_mono_biproduct_lowerStar_of_isNoetherian_etaleModule`, and
  `finite_pushforward_embedding_of_isConstructibleEtaleModuleSheaf`.
  Upstream uses another constructibility predicate; the project versions
  quantify over Noetherian or compact quasi-separated schemes, rather than
  finite-type schemes over a specified field; the last also includes local
  finite presentation in its conclusion. These are useful related results,
  not declarations with this node's exact statement. The delivered module
  introduces no definition and duplicates no underlying notion.

There are no new definition nodes, dependency replacements or statement-change
records to review. The module defines no data, leaves only the named theorem's
whole proof as `sorry`, and introduces no local notation, instances or private
notions. Both docstrings cite the source and blueprint id; the theorem docstring
tracks all seven proof steps of the node, including the adjunction equations
and stalk injectivity before finite selection. The node's `lean.statement`
was checked against the signature in the file and is verbatim equal.

Mismatches found: none. Changes: only this independent second-reading report;
no Lean or node repair was needed. Server compilation via scompile.py succeeded
without errors or warnings (3.1 seconds, nice 19, two threads, 60-second limit).
