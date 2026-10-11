## Worker report

The module `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist` states
`CochainComplex.etale_kinjective_resolutions_exist`. Its only proof is `sorry`.
No definitions, new nodes, dependency modules, or statement corrections are needed.

Hypotheses and clauses:

- The scheme is `(T : Scheme.{u})`; the commutative coefficient ring is
  `(R : Type (u + 1)) [CommRing R]`. The universe is the established six-functor encoding,
  including small rings by universe lifting. No finiteness or boundedness hypothesis is
  imposed on the input complex.
- `Cpx(Mod(T_et,R))` is
  `CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ`, the category underlying
  the dependency's `AlgebraicGeometry.Etale.DerivedCategoryModule R T`.
- Every complex has a resolution: the first conjunct supplies an object assignment `I`,
  chain maps `s : ∀ K, K ⟶ I K`, and `∀ K, IsKInjectiveResolution T R (s K)`.
  The recorded dependency abbreviation expands to `QuasiIso (s K) ∧ (I K).IsKInjective`.
- Functoriality up to chain homotopy: the assignment `φ` on chain maps preserves identities
  and compositions up to `Nonempty (Homotopy ...)`, sends homotopic maps to homotopic maps,
  and satisfies `Nonempty (Homotopy (s K ≫ φ f) (f ≫ s L))`. Thus it descends to a functor on
  the homotopy category and `s` descends to a natural transformation. Conversely, choosing
  representatives of a functor on homotopy classes gives these clauses. Strict naturality
  or a strict functor is not required. These are the expanded laws of the node's phrase
  “functorially up to chain homotopy”, not additional mathematical conclusions.
- Two K-injective resolutions of one object: the second conjunct quantifies `K I J`,
  `s : K ⟶ I`, `t : K ⟶ J`, and assumes the existing resolution predicate for both. Its
  conclusion `Nonempty (HomotopyEquiv I J)` asserts maps both ways and homotopies of both
  composites to the identities. The node does not separately require compatibility of
  that equivalence with the augmentations (its proof establishes this stronger fact).
- Bounded-below injectives: the third conjunct quantifies any `I` and integer lower bound
  `d`; `I.IsStrictlyGE d` means its terms below `d` are zero, not merely its cohomology.
  With `∀ n : ℤ, Injective (I.X n)` it concludes `I.IsKInjective`.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.KInjectiveResolutions`,
  `CochainComplex.IsKInjectiveResolution`: full sheaf-specific abbreviation, together with
  Mathlib's `CochainComplex.IsKInjective` and `QuasiIso`.
- `Sheaf.AlgebraicGeometry.DerivedCategories` (imported through the preceding dependency):
  its recorded `AlgebraicGeometry.Etale.DerivedCategoryModule` is defined in
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients` as
  `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R))`.
  The theorem concerns complexes in this exact category; the dependency's torsion
  predicate and bounded derived subcategories play no role here.
- Mathlib `Homotopy`, `HomotopyEquiv`, `CochainComplex.IsStrictlyGE`, `Injective`.
  Their signatures and the K-injective definition were read directly in Mathlib source.

Sources: the blueprint node and its full three-step proof were read. The machine has no
blueprint or Stacks source checkout under `literature/`; the cited Stacks sources were
therefore opened at https://stacks.math.columbia.edu/tag/079P and
https://stacks.math.columbia.edu/tag/070I. The former gives functorial existence in a
Grothendieck category; the latter gives bijectivity of morphisms in the homotopy category
into a K-injective complex after inverting quasi-isomorphisms. The module docstring carries
all three proof steps and their dependency ids, including the bounded-below Mathlib leaf.

Edge cases checked before writing: the zero complex can resolve itself; the empty scheme
and the zero coefficient ring give the zero category and do not invalidate any clause.
Two identical resolutions admit the identity homotopy equivalence. A complex concentrated
in one degree in an injective sheaf satisfies the third clause for that degree as bound.
Negative lower bounds are allowed (`d : ℤ`); unbounded complexes are allowed in the first
and second clauses. There are no independent index universes or excluded characteristics.

Searches (executed through msearch.py and recorded in searches.jsonl):

- LeanFinder: “Every complex of etale module sheaves has a K injective resolution
  functorially up to homotopy, unique up to chain homotopy; bounded below injective
  complexes are K injective”: eight hits on ordinary injective resolutions and their
  K-injectivity; no combined statement.
- Loogle: `CochainComplex.IsKInjective, HomotopyEquiv`: one hit,
  `HomotopyEquiv.isKInjective`, which transports K-injectivity and does not state this node.
- Mathlib grep: `isKInjective_of_injective|homotopyEquiv|exists.*[Kk]Injective` in
  `Algebra/Homology`: bounded-below injectivity leaf and homotopy equivalence infrastructure,
  no combined theorem.
- LeanSearch: “Every complex admits a K injective resolution unique up to homotopy”:
  service returned Internal Server Error; recorded unavailable, no mathematical verdict.
- Source rg: `prop-weil-pbc-kinjective-resolutions-exist` has no matches.
  `kInjectiveResolution|IsKInjective` finds the generic functor in
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`, read in full.
  Its functor, transformation, and resolution instances cover only the existence clause.
- Project rg for the same terms finds the dependency definition and partial results,
  including `KInjectiveBridge`, `KInjectiveComputes`, and bounded-below resolution modules;
  none states the combined node.
- Name collision rg for `kinjective_resolutions_exist|KInjectiveResolutionsExist` in
  `dag/lean_names_upstream.json`, Mathlib/project source: no existing declaration.

Server validation: scompile.py compiled the module cleanly in 2.1 seconds, with no errors
or warnings. No local Lean build was run. No disputed statement or dependency fault found.

## Second reading by K1

Independent review with the item's node, both statement-dependency nodes, their modules,
the source coefficient-category declaration, and the Mathlib definitions open.

Source check: the local literature directory contains citation lists but no Stacks checkout.
I fetched upstream `injectives.tex` and `derived.tex` into this item's scratchpad and read
`section-K-injective`, `theorem-K-injective-embedding-grothendieck`,
`definition-K-injective`, `lemma-K-injective`, and
`lemma-bounded-below-injectives-K-injective`. The corresponding online tags were also read:
[079P](https://stacks.math.columbia.edu/tag/079P),
[070H](https://stacks.math.columbia.edu/tag/070H),
[070I](https://stacks.math.columbia.edu/tag/070I), and
[070J](https://stacks.math.columbia.edu/tag/070J).
The existence theorem assumes a Grothendieck abelian category; comparison and the
bounded-below assertion assume an abelian category. There are no ambient Noetherian,
characteristic, torsion, or finite-dimensional hypotheses. The node specializes these
results to module sheaves and does not demand the source's additional termwise
monomorphism or injective-term properties of the chosen replacement.

Object/hypothesis/conclusion checklist, in the node's order:

1. Scheme T: `(T : Scheme.{u})`. Verdict: exact; no geometric property is assumed.
2. Commutative coefficient ring R: `(R : Type (u + 1)) [CommRing R]`.
   Verdict: exact in the dependency's established six-functor universe encoding, allowing
   all commutative rings at a sufficiently large common universe, including lifted small
   rings. No field, nonzero-ring, torsion, or characteristic condition is present.
3. Complexes in Mod(T_et,R):
   `CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ`.
   Verdict: exact. I read `AlgebraicGeometry.Etale.DerivedCategoryModule` in
   `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`; this is precisely its
   underlying abelian category. Sheaves of R-modules encode modules over the constant
   ring sheaf, using the same model as both recorded dependencies.
4. Every complex has a K-injective resolution K -> I: the first existential chooses
   `I`, `s : ∀ K, K ⟶ I K`, with `∀ K, IsKInjectiveResolution T R (s K)`.
   Verdict: exact; the recorded dependency abbreviation is `QuasiIso f ∧ I.IsKInjective`.
   Mathlib's `IsKInjective` is the null-homotopy criterion of 070H, equivalent to the
   node's Hom-complex acyclicity criterion by applying it to all shifts of acyclic
   complexes. No alternative predicate is introduced.
5. Functorially up to chain homotopy: `φ` assigns a chain map to every input chain map;
   the identity and composition clauses impose functor laws on homotopy classes.
   The `Homotopy f g → Homotopy (φ f) (φ g)` clause makes this assignment well-defined
   on homotopy classes, and `Homotopy (s K ≫ φ f) (f ≫ s L)` makes the resolution maps
   natural there. Verdict: exactly the stated functoriality. All homotopies are
   propositionally truncated by `Nonempty`; no strict laws or coherent higher data
   are demanded. Choice of representatives gives the converse interpretation.
6. Two resolutions of one object are chain-homotopy equivalent: the second conjunct
   quantifies every `K I J`, both maps `s t`, and both resolution hypotheses, and
   concludes `Nonempty (HomotopyEquiv I J)`. I read Mathlib's `HomotopyEquiv` fields:
   one map each way and homotopies of both composites to the identities.
   Verdict: exact. Compatibility with the augmentations is in the node's proof,
   but is not a separate clause of its statement and is not added to the conclusion.
7. A bounded-below complex of injectives is K-injective: the third conjunct quantifies
   `I` and `d : ℤ`, assumes `I.IsStrictlyGE d` and `∀ n : ℤ, Injective (I.X n)`, and
   concludes `I.IsKInjective`. I read `IsStrictlyGE`, its strict-support definition,
   and `isZero_of_isStrictlyGE`: this is termwise vanishing below d, rather than
   cohomological boundedness. Verdict: exact; universal quantification over every
   witness d is equivalent to the bounded-below implication. Negative bounds are allowed.

Edge cases: K = 0 has the identity resolution, and identical resolutions have the
identity homotopy equivalence. The empty scheme and the zero ring yield zero sheaf
categories and satisfy all clauses. Degree-zero and single-degree injective complexes
are included, as are all integer lower bounds. No boundedness is assumed in clauses
one and two. No characteristic is excluded. There is no index family or nonemptiness
assumption; the integer degree set is the node's degree set. The universe u is explicitly
bound and the coefficient and sheaf universes agree with the dependency signatures.
No variables or universes are left unbound.

Independent searches (msearch.py records these in searches.jsonl):

- LeanFinder: “functorial replacement of unbounded complexes by homotopically injective
  complexes and uniqueness of resolutions”. Eight hits, including ordinary
  `InjectiveResolution.homotopyEquiv` and `injectiveResolutions`; these resolve objects
  using natural-number complexes and do not state this unbounded combined proposition.
- Loogle: `"IsKInjective"`. Twelve hits, including `isKInjective_of_injective`,
  `HomotopyEquiv.isKInjective`, and shifted K-injectivity; no combined statement.
- LeanSearch: “Unbounded complexes of sheaves of modules admit functorial K injective
  replacements”. Service returned Internal Server Error; unavailable, no verdict.
- Direct rg across Mathlib homological algebra and abelian-category files, the entire
  source `WeilConjectures/`, and project `lean/Sheaf/`, using
  `resolution.*[Hh]omotopy`, `[Hh]omotopy.*resolution`,
  `[Kk]Injective.*[Ee]xist`, and `[Ee]xist.*[Kk]Injective`.
  I opened the source's `GrothendieckAbelian/KInjectiveResolution.lean` in full:
  its replacement functor and natural transformation give existence, not all clauses.
  I also read `KInjectiveBridge`, `KInjectiveComputes`, and
  `KInjectiveDegreewiseExistence` in the project: these are respectively choice data,
  a bounded-below derived-functor comparison, and strict functorial existence with
  injective terms. None states this node. The bounded-below Mathlib theorem is already
  a proof dependency, not the combined proposition.
- Name collision search `kinjective_resolutions_exist|KInjectiveResolutionsExist` in
  `dag/lean_names_upstream.json`, Mathlib, source Lean, and project Lean: no matches.

Findings and changes: no statement or dependency mismatch, no new definition node,
no dependency module, and no statement correction. The sole repair completes proof
step 2 of the docstring with the node's omitted augmentation-compatibility argument:
the comparison carries s to t up to homotopy because both lift Qt. The theorem's
signature and the node's `lean.statement` are unchanged and checked verbatim equal.
The sole theorem still has proof `sorry`; there are no definitions, hollow data,
private notions, local notation, or local instances. The one import supplies the used
resolution predicate and its infrastructure; all Lean lines satisfy the 100-character
limit, and module/declaration docstrings identify the source and blueprint node.

Second-reader validation: scompile.py compiled the repaired 65-line module on the
server in 2.2 seconds, exit code 0, with no errors or warnings. No local build was run.
