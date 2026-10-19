## Worker report

Existing declaration: `AlgebraicGeometry.Etale.hasTorAmplitudeIn_iff_exists_flatModel`,
module `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel`, slopmaster2,
lines 91–107. Read its complete signature, docstring and proof, together with
`IsBoundedFlatComplex` at lines 46–50 and the surrounding variable binders.
The node already points to this exact theorem; its incomplete attachment is replaced
by a complete existing-declaration record. No new module or notion is needed.

Hypothesis and clause correspondence:

- A commutative ring Λ: surrounding `(Λ : Type (u + 1)) [CommRing Λ]`.
- A scheme X: surrounding `{X : Scheme.{u}}`; Y is unused and is not a theorem parameter.
- Arbitrary integer endpoints: `(a b : ℤ)`.
- The explicit order hypothesis: `(_hab : a ≤ b)`.
- K in the derived category of small-etale Λ-module sheaves:
  `(K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))`.
- Bounded constructibility: `_hK : DerivedCategory.boundedConstructible
  (ModuleCat.{u + 1} Λ) X K`. Read its definition in
  `WeilConjectures.CategoryTheory.DerivedCategory.Constructible`, lines 98–103:
  bounded for the canonical t-structure and constructible homology in every degree.
- Tor amplitude in [a,b]: `DerivedCategory.hasTorAmplitudeIn Λ X a b K`.
  Read `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`, lines 63–75:
  every sheaf F, every integer q outside the interval, has zero q-th homology
  after derived tensor with F placed in degree zero.
- Both directions of equivalence: `↔`.
- A cochain complex of the same sheaves: `∃ P : CochainComplex
  (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ`.
- Flat and zero outside [a,b]: `IsBoundedFlatComplex Λ a b P`, defined as
  `(∀ q : ℤ, q < a ∨ b < q → IsZero (P.X q)) ∧
  ∀ q : ℤ, ObjectProperty.flat (P.X q)`.
- An isomorphism from K to the image of P: `Nonempty (K ≅
  (_root_.DerivedCategory.Q).obj P)`.

Dependency declarations inspected:

- `def-weil-pbc-etale-site`: Mathlib.AlgebraicGeometry.Sites.Etale,
  `AlgebraicGeometry.Scheme.smallEtaleTopology` (lines 49–52), and
  `ofArrows_mem_smallEtaleTopology_iff` (lines 61–66); also Mathlib.AlgebraicGeometry.
  Morphisms.Etale, `AlgebraicGeometry.Scheme.Etale` (lines 157–159), deriving finite limits.
  These are precisely the small site in the existing theorem.
- `def-weil-pbc-etale-sheaves`: read its full mixed record. It explicitly accepts
  `Sheaf X.smallEtaleTopology (ModuleCat.{u+1} Λ)` for six-functor and constructible
  material alongside the constant-ring-sheaf encoding. No replacement definition
  is needed. The record names `WeilConjectures.AlgebraicGeometry.EtaleSheaves`;
  that source path is absent locally, but its set-sheaf declarations are present
  in `lean/Sheaf/AlgebraicGeometry/EtaleSheaves.lean` and were inspected there.
  Those set-sheaf predicates are not used by this theorem. Its used declaration
  is Mathlib's `CategoryTheory.Sheaf`, together with `ModuleCat`.

Edge cases checked by reading the signature and definitions: a=b is included;
negative endpoints are allowed; the zero object and empty scheme are not excluded;
the zero coefficient ring and all characteristics are allowed. No finite-ring,
Noetherian, nonempty, or invertibility hypothesis occurs. The universe convention
is exactly the recorded six-functor convention, with modules one universe above schemes.
No requirement that the terms of P be constructible is added: that is a distinct
upstream theorem, `hasTorAmplitudeIn_iff_exists_flatConstructibleModel`.

Searches actually run through msearch.py:

- LeanFinder: "etale tor amplitude if and only if existence of bounded flat model";
  eight unrelated ring-etale/smooth results, no exact Mathlib theorem.
- Loogle: "hasTorAmplitudeIn"; zero hits, unknown identifier.
- LeanSearch: "Tor amplitude bounded complex flat sheaves"; service unavailable,
  Internal Server Error (not treated as a negative search).
- Mathlib grep: "hasTorAmplitudeIn_iff_exists_flatModel"; zero hits.
- rg of upstream WeilConjectures for the theorem name and node id: exact theorem
  at FlatModel.lean:91, with additional references in pro-etale flat models and generation.
- rg of lean/Sheaf for the theorem name and node id: no matches.
- rg of dag/lean_names_upstream.json for the theorem name: no matches.

The supplied lean_audit.slopmaster2 record marks the theorem closed and sorry-free;
its complete local proof contains no sorry. No statement correction or dispute.
Server availability and delivery validation are checked by deliver2.py --no-push,
which imports this existing module and checks the declaration through scompile.py.

## Second reading by NM

I independently opened the item JSON, its sandbox copy, and the complete source
module FlatModel.lean, including its surrounding binders, definitions and proof.
The source place of this node is this Lean theorem, not a Stacks tag; there is
no source-wide Stacks hypothesis to recover. The two copies have the same natural
statement and statement dependencies; there is no statement_change.

Object, hypothesis and conclusion checklist, in the node's order:

1. Arbitrary commutative coefficient ring: `(Λ : Type (u + 1)) [CommRing Λ]`
   in the source's variable declaration. Match: no field, finiteness, nontriviality
   or torsion assumption. Λ is an explicit theorem argument.
2. Arbitrary scheme: `{X : Scheme.{u}}`. Match: no Noetherian or separated
   assumption. The surrounding Y does not occur and is not an inferred parameter.
3. Two integers and their order: `(a b : ℤ) (_hab : a ≤ b)`. Exact match,
   including the order hypothesis even though the existing proof does not use it.
4. Object of the derived category of small-etale Λ-module sheaves:
   `(K : _root_.DerivedCategory
   (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))`. Exact match.
5. Bounded constructibility of that same K:
   `(_hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K)`.
   Opened Constructible.lean:98–103 and the preceding constructibleHomology
   definition: canonical-t-structure boundedness and constructible homology in
   every integer degree. Match; no finite Tor hypothesis hidden in this predicate.
6. Tor amplitude in the specified interval:
   `DerivedCategory.hasTorAmplitudeIn Λ X a b K`. Opened Coefficients.lean:63–75:
   for every sheaf F and integer q outside [a,b], the q-th homology of the derived
   tensor with F in degree zero is IsZero. This is exactly the notion the node
   explicitly points to. No independent lower test universe occurs.
7. Equivalence: `↔`. Match, both implications, with K and the interval fixed
   before the existential model.
8. Model: `∃ P : CochainComplex
   (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ`. Match, same sheaves
   and integer cochain indexing, with no termwise constructibility condition.
9. Termwise flat and zero outside [a,b]: `IsBoundedFlatComplex Λ a b P`.
   Opened its definition at FlatModel.lean:46–50: all q outside the interval
   satisfy `IsZero (P.X q)` and all q satisfy `ObjectProperty.flat (P.X q)`.
   Opened FromJoel/CategoryTheory/Abelian/Flat/Basic.lean: flat means exactness
   of tensorLeft and tensorRight, the ordinary flatness notion in this symmetric
   module-sheaf category. Match; zero is categorical zero, not mere acyclicity.
10. Isomorphism with the derived image of that same P:
    `Nonempty (K ≅ (_root_.DerivedCategory.Q).obj P)`. Exact match, with the
    stated orientation and existential isomorphism rather than an equality.

Dependencies independently inspected: both dependency JSON files in
sec-abelian-varieties, Mathlib's Sites/Etale.lean:49–66 and
Morphisms/Etale.lean's Scheme.Etale category, and the project's
Sheaf/AlgebraicGeometry/EtaleSheaves.lean. The site declaration is the topology
on etale X-schemes, with covering families characterized by joint surjectivity.
The mixed etale-sheaves record expressly accepts ModuleCat-valued sheaves for
six-functor/constructible statements. Its set-sheaf predicates serve other clauses
and are not substituted here. The canonical upstream EtaleSheaves module named
by that dependency record is absent in this local source checkout; the project's
corresponding source was read. None of those absent set-sheaf declarations is
used by this attachment, whose imports and actual used objects are checked on
the server. No missing notion, dependency module, or new node is needed.

Edge cases: a=b (including a=b=0) is covered, as are negative endpoints; a>b is
outside the node because of hab. Zero K, zero Λ and the empty scheme are not
excluded. There is no characteristic or invertibility assumption. There is no
index-family parameter whose empty case could be lost. The arbitrary universe u
and coefficient/module universe u+1 agree with the source and the accepted
six-functor encoding; smaller coefficients can also inhabit the larger universe.
All variables and universes are bound. No hollow definition or new proof is
introduced: this is reuse of an existing theorem, not a new sorry theorem.
The new-module docstring/proof-plan requirements do not require rewriting the
existing module; the item's proof and proof_deps are empty. I read the source
proof: it converts homology-based amplitude to t-structure amplitude, applies
the generic flat-model theorem, translates strict degree bounds to the defined
bounded-flat predicate, and reverses the supplied isomorphism in each direction.

Independent searches, using different conceptual words from the first reader:

- LeanFinder via msearch.py: "complex of flat sheaves supported in an interval
  represents derived object Tor dimension". Eight results about derived
  t-structure bounds, including exists_iso_Q_obj_of_isGE_of_isLE; none supplies
  termwise flatness or this exact equivalence.
- Loogle via msearch.py: "IsBoundedFlatComplex". Unknown identifier; zero hits.
- LeanSearch via msearch.py: "bounded flat resolution derived tensor amplitude
  of sheaves". Internal Server Error; unavailable, not negative evidence.
- rg for flatModel, BoundedFlat and flat/complex phrasing across lean/Sheaf,
  upstream Etale/Derived/Finiteness and Mathlib's DerivedCategory directory.
  The exact upstream theorem is found in FlatModel.lean; nearby flat-model
  reduction results and project ringed-space/affine flat models are different
  statements. No replacement module is warranted.

Mismatches found: none. Changes: appended this independent second reading only;
the existing-declaration record and natural statement are retained. A literal
comparison against the source confirmed lean.statement is exactly the theorem
signature before `:= by`, including its line breaks. Server declaration checking
and preflight are performed by deliver2.py through scompile.py; no local compiler
or global build is used.
