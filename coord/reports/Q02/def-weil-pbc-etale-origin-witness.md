## Worker report

The module `Sheaf/Paper/EtaleOriginWitness.lean` defines
`AlgebraicGeometry.ProEtale.EtaleOriginWitness`. For a scheme `T`, finite ring `Λ`
with discrete topology, and `K` in the bounded-below pro-etale derived category, it
stores (1) an etale bounded-below derived object `L` and (2) an isomorphism `alpha`
from the termwise exact comparison image of `L` to `K`. Thus the displayed pair is
retained as data, rather than reduced to an existential proposition.

The Lean binders render the node hypotheses as follows: `T : Scheme.{u}` is the
scheme; `Λ : Type (u + 1)` with `[Ring Λ] [Finite Λ] [TopologicalSpace Λ]
[DiscreteTopology Λ]` is a finite discrete (possibly noncommutative) ring; and
`K : FiniteCoefficientDerivedCategoryPlus T Λ` is the pro-etale `D⁺` object. The
field `L` is `DerivedCategory.Plus (Sheaf T.smallEtaleTopology
(ModuleCat.{u + 1} Λ))`, the etale `D⁺` object. The field `alpha` is the specified
isomorphism
`(finiteCoefficientComparison T Λ).mapDerivedCategoryPlus.obj L ≅ K`, rendering
`ν_T^* L ≅ K` using the canonical module comparison construction.

The dependency declarations used are `AlgebraicGeometry.ProEtale.FiniteCoefficientDerivedCategory`,
`AlgebraicGeometry.ProEtale.FiniteCoefficientDerivedCategoryPlus`, and
`AlgebraicGeometry.ProEtale.finiteCoefficientComparison` from
`Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`; the comparison site declaration is
`AlgebraicGeometry.Scheme.proEtaleSiteComparison` from
`Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`; bounded derived categories use the
recorded Mathlib declaration `DerivedCategory.Plus`.

Edge cases checked include the zero ring and zero derived object, the empty scheme,
connected and disconnected schemes, noncommutative finite rings (e.g. matrices over
`F₂`), and arbitrary integer lower bounds in `D⁺` (including shifted complexes).
No commutativity, Noetherian, nonemptiness, or degree-zero restriction is added.

Searches: the supplied LeanFinder/Loogle/grep searches in the node found no retained
origin-pair declaration; I additionally ran `rg` over `lean/Sheaf` and
`WeilConjectures` for `EtaleOriginWitness`, `plusEtaleOrigin`, and comparison-derived
origins. Existing `DerivedCategory.plusEtaleOrigin` is only an existence/object
property and does not retain a chosen pair, so it is not identical. The module was
compiled with `scompile.py` successfully. The previously absent coefficient dependency
landed during this task, so its published module and record are reused without changes.


Fresh searches made for this task:

- `msearch.py leanfinder`, query “A chosen bounded below etale origin is an etale
  derived object together with an isomorphism of its proetale comparison inverse image
  to a given object”: eight ring-theoretic etale hits, no retained witness.
- `msearch.py loogle`, query `CategoryTheory.Functor.essImage`: twelve hits, including
  `essImage`, `witness`, and `getIso`. Read their full signatures and bodies in
  Mathlib/CategoryTheory/EssentialImage.lean. These assert existence in Prop or extract
  a classical choice, rather than defining the type of specified pairs.
- `msearch.py grep`, query `EtaleOriginWitness|plusEtaleOrigin|structure.*Preimage`:
  ten general preimage hits, no matching definition.
- `rg` over Mathlib, slopmaster2 `WeilConjectures`, and shared `lean/Sheaf` for the
  witness name and exact item id found no existing retained witness. Read upstream
  `WeilConjectures.SixFunctors.ProEtale.Derived.Comparison` and its
  `DerivedCategory.plusEtaleOrigin` object property: this is an existence predicate,
  so it does not define the requested data type. Read the current server source with
  `scompile.py --source Sheaf.AlgebraicGeometry.ProEtaleFiniteModules` and the now
  landed dependency's full Lean record before reusing it.

There are no new nodes, dependency repairs, statement corrections, disputed statements,
or postponed proofs in this delivery. The independent second reader writes its own
reading after this worker finishes.

## Second reading by Q02

Independent second reading on 2026-10-16. I opened the sandbox node and complete
Lean module, the three dependency nodes and their recorded signatures, the full
`ProEtaleFiniteModules` and `ProEtaleSiteComparison` modules, upstream
`SixFunctors.ProEtale.Derived.Comparison`, and the implementation of
`Functor.mapDerivedCategoryPlus`. I read the exact master blueprint source for
this item (order 1289) on the server, since literature source files are absent
from the local shared checkout. Its displayed pair and retention sentence agree
verbatim with the node. I also read the enclosing proper-base-change sketch,
the finite-coefficient blueprint definition (order 1233), and Stacks
`proetale.tex`, section-comparison (Tag 099R), opening paragraph and site-choice
footnote. The latter assumes an arbitrary scheme and compatible site bounds;
it adds no Noetherian, nonempty, characteristic, or properness condition to the
comparison construction. Properness belongs to the surrounding theorem's
morphism, not to this witness definition.

Object/hypothesis/clause inventory and Lean match:

1. A scheme T: `T : Scheme.{u}`. Verdict: exact; T is arbitrary, with no
   geometric-property instance. The scheme/site universe u is explicitly bound.
2. Finite discrete ring coefficients, supplied by the coefficient-category
   dependency: `Λ : Type (u + 1)` with `[Ring Λ] [Finite Λ] [TopologicalSpace Λ]
   [DiscreteTopology Λ]`. Verdict: exact finite left-ring coefficients; no
   commutativity or nontriviality is assumed. The topology is the unique discrete
   topology required by the source, and is already part of the dependency API.
3. A fixed pro-etale bounded-below derived object K:
   `K : FiniteCoefficientDerivedCategoryPlus T Λ`. Verdict: exact.
   I unfolded the dependency: this is `DerivedCategory.Plus` of
   `FiniteCoefficientModules T Λ`, with `HasDerivedCategory.standard`;
   the modules are the recorded ringed-site modules over the actual
   sheafification of continuous functions on connected components. It is not
   an arbitrary sheaf category or a condensed-coefficient category.
4. Chosen etale object L in D-plus:
   `L : DerivedCategory.Plus
   (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))`.
   Verdict: exact. The dependency's `FiniteCoefficientEtaleDerivedCategory`
   uses this same fixed-ring encoding. Its canonical
   `finiteCoefficientEtaleRealization` identifies it with modules over the
   sheafification of the constant ring presheaf, including noncommutative
   rings. Mathlib `DerivedCategory.Plus` is the full subcategory of the
   standard t-structure's `plus`, defined by an existential integer lower bound;
   `DerivedCategory.isGE_iff` gives the cohomological interpretation.
5. The inverse image is the specified comparison functor nu-star:
   `finiteCoefficientComparison T Λ`. Verdict: exact. Its definition is
   `comparisonUpperStar (ModuleCat.{u + 1} Λ) T` followed by the canonical
   `finiteCoefficientRealization T Λ`. The former is the same functor appearing
   in `Scheme.proEtaleSiteComparisonModules`; the latter is associated module
   sheafification along constant scalar sections. Neither is an arbitrary
   equivalence or arbitrary map. Their recorded additivity and exactness
   instances allow termwise passage to the derived category without an extra
   hypothesis on the witness.
6. Chosen isomorphism alpha from nu-star L to K:
   `alpha : (finiteCoefficientComparison T Λ).mapDerivedCategoryPlus.obj L ≅ K`.
   Verdict: exact, including its direction. The upstream implementation of
   `mapDerivedCategoryPlus` restricts `mapDerivedCategory` using the full
   bounded-below subcategories and preserves the same lower bound. Thus this
   is precisely the termwise exact derived comparison, not a right derived
   direct image or a degree-zero construction. Isomorphisms in these full
   subcategories are the ambient derived isomorphisms.
7. Retain the pair, rather than only its existence, for later transport:
   `structure EtaleOriginWitness ... where` with the two data fields `L` and
   `alpha`. Verdict: exact. The definition is a data type, not Prop,
   `Nonempty`, an existential proof, or a classical selection of one origin.
   The binders fix T, the coefficient ring and K before the chosen pair;
   there is no uniqueness assertion or additional transport theorem.

Edge cases: the zero coefficient ring is allowed by `Ring` (no `Nontrivial`
binder), and zero derived objects are not excluded. Empty and disconnected
schemes are allowed. No characteristic restriction, invertible integer, finite
Tor dimension, constructibility, bounded-above condition, or degree-zero
restriction occurs. Every integer lower bound and every shift allowed in
D-plus remains covered. There is no index set or natural-number parameter in
this definition, so empty-index and n = 0 issues introduce no further cases.
The coefficient and module universe u+1 agrees with the recorded dependencies;
u is arbitrary, and there is no equation forcing the site's object and
morphism universes to coincide. Finite coefficient rings can be represented in
this coefficient universe. All variables are bound with `autoImplicit false`;
no extra `HasDerivedCategory` or smallness assumption is required of callers.

Fresh independent duplicate searches, using different descriptions from the
worker's searches:

- `msearch.py leanfinder`: “A specified preimage object and a chosen comparison
  isomorphism along an exact functor between bounded below derived categories”.
  Eight results, principally exact-derived-functor and Ext constructions;
  none defines the specified origin-pair type.
- `msearch.py loogle`: `CategoryTheory.StructuredArrow`. Twelve hits; I read
  the actual constructor and projections. Structured arrows retain an
  arbitrary morphism, not the required comparison isomorphism, and do not
  already define this witness.
- `msearch.py grep`: `structure.*(IsoFiber|Fiber|Origin)|def.*(isoFiber|preimage)`
  in Mathlib CategoryTheory. Results included preimages and fiber machinery.
  I opened `Functor.Fiber`: its object condition is equality `p.obj a = S`,
  not a chosen isomorphism. `Functor.essImage` is existential with `Nonempty`
  isomorphism; `witness`/`getIso` select data from its proof. None is this type
  of arbitrary specified pairs.
- Direct `rg` searches of Mathlib, slopmaster2 `WeilConjectures`, shared
  `lean/Sheaf`, the exact shared `lean/WeilConjectures` framework, and the
  upstream-name index checked origin, preimage, lift and fiber spellings as
  well as `EtaleOriginWitness`, `plusEtaleOrigin` and the blueprint id.
  I opened `DerivedCategory.plusEtaleOrigin`: it is an `ObjectProperty`
  obtained by mapping the bounded-below property, not retained origin data.
  Upstream mentions of the blueprint id use this existence property and
  do not supply a competing witness declaration. No exact existing
  definition was found. The framework manifest in
  `coord/pefw-upstream-framework.md` was also read.

No mathematical or signature mismatch was found, so the Lean module and node
record are unchanged. There are no new nodes, dependency repairs, or statement
corrections to audit, and no citer correction audit is applicable. The module
and main declaration docstrings identify the source and blueprint id; this
is a definition node with empty proof and proof-dependency lists, so no proof
steps are missing. It has real fields, no hollow data, no postponed theorem,
no proof, no private copy, and no file-local notation or instance.
The node's `lean.statement` was checked verbatim against the structure header.

Validation: `scompile.py Q02 def-weil-pbc-etale-origin-witness` on the delivered
module passed cleanly, with its coefficient dependency compiled by the wrapper
in 4.9 seconds and this module in 1.8 seconds, each within the standard
60-second limit. No errors or warnings were emitted. The second reading adds
this clause-by-clause report only; it does not rewrite correct Lean.
