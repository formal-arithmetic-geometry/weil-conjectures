## Worker report

The delivery states `WeilConjectures.integral_constructible_internalHom` in
`Sheaf.Paper.IntegralConstructibleInternalHom`. Its proof is `sorry`.
The canonical map is constructed in `Sheaf.Paper.IntegralHomReductionComparison`
as the tensor-Hom transpose of reduced evaluation, with normalized tensor models.
No mathematical proof is filled in. The auxiliary model-existence and projection-existence theorems are also `sorry`;
both belong to the canonical-comparison definition node and have complete proof docstrings.

Hypotheses and clauses:

- The global finite-field datum is `D : FiniteFieldDatum.{u}`. Its fields give the
  finite field, its characteristic prime and fixed algebraic closure `D.k`.
- The coefficient prime is `l : ℕ`, `[Fact l.Prime]`, `hl : l ≠ D.p`.
  `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]` and
  `[FiniteDimensional (Padic l) E]` give exactly the finite extension. Its ring of
  integers, uniformizer and finite quotient rings are the recorded Padic constructions.
- `X : Scheme.{u}`, `[X.Over (Spec (CommRingCat.of D.k))]` specifies the k-scheme.
  `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` on its structure morphism
  specify separated finite type, without assuming properness.
- `K L : completedIntegralDerivedCategory l E X D hl` are objects of the ambient
  derived category over the completed, rather than discrete constant, ring sheaf.
  The completed sheaf is the recorded inverse limit of constant finite quotients.
- `hK` and `hL` assert `boundedConstructibleDerivedCompleteIntegral` membership.
  This is the recorded predicate: derived completeness, finite-torsion constructibility
  of every positive reduction, and one common interval for their cohomological supports.
- `homReductionHom (completedIntegralCommRingSheaf ...)` is an abbreviation for the
  recorded `CategoryTheory.derivedInternalHomOfUniverses`, with standard localization.
  Its application to `(op K, L)` is the ambient H of the node.
- The first conjunct asserts the same integral membership predicate of H.
- The second conjunct is `∀ n : ℕ, IsIso (integralHomReductionComparison ... n K L)`.
  Index n denotes exponent n+1, so this covers exactly all positive finite quotients,
  including the residue quotient at index zero. The arrow is A_n-linear and lands in
  the A_n-derived category; the statement does not discard its coefficient action.
  Its target is precisely the recorded finite-coefficient internal Hom of the two
  recorded reductions. It is defined by transposing reduced evaluation, not by
  choosing an unrelated isomorphism of its source and target.
- The quantitative conjunct quantifies over `a b c e : ℤ`, with `a ≤ b` and `c ≤ e`,
  and over `d : ℕ` with `topologicalKrullDim X ≤ (d : WithBot ℕ∞)`. Natural d is exactly
  the nonnegative integer dimension bound in the node.
- The two uniform input Tor hypotheses are `∀ n, HasProEtaleTorAmplitude X
  (Padic.coefficientExtensionRing l E (n+1)) (reduction.obj K/L) ...`.
  The output uses that same predicate over that same finite quotient, and endpoints
  `(c - b - 2 * (d : ℤ))`, `(e - a + 2 * (d : ℤ))`. It does not instead measure Tor
  amplitude after restriction to the integral coefficient ring.

Dependency declarations used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` (transitively through the
  coefficient definitions): `Padic.finite_coefficientExtensionRing`, and the underlying
  coefficient ring/uniformizer constructions of `CoefficientExtension`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsSeparated`, the
  separated clause of the recorded proper-morphism definition. The proper class is
  intentionally not imposed: the node requires separated finite type.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`
  together with `QuasiCompact` for finite type.
- `Sheaf.Paper.CompletedIntegralCoefficients`: `completedIntegralCoefficientSheaf`,
  `completedIntegralCommRingSheaf`, `integralCoefficientSheaf`,
  `integralCoefficientCommRingSheaf`, `completedIntegralDerivedCategory`, and the
  actual limit projections and restriction-of-scalars functor.
- `Sheaf.Paper.DerivedCompleteIntegralDetailed`:
  `boundedConstructibleDerivedCompleteIntegral`.
- `Sheaf.Paper.IntegralDerivedReduction`: `integralDerivedReduction`, its universal
  left-derived counit, and its ordinary additive change-of-rings functor.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses` and its localization invariance.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`:
  `AlgebraicGeometry.Scheme.HasProEtaleTorAmplitude`.
- `Sheaf.Paper.IntegralReductionTowerWellDefined`: `integralTowerTensorSection`,
  reused for the sheafified `1 tensor x` coordinate of the scalar unit.
- Proof-only imports: `Sheaf.Algebra.Homology.DerivedTensor`,
  `Sheaf.Paper.IntegralResidueTor` and
  `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
  `lem-coef-integral-hom-reduction` and `cor-weil-finite-constructible-hom` have no
  recorded statement modules in the base and so have no proof-only import yet.
  The former's needed comparison *definition* is supplied here. Neither unproved
  lemma is assumed as a hypothesis of the main theorem.

Edge cases checked before writing: the empty scheme has Krull dimension bottom and
allows d=0; all object statements remain meaningful. Zero K or L is not excluded and
permits any ordered Tor interval. The residue level n+1=1 is included. Negative endpoints
are integers without truncation. Equal endpoints and d=0 retain the exact formula.
There is no global site-perfectness assumption. The site keeps object universe u+1 and
morphism universe u, with coefficient and module universe u+1. The size choices are those
of the recorded integral membership and finite Tor interfaces.

Searches: msearch LeanFinder for "adic constructible derived category closed under derived
internal Hom with reduction modulo a uniformizer" returned eight local-cohomology,
condensed-module and generic derived-category results, none matching. Loogle query
`"derived", "Hom"` returned twelve generic derived-category declarations. Mathlib grep
`internalHom|derivedHom|adic` in Algebra/Homology returned seven unrelated lines.
LeanSearch "derived internal Hom reduction adic constructible sheaves" was unavailable
with Internal Server Error. LeanFinder for the scalar-extension transpose of evaluation
returned eight ordinary ModuleCat evaluation/adjunction declarations, and Loogle
`"Hom", "tensor"` returned twelve ordinary tensor-product maps. The exact search
queries and returned declaration lists are recorded in the new node.
Project searches for the item id and integral Hom/reduction patterns found
`AlgebraicGeometry.Etale.boundedConstructibleIntegral_derivedHom` in upstream
`SixFunctors/Etale/Derived/IntegralCoefficients.lean`, read in full with its docstring.
It uses discrete small-etale coefficient sheaves and compares after restriction of
scalars, so it is not the completed small-pro-etale statement here. The project
`integralDerivedInternalHom` uses the same recorded Hom but does not supply the reduction
comparison or this constructibility/Tor theorem. Searches of the DAG and blueprint
references found the unstated reduction lemma, but no separate definition of its
canonical comparison. Exact helper declaration names have no Mathlib/upstream/project
collision. Current server sources of the recorded Hom and integral membership interfaces
were read with scompile --source.

No statement correction or disputed mathematical statement is proposed.

## Second reading by NH

I reread the item node, its source paragraphs, the two delivered modules, and
the signatures of every recorded dependency. The node introduces the global
finite-field datum (D), a prime ℓ different from its characteristic, a
finite extension (E/ℚ_\ell), and a scheme (X) over the fixed algebraic
closure. The Lean binders are respectively `D : FiniteFieldDatum`,
`l : ℕ` with `[Fact l.Prime]` and `hl : l ≠ D.p`, `E` with `Field`,
`Algebra (Padic l) E`, and `FiniteDimensional`, and `X` with `X.Over` over
`Spec (CommRingCat.of D.k)`. The separated and finite-type assumptions are
rendered by `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` on the
same structure morphism. Verdict: exact; no properness, smoothness,
connectedness, or nonemptiness was added.

The node's completed coefficient sheaf and ambient derived category are
rendered by `completedIntegralDerivedCategory l E X D hl`. The two inputs are
ambient objects `K L` with the node's full predicate
`boundedConstructibleDerivedCompleteIntegral` as `hK` and `hL`; this predicate
contains derived completeness, every positive finite-level constructibility
condition, and one uniform cohomological interval. Verdict: exact.

The ambient object (H=R\mathcal Hom(K,L)) is exactly
`(homReductionHom (completedIntegralCommRingSheaf l E X D hl)).obj (op K, L)`.
The first conclusion conjunct applies the same integral predicate to this H.
The second is `∀ n : ℕ, IsIso (integralHomReductionComparison ... n K L)`.
The comparison declaration in `IntegralHomReductionComparison.lean` has the
source reduction of H and the target internal Hom of the two reductions, and
its construction is the inverse normalized tensor comparison followed by
reduced evaluation and the target Hom transpose. Thus it retains the finite
coefficient action and is the evaluation-defined canonical map, rather than an
arbitrary object isomorphism. Lean uses `n + 1` for the positive level, so
Lean's `n = 0` is the node's (A_1), and every (A_m) for (m \ge 1) occurs.

The quantitative conclusion has the node's quantifier order and clauses:
`a b c e : ℤ`, `a ≤ b`, `c ≤ e`, `d : ℕ`, and
`topologicalKrullDim X ≤ (d : WithBot ℕ∞)`, followed by the two uniform
input `HasProEtaleTorAmplitude` hypotheses and the output amplitude. The output
endpoints are exactly `c - b - 2 * (d : ℤ)` and
`e - a + 2 * (d : ℤ)`, over the same coefficient ring and the reduction of
the same H. Verdict: every hypothesis and conclusion clause agrees.

I checked edge cases directly against these types: the empty scheme is allowed
and has bottom Krull dimension (so `d = 0` is admissible); zero K or L is not
excluded; negative or equal integer endpoints are allowed subject only to the
stated order hypotheses; no nonempty index type is introduced; and the residue
level is included by `n = 0`. The site object and morphism universes remain
distinct, with no universe equality imposed.

For the new definition node `def-sf-integral-hom-reduction-comparison`, I
checked its statement against the blueprint comparison paragraph and Stacks
Tags 08J7, 06YY, and 0A90. Its module supplies the signed total tensor,
sectionwise Hom-complex currying, K-flat representative comparisons, the
ordinary unit (x \mapsto 1 \otimes x), and the derived counit square before
defining the displayed comparison. The helper declarations are all documented
with that node's source and blueprint tag; the data of the definition is real,
and only the named existence theorem is postponed. Searches of Mathlib,
`WeilConjectures`, and shared `lean/Sheaf` found no declaration collision or
existing completed pro-etale comparison. LeanSearch/LeanFinder/Loogle queries
returned only generic derived-category or tensor/Hom results.

No mismatch was found and no file or node statement was changed. The only
delivery delta is the item's `lean` record and its added dependency on the new
comparison definition; the new definition node carries its own module and
record. The required `scompile.py` checks have been run on both modules; the
server confirmation compiled the comparison and corollary within the 60-second
per-file limit with no errors or non-sorry warnings.

## New nodes

`def-sf-integral-hom-reduction-comparison` records the missing canonical arrow,
with source the comparison statement and second proof paragraph of blueprint order 2134
and Stacks Tags 08J7, 06YY and 0A90. Its module supplies the actual transpose formula.
The model-existence theorem supplies normalized tensor/Hom models: their
K-flat representative comparisons, literal local-section currying, unit `1 tensor x`,
ordinary total tensor comparison, and derived counit square. These are universal data
fixed up to unique compatible isomorphism, not a bare choice of an arbitrary Hom map.
Inverting the derived tensor comparison and reducing evaluation are real categorical
compositions. Invertibility of the resulting Hom comparison is asserted only by the main
corollary. The node cites the existing coefficient, reduction, Hom, K-flat and sheaf tensor
nodes and is cited by the item. Its searches are the actual msearch records above,
plus DAG/blueprint and source greps. No existing definition node carries this arrow.


## Earlier second reading (a previous round; superseded)

I independently read the item and both sandbox modules, the blueprint item at
order 2147, the biduality unit `_section.md`, the six-functors chapter, the
completed-coefficient and integral-category source definitions, and the
comparison lemma at order 2134. The untracked literature is available at
`/home/ubuntu/weil-launcher-nt/literature/`; the shared clone has only its index.
I also read Stacks `sites-cohomology.tex`, Tags 06YY (derived pullback on K-flat
representatives), 0A90 (Hom-complex currying), and 08J7 (the canonical derived
internal-Hom adjunction). These assume a ringed site, not site-perfect inputs.

The following is my object/hypothesis/conclusion inventory, matched directly
to the Lean signature rather than inferred from the first reader's report:

1. Global characteristic-p algebraic closure: `D : FiniteFieldDatum.{u}`.
   I opened `FiniteFieldFiber.lean`: its prime, positive exponent, finite
   cardinality, base field, algebra structure, and `IsAlgClosure` fields give
   precisely the stipulated datum. Verdict: exact.
2. Prime ell different from p: `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)`.
   Finite coefficient extension: `(E : Type u) [Field E]
   [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`.
   I read the coefficient construction: `coefficientExtensionRing l E m` is
   the quotient by the m-th power of the ideal of the chosen uniformizer in
   the spectral-absolute-value valuation ring. Verdict: exact; no extra
   field characteristic, completeness or unramified-extension hypothesis.
3. Separated finite-type k-scheme: `X : Scheme.{u}` with `X.Over (Spec
   (CommRingCat.of D.k))`, `IsSeparated`, `LocallyOfFiniteType`, and
   `QuasiCompact` on that same structure morphism. I opened the Mathlib
   separated and finite-type interfaces. Verdict: precisely the unit context;
   properness, smoothness, connectedness and nonemptiness are not assumed.
4. Completed coefficient sheaf and its ambient derived category:
   `completedIntegralDerivedCategory l E X D hl`. I opened
   `CompletedIntegralCoefficients.lean`: the source is the inverse limit of
   constant finite quotient ring sheaves on `Scheme.ProEt.topology X`, with
   Mathlib module sheaves and the standard derived localization. The
   commutative enhancement keeps its underlying ring data. Verdict: the
   completed pro-etale category in the node, not the discrete etale category.
5. Both inputs in the full integral subcategory: `K L` in that ambient category
   and `hK`, `hL : boundedConstructibleDerivedCompleteIntegral ... K/L`.
   I read the complete predicate, including its current source through
   `scompile.py --source`: it is derived completeness plus positive-level
   intrinsic finite-torsion constructibility and one ordered cohomological
   interval independent of n. Verdict: all and only the node's conditions.
6. Ambient H: `(homReductionHom (completedIntegralCommRingSheaf ...)).obj
   (op K, L)`. This abbreviation calls the recorded
   `CategoryTheory.derivedInternalHomOfUniverses`; I opened that declaration
   locally and through `scompile.py --source`. It localizes the Hom-complex
   bifunctor with canonical K-injective replacement in its second variable.
   Verdict: the recorded ambient derived internal Hom, without a private copy.
7. Closure: the first conjunct applies the same integral membership predicate
   to that very H. Verdict: completeness, constructible reductions and uniform
   boundedness are all asserted, not just one of them.
8. Canonical reductions: the second conjunct is `∀ n : ℕ, IsIso
   (integralHomReductionComparison D l hl E X n K L)`. I followed its full
   definition and arrow type: source is `integralDerivedReduction ... n` of H;
   target is the recorded Hom over `integralCoefficientCommRingSheaf ... n`
   of the two reductions. The morphism is the target currying inverse applied
   to the inverse scalar tensor comparison followed by reduced evaluation.
   Verdict: exactly the evaluation-defined A_n-linear comparison in the
   A_n-derived category. The comparison is not merely an arbitrary object
   isomorphism, and is not read after forgetting its A_n action.
9. Quantitative objects: `∀ a b c e : ℤ, a ≤ b → c ≤ e → ∀ d : ℕ,
   topologicalKrullDim X ≤ (d : WithBot ℕ∞) → ...`.
   `d : ℕ` represents precisely a nonnegative integer bound. I opened Mathlib's
   `topologicalKrullDim`: it is dimension from strict chains of irreducible
   closed subsets. Verdict: same dimension, endpoints and quantifier order.
10. Input Tor hypotheses: each is `∀ n : ℕ, HasProEtaleTorAmplitude X
    (Padic.coefficientExtensionRing l E (n + 1)) (reduction.obj K/L) ...`.
    I opened the Tor predicate: every degree-zero module sheaf is tested
    against the recorded K-flat derived tensor, with vanishing outside the
    ordered interval. Verdict: amplitudes over A_n itself, uniformly over n.
11. Output Tor conclusion: for every n the same predicate is applied to the
    reduction of the same H, with endpoints `c - b - 2 * (d : ℤ)` and
    `e - a + 2 * (d : ℤ)`. Verdict: the exact formula, over the same finite
    quotient ring, with no hidden restriction of scalars.

The natural index `n` throughout is exponent `n+1`; every positive exponent
is represented and no zero quotient is required. In particular n=0 in Lean
is the residue level. The empty scheme remains allowed, its dimension is
bottom, and d=0 is admissible. K=0 or L=0 is allowed without nonempty-support
conditions; equal endpoints, negative endpoints, and d=0 are retained. At a
point, shifted free coefficients in degrees r,s give the interval [s-r,s-r].
For the torsion input R/(varpi), its derived residue occupies [-1,0], so the
possible degree-one integral dual is compatible with the quantitative clause.
No index set or nonempty family is added. Universe u is arbitrary; the
pro-etale site has object universe u+1 and morphism universe u, while the
coefficient/module universe is u+1. The declarations do not identify the
site's object and morphism universes. They use the common ambient size of
the recorded integral-membership and finite-Tor interfaces.

I separately reviewed `def-sf-integral-hom-reduction-comparison` as a new node.
It is a definition of the missing canonical arrow, not a restatement of its
invertibility. Its blueprint source explicitly requires the evaluation-defined
comparison and its transposes; Stacks 0A90 and 08J7 specify the currying
used here. Its statement introduces every object and cites the recorded
coefficient, reduction, Hom, K-flat, sheaf tensor and reduction-tower notions.
The metadata has the required definition/split kind/status, empty proof and
proof dependencies, null match, creation record, ancestor/via, chapter/unit,
three search kinds, and declaration list. Every dependency node was opened;
I followed the Lean signatures of KFlat, HomComplex, IntegralDerivedReduction
and IntegralReductionTowerWellDefined in addition to those above.

In its module, `homReductionTotal` uses the existing sheaf tensor and signed
direct-sum totalization. `homReductionProjection` comes from the very
`homComplex_exists` witness used by `homComplexFunctor`, not from an unrelated
choice of product coordinates. `IsHomReductionCurry` checks evaluation on all
localized sections and summands. `HomReductionTensorModel.normalize` ties
the derived adjunction to this chain-level equation via the canonical
Hom/K-injective localization map. Its `natural` field fixes functoriality.
`IntegralHomReductionTensorData` fixes the ordinary scalar unit by
`integralTowerTensorSection ... 1 x`, the ordinary tensor comparison on these
sections, and the derived tensor comparison by the left-derived counit square
on all pairs of K-flat representatives. These universal/normalization data
fix the resulting arrow up to the compatible model isomorphisms, so the
existence theorem does not choose an unconstrained map. The definition itself
is a concrete composition and target transpose. The auxiliary theorem is
named, appears in `lean.declarations`, has the same matching DAG definition
statement, and has the four-step construction proof in its docstring. No
hollow data, completed proof, or extra theorem asserting invertibility was
introduced. There are no dependency repair modules in this packet.

Independent searches, with different wording from the first reader:

- LeanFinder via msearch: "Internal Hom preserves bounded constructible
  complexes over completed adic coefficients and commutes with quotient
  scalar extension". Eight hits, including `AdicCompletion.ofTensorProduct`,
  `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian` and
  `localCohomology.diagram`; none is this sheaf theorem or canonical arrow.
- Loogle via msearch: `"internalHom", "baseChange"`: zero hits.
- LeanSearch via msearch: "Canonical change of coefficients map for derived
  sheaf Hom given by tensor Hom adjunction": service unavailable, Internal
  Server Error, recorded rather than treated as a successful empty search.
- I independently ran rg on Mathlib Algebra/Homology and CategoryTheory for
  derived Hom and internal-Hom/base-change variants, and on both
  `WeilConjectures` and shared `lean/Sheaf` for integral Hom, duality,
  reduction comparisons and evaluation comparisons. I read
  `AlgebraicGeometry.Etale.boundedConstructibleIntegral_derivedHom` and
  `nonempty_iso_reductionModIdeal_derivedHom` in full: they use the discrete
  small-etale category and the latter compares after restriction to the
  integral coefficient category. They do not state this node or its arrow.
  `integralDerivedInternalHom` in `IntegralDerivedOperations.lean` is the
  same recorded internal Hom for unrestricted completed coefficients and
  supplies no reduction arrow or closure theorem. The helper names have no
  existing declaration collision. DAG and `blueprint_refs.py search` checks
  found the existing Hom-reduction lemma, but no existing separate definition
  of the normalized canonical comparison. Thus the module is retained.

H8/H9: the main docstring carries all five node proof steps, including the
empty-dimension case and tensor-unit justification of cohomological bounds.
Both modules give source/blueprint docstrings for every declaration, use the
standard namespace, bind every variable and universe under `autoImplicit
false`, and have no file-local notation, private definition or local instance.
The recorded primary signatures were checked against the files verbatim.

Mismatches and changes: no mathematical, dependency, or Lean-statement
mismatch was found. I left both Lean modules and node records unchanged and
added this independent reading, its source/interface checks, and new searches.
No statement correction is proposed, so no correction citer audit is required.

Validation: I reran the required `scompile.py` command on both sibling modules
in dependency order. The local preliminary comparison compile timed out at
60 seconds, and the wrapper's current-server confirmation completed cleanly:
`IntegralHomReductionComparison.lean` in 45.1 seconds and
`IntegralConstructibleInternalHom.lean` in 2.2 seconds, with no errors or
warnings. Every per-file invocation retained nice 19, two threads, and the
60-second limit. The transitive source-overlay rebuilds also passed.


## Worker repair of return L (2026-10-16)

Returned point: independent immutable-head compilation of
`Sheaf.Paper.IntegralHomReductionComparison` timed out after 60 seconds.
This repair changes the definition implementation and rechecks the entire packet;
it does not increase the time limit or divide a module into separate compile jobs.

A declaration-level `trace.profiler` run identified the expensive nested expression
`homComplex_exists.choose_spec.choose`. In the server profile its extracted proof
cost 16.2 seconds and the projection definition cost 23.1 seconds of kernel checking;
checking the following model structure also waited on this expression. Merely making
the projection generic or moving its normalization propositions did not cure the local
timeout, so those experiments are not the delivered interface.

The delivered repair states `homReductionHomProjections_exist` with precisely the
projection-limit, signed-differential and functoriality proposition for the already
recorded `homComplexFunctor`. Its proof is postponed as required in stage 2, and its
proof docstring explains the complete proof: unfold `homComplexFunctor` and apply
`Classical.choose_spec` to `homComplex_exists`. The statement is definitionally the
original choice-specification proposition; proof irrelevance therefore makes its
chosen projection family definitionally equal to the old family. The generic helper
`homReductionHomProjection` chooses from this smaller interface, and the original
`homReductionProjection` specializes it to the unchanged pro-etale universes.
This avoids repeatedly checking the large nested proof expression. It adds no new
hypothesis, no arbitrary projection, and no alternative Hom complex or comparison.
The new definition node explicitly records this proof interface and both helper
names are included in `lean.declarations`; their source/blueprint docstrings are in
the same owning module. The normalization fields of `HomReductionTensorModel` and
the main corollary's signature are unchanged.

I searched both new helper names in Mathlib, upstream WeilConjectures and shared
Sheaf sources with rg: no collisions. The existing sources and blueprint comparison
passage were reread. All edge cases and coefficient/site sizes listed in the worker
report remain applicable. The prior second reading above describes the previous
version; a fresh second reader must assess this repair before delivery.

The standalone `scompile.py` repair run completed all five local invocations
(preliminary comparison, both sandbox modules, and both library module paths),
without the server fallback. The comparison's preliminary and sandbox checks
were 35.0 and 25.0 seconds. The only diagnostics were two line-width warnings;
the two lines were then wrapped, and every delivered Lean line is now at most
100 characters. The required final dry run recompiles the exact wrapped files
and rejects any remaining warning. No compiler time limit was changed.

A text comparison against the full recorded `homComplex_exists` proposition also
confirmed exact agreement after replacing its bound functor by
`homComplexFunctor (R := R)` and ignoring whitespace. The three original
projection clauses and their quantifiers are unchanged. Static checks confirmed
that the main node differs from the current shared copy only in `lean` and the
already added comparison-definition dependency, and that no delivered module
contains profiling or heartbeat overrides.


## Maintainer independent review repair (2026-10-16)

H4: `CategoryTheory.homComplex_projections_exists` in the already published
`Sheaf.Algebra.Homology.HomComplexProjections` states the same proposition
as the delivered `homReductionHomProjections_exist`. The replacement module
imports it, removes the duplicate theorem, and selects its projections directly.
The new definition node cites `lem-sc-hom-complex-projections` and removes the
deleted helper from `lean.declarations`. By unfolding its let-bound functor
and proof irrelevance, this is the same projection family; all normalization
fields, the canonical arrow, and the main corollary signature are unchanged.
The earlier worker account of a newly postponed projection proof is superseded
by this repair. The two remaining postponed proofs are the normalized-model
existence theorem and the main corollary. See the independent review.md for
the full statement audit and final immutable/replacement compile evidence.

Validation of this exact repair: `scompile.py NH cor-coef-integral-internal-hom`
was run with the replacement comparison and unchanged immutable main module as
siblings. All five local preliminary/sandbox/library invocations passed with
exit 0 and no diagnostics; no server fallback was needed. The library comparison
and corollary reported 42.3 s and 5.8 s. The preliminary total of 64.5 s includes
slot waiting; the actual Lean subprocess retained the wrapper's timeout=60.
The original immutable packet also reproduced successfully, with no diagnostics.
