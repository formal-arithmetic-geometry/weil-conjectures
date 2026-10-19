## Worker report

The new module `Sheaf.Paper.IntegralResidueTor` states
`WeilConjectures.integral_residue_tor`, with proof `sorry`. It states both the
prescribed Tor interval for every finite reduction and equality of the integral
constructible and finite-Tor object predicates. Equality of these predicates is
exactly equality of their full subcategories of the same ambient derived category.
The item's natural-language statement and proof are unchanged. The additional
statement dependencies are existing recorded nodes required by the paired-source
repair below, not new notions or mathematical hypotheses.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The global finite-field datum is `(D : FiniteFieldDatum.{d})`. The prime ell is
  `(l : ℕ) [Fact l.Prime]`, and `hl : l ≠ D.p` is the distinction from p.
- The finite extension E/Q_ell is `(E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`. Its valuation ring and
  chosen uniformizer are precisely the ones used by the dependency
  `Padic.coefficientExtensionRing`, not fresh coefficient data or a separate choice.
- The arbitrary scheme is `(X : AlgebraicGeometry.Scheme.{u})` and invertibility
  of ell on X is `[∀ x : X, Invertible (l : X.residueField x)]`. No Noetherian,
  quasi-compact, separated, finite-dimensional, finite-type or base-field condition
  is imposed on X. Invertibility in every residue field is equivalent to the
  integer section being a unit locally, hence on X.
- The coefficient ring at positive exponent j is
  `Padic.coefficientExtensionRing l E j`. The existing integral API uses n for
  exponent n+1. Thus all positive exponents, including j=1, occur exactly once;
  there is no exponent-zero condition.
- `K : completedIntegralDerivedCategory l E X D hl` is an object of the derived
  category of modules over the inverse-limit completed ring sheaf on the small
  pro-etale site. It is not a constant valuation-ring sheaf or an etale substitute.
- `boundedConstructibleDerivedCompleteIntegral D l hl E X K` is the exact
  recorded D^b_c membership: derived completeness, constructible finite reductions,
  and a common cohomological interval for all reductions. Neither completeness
  nor the uniformity condition is replaced by Tor amplitude in the premise.
- The ordered interval is `∀ a b : ℤ, a ≤ b → ...`, with integer endpoints.
- The hypothesis that K_1 has cohomology only in [a,b] is
  `∀ i : ℤ, i ∈ proEtaleCohomologicalSupport
  ((integralDerivedReduction l E X D hl 0).obj K) → a ≤ i ∧ i ≤ b`.
  The dependency's support is exactly the set of indices with nonzero homology
  sheaf. Hence this is vanishing outside the closed interval, with both endpoints
  included, and index 0 is exactly the level-one residue reduction.
- The conclusion for every positive finite level is `∀ n : ℕ,
  HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
  ((integralDerivedReduction l E X D hl n).obj K) a b`. The same a and b
  precede the n quantifier. The Tor predicate tests all module sheaves in degree
  zero on all K-flat computations; it is not ordinary cohomological amplitude.
- The consequence is the second conjunct
  `boundedConstructibleDerivedCompleteIntegral D l hl E X =
  finiteTorConstructibleIntegral D l hl E X`. Both are object predicates on
  the identical completed integral category. Their `.FullSubcategory` definitions
  therefore select exactly the same objects and all the same morphisms. This
  does not compare different ambient categories or merely assert an equivalence.
- The final caution about site-perfectness is respected: the theorem contains no
  perfectness predicate, equivalence, or inference about the whole scheme.

The single theorem packages the interval implication universally over K,a,b and
then the categorical consequence. This retains both clauses even when the chosen
interval hypothesis is false for a particular K; the categorical equality is not
made conditional on such a choice.

Recorded statement-dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and its
  coefficient convention. The field, prime and chosen DVR quotients are unchanged.
- `Sheaf.Paper.DerivedCompleteIntegralDetailed`:
  `WeilConjectures.boundedConstructibleDerivedCompleteIntegral` and
  `WeilConjectures.boundedConstructibleDerivedCompleteIntegralCategory`.
- `Sheaf.Paper.IntegralDerivedReduction`:
  `WeilConjectures.integralDerivedReduction`, with its canonical universal counit,
  exactness and comparisons on K-flat resolutions.
- `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`:
  `AlgebraicGeometry.Scheme.HasProEtaleTorAmplitude` and
  `AlgebraicGeometry.Scheme.HasFiniteProEtaleTorAmplitude`.
- The supplied `Sheaf.Paper.FiniteTorAmplitude`:
  `WeilConjectures.finiteTorConstructibleIntegral`, with its full-subcategory alias.
- `Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport`:
  `AlgebraicGeometry.Scheme.proEtaleCohomologicalSupport`. This is the recorded
  support definition already used inside the integral constructibility predicate.

The proof docstring reproduces the complete four-step node proof: choose a K-flat
resolution; identify the iterated residue reduction by the explicit balanced maps;
apply the pro-etale residue Tor test to each bounded constructible reduction;
use the existing uniform cohomology interval and the reverse defining inclusion.
All recorded proof-dependency modules with statements are imported. These include
`CochainComplex.exists_isKFlatResolutionIndependentCoefficients`,
`CochainComplex.IsKFlat`, `SheafOfModules.siteSheafTensorRight`,
`SheafOfModules.derivedChangeOfRingsIndependentCoefficients`, and
`AlgebraicGeometry.Scheme.proEtale_torAmplitude_iff_residue_tensor`.
The general change-of-rings and tensor APIs keep the prescribed coefficient maps,
not arbitrary functors or isomorphisms. No proof is claimed by this delivery.

Edge cases checked before writing:

- K=0 and the empty scheme are allowed. Empty cohomological support satisfies
  every ordered interval, and the corresponding Tor vanishing is consistent.
- a=b gives a one-degree interval; negative endpoints and negative degrees are
  retained by ℤ. No strictness at either endpoint is introduced.
- n=0 in the API is exactly the residue quotient, not R/(1). All arbitrarily
  large positive powers are included by the natural-number quantifier.
- A bounded constructible finite-level complex alone need not have finite Tor
  dimension. The theorem assumes one actual integral K and uses its reductions;
  no finite-level constructible object is silently promoted to finite Tor amplitude.
- The same ambient universe u for E and X follows the recorded integral predicate;
  d for the finite-field datum is independent. Small pro-etale site objects are
  in u+1, morphisms in u, and the modules in u+1. The repair retains independent
  site object/morphism/coefficient universes for the general prerequisites.
- Equality is between object predicates, not chosen skeletal categories, and the
  full-subcategory morphisms are inherited without a further finiteness condition.

Searches for existing statements/definitions:

- msearch.py LeanFinder: "For a derived complete constructible complex over a
  discrete valuation ring, bounded residue reduction controls uniformly the Tor
  amplitude of all finite reductions" returned eight results about derived-category
  cohomology bounds, t-structures, and projective Tor vanishing. None states the
  uniform completed-integral pro-etale assertion. The signatures were inspected;
  `DerivedCategory.isLE_iff`, `isGE_Q_obj_iff`, `isLE_Q_obj_iff`,
  `isZero_of_isLE`, `isZero_of_isGE`, and
  `exists_iso_Q_obj_of_isGE_of_isLE` concern cohomological bounds only.
- msearch.py Loogle: `HasProEtaleTorAmplitude,
  boundedConstructibleDerivedCompleteIntegral` returned zero hits, with unknown
  identifier `HasProEtaleTorAmplitude`; this is not evidence against the known
  project predicate, whose source was read and used.
- msearch.py LeanSearch: "Uniform finite Tor amplitude of reductions of derived
  complete constructible integral complexes" was unavailable (Internal Server
  Error). This is recorded as unavailable, not as a negative mathematical result.
- msearch.py Mathlib grep: `torAmplitude|TorAmplitude|residue.*[Tt]or` returned
  sixteen unrelated residue, tensor and local-ring occurrences, no exact theorem
  or coefficient-category definition.
- Direct rg in upstream WeilConjectures and project lean/Sheaf checked the item id,
  integral/residue/Tor combinations, and the proposed declaration names. The
  exact upstream item-id hit is documentation in
  `SixFunctors/Etale/Derived/IntegralCoefficients.lean`, line 498. I read the nearby
  `exists_normalizedTower_and_boundedConstructibleIntegral_iff`: it concerns the
  etale constant-ring category and normalized towers, not this completed pro-etale
  object predicate. It is not an exact existing declaration for this node.
- Direct project search found `ProEtaleResidueTorTest`, `FiniteCtfTriangulated`,
  and the recorded Tor predicate, which are reused. No existing integral
  finite-Tor predicate or statement has either proposed name. The upstream name
  table was also searched for name collisions.
- The prescribed server source lookup for `Sheaf.Paper.FiniteTorAmplitude`
  reported "Module source unavailable". Read-only server searches of Lean and
  delivery-branch names found no delivered finite-Tor definition or item statement.

Source checked: the actual blueprint item at order 2133 and its full proof, and
`def-weil-finite-tor-amplitude` at order 1464. The local repository omits the
blueprint text, so the launcher's literature mirror supplied these exact files.
The framework coordination note was read; its condensed module-object categories
are not substituted for these completed sheaves of modules. No statement correction
or STATEMENT-DISPUTED flag is needed. There are no new DAG nodes.

## Dependency modules

`lem-weil-integral-constructible-triangulated`, module
`Sheaf.Paper.IntegralConstructibleTriangulated`, is included under §1(B) in the
repair of immutable head a7224e4bc65c. Its recorded module could not be compiled
in automatic overlay preparation because its DerivedCompleteIntegralDetailed
object was a sibling not yet built. Including this triangulation module as a
sibling orders it after that definition. It retains the two coefficient-size
sheafification instances and the exact isomorphism-closure and triangulation
statement for bounded constructible derived-complete integral objects. Only the
module comment and the node's `lean` record change; all declarations and bodies
are identical to the current recorded source. The later repair section gives
the clause audit and compile evidence.

`def-weil-finite-tor-amplitude` was an existing, genuinely unstated prerequisite.
Following the human's instruction that such prerequisites are supplied in the same
delivery, its new module `Sheaf.Paper.FiniteTorAmplitude` defines:

- `finiteTorConstructible`: intrinsic finite-torsion constructibility intersected
  with `HasFiniteProEtaleTorAmplitude`, and `finiteTorConstructibleCategory` as
  its full subcategory. The existing finite Tor predicate includes an ordered
  interval and all degree-zero module sheaves. No perfectness is imposed.
- `finiteTorConstructibleIntegral`: the recorded integral constructible predicate
  intersected with `∃ a b : ℤ, a ≤ b ∧ ∀ n : ℕ, ...`, testing Tor amplitude
  of `integralDerivedReduction ... n` over A_{E,n+1}; and its full-subcategory
  alias `finiteTorConstructibleIntegralCategory`. This is a single interval for
  all levels, not a separate interval at each level.
- `finiteTorFieldCoefficientCategory C := C` expresses the source's field-stage
  naming convention parametrically in the already chosen bounded constructible
  category C. Applied to D^b_c(Y,E), respectively its common-stage algebraically
  closed category, it is literally that same category. This alias adds no
  perfectness condition, completion, object, morphism or triangulation. It does
  not reimplement the independent rationalization or common-stage constructions;
  those notions are not needed to formulate this integral item. The source's
  field equalities are identity aliases rather than new mathematical assertions.

This module imports the recorded finite and integral constructible triangulation
statements as proof ingredients. The separate integral finite-Tor triangulation
node is not needed to define the object predicate, and no new theorem asserting
triangulatedness is inserted into this definition module. All data is explicit;
there is no `sorry` in a definition. The node's fields other than `lean` are unchanged.

The initial compilation failed in `IntegralReductionTower.lean`: its completed
ring sheaf has coefficient universe max u (t+1), while the loaded
`CochainComplex.IsKFlatResolution` expected t+1. This is the same stale artifact
failure documented by the preceding integral-constructibility triangulation
packet. The following eight recorded sources are retained together under §1(B).
Each differs only by a module-docstring explanation of this packet. No Lean
signature, definition, proof, canonical map or mathematical assumption changes.
Each node changes only `lean` and has a note explaining the unusable artifact.

- `def-pc-kflat-complex`, `Sheaf.Algebra.Homology.KFlat`: retains the K-flat
  predicate, quasi-isomorphic K-flat resolution predicate, and the independent
  sheafification/monoidal-localization infrastructure, with coefficient universe w.
- `lem-pc-kflat-resolution`,
  `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`: retains
  existence of a K-flat resolution with flat terms, quasi-isomorphic augmentation,
  and epimorphic augmentation in each degree, with independent coefficient size r.
- `lem-pur-derived-change-of-rings`,
  `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`: retains
  the fixed tensor-on-objects/maps action, K-flat quasi-isomorphism preservation,
  pointwise derived universal property, exactness and canonical counit computation.
- `def-weil-integral-derived-reduction`, `Sheaf.Paper.IntegralDerivedReduction`:
  retains the actual completion projections, universal derived functor, exactness
  and canonical computation on every K-flat resolution.
- `lem-weil-integral-reduction-tower-well-defined`,
  `Sheaf.Paper.IntegralReductionTowerWellDefined`: retains the chain-level unit
  and transition characterized on sheafified pure tensors, and the canonical
  counit comparison respecting both augmentations and transitions.
- `def-weil-integral-reduction-tower`, `Sheaf.Paper.IntegralReductionTower`:
  retains the inverse tower of restricted reductions and its compatible cone
  with the prescribed maps from K, rebuilt against that well-definedness interface.
- `def-weil-derived-complete`, `Sheaf.Paper.DerivedComplete`: retains existence
  of the distinguished Roos triangle with its first map induced by that canonical
  cone. It does not replace this with an arbitrary map to a limit.
- `def-weil-derived-complete-integral-detailed`,
  `Sheaf.Paper.DerivedCompleteIntegralDetailed`: retains derived completeness and
  intrinsic constructibility of each reduction in one common cohomology interval.

The existing node statements, complete signatures and docstrings of these modules
were read. Their definitions contain real data; the inherited postponed theorems
keep their matching blueprint nodes and natural-language proof plans. All additional
item stmt_deps name already recorded nodes, and no dependency statement is changed.

Validation: scompile.py compiled every delivered module separately in dependency
order. The ten-file packet passed cleanly, with no error or warning, including the
new finite-Tor definitions and integral residue statement. Each file stayed below
the required 60-second limit. No global build or direct git mutation was run by
this worker. The prescribed delivery dry run follows; independent second reading
is intentionally left to the next worker.

## Earlier second reading (a previous round; superseded)

I independently read the item JSON, its four proof steps, its blueprint source
(order 2133), and `IntegralResidueTor.lean` together. I also read the finite-Tor
source (order 1464), the integral constructibility source (order 1459), the
surrounding units, and every delivered dependency module. The mathematical
statement needs no correction. The second reading adds this audit and independent
searches; it changes no Lean declaration or node statement.

The object/hypothesis/conclusion inventory and its Lean correspondence are:

1. Global finite-field coefficient data and a prime different from its characteristic:
   `D : FiniteFieldDatum.{d}`, `l : ℕ`, `[Fact l.Prime]`, `hl : l ≠ D.p`.
   I opened `FiniteFieldFiber.lean`: its fields specify the prime, positive exponent,
   finite base field of the prescribed cardinality, and algebraic closure. Verdict:
   exact; no assumption that X is a scheme over either field has been inserted.
2. A finite extension E/Q_l, its valuation ring, uniformizer, and positive-power
   quotients: `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]`,
   `[FiniteDimensional (Padic l) E]`, and `Padic.coefficientExtensionRing l E (n+1)`.
   I opened `CoefficientExtension.lean`: the quotient is by the power of the
   principal ideal of the recorded uniformizer in the recorded valuation ring.
   Verdict: the dependency's actual coefficient objects, with no extra coefficient
   embedding into an algebraic closure.
3. Any scheme X where l is invertible: `X : AlgebraicGeometry.Scheme.{u}` and
   `[∀ x : X, Invertible (l : X.residueField x)]`. Being a unit in all residue
   fields is equivalent to the integer section being a unit on X. Verdict: exact;
   no Noetherian, qcqs, separated, finite-type, or base-field hypothesis is present.
   The blueprint item itself permits this general X. The qcqs setup in
   Bhatt--Scholze §6.5 is not an additional hypothesis of the blueprint's
   independently defined completed-coefficient category and residue argument.
4. An integral derived object with the prescribed bounded constructibility:
   `K : completedIntegralDerivedCategory l E X D hl` and
   `boundedConstructibleDerivedCompleteIntegral D l hl E X K`.
   I followed `CompletedIntegralCoefficients` to its actual inverse limit of
   constant quotient ring sheaves, and `DerivedCompleteIntegralDetailed` to
   `IsDerivedComplete`, constructibility of every reduction, and one ordered
   cohomological interval for all reductions. Verdict: exact; the premise is
   neither an etale/constant-integral substitute nor the finite-Tor conclusion.
5. Its canonical derived reductions K_n: `(integralDerivedReduction l E X D hl n).obj K`.
   I read its defining change-of-rings witness, universal derived pair, counit,
   and K-flat computation isomorphisms. The coefficient map is the actual
   completion projection. Verdict: exact. Index n denotes mathematical exponent
   n+1 throughout this API; index 0 is K_1.
6. Ordered integer endpoints and residue cohomology vanishing outside them:
   `∀ a b : ℤ, a ≤ b → (∀ i : ℤ, i ∈ proEtaleCohomologicalSupport
   ((integralDerivedReduction ... 0).obj K) → a ≤ i ∧ i ≤ b) → ...`.
   I opened `ProEtaleCohomologicalSupport`: membership means the homology sheaf
   is not a zero object, so the implication is precisely vanishing outside the
   inclusive interval. Verdict: exact; no lower-degree or endpoint omission.
7. Tor amplitude in that SAME interval at EVERY positive finite level:
   `∀ n : ℕ, HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n+1))
   ((integralDerivedReduction ... n).obj K) a b`.
   I opened `ProEtaleTorAmplitude`: it tensors with every module sheaf in degree
   zero on every K-flat representative and tests the derived homology objects.
   Verdict: exact. The a,b quantifiers precede n, so the bound is uniform.
8. Equality of the two full subcategories:
   `boundedConstructibleDerivedCompleteIntegral D l hl E X =
   finiteTorConstructibleIntegral D l hl E X`.
   These are object properties of exactly the same completed derived category;
   both category aliases use `.FullSubcategory`. Equality of object properties
   gives the identical full subcategory. Conversely its object set determines
   the property extensionally. Verdict: the categorical consequence is fully
   retained and is outside the implication for any particular K,a,b.
9. No identification with site-perfectness: the conclusion contains no
   site-perfectness predicate. Verdict: the source's caution is respected.

Dependency-module reading (H4/H5/H12/H13):

- `def-weil-finite-tor-amplitude` is an existing DAG node, not a new definition
  node. I read its entire statement and blueprint source against
  `FiniteTorAmplitude.lean`. `finiteTorConstructible` intersects intrinsic
  finite-torsion constructibility with the existing finite Tor predicate;
  `finiteTorConstructibleIntegral` intersects actual integral membership with
  `∃ a b, a ≤ b ∧ ∀ n, HasProEtaleTorAmplitude ... a b`. Its category aliases
  select those exact objects. The field clause is only a naming convention:
  `finiteTorFieldCoefficientCategory C := C` takes the already specified bounded
  constructible field category as its parameter and preserves its existing
  objects, morphisms, and structure definitionally, for either field stage.
  It does not assert or supply an alternative construction of the rationalized
  or common-stage category. I checked that those are separate DAG notions;
  neither is used as an undefined object in this integral theorem. The finite
  definitions also make sense without invertibility; on the schemes stipulated
  by the source they impose exactly its condition. No triangulation theorem is
  smuggled into a definition; closure has its own recorded statement nodes.
- `def-pc-kflat-complex`: `IsKFlat` tests total tensor acyclicity against every
  acyclic complex; `IsKFlatResolution` is the conjunction with quasi-isomorphism.
  These match Stacks 06YN/06YS. The auxiliary instances give the sheafification,
  monoidal localization, and zero-map infrastructure at coefficient size w.
- `lem-pc-kflat-resolution`: its existential includes a K-flat complex, flatness
  in every degree, a quasi-isomorphism, and degreewise epimorphic augmentation.
  This is exactly Stacks 06YS, including its surjectivity clause.
- `lem-pur-derived-change-of-rings`: the witness fixes the ordinary functor's
  objects AND maps to recorded scalar extension. It states quasi-isomorphism
  preservation between K-flat complexes, pointwise left derivability, an exact
  universal derived pair, and an invertible counit on every K-flat complex.
  These retain both clauses and the canonical comparison of the dependency node.
- `def-weil-integral-derived-reduction`: the ordinary functor uses the fixed
  completion projection and the derived functor is selected with its universal
  counit. The resolution comparison inverts the image of the augmentation and
  composes with that counit. The choice is fixed up to compatible isomorphism
  by a universal property, rather than a bare arbitrary functor choice.
- `lem-weil-integral-reduction-tower-well-defined`: the unit and transition maps
  are uniquely characterized on sheafified local pure tensors; the finite
  comparison is the composite through the common derived reduction. The theorem
  gives both augmentation and transition identities, with their actual maps.
- `def-weil-integral-reduction-tower`: `Functor.ofOpSequence` uses these actual
  transitions; the cone legs invert the augmentation and use the actual unit.
  Its named naturality theorem supplies the cone law, with its own proof plan.
- `def-weil-derived-complete`: the existential packages representatives and the
  canonical cone, then asks that the specified map into the product start a
  distinguished Roos triangle. It is not existence of an arbitrary map or an
  arbitrary derived-limit isomorphism. I read Bhatt--Scholze p.24, Definition
  3.5.2, against this condition.
- `def-weil-derived-complete-integral-detailed`: its three requirements are
  derived completeness, all finite reductions constructible, and their common
  cohomological interval. Its category is the full subcategory on that property.

For the eight rebuilt recorded modules I compared sandbox/shared sources after
removing comments: all declarations and bodies are identical. Each node changes
only `lean`, with a note explaining the incompatible published artifact. I read
all eight interfaces against their node statements, not just this comparison.
The general coefficient universe stays independent of both site universes, and
specializes to the required max u (t+1). No new universe equality is introduced.
The item's common ambient u for E and X is the recorded finite-coefficient and
integral constructibility convention; d is independent. Its pro-etale site still
has object size u+1 and morphism size u. Every definition has explicit data;
postponed proofs are named theorems with source/blueprint and proof docstrings.

Sources read also include the actual Stacks `.tex` mirror, labels
`definition-K-flat`, `lemma-K-flat-resolution`,
`lemma-derived-tor-quasi-isomorphism-other-side`, `lemma-derived-base-change`,
and `definition-tor-amplitude`, including their surrounding setups. The ringed
site setup adds no scheme finiteness condition. I also cross-checked the published
[06YN](https://stacks.math.columbia.edu/tag/06YN),
[06YS](https://stacks.math.columbia.edu/tag/06YS),
[06YY](https://stacks.math.columbia.edu/tag/06YY), and
[08FZ](https://stacks.math.columbia.edu/tag/08FZ).

Edge cases: the zero complex and empty scheme are admitted, with empty
cohomological support and vacuous vanishing tests. There is no nonempty indexing
assumption. API n=0 is exponent 1, while exponent 0 of the quotient ring (the
zero-ring quotient) is deliberately outside the node's range. All positive
exponents occur. Negative degrees, a=b, arbitrary large n, ramified coefficient
extensions and every prime l distinct from p are retained. The characteristic
restriction is exactly invertibility of l on X. Equality of predicates supplies
all objects and all morphisms of the two full subcategories.

Independent searches (different natural-language query from the worker):

- `msearch.py ... leanfinder "Derived completion modulo powers of a uniformizer
  bounded residue cohomology gives Tor dimension bounds"`: eight hits, including
  local-ring cotangent-space dimension and ramification quotient rank results;
  their printed signatures contain no completed sheaf category or Tor interval.
- `msearch.py ... loogle '"Tor"'`: twelve substring results in core programming
  declarations; none is a match.
- `msearch.py ... leansearch "Uniform Tor bounds on reductions of a derived
  complete integral constructible complex"`: unavailable, Internal Server Error.
  This is not recorded as a negative search result.
- Direct `rg` in Mathlib Algebra, CategoryTheory and RingTheory for
  `TorAmplitude|torAmplitude|tor_amplitude|bounded.*residue|residue.*bounded`
  found no exact declaration. Direct upstream/project searches for uniform Tor
  bounds, the item id, and all new names found no competing theorem or definition.
  I opened upstream `Etale/Derived/IntegralCoefficients.lean`, especially
  `exists_normalizedTower_and_boundedConstructibleIntegral_iff`: it uses an
  etale constant-ring category and includes the Tor bound in its constructibility
  definition, so it cannot replace this node. I also read the corresponding
  references in `SixFunctors/ClosedImmersionStages.lean`; they use those same
  different categories. The project's pro-etale residue test and Tor predicates
  are reused rather than copied.

No H3 mismatch, missing prerequisite, new node, or statement correction was found.
I checked each `lean.statement` is a verbatim substring of its declaration
signature and every delivered line is at most 100 characters. The main proof
uses only `sorry`; its docstring covers all four DAG proof steps, including both
balanced maps and the uniform-interval consequence. All ten delivered files were
compiled separately by scompile.py in dependency order: clean, no errors or
warnings, 1.2--10.3 seconds per delivered file. No global build was run.

## Repair of returned immutable head a7224e4bc65c

The returned compilation attempted to build the published side-overlay module
`Sheaf.Paper.IntegralConstructibleTriangulated` before the object file of its
dependency `Sheaf.Paper.DerivedCompleteIntegralDetailed` existed. The latter was
already supplied by this packet, so the overlay preparation skipped it while
trying to compile the former. This is repaired by supplying the former as a
sibling module as well, retaining the recorded declarations without modification.
The local compiler then orders both after their dependencies within the packet.

### Dependency module added in this repair

`lem-weil-integral-constructible-triangulated` is included under §1(B), with its
existing node copied and only its `lean` changed. The item cites this existing
prerequisite, already needed by its finite-Tor dependency. Its `lean.note` records
why the isolated recorded module could not be used. The only source edit is a
module-docstring explanation of the packet; no declaration signature or body
changes. No new notion or new DAG node is introduced.

The module's three existing declarations were read against the recorded node.
`integralConstructibleAbSheafify` and `integralConstructibleAbLocallyBijective`
specialize the existing coefficient-size transports on the actual small pro-etale
site; they impose no new hypothesis. The theorem
`boundedConstructibleDerivedCompleteIntegral_isTriangulated` uses the node's
finite-field datum, prime, finite coefficient extension, and arbitrary scheme.
`ObjectProperty.IsClosedUnderIsomorphisms` states isomorphism closure and
`ObjectProperty.IsTriangulated` states zero, shift and extension closure for the
actual completed-integral object predicate. The inherited full-subcategory
triangulation is the Mathlib consequence of these clauses. The existing eight-step
proof docstring is retained, including the canonical completion unit and uniform
reduction interval. The zero object, empty scheme, shifts by all integers, and
independent site/coefficients universes remain admitted.

The source was checked both in the read-only shared tree and with
`scompile.py --source Sheaf.Paper.IntegralConstructibleTriangulated`; they agree.
The returned server log also records `OSError: [Errno 28] No space left on device`
while creating a temporary overlay symlink. No shared compiler file, object cache
or server temporary directory is edited by this repair. The prescribed wrapper
checks are rerun below to test the current tool state.

Repair validation: `scompile.py Q20 lem-coef-integral-residue-tor` compiled all
eleven delivered modules separately in dependency order, both in sandbox and
library placement. It exited 0 with no errors or warnings. The repaired ordering
was DerivedCompleteIntegralDetailed, IntegralConstructibleTriangulated,
FiniteTorAmplitude, then IntegralResidueTor. The longest individual invocation
was 34.8 seconds, below the unchanged 60-second limit. The new dependency node
changes only `lean`; stripping block comments confirms that every declaration
and body in its module is identical to the recorded source. The pre-existing
second reading above predates this repair; the next independent reader must
review this added module and its node record before delivery.

First repair dry run: all eleven modules compiled; preflight found exactly one
report-shape issue, because the added dependency's description was outside the
`## Dependency modules` section. Its full description is now also in that section.
No Lean source or mathematical statement required a change for this check.


## Second reading by Q20

This is an independent second reading of the repaired packet, including the added
IntegralConstructibleTriangulated module. I read the current shared node, the
sandbox node and theorem, their dependency declarations and the actual blueprint
source for order 2133. I also read the sources of orders 1459, 1464 and 1867 and
Stacks sites-cohomology.tex at definition-K-flat (06YN), lemma-K-flat-resolution
(06YS), lemma-derived-base-change (06YY) and definition-tor-amplitude (08FZ),
including their surrounding ringed-site setup. The local literature mirror supplies
the blueprint and Stacks sources absent from the shared checkout. The source
introduces no additional Noetherian, qcqs, separated or base-field hypothesis on X.
The main mathematical statement and its four proof steps require no correction.

The earlier worker report and earlier second reading above describe the historical
eleven-module packet. The final delivered packet has TWO modules and TWO node
records: IntegralResidueTor and its previously unstated finite-Tor dependency,
FiniteTorAmplitude. The nine obsolete dependency copies are retained only under
scratchpad/superseded-packet for audit; deliver2 does not deliver that directory.
No new DAG node, statement_change or citer repair is needed.

Object, hypothesis and conclusion inventory, with the final Lean correspondence:

1. Global finite-field datum, its characteristic p, and a prime ell different from p:
   `(D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)`.
   I opened FiniteFieldFiber: the datum carries a prime, positive exponent, finite
   field of the specified cardinality and its fixed algebraic closure. Verdict:
   exact. The unused-proof binder retains the stipulated characteristic inequality;
   it does not restrict X to a scheme over this datum.
2. Finite extension E/Q_ell, valuation ring and chosen uniformizer:
   `(E : Type u) [Field E] [Algebra (Padic l) E]
   [FiniteDimensional (Padic l) E]`. I opened CoefficientExtension: its absolute
   value is spectral, its valuation ring has the prescribed absolute-value
   description, and `coefficientExtensionIdeal` is `(span {uniformizer}) ^ n`.
   `Padic.coefficientExtensionRing l E n` is its quotient. Verdict: the recorded
   coefficient data, with no extra closure embedding or ramification restriction.
3. Any scheme X where ell is invertible:
   `(X : AlgebraicGeometry.Scheme.{u})
   [∀ x : X, Invertible (l : X.residueField x)]`.
   Being nonzero in each residue field says exactly that ell is locally a unit.
   Verdict: exact; no finiteness, nonemptiness, or base-field assumption is added.
4. An object K of the derived category of the COMPLETED coefficient sheaf:
   `K : DerivedCategory (scalarReductionSource.{u, u} l E X)`.
   I opened CompletedIntegralCoefficients and DerivedScalarExtensionRestrictionAdjunction.
   `scalarReductionSource` is SheafOfModules of the existing inverse-limit ring
   sheaf after forgetting commutativity, using the standard derived localization.
   Its unrestricted completed ring is the same limit of the finite constant
   quotient ring sheaves, not the constant sheaf of the valuation ring. Verdict:
   exact object, using the current recorded dependency interface.
5. Membership in the actual bounded constructible derived-complete category:
   `sfIntegralConstructible l E X K`. I read SfIntegralConstructible,
   SfDerivedComplete and SfIntegralReductionTower. This is canonical derived
   completeness, intrinsic constructibility of every reduction, and one ordered
   cohomological interval containing all reductions. The completion predicate
   uses the canonical adjunction units and the Roos triangle; its transitions are
   uniquely normalized on K-flat representatives. Verdict: exact, with no Tor
   hypothesis substituted into the premise and no arbitrary completion map.
6. Canonical derived reductions K_n for all positive exponents:
   `(scalarReductionDerivedExtension.{u, u} l E X n).obj K`.
   I read scalarReductionExistence, scalarReductionDerivedExistence,
   scalarReductionDerivedExtension and scalarReductionCounit: the ordinary
   objects AND maps are fixed scalar extension along the actual completed-ring
   projection; the derived functor and counit have their universal property and
   are computed on K-flat complexes. Verdict: exact. API n means exponent n+1;
   API zero is precisely the mathematical residue reduction K_1.
7. Ordered integer bounds and cohomology only inside the inclusive interval:
   `∀ a b : ℤ, a ≤ b → (∀ i : ℤ,
   i ∈ proEtaleCohomologicalSupport
   ((scalarReductionDerivedExtension.{u, u} l E X 0).obj K) →
   a ≤ i ∧ i ≤ b) → ...`.
   I opened ProEtaleCohomologicalSupport: membership is nonzero derived homology
   sheaf. Verdict: exactly vanishing outside [a,b], including both endpoints.
8. Tor amplitude in THAT interval at EVERY finite level:
   `∀ n : ℕ, HasProEtaleTorAmplitude X
   (Padic.coefficientExtensionRing l E (n + 1))
   ((scalarReductionDerivedExtension.{u, u} l E X n).obj K) a b`.
   I opened ProEtaleTorAmplitude: it tests every module sheaf in degree zero on
   every K-flat resolution of every representative of K and asks for zero
   homology outside [a,b]. Verdict: exact Tor amplitude; a,b precede n, so the
   bound is uniform and is not merely a cohomology bound.
9. Equality of the two full integral subcategories:
   `sfIntegralConstructible l E X = finiteTorConstructibleIntegral l E X`.
   The right predicate intersects precisely the left predicate with existence
   of ONE ordered interval valid for all positive finite reductions. Both
   category aliases are `.FullSubcategory` on this identical ambient category.
   Verdict: equality of the object predicates gives equality of those full
   subcategories, retaining every morphism. This is the second conjunct, outside
   the interval implication, and so is unconditional on a particular K or a,b.
10. The caution about site-perfectness: no site-perfectness predicate or
    identification occurs in the conclusion. Verdict: respected.

Dependency module audit (H4/H5/H12/H13):

- def-weil-finite-tor-amplitude is an existing, previously unstated DAG node,
  already in the item's stmt_deps. Its finite predicate is exactly intrinsic
  finite-torsion constructibility intersected with the recorded finite Tor
  predicate. Its integral predicate now uses the CURRENT recorded
  sfIntegralConstructible and scalarReductionDerivedExtension, and adds
  `∃ a b : ℤ, a ≤ b ∧ ∀ n : ℕ, ...` with the prescribed finite quotient rings.
  Both full-category aliases select these objects with all ambient morphisms.
  The field-coefficient clause is a naming convention, implemented by the
  identity alias `finiteTorFieldCoefficientCategory C := C`, where C is the
  already specified rationalized or common-stage constructible category. It
  asserts no alternative construction, imposes no condition on objects, and
  performs no idempotent completion. The two category constructions have their
  own DAG nodes; the alias needs no construction of their data. Triangulated
  closure belongs to the separate closure nodes, not to these definitions.
  The finite-Tor definitions make sense more generally without ell-invertibility;
  on the schemes specified by the source they impose exactly its condition.
- No new definition node is introduced. The dependency node differs from the
  current shared node only in lean, with a note explaining its supplied module.
  The main node differs only in lean; its original stmt_deps are retained.
- All definitions in the final packet have real explicit data. There is exactly
  one postponed theorem, integral_residue_tor, with proof `sorry`, its matching
  DAG node, source/blueprint docstring and all four natural-language proof steps.
  The docstring includes both balancing maps, canonical composite projection,
  the pro-etale residue test and the uniform-interval/full-subcategory argument.

Mismatches found and repaired:

- H4/current-record mismatch: since the first packet was written, the canonical
  integral-reduction, integral-constructibility, derived-completeness and tower
  nodes acquired unrestricted interfaces in group Q29. The packet would have
  replaced those records by their superseded finite-field-dependent interfaces,
  and its theorem used those superseded records. I replaced the theorem's
  ambient-category, membership and reduction terms by the current recorded
  scalarReductionSource, sfIntegralConstructible and scalarReductionDerivedExtension.
  The integral finite-Tor definition uses these same recorded objects. The main
  theorem still binds D and ell != p exactly as its own node requires.
- The old nine dependency-module copies were needed by a stale-artifact repair
  of the superseded API, including the added IntegralConstructibleTriangulated.
  I read that added module: its sheafification instances specialize the existing
  transport, and its theorem states isomorphism, zero, shift and extension
  closure, exactly its node's triangulation assertion. It adds no new mathematical
  premise. Nevertheless this packet no longer needs to rebuild that older API,
  so I removed all nine copies from deliverable roots rather than overwriting
  the newer records. The old added stmt_deps are also absent from the final
  main-node copy; the final list is exactly the current base list.
- The two triangulation imports in the finite-Tor definition module were unused
  by its definitions; its node has no proof_deps. I removed them. The theorem
  directly imports every currently recorded proof dependency module, including
  the newly recorded scalar reduction and constructibility modules. The source
  statements and all four mathematical proof steps remain unchanged.
- I refreshed the two lean.statement fields to the final verbatim signatures.
  No target/unit statement, dependency mathematical statement, proof or other
  maintainer field was edited.

Edge cases: the zero object and empty scheme are admitted. Empty cohomological
support makes the interval hypothesis vacuous, as required. There is no nonempty
index hypothesis. API n=0 is the positive exponent 1; all positive exponents occur,
and exponent zero (the zero-ring quotient) is outside the node's range. Negative
cohomological degrees, a=b, arbitrarily large n and ramified E are retained.
The characteristic conditions are precisely ell != p and invertibility on X.
Universe d of the auxiliary finite-field datum is independent of u. E and X use
the existing finite-coefficient universe convention u; every pair can be put in
one common universe. The small pro-etale site retains objects in u+1, morphisms
in u and sheaf/module coefficients in u+1. No object/morphism-universe equality,
smallness hypothesis or arbitrary lower test universe has been introduced.

Independent searches using different words from the worker:

- leanfinder: "Completion along a principal ideal and cohomological bounds after
  tensoring with the residue field control uniform Tor dimension of quotient
  reductions". Eight hits, including AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian,
  Module.free_of_lTensor_residueField_injective and local-ring support dimension.
  I read their printed signatures: no completed ring sheaf or uniform derived
  reduction/Tor statement, hence no match.
- loogle: `"TorAmplitude"` returned zero hits.
- leansearch: "Uniform homological amplitude for reductions modulo powers of a
  uniformizer detected at the residue field" was unavailable (Internal Server
  Error). This is not a negative search result.
- Direct rg of Mathlib Algebra and CategoryTheory, upstream WeilConjectures and
  project lean/Sheaf for TorAmplitude, tor_amplitude, residue/amplitude and the
  new declaration names. Mathlib has no exact statement. I opened upstream
  SixFunctors/Etale/Derived/IntegralCoefficients at
  exists_normalizedTower_and_boundedConstructibleIntegral_iff: it is an etale
  constant-ring formulation with Tor amplitude already in its constructibility
  definition, not this assertion about the completed pro-etale ring sheaf.
  Upstream generic/pro-etale Tor-amplitude predicates do not supply the integral
  theorem or the completed coefficient construction. Existing project support,
  Tor amplitude, intrinsic constructibility and reduction definitions are reused.

Initial validation of the revised two-module packet: scompile.py compiled both
files separately in sandbox and library placement, cleanly with no warnings or
errors. It automatically compiled the published SfIntegralReductionTower,
SfDerivedComplete and SfIntegralConstructible dependencies in order. No legacy
paired dependency packet, universe equality or live-file edit was needed.
Final validation and the delivery preflight follow below.

Final scompile.py validation passed for both delivered files, separately in sandbox
and library placement: 3.3--4.6 seconds per invocation, no errors or warnings.
Both lean.statement fields are verbatim substrings of their declaration signatures;
all Lean lines are at most 100 characters, and autoImplicit is false. Only lean
changes on either current node. The finite-Tor module contains no postponed proof;
the sole theorem's proof is sorry, as required for stage 2.

Delivery dry run: deliver2.py Q20 lem-coef-integral-residue-tor --no-push printed
OK: commit 3d46114c53 passes preflight and compiles. Exactly the two node records,
two Lean modules and this report were staged; nothing was pushed by the dry run.
