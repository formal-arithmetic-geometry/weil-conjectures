## Worker report

The module `Sheaf.Paper.NormalizedEtaleOriginWitnesses` states
`AlgebraicGeometry.ProEtale.normalizedEtaleOriginWitnesses`, with `sorry` as its only
postponed proof. The helpers construct the actual canonical unit and reassociation
identifications and spell out the compatibility equation; they introduce no alternative
notion of origin. Definitions have real data. No statement correction, disputed
statement, new node, or dependency repair is needed.

The source is the current blueprint main-20261015,
`sec-proper-base-change/sk-thm-properbasechange/prop-weil-pbc-preservation-constructible.proof.md`,
the compatible witness sentence. I also read Stacks `proetale.tex`,
`lemma-compare-derived` (Tag 09B1), particularly its bounded-below comparison (2).
The normalized tower refinement is the node's agent-written refinement of that source,
not a claim that Stacks states this packaged theorem verbatim. The docstring carries
all six steps of the node's proof, including boundedness reflection before D+ full
faithfulness, the K-flat balancing computations, lifting the inverse, and cancellation
for the unit and cocycle.

Hypotheses and their Lean rendering:

- The arbitrary scheme T is `(T : Scheme.{u})`. There is no Noetherian, dimension,
  invertibility, or nonemptiness hypothesis on T.
- The commutative coefficient ring and adic datum are `{A : Type (u + 1)} [CommRing A]`
  and `(d : Scheme.AdicCoefficientDatum A)`. This is the recorded datum (through
  `AdicCoefficientDatum`), retaining its Noetherian, finitely generated ideal, additive
  torsion, finite quotients and perfectness fields.
- Positive levels P_n=A/I^n are the existing `PbcQuotient d n`, where the Lean index
  n denotes exponent n+1. Thus Lean n=0 is the paper's first level A/I; this is a
  bijective reindexing of all positive levels, not an additional level or restriction.
  The published instances give the actual quotient ring, finite set and discrete topology.
- The M_n are `(M : ∀ n : ℕ, PbcWitnessAmbient T d n)`. These are the canonical
  fixed-ring presentation of the specified function-coefficient module derived category.
  `hM` requires bounded-below membership of their canonical realizations in
  `FiniteCoefficientDerivedCategory`. The exact equivalence
  `finiteCoefficientRealization` identifies this presentation with the node's ringed
  coefficients; this is already the convention of `WitnessCompatibility`.
  The site has object universe u+1 and morphism universe u, and the coefficients and
  module sections live in u+1. No equality of those site universes is imposed.
- `(W : ∀ n, Scheme.EtaleOriginWitness ...)` is the recorded retained pair, not a
  replacement existence predicate. `(W n).L` is precisely the chosen bounded-below
  etale origin. `(W n).alpha` is its specified comparison isomorphism in D+.
  `pbcFixedOriginAlpha ... (W n)` transports that same isomorphism back through
  the canonical realization, using its full faithfulness. No origin is chosen afresh.
- `(rho : ∀ m n h, ... ≅ M n)` supplies the specified isomorphisms for every pair
  n≤m. `normalizedOriginReduction` abbreviates the published
  `pbcFixedScalarExtension` along `pbcWitnessQuotientMap d m n h`, the actual
  factor map A/I^(m+1) → A/I^(n+1). Scalar extension is the left adjoint of actual
  derived restriction, so it is derived coefficient tensor, including for nonflat maps.
- `rho_id` is the supplied self-normalization: rho_nn equals the canonical
  `normalizedOriginQuotientUnit`. That helper uses the quotient-factor identity
  `Scheme.adicQuotientMap_id`, the identity-on-sections restriction isomorphism,
  its exact derived image, and `Adjunction.leftAdjointIdIso`. Thus it is the unit
  x tensor a → ax, not an arbitrary isomorphism or automorphism.
- `rho_comp` is the supplied cocycle for all k≥m≥n, written as equality of maps
  from the iterated reduction. The right-hand path first applies
  `normalizedOriginQuotientComp`, then rho_kn. The helper is exactly
  `pbcFixedScalarExtensionComp` on the actual quotient-factor identity
  `Scheme.adicQuotientMap_comp`, using positive indices k+1,m+1,n+1.
  The proof arguments on inequalities are propositions, so no extra data depend on them.

Conclusions, clause by clause:

- The first conjunct is `∀ m n h, DerivedCategory.TStructure.t.plus (...)` on the
  unbounded etale scalar extension of `(W m).L.obj`. Hence boundedness is a conclusion;
  it is not assumed to make comparison applicable.
- `∃ beta : ∀ m n h, ... ≅ (W n).L.obj` gives all the required quotient-linear
  etale normalization isomorphisms, simultaneously for every pair.
- The first conjunct after existence requires `NormalizedOriginCompatibility` for
  every beta. Expanded, it is `ν_n(beta).hom ≫ alpha_n.hom =
  c_mn.inv ≫ Red(alpha_m).hom ≫ rho_mn.hom`. Here c is precisely
  `pbcComparisonReduction`, the published canonical mate of restriction comparison.
  Its inverse identifies the source `ν_n(L_m tensor P_n)` with the reduced
  `ν_m L_m`. This is the node's displayed equation with categorical composition
  written left to right, and with the canonical tensor source identification included.
- The next conjunct quantifies over every competing isomorphism beta' satisfying that
  same equation and states `beta' = beta m n h`. This is uniqueness among all lifts
  for each pair, without adding any unit or cocycle condition on the competitor.
- The following conjunct makes every beta_nn equal to the actual canonical etale
  self-extension unit, rendering beta_nn=1 under the prescribed identification.
- The final conjunct is the complete k≥m≥n cocycle, with the actual canonical
  `normalizedOriginQuotientComp` on the source. Thus all supplied normalization
  maps, rather than only adjacent transitions, are retained and respected.
- No common cohomological interval, constructibility, flatness, or finite Tor
  dimension is a binder. The statement leaves the lower bound level-dependent.

Dependency declarations read and used:

- `Sheaf.Paper.AdicCoefficientDatum` publicly imports
  `Sheaf.Paper.CompletedAdicCoefficientDatum`: `Scheme.AdicCoefficientDatum`,
  and the actual quotient-factor constructions inherited from
  `Sheaf.Paper.CompleteCoefficientDatum` (`adicQuotientMap`, `_id`, `_comp`).
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`:
  `FiniteCoefficientModules`, `FiniteCoefficientDerivedCategoryPlus`,
  `finiteCoefficientRealization`, `finiteCoefficientComparison` and their exactness
  and equivalence interfaces; these give the specified coefficient categories and ν*.
- `Sheaf.Paper.RingedEtaleOriginWitness`: `Scheme.EtaleOriginWitness`, the recorded
  alias of `ProEtale.EtaleOriginWitness`, with exactly its L and alpha fields.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`:
  `SheafOfModules.derivedChangeOfRingsIndependentCoefficients`, whose full independent
  site-universe signature and K-flat comparison docstring were read. The recorded
  module is publicly imported; its scalar-extension specialization is used through
  the published fixed-ring scalar-extension interface.
- `Sheaf.Paper.PbcActualScalarPullback`: the recorded ringed-topoi tensor dependency,
  including its publicly reexported arbitrary-ringed-topos canonical interface.
  Its canonical K-flat normalization is the source of the comparison used by the
  fixed-ring mate, not a freely selected Nonempty isomorphism.
- `Sheaf.Paper.WitnessCompatibility`: `PbcQuotient`, `pbcWitnessQuotientMap`,
  `PbcWitnessAmbient`, `pbcFixedScalarExtension`, `pbcFixedScalarExtensionComp`,
  `pbcComparisonReduction` and `pbcFixedOriginAlpha`. Its node
  `def-weil-pbc-witness-compatibility` is added as an already-landed statement dependency
  under brief-stage2 §5. It supplies reusable canonical constructions, not the theorem
  being stated. I checked that it has no statement/proof dependency path back to this item.
- Proof imports (ordinary, not public):
  `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel.siteComparison_finiteLevel`
  (namespace `AlgebraicGeometry.ProEtale`) for exactness and the sheaf-level unit;
  `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived.siteComparison_boundedBelow`
  (same namespace) for D+ full faithfulness. Their full statements and docstrings
  were read. These are the two extra proof dependencies of this node.
- Mathlib `ModuleCat.restrictScalarsId'`, `fullyFaithfulSheafToPresheaf`,
  `Functor.mapDerivedCategoryNatIso`, `Functor.mapDerivedCategoryIdIso`, and
  `Adjunction.leftAdjointIdIso` construct the unit with identity section maps.

Edge cases checked before and after drafting: the empty scheme and zero ring impose
no excluded case; no nontriviality instance is requested. Lean n=0 includes P_1.
Equal indices and k=m or m=n are in both cocycle quantifiers. The identity quotient
and the full identity triangle are explicit, including their canonical unit rather
than an unexplained equality of objects. Zero complexes have the unique zero-object
isomorphisms with the same formulation. The hypotheses allow arbitrarily varying
cohomological lower bounds. Nonflat reductions, including quotient rings with
infinite Tor dimension over an earlier quotient, remain allowed: only their realized
pro-etale reductions are assumed bounded below by the supplied isomorphism.

Searches made before drafting:

- `msearch.py ... leanfinder` with query "Compatible etale origins of normalized
  proetale finite coefficient towers lift uniquely through exact fully faithful inverse
  image"; no exact theorem was found (the search concerns etale algebra and generic
  categorical facts rather than the required normalized tower).
- `msearch.py ... loogle` with query
  `CategoryTheory.Functor.preimageIso, CategoryTheory.Functor.Faithful`: four generic
  preimageIso lemmas. They lift a single isomorphism for an already fully faithful
  functor; they do not give boundedness after tensor, the comparison source map,
  or quotient-cocycle compatibility, so none is an exact match.
- `msearch.py ... grep` with regular expression
  `etale.*(witness|normaliz)|ProEtale.*(tower|Tower)`: zero Mathlib hits.
- `rg` over `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for this node id:
  no hit; the broader origin/witness and normalization searches find
  `DerivedCategory.plusEtaleOrigin`, not this theorem.
- `rg` over the shared `lean/Sheaf` for normalized etale/origin witness and the
  all-pair compatibility vocabulary finds `WitnessCompatibility` (retains beta as
  already supplied data) and the downstream preservation and adic smooth theorems.
  None constructs the unique beta family from rho. The prior
  `AdicConstructibleFiniteReductions` theorem has other coefficient and
  constructibility hypotheses and is not a match. The actual recorded dependency
  declarations, including the latest `WitnessCompatibility` source via
  `scompile.py --source`, were inspected rather than inferred from their names.

Compilation: the entire module passed the prescribed `scompile.py Q54
lem-weil-pbc-normalized-etale-origin-witnesses ...` in both sandbox and library modes,
without errors or non-sorry warnings (2.3 and 2.7 seconds in the final drafting pass).
Every universe is explicit, autoImplicit is false, all lines have at most 100
characters, and no file-local notation or instance is required by a consumer.

## Second reading by Q54

The dispatcher explicitly forbids starting other agents, so this is the worker's
second pass, not a claim of independent review. I reopened the node and the completed
module and matched every binder and every conclusion as above. I checked specifically
that hM is the existing D+ condition on the realized M, W is the existing retained pair,
all supplied rho_mn occur, boundedness of etale reductions is concluded, uniqueness
is pairwise among all compatible isomorphisms, and both the identity and three-level
cocycle use canonical source comparisons. No mathematical mismatch was found.
No source statement, proof, or proof-dependency field is changed. The sole dependency
addition is the landed canonical fixed-ring interface that the statement actually uses.
The maintainer's independent review remains the independent mathematical review.
