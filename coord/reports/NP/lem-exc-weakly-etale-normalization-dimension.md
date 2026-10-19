## Worker report

The module `Sheaf.RingTheory.NormalizationLocalizationDimension` states
`IsUniversallyCatenary.ringKrullDim_localization_integralClosure_eq` with proof `sorry`.
It is exactly lem-exc-weakly-etale-normalization-dimension. No definitions, additional
statements, new nodes, dependency repairs, or statement corrections are needed.

The source checked is Stacks Project, Algebra, Tag 02IJ, `lemma-dimension-formula`,
lines 27519–27541 of the supplied algebra.tex. Its equality clause for a universally
catenary base applies to the finite birational integral extension in the node; both
transcendence-degree terms vanish. The module docstring identifies Greco Lemma 5.5,
printed p. 147, as the application. The theorem docstring carries all three DAG proof
steps, including both append-a-prime comparisons of chain suprema and heights.

Every hypothesis and clause is represented as follows:

- The commutative ring C is `{C : Type u} [CommRing C]`.
- Noetherianity is `[IsNoetherianRing C]`.
- Universal catenarity is `(hC : IsUniversallyCatenary C)`. This uses the dependency's
  predicate, which includes Noetherianity and catenarity of every finite type algebra.
- Locality is `[IsLocalRing C]`. Mathlib's nontrivial local-ring predicate gives the
  unique maximal ideal `IsLocalRing.maximalIdeal C`.
- The nonzero-domain requirement is `[IsDomain C]`; this includes nontriviality and
  absence of zero divisors, without any characteristic restriction.
- K = Frac(C) is `{K : Type v} [Field K] [Algebra C K] [IsFractionRing C K]`.
  This is any realization of the fraction field, including `FractionRing C` itself.
  The independently bound universe v does not constrain C or a test algebra.
- C' is exactly Mathlib's canonical `integralClosure C K`, whose carrier consists of
  the elements integral over C, with its induced C-algebra structure and inclusion in K.
  There is no additional arbitrary ring or comparison map.
- Finiteness as a C-module is `[Module.Finite C (integralClosure C K)]`.
- Every maximal ideal of C' is covered by the arbitrary binder
  `(m : Ideal (integralClosure C K)) [m.IsMaximal]`. The maximal-ideal instance also
  supplies primality for localization.
- The stated contraction requirement is exactly
  `(hm : m.comap (algebraMap C (integralClosure C K)) = IsLocalRing.maximalIdeal C)`.
- The conclusion dim(C'_m) = dim C is exactly
  `ringKrullDim (Localization.AtPrime m) = ringKrullDim C`.

Dependency declarations read and used (including their signatures and docstrings):

- def-weil-pbc-noetherian-ring: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing` (all ideals finitely generated).
- def-exc-excellent-ring: `Sheaf.RingTheory.ExcellentRing`, `IsUniversallyCatenary`;
  read the whole module, including `IsPrimeChain`, `IsSaturatedPrimeChain` and
  `IsCatenaryRing`. Excellence itself is not imposed by this node.
- def-weil-pbc-integral-closure:
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`, `integralClosure` (and its use
  of `IsIntegral` from `Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs`).
- def-weil-finitely-generated-module: `Mathlib.RingTheory.Finiteness.Defs`,
  `Module.Finite` (the top submodule is finitely generated).
- def-weil-pbc-krull-dimension-ring: `Mathlib.RingTheory.KrullDimension.Basic`,
  `ringKrullDim`, with values in `WithBot ℕ∞`.
- def-weil-pbc-localization-at-prime:
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime`.
- The fraction-field realization uses `IsFractionRing` from
  `Mathlib.RingTheory.Localization.FractionRing`.

Proof-only dependencies are imported without `public`: `Algebra.trdeg` from
`Mathlib.RingTheory.AlgebraicIndependent.Basic`, `Algebra.FiniteType` from
`Mathlib.RingTheory.FiniteType`,
`IsLocalization.AtPrime.ringKrullDim_eq_height` from `Mathlib.RingTheory.Ideal.Height`,
and `Ideal.exists_le_maximal` from `Mathlib.RingTheory.Ideal.Maximal`.
The dimension-formula proof dependency
`lem-exc-dimension-formula-universally-catenary-finite-type-domain` has neither a Lean
record nor a Mathlib match in the supplied DAG, so no module for it is imported and
no declaration for that separate node is stated here. It is a proof dependency only,
not an unavailable statement prerequisite. The maintainer can add its import when stated.

Edge cases checked mathematically before writing:

- If C is a field, the normalization is C, the unique maximal ideal is zero, and the
  localization has dimension zero. No positive-dimension condition is imposed.
- If C is a DVR (or any integrally closed Noetherian universally catenary local domain),
  C' = C and the equality specializes to the usual maximal localization equality.
- A local nodal domain can have semilocal normalization: the binder covers each maximal
  ideal separately and never assumes that C' is local or that m is unique.
- The zero ring is correctly excluded by the node's domain hypothesis; no accidental
  empty-spectrum case or nontriviality assumption has been added beyond that hypothesis.
- Equal and positive characteristics are both covered, with no residue-field restrictions.
- All universes and variables are explicitly bound; no `let`, local notation, private
  definition, or additional map hypothesis occurs in the signature.

Searches for an existing exact statement:

- `msearch.py ... leanfinder "The localization at every maximal ideal of the finite
  normalization of a universally catenary Noetherian local domain has the same Krull
  dimension as the domain"`: eight hits, including
  `instFiniteRingKrullDimOfIsNoetherianRingOfIsLocalRing`,
  `Ring.krullDimLE_of_isLocalization_maximal`, Dedekind dimension-one results and
  `IsLocalRing.maximalIdeal_height_eq_ringKrullDim`. None compares every maximal
  localization of the normalization with its original base.
- `msearch.py ... leansearch "A finite normalization of a universally catenary local
  domain has the same Krull dimension at every maximal ideal"`: eight hits, primarily
  maximal-ideal height identities, existence of a maximal ideal attaining dimension,
  and local dimension bounds. No exact statement.
- `msearch.py ... loogle '"ringKrullDim", "integralClosure"'`: zero hits.
- `msearch.py ... grep
  'catenar|integralClosure.*ringKrullDim|ringKrullDim.*integralClosure' RingTheory`:
  zero hits.
- Direct `rg` with that catenarity/dimension pattern and the item id over the upstream
  `WeilConjectures/` and the project's `lean/Sheaf/`: no upstream exact theorem;
  project hits are the excellent-ring definitions, weakly etale component-dimension
  consumer, and the dimension-one normalization theorem. The latter assumes dimension
  one and does not state the general universally catenary comparison here.
- Direct search of the exact proposed declaration name across Mathlib,
  `WeilConjectures/` and `lean/Sheaf/`: no collision.
- `dag/lean_names_upstream.json` was searched for normalization and catenarity and the
  item id; only different scheme normalization and other normalization nodes appeared.
- No repair note exists for this item in `coord/repair-notes/`.

Validation: the prescribed `scompile.py NP lem-exc-weakly-etale-normalization-dimension`
compiled the delivered module both as sandbox and as its library module, with no errors
or warnings (about 2.0 s and 1.6 s). The only postponed theorem is the node's own statement.
There is no STATEMENT-DISPUTED flag or node fault.


## Second reading by NP

I am the fresh second reader, not the author of the module. I read the shared
node, sandbox node and Lean module side by side, Stacks algebra.tex lines
27512–27604 (Tag 02IJ, confirmed by tags/tags), the six statement dependency
records and their declaration sources, and the current proof-dependency records.
There is no repair note for this item, no statement_change, no new definition
node and no dependency module in this delivery.

The source introduces an injective finite-type map of domains R into S, with R
Noetherian, and primes q over p. Universal catenarity gives equality in its
height/transcendence-degree formula. For this node S is precisely the finite
normalization inside Frac(C): finite module implies finite type, the inclusion is
injective, S is a domain, and both fraction-field and residue-field transcendence
degrees vanish. Thus the source requires no additional excellence, normality of
C, characteristic, residue-field, or going-down hypothesis.

My complete object/hypothesis/conclusion checklist is:

- Commutative ring C: `{C : Type u} [CommRing C]`. Exact.
- C Noetherian: `[IsNoetherianRing C]`, the recorded Mathlib predicate in
  Noetherian.Defs (Noetherian as its own module, equivalently all ideals FG). Exact.
- C universally catenary: `(hC : IsUniversallyCatenary C)`, from the recorded
  `Sheaf.RingTheory.ExcellentRing`, not `IsExcellent`. I read IsPrimeChain,
  IsSaturatedPrimeChain, IsCatenaryRing and IsUniversallyCatenary in that module:
  finite chain-length bounds and equality of saturated lengths for every finite
  type algebra. Its Noetherian conjunct repeats an assumption, without adding one.
  Exact.
- C local with a unique maximal ideal: `[IsLocalRing C]` and
  `IsLocalRing.maximalIdeal C`. Mathlib's local-ring class is nontrivial, compatible
  with the node's explicit domain/nonzero convention. Exact.
- C a nonzero domain: `[IsDomain C]`. No zero divisors and nontriviality, with no
  extra normality assumption. Exact.
- K = Frac(C): `{K : Type v} [Field K] [Algebra C K] [IsFractionRing C K]`.
  I read IsFractionRing as localization at nonZeroDivisors C. Any realization is
  allowed, including the standard FractionRing C. Exact.
- C' the integral closure of C in that very K: `integralClosure C K`, the
  dependency's actual Subalgebra with carrier `{x | IsIntegral C x}`. Its canonical
  algebraMap is the inclusion of C into that subring of K. No arbitrary ring or
  arbitrary map replaces the normalization. Exact.
- C' finite as a C-module: `[Module.Finite C (integralClosure C K)]`, using the
  recorded notion (the top submodule is FG, a finite spanning set). Exact.
- Every maximal ideal m of C': `(m : Ideal (integralClosure C K)) [m.IsMaximal]`.
  No uniqueness or locality assumption on C' is present. Maximality supplies the
  prime instance needed by localization. Exact universal quantifier.
- Its contraction is the maximal ideal of C:
  `(hm : m.comap (algebraMap C (integralClosure C K)) =
  IsLocalRing.maximalIdeal C)`. This is precisely contraction along the canonical
  inclusion, with the same orientation of equality. Exact.
- Conclusion, with no additional clause:
  `ringKrullDim (Localization.AtPrime m) = ringKrullDim C`.
  I read Localization.AtPrime as localization at the prime complement and
  ringKrullDim as Order.krullDim of PrimeSpectrum in WithBot ℕ∞. These are the
  recorded dependency notions, and the displayed equality is exactly dim(C'_m) =
  dim C. Exact.

Edge cases: C a field gives dimension zero and is included; there is no positive
integer dimension binder or positive-height hypothesis. An integrally closed
local domain specializes to its own maximal localization. A semilocal
normalization with several maximal ideals is allowed, each quantified separately.
The zero ring and empty spectrum are excluded already by the node's domain
hypothesis, so no case was lost. There is no index family or integer parameter.
All characteristics are allowed. Universes u and v are bound independently:
K is a fraction-field realization, not a universe-bounded test algebra. The
Type u finite-type algebras in the dependency's universal-catenarity predicate
suffice in any larger universe as well, since every finite-type algebra has a
presentation by finitely many variables over C and hence a same-universe copy.
No new universe equality, smallness assumption, or unbound variable is present.

I independently repeated H4 searches with different words from the first reader:

- msearch.py leanfinder: “Every maximal ideal of a finite birational algebra over
  a catenary local integral domain has height equal to the dimension of the base”.
  Eight hits were generic maximal-ideal height identities, existence of a maximal
  ideal attaining dimension, and localization bounds; none says the item.
- msearch.py leansearch: “Krull dimensions of localizations at maximal ideals in a
  finite birational extension of a local ring with the dimension formula”. Eight
  hits, again the generic localization-height identity and local dimension bounds;
  no normalization comparison.
- msearch.py loogle: `"ringKrullDim", "Module.Finite"`: zero hits.
- msearch.py grep in RingTheory: `birational|equidimensional|universally.?catenary`:
  zero hits. Direct rg in Mathlib/RingTheory for height comparisons and integral
  closure dimension found Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown;
  I opened its signature and it assumes HasGoingDown, not given here. It is not
  an exact existing match.
- Direct rg across upstream WeilConjectures and project lean/Sheaf for the item
  id and full declaration name found no exact statement/name collision. Conceptual
  rg for birational, equidimensional, catenarity, normalization, dimension and height
  found the weakly-etale component-dimension consumer, excellent-ring definitions,
  and SemilocalNormalizationDimOne. I opened the latter's signature: it assumes
  dimension one and concludes global normalization properties, not this arbitrary
  dimension equality at every maximal localization. No duplicate was found.

H5/H6/H8/H9: there are no new definitions, hollow constructions, local notation,
private declarations or proofs beyond the single theorem's `by sorry`. The
source/blueprint module and theorem docstrings are present. The theorem docstring
faithfully carries all three proof steps, including algebraicity of the residue
extension and both append-the-final-prime comparisons of chain suprema. All
recorded statement modules are imported publicly; the available proof-only
modules are imported without public. The dimension-formula proof dependency
still has neither a Lean record nor Mathlib match, so omitting that unavailable
proof import is correct and does not affect the statement. No independent missing
notion or unusable dependency interface was found (H12/H13 do not apply).

No mismatch was found, and no Lean or mathematical node change was needed. I
left the correct module intact. I verified programmatically that lean.statement
is verbatim the file's signature and that the only node-field delta from the
shared base is lean; every Lean line is at most 100 characters. My independent
scompile.py run compiled this exact sandbox module and its library-path form
cleanly (1.3 s and 1.4 s), with no errors or warnings. The only second-reading
change is this appended independent review; the Worker report remains in place.
