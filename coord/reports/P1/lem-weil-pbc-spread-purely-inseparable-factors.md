## Worker report

Item: `lem-weil-pbc-spread-purely-inseparable-factors`.
Module: `Sheaf.AlgebraicGeometry.SpreadPurelyInseparableFactors`.
Declaration: `AlgebraicGeometry.exists_spread_purely_inseparable_factors`.
The module states the node with one theorem and `sorry`; it defines no new notion.
The node copy changes only `lean`. No statement correction, new node, or dependency module
is needed.

Hypothesis and conclusion matching:

- The Noetherian integral domain A is `(A : Type u)` with `[CommRing A]`,
  `[IsDomain A]`, and `[IsNoetherianRing A]`.
- Its fraction field K is `(K : Type v)` with `[Field K]`, `[Algebra A K]`,
  and `[IsFractionRing A K]`. Although K is not used in the conclusion, the node's
  named fraction field is retained explicitly.
- The finite étale A-algebra A' is `(A' : Type u)` with `[CommRing A']`,
  `[Algebra A A']`, `[Module.Finite A A']`, and
  `[Etale (Spec.map (CommRingCat.ofHom (algebraMap A A')))]`.
  This uses the dependency's scheme-morphism notion directly, with no alternate definition.
- A' is a domain by `[IsDomain A']`; its fraction field K' is `[Field K']`,
  `[Algebra A' K']`, and `[IsFractionRing A' K']`.
- The finite A'-algebra E is `(E : Type u)`, `[CommRing E]`, `[Algebra A' E]`,
  and `[Module.Finite A' E]`. Its domain hypothesis is `[IsDomain E]`.
- Its fraction field L is `(L : Type z)`, `[Field L]`, `[Algebra E L]`,
  and `[IsFractionRing E L]`.
- The finite purely inseparable extension L/K' is `[Algebra K' L]`,
  `[Module.Finite K' L]`, and `[IsPurelyInseparable K' L]`.
- `[Algebra A E]` and `[IsScalarTower A A' E]` encode the composite A-algebra structure
  used by the tensor products. `[Algebra A' L]`, `[IsScalarTower A' E L]`, and
  `[IsScalarTower A' K' L]` express that the fraction-field extension is induced by
  A' → E. These are compatibility data inherent in the stated fraction-field extension,
  not new mathematical restrictions. They imply injectivity of A' → E, since its
  composite into L agrees with the injective map through K'.
- A nonzero element of the original base is `∃ s : A, s ≠ 0 ∧ ...`.
- A_1 is `Localization.Away s`; A'_1 and E_1 are respectively
  `A' ⊗[A] Localization.Away s` and `E ⊗[A] Localization.Away s`.
  They appear as the domain and codomain of `Algebra.TensorProduct.map`.
- The induced algebra map is
  `Algebra.TensorProduct.map (IsScalarTower.toAlgHom A A' E)
  (AlgHom.id A (Localization.Away s))`, whose ring homomorphism sends
  `a' ⊗ t` to `algebraMap A' E a' ⊗ t`. Applying `Spec.map` to
  `CommRingCat.ofHom` of this map gives exactly Spec(E_1) → Spec(A'_1).
  The same expression appears in all three conclusions; no independent map is quantified.
- Surjectivity is the first `Surjective (Spec.map ...)` conjunct.
- Radiciality is `UniversallyInjective (Spec.map ...)`, the exact equivalent notion
  recorded by `def-weil-radicial-morphism` via Mathlib's Tag 01S4 theorem.
- The universal-homeomorphism conclusion is the final
  `(topologically IsHomeomorph).universally (Spec.map ...)` conjunct, as prescribed
  by `def-weil-universal-homeomorphism`. It quantifies over every base-change square.

Dependency declarations used (their full signatures and docstrings were read in the pinned
source checkout):

- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`.
- `def-weil-pbc-finite-purely-inseparable-extension`: `IsPurelyInseparable`,
  `Mathlib.FieldTheory.PurelyInseparable.Basic`; `Module.Finite`,
  `Mathlib.RingTheory.Finiteness.Defs` (imported transitively).
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale`,
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `def-weil-radicial-morphism`: its `mathlib_match` is
  `AlgebraicGeometry.UniversallyInjective`,
  `Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective`.
  `tfae_universallyInjective` identifies this with injectivity and purely inseparable
  residue-field maps. The dependency needs no `lean` record because it is a Mathlib leaf.
- `def-weil-surjective-morphism`: `AlgebraicGeometry.Surjective`,
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap` (imported transitively).
- `def-weil-universal-homeomorphism`: `CategoryTheory.MorphismProperty.universally`,
  `Mathlib.CategoryTheory.MorphismProperty.Limits`; `AlgebraicGeometry.topologically`,
  `Mathlib.AlgebraicGeometry.Morphisms.Constructors`; `IsHomeomorph`,
  `Mathlib.Topology.Homeomorph.Defs` (all imported transitively).

Edge cases checked before writing:

- Characteristic zero: purely inseparable fields have a surjective field inclusion;
  clearing denominators of finite generators makes E_1 = A'_1, giving the conclusions.
- Characteristic p > 0: p-power membership in the base forces unique primes and purely
  inseparable residue extensions. No prime or positive-characteristic restriction is added.
- Trivial extensions E = A', K' = L, including the identity cover, allow s = 1.
- A can itself be a field: the finite domain A' is then a field and the finite domain E
  is a field, so no shrinking is needed.
- Nonzero s and the compatible fraction maps keep the localized domain rings nonzero.
  The zero ring is excluded already by the node's integral-domain hypothesis; no extra
  nonemptiness condition on spectra is imposed.
- Non-normal and non-regular bases are allowed: no normality or regularity is assumed.
- Rings A, A', E use a common arbitrary universe u so that their spectra inhabit one
  scheme category, following the project's affine-scheme convention; fields have separately
  bound universes v, w, z. All universes and variables are explicit; autoImplicit is false.

Searches for an existing statement:

- `msearch.py ... leanfinder`: query "finite purely inseparable fraction field extension
  spreads to a surjective radicial morphism after localization". Eight results including
  `IsPurelyInseparable.isPRadical` and
  `IsPurelyInseparable.surjective_algebraMap_of_isSeparable`; no localization/spreading
  theorem with these hypotheses and conclusions.
- `msearch.py ... loogle`: query `IsPurelyInseparable, IsLocalization.Away`: zero hits.
- `msearch.py ... grep`: query `purelyInseparable|IsPurelyInseparable|UniversallyInjective`
  in AlgebraicGeometry: thirteen hits, concerning the definition and stability of
  universally injective maps; none give this spreading theorem.
- `msearch.py ... leansearch`: query "finite purely inseparable extension of fraction fields
  becomes universally injective and surjective after localization". Service unavailable
  (Internal Server Error); no verdict inferred from this search.
- `rg` over the source project's `WeilConjectures` and this project's `lean/Sheaf`, query
  `purely.inseparable|spread.*inseparable|lem-weil-pbc-spread-purely-inseparable-factors|
  IsPurelyInseparable`: related field-extension and base-change results, including the
  existing power-in-base lemma, but no declaration of this statement. The generic finite
  algebra splitting docstring cites the present item as a proof dependency only.
- Exact node-id search in `WeilConjectures`: zero hits. Exact chosen declaration/module
  search in `dag/lean_names_upstream.json`, `WeilConjectures`, and `lean/Sheaf`: zero hits.

Source check: the local literature file is absent, and the public raw GitHub URL returned
404. Read the complete recorded blueprint source over SSH from the server's read-only
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
lem-weil-pbc-finite-pushforward-generic-constructible.md`. Its finite-algebra calculation
has the two characteristic cases and the descent of localizations to A. Also opened
[Stacks 00GQ](https://stacks.math.columbia.edu/tag/00GQ),
[Stacks 0BR5](https://stacks.math.columbia.edu/tag/0BR5),
[Stacks 01S4](https://stacks.math.columbia.edu/tag/01S4), and
[Stacks 04DF](https://stacks.math.columbia.edu/tag/04DF) to check the cited criteria.
The docstring carries all three DAG proof steps and their dependency ids. No statement
fault or disputed statement was found.

Validation: `scompile.py P1 lem-weil-pbc-spread-purely-inseparable-factors
<SpreadPurelyInseparableFactors.lean>` compiled cleanly on the server in 1.9 seconds,
with exit code 0 and no warnings. The independent second reading remains for the next worker.

## Second reading by P1

I independently opened the sandbox node and module, all six statement-dependency
nodes, and the actual Mathlib declarations below. I read the complete blueprint
`sec-smooth-purity/sk-prop-sf-cbc/lem-weil-pbc-finite-pushforward-generic-constructible.md`
from the server's read-only literature directory. Its finite-algebra calculation
introduces a Noetherian domain A, a finite étale domain A', and finite domain factors
D_j with purely inseparable fraction fields over K'. It treats characteristic p by
clearing denominators of powers, characteristic zero by clearing denominators of
finite generators, and brings the localizations back to A. I also read the server's
Stacks .tex at `algebra-lemma-integral-overring-surjective` (00GQ),
`algebra-section-universal-homeomorphism` (0BR5),
`morphisms-lemma-universally-injective` (01S4), and
`morphisms-lemma-universal-homeomorphism` (04DF). These criteria assume no additional
normality, regularity, perfectness, separatedness, or characteristic restriction.

The node's objects, hypotheses and conclusion clauses, matched individually:

- A: `A : Type u`, `[CommRing A] [IsDomain A] [IsNoetherianRing A]`.
  Verdict: exactly the Noetherian integral domain.
- K: `K : Type v`, `[Field K] [Algebra A K] [IsFractionRing A K]`.
  Verdict: precisely the named fraction field; its absence from the conclusion is
  consistent with the node.
- A': `A' : Type u`, `[CommRing A'] [Algebra A A'] [Module.Finite A A']`
  and `[Etale (Spec.map (CommRingCat.ofHom (algebraMap A A')))]`.
  Verdict: finite étale A-algebra, using the dependency's actual scheme notion.
- A' is a domain: `[IsDomain A']`. Verdict: exact.
- K': `K' : Type w`, `[Field K'] [Algebra A' K'] [IsFractionRing A' K']`.
  Verdict: its fraction field, not an arbitrary auxiliary field.
- E: `E : Type u`, `[CommRing E] [Algebra A' E] [Module.Finite A' E]`.
  Verdict: finite A'-algebra, not merely finite type.
- E is a domain: `[IsDomain E]`. Verdict: exact.
- L: `L : Type z`, `[Field L] [Algebra E L] [IsFractionRing E L]`.
  Verdict: its fraction field.
- L/K': `[Algebra K' L] [Module.Finite K' L] [IsPurelyInseparable K' L]`.
  Verdict: the finite purely inseparable extension in all characteristics.
- Induced extension and composite base action: `[Algebra A E]`
  `[IsScalarTower A A' E]`, `[Algebra A' L]`,
  `[IsScalarTower A' E L] [IsScalarTower A' K' L]`.
  Verdict: compatibility already inherent in the node's induced fraction-field
  extension and tensor products. This excludes an unrelated field embedding,
  without imposing a new condition: both routes A' → L agree. Their equality and
  the injective A' → K' → L show A' → E is injective, as the node's proof requires.
- Shrinking parameter: `∃ s : A, s ≠ 0 ∧ ...`. Verdict: one nonzero element of
  the original base A, not merely an element of A'. The existential follows all
  the data and hypotheses.
- A_1: `Localization.Away s`. Verdict: A[1/s].
- A'_1 and E_1: the source and target of `Algebra.TensorProduct.map` are
  `A' ⊗[A] Localization.Away s` and `E ⊗[A] Localization.Away s`.
  Verdict: the two tensor products required by the node.
- Induced scheme morphism: `Spec.map (CommRingCat.ofHom
  (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A A' E)
  (AlgHom.id A (Localization.Away s))).toRingHom)`.
  Verdict: contravariance gives Spec(E_1) → Spec(A'_1), and `map_tmul` sends
  a' ⊗ t to (algebraMap A' E a') ⊗ t. All three clauses concern this same map.
- Surjectivity: first `Surjective` conjunct. Verdict: exactly surjective on points.
- Radiciality: second `UniversallyInjective` conjunct. Verdict: exactly equivalent
  to injectivity and purely inseparable residue maps by `tfae_universallyInjective`,
  item 3, Mathlib's theorem tagged 01S4.
- Universal homeomorphism: final `(topologically IsHomeomorph).universally` conjunct.
  Verdict: every pullback map is a homeomorphism on underlying spaces, including
  arbitrary non-affine base changes; no replacement by an ordinary homeomorphism.

Dependency-source reading: `Algebra/Algebra/Defs.lean:95` gives Algebra;
`FieldTheory/PurelyInseparable/Basic.lean:107,211` gives IsPurelyInseparable and its
power criterion (exponential characteristic 1 in characteristic zero);
`RingTheory/Finiteness/Defs.lean:117` gives Module.Finite;
`AlgebraicGeometry/Morphisms/Etale.lean:41` gives affine-locally étale maps;
`UniversallyInjective.lean:47,107` gives universal injectivity and the radicial
criterion; `UnderlyingMap.lean:59` gives Surjective;
`Constructors.lean:259`, `CategoryTheory/MorphismProperty/Limits.lean:872`, and
`Topology/Homeomorph/Defs.lean:511` give topologically, universally, and IsHomeomorph.
All records are usable directly; no dependency module or new definition node is
needed. The upstream IsUniversalHomeomorphism class was also read: the existing
inline predicate is exactly the recorded dependency, not a duplicated definition.

Edge cases: no index set or product multiplicity is quantified, so an empty family
is irrelevant. Zero rings and empty affine spectra are excluded by IsDomain,
already in the node, rather than by an added hypothesis. Nonzero s leaves the
localized domains nonzero. A may be a field, and the identity factor E = A' is
included (s = 1 suffices). Non-normal and non-regular domains are included.
Characteristic zero includes mixed-characteristic domains: after localization
finite birational E becomes A'; it need not coincide before shrinking. In positive
characteristic the exponent n may be zero; no positive exponent assumption or
chosen prime is added. The three rings share an arbitrary universe u, as required
by Spec maps in one Scheme category; different original sizes can be placed in a
common larger universe, and the three fraction fields have independently bound
universes v, w, z. No small test universe makes a universal quantifier vacuous.

Independent searches (different queries from the worker):

- `msearch.py ... leanfinder`: "localization of a finite domain algebra with
  radicial generic fibre is a universal homeomorphism" returned eight results.
  I opened `PrimeSpectrum.isHomeomorph_comap` and
  `PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable`: the former assumes
  the powers already lie in the ring image and the latter concerns field base
  change, so neither supplies this localization theorem.
- `msearch.py ... loogle`: `IsPurelyInseparable, Algebra.TensorProduct.map`
  returned `PrimeSpectrum.isHomeomorph_comap_tensorProductMap_of_isPurelyInseparable`.
  I read its full signature in `Spectrum/Prime/Homeomorph.lean`: it tensors the
  fields K and L themselves with an arbitrary algebra S. It does not state the
  existence of a localization for finite domain models A' and E.
- `msearch.py ... grep`: `radicial|[Uu]niversal.*[Hh]omeomorph|inseparable.*locali`
  returned the two headings in `Spectrum/Prime/Homeomorph.lean`, no exact match.
- Direct `rg` in both `WeilConjectures` and `lean/Sheaf` with
  `radicial|spread.*(inseparable|factor)|inseparable.*locali|universally.*homeomorph`
  and the exact node id found the upstream universal-homeomorphism API and related
  sheaf/base-change modules. I opened UniversalHomeomorphism,
  GenericFiniteAlgebraSplitting, and HomeomorphPurelyInseparableBaseChange.
  The splitting module cites this item in its proof docstring; the other two
  concern universal-homeomorphism properties and base change of fields. None
  already states the item's theorem.

No mismatch was found, and no correct Lean or node text was rewritten. The only
change in this reading is this independent review section. There is no statement
correction, so the correction/citer-verdict procedure does not apply. The module
contains one theorem with proof `sorry`, no definitions, private copies, local
notation or local instances, and no hidden `let`/`show` statement binders. Its
source/blueprint docstrings reproduce all three DAG proof steps, including descent
of s' to s, the two characteristic cases, and the 04DF criterion. I checked the
node's lean.statement is verbatim the file signature, every universe and variable
is explicitly bound, and all lines have at most 100 characters.

Validation: the required `scompile.py P1 lem-weil-pbc-spread-purely-inseparable-factors
.../SpreadPurelyInseparableFactors.lean` compiled on the server in 1.9 seconds,
exit code 0, with no errors or warnings.
