## Worker report

The module `Sheaf.Paper.GeneralLfpAdicInputWitness` states
`AlgebraicGeometry.ProEtale.generalLfpAdicInputWitness`, with proof `sorry`.
It assembles the general-lfp input characterization; it does not assume adic
completeness or scalar local models. Four fully defined helpers specify the
canonical coefficient normalization, the termwise section-action transport of
the same input object, the published adic predicate after localization, and
the normalized finite-residue comparison. These are
parts of this node's coefficient presentation, not independent new notions.

Hypotheses, one by one:

- The prime ell is `l : ℕ` and `[Fact l.Prime]`.
- The positive characteristic of the field is `p : ℕ`, `[Fact p.Prime]`,
  `k : Type u`, `[Field k]`, `[CharP k p]`. The prime binder expresses positive
  field characteristic; no characteristic-zero or composite-characteristic
  field is admitted. `_hpl : p ≠ l` is the unequal-characteristic hypothesis.
- A k-scheme is `X : Over (Spec (CommRingCat.of k))`. Finite type is precisely
  `[LocallyOfFiniteType X.hom] [QuasiCompact X.hom]`; separatedness is
  `[IsSeparated X.hom]`. The conclusions concern `X.left`.
- The finite coefficient extension is `E : Type u`, `[Field E]`,
  `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]`. This is the dependency's
  presentation of finite ell-adic extensions; choosing an embedding into the
  algebraic closure has no role in this statement about one extension.
- R, t and A are exactly the dependency's
  `Padic.coefficientExtensionIntegers l E`,
  `Padic.coefficientExtensionUniformizer l E`, and
  `Padic.coefficientExtensionRing l E 1`. The latter is quotient by the first
  power of the uniformizer ideal, not exponent zero. The completion interface
  uses their canonical `ULift` through `IntegralConstantCompletion.integers`
  and `.ideal`. Lattice integers use `WithAbs` only to install the valuation
  topology on the same subring.
- B is the actual continuous condensed ring `integralCondensedRing l E`,
  pulled back by `condensedRingObj ... X.left`. The input category
  `ModuleObjectRingedComparison.Internal` is the existing abbreviation for
  its module objects. `M` belongs to its ordinary unbounded derived category.
- `_hM : boundedConstructible ... M` uses the recorded GENERAL ring-object
  predicate, not `constantModelBoundedConstructible`, a finite-Tor subcategory,
  or a complete subcategory. It imposes bounded cohomology and constructible
  local finite presentation with arbitrary section matrices.

Conclusions, one by one:

- `CompactSpace X.left ∧ IsLocallyNoetherian X.left` gives exactly Noetherian
  in the node's stated convention. `QuasiSeparatedSpace X.left` is the
  recorded scheme equivalent of quasi-separatedness of the terminal morphism.
- `IsDiscreteValuationRing ...` is the DVR assertion for R. `IsField A ∧
  Finite A ∧ CharP A l` gives the finite residue field and its characteristic,
  without assuming unramifiedness or choosing a new field structure.
- The existential ring isomorphism `c` identifies the actual reconstructed
  section-ring sheaf of B with `Scheme.adicLisseCompletedRing X.left ideal`.
  The latter is the genuine inverse limit of `adicLisseRingSystem`, whose
  term at n is the constant ring R/(t)^(n+1), with quotient factor maps.
  Inverting `c` gives the direction B to limit written in the node.
  `IsNormalized` equates c on every constant scalar with the existing
  `FiniteDiscreteOrdinary.canonicalAbelianMap`; the following universal
  equality of normalized isomorphisms records canonicity, rather than an
  arbitrary isomorphism. Fixing integral scalars fixes all finite quotients.
- `HasResidueComparison` gives the existing `FiniteDiscreteOrdinary.Encoding`
  of the DISCRETE ring A on this scheme. Its `ringIso` and `normalization`
  identify the pulled-back continuous finite residue ring canonically with
  the constant ring sheaf. Its specified ordinary and fixed functors are
  section-action and restriction along constant scalars. Monoidality of the
  actual termwise derived equivalence records the ordinary relative derived
  tensor comparison; every ordered Tor interval is preserved. The final
  equivalence identifies `HasFiniteConstantLocalModel` with the existing
  ordinary finite constant local models. No topology is imposed on M.
- `∀ q : ℤ, IsConstantModelConstructible ... (H^q M)` is the scalar-model
  conclusion in every degree, using the recorded predicate. Its finite
  presentations allow torsion R-modules; freeness is not required.
- `transport ... c` is the termwise functor to the ringed-site presentation.
  The concluding existential gives a cochain representative P and an explicit
  derived isomorphism `Q.obj P ≅ M`; applying the functor to P and localizing
  therefore reads the SAME input object. The functor applies the existing
  section-action equivalence termwise and restricts scalars along c.
  All data are explicitly constructed; no completion functor and no object
  selected from a mere existence theorem occurs here.
- `IsAdicRepresentative ... ((transport ... c).obj P)` unfolds to
  `Scheme.IsSfbAdicConstructible ... (Q.obj ((transport ... c).obj P))`, the already
  published full adic predicate. Its first conjunct `IsSfbAdicComplete` uses
  the equivalent small site and the kernel of the actual residue projection;
  for these Noetherian coefficients this is precisely the locally derived
  (t)-complete condition in the recorded dependency.
- Its second conjunct supplies a cochain complex C on `X.smallEtaleTopology`
  with coefficients in the lifted first quotient. The explicit existence of
  ordered cohomological bounds is boundedness of C; every `C.homology q`
  satisfies `IsConstructibleSheaf`. Finitely generated stalk models over the
  residue field mean finite-dimensional cohomology, not finite underlying
  sets in an unrelated coefficient ring. On a Noetherian scheme this finite
  global stratification notion equals the recorded affine-local notion.
- That same predicate includes a `Nonempty` ISOMORPHISM IN THE DERIVED
  CATEGORY between `sfbResidueComplex ...` and the termwise comparison
  inverse image of C. Its inverse is the direction nu* C to M tensor^L A.
  `sfbResidueComplex` is the actual derived extension of scalars along the
  exponent-one quotient, followed by fixed scalar restriction. The coefficient
  identifications and section-action equivalence above retain this tensor.
- The last conjunct of that predicate is `∃ a b : ℤ, a ≤ b ∧ ∀ N q, ...`.
  N ranges over ALL degree-zero etale residue-module sheaves; the same interval
  works for every N. `sfbEtaleTensorDegreeZero` computes derived tensor here
  since the residue is a field and stalks detect exactness. Vanishing is
  `IsZero` for q<a or b<q. This is not merely a stalkwise or finite-N test.

Dependency declarations used, with their modules:

- `Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale` publicly
  retains `AlgebraicGeometry.ProEtale.boundedConstructible` and the general
  local finite presentation notion from the upstream module-object framework.
- `Sheaf.Paper.IntegralLfpConstantModelComparison` supplies
  `integralCondensedRing`, `integralCoefficientRing`, and the proved
  `integralLfpConstantModelComparison`; this publicly imports the recorded
  continuous and pulled-back coefficient declarations.
- `Sheaf.Paper.CondensedConstantConstructibility` supplies
  `IsConstantModelConstructible` and `HasFiniteConstantLocalModel`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` supplies the
  coefficient constructions and `Padic.finite_coefficientExtensionRing`;
  `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr` supplies
  `Padic.extension_integers_dvr`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit` supplies the
  canonical `AlgebraicGeometry.ProEtale.sfb_integral_coefficient_limit`.
- `Sheaf.Paper.InternalSectionTotalComparison` supplies
  `ModuleObjectRingedComparison.ring`, `.Internal`, `.Modules`,
  `.complexForward` and the exact section-action equivalence.
  `Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison` supplies
  `.moduleObject_ringedSite_derived_comparison`, including tensor and slice
  normalization, as a proof dependency.
- `Sheaf.Paper.FiniteDiscreteOrdinaryEncoding` supplies `.Encoding`,
  `.canonicalAbelianMap`, `.ordinaryLocalModel` and the actual derived
  equivalences. `Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence` supplies
  `.moduleObject_ordinary_coefficient_equivalence` as a proof dependency.
- `Sheaf.AlgebraicGeometry.IntegralConstantCompletion` supplies the lifted
  coefficient integers and fixed uniformizer ideal.
- `Sheaf.Paper.AdicStratifiedPerfectData` supplies
  `Scheme.IsSfbAdicConstructible`, `IsSfbAdicComplete`, `sfbResidueComplex`,
  `sfbEtaleTensorDegreeZero`, and publicly imports the site comparison
  `ProEtale.comparisonUpperStar`.
- `Sheaf.Paper.IntegralCohomologicalAdicCriterion` supplies
  `Scheme.integral_cohomological_adic_criterion`, the final proof step.
- `Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete` supplies the
  recorded local-completeness notion used by the existing adic presentation.
- `Sheaf.AlgebraicGeometry.CoefficientConstructibleEtaleModules` supplies the
  recorded etale constructibility presentation, equivalent to the reused
  finite-global predicate for Noetherian X.
- Mathlib supplies `CompactSpace`, `AlgebraicGeometry.IsLocallyNoetherian`,
  `QuasiSeparatedSpace`, `CategoryTheory.constantSheaf`, ordinary derived
  localization and cohomology. Scheme preparation uses the recorded Mathlib
  affine qcqs and finite-type-over-Noetherian declarations. The setting's
  finite-type and separated assumptions are stated on X's structure map;
  no compactification is required for this node's input assertion.

Source reading: Bhatt--Scholze Definitions 6.5.1 and 6.8.10, Proposition
6.8.11(3), coefficient convention and Lemma 4.2.12; the current blueprint's
`lem-sfb-dc-hom-preserves.proof.md`, integral first sentence; Stacks 01T6
(`morphisms.tex`, finite-type-noetherian) and 01OY (`properties.tex`,
locally-Noetherian-quasi-separated). The theorem docstring carries all five
DAG proof steps with the named dependencies. Definitions contain real data.

Edge cases read mathematically: X empty and M=0 give zero module categories
and valid ordered zero intervals. Torsion M=R/(t) on a point is permitted:
its derived reduction can have degrees -1 and 0; no flatness was imposed.
Arbitrary ramification and ell=2 are admitted. Positive quotient indexing
avoids the zero ring R/(1). Strata/covers retain their existing empty cases.
The original pro-etale site's object universe is u+1 and morphism universe u;
module coefficients live in u+1. The ordinary derived localizations use their
published universe conventions, not a forced equality of site universes.

Searches performed (the launcher also saved exact outputs in searches.jsonl):

- LeanFinder via msearch.py: "A bounded constructible complex of locally
  finitely presented integral ell-adic module sheaves is locally derived
  complete and admits a constructible etale residue complex of finite Tor
  amplitude". Hits included BDeRhamPlus, BDeRham, SheafOfModules finite
  presentation and CondensedMod.IsSolid; no exact statement.
- Loogle via msearch.py: `"DerivedCategory", "IsAdicComplete"`: no hits.
- Mathlib grep via msearch.py:
  `(constructible|proetale).*(complete|residue)|(complete|residue).*(constructible|proetale)`:
  no hits.
- LeanSearch via msearch.py: "Bounded constructible integral adic module
  sheaves are locally derived complete and have constructible etale residue
  models of finite Tor amplitude": ordinary IsAdicComplete and AdicCompletion
  declarations only, no exact match.
- rg/grep in both named project source trees for the node id and the
  constructible/completion/residue patterns found the existing constituent
  comparisons above, not this assembled general-lfp input assertion. Recorded
  dependency signatures and docstrings were read. No second notion is defined.

Instance-elaboration repair: importing the proof dependencies exposes
`WeilConjectures.integralCoefficientAbLocallyBijective.{u,v}`, whose inferred
maximum universe can leave v unresolved. `IsAdicRepresentative` fixes this
published instance to `{u,0}` inside its definition, along with the existing
abelian and standard localization instances. These are constructed instances,
not hypotheses or file-local instances. The original site universes are intact.
Its owning module is publicly imported: `Sheaf.Paper.CompletedIntegralCoefficients`.

No mathematical statement correction, new node, or dependency replacement is
needed. Only the item's lean record is changed. No STATEMENT-DISPUTED finding.

Validation: all compilations use scompile.py against the live published library.
The first dry run found the preflight scanner did not retain the parent
namespace after a combined namespace opening. The namespace openings were
separated; mathematical signatures are unchanged. The final compile and
deliver2.py preflight results are recorded by the delivery wrapper; only the main theorem's expected sorry warning is allowed.

## Second reading by Q83

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
