## Worker report

Item: lem-pur-rational-lattice-adic-domain. Module:
`Sheaf.Paper.RationalLatticeAdicDomain`. Four theorem statements, each with proof
`sorry`, jointly render the node. No definitions, new nodes, dependency repairs,
or statement corrections are needed. No statement dispute was found.

Hypothesis and clause correspondence:

- `P : PurityFiniteSetting.{u}` supplies the recorded finite-field datum p,a,q,k0,k,
  its primality, positive exponent, algebraic closure, the distinct prime
  `P.coefficients.l`, the fixed coefficient closure, and the literal finite
  intermediate extension `P.extension`. Its ring, uniformizer and all positive
  quotients are the existing Padic coefficient-extension constructions. The bundled
  positive level in P is not used to restrict the quantified reduction levels.
- `T : Scheme.{u}` with `[T.Over (Spec (.of P.field.k))]` is the k-scheme.
  `LocallyOfFiniteType` and `QuasiCompact` on its structure morphism say finite type;
  `IsSeparated` says separated. No Noetherianity, dimension, invertibility, finite-Tor,
  or torsion-free premise is added.
- `rational_lattice_adic_base` concludes `IsNoetherian T`, an explicit natural
  bound on `topologicalKrullDim T`, and invertibility of ell in every
  `T.presheaf.stalk x`. These are precisely the applicability conditions of
  `PbcRationalDerivedCategory`, whose underlying category is `PbcRationalCategory`.
- `rational_lattice_integral_comparison` equates `sfIntegralConstructible` with
  `PbcIsBoundedConstructibleComplete` after the existing
  `integralDetailedTransport`. This transport is restriction along the canonical
  `integralDetailedCoefficientComparison`, uniquely fixed by every finite
  projection. Thus it compares the actual completed coefficient sheaves and
  reductions, rather than choosing a different coefficient ring or category.
  PBC compatible etale-origin witnesses are retained in its existing predicate.
- The ambient integral object K is in `DerivedCategory (scalarReductionSource ... )`.
  `scalarReductionDerivedExtension ... n` is the recorded derived change of rings
  along the completed-ring projection, with its quotient-module action. Its index n
  means exponent n+1, so index 0 is precisely K_(0,1) and all positive exponents occur.
- `rational_lattice_reduction_tor` assumes exactly integral constructibility,
  integers r,s, `r ≤ s`, and residue cohomological support contained in
  `Set.Icc r s`. It concludes `∀ n : ℕ, HasProEtaleTorAmplitude ... n ... r s`.
  In particular the interval is fixed before quantifying levels. This is the
  original representative-independent Tor predicate of the dependency node, still
  published and used by its recorded integral finite-Tor definition. The newer
  independent-universe interface is imported as well; no private Tor predicate or
  additional equality of universes is introduced.
- `rational_lattice_adic_domain` first asserts existence of an ordered residue
  interval for every integral constructible K and its membership in
  `finiteTorConstructibleIntegral`. The latter includes constructibility and one
  ordered Tor interval for every positive reduction, exactly D^b_ctf(T,O_E).
  Its second clause quantifies over every object L of the actual raw
  `PbcRationalCategory`. `L.obj.obj` is its integral underlying object. It has a
  detailed integral presentation K, an isomorphism from the actual canonical
  transport of K to that underlying object, and the finite-Tor property for K.
  This existence is a mathematical conclusion about presentations, not a hollow
  definition or an arbitrary chosen map. Every integral PBC object is retained
  by raw localization, so the quantification includes every integral representative.
  No Karoubi completion and no torsion-free restriction occurs.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`, its
  fields and `coefficientPrime_isUnit_stalk`.
- `Sheaf.Paper.PbcRationalCategory`: `PbcRationalCategory`,
  `PbcRationalDerivedCategory`, `pbcRationalization` in namespace
  `AlgebraicGeometry.Scheme`.
- `Sheaf.Paper.IntegralUniformCoefficient`: `pbcBoundedConstructibleComplete` and
  `IsPbcBoundedConstructibleComplete`; the underlying published predicate and
  `pbcIntegralDatum` in `Sheaf.Paper.BoundedConstructibleComplete` are used for
  the same universe lift already used by the rational category. This is not a
  dependency redefinition: the wrapper with E : Type(u+1) is an additional
  specialization, whereas the recorded rational category uses E : Type u and
  the canonical ULift of its valuation ring.
- `Sheaf.Paper.SfIntegralConstructible`: `WeilConjectures.sfIntegralConstructible`.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`:
  `WeilConjectures.scalarReductionSource`, `scalarReductionDerivedExtension`.
- `Sheaf.AlgebraicGeometry.RingedProEtaleTorAmplitudeOfUniverses`:
  `CategoryTheory.HasRingedSiteTorAmplitudeOfUniverses`; its public predecessor
  `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude` supplies
  `AlgebraicGeometry.Scheme.HasProEtaleTorAmplitude`, used by the integral predicate.
- `Sheaf.Paper.FiniteTorAmplitudeSites` publicly imports
  `Sheaf.Paper.FiniteTorAmplitude`, containing
  `WeilConjectures.finiteTorConstructibleIntegral`.
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`:
  `integralStratifiedPerfectDetailed`, `integralDetailedCoefficientComparison`,
  `integralDetailedTransport`. This already-recorded proof dependency supplies
  the statement's canonical comparison, so its import is public.
- Proof-only imports follow the DAG: finite-type dimension
  `AlgebraicGeometry.exists_topologicalKrullDim_le`; Mathlib Noetherian ascent
  `LocallyOfFiniteType.isLocallyNoetherian` and
  `QuasiCompact.compactSpace_of_compactSpace`; the adic coefficient datum and its
  quotient normalization; `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel`;
  `Padic.extension_integers_dvr`; and
  `AlgebraicGeometry.Scheme.proEtale_torAmplitude_iff_residue_tensor`.
- `def-weil-scheme-morphism-properties` is explicitly a convention node with no
  declaration. Its named Mathlib scheme/morphism properties are used directly.

Edge cases checked before writing: empty T and zero K allow [0,0]; for exponent
one the residue reduction is the first reduction; natural index n covers every
positive exponent n+1, excluding only the source-excluded exponent zero. On a
geometric point the torsion object O_E/(varpi) has reduction complex
[A_n --varpi--> A_n] in degrees -1,0, giving interval [-1,0] uniformly, including
n=1 where the differential is zero. All intervals containing residue support,
not only one chosen interval, are allowed. No nonemptiness, connectedness,
smoothness or torsion-freeness assumption was introduced. The pro-etale site keeps
objects in u+1, morphisms in u, and module values in u+1 as in the published API.

Searches for an existing complete statement:

- msearch.py leanfinder: "Derived complete integral constructible complexes have
  uniformly bounded Tor amplitude after all uniformizer reductions": 8 hits,
  all generic derived-category degree-bound declarations, no full node match.
- msearch.py loogle: `"torAmplitude"`: 0 hits.
- msearch.py grep: `derivedComplete.*[Tt]or|[Tt]or.*derivedComplete|residue.*torAmplitude`:
  0 Mathlib hits.
- msearch.py leansearch: "Integral constructible derived complete sheaves have
  uniformly bounded Tor amplitude after reduction modulo powers of a uniformizer":
  8 hits, ordinary AdicCompletion/IsAdicComplete and a tilde module sheaf, no match.
- rg over both lean/WeilConjectures and lean/Sheaf for rational/lattice/Tor,
  `integralDetailedTransport` and `finiteTorConstructibleIntegral`; exact node-id
  search over lean/WeilConjectures found no existing declaration for this item.
  `Sheaf.Paper.IntegralResidueTor.integral_residue_tor` covers the Tor step but
  does not assert this node's geometric applicability, PBC integral comparison,
  or every raw-rational representative clause. It therefore is not a complete
  existing match. No duplicate definition is introduced.

Validation: scompile.py compiled this exact module both as sandbox and under its
library module name with no errors or warnings (about 3 seconds per pass).
All variables/universes are explicit (`autoImplicit false`); every theorem has
only `sorry` as proof, with the relevant node proof steps in its docstring.

## Second reading by Q149

The dispatcher starts this worker directly and explicitly prohibits other agents;
therefore this section records a second self-audit, not an invented independent
reader. The maintainer's independent review remains the independent reading.

Reopened the node and the completed module. Checked each of the eight statement
dependencies and the five proof steps against the four declarations. The initial
draft used a bundled Over object; the final version uses the project's preferred
Scheme.Over instance for a scheme over a field. No mathematical condition changed.
The geometric conditions are conclusions rather than extra premises. The integral
comparison uses the exact projection-normalized published transport. The residue
interval is arbitrary and precedes the universal positive-level quantifier.
The final raw-localization clause uses L.obj.obj, preserving the PBC integral
underlying object, and an actual derived-category isomorphism to its detailed
presentation. This checks the category bridge rather than silently pretending
the two ambient Lean types are definitionally equal. No new data, dependent
modules, statement corrections or false-statement flags remain.
