## Worker report

The module Sheaf.TraceFormula.AlmostFiniteResidueFieldDegree states
RingTheory.almostFinite_residueField_fractionDegree, with exactly one postponed
proof (`sorry`). It also constructs RingTheory.quotientFractionRingMap with real
data, using Mathlib's existing quotient map and fraction-field lift. This helper
belongs to the induced extension in this item; it introduces no independent
notion, assumes no integrality, and is listed in lean.declarations.

The source is Swanson–Huneke, Proposition 4.8.5, printed p. 85 (PDF p. 98):
https://www.math.purdue.edu/~iswanso/book/SwansonHuneke.pdf . I read the proposition
and its proof. The node is its domain/finite-field-extension specialization;
embedding a finite field extension in an algebraic closure changes no hypothesis.

Hypothesis and clause correspondence:

- The commutative Noetherian domain is `(R : Type u) [CommRing R]
  [IsNoetherianRing R] [IsDomain R]`. IsDomain includes nontriviality and absence
  of zero divisors. The zero ring is excluded exactly as the node requires.
- `K = Frac(R)` is Mathlib's `FractionRing R`, its canonical localization at the
  nonzero divisors. In a domain these are precisely the nonzero denominators.
- The finite extension is `(F : Type v) [Field F]
  [Algebra (FractionRing R) F] [FiniteDimensional (FractionRing R) F]`.
  `[Algebra R F] [IsScalarTower R (FractionRing R) F]` expresses the stipulated
  inclusion of R as the composite through its fraction field, not extra data
  unrelated to the finite extension. Every extension admits this composite.
- The subring containing R is `(C : Subalgebra R F)`. Each such subring determines
  exactly such a subalgebra, since it contains the image of R. Its integrality
  is precisely `hC : C ≤ integralClosure R F`, because the carrier of
  integralClosure is `{x | IsIntegral R x}`.
- The prime is `(Q : Ideal C) [Q.IsPrime]`. The contraction P is written directly
  `Q.comap (algebraMap R C)`. No extra prime or contraction assumption is imposed.
  Comap of a prime is prime; the two quotient rings are domains by instances.
- The fields in the conclusion are literally
  `FractionRing (R ⧸ Q.comap (algebraMap R C))` and `FractionRing (C ⧸ Q)`.
  The scalar action is explicit through `Module.compHom` of
  `quotientFractionRingMap R C Q`; this is the canonical induced field map,
  not an arbitrary algebra structure. The helper composes the injective
  `Ideal.quotientMap Q (algebraMap R C) le_rfl` with the canonical map of C/Q
  to its fraction field, then applies `IsFractionRing.lift` to its injection.
  Thus it sends a/b to the quotient of the two images. The injection proof uses
  only existing Mathlib lemmas; the definition contains no postponed proof.
- `@FiniteDimensional ...` for that action is exactly finite degree of the
  induced extension. There is no Module.Finite R C or finite-type hypothesis.

Statement dependencies read and used:

- Mathlib.RingTheory.Noetherian.Defs: IsNoetherianRing (all ideals finitely generated).
- Mathlib.Algebra.Algebra.Defs: Algebra (the field-extension homomorphism).
- Mathlib.RingTheory.IntegralClosure.Algebra.Basic: integralClosure, with
  IsIntegral from IsIntegral.Defs (monic polynomial root).

The full signatures and docstrings were read, including the integralClosure
carrier and IsIntegral definition. Proof dependency imports include the recorded
Mathlib modules and Sheaf.RingTheory.AdicCompletionNoetherianOfQuotient,
Sheaf.RingTheory.NormalizationCompletedBranchLift, Sheaf.RingTheory.NagataOfCompleteLocal,
and Sheaf.RingTheory.JapaneseDomain. Their source statements were read. The theorem's
docstring records all eight node proof steps and the relevant dependency ids.

Edge cases checked: Q = 0 and P = 0 are permitted; no nonzero-prime restriction.
Maximal and nonmaximal primes both occur. C equal to the image of R and C equal
to the full integral closure are included. F = Frac(R), the degree-one extension,
is allowed. R may be a field. No perfectness, characteristic, separability,
normality, or module-finiteness condition is imposed. Universes u and v are
independent; C inherits F's universe and there is no test-object universe restriction.
The hypothesis hC is not automatic: an element of F may have a denominator
that is not integral over R.

Searches performed:

- msearch.py leanfinder: “An integral subring of a finite extension of the fraction
  field of a Noetherian domain has finite residue field extensions at every prime”.
  Eight hits: QuasiFinite.instFiniteResidueField and related quasi-finite results,
  algebraicity of residue extensions of integral algebras, finite local modules.
  None states the item without an extra quasi-finite or finite-module assumption.
- msearch.py loogle: `"ResidueField", "IsIntegral"`. Four hits: integral residue
  algebra/tower structures, algebraicity, and separability over perfect residue
  fields; none asserts finite degree in this generality.
- msearch.py grep: `ResidueField|residueField` in RingTheory/IntegralClosure.
  No hits.
- msearch.py leansearch: “Residue field extensions of integral subrings in finite
  fraction field extensions of Noetherian domains are finite dimensional”.
  Eight hits including instFiniteDimensionalFractionRingOfFinite, which assumes
  module finiteness and is only the proof dependency, not the present statement.
- rg over WeilConjectures, Mathlib, and shared lean/Sheaf for almost-finite,
  residue-field-degree and finite fraction-field combinations: no exact match.
  In particular PrincipalPrimeQuotientFractionFinite assumes a principal
  contracted prime; it does not cover every prime as this item requires.
- rg for quotientFractionRingMap, almostFinite_residueField_fractionDegree and
  this node id in upstream WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json:
  no declaration collision or prior implementation found.

No node correction, new node, dependency repair, or statement dispute is needed.

## Second reading by Q150

I reread the node and final file clause by clause. This is a worker self-check;
the dispatch brief assigns the independent reading to the maintainer and forbids
starting other agents. The base, domain, Noetherianity, finite extension, integral
subring, arbitrary prime, contraction, both exact quotient fraction fields, and
finite degree all match as detailed above. An initial draft omitted the scalar
module instance, which failed elaboration; the final statement explicitly fixes
that instance by the canonical fraction-field map, without adding a hypothesis.
The helper uses actual Mathlib quotient and lift constructions, with proved
injectivity supplied by existing lemmas. The proof plan now correctly places the
finite model inside F's normalization, not inside the arbitrary C. No remaining
mathematical mismatch was found.

Process deviation: during signature inspection I mistakenly wrote a temporary
`/tmp/check.lean` probe and ran it directly with `lake env lean` in the read-only
source checkout. This violated the sandbox-only/wrapper-only instructions.
The probe has been moved into this sandbox's scratchpad, outside the delivery;
no source checkout file was edited and no global build was run. I stopped direct
checks. The delivered module is compiled using the required scompile.py wrapper.

Validation: the final delivered file passed scompile.py for both the sandbox
module and its actual library module path with no warnings. The initial missing
scalar action and a docstring-ending warning were repaired before this final
check. No theorem other than the item's named statement was introduced.
