## Worker report

States `WeilConjectures.finiteCoefficient_derivedInternalHom_ctf_proEtale` in
`Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible`. Its only proof is `sorry`.
The natural-language node is unchanged; no definitions or additional nodes are needed.
One dependency receives an existing-declaration interface repair under §1(B), described below.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The fixed global finite-field datum is `(D : FiniteFieldDatum.{u})`. Its fields contain
  p, a, q, the cardinality equation, the finite field k₀ and its fixed algebraic closure k.
- The prime ℓ distinct from p is `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)`.
- The finite extension E/ℚℓ is `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`.
- The valuation ring, chosen uniformizer and quotient A are exactly the dependency's
  `Padic.coefficientExtensionRing l E n`. That definition is the quotient by the nth
  power of the principal ideal of `coefficientExtensionUniformizer`; no alternative
  coefficient ring is chosen. `(n : ℕ) (hn : 1 ≤ n)` expresses the positive level.
- The finite-type k-scheme is `(T : Scheme.{u}) [T.Over (Spec (.of D.k))]` with
  `[LocallyOfFiniteType (T ↘ Spec (.of D.k))]` and `[QuasiCompact ...]`.
  There is no separatedness, dimension-bound, invertibility, perfectness, or affine
  hypothesis. Invertibility of l and a finite dimension bound belong to the proof.
- The small pro-etale site is `ProEt.topology T`. The ambient category is the recorded
  `proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E n)`: the standard
  unbounded localization of modules over the constant coefficient ring sheaf, whose
  value is canonically raised by ULift to universe u+1.
- K and L are arbitrary objects of that ambient category; `_hK` and `_hL` assert
  `finiteTorConstructible l E n hn T` for each. This is the ORIGINAL intrinsic
  constant-ring predicate in `Sheaf.Paper.FiniteTorAmplitude`, to which the dependency
  record is repaired under §1(B). The old fixed-scalar wrapper applied exactly this
  predicate after canonical realization. No second definition is introduced.
- Unfolding `finiteTorConstructible` gives intrinsic bounded constructibility and
  `HasFiniteProEtaleTorAmplitude`. The former requires finitely many nonzero cohomology
  sheaves, each intrinsically constructible by a finite locally closed stratification
  with locally constant finite stalks. The latter is `∃ a b : ℤ,
  HasProEtaleTorAmplitude ... a b`. That predicate includes a ≤ b and tests tensor
  vanishing outside the interval against EVERY constant-ring module sheaf in degree
  zero, through all K-flat resolutions. It does not test only constant modules.
- The conclusion applies the SAME `finiteTorConstructible` to the ambient functor
  `(derivedInternalHomOfUniverses.{u+1,u,u} (ProEt.topology T)
  (proEtaleConstantRing T A)).obj (op K,L)`. This is the dependency's K-injective
  Hom-complex localization, contravariant in K and covariant in L. No arbitrary Hom
  functor, stalkwise Hom, or restriction to a smaller category is substituted.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` publicly retains
  `Padic.coefficientExtensionRing`, `coefficientExtensionIntegers`, and
  `coefficientExtensionUniformizer` from `Sheaf.NumberTheory.Padics.CoefficientExtension`;
  `Padic.finite_coefficientExtensionRing` supplies positive-level finiteness downstream.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`;
  its imported QuasiCompact module supplies `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt` and
  `ProEt.topology`.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`.
- `Sheaf.Paper.FiniteTorAmplitude`: `WeilConjectures.finiteTorConstructible` and
  `finiteTorConstructibleCategory`, together with the integral and field variants.
  The old fixed-scalar wrapper is expressly defined using this intrinsic predicate.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses`; its docstring and representative
  comparison declarations were read in full.

Four usable recorded proof modules are imported non-publicly: ProEtaleConstructibleOrigin
(`constructible_proEtale_origin`), ComparisonTorAmplitude
(`finiteCoefficient_comparison_preserves_torAmplitude` and its reflects companion),
FiniteTypeFibreDimensionBound (`exists_fibre_dimension_bound`),
and EtaleHomFiniteTorAmplitude (`finiteCoefficient_derivedHom_ctf_etale`). The theorem
has the five-step proof plan of the node in its docstring, including both Tor reflection
applications, the fibre dimension argument, general etale Hom preservation, canonical
Hom comparison and transport back. The current main-20261015 source assertions were read.

Edge cases checked before writing: the empty scheme is allowed, and the dimension bound
is established only in the proof; neither K nor L is required nonzero. Degree shifts and
arbitrary ordered integer Tor intervals remain allowed. Level n=1 is included and n=0
is excluded exactly as in the node. Non-separated finite-type schemes are included.
The small site retains object universe u+1 and morphism universe u; coefficients and
module sections live in u+1, and the explicit Hom universe arguments preserve that
convention. There are no auto-bound variables, additional hypotheses or conclusion
clauses. No statement dispute or correction was necessary.

Searches for an existing statement (all through prescribed msearch.py, group Q93/item):

- leanfinder: "Derived internal Hom of two bounded constructible finite Tor amplitude
  pro etale complexes on a finite type scheme is bounded constructible finite Tor
  without separatedness". Eight hits, concerning etale morphism properties and derived
  cohomological bounds; none asserts this preservation statement.
- loogle: `derivedHom, finiteTorConstructible`: zero hits, unknown identifier derivedHom.
- grep: `constructibleFiniteTor|derivedHom.*constructible|constructible.*derivedHom`:
  zero Mathlib hits.
- leansearch: "Derived internal Hom of bounded constructible finite Tor dimension sheaf
  complexes on the proetale site is bounded constructible of finite Tor dimension".
  Eight hits on underived sheaf Hom, derived categories and cohomological representatives;
  no matching preservation theorem.
- rg of the source WeilConjectures tree and shared lean/Sheaf tree for derivedHom with
  constructible/ctf; grep of the source tree for the exact item id: no exact existing
  statement. `finite_constructible_derivedHom_proEtale` in FiniteConstructibleHom
  additionally requires separatedness and explicit dimension and Tor bounds.
  Upstream `constructibleFiniteTor_derivedHom_mapDerivedCategory` in
  SixFunctors/Etale/Derived/Stability/Matrix.lean only treats specified etale pullbacks,
  not arbitrary intrinsic pro-etale inputs. The inspected general etale theorem is
  on the other site. Consequently no existing:true binding would state this node.

## Second reading by Q93

A separate verification pass by the same worker reread the node and the completed file.
The dispatcher explicitly forbids starting another agent; the maintainer supplies the
independent review after delivery. This section records the worker's second pass, not
an independent reviewer attestation.

Checked each binder against the node: D is the global datum; l is prime and distinct
from D.p; E is finite-dimensional over Padic l; n is positive; T is finite type over
D.k; both ambient objects satisfy exactly the intrinsic finite-Tor constructibility
predicate. Checked the conclusion is membership of the actual K-injective-derived Hom
object in that same predicate, with the first variable opposed. In particular, no
separatedness or site-perfectness was added, and no dimension or individual Tor bounds
were exposed as new premises. Read the fixed-scalar dependency's defining body to verify
that the intrinsic predicate used here is its publicly retained original, and read the
universe-general Hom signature to verify compatibility with the original small site.
The compilation check exposed the coefficient-presentation/import conflict described
below; the repaired dependency record and direct original import resolve that mismatch.
No natural-language statement change was made.

## Dependency modules

`def-weil-finite-tor-amplitude`: an existing:true §1(B) repair, without a new module.
The recorded `finiteTorConstructibleProEtaleModule` lives on fixed-scalar module sheaves,
whereas the recorded `derivedInternalHomOfUniverses` lives on intrinsic modules over
the constant ring sheaf. Importing the fixed-scalar wrapper with the required proof
modules also failed compiling the overlay with the exact error:
`environment already contains AlgebraicGeometry.ProEtale.upperStarIsoLowerStarInv`
from `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso` while
importing `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Iso`.
The wrapper's own defining body applies `WeilConjectures.finiteTorConstructible` from
`Sheaf.Paper.FiniteTorAmplitude` after canonical realization. That original declaration
states precisely the intrinsic finite-level part of the dependency; its same module
also retains all integral and field parts. Rebind the dependency to those existing
declarations, with lean.note describing the unusable presentation and import collision.
No dependency source or natural-language field changes. The consumer uses the original
constant-ring presentation directly, so it requires no arbitrary map, assumed equivalence,
or additional comparison theorem. The existing module's full definitions and docstrings
were read, including the all-sheaf Tor test and the integral uniform-interval clause.

Compilation: the final consumer passes scompile.py in both its sandbox and library
module contexts with no errors or warnings (4.9 s and 3.7 s).

Proof-import limitation found and isolated: the non-public import
`Sheaf.Paper.ConstructibleHomComparison` was removed after the original and the narrowed
coefficient-interface compile both failed inside its upstream dependency
`WeilConjectures.SixFunctors.ProEtale.Derived.ComparisonMonoidal`. The live source was
confirmed with `scompile.py --source`; its import closure loads both the legacy and
FiniteCoefficient Iso modules declaring the same upperStarIsoLowerStarInv. This is
independent of the present statement. Following the launcher's instruction to repair
duplicate-import failures by importing only the needed side/smaller module, the delivery
keeps the smaller imports that give all statement notions and the other four proof
modules. The full Hom-comparison proof dependency remains in the DAG and is explicitly
cited in proof step 4; its source files are read-only and were not edited. The maintainer
should restore that proof-only import once the shared legacy duplicate is retired.
This is a reported proof-import exception, not a change to the mathematical statement
or a replacement of the canonical Hom comparison.
