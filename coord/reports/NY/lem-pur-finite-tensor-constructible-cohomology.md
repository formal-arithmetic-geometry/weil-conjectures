## Worker report

The theorem `AlgebraicGeometry.Scheme.finiteTensor_constructible_cohomology` states
constructibility in every integer degree of the recorded finite-coefficient derived tensor.
Its sole proof is `sorry`, with the complete five-step DAG proof in its docstring.

Hypotheses and clauses:
- Prime ell is `(l : ℕ) [Fact l.Prime]`.
- A finite extension E/Q_l is `E : Type u`, `Field E`, `Algebra (Padic l) E`, and
  `FiniteDimensional (Padic l) E`.
- The valuation ring, chosen uniformizer and A = O_E/(uniformizer^n) are precisely
  `Padic.coefficientExtensionRing l E n`, imported from the coefficient dependency.
- A positive level is `(n : ℕ) (hn : 1 ≤ n)`.
- The scheme T and invertibility of ell are `(T : Scheme.{u})` and
  `[∀ x : T, Invertible (l : T.residueField x)]`.
- The site and constant coefficient sheaf are `proEtaleRingModules T
  (proEtaleConstantRing T (Padic.coefficientExtensionRing l E n))`.
- Membership of K,L in intrinsic D^b_c is `hK`, `hL`, applying the repaired
  `intrinsicFiniteTorsionConstructible` predicate to `DerivedCategory.Q.obj K/L`.
- K,L are arbitrary representative complexes; P, f, hf, hP are the arbitrary
  chosen K-flat resolution used by the recorded `derivedTensor`. These computing
  data do not impose a Tor bound on K or L. Every derived object has representatives
  and a K-flat resolution, so this presentation covers the stated derived inputs.
- Every integer i is `(i : ℤ)`; the output is
  `IsConstructibleProEtaleModuleSheaf` of `DerivedCategory.homologyFunctor ... i`
  applied to `derivedTensor T ... K L P f hf hP`.
- No lower bound, output boundedness or finite Tor dimension is asserted.
  The finite coefficient instance is supplied by the existing finiteness theorem,
  rather than imposed as an additional assumption.

Dependency declarations read and used:
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, and its imported
  `Padic.coefficientExtensionRing` / `coefficientExtensionUniformizer` constructions.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`.
- `Sheaf.Paper.FiniteTorsionConstructibility`:
  `AlgebraicGeometry.Scheme.finiteTorsionConstructible`; the dependency repair
  exposes its intrinsic predicate without the unused global base parameters.
- Mathlib `Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`.
- `Sheaf.Algebra.Homology.DerivedTensor`:
  `AlgebraicGeometry.Scheme.derivedTensor`, with its K-flat convention.
- `Sheaf.Paper.ProEtaleConstructibleSheaf`:
  `AlgebraicGeometry.Scheme.IsConstructibleProEtaleModuleSheaf`.
All recorded proof-dependency modules are imported for the stage-3 proof plan;
Mathlib-only dependencies use their recorded source modules.

Edge cases: n=1 is included, n=0 excluded exactly as stated. The empty scheme and
zero complexes are included; the definition permits the single empty stratum.
Unbounded negative Tor cohomology is allowed: the conclusion quantifies over each
degree and never requests finite support. No separatedness, Noetherianity of T,
finite Tor dimension or global finite-field base datum is assumed. The modules
use the existing site with object universe u+1, morphism universe u, and module
universe u+1. Universes and binders are explicit.

Searches (2026-10-15):
- msearch.py leanfinder: “Derived tensor products of bounded constructible proetale
  sheaf complexes have constructible cohomology”: eight condensed category and
  monoidal infrastructure hits, no matching theorem.
- msearch.py loogle: `IsConstructibleProEtaleModuleSheaf, derivedTensor`: zero hits,
  unknown identifier for the project predicate.
- msearch.py grep: `constructible.*homology|homology.*constructible|constructible.*derivedTensor`:
  zero Mathlib hits.
- rg in upstream WeilConjectures and project lean/Sheaf found upstream
  `Etale.constructibleHomology_derivedTensor`, a devissage statement on etale
  sheaves with extra Serre and hTor hypotheses, not the intrinsic pro-etale theorem.
  Its full signature was read. No occurrence of this item's blueprint id existed.
- Read the source Stacks proetale.tex lemma-tensor-c (09BQ). The proof here follows
  the DAG common-stratification argument, without the source's incorrect fixed
  truncation shortcut. No statement correction or dispute is needed.

## Dependency modules

`def-weil-finite-torsion-constructibility`: the recorded predicate's global
`FiniteFieldDatum` and `l ≠ D.p` arguments are unused in its body and absent from
this consumer's intrinsic statement. Under §1(B),
`Sheaf.Paper.IntrinsicFiniteTorsionConstructibility` imports the original module
and exposes the identical cohomological predicate as
`AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`, with those unused
parameters removed. It keeps the exact coefficient construction, standard
localization, finite-support clause and every-degree constructibility clause.
No new DAG notion, coefficient choice, or hypothesis is introduced.

Validation: `scompile.py NY lem-pur-finite-tensor-constructible-cohomology`
compiled both delivered files separately in dependency order against the server
library, with no errors or warnings. The intrinsic definition took 1.6 seconds;
the main theorem file took 2.0 seconds. Only the main theorem is postponed.

## Second reading by NY

Independently read the item JSON and both delivered modules, all six statement
 dependency nodes and their actual declarations, the original finite-torsion
module, the coefficient constructions, and Stacks proetale.tex section
`section-constructible`, especially `definition-constructible` and
`lemma-tensor-c` (09BQ). No mathematical or Lean mismatch was found; no Lean or
node changes were needed. This section supplies the independent reading.

Object/hypothesis/conclusion checklist, in the order of the node:

1. Prime ell: `(l : ℕ) [Fact l.Prime]`. Exact; no characteristic excluded beyond
   primality and the explicit invertibility hypothesis below.
2. Finite extension E/Q_ell: `(E : Type u) [Field E] [Algebra (Padic l) E]
   [FiniteDimensional (Padic l) E]`. Exact, not an arbitrary coefficient field.
   `Padic.coefficientExtensionAbsoluteValue`, `coefficientExtensionIntegers`,
   `coefficientExtensionUniformizer`, `coefficientExtensionIdeal` and
   `coefficientExtensionRing` were opened: the final ring is exactly the quotient
   by the nth power of the ideal generated by the recorded chosen uniformizer.
   There is no independently chosen coefficient ring in the theorem.
3. Positive integer n: `(n : ℕ) (hn : 1 ≤ n)`. Exact.
   `Padic.finite_coefficientExtensionRing l E n hn` supplies finiteness from the
   recorded dependency; the theorem does not add a finiteness hypothesis.
4. Scheme T with ell invertible: `(T : Scheme.{u})` and
   `[∀ x : T, Invertible (l : T.residueField x)]`. Exact: invertibility of the
   integer in every residue field is equivalent to invertibility on the scheme.
   No finite-field base, Noetherianity, quasi-compactness or separatedness is added.
5. Small pro-etale site and constant ring A_T: every complex is over
   `proEtaleRingModules T (proEtaleConstantRing T
   (Padic.coefficientExtensionRing l E n))`. Read `proEtaleRingModules` and
   `proEtaleDerivedCategory`: both use precisely the same constant commutative
   ring sheaf, forgotten to rings, and `SheafOfModules` with the standard derived
   localization. This is neither the etale category nor condensed module objects.
6. K,L in intrinsic D^b_c(T,A): `hK` and `hL` use
   `intrinsicFiniteTorsionConstructible` on `DerivedCategory.Q.obj K` and `.obj L`.
   Its two clauses are finite support of nonzero integer cohomology and
   `IsConstructibleProEtaleModuleSheaf` in every degree. Exact.
7. Derived tensor: the extra presentation data `(P : CochainComplex ... ℤ)`,
   `(f : P ⟶ K)`, `(hf : QuasiIso f)` and `(hP : CochainComplex.IsKFlat ... P)`
   are exactly the recorded `derivedTensor` interface, not finite Tor amplitude
   or a bounded K-flat resolution. Its body is the total tensor of P and L,
   sent to the same derived category. Arbitrary representatives and arbitrary
   computing resolutions are quantified; the construction imposes no restriction
   on the derived inputs beyond the stated D^b_c membership.
8. Every integer i: `(i : ℤ)` comes after the inputs. Its cohomology is
   `(DerivedCategory.homologyFunctor ... i).obj (derivedTensor ... K L P f hf hP)`.
   Opened Mathlib's `homologyFunctor` and `homologyFunctorFactors`: this is the
   actual cochain cohomology, not chain homology with reversed degree.
9. Constructible output: `@IsConstructibleProEtaleModuleSheaf T ... _
   (Padic.finite_coefficientExtensionRing ...)` applied to that cohomology.
   Opened this dependency: it requires a positive finite partition into locally
   closed constructible immersed subschemes, canonical constant-coefficient
   pullback, local constancy, and finite geometric stalks. All node clauses are
   retained. No output boundedness or lower bound appears.

Dependency-module review (H13): the source blueprint definition at order 1454
introduces a global finite-field datum and ell different from its characteristic,
but neither occurs in the body of `finiteTorsionConstructible`. Comparing both
bodies shows that `intrinsicFiniteTorsionConstructible` is exactly the same
cohomological predicate on the same coefficient ring, with those unused arguments
removed as required by this consumer's explicit intrinsic formulation. The repair
imports the original definition and preserves its actual notions. It introduces
no new DAG definition, arbitrary object, missing proof, or changed dependency
statement. The source blueprint also explicitly uses a global finite partition;
Stacks 09AJ uses an affine-local convention instead. The delivered statement
correctly retains the node/blueprint convention. Stacks 09BQ assumes a Noetherian
ring and bounded-above constructible inputs: a finite ring is Noetherian, and
bounded inputs qualify. The common finite-stratification proof in this node gives
its global conclusion without adding a scheme hypothesis or making a claim of
lower boundedness. No statement correction or citer audit is required.

Edge cases: n=1 is allowed; n=0 is excluded exactly by the node. Zero inputs and
the empty scheme are allowed, with the single empty stratum permitted by the
constructibility definition. There is no quantified family whose nonemptiness
has been assumed. The resolution may be unbounded, and all negative degrees of
Tor are covered. Schemes of arbitrary characteristic are allowed precisely when
ell is invertible; for the empty scheme this condition is vacuous. The universe
u is arbitrary and is the same small universe as the dependency's scheme and
coefficient types; the site has object universe u+1, morphism universe u, and
modules are in u+1. No equality between object and morphism universes is imposed.
All names and universe variables are explicitly bound.

Independent searches (2026-10-15), using different phrases from the first worker:
- `msearch.py ... leanfinder`: "Constructibility of all Tor sheaves for bounded
  constructible complexes over a finite coefficient ring": eight hits concerning
  derived t-structure bounds and condensed infrastructure; no matching statement.
- `msearch.py ... loogle`: `"constructible", "tensor"`: zero hits.
- `msearch.py ... grep`: `constructible.*[Tt]ensor|[Tt]ensor.*constructible`:
  zero Mathlib hits.
- Direct rg on Mathlib, upstream WeilConjectures, project lean/Sheaf, and the
  upstream declaration index, by constructibility/tensor words and proposed full
  names: no duplicate of either delivered declaration. Opened upstream
  `Etale.constructibleHomology_derivedTensor` and `Etale.boundedConstructible_tensor`:
  the first is for etale sheaves with explicit Serre and hTor hypotheses; the
  second requires finite Tor amplitude. Neither is this pro-etale theorem.
  Also read the new pro-etale framework documentation and its module-object
  `derivedTensor` and `boundedConstructible`: these are internal module-object
  categories, not this recorded SheafOfModules constant-ring interface, and do
  not provide the theorem under review.

H5/H6/H8/H9: the new definition has real predicate data and uses the existing
named finiteness theorem; the only new theorem has exactly `by sorry`. Both
modules and declarations carry their correct source/blueprint docstrings. The
main docstring reproduces all five proof steps, including finite coefficients,
common stratification, exact restriction/tensor compatibility, locally constant
finite-type tensor cohomology, and the constructibility conclusion. No local
notation, local instance, private definition, or hidden let-binder occurs in the
statement. The signature reader prints exactly both nodes' `lean.statement`.

Validation: independently reran `scompile.py NY
lem-pur-finite-tensor-constructible-cohomology` with both sibling modules in
 dependency order. Both compiled separately, with no errors or warnings, using
 the authorized local side overlay; final library checks took 2.0 s and 2.6 s.
