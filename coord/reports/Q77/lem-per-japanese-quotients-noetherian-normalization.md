## Worker report

The module `Sheaf.RingTheory.JapaneseQuotientsNoetherianNormalization` states
`RingTheory.isNoetherianRing_integralClosure_of_isN2_nonzero_prime_quotients`.
Its only theorem has the whole proof `sorry`; no definitions or additional nodes are needed.
The item JSON changes only in `lean`.

Source read: Marot, *Sur les anneaux universellement japonais*, Bull. SMF 103 (1975),
Lemma 1.2 and its proof, printed pp.104–105, and Proposition 2.3, printed p.107.
The PDF at the node's Numdam URL was downloaded and read with pdftotext in the sandbox.
The web reader could not open the PDF, but the direct download succeeded. On p.104
Marot fixes a Noetherian domain, its fraction field, an arbitrary finite extension,
and its integral closure. Lemma 1.2 assumes Japanese associated-prime quotients;
Proposition 2.3 explicitly applies it under the stronger hypothesis that every
nonzero prime quotient is Japanese, exactly as this node states.

Hypothesis and clause correspondence:

- `R : Type u` with `[CommRing R] [IsDomain R] [IsNoetherianRing R]` renders a
  commutative Noetherian integral domain, including the nonzero condition in IsDomain.
- `K : Type v`, `[Field K] [Algebra R K] [IsFractionRing R K]` renders the given
  fraction field of R, without selecting a particular presentation of it.
- `hR : ∀ (q : Ideal R) [q.IsPrime], q ≠ ⊥ → IsN2 (R ⧸ q)
  (FractionRing (R ⧸ q))` says that every nonzero prime quotient is Japanese.
  The prime instance supplies its domain structure, and its canonical fraction field
  is used in the existing IsN2 definition. The zero prime is deliberately excluded.
- `L : Type w`, `[Field L] [Algebra K L] [FiniteDimensional K L]` renders every
  finite field extension L/K. The outer theorem binders make L arbitrary.
- `[Algebra R L] [IsScalarTower R K L]` requires exactly the composite R-algebra
  structure through K; it is compatible structure, not an extra mathematical restriction.
- `integralClosure R L` is the actual subalgebra of elements integral over R.
  `IsNoetherianRing (integralClosure R L)` is precisely that T is a Noetherian ring,
  rather than the stronger claim that T is module-finite over R.
- There is no separability, characteristic, or normality hypothesis. Universes
  `u v w` are independently bound; arbitrary sizes of the three given rings/fields
  are permitted. The IsN2 test extensions live in the universe of the quotient's
  own fraction field, as in the recorded dependency; this has all finite extensions
  up to isomorphism and does not create a vacuous test universe below its base.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, the abbrev for
  Noetherianity as a module over itself, and its ideal-finiteness characterization.
- `WeilConjectures.RingTheory.JapaneseDomain`: `IsN2`, with the full definition
  quantifying over finite extensions and the composite algebra structure. This is
  the recorded upstream declaration of def-weil-pbc-japanese-domain, not a copy.
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure`, whose
  carrier is `{x | IsIntegral R x}`. Its full construction and the monic-polynomial
  definition of IsIntegral in IntegralClosure.IsIntegral.Defs were read.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, the recorded declaration for
  def-pc-field-extension; fields with an Algebra structure are field extensions.
  These Algebra and integralClosure modules, and FiniteDimensional.Defs, are public
  imports of the existing JapaneseDomain module.

The proof docstring follows all five DAG steps: the scaled integral finite model,
its Krull normalization by transitivity and Mori–Nagata, nonzero contraction of a
height-one prime, finite residue extension followed by the Japanese quotient and
Noetherian submodule argument, and the height-one quotient criterion. Stated proof
dependencies are imported without `public`: IntegralClosure.IsIntegral.Basic
(finite_adjoin_of_finite_of_isIntegral), IntegralClosure.IsIntegralClosure.Basic
(RingHom.IsIntegral.trans), Noetherian.Basic (finite algebras, quotient permanence,
and submodule finiteness), Sheaf.RingTheory.NormalizationIntegralClosureKrull
(RingTheory.normalization_integralClosure_isKrull), and
Sheaf.TraceFormula.AlmostFiniteResidueFieldDegree
(RingTheory.almostFinite_residueField_fractionDegree). The full signatures and
docstrings of the last two project declarations were read. The proof dependency
lem-per-krull-height-one-quotients-noetherian has no Lean record or Mathlib match
and is not imported; this proof-only prerequisite is not needed to state the item.

Edge cases checked: if R is a field there are no nonzero prime ideals, the
hypothesis is vacuous and the integral closure in the finite algebraic extension
is the whole field L, so the conclusion holds. The identity extension L=K is
included, as are purely inseparable extensions in positive characteristic and
nonnormal R. The zero ring is excluded exactly by the integral-domain assumption.
No assumption that the normalization is module-finite was smuggled into the result.
The nonzero condition refers to q unequal to the bottom ideal, not q unequal to top;
top is already excluded by primality.

Searches actually run:

- msearch.py leanfinder, query: "A Noetherian integral domain whose nonzero prime
  quotients are Japanese has Noetherian integral closure in every finite fraction
  field extension". Eight hits, including IsIntegralClosure.isNoetherian,
  IsIntegralClosure.isNoetherianRing, and integralClosure.isNoetherianRing. None
  states this result: the nearby general results assume a normal base and a
  separable extension. Their full surrounding binders in
  Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean were read, including
  lines 53–60 and 147–177.
- msearch.py loogle, query: `"integralClosure", "IsNoetherianRing"`. Two hits:
  integralClosure.isNoetherianRing and IsIntegralClosure.isNoetherianRing,
  with the same unwanted normality and separability assumptions; no exact match.
- msearch.py grep, query:
  `integralClosure.*[Nn]oetherian|[Nn]oetherian.*integralClosure`.
  Nine hits, comprising the above results and applications to number/function
  fields; no exact match.
- rg on WeilConjectures and Sheaf for Japanese/japanese, IsN2 with isNoetherian,
  and the item's id: existing Japanese/Nagata definitions and other normalization
  results, but no occurrence of this item or its exact statement. A further search
  for japanese-quotient phrases likewise found no duplicate. The upstream names
  index was searched for IsN2/Japanese and the proposed theorem name, with no match.
- rg on Mathlib, WeilConjectures, Sheaf and the upstream names index for the proposed
  declaration name found no collision.

No statement correction, dependency-interface repair, new node, or disputed statement.

## Second reading by Q77

No second reading by another worker: the current dispatcher brief requires direct
worker delivery without spawning agents. The maintainer supplies the independent
review. I reread the signature against the node: every hypothesis and the single
conclusion match as detailed above; no mismatch requiring a change was found.
