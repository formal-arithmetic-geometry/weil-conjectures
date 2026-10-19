## Worker report

The module `Sheaf.Paper.ComparisonTorAmplitude` states the two clauses of
`lem-sf-comparison-tor-amplitude`, separately, with `sorry` proofs:
`AlgebraicGeometry.finiteCoefficient_comparison_preserves_torAmplitude` and
`AlgebraicGeometry.finiteCoefficient_comparison_reflects_torAmplitude`.
There are no new definitions, new nodes, or statement corrections. One existing
dependency record is repaired under §1(B), as detailed below.
The item's JSON and the dependency JSON are each changed only in `lean`. No proofs were attempted.

Source read: blueprint `sec-six-functors/sk-prop-sf-rf-shriek-preservation/`
`lem-sf-comparison-tor-amplitude.md`, statement and Proof (i), (ii), in the
launcher's literature checkout (the shared checkout does not retain the paper files).
I also read the node's full six-step proof. Both theorem docstrings carry the
corresponding proof, including the coefficient identification, exact termwise
pullback, and, in the converse, the unbounded tensor comparison followed by the
sheaf-level unit. In particular, the converse never applies a bounded-below
comparison unit to a tensor whose boundedness has not been established.

Hypothesis and clause correspondence:

- The global finite-field datum is `(D : WeilConjectures.FiniteFieldDatum.{u})`.
- The coefficient prime is `(l : ℕ) [Fact l.Prime] (_hlp : l ≠ D.p)`.
- The finite extension is `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`. Its integer ring and fixed uniformizer are
  those already used by `Padic.coefficientExtensionRing l E n`; no new choice
  is made. The positive level is `(n : ℕ) (hn : 1 ≤ n)`.
- `A = A_{E,n}` is written out as `Padic.coefficientExtensionRing l E n`.
  Étale modules use `ULift.{u + 1, u}` of exactly this ring, with its canonical
  ring structure and scalar equivalence. The recorded flat-model dependency
  uses this identical lift. This is a size convention, not a different ring.
- The scheme is `(T : Scheme.{u})`. Invertibility of l on T is
  `[∀ x : T, Invertible (l : T.residueField x)]`, precisely the convention
  of `lem-sf-flat-model`; this does not require T to be over the global field,
  Noetherian, or of finite type.
- The interval endpoints are `(a b : ℤ)`. Clause (i) also names `_hab : a ≤ b`,
  the ordered-interval convention expressly required by its cited étale
  flat-model clause and the pro-étale Tor predicate. Clause (ii) does not
  add this binder: its `HasProEtaleTorAmplitude` hypothesis already includes it.
- The comparison inverse image is the published
  `ProEtale.finiteCoefficientIntrinsicDerivedComparison T A`. This is
  `comparisonUpperStar` followed by canonical constant-scalar module
  sheafification, applied termwise and localized; its source and target are
  exactly the recorded étale fixed-scalar and intrinsic pro-étale categories.
  It is not an arbitrary functor, inverse image, or chosen isomorphism.
  Finiteness is passed explicitly using `Padic.finite_coefficientExtensionRing`
  at `hn`, including the transported Finite witness for lifted coefficients;
  there is no extra finite-ring hypothesis and no local instance.
- Clause (i)'s `K' ∈ D^b_c(T_et,A)` is `_hK'` using the recorded
  `Etale.DerivedCategory.isBoundedConstructible`. It quantifies over the
  unbounded derived category and requires exactly constructible cohomology
  with a bounded support interval.
- Clause (i)'s étale Tor bound is `_hTor'` using
  `Etale.DerivedCategory.hasTorAmplitudeIn ... T a b K'`, which tests every
  étale module sheaf placed in degree zero and every degree outside [a,b].
- The two conclusions of (i) are a conjunction on that same pullback of K':
  `Scheme.intrinsicFiniteTorsionConstructible l E n hn T` and
  `Scheme.HasProEtaleTorAmplitude T A ... a b`. The first is the intrinsic
  bounded constructibility of the node, not an étale-origin substitute;
  the second is the recorded resolution-independent tensor-vanishing predicate.
- Clause (ii)'s bounded-below étale K' is `_hPlus :
  _root_.DerivedCategory.TStructure.t.plus K'`. By the Mathlib definitions
  underlying `DerivedCategory.Plus`, this means the existence of a lower
  cohomology bound, not a bounded or constructible étale K'.
- Clause (ii)'s pro-étale object is `(K : Scheme.proEtaleDerivedCategory T A)`,
  with `_hK : Scheme.intrinsicFiniteTorsionConstructible ... K` and
  `_hTor : Scheme.HasProEtaleTorAmplitude T A K a b`.
- Its given isomorphism is `_e : K ≅ (...IntrinsicDerivedComparison...).obj K'`,
  in exactly the orientation of the node; it is supplied data, not used to
  define the canonical comparison.
- Its conclusion is the étale `hasTorAmplitudeIn ... T a b K'`, with the same
  endpoints. It assumes neither boundedness nor constructibility of K' beyond
  the specified bounded-below condition.

Dependency declarations read and reused:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` (and its public
  `CoefficientExtension` import): `Padic.coefficientExtensionRing` and
  `Padic.finite_coefficientExtensionRing`.
- `Sheaf.Paper.FiniteCoefficientFlatModel`:
  `AlgebraicGeometry.Etale.finiteCoefficient_hasTorAmplitude_iff_flatModel`
  and its pro-étale companion. The input encodings and interval convention
  are retained exactly.
- `Sheaf.Paper.FiniteTorAmplitude`: `WeilConjectures.finiteTorConstructible`,
  which uses precisely the intrinsic constructibility and finite-interval
  predicates used here. We state the specified interval, rather than merely
  membership in this existential finite-Tor subcategory.
- `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`, publicly importing the existing
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `Etale.DerivedCategory.hasTorAmplitudeIn`. The new lower-bound-only predicate
  in that dependency is not substituted for the bounded interval.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`:
  `AlgebraicGeometry.Etale.derivedTensor`, used by that étale Tor predicate.
- `Sheaf.Algebra.Homology.DerivedTensor`:
  `AlgebraicGeometry.Scheme.derivedTensor` and `derivedTensorRing`, the published
  intrinsic constant-ring K-flat representative construction. These are exactly
  the operations used by the recorded `HasProEtaleTorAmplitude` predicate.
  The dependency's record-only repair makes this existing interface explicit.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `Scheme.intrinsicFiniteTorsionConstructible`.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `Etale.DerivedCategory.isBoundedConstructible`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparison`, `Scheme.proEtaleSiteComparisonModules`;
  the inclusion and fixed-scalar adjunction are exactly those used by the
  intrinsic comparison's `comparisonUpperStar`.
- Mathlib `Algebra.Homology.DerivedCategory.TStructure`:
  `DerivedCategory.Plus`, `DerivedCategory.TStructure.t.plus`, and
  `DerivedCategory.isGE_iff` for the lower-bounded membership meaning.
- The existing `Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison`:
  `ProEtale.finiteCoefficientIntrinsicDerivedComparison`, with its canonical
  realization construction and exactness instances. I read the full module
  locally and confirmed its current published source using `scompile.py --source`.
  This is existing data associated with `def-weil-pbc-proetale-modules`, already
  transitively reached by the flat-model/constructibility definitions.

Every stated proof dependency is imported, including the constant sheaf and
sheafification constructions, comparison flatness, bounded-above flat K-flatness,
constructible-origin comparison, lifted algebraic structures and adjunction,
exact-functor cohomology and derived factorization/derivation, canonical ringed-topos
tensor pullback, and the finite-level sheaf unit. Proof-only imports are non-public.
The original generic tensor-pullback interface is publicly reexported by the recorded
`ProEtaleCanonicalTensorPullback` repair module.

Edge cases checked before the final statements:

- T can be empty. Invertibility on residue fields is then vacuous, as required,
  and neither theorem adds nonemptiness or a finite-type condition.
- The zero complex is allowed on both sites; all Tor tests and cohomological
  support conditions specialize correctly. The isomorphism in (ii) remains
  the node's actual given origin, not a universal arbitrary-map hypothesis.
- Degenerate ordered intervals a = b are allowed; negative endpoints and n = 1
  are allowed. Reversed endpoints are not a finite ordered Tor interval in the
  cited flat-model/pro-étale conventions, hence the explicit order premise in (i).
- Clause (ii) allows unbounded-above K' and arbitrary test sheaves. It never
  imposes boundedness on their derived tensor product.
- Coefficients and the scheme have the same arbitrary universe u, as in the
  recorded dependencies; the étale module universe is u+1. The small pro-étale
  site retains objects in u+1 and morphisms in u. No equality of these universes,
  small-site replacement, or additional size assumption is imposed.

Searches executed:

- `msearch.py ... leanfinder` with “Tor amplitude is preserved and reflected by
  pullback from the etale site to the proetale site”: 8 results, all generic
  étale morphisms/sites or formally étale algebra facts; no comparison theorem.
- `msearch.py ... loogle '"torAmplitudeIn", "mapDerivedCategory"'`: 0 hits.
- `msearch.py ... grep 'torAmplitude|TorAmplitude|comparisonUpperStar'
  AlgebraicGeometry`: 0 Mathlib hits.
- `rg` over upstream WeilConjectures and the project `lean/Sheaf` for
  `comparison.*Tor|tor amplitude|TorAmplitude|HasProEtaleTorAmplitude|
  proEtaleSiteComparison|finiteCoefficient_torAmplitude` found the recorded
  predicates, flat-model theorem, and upstream
  `SixFunctors/ProEtale/Derived/HomComparison.lean`. Its full docstrings and
  signatures were read: `torAmplitudeIn_mapDerivedCategory` omits the intrinsic
  constructibility conclusion; `constructibleFiniteTor_mapDerivedCategory`
  existentially forgets the fixed interval and uses a different constructibility
  predicate; `torAmplitudeIn_of_mapDerivedCategory` uses fixed-scalar pro-étale
  objects and `HasInvertibleExponent`. None is literally this node's two-clause
  statement on its recorded intrinsic objects/predicates. They can be used as
  ingredients after the known coefficient and constructibility transports;
  attaching one as the whole node would drop clauses or change its objects.
- Searching for the item id in upstream found these same three declarations,
  not a complete statement using the intrinsic project definitions.
- `rg` for both new full declaration suffixes in Mathlib, upstream,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: no collisions.

No `STATEMENT-DISPUTED` issue was found. No source statement was corrected.
The dry run is performed with `deliver2.py ... --no-push`; the second reader
will supply the independent reading and make the delivery.

## Dependency modules

`def-weil-derived-tensor`: record-only §1(B) repair, using existing
`Sheaf.Algebra.Homology.DerivedTensor` declarations
`AlgebraicGeometry.Scheme.derivedTensor` and `derivedTensorRing`. The node's statement
explicitly defines the tensor of K-flat representatives on the constant commutative
ring sheaf and its coefficient-ring specialization; both are already constructed in
this module, with no postponed data. The previous fixed-scalar bifunctor record cannot
be imported with the recorded intrinsic flat-model, constructibility, and comparison
modules: the compiler reports that generic
`WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs` and
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs` both declare
`AlgebraicGeometry.ProEtale.«term(_)_*[_]»`. Both local compilation and server
confirmation reproduced that conflict. Reusing the existing intrinsic representative
operation resolves it and states precisely this dependency node's construction;
`HasProEtaleTorAmplitude` already unfolds to the very same operation. Only `lean` is
changed in this dependency; its definition, statement, proof plan, and other fields
are preserved. There is no new dependency module to compile. The record's signature
is verbatim from the existing source; the source's legacy local notation denotes the
explicit constant coefficient sheaves explained in its module docstring.

Validation: the final module passed `scompile.py` with all required proof imports,
no errors and no warnings (sandbox pass 35.9 s; module pass 10.8 s, each under the
unchanged 60-second limit). The two node copies differ from the shared base only in
`lean`. The file has two theorem-only `sorry` terms, no auto-implicit binders, and no
line longer than 100 characters. The delivery dry run also checks both existing
intrinsic tensor declarations by importing their existing module and `#check`ing them.


## Second reading by Q09

Independent reader, 2026-10-16. I opened the complete item JSON, its sandbox module,
the complete master blueprint source (order 2067) in the launcher's literature mirror,
and the statement and recorded interface of every statement dependency. The source
is a blueprint Markdown lemma, not itself a Stacks lemma. I also read the actual
Stacks TeX passages sites.tex 0H7J and 00YV and sites-cohomology.tex 06YQ and 07A4.
The latter permits arbitrary unbounded derived objects; the former flatness lemma
requires only a ringed site and a bounded-above flat complex. No extra Noetherian,
finite-type, or base-field condition is inherited by this lemma: it explicitly
introduces an arbitrary scheme T on which ell is invertible.

Object/hypothesis/conclusion inventory and Lean correspondence:

1. Global finite-field datum: `D : WeilConjectures.FiniteFieldDatum.{u}` in both
   declarations. I opened `FiniteFieldFiber.lean`: this contains the prime p,
   positive exponent, finite field of the required cardinality, and its chosen
   algebraic closure. PASS; T is not required to be over that closure.
2. Coefficient prime ell different from p: `(l : ℕ) [Fact l.Prime]
   (_hlp : l ≠ D.p)` in both declarations. PASS; no characteristic is lost.
3. Finite extension E/Q_ell, fixed valuation ring/uniformizer, and positive level:
   `(E : Type u) [Field E] [Algebra (Padic l) E]
   [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)`.
   I opened `CoefficientExtension.lean` and the finiteness dependency: the ring
   is `Padic.coefficientExtensionRing l E n`, the quotient by the recorded chosen
   uniformizer ideal power, not a field or a new coefficient choice. PASS.
4. Scheme T with ell invertible: `(T : Scheme.{u})
   [∀ x : T, Invertible (l : T.residueField x)]`. This is precisely invertibility
   at every point, the existing flat-model interface. PASS; no Noetherianity,
   quasi-compactness, nonemptiness, or structural morphism is added.
5. Comparison nu_T^*: `ProEtale.finiteCoefficientIntrinsicDerivedComparison T A`.
   I read the entire owning module, `ProEtaleSiteComparison.lean`, and the
   intrinsic derived-category definition. The functor is the specified
   `comparisonUpperStar` composed with canonical constant-scalar module
   sheafification, then `mapDerivedCategory`. It is exact termwise comparison
   into modules over the actual constant commutative ring sheaf. PASS; there
   is no arbitrary functor, independently chosen equivalence, or abstract map.
   Its Finite premise is supplied by `Padic.finite_coefficientExtensionRing`
   at hn, rather than assumed as another hypothesis.
6. Interval [a,b]: `(a b : ℤ)` in both clauses. Clause (i)'s `_hab : a ≤ b`
   is the explicit ordered-interval convention in its cited `lem-sf-flat-model`
   (I read that node and all four Lean signatures). Clause (ii) gets exactly
   the same order from `_hTor`, since `HasProEtaleTorAmplitude` begins with
   `a ≤ b ∧ ...`. PASS; this does not discard an interval the cited convention
   admits, or merely impose a technical premise to use an API.
7. Clause (i), bounded constructible etale K': `K' : Etale.DerivedCategoryModule
   (ULift.{u + 1, u} A) T` and `_hK' : isBoundedConstructible ... T K'`.
   I read `BoundedConstructibleComplexes.lean`: all cohomology sheaves satisfy
   the recorded finite-value constructibility condition, and one bounded
   support interval exists. PASS; the ambient derived category is unbounded,
   with bounded constructibility asserted as the node requires.
8. Clause (i), etale Tor amplitude in the particular interval: `_hTor' :
   Etale.DerivedCategory.hasTorAmplitudeIn ... T a b K'`. I opened its actual
   upstream definition in `Etale/Derived/Coefficients.lean` and the recorded
   etale tensor module. It tests every module sheaf F in degree zero and
   every q outside [a,b], using derived tensor and homology. PASS; it does
   not replace the fixed interval by an existential finite-Tor bound.
9. Clause (i), BOTH conclusions on that very comparison object:
   `Scheme.intrinsicFiniteTorsionConstructible ... (comparison.obj K') ∧
   Scheme.HasProEtaleTorAmplitude T A (comparison.obj K') a b`.
   I opened both predicate definitions. The first requires finitely many
   nonzero cohomology sheaves, all intrinsically constructible; the second
   requires the same ordered interval and tests all degree-zero sheaves on
   every K-flat resolution of every representative. PASS; neither conclusion
   is replaced by a weaker etale-origin or finite-Tor-existence predicate.
10. Clause (ii), bounded-below etale origin only: `K'` is in the same etale
    category, with `_hPlus : DerivedCategory.TStructure.t.plus K'`.
    I read Mathlib's standard t-structure and `DerivedCategory.Plus` interface:
    plus is existence of a lower cohomological bound. PASS; K' is allowed to
    be unbounded above and is not assumed constructible.
11. Clause (ii), bounded constructible pro-etale K with the stated Tor bound:
    `(K : Scheme.proEtaleDerivedCategory T A)`, `_hK :
    intrinsicFiniteTorsionConstructible ... K`, and `_hTor :
    HasProEtaleTorAmplitude T A K a b`. PASS, by the same opened definitions.
12. Clause (ii), given origin isomorphism: `_e : K ≅ comparison.obj K'`.
    PASS; same objects and orientation as the source, supplied after K and K'.
13. Clause (ii), conclusion: `Etale.DerivedCategory.hasTorAmplitudeIn
    (ULift.{u + 1, u} A) T a b K'`. PASS; all test modules and outside degrees
    are quantified inside the recorded predicate, with precisely the original
    endpoints. No boundedness of `K' tensor^L N` is assumed.

Size and edge checks: the zero complex and empty T remain allowed on both sites.
All finite partitions, zero cohomology sheaves, and degree-zero test sheaves are
those of the existing definitions; there is no nonempty index premise. Arbitrary
negative endpoints and a=b are admitted. Reversed endpoints are outside the
explicit ordered Tor-interval convention cited by this node, including for the
zero object. n=1 is included and n=0 is excluded by the source's n>=1, not by a
compiler workaround. l=2 and all primes distinct from D.p are included. A remains
a finite local quotient, not a field when n>1. The common arbitrary universe u
is the existing scheme/coefficient convention, and ULift is the canonical ring
lift with Finite transported by Equiv.ulift. The pro-etale site still has objects
in u+1 and arrows in u, with module values in u+1. No site-universe equality or
additional smallness instance is assumed.

Independent one-definition searches actually executed:

- LeanFinder: “An exact conservative comparison of etale and proetale sheaves
  preserves and detects a prescribed interval of derived tensor cohomology”.
  Eight results: formally etale/Kahler differential facts, light condensed
  monoidal/internal-projectivity facts, and a Mayer-Vietoris exactness result;
  no statement of these two clauses.
- Loogle: `"hasTorAmplitudeIn"` returned zero results.
- Mathlib grep via msearch: `tor.?amplitude|tensor.*comparison|comparison.*tensor`
  in AlgebraicGeometry returned zero results.
- Independent rg over all Mathlib, upstream WeilConjectures, and project
  lean/Sheaf used `amplitude.*(comparison|inverse.image)|comparison.*amplitude|
  tor.*reflect|torAmplitudeIn_of_mapDerivedCategory|torAmplitudeIn_mapDerivedCategory`.
  I opened upstream `ProEtale/Derived/HomComparison.lean`, including all three
  relevant signatures. The preservation theorem lacks the intrinsic bounded
  constructibility conclusion; its constructibleFiniteTor companion forgets
  the prescribed interval. The reflection theorem uses the fixed-scalar
  pro-etale category and its different constructibility predicate. They are
  useful ingredients after transport but are not the exact statement on the
  recorded intrinsic categories. No exact project or Mathlib duplicate was
  found, and no private notion is introduced here.

Dependency repair: I independently read the entire existing
`Sheaf.Algebra.Homology.DerivedTensor` module against the full
`def-weil-derived-tensor` node. The data are explicitly `Q(P tensor K2)` for
one supplied K-flat quasi-isomorphism P -> K1. `derivedTensorRing` restricts
scalars on the actual constant B-ring unit and places that module in degree
zero. This is precisely the node's two constructions, with no extra theorem
or hollow data. I also read the competing upstream fixed-scalar bifunctor and
its imports. The retained §1(B) record repairs the coefficient presentation
needed by the intrinsic predicates; its note explicitly explains the duplicate
UpperLowerStar notation collision. The repair does not change the mathematical
statement or add a second definition. Both recorded declarations are existing;
there is no dependency module or new node to add or compile.

Docstring and stage checks: clause (i)'s proof docstring covers steps 1--4
(coefficient identification, exact termwise pullback, flat model, flatness,
K-flat tensor calculation and separate constructibility). Clause (ii)'s covers
steps 1--2 and 5--6 (unbounded tensor comparison, exact cohomology and the unit
on each individual cohomology sheaf). This correctly avoids the blueprint
proof's unjustified bounded-below assertion about the derived tensor. Both
module and theorem docstrings name the source and exact blueprint id. The
module has exactly two theorem-body sorry terms, no data definitions, proofs,
private definitions, local notation or local instances. All variables and
universes are bound; no line exceeds 100 characters. The item's lean.statement
is byte-for-byte its primary theorem signature, checked by extraction from
the file. The repaired existing tensor signature is likewise copied verbatim
from its source; its old file-local symbols are documented in that existing
module and are not introduced in this delivery.

Mismatches found in this second reading: none. I retained the correct Lean
statements, node statement and record-only dependency repair without rewriting
them. There is no statement_change and no citer correction audit is required.
The only change by this reader is this independent report section and its
search/validation evidence.

Validation: scompile.py compiled the delivered module cleanly (sandbox 6.1 s,
library 8.9 s), within the unchanged 60-second per-file limit, with no errors
or warnings. The initial relative-path invocation from the shared repository
could not locate this sandbox-only file; rerunning with its absolute sandbox
path succeeded. Final deliver2.py dry run and delivery follow this reading;
both also check the two recorded existing tensor declarations.
