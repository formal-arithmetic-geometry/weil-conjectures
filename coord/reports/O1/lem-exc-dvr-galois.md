## Worker report

`Sheaf.RepresentationTheory.DvrGalois` states
`Rep.isZero_dvr_galois_cohomology`. Its sole postponed proof is the item's
`by sorry`; there are no additional definitions or helper theorems. The
statement is unchanged from the DAG. Its docstring gives all six DAG proof
steps: the tame quotient, its prime-to-ell kernel, finite-quotient averaging,
inflation and injectives, the common invariant resolution, and the procyclic
calculation and finiteness argument.

Sources read: the node's recorded master blueprint source and the current
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-prop-a1-kummer/lem-exc-dvr-galois.md` and `.proof.md`. Their mathematical
statements agree. The current source's coefficient prime convention is made
explicit in the DAG. The module cites that current blueprint and Stacks Tag
09E3, as does the blueprint's ramification discussion.

Every hypothesis and conclusion is rendered as follows:

- `R : Type u`, `[CommRing R] [IsDomain R] [IsDiscreteValuationRing R]`
  describe the integral-domain DVR: Mathlib's class extends local ring and
  principal ideal ring and requires nonzero maximal ideal. The explicit
  `hR : IsExcellent R` is the dependency's excellent-ring predicate.
- `[IsStrictlyHenselianLocalRing R]` is the recorded henselian local ring with
  separably closed residue field. The separate source clause that the residue
  field is algebraically closed is
  `[IsAlgClosed (IsLocalRing.ResidueField R)]`.
- `p : ℕ`, `[Fact p.Prime]`, and
  `[CharP (IsLocalRing.ResidueField R) p]` express positive residue
  characteristic. A field's positive characteristic is prime, so the prime
  fact does not exclude any positive-characteristic residue field.
- `FractionRing R` is F and
  `Gal(SeparableClosure (FractionRing R)/FractionRing R)` is precisely G,
  with Mathlib's Krull topology. This uses the separable closure even when F
  is imperfect. The imported `IsSepClosed` and `Galois.Profinite` modules
  supply its Galois and profinite structure, without extra theorem hypotheses.
- `ell : ℕ`, `[Fact ell.Prime]`, and `hell : ell ≠ p` give exactly the
  coefficient prime distinct from p.
- `A : Type v`, `[Ring A] [Finite A]` give a finite ring, with no
  commutativity assumption. `hA : ∃ s : ℕ, (ell ^ s : ℕ) • (1 : A) = 0`
  expresses ell-power annihilation of A; multiplying this equality by any
  element shows it annihilates every A-element, and hence every A-module.
- `M : DiscreteContinuousRep.{v, u, max u w} A
  (Gal(SeparableClosure (FractionRing R)/FractionRing R))` quantifies over
  the discrete continuous A[G]-modules from the recorded dependency. Its
  objects have open element stabilizers; maps are equivariant A-linear maps.
  The carrier universe is the recorded cohomology API's `max u w` with free
  `w`, so it has no upper size bound.
- `∀ q : ℕ, 1 < q → IsZero ((discreteContinuousCohomologyFunctor G A q).obj M)`
  is H^q(G,M)=0 for all q>1. Here G is expanded in the file. `IsZero` applies
  to a `ModuleCat` object, not to a bare type. This is exactly the dependency's
  right-derived invariant functor and its continuous-cochain comparison.
- `Finite M.obj.V → Finite (...) ∧ Finite (...)` says that for finite M,
  the `.carrier` types of the same cohomology functor in degrees 0 and 1
  are both finite. No finiteness restriction is placed on M in the first
  conjunct, and neither finiteness clause is omitted.

Statement dependency declarations read, including their full signatures and
source docstrings, and used:

- `Sheaf.RingTheory.ExcellentRing`: `IsExcellent`, defined as
  `IsQuasiExcellent R ∧ IsUniversallyCatenary R`.
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`:
  `IsDiscreteValuationRing`, the `mathlib_match` for
  `def-sc-discrete-valuation-ring` (this Mathlib leaf has no `lean` record).
- `WeilConjectures.Mathlib.RingTheory.Henselian`:
  `IsStrictlyHenselianLocalRing`, extending `HenselianLocalRing` with
  `isSepClosed_residueField`.
- `Sheaf.RepresentationTheory.DiscreteContinuousCohomology`:
  `Rep.discreteContinuousCohomologyFunctor`, taking a compact Hausdorff
  totally disconnected topological group and a finite ring and returning the
  right-derived invariant functor on `DiscreteContinuousRep`.

The stated proof dependencies are imported without `public`:
`Sheaf.CategoryTheory.DiscreteModulesAbelian`
(`CategoryTheory.discreteModules_abelian`),
`Sheaf.RepresentationTheory.ProcyclicTwoTerm`
(`Rep.exists_procyclic_twoTerm_computation`),
`Mathlib.CategoryTheory.Preadditive.Injective.Resolution`
(`CategoryTheory.InjectiveResolution`), and
`Mathlib.CategoryTheory.Abelian.RightDerived`
(`CategoryTheory.Functor.rightDerived`).
`lem-exc-henselian-dvr-tame-sequence` has no Lean declaration yet and therefore
has no import; it is a proof dependency, not a statement prerequisite.
No other DAG node is stated in this delivery.

Edge cases checked:

- q=0 and q=1 are excluded only from higher vanishing and remain explicitly
  present in the finite conclusion. Every natural q>1 is included.
- s=0 is permitted and gives the zero coefficient ring; the zero module is
  also permitted. There is no nonzero, faithful, or commutative coefficient
  hypothesis. No finite hypothesis on M is used for higher vanishing.
- Both equal and mixed characteristic DVRs are allowed: the `CharP` instance
  concerns only the residue field. The DVR cannot be a field, exactly as in
  its definition node. The residue and coefficient primes are unequal.
- All universes `u v w` and all variables are explicitly bound; the file
  sets `autoImplicit false`. There is no local notation or private instance.

Searches for an existing declaration (2026-10-16):

- `msearch.py leanfinder`: “Continuous Galois cohomology of the fraction field
  of an excellent strictly henselian discrete valuation ring vanishes above
  degree one for prime-to-residue-characteristic torsion coefficients”. Eight
  hits: finite-extension Hilbert 90, unrelated cotangent H1 vanishing, and
  absolute-Galois abelianization. None states this result.
- `msearch.py loogle`: `IsDiscreteValuationRing, groupCohomology`; zero hits.
- `msearch.py grep`: `cohomologicalDimension|tameInertia|wildInertia|dvr_galois`
  in `Mathlib/FieldTheory`; zero hits. Earlier recorded searches also checked
  Mathlib/RepresentationTheory and the continuous-cohomology terminology.
- `rg -n` for
  `isZero_dvr_galois_cohomology|dvr.galois|DVR.*cohomolog|cohomolog.*DVR|cohomologicalDimension|tameInertia|wildInertia`
  in Mathlib, upstream `WeilConjectures`, and project `lean/Sheaf` found only
  unrelated finite-extension DVR lemmas and the two downstream proof
  docstrings citing this item, not an existing declaration of it.
  `grep -rn lem-exc-dvr-galois` in upstream `WeilConjectures` had no hits.
- Read the actual Mathlib Krull topology, separable closure, and profinite
  Galois declarations: `SeparableClosure` is the separable closure inside the
  algebraic closure and is Galois; `InfiniteGalois` supplies `CompactSpace`
  for Galois automorphism groups; the Krull topology is totally separated
  for algebraic extensions. Thus no postponed topology helper is needed.

The existing sandbox was checked against the node and dependencies. Its final
Lean signature was retained, its source docstrings now cite the current
blueprint, and this worker report replaces superseded descriptions of three
removed topology helper theorems. The node copy is refreshed from the shared
base with only `lean` changed; its `lean.statement` is the file signature
with whitespace flattened. There is no statement correction,
`STATEMENT-DISPUTED` flag, new node, or dependency repair.

Validation: `scompile.py N1 lem-exc-dvr-galois
lean/Sheaf/RepresentationTheory/DvrGalois.lean` returned exit 0, with no
errors or warnings, for the statement. The delivery dry run is the final
check. A fresh second reader will read the final module and this report;
no second-reading section is asserted by this worker.


## Earlier second reading (a previous round; superseded)

I independently compared the unchanged DAG statement and its six proof steps with
`DvrGalois.lean`, the original master blueprint statement/proof, the current
main-20261015 statement/proof, and Stacks `more-algebra.tex`, Section 09E3.
The Stacks ramification lemmas introduce a DVR with fraction field and a finite
Galois extension; they impose no additional ambient completeness or characteristic
zero assumption. The blueprint's purity conventions explicitly fix a prime ell.
No statement correction or maintenance repair note applies to this item.

Here is my object/hypothesis/conclusion inventory and its Lean comparison:

1. An excellent DVR R: `R : Type u`, `[CommRing R] [IsDomain R]`,
   `[IsDiscreteValuationRing R]`, and `hR : IsExcellent R`. Verdict: exact.
   I read `ExcellentRing.lean`: excellence is quasi-excellence and universal
   catenarity, including the Noetherian, G-ring, open regular locus, and chain
   conditions. Mathlib's DVR class is a local principal ideal domain with
   nonzero maximal ideal; it does not mean an arbitrary valuation ring or a
   field. Neither completeness nor a chosen uniformizer is assumed.
2. Strict henselianity: `[IsStrictlyHenselianLocalRing R]`. Verdict: exact.
   The recorded upstream class extends `HenselianLocalRing` and has the
   `isSepClosed_residueField` field. The separate clause that the residue
   field is algebraically closed is retained as
   `[IsAlgClosed (IsLocalRing.ResidueField R)]`; it was not silently weakened
   to separable closedness.
3. Positive residue characteristic p: `(p : ℕ) [Fact p.Prime]` and
   `[CharP (IsLocalRing.ResidueField R) p]`. Verdict: exact.
   Positive characteristic of a field is prime, so this exposes an implied
   fact rather than imposing an extra restriction. No characteristic is
   imposed on R itself or its fraction field.
4. F = Frac(R) and G = Gal(F-sep/F): `FractionRing R` and
   `Gal(SeparableClosure (FractionRing R)/FractionRing R)`. Verdict: exact.
   I read Mathlib's separable-closure construction, Krull topology, and
   Galois profiniteness instance. The chosen separable closure is Galois;
   compactness, Hausdorffness, total disconnectedness, and the topological
   group structure used by the cohomology API are supplied by those imports.
   None is a new hypothesis or a postponed helper in this module.
5. A prime ell distinct from p: `(ell : ℕ) [Fact ell.Prime]` and
   `hell : ell ≠ p`. Verdict: exact, including the blueprint's coefficient
   prime convention and the DAG's explicit word 'prime'.
6. A finite ring A killed by an ell-power: `(A : Type v) [Ring A] [Finite A]`
   and `hA : ∃ s : ℕ, (ell ^ s : ℕ) • (1 : A) = 0`. Verdict: exact.
   An integer annihilates a unital ring exactly when it annihilates its unit;
   this then annihilates every left A-module. Commutativity, nontriviality,
   and a fixed positive exponent are not imposed.
7. Every discrete continuous A[G]-module M:
   `M : DiscreteContinuousRep.{v, u, max u w} A G`, with G expanded above.
   Verdict: the recorded category, not a category of finite modules.
   Because the module is absent from the older local upstream tree, I read
   its current source using `scompile.py --source
   WeilConjectures.RepresentationTheory.DiscreteContinuousRep`. It is the
   full subcategory of `Rep A G` on actions with open element stabilizers;
   its morphisms are equivariant A-linear maps.
8. H^q(G,M) = 0 for every q > 1: the first conjunct is
   `∀ q : ℕ, 1 < q → IsZero ((discreteContinuousCohomologyFunctor G A q).obj M)`.
   Verdict: exact, with no finiteness hypothesis on M.
   I read the dependency's actual body and its continuous-cochain comparison:
   the functor is `Functor.rightDerived` of an additive invariant functor
   naturally linearly equivalent, compatibly with maps, to the fixed submodule.
   Thus this is the specified continuous cohomology, and `IsZero` is applied
   to a module-category object.
9. If M is finite, both H^0 and H^1 are finite: the second conjunct starts
   `Finite M.obj.V →` and concludes the conjunction of `Finite` on the
   `.carrier` of the same cohomology functor in degrees 0 and 1.
   Verdict: both clauses are present, with the quantifiers in the required
   order. The conclusion does not assert finiteness for arbitrary M.

Edge cases: q = 0 and q = 1 are outside the higher-vanishing clause and are
both inside the finite-module clause; every q >= 2 is covered. The exponent
s = 0 and the zero coefficient ring are allowed, as is the zero module.
Infinite discrete modules are permitted in higher vanishing. The zero ring
and fields are excluded as DVRs by the mathematical definition itself.
Both equal and mixed characteristic R are covered, with p = 2 and ell = 2
allowed when distinct. There is no index family or scheme here, so empty
index/empty scheme cases do not arise. Universes u, v, w are all bound;
the carrier universe `max u w` is precisely the recorded cohomology API's
size convention, with w arbitrary and no equation between coefficient and
field universes. Smaller carriers have their usual lifted representatives;
there is no finite-dimensional or small-cardinality constraint.

Independent searches on 2026-10-16 (with phrases different from the first
worker's principal query):

- LeanSearch: 'An excellent henselian discrete valuation ring with
  algebraically closed residue field of characteristic p has absolute Galois
  ell cohomological dimension at most one for ell different from p'. Eight
  hits, all henselian/DVR infrastructure and Hensel's lemma; none states the
  cohomological assertion.
- LeanFinder: 'For a henselian trait with algebraically closed residue field,
  prime-to-residue-characteristic continuous Galois cohomology is finite in
  degrees zero and one and vanishes in higher degrees'. Eight hits:
  residue-field finiteness, arithmetic Frobenius, and finite-extension
  Hilbert 90. These concern other objects or only degree-one multiplicative
  cohomology and do not give this node.
- Loogle: `IsDiscreteValuationRing, _ = 0` returned five valuation identities,
  none about cohomology. The earlier query using
  `IsStrictlyHenselianLocalRing` was unavailable in Loogle's index; I did not
  treat that diagnostic as evidence of mathematical absence.
- The grep search service found no hits for
  `cohomology.*henselian|henselian.*cohomology|ramification.*cohomology|cohomology.*ramification`.
  I also used `rg` on Mathlib, upstream `WeilConjectures`, and project
  `lean/Sheaf`, looking for cohomological dimension, tame/wild inertia,
  DVR/cohomology, valuation/cohomology, and strictly henselian/cohomology.
  The results were different geometric dimension bounds or absolute-Galois
  definitions, not this simultaneous vanishing and finiteness theorem.
  The existing absolute-Galois notation uses automorphisms of an algebraic
  closure; this delivery instead directly uses the source's separable
  closure and introduces no competing definition.

There are no added nodes or dependency modules to audit. The statement
imports all four recorded statement dependencies. I also checked the
available proof imports, including `discreteModules_abelian`,
`exists_procyclic_twoTerm_computation`, `InjectiveResolution`, and
`Functor.rightDerived`. The structural tame-sequence proof dependency is
not yet recorded as Lean, so its absence from imports is appropriate.
The theorem docstring reproduces the six DAG steps in order, including
finite-quotient averaging, inflation's adjunction, the common injective
resolution, and the final kernel/cokernel finiteness argument.

No mathematical or interface mismatch was found. I retained the Lean file
and its statement record. Only this independent second-reading report was
added. The node differs from the shared base only in `lean`; its recorded
signature equals the file signature after whitespace normalization.
The file has one named theorem with its whole proof `sorry`, no definitions,
no local notation/instance, no unbound names, and no overlong lines.

Validation: the prescribed `scompile.py N1 lem-exc-dvr-galois
lean/Sheaf/RepresentationTheory/DvrGalois.lean` returned exit 0 with clean
server compilation (3.3 seconds for the item, no warnings). The local overlay
attempt had hit its 60-second limit; the wrapper's normal current-server
confirmation succeeded without changing the limit or the statement.

Delivery-tool failure: two consecutive invocations of
`deliver2.py N1 lem-exc-dvr-galois --no-push` terminated with exit 143
(SIGTERM), without a diagnostic, after announcing the library compile.
Neither printed OK, so no push was attempted. The standalone prescribed
scompile server confirmation above passed. The reviewed statement and
second-reading report remain available in this sandbox for retry.


## Second reading by N1

I independently read the node and final Lean file, rather than relying on the
previous reading above. I also opened both blueprint versions and the current
proof, the statement-dependency nodes and their actual declarations, and Stacks
`more-algebra.tex`, Section 09E3 (Galois extensions and ramification). The latter
starts with a DVR, its fraction field, and a finite Galois extension; it assumes
neither completeness nor characteristic zero. I checked `pione.tex`, Tag 0BUB,
for the separable-closure ramification formulation. There is no repair note for
this item. The node has no statement correction and the sandbox differs from
the current shared node only in `lean`.

My inventory of the node's objects, hypotheses, and conclusion clauses, with
its Lean rendering and verdict, is:

1. An excellent integral-domain DVR R: `(R : Type u) [CommRing R] [IsDomain R]
   [IsDiscreteValuationRing R] (hR : IsExcellent R)`. Exact. I read
   `IsDiscreteValuationRing` in Mathlib: it extends `IsPrincipalIdealRing` and
   `IsLocalRing` and requires nonzero maximal ideal. I read `IsExcellent` in
   `Sheaf.RingTheory.ExcellentRing`: it is quasi-excellence and universal
   catenarity, with the specified Noetherian, G-ring, regular-locus and chain
   conditions. No chosen uniformizer, completion, or extra finiteness is assumed.
2. R is strictly henselian: `[IsStrictlyHenselianLocalRing R]`. Exact. The
   dependency's upstream class extends `HenselianLocalRing` and specifies
   separable closedness of the residue field, as the node requires.
3. Its residue field is algebraically closed of characteristic p > 0:
   `[IsAlgClosed (IsLocalRing.ResidueField R)] (p : ℕ) [Fact p.Prime]
   [CharP (IsLocalRing.ResidueField R) p]`. Exact. Algebraic closedness is
   separately retained, not replaced by separable closedness. Positive field
   characteristic is necessarily prime, so the prime fact adds no mathematical
   restriction. R itself and its fraction field have no characteristic binder.
4. F = Frac(R), and G = Gal(F-sep/F): `FractionRing R` and
   `Gal(SeparableClosure (FractionRing R)/FractionRing R)`. Exact. I opened the
   Mathlib separable-closure and Galois-profiniteness declarations: the chosen
   separable closure is Galois, and Krull topology supplies the requisite
   profinite topological-group instances. This covers imperfect fraction fields;
   it neither assumes F perfect nor substitutes a finite Galois group.
5. A prime ell distinct from p: `(ell : ℕ) [Fact ell.Prime] (hell : ell ≠ p)`.
   Exact against the explicit DAG statement and the source's prime convention.
6. A finite ring A killed by an ell-power: `(A : Type v) [Ring A] [Finite A]`
   and `hA : ∃ s : ℕ, (ell ^ s : ℕ) • (1 : A) = 0`. Exact. An integer kills
   a unital ring precisely when it kills its unit. Multiplying the unit relation
   kills every ring element and hence every A-module. Neither commutativity,
   nontriviality, nor a prescribed positive exponent is added.
7. Every discrete continuous left A[G]-module M:
   `M : DiscreteContinuousRep.{v, u, max u w} A G`, with G expanded in the file.
   Exact. I read the current upstream module through `scompile.py --source
   WeilConjectures.RepresentationTheory.DiscreteContinuousRep`: it is the full
   subcategory of `Rep A G` with open element stabilizers. Its morphisms are
   equivariant A-linear maps. No finite-module restriction is present here.
8. Vanishing in every degree q > 1: the first conjunct is
   `∀ q : ℕ, 1 < q → IsZero ((discreteContinuousCohomologyFunctor G A q).obj M)`.
   Exact. I read `Sheaf.RepresentationTheory.DiscreteContinuousCohomology`
   and its comparison theorem `continuousCochains_derived_invariants` in
   `Sheaf.RepresentationTheory.ContinuousCochainsDerivedInvariants`. The functor
   is right-derived invariants, naturally identified with the usual continuous
   inhomogeneous cochain cohomology; the fixed-submodule and coefficient maps
   are specified. `IsZero` concerns a ModuleCat object, not a bare type.
9. If M is finite, H^0 and H^1 are finite: the second conjunct is
   `Finite M.obj.V → Finite (... A 0 ...).carrier ∧ Finite (... A 1 ...).carrier`.
   Exact. It applies to the same cohomology functor and same arbitrary M as
   the first conjunct. Both degree clauses and the conditional order are intact.

Edge cases: q = 0 and q = 1 are excluded only from higher vanishing and both
appear in the finiteness clause. All q >= 2 occur. The exponent s = 0, zero
coefficient ring, zero module, and infinite discrete modules are allowed.
A field or zero ring cannot be the DVR, as required by its definition node.
Both equal and mixed characteristic are included. The primes may include 2,
but must be distinct. There is no scheme or index-family parameter, so empty
scheme and empty-index cases do not arise. Universes u, v, w are explicitly
bound. The carrier universe `max u w` is inherited from the recorded continuous
cohomology API, with arbitrary w, no equality of coefficient and field universes,
and no cardinality bound; smaller carriers admit their lifted representatives.
No universe or variable is left auto-implicit.

Independent searches used different phrases from the worker's main query:

- LeanSearch: "The absolute Galois group of the fraction field of a henselian
  valuation ring has vanishing continuous cohomology above one for torsion prime
  to residue characteristic". Eight hits: absolute-Galois definitions, Krull
  topology, fraction-ring Galois transport, cyclotomic continuity, and degree-zero
  continuous cohomology. None gives this vanishing and finiteness theorem.
- LeanFinder: "finite ring killed by a power of a prime continuous Galois module
  H^0 H^1". Eight hits: arithmetic Frobenius, Hilbert 90, and a finite-extension
  inertia/degree formula. None treats this absolute Galois cohomology assertion.
- Loogle: `DiscreteContinuousRep cohomology IsZero` reports the identifier absent
  from its index, so this is an unavailable indexed notion, not evidence of
  absence. LeanFinder supplies the successful second search kind.
- The prescribed grep service found zero hits for
  `henselian.*cohomolog|cohomolog.*henselian|valuation.*cohomolog|cohomolog.*valuation`.
  Direct `rg` over Mathlib, upstream `WeilConjectures`, and project `lean/Sheaf`
  for those concepts and ramification/cohomology found no matching statement.
  The theorem name and blueprint id are also absent from upstream declarations
  and `dag/lean_names_upstream.json`. The module introduces no competing notion.

I read the available proof-dependency declarations as well: the discrete-module
abelian/enough-injective theorem, the natural procyclic two-term computation,
Mathlib injective resolutions and right derived functors. Their modules are
imported without `public`. The tame-sequence proof dependency has no recorded
Lean module and appropriately contributes no import. All six DAG proof steps
are present in the theorem docstring in order. There are no new definition
nodes or dependency modules to review. The file has one named theorem whose
entire proof is `sorry`, no new definitions, no hollow data or hypotheses, no
local notation or private instance, and no lines beyond 100 characters.

No mathematical or dependency-interface mismatch was found; I retained the Lean
file. I repaired the record-only discrepancy that `lean.statement` had flattened
whitespace: it now equals the literal multiline signature from `theorem` to
before `:=`. This does not change the theorem or the DAG statement. This section
supersedes the historical validation and delivery-failure status above.

Validation: from the sandbox, the prescribed `scompile.py N1 lem-exc-dvr-galois
lean/Sheaf/RepresentationTheory/DvrGalois.lean` returned exit 0. Both the sandbox
check (5.0 s) and the library-context file check (4.6 s) compiled cleanly, without
warnings or errors. Delivery preflight and push follow this reading.
