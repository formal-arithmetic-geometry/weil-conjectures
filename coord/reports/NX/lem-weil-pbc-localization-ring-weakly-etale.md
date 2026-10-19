## Worker report

The node is exactly the existing theorem
`Algebra.WeaklyEtale.of_isLocalization` in
`WeilConjectures.Mathlib.RingTheory.Etale.Weakly` (lines 44–53 of the read-only
upstream source). The published server source was also read through
`scompile.py --source WeilConjectures.Mathlib.RingTheory.Etale.Weakly` and has
this same declaration and proof. Accordingly this delivery records
`existing: true` and adds no Lean module or theorem.

Hypotheses and clauses match as follows:

- The commutative ring A is `(R : Type*) [CommRing R]`.
- The multiplicative subset M, including its unit and multiplication closure,
  is `(S : Submonoid R)`. No exclusion of zero or nontriviality is imposed.
- The commutative fraction ring B and its canonical map are
  `(T : Type*) [CommRing T] [Algebra R T] [IsLocalization S T]`.
  Mathlib's `IsLocalization` says that T is isomorphic as an R-algebra to the
  localization at S. Its defining conditions invert S, express every element
  as a fraction, and identify base elements exactly after multiplication by
  an element of S. They therefore give precisely the fraction equivalence
  in the node, including zero divisors; this is not an arbitrary R-algebra.
  In particular the literal `Localization S` carries these instances.
- The conclusion is `Algebra.WeaklyEtale R T`. In
  `Mathlib.RingTheory.Etale.Weakly` the class fields are
  `flat : Module.Flat R T` and
  `flat_lmul' : (Algebra.TensorProduct.lmul' R (S := T)).Flat`.
  These are respectively flatness of B over A and flatness of B over
  B tensor_A B via the multiplication map. No clause is omitted or added.

Dependency read and used: `def-weil-pbc-ind-etale-algebra` records
`Sheaf.RingTheory.IndPrincipalZariski`, whose module docstring and public imports
explicitly reuse `Algebra.WeaklyEtale` for its weakly etale clause. Its other
recorded declarations concern ind-etale and ind-Zariski algebras and are not
needed for this localization theorem. The relevant full class signature and
fields were read in `Mathlib.RingTheory.Etale.Weakly`; the dependency module's
full definition and documentation were also read. No dependency repair is needed.

The source `literature/stacks-project/more-algebra.tex`, definition
`definition-weakly-etale` (Tag 092B), defines the two flatness conditions and
immediately states that a localization is weakly etale. The existing theorem
also carries Stacks Tag 092J (1). Its proof uses `IsLocalization.flat`, then
bijectivity of tensor multiplication (`IsLocalization.bijective_linearMap_mul'`)
and flatness of a bijective ring map. The node has no additional proof steps.

Edge cases checked by inspecting the unrestricted theorem and the localization
conditions: S containing zero (zero localization), the zero base ring,
S = {1} (identity localization), arbitrary infinite multiplicative subsets,
and rings with zero divisors. All are included: no field, domain, finite
presentation, nonzero-denominator, or Nontrivial hypothesis occurs. The base
and localization types have independently generalized universe levels in the
existing theorem; no common-universe restriction is added.

Searches performed:

- LeanFinder, through `msearch.py`: “Every localization of a commutative ring
  at a multiplicative subset is weakly etale”. Eight Mathlib hits, including
  `Algebra.Etale.of_isLocalizationAway` and formal-etale localization results;
  none is the arbitrary-localization weak-etale theorem.
- Loogle, through `msearch.py`: `Algebra.WeaklyEtale, IsLocalization`.
  Zero hits.
- Mathlib grep, through `msearch.py`: `WeaklyEtale|weaklyEtale` in
  `RingTheory/Etale/Weakly.lean`. Five hits including the class and its flatness
  field; the source file was opened to inspect the full definition.
- Project grep: `of_isLocalization` and `WeaklyEtale` in the read-only
  WeilConjectures tree located the exact theorem in
  `WeilConjectures/Mathlib/RingTheory/Etale/Weakly.lean`. The whole declaration,
  docstring, and proof were read, then confirmed in the server source.
  The `msearch.py` grep with subdirectory `WeilConjectures` returned zero
  Mathlib hits; direct project `rg` supplied the project search.
- Direct `rg` for the item id in the upstream project returned no blueprint
  marker; this does not affect the full statement match above.
- Direct `rg` for `of_isLocalization|Localization.*Weakly|WeaklyEtale` in
  `lean/Sheaf` and the project source found the dependency's reuse of the
  Mathlib notion and the exact upstream theorem. No duplicate is written.

No statement correction, disputed statement, new node, or dependency module.
The dry run performs a real server #check of the existing declaration.

## Second reading by NX

I independently opened the item JSON, the existing upstream theorem (including its
namespace and preceding binders), the current published source returned by
`scompile.py --source WeilConjectures.Mathlib.RingTheory.Etale.Weakly`, and
Stacks `more-algebra.tex`, lines 30179–30201. The section introduces no standing
field, finiteness, or nontriviality hypotheses. Tag 092B defines exactly the two
flatness conditions and its following paragraph asserts the localization case.

The complete object/hypothesis/conclusion checklist is:

- Commutative ring A: `(R : Type*) [CommRing R]`. Exact; no domain, field,
  Noetherian, characteristic, or nonzero condition.
- Multiplicative subset M with 1 and product closure: `(S : Submonoid R)`.
  Exact; these are the submonoid axioms, without a nonzero-denominator condition.
- Fraction ring B and canonical A-algebra map: `(T : Type*) [CommRing T]
  [Algebra R T] [IsLocalization S T]`. Exact up to the canonical algebra
  isomorphism, as intended by the node's fraction-ring description. I read
  `IsLocalization'`, `isLocalization_iff`, and `IsLocalization.eq_iff_exists`
  in Mathlib's `RingTheory/Localization/Defs.lean`: denominators become units,
  every element is a fraction, and equality of base elements is precisely
  equality after multiplication by a denominator. Applying this to cross
  products gives the node's relation u(at-bs)=0, even with zero divisors.
  The algebra map is thus the localization map, not an arbitrary chosen map.
- B flat over A: `Algebra.WeaklyEtale R T`, field `flat : Module.Flat R T`.
  Exact.
- B flat over B tensor_A B through multiplication: the same conclusion's
  field `flat_lmul'`, the flatness of `Algebra.TensorProduct.lmul' R`.
  Exact. I read the class fields rather than relying on the class docstring
  (whose displayed codomain has a harmless R/S typo).
- Quantifier order: R, its submonoid S, and any realization T of that
  localization, followed by the weakly-etale conclusion. Exact; allowing any
  isomorphic localization realization adds no mathematical hypothesis or claim.

I also opened the dependency node `def-weil-pbc-ind-etale-algebra` and its
recorded module `Sheaf.RingTheory.IndPrincipalZariski`. Its weakly-etale clause
explicitly reuses this very Mathlib class. The recorded spectrum comparison
`AlgebraicGeometry.weaklyEtale_SpecMap_algebraMap_iff` identifies the class with
weak etaleness of the canonical affine scheme map. Its same-universe scheme
binders impose no restriction on this purely ring-theoretic theorem, whose
R and T universes are independently generalized. The principal ind-Zariski
predicate is a different clause and is not substituted for weak etaleness.
No dependency repair, new definition node, or sibling module is required.

Edge cases: zero base ring, S containing zero (hence zero localization),
S = {1}, arbitrary infinite S, and rings with zero divisors are all admitted.
The multiplicative subset itself cannot be empty because 1 belongs to it;
there is no index set, degree n, or scheme input to restrict. The zero
localization includes the corresponding empty affine scheme case. All
characteristics and independent ring universes are covered. All theorem
variables and instances are bound, and the recorded signature matches the
source verbatim up to its `where` body delimiter.

Independent searches used different wording: LeanFinder via `msearch.py` for
“Flatness of a localization and its tensor square multiplication map” returned
`IsLocalization.flat`, `Localization.flat` and related flatness results, but
no replacement for the full theorem. Loogle via `msearch.py` for
`IsLocalization, Algebra.WeaklyEtale` returned zero hits. Direct `rg` over
Mathlib localization sources, upstream ring-theoretic etale sources, and
`lean/Sheaf/RingTheory` for `of_isLocalization`, `WeaklyEtale`, and weakly-etale
wording confirmed the exact upstream theorem and the dependency's existing
class reuse. The theorem body uses localization flatness and bijectivity of
tensor multiplication to establish its flatness; it is already proved upstream.

Verdict: no mismatch found and no Lean or node correction needed. Reusing an
existing theorem creates no hollow data, new proof, or duplicate definition;
new-module docstring/proof obligations do not apply. The node has no proof
steps to transcribe. This second reading adds only this report section.
Validation is the delivery script's real server import and `#check` through
`scompile`, followed by stage-2 preflight; no new file needs compilation.
