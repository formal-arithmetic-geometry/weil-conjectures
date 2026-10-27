## Worker report

The module `Sheaf.AlgebraicGeometry.JTwoClosedFibreRegularLocus` states
`AlgebraicGeometry.isOpen_regularLocus_on_j2_closedFibre`. Its sole proof is `sorry`.
It introduces no definitions, helper theorems, or new nodes. Only the item's `lean`
record changes; its statement, dependencies, accepted split, and other fields are preserved.

The mathematical source was read online: Kurano–Shimomoto,
[Ideal-adic completion of quasi-excellent rings (after Gabber)](https://www.isc.meiji.ac.jp/~kurano/ronbun/kurano40.pdf),
Lemma 4.2 and Claim 4.3, printed pp. 4–5. Lemma 4.2 has precisely the node's
Noetherian base, arbitrary ideal, finite-type scheme map, J-2 quotient, and
relative openness conclusion. The equivalent ambient closedness follows because
this fibre is closed. Stacks `more-algebra.tex`, definition-J (07P7) and
lemma-intersection-regular-with-closed (07P9), were also read. WANTED: an archival
local copy of the Kurano–Shimomoto paper, as already indicated in the node's source.
No source statement correction or mathematical dispute was needed.

Hypothesis and clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Commutative Noetherian ring A | `(A : Type u) [CommRing A] [IsNoetherianRing A]` |
| Arbitrary ideal I of A | `(I : Ideal A)`; no properness or radical assumption |
| Scheme X | `(X : Scheme.{u})` |
| Named map f to Spec A | `(f : X ⟶ Spec (CommRingCat.of A))` |
| f of finite type | `[LocallyOfFiniteType f] [QuasiCompact f]`, exactly the conjunction in the recorded finite-type dependency |
| A/I is J-2 | `hJ` quantifies over every commutative finite-type `(A ⧸ I)`-algebra B and asserts openness of `{p : PrimeSpectrum B \| IsRegularLocalRing (Localization.AtPrime p.asIdeal)}` |
| Z is f inverse image of V(I), with subspace topology | The subtype `{x : X // f x ∈ PrimeSpectrum.zeroLocus (I : Set A)}` has the induced topology; `Spec (.of A)` has underlying space `PrimeSpectrum A` |
| Ambient regular locus open in Z | The first conjunct `IsOpen {x : {x : X // ...} \| IsRegularLocalRing (X.presheaf.stalk x.1)}` |
| Equivalent set W closed in X | The second conjunct `IsClosed {x : X \| f x ∈ PrimeSpectrum.zeroLocus (I : Set A) ∧ ¬ IsRegularLocalRing (X.presheaf.stalk x)}` |
| Use the local rings of X | Both conjuncts explicitly use `X.presheaf.stalk`; no closed-subscheme stalk occurs |

The two conclusions are conjoined so the declared theorem supplies each advertised
form directly. This does not strengthen the node: its equivalence uses only that
`f⁻¹V(I)` is closed and the complementary sets have the indicated subspace topology.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme.Hom`, `AlgebraicGeometry.Spec`, and `Spec.map`.
  The actual theorem uses `Scheme`, scheme morphisms, and `Spec` directly.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`; its public dependency
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` supplies
  `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` and its ideal-finiteness
  meaning. No separate Noetherianity assumption is imposed on X or A/I.
- `Sheaf.RingTheory.ExcellentRing`: `IsQuasiExcellent`, whose final conjunct is
  the J-2 condition used verbatim as the quantified `hJ`. Neither its Noetherian
  conjunct nor its G-ring conjunct is imposed on A/I as an extra hypothesis.
  The dependency has no standalone J-2 declaration; existing siblings likewise
  write this exact conjunct explicitly, so no second named definition is needed.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`,
  reusing `WeilConjectures.AlgebraicGeometry.Regular`'s stalkwise `IsRegular`.
  For this pointwise statement the unchanged ring clause of the node is the
  recorded Mathlib match `IsRegularLocalRing` in
  `Mathlib.RingTheory.RegularLocalRing.Defs`; that class is used at each stalk.
  The scheme predicate is imported but is not assumed globally.
- `PrimeSpectrum.zeroLocus` is the existing zero locus in the spectrum,
  not a new closed-fibre definition.

All recorded proof-dependency modules are included as plain imports where they
are not statement dependencies. This includes finite-type Noetherianity,
affine stalk localization, quotient spectra, prime-localization correspondence,
localization of localizations, regular-local localization, regular systems of
parameters, spreading a regular sequence, denominator clearing, localization of
weakly regular sequences, quotient localization, localization Noetherianity,
lifting regularity from a regular-sequence quotient, and the constructibility
criteria. The docstring spells out all nine accepted proof steps and names the
relevant DAG inputs. No proof was attempted.

Universes: all variables and the universe `u` are explicit, with
`set_option autoImplicit false`. The J-2 test algebras are in `Type u`, the
universe of A and the affine chart rings of X. This is the dependency's size
convention; a finite-type algebra in a larger universe is isomorphic to a
quotient of a finite polynomial algebra in the base universe. There is no
independent smaller test-algebra universe that could make the hypothesis vacuous.

Edge cases checked before writing:

- I is the unit ideal: V(I), Z and W are empty. Relative openness and ambient
  closedness hold; no proper-ideal restriction excludes this case.
- I is zero: Z is X, and the conclusion is ordinary regular-locus openness for
  a finite-type scheme over a J-2 Noetherian base.
- X empty, and A the zero ring: no point is demanded and both conclusions allow
  the empty scheme. A scheme mapping to the empty spectrum must itself be empty.
- The ambient/fibre distinction: take A = k[ε]/(ε²), I = (ε), and f the identity.
  Then A/I = k is J-2, the closed subscheme is regular, but the ambient local
  ring at its unique point is nonregular. The stated regular subset is empty
  and W is the whole point, as required. Fibre-stalk regularity would be wrong.
- No reducedness, domain, characteristic-zero, flatness, separateness, or
  excellence assumption was added. Zero-dimensional parameter systems and empty
  products are handled in steps 5–6 of the proof docstring.

Searches made for an existing statement (2026-10-24):

- `msearch.py ... leanfinder`: “For a finite type scheme X over a Noetherian
  ring A and an ideal I with J-2 quotient A/I the ambient regular locus restricted
  to the preimage of V(I) is open in that closed subspace”. Eight hits, on
  smooth, étale, unramified, free and related loci; none is ambient regularity
  along a J-2 closed fibre.
- `msearch.py ... leansearch`: “regular locus of ambient scheme restricted to
  inverse image of V I open when quotient base is J2”. Eight hits on restriction
  morphisms and their properties, plus the existing zero-locus comparison;
  none states this theorem.
- `msearch.py ... loogle '"IsJ2Ring"'`: zero hits.
- `msearch.py ... grep 'regularLocus|IsJ2Ring|IsQuasiExcellent|isRegularLocus'`:
  zero Mathlib hits.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for J-2/regular loci found
  `WeilConjectures.RingTheory.Excellent`'s `IsJ2` and
  `PrimeSpectrum.regularLocus`, plus the landed ExcellentRing, JTwoAffineCover,
  JTwoFiniteAlgebraCriterion and regular-locus criterion modules. These give
  notions or different algebraic criteria, not this theorem. The statement
  follows the already-recorded dependency's explicit J-2 conjunct.
- Searches for the node id in `lean/WeilConjectures` and for the proposed
  theorem name in both source trees and `dag/lean_names_upstream.json` found
  no duplicate. Searches for regular/closed/fibre combinations found only
  different flat-local and fibre-regularity results.

Validation: the prescribed `scompile.py` compiled the module in both sandbox
and library module modes without errors or warnings (2.4 s and 2.2 s for the
initial compile). The final import-complete module is recompiled by the dry run.

## Second reading by Q96

This is a second pass by the same worker; the dispatcher's explicit instruction
forbids starting other agents. The maintainer supplies the independent review.
I reopened the node and the module and checked their clauses against the table:
Noetherian A, arbitrary I, a named finite-type map with BOTH finite-type
properties, and exactly the J-2 quotient assumption. In particular `hJ` does
not accidentally assume quasi-excellence. The subtype uses the actual inverse
image of V(I) with its induced topology. Its predicate uses `x.1` to take the
stalk on X; the second conjunct uses the same stalk and conjoins membership in
Z before negating regularity. Neither conjunct uses a local ring of the fibre
subscheme. The two results match the node's equivalent forms, with no equality
or witness assumption added. The empty, unit-ideal and nonreduced test cases
above still match after elaboration. No mismatch was found and no statement
or dependency change was required. Two explicit Mathlib proof imports were
added to cover the multideclaration quotient-localization dependency in full.
