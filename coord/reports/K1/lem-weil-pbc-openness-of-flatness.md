## Worker report

The module `Sheaf.RingTheory.OpenFlatLocus` states
`Module.isOpen_setOf_flat_localizedModule`, with its proof `sorry`.
It introduces no new definition. The node and its statement are unchanged.

Source checked: https://stacks.math.columbia.edu/tag/00RC, Theorem 10.129.4.
The local literature checkout has no `algebra.tex`, so the source was read online.
The theorem there has precisely an arbitrary base ring, a finitely presented
algebra, a finitely presented module, and the asserted open locus.

Hypotheses and conclusion, clause by clause:
- Commutative rings R and S: `{R : Type u} {S : Type v}` with
  `[CommRing R] [CommRing S]`.
- Ring map R → S: `[Algebra R S]`, representing `algebraMap R S`.
  Every commutative ring homomorphism gives this structure via `RingHom.toAlgebra`.
- Finite presentation of that map: `[Algebra.FinitePresentation R S]`.
- S-module M: `{M : Type w} [AddCommGroup M] [Module S M]`.
- Finite presentation of M, equivalently a cokernel of a map between finite free
  S-modules: `[Module.FinitePresentation S M]`. Mathlib defines this by finite
  generators and finitely generated presentation kernel, giving exactly that
  finite free presentation; no chosen presentation is required by the node.
- Induced R-action: `[Module R M] [IsScalarTower R S M]`. This is structural
  bookkeeping, not an additional mathematical restriction: the tower axiom at
  `1 : S` says `r • m = (algebraMap R S r) • m`; the induced action always exists.
- A prime q of S: `q : PrimeSpectrum S`, with ideal `q.asIdeal`.
- Localization M_q at S minus q: `LocalizedModule q.asIdeal.primeCompl M`.
  Its inherited R-action acts on the numerator, so is the required restricted action.
- Flatness over R: `Module.Flat R (LocalizedModule q.asIdeal.primeCompl M)`.
- The set of exactly those primes: the set comprehension in the conclusion.
- Openness in the specified Zariski topology: `IsOpen` with Mathlib's
  `PrimeSpectrum.zariskiTopology`, whose closed sets are zero loci (equivalently
  V(J) for ideals J). This is the underlying topology of the dependency's Spec.

Dependency declarations read and used:
- `def-weil-pbc-finitely-presented-algebra`: `Algebra.FinitePresentation`,
  `Mathlib.RingTheory.FinitePresentation` (definition by finite polynomial
  generators and finitely generated kernel).
- `def-weil-pbc-localization-at-prime`: the recorded `Localization.AtPrime`
  in `Mathlib.RingTheory.Localization.AtPrime.Basic` is localization at
  `p.primeCompl`; its record explicitly identifies module localization as
  `LocalizedModule p.primeCompl M`. We use that Mathlib module construction,
  available through `Mathlib.RingTheory.Flat.Localization`.
  The recorded residue-field and fibre-ring declarations were also read but
  are not needed in this statement.
- `def-weil-pbc-flat-ring-map`: the recorded `Module.Flat` from
  `Mathlib.RingTheory.Flat.Basic`, available through the localization import.
  The equivalence with tensor-injectivity is documented and proved there.
  `RingHom.Flat` was read; ring-map flatness is not the predicate asserted here.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map` from
  `Mathlib.AlgebraicGeometry.Scheme` were read. Their underlying space is
  Mathlib's `PrimeSpectrum S`, so the ring-theoretic statement uses that existing
  carrier and its topology directly, imported from
  `Mathlib.RingTheory.Spectrum.Prime.Topology`. No redundant scheme import.
- Finitely presented modules use `Module.FinitePresentation` from
  `Mathlib.Algebra.Module.FinitePresentation`, whose definition and docstring
  were read. No missing notion or unusable dependency was found.

Edge cases checked before writing: the zero ring S has empty spectrum, so the
conclusion is openness of the empty set; zero M has everywhere-flat localizations
and the locus is the whole spectrum. Finite free presentations allow zero
relations and zero generators. The identity ring map specializes to the usual
flat locus of a finitely presented module over its own ring. No Noetherian,
nontriviality, finite-type-over-integers, characteristic, or nonzero-rank
hypothesis is imposed. The universes of both rings and M are independently
bound; no size case is excluded. Scalar compatibility is explicit.

Searches (recorded by msearch.py in searches.jsonl):
- LeanFinder: "The flat locus of a finitely presented module over a finitely
  presented algebra is open in its prime spectrum". Eight hits, including
  `Module.isOpen_freeLocus`, localization criteria, and smooth-locus openness;
  none is the relative flat-locus theorem.
- Loogle: `Module.Flat, IsOpen`. Zero hits.
- LeanSearch: "Openness of the flat locus of a finitely presented module over
  a finitely presented algebra". Service unavailable (Internal Server Error);
  no absence verdict is inferred from this unavailable service.
- Mathlib grep: `flatLocus|flat_locus|isOpen.*flat|openness.*flat`. Seven hits
  on geometric flatness/open immersions, none on this locus.
- rg of all `WeilConjectures` and `lean/Sheaf` for
  `flatLocus|flat_locus|isOpen.*[Ff]lat|lem-weil-pbc-openness-of-flatness`:
  found `PrimeSpectrum.isOpen_setOf_flat_localization` in the source extension
  `WeilConjectures.Mathlib.RingTheory.Flat.Localization`; its full signature
  and docstring were read. It requires a Noetherian base and treats M = S,
  so is not the arbitrary-base, arbitrary-finitely-presented-module statement.
  Other results concern fibre dimensions, perfect loci, or citations of this node.
- Exact-name rg in Mathlib, the source project, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no existing
  `isOpen_setOf_flat_localizedModule` declaration.

The declaration docstring reproduces all four proof steps of the node, including
Noetherian approximation, eventual flatness after prime localization, the
Noetherian neighborhood, and base change/localization of that neighborhood.
There is no statement dispute or correction.

Validation: scompile.py compiled the module on the server in 1.4 seconds,
exit code 0, without errors or warnings. The delivery dry run is the final check;
the independent second reader will supply their own reading before delivery.

## Second reading by K1

I independently read the item's node copy, `OpenFlatLocus.lean`, all four
statement-dependency nodes and the declarations they record, and the relevant
Mathlib definitions. The local Stacks checkout is absent. I read the actual
`algebra.tex` at
https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex,
label `theorem-openness-flatness`, and its chapter conventions, as well as
https://stacks.math.columbia.edu/tag/00RC. The conventions say rings are
commutative with 1 and explicitly include the zero ring. Neither the theorem
nor the surrounding section assumes Noetherianity throughout.

Object/hypothesis/conclusion checklist, in the node's order:

1. Arbitrary commutative rings R and S: `{R : Type u} {S : Type v}`,
   `[CommRing R] [CommRing S]`. PASS, including zero rings.
2. A ring homomorphism phi from R to S: `[Algebra R S]` represents
   `algebraMap R S`. PASS: an arbitrary unital ring homomorphism gives an
   algebra via `RingHom.toAlgebra`; injectivity is not required.
3. Finite presentation of phi: `[Algebra.FinitePresentation R S]`. PASS.
   I read its class in `Mathlib.RingTheory.FinitePresentation`: a surjective
   map from `MvPolynomial (Fin n) R` with finitely generated kernel, exactly
   the presentation in `def-weil-pbc-finitely-presented-algebra`.
4. An S-module M: `{M : Type w} [AddCommGroup M] [Module S M]`. PASS.
5. A finite free presentation of M with s,t >= 0:
   `[Module.FinitePresentation S M]`. PASS: I read the class and
   `Module.FinitePresentation.exists_fin'` in
   `Mathlib.Algebra.Module.FinitePresentation`; the latter gives a surjection
   from a finite free module and a map from another finite free module whose
   image is its kernel. This is precisely the stated cokernel condition,
   with no selected presentation required.
6. The R-action on M is restriction along phi: `[Module R M]` and
   `[IsScalarTower R S M]`. PASS: the scalar-tower identity at `1 : S`
   forces `r • m = (algebraMap R S r) • m`. Conversely the restricted action
   always supplies this tower. These binders add no mathematical assumption.
7. All prime ideals q of S: `q : PrimeSpectrum S` in the set comprehension.
   PASS: its `asIdeal` carries the prime instance; no point is excluded.
8. Localization M_q at S minus q:
   `LocalizedModule q.asIdeal.primeCompl M`. PASS: I read `LocalizedModule`
   and `mk_eq` in `Mathlib.Algebra.Module.LocalizedModule.Basic`, giving the
   fraction construction and the expected equality after multiplication by
   a denominator. The dependency's recorded `Localization.AtPrime` uses the
   same prime complement and explicitly records this module localization.
9. The localized module's R-action is also restricted along phi. PASS:
   `LocalizedModule.smul'_mk` acts on the numerator and keeps its denominator,
   using the compatible action from item 6.
10. Flatness is over R, not S or a residue field:
    `Module.Flat R (LocalizedModule q.asIdeal.primeCompl M)`. PASS. I read
    `Module.Flat` and its tensor-injectivity equivalences in
    `Mathlib.RingTheory.Flat.Basic`, and `RingHom.Flat` in the dependency's
    recorded module. This uses the dependency's module clause; the ring-map
    clause is not the conclusion here. Tensor symmetry identifies Mathlib's
    left-tensor formulation with the node's right-tensor formulation, and
    the equivalences support arbitrary module universes.
11. Exactly the flat primes form the asserted set:
    `{q : PrimeSpectrum S | Module.Flat R (LocalizedModule q.asIdeal.primeCompl M)}`.
    PASS: no neighborhood, implication, or existentially smaller set is used.
12. That set is open in the Zariski topology: `IsOpen` of item 11. PASS.
    I read `PrimeSpectrum.zariskiTopology`, defined by zero loci, and
    `AlgebraicGeometry.Spec` / `Spec.map` in the dependency module.
    The underlying topological space is this spectrum; zero loci of subsets
    equal zero loci of their generated ideals, hence the closed sets are V(J).
    No scheme data beyond that underlying topology is needed.

All ring and module quantifiers precede the conclusion; the prime quantifier
is inside the set exactly as in the node. Universes u,v,w are separately
bound, with no independent undersized test-module universe. There are no
Noetherian, field, characteristic, domain, nontriviality, rank or finite-base
hypotheses. For S the zero ring the spectrum is empty and the conclusion is
openness of the empty set. If R is zero, any unital R-algebra S is zero, also
covered. For M zero every localization is flat and the set is the whole
spectrum. The two presentation ranks may be zero (including no generators
or no relations). The identity map recovers the ordinary flat locus over S.
There is no index-set or scheme nonemptiness binder to exclude empty cases.

Independent searches, using different wording from the first reader:

- LeanFinder via msearch.py: "Relative flatness of a finite presentation module
  at primes gives a Zariski open subset without noetherian assumptions".
  Eight hits: local flatness criteria, free-locus results, ring-map locality,
  and smooth flatness; none states this relative open locus.
- Loogle via msearch.py: `"isOpen", "Flat"`. Four geometric hits about open
  immersions and descent; none is this theorem.
- LeanSearch via msearch.py: "The primes q of S for which localization of a
  finitely presented S module is flat over R form an open set when S is
  finitely presented over R". The service returned Internal Server Error;
  this is unavailability, not evidence of absence.
- `rg` on Mathlib, the entire source `WeilConjectures`, and project `lean/Sheaf`
  for `flat.*[Ll]ocus|[Ll]ocus.*flat|[Oo]pen.*flat|isOpen_setOf_flat|isOpen.*Flat`.
  I opened `Module.Flat.exists_notMem_forall_flat_localizedModule` and
  `PrimeSpectrum.isOpen_setOf_flat_localization` in the source extension
  `WeilConjectures.Mathlib.RingTheory.Flat.Localization`: both require a
  Noetherian base; the latter additionally specializes M to S. I also read
  `isOpen_setOf_flat_localization_tensorProduct` in the source's residue-field
  fibre extension: it concerns finite-type models over a Noetherian ring,
  not this general statement. Other matches concern geometric open maps,
  free loci, cohomology, or citations of this item.
- Exact-name `rg` for `isOpen_setOf_flat_localizedModule` on the three Lean
  trees and `dag/lean_names_upstream.json` returned no match. No usable
  existing declaration replaces this module, and no notion is privately
  redefined. The finite-presentation predicate for modules already exists
  in Mathlib and needs no new definition node.

There are no new nodes or dependency modules in this delivery, and no
statement correction or `statement_change`. No mismatch was found: the Lean
module and node record remain unchanged. I checked all four proof steps
against the node: finite-type integer approximation and local transitions;
localized colimits and eventual flatness; the Noetherian neighborhood;
base change and further localization producing the basic-open cover. Each
step and its cited dependencies appear in the declaration docstring. Both
source and blueprint tags are present. The only declaration is a theorem
with proof `by sorry`; there are no hollow definitions or proved helpers.
Imports supply the four notions used, namespace and topic follow conventions,
and every line is at most 100 characters. All variables and universes are
explicitly bound. A direct comparison confirms `lean.statement` equals the
file signature verbatim, before `:=`.

Validation: independent scompile.py server compilation of
`lean/Sheaf/RingTheory/OpenFlatLocus.lean` returned exit code 0 in 1.4 seconds,
with no errors or warnings. Delivery preflight is run after this report.
