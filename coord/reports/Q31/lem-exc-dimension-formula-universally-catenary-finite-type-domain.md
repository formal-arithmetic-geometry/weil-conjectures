## Worker report

The module `Sheaf.RingTheory.UniversallyCatenaryDimensionFormula` states
`IsUniversallyCatenary.height_add_trdeg_residueField_eq`, with one postponed proof (`sorry`).
It is exactly the equality clause of Stacks Project, Algebra, Tag 02IJ,
`literature/stacks-project/algebra.tex`, lines 27520–27607. I read the source statement
and proof, the current item's nine proof steps, and each statement dependency's node
and recorded declaration, including its full definition and docstring. There is no
repair note for this item. No definitions or dependency repairs are needed.

Hypotheses and clauses, matched to the node:

- “R subset S, an inclusion of commutative domains”: independent universes `u v`,
  `{R : Type u} {S : Type v}`, `[CommRing R] [CommRing S]`, `[IsDomain R] [IsDomain S]`,
  `[Algebra R S]`, and `hinj : Function.Injective (algebraMap R S)`. Thus both rings are
  nonzero and have no zero divisors, as the node explicitly specifies. An injective
  algebra map is the general presentation of the inclusion; no literal subtype or
  common universe is imposed.
- “R Noetherian”: `[IsNoetherianRing R]`, exactly the dependency's abbreviation.
- “R universally catenary”: `hR : IsUniversallyCatenary R`, from the dependency's
  `Sheaf.RingTheory.ExcellentRing`, not the stronger `IsExcellent R`.
  Its quantified finite type algebras are in the universe of R, as recorded. An
  arbitrary finite type algebra in another universe has a small representative:
  the finite polynomial presentation supplies one. No equality `u = v` is imposed.
- “S finite type over R”: `[Algebra.FiniteType R S]`, the dependency's class asserting
  finite generation of the top subalgebra (equivalently a finite polynomial presentation).
- “p and q prime ideals”: `(p : Ideal R) (q : Ideal S) [p.IsPrime] [q.IsPrime]`.
- “q intersect R = p”: `hpq : p = q.comap (algebraMap R S)`, the contraction equality,
  with its orientation chosen to use Mathlib's canonical residue-field map.
- “kappa(r) = Frac(A/r)”: `p.ResidueField`, `q.ResidueField`. I read
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`: its `IsFractionRing (A ⧸ r)
  r.ResidueField` instance gives precisely the specified fraction field.
  The kappa(p)-algebra structure on kappa(q) is explicitly the one from
  `(Ideal.ResidueField.map p q (algebraMap R S) hpq).toAlgebra`; the map's docstring
  specifies the canonical embedding when p is the contraction. No arbitrary residue
  algebra structure is quantified or chosen.
- “height is the supremum of lengths of strict prime chains ending at the prime”:
  `q.height` and `p.height`, using `Mathlib.RingTheory.Ideal.Height`. Its definition
  is via minimal primes for general ideals; at a prime it equals order height in the
  prime spectrum (`PrimeSpectrum.height_eq_orderHeight`). Chains below a prime may
  be extended to end at it, so this is exactly the node's convention.
- “transcendence degree”: the recorded `Algebra.trdeg`, including explicit canonical
  residue algebra structure in the first occurrence. This is the cardinal supremum
  of algebraically independent subsets, not a newly defined dimension invariant.
- The equality is `q.height + Cardinal.toENat (Algebra.trdeg kappa(p) kappa(q)) =
  p.height + Cardinal.toENat (Algebra.trdeg R S)`, with the first algebra instance
  written explicitly via `@Algebra.trdeg`. `Cardinal.toENat` preserves finite natural
  cardinalities and addition. Both degrees here are finite: S is finite type over
  the domain R, and the residue-field extension is finitely generated as a field
  (reduce the algebra generators modulo q, then take fractions). Noetherianity gives
  finite height for each prime. Thus this is the numerical equality in the node,
  without loss from truncation or a change of statement. In particular, this does
  not use `Cardinal.toNat`, which would send infinite cardinals to zero.

Statement dependency declarations used:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`; its `isNoetherianRing_iff_ideal_fg` confirms the ideal formulation.
- `def-exc-excellent-ring`: `Sheaf.RingTheory.ExcellentRing`, `IsUniversallyCatenary`.
  I read its chain and saturated-chain definitions as well as `IsCatenaryRing`.
- `def-weil-pbc-finite-type-algebra`: `Mathlib.RingTheory.FiniteType`,
  `Algebra.FiniteType`.
- `def-kun-transcendence-degree`: `Mathlib.RingTheory.AlgebraicIndependent.Basic`,
  `Algebra.trdeg`.

Proof dependency imports follow stage 2 rule 7: the polynomial PID and principal
ideal domain modules, the simple-adjoin power basis module, transcendence basis and
its tower theorem, the polynomial-domain module, polynomial basics, flat-module
basics, finite-type Noetherianity, the flat height formula and going-down instance,
and `Sheaf.RingTheory.LocalizationPrimeResidueFieldIso` (whose theorem and proof
were read). These are private imports where used only in the future proof. All nine
current DAG proof steps are rendered in the theorem docstring, naming their nodes.

Edge cases checked against the statement and source:

- Zero rings are excluded precisely by the node's domain requirement, not by an
  extra hypothesis. The zero prime is allowed and maximal primes are not required.
- R = S: the residue map is the identity, the generic and residue degrees are zero,
  and the equality reduces to equality of heights.
- R a field and S = R[T]: q = 0 gives `0 + 1 = 0 + 1`; a nonzero prime gives
  `1 + 0 = 0 + 1`, in every characteristic.
- R = Z, S = Z[T], q = (2,T): `2 + 0 = 1 + 1`; q = (2): `1 + 1 = 1 + 1`.
- R = Z, S = Z[1/2], q = (3): `1 + 0 = 1 + 0`. Surjectivity and integrality
  are not imposed. The formula also covers q = 0 and transcendence degree zero.
- No finite global Krull dimension is assumed; Noetherian domains may have
  arbitrarily large prime heights while each individual height remains finite.
- The independent universes do not exclude a larger representation of a finite type
  algebra. The explicit residue-field map avoids an additional universe constraint.

Searches actually made (the service searches are in the Q31 msearch log):

- LeanFinder: `dimension formula for finite type extensions of universally catenary
  domains height transcendence degree`: 8 hits, including `lift_trdeg_add_eq`,
  algebraic fraction-ring rank lemmas, `trdeg_lt_aleph0`, and a polynomial dimension
  bound; none states the formula. The tower theorem is an existing proof dependency.
- Loogle: `"height", "Algebra.FiniteType"`: OK, zero hits.
- Mathlib grep via msearch, RingTheory: `height.*trdeg|trdeg.*height|catenary|dimension.formula`:
  OK, zero hits.
- LeanSearch: `finite type domain dimension formula universally catenary height`:
  8 hits, concerning supremum of prime heights and dimension bounds; no formula.
- Direct rg of upstream `WeilConjectures` and project `lean/Sheaf` for
  `dimension.formula|height.*trdeg|trdeg.*height|IsUniversallyCatenary`: the project
  supplies excellence and normalization-dimension statements, and unrelated
  geometric dimension formulas; none is the general ring formula. The upstream
  node-id search returned no match. The new declaration name was also searched in
  the upstream name index, upstream Lean and project Lean: no match.
- Mathlib sources were searched for canonical residue-field maps, `toENat`, and
  finite transcendence degree; the existing definitions above suffice.

Validation: the prescribed `scompile.py` compiled the new file cleanly in both its
sandbox and library-path checks, with explicit `autoImplicit false` and independently
bound universes and types. No theorem is proved. No statement is disputed or corrected.
The previous worker's preflight problem is being checked with the unchanged current
Q37 split retained; no stage-1-owned field is altered in the sandbox node.


## Second reading by Q31

I am the independent second reader, not the statement author. I read the sandbox
node and module, the current repository node, all four statement-dependency nodes
and their recorded declaration sources, the nine proof steps, and Stacks Algebra
`algebra.tex`, lines 27510–27607 (Tag 02IJ). The preceding section only recalls
catenarity; it imposes no additional standing hypotheses. Tag 02IJ assumes a
Noetherian base, a finite type injective map, and two domains. Its final equality
clause additionally assumes universal catenarity, exactly as this node does. I
also read Definitions 00NI and 00NL at lines 25462–25500 to check the imported
predicate. There is no repair note for this item.

Here is my independent list of every object, hypothesis and conclusion clause,
with its Lean rendering and verdict:

| Node item | Lean rendering and verdict |
| --- | --- |
| Two commutative rings R and S, with no size equality specified | `{R : Type u} {S : Type v} [CommRing R] [CommRing S]`; PASS, separately bound universes. |
| Both are nonzero domains | `[IsDomain R] [IsDomain S]`; PASS, includes nontriviality and absence of zero divisors. |
| R is included in S as an R-algebra | `[Algebra R S]` and `hinj : Function.Injective (algebraMap R S)`; PASS, a faithful presentation of the inclusion, without a subtype restriction. |
| R is Noetherian | `[IsNoetherianRing R]`; PASS, the recorded Mathlib abbreviation, with `isNoetherianRing_iff_ideal_fg` giving the node's ideal formulation. |
| R is universally catenary | `hR : IsUniversallyCatenary R`; PASS, the exact recorded declaration from `Sheaf.RingTheory.ExcellentRing`, rather than excellence or regularity. |
| S is finite type over R | `[Algebra.FiniteType R S]`; PASS, the recorded finite generation of the top subalgebra, equivalent to the finite polynomial presentation in the node. |
| Arbitrary primes p in R and q in S | `(p : Ideal R) (q : Ideal S) [p.IsPrime] [q.IsPrime]`; PASS, neither prime is required maximal or nonzero. |
| q contracts to p | `hpq : p = q.comap (algebraMap R S)`; PASS, exactly contraction with a harmless equality orientation. |
| kappa(p) and kappa(q) are fraction fields of the prime quotients | `p.ResidueField`, `q.ResidueField`; PASS, the source of `Mathlib.RingTheory.LocalRing.ResidueField.Ideal` supplies `IsFractionRing (A ⧸ r) r.ResidueField`. |
| The extension kappa(p) to kappa(q) is induced by the given inclusion | `(Ideal.ResidueField.map p q (algebraMap R S) hpq).toAlgebra`; PASS. I read the map's construction through `Localization.localRingHom` and its `map_algebraMap` compatibility lemma. No arbitrary field embedding is supplied as a hypothesis. |
| Heights are suprema of strict prime-chain lengths ending at each prime | `q.height` and `p.height`; PASS. Although general ideal height is an infimum over minimal primes, `PrimeSpectrum.height_eq_orderHeight` identifies it with precisely the required order height at primes. |
| Transcendence degrees are the recorded algebraic-independence invariant | `Algebra.trdeg R S` and explicitly instantiated `@Algebra.trdeg p.ResidueField q.ResidueField ...`; PASS. I read its defining supremum in `Mathlib.RingTheory.AlgebraicIndependent.Basic`. |
| The single conclusion is ht(q) + trdeg(kappa(q)/kappa(p)) = ht(p) + trdeg(S/R) | The final displayed equality, with both transcendence degrees passed through `Cardinal.toENat`; PASS, in the same order with every summand present. |

The last representation deserves an explicit check. `Cardinal.toENat` is an
order-preserving additive map that sends a natural cardinal to that natural in
`ℕ∞`. The generic degree is finite by finite type (Mathlib's
`trdeg_lt_aleph0_of_finiteType`, whose signature I read). For the residue degree,
choose finitely many R-algebra generators of S. Their images generate S/q over
R/p. Taking fractions identifies the residue field as a field generated over
Frac(R/p) by those finitely many images, so its transcendence degree is finite
as well. Noetherianity passes to S and forces each individual prime height to be
finite. Thus all four values are natural numbers in this situation; no infinite
cardinal information is lost, and this equality is equivalent to the numerical
formula in the node and source. No global finite-dimensionality assumption is
needed.

I opened `Sheaf.RingTheory.ExcellentRing` and checked all of `IsPrimeChain`,
`IsSaturatedPrimeChain`, `IsCatenaryRing`, and `IsUniversallyCatenary`. Chains
have n+1 entries with n strict inclusions, fixed endpoints and prime entries;
saturation excludes a prime strictly between adjacent entries. The predicate
has the common finite chain bound and equality of saturated chain lengths in
00NI, and universal catenarity includes Noetherianity and all finite type
algebras as in 00NL. Repeating the Noetherian condition as an instance in the
item introduces no stronger mathematical hypothesis and matches the explicit
node. Quantifying algebras in the base universe does not exclude larger
representations: a finite type algebra is isomorphic to a quotient of a finite
polynomial algebra on R, which lives in that universe. Catenarity is invariant
under that ring isomorphism. The item's independent `u v` therefore remain
appropriate, with no hidden equality imposed by the residue-field map.

Edge cases: R = S and zero algebra generators give identity residue extensions
and zero degrees; q = p = 0 is allowed and gives the generic-degree identity.
A field base and S = R[T] give 0+1=0+1 at q=0 and 1+0=0+1 at a nonzero prime.
The localization example Z into Z[1/2] is included, so surjectivity, integrality
and module finiteness are not extra hypotheses. Degree zero and height zero
are allowed. The rings of any characteristic are admitted. Zero rings are
excluded exactly because the node explicitly requires nonzero domains. There
are no scheme, complex or arbitrary index-set parameters to exclude an empty
case. Finite chain length zero is handled by the imported chain definition.
No universe or variable is unbound.

Independent searches (different queries from the first reader; service calls
are logged by msearch):

- LeanFinder: `height of prime finite type algebra dimension formula catenary
  transcendence residue fields`; eight hits. The closest is
  `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`, whose actual source
  signature I opened: it concerns height of the quotient prime for a
  going-down map, so is a proof input and not this statement.
- Loogle: `"height", "ResidueField"`; zero hits.
- LeanSearch: `altitude formula universally catenary Noetherian ring prime
  ideal residue transcendence degree`; eight hits, including height bounds,
  localization height, `Algebra.trdeg`, and a finite-type transcendence-degree
  bound. None states Tag 02IJ's equality.
- Direct rg in Mathlib/RingTheory, upstream WeilConjectures, and project
  lean/Sheaf: `height.*trdeg|trdeg.*height|catenary|[Dd]imension.?[Ff]ormula`.
  Mathlib and upstream have no match for this general formula. Project matches
  include the excellent-ring definition, geometric formulas over a field and
  `NormalizationLocalizationDimension`, whose declaration I opened: its
  finite birational local specialization is narrower and cites this node.
- Direct rg in the upstream name index, upstream WeilConjectures and project
  lean/Sheaf for the proposed declaration name and universal-catenary
  finite-type dimension-formula name: no duplicate declaration.

I also checked the proof-dependency records and the actual signatures for the
PID/power-basis statements, field/domain transcendence tower identity, flat
height formula, and the project's localization prime/residue-field theorem.
They support the nine-step proof plan and their available modules are imported.
The theorem docstring follows all nine current node steps, including the
one-generator polynomial/quotient split, saturated-chain cancellation, and
induction on generators. No new definition node or dependency repair module
is present or necessary, so H12/H13 introduce no extra review obligations.

No mathematical, signature, dependency, or convention mismatch was found. I
left the Lean module and node unchanged and appended this independent review.
The node differs from the current shared node only in its permitted `lean`
record; there is no statement correction or citer-verdict audit to validate.
The recorded `lean.statement` is character-for-character equal to the signature
in the module. The file has one named theorem with whole proof `sorry`, no new
definitions, no local notation or private auxiliaries, no proof of a theorem,
and no line over 100 characters. Source/blueprint docstrings and the namespace
follow the project convention.

Validation: I reran the prescribed `scompile.py` on the exact delivered module.
Both sandbox and library-path checks completed cleanly (1.6 s and 1.9 s), with
no diagnostics. An initial invocation used the read-only repository as the
working directory with a relative sandbox path and was immediately corrected
to the absolute sandbox path; it compiled no live source.
