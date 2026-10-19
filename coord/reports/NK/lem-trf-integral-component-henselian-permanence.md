## Worker report

The delivery adds `Sheaf.RingTheory.IntegralComponentHenselianPermanence` and its one
statement `HenselianLocalRing.integral_component_henselian_permanence`. Its proof is
`sorry`; no definitions or proofs are added. The item's JSON differs only in `lean`.
The previous attempt's unchanged-node preflight failure is repaired by supplying the
missing Lean module and its corresponding `lean` binding, rather than redelivering the
already-reviewed stage-1 split.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The commutative rings are `(R : Type u) (S : Type v) [CommRing R] [CommRing S]`.
  The universes are explicit and independent.
- Henselian locality of the base is `[HenselianLocalRing R]`. This includes locality;
  there is no separate restriction on R.
- The structural R-algebra is `[Algebra R S]`, with structural map `algebraMap R S`.
- Nonzeroness of S is `[Nontrivial S]`.
- Integrality of every element over R is `[Algebra.IsIntegral R S]`, the usual monic
  annihilating-polynomial condition for this structural map. Injectivity is not assumed.
- The only-idempotents hypothesis is
  `hconnected : ∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1`.
  `IsIdempotentElem e` is exactly `e * e = e`.
- Henselian locality of S is the first existential witness
  `∃ (_ : HenselianLocalRing S), ...`. It is a conclusion, not a premise.
- Locality of R → S is the second existential witness
  `∃ (_ : IsLocalHom (algebraMap R S)), ...`. This is unit reflection, equivalent
  for local rings to contraction of maximal ideals.
- The residue extension is
  `@Algebra.IsAlgebraic (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
    _ _ (IsLocalRing.ResidueField.map (algebraMap R S)).toAlgebra`.
  In particular this uses the canonical quotient map induced by the structural map,
  with its canonical algebra structure; no arbitrary residue embedding is quantified.
  `ResidueField.map` needs precisely the preceding local-ring and local-map witnesses.
  `Algebra.IsAlgebraic` means every residue element satisfies `IsAlgebraic`.
- Strict henselian permanence is the final implication
  `IsStrictlyHenselianLocalRing R → IsStrictlyHenselianLocalRing S`.
  It is conditional, so henselian bases without separably closed residue fields remain covered.
- There are no module-finiteness, reducedness, domain, characteristic, or cardinality
  assumptions on S. The seven-step proof in the docstring matches all steps of the node.

Dependency declarations read and used:

- `def-weil-pbc-henselian-terminology`: the recorded module
  `WeilConjectures.Mathlib.RingTheory.Henselian` supplies
  `IsStrictlyHenselianLocalRing` (extending `HenselianLocalRing` with separably closed
  residue field) and imports Mathlib's `HenselianRing` and `HenselianLocalRing`.
  The latter extends `IsLocalRing` and states simple-root lifting, as specified by
  the dependency's equivalence note. The upstream declaration and docstring were read.
- `def-weil-algebraic-element`: `Mathlib.RingTheory.Algebraic.Defs.IsAlgebraic`
  (global declaration `IsAlgebraic`) and `Algebra.IsAlgebraic`; the latter's field is
  `∀ x, IsAlgebraic R x`. The recorded signatures and their source docstrings were read.

Proof dependencies whose modules are already available are imported without `public`:
`Algebra.finite_adjoin_of_finite_of_isIntegral` from
`Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic`;
`HenselianLocalRing.finite_over_henselian_exists_algEquiv_pi` from the recorded
`WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct` (read through
`scompile.py --source`, since absent in the older checkout);
`Ideal.isMaximal_comap_of_isIntegral_of_isMaximal'` from
`Mathlib.RingTheory.Ideal.GoingUp`;
`CategoryTheory.Limits.colimit` and related universal-property API from
`Mathlib.CategoryTheory.Limits.HasLimits`;
`filteredColimit_henselianPair` from `Sheaf.RingTheory.FilteredColimitHenselianPair`;
`Algebra.IsAlgebraic.isSepClosed` from `Mathlib.FieldTheory.PurelyInseparable.Basic`;
`Polynomial.Separable` from `Mathlib.FieldTheory.Separable`;
and `IsSepClosed` from `Mathlib.FieldTheory.IsSepClosed`.
No dependency interface needs repair, no new node is needed, and no import cycle is introduced.

Source reading: opened the Hübner--Schmidt paper
<https://www.mathi.uni-heidelberg.de/~schmidt/papers/algebraic_tame_site.pdf>, printed
p. 12, the paragraph before Theorem 6.3 citing Artin Proposition 3.3. It asserts integral
permanence of quasi-acyclic rings. The node's connected specialization and strict-residue
consequence were checked against the supplied proof and local Stacks `more-algebra.tex`,
`lemma-integral-over-henselian` (092X) and `lemma-integral-over-henselian-pair` (09XK).
092X states only the domain case; the node's proof replaces that restriction with the
zero-one-idempotent argument in each finite subalgebra. This is mathematically valid.

Edge cases checked: the zero algebra is excluded exactly by Nontrivial; S = R is included;
a product of two nonzero integral factors fails precisely the idempotent hypothesis;
nilpotents and non-domain connected finite algebras remain included; an infinite algebraic
field extension over a field is included, so no finite-degree bound has slipped in;
a noninjective structure map, such as a quotient of a henselian local ring, remains included;
positive and mixed characteristic and independent ring universes are unrestricted.
No statement dispute or correction is necessary.

Searches for reuse (all prescribed search wrappers run with group NK and this item):

- LeanSearch: `A connected integral algebra over a henselian local ring is henselian local`.
  Eight hits include `HenselianLocalRing.TFAE`, `HenselianLocalRing`,
  `instHenselianRingMaximalIdeal`, `Field.henselian` and `IsAdicComplete.henselianRing`.
  These are root-lifting definitions/criteria or special instances; no matching permanence statement.
- Loogle: `HenselianLocalRing, Algebra.IsIntegral, IsLocalHom`: zero hits.
- LeanFinder: queried the full connected integral-algebra permanence statement, and
  `connected integral algebra over henselian local ring is henselian local`; results
  were checked against the root-lifting API, not treated as an exact-match theorem.
- Mathlib grep through `msearch.py`: expression
  `HenselianLocalRing.*[Ii]ntegral|[Ii]ntegral.*[Hh]enselian|[Hh]enselian.*[Cc]onnected`
  in `RingTheory`: zero hits.
- Direct `rg` of the upstream project, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  by the item id and connected/integral/henselian names: no declaration of the full item.
  A relevant upstream candidate is
  `IsLocalRing.of_henselianLocalRing_of_isIntegral_of_isDomain` in
  `WeilConjectures.RingTheory.ProEtale.IntegralLocal`. Its signature and docstring
  were read: it assumes `[IsDomain S]` and concludes only locality, so it does not match.
  `Sheaf.RingTheory.IntegralOverHenselianPair.henselianRing_of_isIntegral` concerns a
  henselian ideal pair and also does not state this node's locality/residue conclusions.
  Existing henselian and algebraic definitions are reused directly.

Validation: every delivered Lean file is checked separately using the prescribed
`scompile.py` wrapper; the delivery dry run checks the packet and compiles again.

## Second reading by NK

Independent maintainer second reading, 2026-10-18, of immutable delivery
7df243d5a06a8fc119b06531f115bb94215ead55. This reading was performed with the
snapshot node, both statement dependencies, report and delivered module open.
The original placeholder under this heading is replaced by this actual reading.

The statement is correct, clause by clause:

- `R : Type u`, `S : Type v`, `[CommRing R]`, `[CommRing S]` give exactly the
  commutative rings, with explicitly bound, independent universes.
- `[HenselianLocalRing R]` includes locality and simple-root lifting. Mathlib's
  `Henselian.lean:94-111` and the upstream Henselian module's terminology paragraph
  identify this with the maximal-ideal henselian-pair notion. Stacks 09XI(3) and
  04GF justify the dependency's equivalent idempotent wording.
- `[Algebra R S]` specifies the structural map. `[Nontrivial S]` is exactly
  nonzeroness; `[Algebra.IsIntegral R S]` means every element satisfies a monic
  equation via that map. Neither injectivity nor finiteness is assumed.
- `hconnected` quantifies over every element, and `IsIdempotentElem e` is literally
  `e * e = e`. Its conclusion is precisely the zero-one idempotent condition.
- The first existential supplies `HenselianLocalRing S`, rather than assuming it.
  The second supplies `IsLocalHom (algebraMap R S)`, unit reflection, equivalent
  here to contraction of the unique maximal ideal.
- The algebraicity conjunct uses exactly
  `(IsLocalRing.ResidueField.map (algebraMap R S)).toAlgebra`.
  `ResidueField/Basic.lean:94-102` constructs this by quotienting the structural
  map; it uses the preceding existential local-ring/local-map witnesses. There
  is no arbitrary residue-field embedding. `IsAlgebraic` and
  `Algebra.IsAlgebraic` in `Algebraic/Defs.lean:45-69` are exactly the dependency's
  nonzero-polynomial condition and its universal quantification over elements.
- The final implication is conditional strict henselian permanence.
  `WeilConjectures.Mathlib.RingTheory.Henselian:121-135` defines the reused class
  by henselian locality and separably closed residue field. It adds no premise
  to the unconditional conclusion.

Sources read: Huebner--Schmidt, *The tame site of a scheme*, printed p. 12,
paragraph immediately before Theorem 6.3 (Artin Proposition 3.3); local Stacks
`more-algebra.tex:2752-2762` (09XK), `2884-2917` (0FWT), `30756-30787` (092X),
`algebra.tex:42074-42090` (04GF), `42384-42418` (04GH), and `42925-42959` (04GI).
Also read Stacks 09XI's finite-algebra idempotent characterization and
`fields.tex:608-614` (09GC). The paper states integral permanence of
quasi-acyclic rings; 092X itself has a domain hypothesis. The node correctly
supplies a connected-case argument rather than claiming that 092X already
states the full theorem.

The seven proof steps are faithfully present in the theorem docstring:

1. Finite generated subalgebras form a nonempty directed union and inherit
   nonzeroness and the idempotent condition. The finite-generators dependency
   gives module finiteness; its exact Mathlib declaration was checked.
2. The finite product dependency gives henselian local factors, local maps and
   finite residue extensions. Its actual published signature was read using
   `scompile.py --source WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct`.
   The empty product is excluded; two nonzero factors give a forbidden coordinate
   idempotent, leaving one factor. No domain assumption is used.
3. Integrality of transitions follows by viewing the same monic equations over
   the larger coefficient ring. The maximal-contraction dependency applies and
   gives local transitions and injective residue maps.
4. The elementary directed-union argument proves the union ideal is exactly
   the nonunits. An inverse in the union would already occur at a common stage.
   This proves locality and maximal-ideal contraction, including for a
   noninjective structural map (contraction means preimage).
5. The displayed stagewise universal-property argument gives the ring colimit;
   the filtered-colimit henselian-pair theorem applies to compatible stage
   maximal ideals. Its exact declaration in `FilteredColimitHenselianPair.lean`
   was read. Its common index/object universe can be met by lifting the diagram;
   it requires no equality of the theorem's independent ring universes.
6. Reducing a monic equation proves residue algebraicity. The residue base is
   a field, so a monic polynomial is nonzero. The union of the stage residues
   really is the residue field since each contraction is the stage maximal ideal.
7. The finite-extension separable-closure dependency applies to every stage.
   Finitely many polynomial and Bezout coefficients descend to one stage;
   injectivity descends the identity and nonconstancy, and its root maps back.
   The exact `Algebra.IsAlgebraic.isSepClosed`, `Polynomial.Separable`, and
   `IsSepClosed` declarations were inspected.

Edge cases checked: zero S is excluded exactly as in the node; zero R cannot
map unitaly to nonzero S; S = R is allowed; disconnected products are excluded
by their coordinate idempotents; connected rings with nilpotents or zero
divisors remain covered (for example k[epsilon]/epsilon^2). Proper nonzero
quotients allow noninjective structural maps. Infinite algebraic field
extensions and infinite directed unions remain covered. No characteristic,
Noetherian, reducedness, finite-degree or domain restriction is present.

Reuse searches: checked the worker's LeanSearch, Loogle/LeanFinder and grep
records, then independently searched Mathlib, `WeilConjectures`, `lean/Sheaf`
and `dag/lean_names_upstream.json` using henselian/integral, connected and
idempotent terminology. The upstream
`IsLocalRing.of_henselianLocalRing_of_isIntegral_of_isDomain` has `[IsDomain S]`
and concludes only locality; it is not this theorem. The existing
`henselianRing_of_isIntegral` is about an extended ideal pair, not the full
locality/residue statement. No exact duplicate was found. The existing notions
are reused without private copies, new definitions or missing helper interfaces.

Pilot checks: one delivered Lean file, one theorem, proof exactly `by sorry`;
no hollow definition or additional local proof. Source-place and blueprint
module/theorem docstrings are present, including all seven steps. All lines
are at most 100 characters. The `lean.statement` string equals the source
signature verbatim, from `theorem` through the conclusion before `:= by`.
Imports are the statement's notions and the recorded proof plan. No source
statement correction or citer audit is needed. No pro-etale substitute or
infinity/dg/model-category machinery is introduced. Direct statement and proof
dependencies have empty intersection with `coord/route-pivot-dropped.txt`;
no item repair note exists at the checked shared ref.

Compiler evidence: On 2026-10-18 ran exactly
`python3 /home/ubuntu/weil-launcher-nt/scompile.py NK lem-trf-integral-component-henselian-permanence snapshot/lean/Sheaf/RingTheory/IntegralComponentHenselianPermanence.lean`.
Exit code 0, no errors or warnings. The wrapper reported
`sandbox Sheaf/Stage2/Sandbox0.lean` with modules in a private `.lbuild`
overlay (110.8 seconds including preparation/dependency work), then
`library Sheaf/RingTheory/IntegralComponentHenselianPermanence.lean [6.3 s]`.
It advertised the unchanged 60-second per-file limit after slot acquisition.
The installed wrapper is the 2026-10-17 server-overlay variant, rather than
the older locally hosted wrapper described in the brief; both checks were
obtained through the prescribed scompile.py entry point. The original
report promised per-file validation but contained no concrete compiler
transcript; this independent reproduction supplies the evidence. The fix
changes only Markdown, so no further Lean compilation is necessary.

Finding repaired: H11 (and the real-reading requirement of H1), the original
`## Second reading by NK` contained only a no-reading notice. This complete
replacement report preserves the worker section and supplies the independent
reading. No Lean module or node record requires a change.
