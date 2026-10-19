## Worker report

The item is an exact existing-statement match for
`RingHom.exists_retraction_of_wlocal_geometric_criterion` in
`Sheaf.RingTheory.WContractibleGeometricCriterion`, at
`lean/Sheaf/RingTheory/WContractibleGeometricCriterion.lean:60`.
The only delivered change to the item is its `lean` record, with `existing: true`.
There is no new module, definition, postponed theorem, or statement correction.
The existing declaration is currently a theorem with `sorry`; this attachment records
its statement, not a completed proof. Its full signature and docstring were read both
in the shared checkout and using `scompile.py --source` against the published sources.
No repair note exists for this item.

Source checked: main-20261015, sec-proetale-coefficients,
sk-thm-pe-weakly-contractible-basis, `det-pe-wcb-split-cover.md` and its companion
`.proof.md`. The node and blueprint statement agree word for word. The theorem's
source is Stacks Tag 0982, implication (3) to (1). Its proof docstring supplies a
refinement/retraction proof; reusing an already stated equivalent theorem does not
change the item's recorded refinement–faithful-flat composition–retraction route.

Hypothesis and conclusion correspondence:

- “D a ring” is `{R : Type u} [CommRing R]`; “E a ring” is
  `{B : Type v} [CommRing B]`. The rings have independent explicit universes.
- “D w-contractible” is exactly the three displayed hypotheses
  `[IsWLocalRing R]`,
  `[ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum R))]`, and
  `hstrict : ∀ (m : Ideal R) [m.IsMaximal],
  IsStrictlyHenselianLocalRing (Localization.AtPrime m)`.
  These are precisely the fields of the dependency's recorded
  `IsWContractibleRing`: it extends `IsWStrictlyLocalRing`, which extends
  `IsWLocalRing` and adds `isStrictlyHenselianLocalRing_localization`; its remaining
  field is `extremallyDisconnected_connectedComponents`. Conversely those three
  hypotheses assemble that same class, so the expanded interface adds or drops no
  mathematical hypothesis.
- “D → E” is the arbitrary unital ring homomorphism `f : R →+* B`.
  Its induced algebra is `f.toAlgebra`, as in both recorded ring-map predicates.
- “faithfully flat” is `hfaithful : f.FaithfullyFlat`, Mathlib's
  `RingHom.FaithfullyFlat`, equivalent to the recorded tensor exactness criterion.
- “weakly étale” is `hweak : f.WeaklyEtale`, the existing ring-map wrapper for
  `Algebra.WeaklyEtale R B` under `f.toAlgebra`. That class says flatness of B
  over R and of tensor multiplication; it is the weakly étale clause exposed by
  the recorded ind-étale dependency, not a replacement by the stronger ind-étale
  hypothesis.
- “there is a D-algebra map E → D” is
  `∃ r : B →+* R, r.comp f = RingHom.id R`.
  In detail, the equation says `r (f a) = a` for every a, which is exactly the
  `AlgHom.commutes'` condition for the target's self-algebra. Conversely a
  D-algebra map has this ring-hom identity. Thus the conclusion asserts precisely
  the desired algebra map, rather than an arbitrary ring map.
- “i.e. Spec E → Spec D has a section” is the same identity under contravariant
  Spec: the candidate section is Spec(r), and the composite with Spec(f) is
  Spec(r ∘ f) = identity. This is the explanatory equivalent clause, not a second
  independent conclusion.

Dependency declarations inspected and reused by the existing interface:

- `det-pe-wlocal-strict-contractible` records
  `WeilConjectures.RingTheory.ProEtale.WContractible.IsWContractibleRing`
  (the declaration is in the root namespace, `IsWContractibleRing`). Its
  superclass definitions `IsWLocalRing` and `IsWStrictlyLocalRing` are in
  `WeilConjectures.RingTheory.ProEtale.WLocal`. Read all three definitions and
  docstrings. The closed-points equivalent in the dependency does not add a
  separate hypothesis here.
- `def-weil-pbc-faithfully-flat-ring-map` records `Module.FaithfullyFlat` in
  `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic` and the ring-map declaration
  `RingHom.FaithfullyFlat` in `Mathlib.RingTheory.RingHom.FaithfullyFlat`.
  Read both definitions and `Module.FaithfullyFlat.iff_exact_iff_lTensor_exact`.
  The existing matched module publicly imports the ring-map module.
- `def-weil-pbc-ind-etale-algebra` records
  `Sheaf.RingTheory.IndPrincipalZariski` with `Algebra.IndEtale`,
  `Algebra.WeaklyEtale`, `AlgebraicGeometry.proAffineEtale_Spec_iff`, and
  `AlgebraicGeometry.weaklyEtale_SpecMap_algebraMap_iff` exposed by its imports.
  Read its full definition and module docstring and these existing signatures.
  `Algebra.WeaklyEtale` is in `Mathlib.RingTheory.Etale.Weakly`;
  `RingHom.WeaklyEtale` and `RingHom.weaklyEtale_algebraMap_iff` are in
  `WeilConjectures.RingTheory.ProEtale.WeaklyEtale`. The matched module publicly
  imports the recorded `Sheaf.RingTheory.IndPrincipalZariski`.

Edge cases checked:

- D = 0 is allowed: any unital algebra E over the zero ring is the zero ring,
  and the unique map back is a retraction. No Nontrivial binder excludes it.
- E = D, f = identity: the identity is the required algebra map; the hypotheses
  do not unnecessarily require a nonidentity extension.
- E = 0 with D nonzero is excluded by faithful flatness, as required; a map
  to zero alone cannot supply a retraction.
- For D a separably closed field and E = D^n, n ≥ 1 gives projection sections;
  the empty product n = 0 is excluded by faithful flatness when D is nonzero.
- No countability, finite-presentation, Noetherianity, characteristic, or same-
  universe restriction is imposed. Independent u and v were compiler checked.

Searches on 2026-10-17:

- `msearch.py leanfinder`, query “Every faithfully flat weakly etale algebra over
  a w-contractible commutative ring admits an algebra retraction”: eight hits on
  formally étale/étale algebras, including `RingHom.formallyEtale_algebraMap`,
  `Algebra.FormallyEtale.comp`, and `Algebra.Etale.exists_subalgebra_fg`; no
  w-contractible retraction theorem.
- `msearch.py loogle`, query `RingHom.FaithfullyFlat, Algebra.WeaklyEtale`:
  zero hits.
- `msearch.py leansearch`, query “A faithfully flat weakly etale algebra over a
  w-contractible ring has an algebra map back to that ring”: eight hits on
  faithful-flat descent and étale maps; no w-contractible retraction theorem.
- `msearch.py grep`, query `IsWContractible|WContractible|exists_retraction`
  in Mathlib/RingTheory: zero hits.
- `rg` of the source project's WeilConjectures tree for
  `exists_retraction_of_wlocal_geometric_criterion|class IsWContractibleRing|theorem
  IsWContractibleRing.exists_retraction`: found the class and upstream ind-étale
  retraction theorem. The latter, at WContractible.lean:717, was read and is
  insufficient by itself: it assumes ind-étale and one common universe.
- `rg` of `lean/Sheaf` for the same expressions found the exact existing
  theorem at WContractibleGeometricCriterion.lean:60. Broader retraction and
  WContractible searches also found the closed-component and stalk-isomorphism
  auxiliaries, which are narrower than this item.
- Direct source-tree search for `det-pe-wcb-split-cover`: no hits. The existing
  declaration is associated with the earlier equivalent node
  `lem-weil-pbc-wcontractible-geometric-criterion`, whose statement and Lean
  record were read. Reusing it follows the one-definition/statement rule.

Validation: `scompile.py Q83 det-pe-wcb-split-cover scratchpad/Consumer.lean`
passed both the local overlay and server confirmation without warnings.
The scratch-only `#check` applies the existing theorem directly to
`[IsWContractibleRing R]` by supplying exactly its superclass and two field
projections. Lean printed the type
`∀ {R : Type u} [CommRing R] [IsWContractibleRing R] {B : Type v} [CommRing B]
(f : R →+* B), f.FaithfullyFlat → f.WeaklyEtale →
∃ r, r.comp f = RingHom.id R`.
The scratch file is outside lean/ and is not delivered.
The required delivery dry run additionally checks the recorded existing name.

No disputed statement or node fault was found.

## Second reading by Q83

I independently read the item JSON, its blueprint statement and companion proof,
Stacks `proetale.tex:1854–1916` (Tags 0981 and 0982), all three statement-dependency
records, and the actual declarations described below. I also read the current
published theorem through `scompile.py --source
Sheaf.RingTheory.WContractibleGeometricCriterion`; it agrees with the shared
source. There is no repair note, statement correction, new node or dependency
module in this delivery.

The complete object/hypothesis/conclusion checklist is:

1. Arbitrary commutative ring D: `{R : Type u} [CommRing R]`. Pass. Stacks says
   “Let A be a ring” and imposes no standing field, characteristic, Noetherian,
   nonzero or finiteness hypothesis in this section.
2. D is w-contractible: `[IsWLocalRing R]`,
   `[ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum R))]`, and
   `hstrict : ∀ (m : Ideal R) [m.IsMaximal],
   IsStrictlyHenselianLocalRing (Localization.AtPrime m)`. Pass. I opened
   `WContractible.lean:40` and `WLocal.lean:30,151`: these are exactly the fields
   of the recorded `IsWContractibleRing`, including its inherited fields. In
   particular `IsWStrictlyLocalRing` adds strict henselianity at every maximal
   ideal to `IsWLocalRing`; `IsWContractibleRing` adds extremal disconnectedness
   of the quotient connected-component space. Conversely the three hypotheses
   construct that same class; none is extra. `WLocalSpace` in
   `Topology/SpectralSpace/WLocal/Basic.lean:29` says spectral, unique closed
   specialization, and closed closed-points. Prime spectra are spectral, and
   closed specializations are precisely maximal ideals containing the prime.
   The strict henselian class in `Mathlib/RingTheory/Henselian.lean:122` extends
   henselian local rings with separably closed residue field. These are the
   dependency's notions, with no private replacement. Stacks 0982 (3) to (1)
   states exactly the equivalence needed for this expanded interface.
3. Arbitrary commutative ring E and map D → E:
   `{B : Type v} [CommRing B] (f : R →+* B)`. Pass. The map is unital and is
   quantified after D and its properties. Independent u and v are explicitly
   bound; E is not required to be w-local, local, finitely presented or ind-etale.
4. D → E faithfully flat: `hfaithful : f.FaithfullyFlat`. Pass. I read
   `Mathlib/RingTheory/RingHom/FaithfullyFlat.lean:25`: this is
   `Module.FaithfullyFlat R B` with algebra structure `f.toAlgebra`. The module
   class and `Module.FaithfullyFlat.iff_exact_iff_lTensor_exact` in the recorded
   dependency's module identify it with that node's tensor exactness criterion.
5. D → E weakly etale: `hweak : f.WeaklyEtale`. Pass. I read the recorded
   `Sheaf.RingTheory.IndPrincipalZariski` module and its public imports, the
   wrapper in `ProEtale/WeaklyEtale.lean:238`, and Mathlib's
   `Algebra.WeaklyEtale` fields at `RingTheory/Etale/Weakly.lean:37`. They say
   flatness of B over R and of tensor multiplication B ⊗[R] B → B, using
   `f.toAlgebra`. The imported `weaklyEtale_SpecMap_algebraMap_iff` identifies
   this with weak etaleness on affine spectra. No ind-etale assumption was
   substituted for weak etaleness. The dependency's unrelated principal
   ind-Zariski definition is not used here.
6. Existence of a D-algebra map E → D:
   `∃ r : B →+* R, r.comp f = RingHom.id R`. Pass. The identity means
   `r (f a) = a` for every a, precisely the commutation equation for a
   D-algebra homomorphism into D with its self-algebra. This asserts existence,
   with no uniqueness, specified choice or extra condition on the retraction.
7. Equivalently Spec E → Spec D has a section: the same equation renders this
   clause. Pass. Contravariant Spec sends r to the section and sends r.comp f
   to the identity. This is an equivalent explanation in the node, not an
   additional independent conclusion. All quantifiers have the required order.

Edge cases: D = 0 is admitted; a unital map then forces E = 0 and the unique
map back is a retraction, covering the empty spectrum. If E = 0 and D is
nonzero, faithful flatness fails, as required. The identity map is allowed.
For a separably closed field D and E = D^n, positive n allows a projection;
the empty product n = 0 is excluded by faithful flatness unless D = 0. There
is no index-set, degree or characteristic binder to restrict. The maximal-ideal
condition is correctly vacuous for D = 0. Both ring universes remain arbitrary;
the consumer compile below confirms that no same-universe constraint is hidden.

Independent searches (different wording from the worker):

- `msearch.py ... leanfinder "A weakly etale cover of the spectrum of a weakly
  contractible ring has a section"`: eight hits on standard-etale
  presentations, etale loci, etale morphisms and etale descent; no exact match.
- `msearch.py ... leansearch "Every faithfully flat weakly etale ring
  homomorphism from a w-contractible ring admits a retraction"`: eight hits,
  including `RingHom.FaithfullyFlat`, its injectivity and composition, and flat
  retracts; none states this retraction result.
- Loogle `RingHom.WeaklyEtale, RingHom.FaithfullyFlat` cannot resolve the
  upstream-only WeaklyEtale identifier. The alternative Mathlib query
  `RingHom.FaithfullyFlat, RingHom, _ = RingHom.id _` succeeds with zero hits.
- Direct `rg` searches for `retraction`, `splits`, and combinations of weak/split
  in the source project's pro-etale ring modules and `lean/Sheaf/RingTheory`
  independently locate the exact existing geometric-criterion theorem. The
  upstream `IsWContractibleRing.exists_retraction` at WContractible.lean:717
  has the stronger ind-etale hypothesis and one common universe, so is not the
  chosen match. The other retraction results impose local-stalk or closed-point
  conditions. Mathlib/RingTheory search for retraction/etale combinations and
  w-contractibility has no matching result. I also checked the upstream-name
  table; it supplies no alternative exact match.

The existing module has a source-bearing module docstring and a full five-step
proof docstring for its owning node, `lem-weil-pbc-wcontractible-geometric-criterion`.
That proof first refines to an ind-etale algebra, composes faithful flatness,
then constructs a retraction and composes it back. The present item's four-step
route uses the already named ind-etale retraction theorem instead of repeating
its local-ring construction. Reusing the exact statement leaves both recorded
proof routes intact. H8 does not require editing an existing declaration's
owning blueprint tag to this item's id; H4 requires this reuse. The existing
proof is `sorry`; this delivery makes no claim that it has been proved, and
introduces no definition, hollow data, theorem or proof.

Validation: the recorded `lean.statement` was compared with the existing source
signature character for character and is equal. I reran
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q83 det-pe-wcb-split-cover
scratchpad/Consumer.lean` from the sandbox. Both sandbox and library consumer
checks pass cleanly, with explicit independent u and v, applying the existing
theorem to `[IsWContractibleRing R]` using exactly its field projections. The
scratch-only `#check` declares or proves nothing and is not delivered.

Mismatches found: none. Changes by this second reader: this review section only;
the existing attachment, signature, node statement and dependency lists are right
and are preserved.
