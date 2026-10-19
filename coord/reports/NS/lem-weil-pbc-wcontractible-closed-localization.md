## Worker report

The module `Sheaf.RingTheory.WContractibleClosedLocalization` states
`IsLocalization.wcontractible_closed_localization`, with `sorry`, and supplies the real
finite-family construction `IsLocalization.closedLocalizationFamily`. No new DAG nodes,
dependency repairs, or statement corrections are needed.

Clause-by-clause correspondence:

- A commutative ring is `(R : Type u) [CommRing R]`; the ideal is `(I : Ideal R)`.
- The finite list is `(r : ℕ) (f : Fin r → R)`, with membership `(hf : ∀ k, f k ∈ I)`.
  Equality of closed subsets is `hV`, equality of `PrimeSpectrum.zeroLocus (I : Set R)`
  and `PrimeSpectrum.zeroLocus (Set.range f)`. Using the set of generators rather than
  its generated ideal gives exactly the same zero locus.
- The denominator monoid is `(IsUnit.submonoid (R ⧸ I)).comap (Ideal.Quotient.mk I)`:
  its elements are precisely the elements whose residue classes are units. The binder
  `[IsLocalization ... B]`, with `[CommRing B] [Algebra R B]`, says that B is the ring
  of fractions at exactly that monoid. It permits any model of the localization and
  adds no assumption to the node's specified B.
- The canonical map on spectra is `PrimeSpectrum.comap (algebraMap R B)`.
  `Topology.IsEmbedding` says that it is a homeomorphism to its image, and the next
  conjunct identifies that image as `{p | ∃ q, I ≤ q.asIdeal ∧ p.asIdeal ≤ q.asIdeal}`.
  Prime containment is precisely specialization from p to q, with q in V(I).
- `IB` is `I.map (algebraMap R B)`. The existential ring equivalence
  `(B ⧸ I.map (algebraMap R B)) ≃+* (R ⧸ I)` gives the quotient isomorphism. Its
  equation on every `a : R` makes it the canonical R-algebra isomorphism, rather than
  an arbitrary isomorphism between the two underlying rings.
- `closedLocalizationFamily R B f` is a `PreZeroHypercover` indexed by `Option (Fin r)`.
  At `some k` its source and arrow are `Spec (Localization.Away (f k))` and Spec of
  the localization map. At `none` they are `Spec B` and Spec of `algebraMap R B`.
  Membership of its `presieve₀` in `Scheme.proetalePrecoverage` asserts exactly the
  full weakly-etale/fpqc covering condition, not merely joint surjectivity.
- The last conjunct is an implication between the two explicitly written retraction
  properties. For each commutative test ring D and ring map g, `g.FaithfullyFlat` and
  `g.WeaklyEtale` imply `∃ t, t.comp g = RingHom.id _`. The left side is the property
  for R and the right side for B. A ring retraction is automatically an algebra map
  for the algebra structure specified by g. Test rings inhabit `Type (max u v)`;
  the free universe v allows arbitrarily large test rings, never a universe below R.
  This follows the node's stated retraction definition of w-contractibility. It does
  not substitute the upstream class `IsWContractibleRing`, whose definition instead
  uses w-strict locality and extremal disconnectedness.

Dependency declarations read and used:

- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec`, `AlgebraicGeometry.Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`; the prime spectrum and comap are its underlying
  topological construction.
- `def-weil-pbc-proetale-covering`: `AlgebraicGeometry.Scheme.proetalePrecoverage`,
  `Mathlib.AlgebraicGeometry.Sites.Proetale`, defined by `propQCPrecoverage @WeaklyEtale`.
- `def-weil-pbc-faithfully-flat-ring-map`: `Module.FaithfullyFlat`,
  `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`, and its ring-map form
  `RingHom.FaithfullyFlat`, `Mathlib.RingTheory.RingHom.FaithfullyFlat`.
- `def-weil-pbc-ind-etale-algebra`: public import
  `Sheaf.RingTheory.IndPrincipalZariski`; this exposes `Algebra.WeaklyEtale` and
  `AlgebraicGeometry.weaklyEtale_SpecMap_algebraMap_iff`, as the dependency's mixed
  record specifies. `RingHom.WeaklyEtale` is its bare ring-map interface, defined by
  installing g.toAlgebra and asking for `Algebra.WeaklyEtale`. The algebra predicate
  requires flatness of the algebra and of tensor multiplication, exactly the node.
  The ind-etale and principal ind-Zariski clauses of that dependency are not extra
  assumptions of this theorem.

The already stated non-Mathlib proof dependency
`Sheaf.RingTheory.LocalizationPrimeResidueFieldIso` is imported without `public`.
The proof-only `lem-weil-pbc-wcontractible-cover-section` has no Lean record yet and
is not imported. It is not needed to type this statement. All seven proof steps of
the node are included in the theorem docstring, including the clopen-summand factorization.

Sources read: `literature/stacks-project/proetale.tex`, lemma-localization (Tag 096V),
lemma-localization-w-contractible (Tag 0987), and lemma-ses-associated-to-open (Tag 09AH).
They give respectively the denominator monoid and image, the retraction argument,
and the finite principal-localization/closed-localization cover.

Edge cases checked mathematically before writing: r = 0 gives `Fin 0` and a singleton
`Option (Fin 0)` family, not an empty covering. Its hV says V(I) is the entire spectrum.
For I = R, zero is a denominator and B is the zero ring; its spectrum is empty and its
quotient is the zero quotient. The principal opens still cover by hV. For I = 0 the
localization at units is R; no nontriviality is assumed. For R = 0 all spectra are empty
and the equivalence and retraction clauses still make sense. No finite generation of I,
Noetherianity, reducedness, or nontriviality has been added.

Searches made (all on 2026-10-15):

- msearch LeanFinder: `closed localization of w-contractible ring at elements invertible
  modulo an ideal`: eight unrelated hits (RingHom local properties and Zariski main theorem),
  no matching combined theorem.
- msearch Loogle: `Localization, PrimeSpectrum.comap`: one free-locus-localization hit,
  no matching theorem.
- msearch LeanSearch: `localization at elements invertible modulo an ideal preserves
  w-contractible rings`: service unavailable (Internal Server Error), recorded as unavailable.
- msearch Mathlib grep: `w[Cc]ontractible|WContractible|closed[Ll]ocalization`: zero hits.
- Source rg for `wContractible|WContractible|w.contractible|closedLocalization|ClosedLocalization`
  found the upstream geometric `IsWContractibleRing` class and its ind-etale retraction
  theorem, but no theorem with all this node's clauses. The exact node-id search in
  WeilConjectures had no hits. Read the class docstring and the retraction interfaces;
  neither is a replacement for this node's combined conclusion.
- Project `lean/Sheaf` rg for the same notions found only a pro-etale subsite source
  citation, no duplicate definition or theorem. The upstream-name index was consulted;
  the chosen declaration names have no collisions in it, Mathlib, or either source tree.
- Mathlib source search for the unit submonoid and its comap found existing uses of
  `(IsUnit.submonoid S).comap f`, which is reused directly; no custom denominator
  predicate or new notion is introduced.

Validation: the delivered file passed scompile.py cleanly against the server's live/side
library (nice 19, two threads, 60 seconds per file). The first attempt required marking
the Spec-valued finite-family construction noncomputable; the subsequent attempt had
no errors or warnings. No local compiler or global build was run.


## Second reading by NS

I independently opened the node, its four statement dependencies and their recorded
source declarations, the delivered module, and proetale.tex at lemma-localization
(096V), lemma-localization-w-contractible (0987), and lemma-ses-associated-to-open
(09AH). There are no new nodes, dependency modules, or statement_change to audit.
The source assumes an arbitrary commutative ring throughout this argument; the
quasi-compact complement in 09AH supplies the finite list, not a Noetherian hypothesis.

Object/hypothesis/conclusion checklist, in node order:

1. Arbitrary commutative R: `(R : Type u) [CommRing R]`. Pass; no nontriviality,
   characteristic, reducedness, field, or finiteness assumption.
2. Ideal I: `(I : Ideal R)`. Pass; no finite generation of I required.
3. Finite list in I: `(r : ℕ) (f : Fin r → R) (hf : ∀ k, f k ∈ I)`.
   Pass; repetitions and the empty list are allowed.
4. Equality V(I) = V(f): `hV` equates `PrimeSpectrum.zeroLocus (I : Set R)`
   with `PrimeSpectrum.zeroLocus (Set.range f)`. Pass; zero locus of a set is
   zero locus of its generated ideal, so no ideal-generation assumption is added.
5. S and B: the comap of `IsUnit.submonoid (R ⧸ I)` along `Ideal.Quotient.mk I`
   is exactly S, and the `IsLocalization ... B` instance gives B = S⁻¹R.
   Pass; the algebra structure specifies the canonical fraction map. B may be
   any model of that localization. Both rings in Type u cover the canonical
   construction; u is arbitrary, so any pair of models can be lifted to a common
   universe. No independent smaller universe of test rings is used.
6. Homeomorphism to the specialization subset: `Topology.IsEmbedding` for
   `PrimeSpectrum.comap (algebraMap R B)`, together with the following range
   equality. Pass; `∃ q, I ≤ q.asIdeal ∧ p.asIdeal ≤ q.asIdeal` means exactly
   that p specializes to some q in V(I), with the correct containment direction.
7. Quotient isomorphism: `∃ e : (B ⧸ I.map (algebraMap R B)) ≃+* (R ⧸ I)`
   and its equation on every a in R. Pass; the equation expresses the canonical
   R-compatible isomorphism in the node's proof, rather than an unrelated ring iso.
8. Finite pro-etale family: `closedLocalizationFamily R B f` has index
   `Option (Fin r)`; `some k` gives Spec R_(f k) with its canonical localization
   arrow and `none` gives Spec B with its canonical arrow. Its `presieve₀`
   membership in `Scheme.proetalePrecoverage` is the full covering assertion.
   Pass. Read proetalePrecoverage = propQCPrecoverage @WeaklyEtale and
   propQCPrecoverage = qcPrecoverage ⊓ precoverage P, together with
   presieve₀_mem_qcPrecoverage_iff; this retains the quasi-compact covering
   condition, as required by the dependency node, and not just surjectivity.
9. Preservation of w-contractibility: the final implication quantifies over
   every commutative D and map g, assumes `g.FaithfullyFlat` and `g.WeaklyEtale`,
   and concludes `∃ t, t.comp g = RingHom.id _`, first for R and then for B.
   Pass. A ring retraction of g is automatically an algebra retraction for
   g.toAlgebra. `Type (max u v)` includes the base-ring size and arbitrary
   larger test-ring sizes as v varies. The same v on both sides supports the
   proof's finite product with the principal localizations; that product stays
   in Type (max u v). Quantifier order matches the node.

Dependency audit: Spec and Spec.map in Mathlib.AlgebraicGeometry.Scheme are
exactly the affine spectrum and contravariant canonical arrow. RingHom.FaithfullyFlat
installs g.toAlgebra and uses Module.FaithfullyFlat, precisely the recorded ring-map
notion. Algebra.WeaklyEtale in Mathlib.RingTheory.Etale.Weakly has fields `flat`
and `flat_lmul'`; RingHom.WeaklyEtale in upstream ProEtale.WeaklyEtale installs
that algebra predicate. These are exposed by the recorded IndPrincipalZariski
module's public imports. Its ind-Zariski predicate is not used as an additional
hypothesis here. The theorem imports the recorded project proof dependency
LocalizationPrimeResidueFieldIso; wcontractible-cover-section is proof-only and
currently has no declaration, so it does not obstruct typing this statement.

Edge cases: r = 0 leaves the B member, rather than an empty family; hV then says
V(I) is the whole spectrum. I = ⊤ makes 0 a denominator, so B and its spectrum
are zero/empty; hV ensures the principal opens cover. I = ⊥ localizes only at
units, giving R. R = 0 makes all spectra empty and all quotient/retraction
clauses meaningful. All characteristics are admitted. No indexing or coefficient
universe is silently tied to a smaller universe.

Independent searches (2026-10-15):

- LeanFinder, `ring localization complement closed subset faithfully flat retraction`:
  eight flatness/localization hits, including IsLocalization.flat and local criteria;
  none states the combined theorem or the finite family construction.
- Loogle, `IsLocalization, PrimeSpectrum`: seven hits, notably
  primeSpectrumOrderIso and localization_comap_isEmbedding/range. I read their
  returned signatures: these give general localization clauses, not this node's
  specialization-set, quotient, covering and retraction conclusion together.
- msearch grep, `closed.localization|contractible.*localization|localization.*contractible`:
  zero hits. LeanSearch for splitting preservation at units modulo an ideal was
  unavailable (Internal Server Error); no negative conclusion is inferred from it.
- Direct rg in Mathlib, upstream WeilConjectures, and project lean/Sheaf for
  `contractib.*localiz|localiz.*contractib|closedLocalization|closed_localization`:
  upstream WContractible and a Koszul-complex contractibility comment only.
  Opened WContractible: IsWContractibleRing is defined geometrically, and
  exists_retraction assumes that class and Algebra.IndEtale. It neither gives
  this combined theorem nor supplies the node's explicit weakly-etale splitting
  property as its definition. The Koszul comment concerns complexes, not rings.
  The two proposed declaration names have no upstream-name-index collision.

No mismatch found; no Lean, node, or definition was changed. The family definition
contains real Spec objects and canonical maps, with no choice from a mere existence
claim and no sorry data. The only sorry is the named theorem's entire proof.
Both declaration docstrings have sources and blueprint tags, and the theorem
carries the seven proof steps, including the open-and-closed summand restriction.
All variables and universes are explicitly bound; the recorded lean.statement
was checked byte-for-byte against the file's theorem signature.

Validation: scompile.py compiled the delivered WContractibleClosedLocalization
module successfully on the server in 1.5 seconds (nice 19, two threads, limit
60 seconds), with no errors or warnings. Its side dependency IndPrincipalZariski
also compiled in the private overlay. No local compiler or global build was run.
