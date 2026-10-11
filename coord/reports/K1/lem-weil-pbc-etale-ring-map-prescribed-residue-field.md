## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleRingMapPrescribedResidueField` states
`AlgebraicGeometry.exists_etale_ring_map_prescribed_residue_field`, with `sorry` only.
The source was checked at https://stacks.math.columbia.edu/tag/00UD (the local
`literature/stacks-project/algebra.tex` is absent). It agrees with the node; no correction
or disputed statement is needed.

Hypothesis and conclusion correspondence:
- A commutative ring R: `(R : Type uR) [CommRing R]`.
- A prime p: `(p : PrimeSpectrum R)`; its prime ideal is `p.asIdeal`.
- Its localization residue field κ(p): `p.asIdeal.ResidueField`.
- L is a field extension with its given structure map: `(L : Type uL) [Field L]`
  and `(iota : p.asIdeal.ResidueField →+* L)`.
- Finiteness: `hfinite`, using `FiniteDimensional` for the algebra `iota.toAlgebra`.
- Separable algebraic: `hsep`, using `Algebra.IsSeparable` for exactly that algebra;
  Mathlib's separability includes algebraicity.
- The commutative ring R' and map ψ: `∃ (S : Type uR) (_ : CommRing S) (ψ : R →+* S)`.
- The induced affine morphism is étale: `Etale (Spec.map (CommRingCat.ofHom ψ))`.
  This is equivalent to `RingHom.Etale ψ` by the recorded
  `AlgebraicGeometry.HasRingHomProperty.Spec_iff` and the Etale instance.
- A prime p' and its contraction: `∃ q : PrimeSpectrum S, ∃ hq :
  q.asIdeal.comap ψ = p.asIdeal`.
- A field isomorphism λ: `∃ e : q.asIdeal.ResidueField ≃+* L`.
- Compatibility λ ∘ κ(ψ) = iota: `e.toRingHom.comp
  (Ideal.ResidueField.map p.asIdeal q.asIdeal ψ hq.symm) = iota`.
  The dependent existential for `hq` lets the canonical residue-field map use precisely
  this contraction equality; it is logically the node's conjunction.

Dependency declarations read and used (all dependency nodes are Mathlib leaves):
- def-weil-pbc-localization-at-prime: `Localization.AtPrime`,
  `Ideal.ResidueField`, `Ideal.Fiber` in Mathlib.RingTheory.Localization.AtPrime.Basic
  and Mathlib.RingTheory.LocalRing.ResidueField.{Ideal,Fiber}. The first two give the
  residue field used here; fibre rings occur in the documented proof.
- def-pc-field-extension: `Algebra` and `RingHom.toAlgebra` in
  Mathlib.Algebra.Algebra.Defs; the latter gives the specified field extension.
- def-weil-pbc-separable-algebraic-extension: `Algebra.IsSeparable` in
  Mathlib.FieldTheory.Separable.
- def-weil-affine-spectrum: `AlgebraicGeometry.Spec` and `Spec.map` in
  Mathlib.AlgebraicGeometry.Scheme.
- def-weil-etale-morphism: `AlgebraicGeometry.Etale` in
  Mathlib.AlgebraicGeometry.Morphisms.Etale.
- lem-weil-pbc-etale-ring-map-iff-etale-affine:
  `AlgebraicGeometry.HasRingHomProperty.Spec_iff` in
  Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties, with the Etale instance.
No dependency needs replacing, and no notion needs a new definition node.

Edge cases checked: a zero ring has no prime p and hence gives no input, as in the source.
The degree-one extension is allowed (the identity ring map suffices). No characteristic,
Noetherian or domain assumption is imposed on R. R and L have independent universes.
The witness S is in R's universe: the standard étale polynomial/localization/quotient
construction lies in that universe even when L is presented in a larger one, so this
choice excludes no case. Fields are nontrivial through `[Field L]`.

Searches:
- msearch.py leansearch, query "An etale ring map realizes a prescribed finite separable
  extension of the residue field at a prime": service unavailable (Internal Server Error).
- msearch.py leanfinder, query "Etale ring map with prescribed finite separable residue
  field extension": eight hits, including
  `Algebra.exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime`,
  `RingHom.Etale.toAlgebra`, `Algebra.IsEtaleAt.comp`, and the field étale classification.
  These preserve residue fields or concern classification, not an arbitrary prescribed
  finite separable extension over a general base ring.
- msearch.py loogle, query "RingHom.Etale, Ideal.ResidueField": zero hits.
- msearch.py grep, query "prescribed.*residue|residue.*prescribed" in RingTheory: zero hits.
- rg in WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json for
  `etale.*prescribed|prescribed.*residue` and the item id: no matching statement
  (only unrelated prescribed Padic residues and coefficient-subring commentary).
- rg for the final declaration name in Mathlib, WeilConjectures, lean/Sheaf and the
  upstream-name table: no existing declaration.

Validation: server single-file compilation is clean. The theorem's docstring records
all four proof steps and the proof dependencies. Delivery dry run is the final check.


## Second reading by K1

Read the item node and its six statement-dependency nodes, the original module,
and the upstream declaration and its entire proof. The authoritative source is
Stacks Algebra, Tag 00UD, label `lemma-make-etale-map-prescribed-residue-field`.
The local literature copy is absent; read the source TeX retrieved from
https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex
(in the sandbox scratchpad), including the surrounding section
`section-etale-local-structure`, and checked https://stacks.math.columbia.edu/tag/00UD.
The section imposes no extra standing assumptions on R. The node accurately
expands the source's isomorphism of extensions into a commuting structure map.
No node statement correction is needed.

Objects, hypotheses and conclusion clauses, in order (all verdicts: exact):

1. R is an arbitrary commutative ring. Originally `(R : Type uR) [CommRing R]`;
   existing theorem has section variables `{A : Type u} [CommRing A]`.
2. p is a prime ideal of that ring. Originally `(p : PrimeSpectrum R)`;
   existing theorem uses `(p : Ideal A) [p.IsPrime]`. PrimeSpectrum bundles
   precisely the ideal and its primality; neither presentation adds a hypothesis.
3. kappa(p) is the residue field of the localization. Both use
   `p.asIdeal.ResidueField` / `p.ResidueField`. Opened `Localization.AtPrime`
   in AtPrime/Basic and `Ideal.ResidueField` in ResidueField/Ideal: the latter
   is `IsLocalRing.ResidueField (Localization.AtPrime p)`, as the dependency says.
4. L is a field with specified structure map iota from kappa(p). Originally
   `(L : Type uL) [Field L] (iota : p.asIdeal.ResidueField →+* L)`;
   existing theorem has `(L : Type v) [Field L] [Algebra p.ResidueField L]`.
   Opened `Algebra` and `RingHom.toAlgebra` in Algebra/Defs: `iota.toAlgebra`
   supplies exactly the chosen map, with `algebraMap = iota`.
5. L/kappa(p) is finite. Original `hfinite` uses `letI := iota.toAlgebra;
   FiniteDimensional ...`; existing binder `[FiniteDimensional p.ResidueField L]`
   is precisely that hypothesis for the chosen algebra, not finiteness of the
   underlying set and not finite dimension over R.
6. The extension is separable algebraic. Original `hsep` and existing
   `[Algebra.IsSeparable p.ResidueField L]` use the same notion. Read Separable.lean
   539-572: every minimal polynomial is separable; this entails integrality and
   algebraicity. There is no missing algebraicity assumption.
7. There exist a commutative ring R' and a ring map psi from R. Original
   `∃ (S : Type uR) (_ : CommRing S) (ψ : R →+* S)`; existing
   `∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A'), ...`.
   Its psi is `algebraMap A A'`; commutative algebra structure and a ring map
   are interchangeable by `RingHom.toAlgebra`, without additional data restrictions.
8. Spec(psi) is etale, equivalently psi is etale. Original
   `Etale (Spec.map (CommRingCat.ofHom ψ))`; existing witness
   `(_ : Algebra.Etale A A')`. Opened Spec and Spec.map in Scheme.lean,
   Etale's `HasRingHomProperty @Etale RingHom.Etale` instance, and
   `HasRingHomProperty.Spec_iff`: the dependency's affine equivalence applies
   to exactly this algebra map, so the conclusion is neither stronger nor weaker.
9. There is a prime p' with contraction p. Original `q : PrimeSpectrum S`
   and `hq : q.asIdeal.comap ψ = p.asIdeal`; existing `(P : Ideal A')
   (_ : P.IsPrime) (hP : p = P.comap (algebraMap A A'))`. This only reverses
   the equality, and the witness order matches the node.
10. There is a field isomorphism lambda : kappa(p') -> L. Original
    `e : q.asIdeal.ResidueField ≃+* L`; existing `e : P.ResidueField ≃+* L`.
    A ring equivalence between fields is exactly the required field isomorphism.
11. lambda composed with kappa(psi) equals iota. Original ring-hom equality
    `e.toRingHom.comp (Ideal.ResidueField.map ... hq.symm) = iota`;
    existing `∀ x, e (Ideal.ResidueField.map p P (algebraMap A A') hP x) =
    algebraMap p.ResidueField L x`. Ring-hom extensionality gives precisely the
    same equality. Opened ResidueField/Ideal: `map` is the canonical map induced
    by `Localization.localRingHom`, not an arbitrary embedding.

Edge cases: R may have zero divisors or be non-Noetherian. The zero ring has
no prime, so both presentations have no input there; the empty spectrum is
covered vacuously. Degree one is allowed. Degree zero is impossible for an
extension of fields; no n or index set occurs in this statement. All
characteristics are allowed. A and L have independent universes u and v;
A' is in u because the standard etale construction uses polynomials,
quotients and localization over A. In particular a presentation of L in a
larger universe is accepted; the existing theorem itself has this signature.

Independent searches (different wording and broader upstream grep):

- LeanSearch through msearch: "An etale algebra realizes any finite separable
  extension of a residue field": service unavailable, Internal Server Error;
  no negative search verdict inferred from that failure.
- LeanFinder through msearch: "Realize a finite separable extension at a prime
  by an étale algebra with that residue field": eight hits. The universal
  factorization ring hit has bijective residue map; the field classification
  and separability-of-residue-field hits do not prescribe a new extension.
- Loogle through msearch: `Algebra.Etale, Algebra.IsSeparable, Ideal.ResidueField`:
  zero hits.
- rg over Mathlib/RingTheory/Etale, the whole upstream WeilConjectures, and
  project lean/Sheaf, with `00UD|make.etale.map.prescribed|exists.*etale.*residue|
  residue.*extension|prescribed.*residue|residue.*prescribed`: found
  `WeilConjectures/Mathlib/RingTheory/Etale/ResidueField.lean:129`,
  `Algebra.exists_etale_residueField_equiv`. Its call sites in FiniteSplitting
  and PropertyC confirm the intended usage; opened the declaration itself.
  No matching project Sheaf declaration was found.

Mismatch found: H4, the worker's search missed this exact upstream theorem
and unnecessarily created a duplicate statement. Removed the sandbox module
and replaced only the item's lean record with `existing: true`, branch
`slopmaster2`, module `WeilConjectures.Mathlib.RingTheory.Etale.ResidueField`,
declaration `Algebra.exists_etale_residueField_equiv`. The recorded statement
is the declaration's written signature verbatim, including its implicit
ambient section variables as explained in lean.note and above. The old
statement itself was accurate, and its docstring carried all four node proof
steps; no H3 repair was necessary. The Worker report remains as the record
of the first reading; its claimed absence of an existing declaration is
superseded by this second reading.

No new nodes or dependency modules are needed: all six dependencies give
their stated notions via their Mathlib leaves. No definition is introduced,
no proof is written, and there are no new unbound variables or universes.
Read the existing proof and checked the committed upstream sorry map
`local/sorry_map_slopmaster2_71d63dcf.jsonl.gz`: the exact declaration has
`s: false`, `ts: false`, so neither direct nor transitive sorry is present.
Existing declarations need no new module compilation; the delivery preflight
checks the declaration in its upstream module.
