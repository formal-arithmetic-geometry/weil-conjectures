## Worker report

The module `Sheaf.RingTheory.EtaleRetractionFiniteTypeSplitting` states
`Algebra.etale_retraction_finite_type_splitting` with proof `sorry`.
The local ring is `(R : Type u)` with `[CommRing R] [IsLocalRing R]`. Its
retraction hypothesis quantifies every étale `R`-algebra `R'`, a prime `q`
over the maximal ideal, and bijectivity of the canonical residue-field map
`Ideal.ResidueField.mapₐ`; it concludes an `R`-algebra retraction whose inverse
image of the maximal ideal is `q.asIdeal`. The finite-type input is `S` with
`[CommRing S] [Algebra R S] [Algebra.FiniteType R S]`.

The conclusion existentially introduces `R`-algebras `A` and `B` (with their
commutative-ring and algebra instances, and finite type for `B`) and an
`R`-algebra equivalence `e : S ≃ₐ[R] A × B`. The conjunction says `A` is a
finite `R`-module and every prime of `B` over the maximal ideal fails
`Algebra.IsQuasiFiniteAtPrime R B q`. The unrestricted existential types allow
`A` or `B` to be zero rings.

Dependencies used are Mathlib `AlgebraicGeometry.Etale`/the affine étale
notion represented by `Algebra.Etale`, Mathlib `Algebra.FiniteType`, Mathlib
`AlgebraicGeometry.Scheme.residueField` (the residue-field notion), and
`Sheaf.RingTheory.QuasiFiniteAtPrime`, declaration
`Algebra.IsQuasiFiniteAtPrime`.

Edge cases checked: zero factors are permitted by the existential; `S` may be
zero; the finite-type algebra may have zero generators; the local residue
field map is stated canonically and the maximal ideal condition is explicit;
universes for the étale test algebra (`w`) and input algebra (`v`) are
independent.

Searches: `msearch.py leanfinder` for “finite type algebra over local ring
etale retraction product finite factor non quasi finite” found no statement;
`msearch.py loogle` for `Algebra.Etale, Algebra.FiniteType, IsLocalRing,
IsQuasiFiniteAtPrime` found only component notions; grep of Mathlib and
`WeilConjectures` for `etale_retraction_finite_type_splitting`, retraction
product decompositions, and this blueprint id found no existing declaration.
The project search found only the dependency declaration
`Algebra.IsQuasiFiniteAtPrime`.

## Earlier second reading (a previous round; superseded)

Reading the node and module clause by clause: the local-ring hypothesis,
quantification over étale extensions, prime-over-maximal-ideal condition,
residue-field isomorphism (rendered as bijectivity of the canonical map), and
retraction condition all match the node. The finite-type map `R → S` is the
`Algebra.FiniteType R S` instance. The product decomposition is an
`R`-algebra equivalence, `A` is `Module.Finite R A`, and `B` is explicitly
finite type and non-quasi-finite at every prime over the maximal ideal. No
hypothesis or conclusion clause is omitted; either factor can be zero.

## Second reading by E1

The node introduces a commutative local ring `(R : Type u)` with
`[CommRing R] [IsLocalRing R]`; the Lean theorem has exactly these binders.
Its hypothesis quantifies an arbitrary-universe étale commutative `R`-algebra
`R'`, a prime `q`, the condition `q.comap (algebraMap R R') = maximalIdeal R`,
and bijectivity of the canonical `Ideal.ResidueField.mapₐ`; Lean renders all
four clauses and concludes an `R`-algebra retraction `τ` satisfying
`τ.toRingHom ⁻¹' maximalIdeal R = q.asIdeal`. This is the source's intended
condition, with the source's reversed displayed equality corrected in the
proof text. The finite-type input is `(S : Type v)` with commutative-ring,
`Algebra R S`, and `Algebra.FiniteType R S` instances.

The conclusion introduces `A B : Type v`, commutative-ring and `R`-algebra
instances for each, and finite type for `B`. It then gives an `R`-algebra
equivalence `S ≃ₐ[R] A × B`, `Module.Finite R A`, and for every prime `q` of
`B` over the maximal ideal, `¬ IsQuasiFiniteAtPrime R B q`. Quantifier order
and conjunctions match the node. Both factors may be zero; `S` may be zero;
there is no positivity assumption on a generator count; and `n = 0` is covered
by `Algebra.FiniteType`. The independent universe `w` for étale test algebras
is retained, and the characteristic is unrestricted.

I checked the source at Stacks Algebra Lemma 04GG, proof of (8) ⇒ (11), and
Lemma 00UK. The four proof clauses in the declaration docstring now match the
DAG: étale-local product decomposition, retraction, tensoring the product back
and finite-type inheritance, then closed-fibre identification transferring
non-quasi-finiteness. The `Algebra.Etale`, `Algebra.FiniteType`, residue-field
map, and `Algebra.IsQuasiFiniteAtPrime` declarations were opened; they are the
recorded dependency notions and no duplicate definition was added. Searches
used LeanFinder, Loogle, LeanSearch (unavailable on this run), and grep over
Mathlib, `WeilConjectures`, and `lean/Sheaf`; no existing theorem states this
splitting.

The only change in the second reading is documentation: the module header and
statement docstring were completed with the source and all four proof steps;
the Lean signature and node statement remain otherwise unchanged.

## Reviewer fix (R-ert1011)

The retraction hypothesis quantified étale test algebras over an independent universe `w`. A theorem polymorphic in `w` may be used at `w` below the universe of `R`. There, for a local ring whose residue field is too large for `Type w`, no test algebra has a prime over the maximal ideal, so the hypothesis holds vacuously. The conclusion for every finite-type `S` would then make every such local ring henselian (Tag 04GG (11) ⇒ (1)), which is false, e.g. for `K[t]_(t)` with such a `K`. The hypothesis is now M1's form from `finite_algebra_is_product_local_rings` (c8ddf5893), verbatim: `R' : Type (max u v)`, `Algebra.Etale R R' →`, a prime `p : Ideal R'` with `[p.IsPrime]`, and `p = (maximalIdeal R).comap τ.toRingHom`. The conclusion is unchanged.
