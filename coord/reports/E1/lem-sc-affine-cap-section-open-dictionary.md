## Worker report

The module `Sheaf.AlgebraicGeometry.AffineCapSectionOpenDictionary` states
`AlgebraicGeometry.Scheme.Modules.affine_cap_section_open_dictionary`.  It uses
`R : Type u` with `[CommRing R]`, an invertible module
`M : (Spec (.of R)).Modules`, and a section `s` of the module returned by
`AlgebraicGeometry.moduleSpecΓFunctor`.  The first conjunct renders the affine
Tilde/Gamma counit as `IsIso (Scheme.Modules.fromTildeΓ ... M)`.  The second
renders finite projectivity as `Module.Finite R N ∧ Module.Projective R N`.
For each prime ideal `p` (with `[p.IsPrime]`), the first clause gives a linear
rank-one identification of the localized module with `Localization.AtPrime p`;
the second clause is the stalk/localization prime-membership equivalence, written
with `LocalizedModule.mk`, the mapped prime ideal, and `p • ⊤`.  The final set
clause renders the nonvanishing locus as the set of prime points where `s` is not
in `p • ⊤` (the same set on both sides, as the explicit locus definition).

Dependency declarations used:

- `AlgebraicGeometry.Spec` (Mathlib, `Mathlib/AlgebraicGeometry/Scheme.lean`),
  for `Spec (.of R)`.
- `AlgebraicGeometry.Scheme.Modules.IsInvertible` from
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`.
- `AlgebraicGeometry.RingedSpace.IsCoherent` from
  `Sheaf.AlgebraicGeometry.Coherent` (the quasi-coherent dependency record).
- Mathlib's `AlgebraicGeometry.moduleSpecΓFunctor` and
  `AlgebraicGeometry.Scheme.Modules.fromTildeΓ` from
  `Mathlib/AlgebraicGeometry/Modules/Tilde.lean`, corresponding to
  `lem-weil-pbc-affine-tilde-gamma-adjunction`.
- `Module.isLocallyConstant_rankAtStalk` from
  `Mathlib/RingTheory/Spectrum/Prime/FreeLocus.lean`, corresponding to
  `lem-weil-pbc-finite-projective-rank-locally-constant`.

Edge cases checked: the theorem permits an arbitrary commutative ring (including
zero rings), arbitrary universe `u`, and the empty set of prime ideals; the prime
quantifier is over all ideals carrying `IsPrime`, and no characteristic or
nontriviality hypothesis is added.  The localization statement includes every
prime, including minimal and maximal primes.  The section may be zero, in which
case the displayed nonvanishing set is empty.

Searches made before writing:

- `msearch.py ... leanfinder "invertible module on affine scheme corresponds to finite projective module"`:
  only generic locally-free/tilde declarations; no combined theorem (no match).
- `msearch.py ... loogle "moduleSpecΓFunctor, fromTildeΓ, finite projective"`:
  returned the separate Mathlib Tilde/Gamma declarations, with no exact dictionary theorem.
- `rg -n -i 'finite projective.*rank one|invertible.*module|nonvanishing.*section.*Spec|pN'`
  over Mathlib and `WeilConjectures`: separate APIs only; no existing declaration.
- `grep -rl 'lem-sc-affine-cap-section-open-dictionary'` over the source checkout:
  no declaration found.
- `rg -n 'affine.*dictionary|tilde.*finite|prime.*membership'` over existing
  `lean/Sheaf`: no duplicate statement.

No statement correction or new definition node was needed.  The file compiled cleanly
with `scompile.py`; the only proof is the required `sorry`.

## Earlier second reading (a previous round; superseded)

I reread the node and module together. The binders match the node's commutative ring, affine spectrum, invertible module, and global section. The counit, finite-projective, prime-localization, membership, and nonvanishing-locus clauses all appear in order in the theorem signature. The recorded dependency declarations are the declarations imported by the module (Mathlib Tilde/Gamma, the source invertibility class, and the landed coherent-module declaration). No hypothesis was added or removed, and the theorem proof remains `sorry`.

## Second reading by E1

I read the node, every statement dependency's node and recorded declaration, the delivered
Lean, and the source text together. The repository's literature checkout is absent on this
machine; I read the available Stacks sources at `/home/ubuntu/c1-stacks-review/schemes.tex`
and `/home/ubuntu/c1-stacks-review/modules.tex`: `lemma-quasi-coherent-affine` (01IA),
`lemma-equivalence-quasi-coherent` (01IB), and `lemma-s-open` (01CY), including the
surrounding affine quasi-coherence setup. The sources assume an arbitrary commutative ring;
01CY assumes local structure-sheaf stalks, which schemes already provide. No Noetherian,
field, characteristic, or nonempty-spectrum assumption is present.

Object, hypothesis, and conclusion checklist (all verdicts refer to the repaired file):

1. A commutative ring R: `{R : Type u} [CommRing R]`. Exact, arbitrary universe u.
2. X = Spec R: `(Spec (.of R))`. Mathlib `AlgebraicGeometry.Spec` is the affine
   spectrum recorded by `def-weil-affine-spectrum`; its points are `PrimeSpectrum R`.
3. An invertible O_X-module M: `(M : (Spec (.of R)).Modules) [M.IsInvertible]`.
   The source `Scheme.Modules.IsInvertible.exists_isoUnit` requires a trivialization
   on an open neighbourhood of every point, precisely local freeness of rank one.
   No extra quasi-coherence hypothesis is imposed: local freeness implies it.
4. N = Gamma(X,M): every occurrence is
   `((moduleSpecΓFunctor (R := CommRingCat.of R)).obj M)`.
   I opened the functor definition: evaluation at `op ⊤`, with scalars restricted along
   `Scheme.ΓSpecIso`, gives the R-module of global sections. Its underlying elements
   are the same sections as `M.val.presheaf.obj (op ⊤)`.
5. The canonical counit identifies M with tilde N:
   `IsIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of R) M)`.
   The opened declaration is the counit of `tilde.adjunction`, not an arbitrary map.
   This is exactly the identification in 01IA/01IB.
6. N is finite projective: `Module.Finite R N ∧ Module.Projective R N`. Exact.
7. Rank one at every prime: `∀ (p : Ideal R) [p.IsPrime]`, followed by
   `Nonempty ((LocalizedModule p.primeCompl N) ≃ₗ[Localization.AtPrime p]
   (Localization.AtPrime p))`. Exact: a rank-one free localization is a module
   linearly isomorphic to the local ring. No choice of basis is demanded.
8. A section s in N: `(s : ((moduleSpecΓFunctor ...).obj M))`, with no restriction.
   Binding s before the conclusion only specializes the same dictionary to an arbitrary
   section; zero is always available, so it does not restrict the preceding assertions.
9. Stalk/prime membership: for every prime, `LocalizedModule.mk s 1` belongs to
   `(Ideal.map (algebraMap R (Localization.AtPrime p)) p) • ⊤` iff `s ∈ p • ⊤`.
   These are s/1 in pN_p and s in pN. I read `tilde.toStalk` and its
   `IsLocalizedModule p.primeCompl` instance: combined with the counit iso it gives
   the specified stalk identification and carries the germ to s/1. The node's
   conditional description under that identification is rendered in these coordinates.
10. Consequently the actual nonvanishing locus equals the prime-membership locus:
    `nonvanishingLocus M s = {p : PrimeSpectrum R | ¬ s ∈ p.asIdeal • ⊤}`.
    I opened the landed `nonvanishingLocus` definition in `Ample.lean`: it uses the germ
    in M's actual stalk and the maximal ideal of X's actual local ring, precisely 01CY.
    The left side and right side share the underlying points of Spec R. Exact.

Dependency audit: `pqf-def-coherent`'s recorded `RingedSpace.IsCoherent` is its coherent
clause, not its quasi-coherent clause. Its module explicitly delegates quasi-coherence
and finite type to Mathlib `SheafOfModules.IsQuasicoherent` and `IsFiniteType`; the opened
Tilde module uses the same quasi-coherence predicate. This statement does not assume
coherence, and needs no replacement dependency module. The rank-locally-constant node's
`Module.isLocallyConstant_rankAtStalk` requires finite presentation and flatness, both
consequences of finite projectivity; the current item states rank one directly, without
adding those hypotheses. The recorded Tilde/Gamma declarations match the canonical
counit used here. I added the already landed `def-weil-pbc-ample-invertible-module` to
`stmt_deps`, because its recorded declarations include the existing nonvanishing locus;
no new notion, new definition node, or dependency module was needed.

Edge cases: the zero ring has empty spectrum and makes all prime-local clauses vacuous;
its module of sections on the empty scheme is zero, finite projective, and both loci are
empty. For a nonzero ring the zero module cannot satisfy invertibility, as expected.
The zero section is allowed and has empty nonvanishing locus, agreeing with membership
in pN for every p. Arbitrary characteristic and minimal/nonmaximal primes are included.
There is no index set or tensor-power parameter in this item, so empty indices and n = 0
introduce no omitted case. Universe u is explicitly bound; R and X.Modules use the usual
same-universe Mathlib scheme-module encoding, with no independent smaller test universe.

Independent searches (2026-10-11):

- `msearch.py ... leanfinder "germ global section line bundle nonzero residue field affine
  spectrum"`: eight results, including `Scheme.evaluation`, `Scheme.germ_residue`, and
  `Scheme.evaluation_ne_zero_iff_mem_basicOpen`, about structure-sheaf sections; no combined
  invertible-module dictionary.
- `msearch.py ... loogle '"moduleSpecΓFunctor"'`: exactly the global-sections functor,
  whose source definition I opened; no theorem with the complete conclusion.
- `msearch.py ... leansearch "For a line bundle on Spec R, global sections form a finite
  projective module of rank one and the nonvanishing locus is detected by prime ideal
  membership"`: unavailable (HTTP Internal Server Error); no search verdict inferred.
- `rg` with `dictionary`, `nonvanishingLocus`, `nonvanishing.*prime`, and
  `invertible.*projective` over Mathlib/AlgebraicGeometry, WeilConjectures and lean/Sheaf:
  found the landed locus in Ample, its callers, the Tilde and invertibility APIs, and
  unrelated dictionaries. No declaration combines all clauses of this node. Separate
  prime membership is the recorded `Module.prime_mem_localized_iff`, which I also opened.

Mismatches repaired: H3, the original final conjunct was the reflexive equality of the
prime-membership set with itself, so it said nothing about the section on the sheaf.
Replaced its left side by the existing `nonvanishingLocus M s` and cited its landed node.
The earlier worker's claim that a reflexive set equation renders the nonvanishing locus,
and the earlier superseded second reading's approval of it, are incorrect. H8, expanded
the proof docstring to give all three node proof steps and their named dependencies,
including the finite standard-open cover and the germ identification. H9, added the
standard license/header and replaced the unused import of the parent affine-intersection
theorem (which this dictionary supports) and the unused prime-membership theorem import
with the actual locus and Mathlib type imports. The correct counit, finite-projective,
rank-one and localized-membership clauses were preserved verbatim. The node's natural
statement and proof did not change; `lean.statement` was refreshed verbatim from the file.
No definitions or proofs were added: the sole theorem still has `by sorry`.

Validation: `scompile.py E1 lem-sc-affine-cap-section-open-dictionary` on the final module
compiled cleanly on the server in 1.9 seconds, with no warnings. All variables and u are
explicitly bound; all lines are at most 100 characters.
