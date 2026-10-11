## Worker report

The module states `Module.Flat.localizedModule_atPrime_of_flat` with a `sorry` proof.
It is the only-if direction of Stacks Project, Algebra, Lemma 10.39.18 (Tag 00HT),
part (6). The local `literature/stacks-project/algebra.tex` checkout is absent on this
machine; I read the Stacks Project Tag 00HT page directly, including part (6) and its proof.

Statement correspondence:

- Commutative rings `R` and `A`: `{R A M : Type*} [CommRing R] [CommRing A]`.
- The ring homomorphism `R -> A`: `[Algebra R A]`, with map `algebraMap R A`.
- The `A`-module `M`: `[AddCommMonoid M] [Module A M]`.
- Every prime of `A`: `(q : Ideal A) [q.IsPrime]`. The theorem is polymorphic in `q`.
- Its contraction: `let p := q.comap (algebraMap R A)`.
- The hypothesis that `M` is flat over `R` for the induced scalar action:
  `(hflat : @Module.Flat R M _ _ (Module.compHom M (algebraMap R A)))`.
- Its prime localization: `LocalizedModule q.primeCompl M`.
- The induced action of `R_p` through `R_p -> A_q`:
  `Module.compHom _ (Localization.localRingHom (q.comap (algebraMap R A)) q
  (algebraMap R A) rfl)`.
- The conclusion: `@Module.Flat (Localization.AtPrime (q.comap (algebraMap R A)))
  (LocalizedModule q.primeCompl M) _ _ ...` under that induced action.

Dependency declarations: `Module.Flat` in `Mathlib.RingTheory.Flat.Basic`, and
`Localization.AtPrime` in `Mathlib.RingTheory.Localization.AtPrime.Basic`.
`LocalizedModule` is in `Mathlib.Algebra.Module.LocalizedModule.Basic`.
The source signature and docstring of each Mathlib dependency were read.
The proof docstring records both DAG proof steps: localization of the flat module
away from `q`, then the flatness equivalence for modules over `R_p`.

Edge cases: no nonzero, Noetherian, finite generation, or nonempty-prime assumption
was added. The zero module and zero ring remain allowed. If `A` has no prime ideals,
the theorem has no instance of `q` and the universal assertion is vacuous.
The arbitrary universes of `R`, `A`, and `M` are retained by `Type*`.

Searches: `msearch leanfinder` with “R-flat A-module M localized at prime q of A
is flat over localization at contraction p of R” found `instFlatAtPrime` for the
ring case and `Module.Flat.of_isLocalizedModule` for base-ring localization, no
exact arbitrary `A`-module statement. `msearch loogle` with “Module.Flat,
LocalizedModule, Localization.AtPrime” returned zero hits. `msearch grep` for
`Flat.*localized|localized.*Flat` under `RingTheory/Flat` found the Mathlib
localization lemmas, but no exact statement. Local `rg` of Mathlib and
`WeilConjectures` found no exact match; `rg` of `lean/Sheaf` found no match.
The node id search in `WeilConjectures` also found no match.

## Second reading by H1

I read the node, its two definition dependencies, the Lean file, and Stacks Project,
Algebra, Lemma 10.39.18 (Tag 00HT), part (6). The source assumes only a ring map and
an `A`-module for this clause. Item-by-item correspondence:

- Commutative rings `R` and `A`: `{R A M : Type*} [CommRing R] [CommRing A]`.
- Map `R -> A`: `[Algebra R A]` and `algebraMap R A`. This is the node's arbitrary
  ring homomorphism; no flatness of the map is assumed.
- `A`-module `M`: `[AddCommMonoid M] [Module A M]`.
- Every prime `q` of `A`: `(q : Ideal A) [q.IsPrime]`. The theorem can be applied
  to each such `q` without a selected or maximal prime assumption.
- Contracted prime `p = q cap R`: `q.comap (algebraMap R A)`. Its primality is
  derived by Mathlib; it is not an extra hypothesis.
- Premise, `M` flat over `R`: `hflat : @Module.Flat R M _ _
  (Module.compHom M (algebraMap R A))`. The explicit scalar action is restriction
  along the given map, matching `def-weil-pbc-flat-ring-map`'s `Module.Flat`.
- Localized ring `R_p`: `Localization.AtPrime (q.comap (algebraMap R A))`, matching
  `def-weil-pbc-localization-at-prime`'s Mathlib declaration.
- Localized module `M_q`: `LocalizedModule q.primeCompl M`. Its `A_q` action comes
  from Mathlib's localized-module construction.
- Induced `R_p` action on `M_q`: `Module.compHom _
  (Localization.localRingHom (q.comap (algebraMap R A)) q
  (algebraMap R A) rfl)`. This is restriction along the canonical map
  `R_p -> A_q`, not an unrelated module instance.
- Conclusion: `@Module.Flat (Localization.AtPrime (q.comap (algebraMap R A)))
  (LocalizedModule q.primeCompl M) _ _ ...`. It asserts exactly `R_p`-flatness
  of `M_q`; the node asks for no reverse implication.

Edge cases: no nonzero, finite generation, Noetherian, characteristic, or
nonemptiness assumption appears. A zero module is included. A zero ring has no
prime `q`, so the universal claim is vacuous. No index or natural-number parameter
occurs. `Type*` leaves the universes of all three carriers arbitrary. Mathlib's
`Module.Flat` and `Localization.AtPrime` signatures were checked against the two
definition nodes; `Localization.localRingHom` is precisely the induced map of
prime localizations.

Independent searches: LeanFinder, "flatness of a module after localization at a
prime of its algebra over the contracted prime of the base ring", returned the
ring-only `instFlatAtPrime`, `RingHom.Flat.localRingHom`, and base-ring module
localization lemmas, but no exact statement. Loogle,
`Module.Flat ?R (LocalizedModule ?S ?M)`, returned
`Module.Flat.localizedModule` (localization in the base ring) and
`Module.flat_of_localized_maximal` (again primes of the base ring). Grep for
`flat_of_localization|localization_flat|flat_localized` returned no match;
targeted `rg` of Mathlib's flatness files, upstream `WeilConjectures`, and this
project's `lean/Sheaf` found no exact arbitrary-algebra-module theorem.

No mismatch found and no Lean or node change needed. The statement's docstring
describes both node proof steps; the only proof body is `sorry`. Single-file
compilation succeeded without errors or warnings.
