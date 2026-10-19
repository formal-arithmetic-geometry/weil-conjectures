## Worker report

Item: `lem-trf-j2-affine-cover`.

The module `lean/Sheaf/AlgebraicGeometry/JTwoAffineCover.lean` states
`AlgebraicGeometry.j2_of_affine_open_cover` with proof `sorry`. It expands J-2 exactly as
the open regular-locus condition for every finite type algebra, using the canonical
`IsRegularLocalRing` predicate and `Localization.AtPrime`.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| A scheme X | `(X : Scheme.{u})`. |
| X is locally Noetherian | `[IsLocallyNoetherian X]`, the recorded Mathlib declaration for `pqf-def-locnoeth`. |
| An index type and affine open family | `(I : Type v) (U : I → X.affineOpens)`. The index universe is independent and no finiteness or nonemptiness is imposed. |
| The family covers X | `hU : ⨆ i : I, (U i : X.Opens) = ⊤`. |
| Every coordinate ring is J-2 | `hJ : ∀ i : I, ∀ (A : Type u) [CommRing A] [Algebra Γ(X, U i) A] [Algebra.FiniteType Γ(X, U i) A], IsOpen {p : PrimeSpectrum A | IsRegularLocalRing (Localization.AtPrime p.asIdeal)}`. This quantifies over every finite type algebra, rather than only the coordinate ring itself. |
| Every affine open V has a J-2 coordinate ring | `∀ V : X.affineOpens, ∀ (A : Type u) [CommRing A] [Algebra Γ(X, V) A] [Algebra.FiniteType Γ(X, V) A], IsOpen {p : PrimeSpectrum A | IsRegularLocalRing (Localization.AtPrime p.asIdeal)}`. |

The declaration uses the statement dependencies as follows:

- `def-pc-scheme`: Mathlib `AlgebraicGeometry.Scheme` from
  `Mathlib.AlgebraicGeometry.Noetherian`.
- `pqf-def-locnoeth`: Mathlib `AlgebraicGeometry.IsLocallyNoetherian` from
  `Mathlib.AlgebraicGeometry.Noetherian`.
- `def-exc-excellent-ring`: `Sheaf.RingTheory.ExcellentRing`; its recorded
  `IsQuasiExcellent` definition uses the same expanded J-2 clause, and the module
  supplies the ring-theoretic imports for `PrimeSpectrum`, localization and
  regular-local predicates.

The proof docstring follows all five node proof steps. It first applies the pointwise
locally-finite-type criterion to an arbitrary finite type algebra over an affine V;
then uses open-immersion, composition and locally-Noetherian permanence; refines inverse
images of the given cover by affine opens and applies the all-affine-pairs criterion;
uses the J-2 hypotheses and affine-open stalk localization to glue regular loci; and
finally identifies the regular locus on the whole affine source. The proof-dependency
names in the docstring are the Mathlib leaves recorded by the node, so no additional
project module is needed at statement stage.

Edge cases checked before writing: an empty index type is allowed (the cover equality then
forces the empty scheme case); no finite subcover is used; the zero algebra has empty
prime spectrum and hence an open regular locus; nonreduced finite type algebras remain in
the quantifier; empty affine opens and an empty scheme are not excluded; arbitrary
characteristic is allowed; and the finite type algebra universe is `Type u`, matching the
coordinate-ring universe and the recorded `IsQuasiExcellent` convention. The index
universe `v` is independent of the scheme universe `u`.

Searches for an existing declaration:

- `msearch.py ... leanfinder` with query “J-2 property passes from an affine open cover to every affine open of a locally Noetherian scheme”: eight hits, all Mathlib affine-cover or Noetherianity results (`isLocallyNoetherian_of_affine_cover`, `of_affine_open_cover`, etc.); none states J-2 locality.
- `msearch.py ... loogle IsLocallyNoetherian`: zero hits with an unknown-identifier diagnostic; no exact J-2 declaration.
- `msearch.py ... grep 'J.?2|regular locus|IsRegularLocalRing' RingTheory`: 25 unrelated RingTheory hits and no J-2 locality theorem.
- `rg -n 'J.?2|regular locus|IsRegularLocalRing|j2_of_affine_open_cover'` over upstream `WeilConjectures` and project `lean/Sheaf`: no existing declaration of this theorem or predicate (only unrelated regular-local uses and comments).
- `grep -rn 'lem-trf-j2-affine-cover'` and the DAG search showed no other Lean declaration for this item.

No new definition node is needed: the statement dependencies and Mathlib provide every
notion. No dependency repair module is needed. No statement correction or
`STATEMENT-DISPUTED` flag is needed.

Validation: `scompile.py N9 lem-trf-j2-affine-cover
/home/ubuntu/weil-newtargets-stage2-sandbox/N9/lem-trf-j2-affine-cover/lean/Sheaf/AlgebraicGeometry/JTwoAffineCover.lean`
completed cleanly (the only postponed proof is the expected `sorry`).

## Second reading by N9

I reopened the target JSON and the complete module after the first compile. The cover
hypothesis is exactly an arbitrary family of affine opens with supremum top, and the
locally-Noetherian assumption is the recorded class instance. I checked each J-2 clause:
both `hJ` and the conclusion quantify over an arbitrary `Type u` commutative finite-type
algebra and assert openness of all primes whose `AtPrime` localization is regular local.
No finite-index, nonempty, reduced, characteristic, or injectivity assumption was added,
and the conclusion ranges over every `X.affineOpens`. The module's signature copied into
the node's `lean.statement` is verbatim through `:=`; its namespace and declaration name
match the file. The only change from the initial draft was to expand J-2 from the regular
locus of the coordinate ring to the required regular loci of all finite type algebras.
