## Worker report

The module `Sheaf.RingTheory.EtaleAwayCompletionFiniteRefinement` states
`RingTheory.etale_away_completion_finite_refinement`, with `sorry` as its only proof.
It follows Stacks Project, restricted.tex, Tag 0AKJ,
`lemma-fully-faithful-etale-over-complement`, read in full in the supplied source.
No definition, new node, dependency repair, or statement correction is needed.

Hypothesis and conclusion correspondence:

- The commutative Noetherian base is `(A : Type u) [CommRing A]
  [IsNoetherianRing A]`; the arbitrary ideal is `(I : Ideal A)`.
- The commutative finite type A-algebra is `(D : Type v) [CommRing D]
  [Algebra A D] (hD : (algebraMap A D).FiniteType)`. This uses the recorded
  `RingHom.FiniteType`, rather than redefining finite generation.
- The commutative Noetherian A-algebra R is `(R : Type w) [CommRing R]
  [Algebra A R] [IsNoetherianRing R]`. There is no henselian-pair binder.
- Being etale over Spec A minus V(I) is `hEtale`: every prime `q` of D with
  `¬ I ≤ q.asIdeal.comap (algebraMap A D)` satisfies
  `Algebra.IsEtaleAt A q.asIdeal`. The negated ideal inclusion says exactly that
  the image point is outside V(I). Mathlib defines `IsEtaleAt` as formal
  etaleness of the localization. Here D is finitely presented over A, by
  Noetherianness and finite type, so Mathlib's
  `Algebra.exists_etale_of_isEtaleAt` identifies this with an etale open
  neighbourhood of q. Conversely an etale scheme neighbourhood gives this
  localized property. Thus this is the full stated scheme condition, in
  arbitrary independent ring universes; no extra finite-presentation assumption
  is imposed.
- The two completions are `AdicCompletion (I.map (algebraMap A D)) D` and
  `AdicCompletion (I.map (algebraMap A R)) R`. The given `φ` is an A-algebra
  map between precisely these rings, using Mathlib's inherited A-algebra
  structures. The theorem has no continuity hypothesis.
- The output `∃ (R' : Type w) (_ : CommRing R') (_ : Algebra R R')
  (_ : Algebra A R') (_ : IsScalarTower A R R')` gives a commutative R-algebra
  and its compatible induced A-algebra structure. The structural map j is
  `algebraMap R R'`. The scalar-tower binder specifies the meaning of the
  induced A-structure; it is part of the output, not an input hypothesis.
  Choosing a carrier in R's universe loses no case because the sought algebra
  is finitely presented over R.
- `Algebra.Etale R R' ∧ Algebra.FinitePresentation R R'` gives exactly the
  etale finitely presented output algebra (not a finite-module algebra).
- `∃ u : D →ₐ[A] R'` is the required A-algebra map.
- `Function.Bijective (Ideal.quotientMap ... (algebraMap R R')
  Ideal.le_comap_map)` says that the canonical induced ring map
  R/IR to R'/((IR)R') is an isomorphism. The target ideal is extension by j,
  exactly as required; extension from A equals this successive extension by
  the output scalar tower.
- The last universally quantified implication is the coordinate expression
  of `û = ĵ ∘ φ`. For every n, x in D-hat and representatives d and r for the
  nth residues of x and φ(x), respectively, the images of u(d) and j(r) in
  R'/I^nR' agree. Both canonical completion maps send such representatives to
  those images. Each quotient projection is surjective, so representatives
  always exist. Equality at all n is equality of compatible sequences.
  Conversely the stated equality of completed maps implies these identities.
  The use of implications does not weaken the conclusion. No arbitrary lift
  or arbitrary comparison map is substituted for a canonical map. The
  maps exist because A-linearity sends I^nD into I^nR' and I^nR into I^nR'.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` and its meaning
  as finite generation of all ideals.
- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType` (the recorded
  declaration), equivalently `Algebra.FiniteType` for the structure map.
- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation`;
  `Algebra.FinitePresentation.of_finiteType` supplies the equivalence used
  to explain the etale-at-prime translation, with no new assumption.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`;
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`,
  its `HasRingHomProperty` instance, and its affine-ring interpretation.
  The latter is publicly imported as the recorded dependency module.
- `Mathlib.RingTheory.Etale.Locus`: `Algebra.IsEtaleAt` and
  `Algebra.exists_etale_of_isEtaleAt`; `Mathlib.RingTheory.Etale.Basic`:
  `Algebra.Etale`, including its finite-presentation field.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`, the recorded
  compatible-sequence construction. `Mathlib.RingTheory.AdicCompletion.Algebra`:
  the commutative-ring and inherited algebra instances, and `AdicCompletion.evalₐ`.
- `Mathlib.Algebra.Algebra.Hom`: `AlgHom`;
  `Mathlib.RingTheory.Ideal.Quotient.Operations`: `Ideal.Quotient.algebra`,
  `Ideal.Quotient.mkₐ`, `Ideal.Quotient.mk`, and `Ideal.quotientMap`;
  `Mathlib.RingTheory.Ideal.Operations`: ideal multiplication and powers.
  The quotient/hom dependency is a Mathlib leaf and needs no lean record repair.

The published proof dependencies are imported with plain `import`:
`WeilConjectures.RingTheory.PairHenselization`,
`WeilConjectures.RingTheory.PairHenselizationNoetherianCompletion`,
`Mathlib.RingTheory.FinitePresentation`,
`Mathlib.Algebra.Category.Ring.FinitePresentation`,
`Mathlib.RingTheory.Etale.Basic`, `Mathlib.RingTheory.Smooth.Flat`,
`WeilConjectures.RingTheory.BijectiveQuotientMapPowOfFlat`, and
`WeilConjectures.RingTheory.PairHenselizationCompletionData` (the finite
presentation and etale-basic imports are already supplied publicly for the
statement). Their recorded declarations were inspected. The proof dependency
`lem-per-etale-away-completion-hom-lifting` currently has no Lean declaration,
so no module is imported for it. It is only a proof dependency; its intended
use is included in the proof docstring, and it is not needed to state this item.

Edge cases checked before drafting:

- I = bottom: completions identify with the original rings; an etale identity
  neighbourhood R' = R realizes φ, without assuming global etaleness of D/A.
- I = top: the etale-away hypothesis is global; all completions and quotient
  rings in the conclusion are zero rings. R' may be the zero algebra, which is
  etale and finitely presented. The statement does not exclude it.
- Nilpotent I: the complement is empty, and completion is the original ring;
  again the identity neighbourhood realizes the map.
- Zero A, D, or R is allowed. No `Nontrivial` binder has been introduced.
  The existence of φ encodes any obstruction to maps out of the zero ring.
- n = 0: both quotient rings are zero, consistently with the inverse-limit
  indexing. n = 1 includes exactly the first nontrivial residue comparison.
- No perfectness, locality, henselianness, or characteristic restriction occurs.
- A, D and R use independent universes u, v and w. Prime tests occur in D's
  own spectrum, so the etale hypothesis cannot become vacuous by a test-object
  universe restriction.

Searches performed with the prescribed msearch.py wrapper:

- LeanFinder query: “A homomorphism of adic completions of algebras etale away
  from an ideal is realized by an etale finitely presented neighbourhood
  inducing an isomorphism modulo the ideal”. Eight hits: standard-etale lifts,
  `Algebra.IsEtaleAt`, `Algebra.exists_etale_of_isEtaleAt`, and localization
  etaleness. None states the required completion realization.
- LeanSearch query: “Homomorphism between adic completions of algebras etale
  outside an ideal descends to an etale neighbourhood of the target”. Eight
  hits: completion constructors, liftRingHom/liftAlgHom and their evaluation
  lemmas. No realization theorem.
- Loogle query: `AdicCompletion, Algebra.Etale`. Zero hits.
- Mathlib grep query: `etale.*completion|completion.*etale|def mapAlgHom`,
  RingTheory. Six hits, all unrelated maps for ideals, power series, roots,
  and residue fields. No match.
- Direct rg in `lean/WeilConjectures` and `lean/Sheaf` for completion/etale
  combinations found henselization-completion comparisons and geometric
  approximation results, not this theorem. In particular
  `RelativeCompletionEtaleApproximation` and `EtaleCompletionCongruence` have
  different inputs and conclusions. The source's completion comparison
  interfaces use quotient-coordinate characterizations, as this statement does.
- Exact node-id grep in `lean/WeilConjectures`, and declaration-name searches
  in both source trees and `dag/lean_names_upstream.json`, found no match.
  No existing declaration states the item.

No STATEMENT-DISPUTED issue or node fault was found. The source and the node
agree, including the absence of a henselian assumption on R.

Validation: the prescribed scompile.py successfully compiled the file in
sandbox mode and library mode, with no diagnostics (1.6 seconds each).

## Second reading by Q142

Author's second reading, not an independent review: I reopened the node and
compared its statement to the compiled signature. The hypotheses A Noetherian,
I arbitrary, D finite type, R Noetherian, etale outside V(I), and arbitrary
A-algebra map φ are all present. The output has an etale finitely presented
R-algebra, its structural j, an A-map u, bijectivity of the canonical quotient
map, and the full completion equality on all coordinates. I checked that the
quotient domain is R/IR, not A/I, that the etale test excludes primes lying
over V(I), and that successive extension of I equals IR'. The coordinate
formulation quantifies x in the whole D-completion, not only images of D.
No mismatch or correction was found. The maintainer supplies the independent
review required for direct remote delivery.
