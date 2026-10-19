## Worker report

Stage 2, Q54, 2026-10-19. The module
`Sheaf.RingTheory.FlatAlgebraEtaleProjectiveNeighborhood` states
`Algebra.exists_etale_projective_neighborhood` with one `sorry` and defines the
canonical auxiliary `Ideal.Fiber.mapOfPrimeSquare` with real data. The node changes
only in `lean`. No definition node, dependency repair, or statement correction is needed.

The previous worker's stale-dispatch diagnosis concerned Q56's stage-1 delivery.
The current node has a reviewed stage-1 split but no Lean record; Q56's report explicitly
says “Stage 1 only”. This delivery performs stage 2 and does not resplit the item.

Clause-by-clause correspondence:

- Commutative rings and the map R → S: `(R : Type u) (S : Type v)`, `[CommRing R]`,
  `[CommRing S]`, and `[Algebra R S]`, whose ring map is `algebraMap R S`.
- Flatness: `[Module.Flat R S]`, the module definition underlying `RingHom.Flat`.
- Finite presentation as an algebra: `[Algebra.FinitePresentation R S]`; there is no
  finite-presentation hypothesis as an R-module.
- The marked prime q and its inverse image p: `(p : PrimeSpectrum R)` and
  `(q : PrimeSpectrum S)` with `hpq : PrimeSpectrum.comap (algebraMap R S) q = p`.
  This introduces p by its required inverse-image equality, without restricting q.
- The new commutative rings and ring maps: existential `R'`, `S'`, their `CommRing`
  structures, and `Algebra R R'`, `Algebra S S'`, `Algebra R' S'` structures.
  `hcomm` is exactly the equality of the two composites R → S'. No cartesian-square
  or extra scalar-tower hypothesis is imposed.
- New marked primes: existential `p' : PrimeSpectrum R'`, `q' : PrimeSpectrum S'`.
- Clause (1): the first two conjuncts are `AlgebraicGeometry.Etale` of the spectrum
  maps of `algebraMap R R'` and `algebraMap S S'`.
- Clause (2): the existential proof witnesses `hp`, `hq`, and `hpq'` assert respectively
  p' over p, q' over q, and q' over p'. These witnesses are part of the conclusion,
  not hypotheses on the original rings.
- Clause (3): the next two conjuncts require `Function.Bijective` of the actual
  induced `Ideal.ResidueField.map` for R → R' and S → S'. A bijective ring map is
  precisely an isomorphism of these fields. The contraction proofs are extracted
  from `hp` and `hq` using `congrArg PrimeSpectrum.asIdeal`.
- Clause (4): `Algebra.FinitePresentation R' S' ∧ Module.Projective R' S'`.
  There is no `Module.Finite R' S'` or finite-rank conclusion.
- The two fibre rings are `p.asIdeal.Fiber S` and `p'.asIdeal.Fiber S'`, Mathlib's
  κ(p) ⊗[R] S and κ(p') ⊗[R'] S'. The standard tensor swap identifies these with
  the source's S ⊗[R] κ(p) and S' ⊗[R'] κ(p'), carrying all the displayed maps.
- The induced fibre map is the explicit helper `Ideal.Fiber.mapOfPrimeSquare`.
  Its data are `Algebra.TensorProduct.mapRingHom` for R → R', the canonical
  residue-field map, and S → S', with compatibility supplied by
  `Ideal.ResidueField.map_algebraMap` and `hcomm`. It sends λ ⊗ s to κ(a)(λ) ⊗ b(s).
  There is no arbitrary map or existence-based choice in the definition.
- The penultimate conjunct asserts that this canonical fibre map has étale spectrum map.
- The final equality contracts the prime
  `PrimeSpectrum.preimageOrderIsoFiber R' S' p' ⟨q', hpq'⟩` along that fibre map
  to `PrimeSpectrum.preimageOrderIsoFiber R S p ⟨q, hpq⟩`, exactly the requested
  correspondence under the dependency node's recorded order isomorphism.

Dependency declarations read and used:

- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, defined using `Module.Flat`;
  `Mathlib.RingTheory.Flat.Basic`: `Module.Flat`.
- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.Algebra.Module.Projective`: `Module.Projective`.
- `Mathlib.RingTheory.LocalRing.ResidueField.Fiber`: `Ideal.Fiber` and
  `PrimeSpectrum.preimageOrderIsoFiber`, whose toEquiv is `preimageEquivFiber`.
  Its inverse contracts along `Algebra.TensorProduct.includeRight`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`;
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`: `Ideal.ResidueField`,
  `Ideal.ResidueField.map`, and `Ideal.ResidueField.map_algebraMap`.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`;
  `Mathlib.RingTheory.TensorProduct.Maps`: `Algebra.TensorProduct.mapRingHom`.

Proof-only imports cover the published interfaces for affine fibre products,
étale and flat base change and cancellation, finite-presentation base change and
composition, étale-implies-flat, localization of finite presentation, principal open
immersions, and `IsLocalization.prime_localRing_residueField_iso` from
`Sheaf.RingTheory.LocalizationPrimeResidueFieldIso`.
The two newly split complete-dévissage theorem nodes have no Lean modules yet and
are not imported; their eight-step use remains recorded in the theorem docstring.
They are proof dependencies, not missing notions in this statement.

Source checks: read local `literature/stacks-project/flat.tex`,
`proposition-finite-presentation-flat-at-point` (Tag 05ID, lines 3287 onward) and
`lemma-weak-bourbaki-pre` (Tag 05IG, lines 3750 onward). The former provides the
elementary étale neighborhoods and projectivity of structure-sheaf sections.
The latter supplies the fibre refinement; the node already corrects its printed
κ(q') to κ(p'). The theorem docstring carries all eight proof steps of the current
node, including how finite algebra presentation and flatness over R' are obtained.

Edge cases checked before drafting: a zero ring S admits no prime q, so the theorem
does not invent a point on its empty spectrum. The contraction of a prime also
ensures the relevant base residue fields exist. Identity maps of fields admit the
identity neighborhood and fibre map. Polynomial algebras such as k[x] over k may
have infinite module rank, which is allowed because only projectivity is concluded.
No Noetherian, field, domain, characteristic, or module-finiteness assumption appears.
The original ring universes u and v are independent; each neighborhood is chosen
in the universe of its original ring (étale algebras are finitely presented), and
the fibres have universe max u v. The helper permits four independent universes.
Both auto-implicit options are false, and all universes and variables are explicit.

Searches:

- `msearch.py` LeanFinder: “A flat finitely presented algebra admits pointed etale
  neighborhoods where it is projective over the new base”: eight hits, including
  `Algebra.exists_etale_of_isEtaleAt`, smooth-coordinate and étale finite-presentation
  results. None produces the two pointed neighborhoods with projectivity.
- `msearch.py` Loogle: `Algebra.Etale, Module.Projective`: zero hits.
- `msearch.py` grep, Mathlib RingTheory:
  `[Ee]tale.*[Pp]rojective|[Pp]rojective.*[Ee]tale`: zero hits.
- `rg` over `lean/Sheaf` and `WeilConjectures/` for the item id and the concepts
  flat/algebra/étale/projective/neighborhood found only the downstream proof-plan
  citation in `WeaklyAssociatedTensorFlatFinitePresentation.lean` and different
  finite-projective lifting or local-freeness results. No duplicate statement.
- `rg` over Mathlib, upstream `WeilConjectures/`, and `lean/Sheaf` for
  `mapOfPrimeSquare|exists_etale_projective_neighborhood`: no matches.
- The existing DAG searches recorded by Q56 also distinguish finite presentation
  as a module (`Module.Flat.projective_of_finitePresentation`) from the item's
  finite presentation as an algebra. The upstream name index supplied no match.

Validation: the prescribed `scompile.py` compiled this file as a sandbox module in
2.9 seconds and as its library module in 3.1 seconds, with no errors or warnings.
No `STATEMENT-DISPUTED` issue or node fault was found.

## Second reading by Q54

Self-check only: this dispatcher brief assigns independent review to the maintainer
and forbids starting another agent. I reopened the node and the compiled module and
matched the hypotheses and every numbered and final clause as listed above.
In particular the residue-field maps are the induced maps, the square is not assumed
cartesian, the fibre map is constructed, and the fibre prime uses the recorded
Mathlib correspondence. The statement and all existing node fields are preserved.
The maintainer's independent reading remains the delivery review.
