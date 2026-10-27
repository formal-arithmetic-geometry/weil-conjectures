## Worker report

The module `Sheaf.RingTheory.FinitePolynomialSimplicialResolution` states
`Algebra.CotangentResolution.exists_finite_polynomial_simplicial_resolution`, with
one `sorry` and no new definitions. Only the item's `lean` field changes.
The accepted stage-1 split, including its explicit compatible-degeneracy repair,
is preserved verbatim. The inherited BLOCKED ending concerned stage 1, not this
stage-2 statement: brief-stage2 §0 expressly permits this stage handoff, and the
current queue lists this node at stage 2 without a Lean record. There is no
released repair note for this item.

Sources read: `cotangent.tex`, proposition-polynomial (08PX), its proof, and
remark-resolution (08QI). The proposition gives finite polynomial terms and a
trivial Kan augmentation; the remark gives the equivalent additive
quasi-isomorphism characterization. The module's docstring carries every step
of the accepted proof, including the finite matching-algebra and split
polynomial attachment nodes, stabilization, and the two homotopy comparison
nodes. It makes no assertion that the proof is completed.

Hypothesis and clause correspondence:

- The commutative rings A and B and their algebra structure are the endpoints
  and arrow of `f : Arrow CommRingCat.{u}`. Thus `f.hom.hom` is the actual
  structure ring homomorphism, without replacing it by an arbitrary auxiliary map.
- A is Noetherian: `[IsNoetherianRing f.left]`.
- B is finite type as an A-algebra: `_hf : RingHom.FiniteType f.hom.hom`.
  This uses the dependency's recorded ring-map interface directly.
- Existence of an augmented simplicial A-algebra over B:
  `∃ Q : Augmentation f`. Its `algebra` is a `SimplicialObject CommRingCat`,
  its natural transformation `base` supplies the compatible A-algebra structures,
  its natural transformation `augmentation` supplies maps to B, and `triangle`
  identifies their composite with the specified map f in every degree.
- It is a polynomial resolution in the dependency's precise sense:
  `IsPolynomialResolution Q`. This is the existing definition, not a copy.
- In each degree the polynomial ring has finitely many variables:
  `∀ n : ℕ, ∃ (r : ℕ) (e : CommRingCat.of (MvPolynomial (Fin r) f.left)
  ≅ Q.algebra.obj (op ⦋n⦌)), ...`.
  The equation `∀ a : f.left, e.hom (MvPolynomial.C a) =
  Q.base.app (op ⦋n⦌) a` makes this a polynomial presentation over A,
  rather than just an isomorphism of the underlying rings.
- Each augmentation is onto: the second conjunct of
  `IsPolynomialResolution Q` is
  `∀ n : ℕ, Function.Surjective (Q.augmentation.app (op ⦋n⦌))`.
- Alternating additive complex, term in degree -n, zero positive terms, and
  augmentation to B[0] a quasi-isomorphism: the last conjunct is
  `QuasiIso (additiveAugmentation Q)`. Reading the recorded definition shows
  it forgets to additive groups, takes the alternating face map complex and
  its canonical augmentation, and extends along `embeddingDownNat`.
  Mathlib's `AlternatingFaceMapComplex.objD` is exactly
  `∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • X.δ i` from degree n+1 to n.
  `ComplexShape.embeddingDownNat` sends n to -n; extension inserts zero
  objects at positive integer degrees, without a sign change in these maps.
- No uniform bound on ranks and no eventual vanishing are asserted:
  `r` is quantified inside `∀ n`; there is no boundedness or truncation clause.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (and its ideal-FG
  characterization read to confirm the node's meaning).
- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType`; the definition is
  `Algebra.FiniteType` for the ring map's induced algebra. The finite polynomial
  surjection equivalence `Algebra.FiniteType.iff_quotient_mvPolynomial''` was
  also read.
- `Mathlib.AlgebraicTopology.SimplicialObject.Basic`:
  `CategoryTheory.SimplicialObject`, its faces `δ` and degeneracies `σ`.
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`, with coefficient map
  `MvPolynomial.C`; its universal property in `MvPolynomial.aeval` and
  `MvPolynomial.algHom_ext` was read as well.
- `Sheaf.RingTheory.CotangentResolutionCoherence`:
  `Algebra.CotangentResolution.Augmentation`, `IsPolynomialResolution`,
  `additiveAugmentation`, and `negativeComplex`. These are the relevant
  declarations explicitly listed by `def-trf-cotangent-resolution-data`.
  Neither a coherence datum nor a derived-category structure is assumed by
  this theorem.
- Proof-only imports, with their full recorded signatures and docstrings read:
  `Sheaf.AlgebraicTopology.TrivialKanFibration` /
  `SSet.Enhanced.trivialKanFibration`;
  `Sheaf.Paper.TrivialKanHomotopyEquivalence` /
  `SSet.exists_section_homotopy_equivalence`;
  `Sheaf.AlgebraicTopology.SimplicialAbelianSetHomotopyQuasiIso` /
  `AlgebraicTopology.quasiIso_alternatingFaceMap_of_underlying_homotopy_equivalence`.
  The two new stage-1 matching/attachment proof dependencies have no recorded
  Lean modules at this time, so there is no module for them to import.

Edge cases checked before writing: n=0 is included, with the augmentation on
degree-zero homology rather than any spurious positive-degree condition.
r=0 is allowed (`Fin 0` is empty). No `Nontrivial` assumption excludes zero
rings, including the zero target of a nonzero base. When B=A, a constant
augmentation with zero-variable polynomial terms illustrates the statement:
the unnormalized constant alternating complex has identity maps in positive
even chain degrees and zero maps in positive odd ones, and still resolves A.
There is no accidental demand that those negative cochain terms vanish.
There is no independent test-object universe producing a vacuous condition:
the base, target, and simplicial terms are in `CommRingCat.{u}`; input rings
can be considered in their common maximum universe. `Fin r` has no size
restriction on r and its polynomial ring lies in that same universe.

Searches for an existing statement (2026-10-23):

- `msearch.py ... leanfinder` with query
  `Every finite type algebra over a Noetherian ring has an augmented simplicial resolution by polynomial algebras in finitely many variables in each degree`:
  eight hits, including `Algebra.FinitePresentation.of_finiteType`,
  `RingHom.FinitePresentation.of_finiteType`,
  `Algebra.FiniteType.exists_fgAlgCatSkeleton`, and
  `Algebra.Presentation.exists_presentation_fin`. These give finite presentations
  or skeleton representatives, not simplicial resolutions.
- `msearch.py ... leansearch` with query
  `A finite type algebra over a Noetherian ring admits a simplicial polynomial resolution with finitely many variables in each degree`:
  eight hits, including `MvPolynomial.isNoetherianRing`,
  `Algebra.FiniteType.isNoetherianRing`,
  `Algebra.FiniteType.iff_quotient_mvPolynomial`, and finite-presentation facts;
  none is the requested existence theorem.
- `msearch.py ... loogle` with query `"simplicial", MvPolynomial`: zero hits.
- `msearch.py ... grep` with query
  `simplicial.*polynomial|polynomial.*resolution|resolution.*polynomial`:
  zero Mathlib hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `IsPolynomialResolution|lem-sfb-finite-polynomial-simplicial-resolution|finite_polynomial_simplicial|exists_finite_polynomial`:
  only the cotangent-resolution definition and its users (injective standard
  quotients, sheaf models, and Tor-independent base change); no finite
  polynomial simplicial resolution existence statement or conflicting name.
- `grep -rn` for the item's exact id in `lean/WeilConjectures`: zero hits.

Validation: `scompile.py NM lem-sfb-finite-polynomial-simplicial-resolution`
compiled the delivered module successfully against the live server, both in
its sandbox check (5.3 seconds) and with its library module name (2.7 seconds),
with no errors or warnings. Auto-bound implicits are disabled in the file.
No new nodes, dependency repairs, statement changes, or statement disputes.

## Second reading by NM

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
