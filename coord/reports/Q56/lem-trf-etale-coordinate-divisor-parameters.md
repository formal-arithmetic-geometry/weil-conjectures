## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleCoordinateDivisorParameters` states
`AlgebraicGeometry.etale_coordinate_divisor_parameters`, with proof `sorry`.
Its only helper, `AlgebraicGeometry.etaleCoordinateGermMap`, constructs the actual ring map
`(h.stalkMap w).hom.comp (StructureSheaf.toStalk C (h w)).hom`.
There are no new nodes, dependency repairs or statement corrections. The item JSON changes
only `lean`. The helper belongs to the affine germ construction in this same statement;
it introduces no alternative parameter, Cartier or strict-henselization definition.

Hypotheses and clauses, matched against the node:

- Commutative Noetherian regular C: `{C : Type u} [CommRing C] [IsRegularRing C]`.
  Mathlib's regular-ring class includes `IsNoetherianRing C`; no nonzero-ring or local-ring
  assumption is imposed on C. `U` is literally `Spec (.of C)` throughout.
- Indexed list of arbitrary length r >= 0: `(r : ℕ) (z : Fin r → C)`, permitting `r=0`.
- At every y the vanishing members occupy distinct positions in a full regular parameter
  system: `hcoord` gives a list `t`, its recorded `IsRegularSystemOfParameters` predicate,
  and an injective map from the subtype of nonunit indices to `Fin t.length`, with the
  corresponding `t.get` equations. A local-ring germ has zero residue precisely when
  it is a nonunit. Indexing by a subtype retains repeated labels and rules out collisions
  of positions, rather than forgetting them by taking a set of coordinate values.
- P is the product, including the empty product 1: the explicit `∏ j : Fin r, z j`.
  D is not a freely chosen divisor: `hD` identifies it with `ofIdealTop` of the principal
  ideal of that product, transported by the canonical `ΓSpecIso.inv`. Introducing D with
  this equality is the explicit Lean rendering of the node's "put D=V(P)".
- Multiplication by P on C is injective: the first `Function.Injective` clause.
- Every etale morphism, including identity: the universal `(W) (h)` and `Etale h →`.
  Neither nonemptiness, affineness, nor a covering condition on W is assumed.
- W regular and locally Noetherian: `IsRegularScheme W`, definitionally the conjunction
  `IsLocallyNoetherian W ∧ IsRegular W` from the recorded dependency.
- Every chosen full system pulls back to a full system: for every w and every parameter
  list t satisfying the base parameter predicate, the list `t.map (h.stalkMap w).hom`
  satisfies that same recorded predicate in W's stalk. The explicit existential witness
  hN supplies its Noetherian instance, not an extra hypothesis.
- Exact nonunit equivalence: the universal `j` clause compares `etaleCoordinateGermMap`
  with `StructureSheaf.toStalk C (h w)` using the stated iff of nonunit predicates.
- Same distinct positions: for every base full parameter system t and every injective
  marking f with the base `t.get` equations, the image list has the same `f j` positions.
  `Fin.cast (List.length_map ...).symm` only identifies the equal list lengths. Together
  with the preceding transport clause and the marking existence in hcoord this gives
  marked full systems in W, with precisely the original distinct positions.
- Unit times the marked germs: `∃ v : (W.presheaf.stalk w)ˣ` followed by equality of the
  actual pulled product with `v * ∏ j : {j // ¬ IsUnit (base germ)}, pulled germ (z j)`.
  In particular the expression multiplies exactly the marked parameters, and no unit
  coordinates are counted as branches.
- Multiplication by h*P in every local ring is injective: the final `Function.Injective`
  in the pointwise clause.
- The pullback divisor is effective Cartier and normal crossings: the explicit
  `(D.comap h).IsInvertible` and `(D.comap h).IsNormalCrossingsDivisor` clauses, using
  precisely the recorded dependency definitions. Identity h gives both assertions on D.
- Geometric branches: for every w, K, H and every
  `Algebra.StrictHenselizationPresentationIn.{u,v} (W.presheaf.stalk w) K H`, the subtype
  of `minimalPrimes` of `H ⧸ (Ideal.span {image of h*P}).radical` is equivalent to the
  finite subtype of base nonunit indices. An equivalence under `Nonempty` asserts exact
  finite cardinality, including cardinality zero; it does not choose branch labels.
  Quotienting H by the radical is canonically the reduction of H/(h*P). For points on
  the divisor, strict henselization commutes with this quotient, as in proof step 6 and
  `lem-trf-parameter-product-strict-local-branches`; hence this is exactly the node's
  reduced strict henselian local ring of the divisor. Off it the unit ideal gives the
  zero ring, with no primes. K is any separable closure of the residue field, and H and
  all pointed etale algebras may live in any universe `max u v`, never below the stalk.
  Thus the assertion includes every geometric choice and every etale neighborhood.
- Branch bound and independence: the equivalence identifies branch cardinality with
  the same subtype `{j : Fin r // ¬ IsUnit (base germ at h w)}` for every h and every K,H.
  The next `Nat.card ... ≤ r` clause states its bound explicitly. Independence is the
  common right-hand side for maps with the same base point, rather than a choice of
  coordinates or of an etale neighborhood.
- r=0: the last implication states the product equals 1 and `IsEmpty (D.comap h).subscheme`.
  It also applies to D itself via the identity. The strict-local equivalence has an empty
  right-hand side, forcing no minimal primes in all the corresponding reduced quotients.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (also a superclass of regularity).
- `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularRing`, `IsRegularLocalRing`;
  `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`.
- `WeilConjectures.RingTheory.IsRegularSystemOfParameters`:
  `IsLocalRing.IsRegularSystemOfParameters`, with maximal-ideal span and length/dimension.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian` and
  the existing Noetherian-stalk instance.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`:
  `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible`, locally regular-principal ideals.
- `Sheaf.AlgebraicGeometry.NormalCrossingsDivisor`:
  `AlgebraicGeometry.Scheme.IdealSheafData.IsNormalCrossingsDivisor`.
- `Sheaf.RingTheory.StrictHenselizationPresentationIn`:
  `Algebra.StrictHenselizationPresentationIn`, with the full pointed-etale diagram,
  universal cocone and specified algebra identification, not an arbitrary henselian ring.
- The recorded proof dependency
  `WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence` is a plain import;
  its `IsRegularLocalRing.isRegular_and_quotients_of_generators` gives regularity of every
  permutation. `RingTheory.Sequence.IsRegular` is provided by its Mathlib proof imports.
  The other two theorem proof dependencies, `lem-trf-etale-coordinate-intersection-geometry`
  and `lem-trf-parameter-product-strict-local-branches`, have no recorded declaration in the
  read DAG and are not imported. Neither supplies an object needed to type this statement.
  Their intended uses are retained in the six-step theorem docstring and unchanged DAG proof.

Sources opened: Stacks `more-algebra.tex`, `lemma-dimension-etale-extension` (07QP) and
`lemma-regular-etale-extension` (0AH0); `algebra.tex`, `lemma-etale-at-prime` (00U4) and
`definition-regular-local` (00KU); ILO PDF pages 124--125, printed pp. 118--119, containing
4.1.6, 4.1.8 and the normal-crossings discussion. The supplied CompactObject example is
withdrawn; I also read its current upstream counterpart recorded by its node.

Edge cases checked: C the zero ring (empty Spec and injective multiplication on a singleton);
r=0 (empty coordinate family and divisor); all coordinates units at a point (no branches);
dimension-zero stalks (only the empty parameter list); empty or non-affine W; h the identity;
repeated coordinate labels (distinct positions must still be supplied whenever they vanish);
units among the coordinates; arbitrary residue characteristic and arbitrary allowed universes.
No disputed statement or source mismatch was found.

Searches for existing statements and notions:

- `msearch.py` LeanFinder: "Etale pullback preserves marked regular parameters and a product
  defines a normal crossings Cartier divisor with the same number of geometric branches".
  Eight results: standard-etale maps, etale base change and etale loci; no exact statement.
- `msearch.py` Loogle: `Algebra.Etale, IsRegularLocalRing`: zero hits.
- `msearch.py` grep: `IsRegularSystemOfParameters|[Ee]tale.*[Rr]egular|[Rr]egular.*[Ee]tale`
  in Mathlib RingTheory: zero hits.
- `msearch.py` LeanSearch: "A product of distinct local regular parameters defines a normal
  crossings effective Cartier divisor preserved by etale base change": eight results on
  etale base change, field products and maximal spectra; no match.
- `rg` in `lean/WeilConjectures`: regular parameter systems, etale regularity, the special
  regular-divisor base-change theorem, and local-dimension lemmas. None states the marked
  coordinate-product theorem with geometric branch count. Searching the exact item id
  there returned no result; searching the final declaration names in Mathlib, upstream
  and `lean/Sheaf` returned no pre-existing declaration.
- `rg` in `lean/Sheaf`: found the existing normal-crossings definition and its branch-count
  chart definition (read in full), and downstream coordinate blowup and maximal-stratum
  statements. They specialize to blowup charts or contain other conclusions and do not
  supply this theorem. I use the recorded normal-crossings definition and the ordinary
  `minimalPrimes` interface directly, with no new branch-count definition. The principal
  ideal is built inline with `ofIdealTop`; no copy of a principal-divisor definition is made.

Compilation: the prescribed scompile wrapper's initial local attempt reported disk space
exhaustion, then its automatic server fallback successfully elaborated the full module.
The sole style warning about global `open Classical` was repaired with `open Classical in`
on the theorem. Final clean compilation and delivery preflight are recorded below.

## Second reading by Q56

A separate reading pass by this worker, with the full node JSON and Lean file open, checked
all the clauses listed above. The dispatcher forbids other agents; no independent sub-agent
reading is claimed here. The maintainer's independent review will read this delivery.
The pass checked especially that the arbitrary full parameter system is quantified (not
only one existential system), that marking positions retain indices, that the unit equation
uses exactly the nonunit subset, and that the strict-local clause is a genuine universal
presentation in a containing universe. The quotient by the radical computes the reduction,
and an equivalence to the finite index subtype guarantees finiteness even in the zero-count
case. It also checked that the pulled equation is the image under the actual stalk map and
that the equality hD fixes the original divisor. No mathematical change to the DAG or to
the statement was needed. The only compiler correction was scoping Classical locally.

Final validation: scompile.py passed on the current server source in 2.3 seconds with no
warnings. deliver2.py --no-push reported `OK (dry run)`: the complete packet passes the
maintainer preflight and both sandbox/library compilation. Original node fields were also
compared structurally and are unchanged outside lean.
