## Worker report

The module `Sheaf.AlgebraicGeometry.InvariantIntersectionAffineDescent` states
`AlgebraicGeometry.invariant_intersection_affine_descent`, with one postponed theorem
proof (`sorry`). Its helper definitions construct the overlap morphism from the existing
transport datum, the tensor product with C in the second position, pure tensors, the tensor
swap, the canonical second comparison, the actual affine model Spec C over Spec A, and the
canonical affine overlap identification. No auxiliary theorem or object is chosen by sorry.
The node's statement, proof, dependencies and other fields are unchanged.

Source read: `literature/stacks-project/more-groupoids.tex`, lemma-affine-base-change (0APJ),
and lemma-ind-quasi-affine (0APK), including the displayed section-ring comparisons and
omitted cocycle paragraph. The source's displayed arrow is the inverse of the comorphism
used in this node; the formal statement follows the node's consistently reversed orientation.
The affine effectivity input is the recorded Tag 0245 theorem.

Hypothesis-by-hypothesis correspondence:

- Commutative rings and R to A: `{R A : CommRingCat.{u}} (r : R ⟶ A)`.
- X=Spec A, S=Spec R and the given flat surjective p: the two class binders
  `[Flat (Spec.map r)] [Surjective (Spec.map r)]`.
- V over X: `V : Over (Spec A)`, with structure map `V.hom` and total scheme `V.left`.
- Quasi-separatedness of the underlying scheme: `[QuasiSeparatedSpace V.left]`.
- Descent datum in the indicated direction: `D : Over.DescentDatum (Spec.map r) V`.
  This recorded definition's `transport_transport` has 01 followed by 12 equal to 02.
  `invariantIntersectionOverlap` constructs the associated map V times X to X times V
  by pairing the original base coordinate with `D.toHom`.
- E is the intersection of a nonempty set-indexed family of quasi-compact opens:
  `{I : Type v}`, `U : I → V.left.Opens`, `hI : Nonempty I`, and
  `hqc : ∀ i, IsCompact (U i : Set V.left)`.
- Invariance phi(E0)=E1: `hinv` says membership in every first-projection inverse image
  is equivalent to membership of `D.toHom x` in every U i. Since phi is an isomorphism
  (the datum's transport has inverse by the self and cocycle laws), this is exactly
  equality of the image subsets, rather than only forward stability.
- The subspace topology, inverse-image structure sheaf and C are the existing
  `intersectionSections` and `intersectionAlgebraSections` constructions; in particular
  E need not be open. `intersectionScalars V.hom U` is its given A-action. The R-action
  is from `V.hom ≫ Spec.map r`, not an independently supplied algebra structure.

Clause-by-clause correspondence:

- The existential isomorphisms alpha0 and alpha1 have precisely the rings C tensor_R A,
  A tensor_R C and the two actual intersection section rings as their source and target.
- `α0.hom = ... intersectionBaseChangeMap ...` fixes alpha0 to the canonical map of the
  recorded comparison node. That definition is `productMap` of the actual restricted
  comorphism and scalar map, so on c tensor a it is g-sharp(c) times a.
- `α1.hom = intersectionLeftComparison ...` fixes alpha1 to the tensor swap followed by
  that comparison and the actual section comorphism of pullback symmetry. It sends
  a tensor c to a times g-sharp(c), including on empty subsets.
- The equation `ψ.hom ≫ α0.hom = α1.hom ≫ intersectionSectionsMap ...` identifies psi
  with the restricted comorphism, conjugated by the two canonical comparisons.
  The membership proof supplied to `intersectionSectionsMap` is exactly `hinv`.
- The equation quantified over a,b in A sends `a tensor iota(b)` to `iota(a) tensor b`.
  These are the images of all pure tensors in A tensor_R A, so this is precisely
  A tensor_R A linearity. Since psi is a ring isomorphism this makes it the stated
  algebra isomorphism, with no extra assumption of linearity.
- `intersectionBaseChangeNaturality` and `intersectionBaseChangeIteration` retain the
  canonical comparison squares, tensor associators and pure-triple-tensor formula.
- The final witness `F : Over.DescentDatum ... (intersectionAffineModel V U)` states
  the geometric cocycle in the dependency's existing transport form, universally in
  all test schemes. The last equation identifies its overlap morphism, through
  pullback symmetry, `intersectionAffineOverlapIso`, and `Spec.map intersectionTensorSwap`,
  with `Spec.map ψ.hom`. Thus this is the datum theta=Spec psi, not an arbitrary datum
  on Spec C. Full faithfulness and contravariance of Spec translate its cocycle to
  psi02=psi01 composed with psi12 under exactly the canonical iterated tensor/section
  identifications. This avoids introducing a second definition of descent data.
- `F.IsEffective` expands verbatim to an S-scheme Z0, a cartesian square for Spec C,
  and invariance under F's transport. It is equivalent to the requested compatible
  X-isomorphism Z0 times_S X isomorphic to Z (the pullback square gives its inverse).

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, its projections
  and `pullback.lift`; `Mathlib.AlgebraicGeometry.Pullbacks`: scheme pullbacks and
  `pullbackSpecIso`, whose structural projections are the tensor inclusions.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`, with `Flat.iff_flat_stalkMap`;
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `Surjective`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: `QuasiSeparated` and
  `quasiSeparatedSpace_iff_forall_affineOpens` (the underlying-scheme formulation).
- `WeilConjectures.CategoryTheory.Comma.Over.DescentDatum`:
  `Over.DescentDatum`, `.toHom`, `.universalPoint`, `.transport_transport`, `.IsEffective`.
  Read its full transport and effectivity definitions and their equivalence docstrings.
- `Sheaf.AlgebraicGeometry.RingedSubspace`: `LocallyRingedSpace.ringedSubspace`, inclusion
  and unit; `Sheaf.AlgebraicGeometry.IntersectionStructureSections`:
  `Scheme.intersectionInclusion`, `.intersectionStructureSheaf`, `.intersectionSections`,
  `.intersectionRestriction`. The family form is the same inverse-image construction.
- `Sheaf.AlgebraicGeometry.IntersectionSectionsFlatBaseChange`: the recorded canonical
  section maps, algebra sections, scalar tensor/source, base-change comparison,
  naturality and iteration, and `flat_affine_intersection_sections_base_change`.
  This module is public because its canonical constructions occur in the statement.
- Proof imports: `WeilConjectures.AlgebraicGeometry.AffineFlatDescent`, recorded theorem
  `Over.DescentDatum.isEffective_of_isAffineHom_flat_affine`; `Mathlib.RingTheory.RingHom.Flat`,
  `RingHom.Flat.comp`. Other available proof inputs (tensor product universal property,
  `Flat.SpecMap_iff`, stability under base change, affine-spectrum pullbacks,
  `isAffineHom_of_isAffine`) are supplied by these imports and their public dependencies.
- `lem-a1-subspace-ring-restriction-unit-coherence` has no Lean record or Mathlib match
  in this checkout, so no unstated module is imported for this proof-only dependency.
  Its role is spelled out in the theorem's proof docstring. Its general statement is
  not needed to type the item: the canonical subset comorphism is already defined by
  the recorded `intersectionSectionsMap` of the comparison module.

Edge cases checked before completing the signature: E empty and V empty (the section
ring is the zero ring; spectra and overlap identifications remain defined); a singleton
family; repeated opens; non-open infinite intersections; E=V when presented by compact
opens; r the identity; zero rings; arbitrary index universe v independent of u. The
family remains nonempty as required by 0APJ. No nonemptiness of E, nontriviality of rings,
affineness/quasi-compactness of V, or openness of E was added.

Searches for an existing statement and helper notions:

- msearch LeanFinder: “Sections on a descent invariant intersection of quasi compact
  opens induce an effective affine descent datum”; eight unrelated limit-section and
  affine-cover results, no matching construction or theorem.
- msearch Loogle: `AlgebraicGeometry.Scheme, "descent"`; zero results.
- msearch grep: `intersection.*[Dd]escent|[Dd]escent.*intersection` in Mathlib's
  AlgebraicGeometry directory; zero results.
- msearch LeanSearch with the same natural-language query: eight results about descent
  of morphism properties and unrelated section/compactness facts, no matching theorem.
- rg of `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json` for
  `lem-a1-invariant-intersection-affine-descent`, invariantIntersection and
  invariant_intersection: only the different invariant-neighbourhood theorem and its
  parent import. The broader intersection/section search located the recorded comparison
  definitions and the canonical affine embedding, which are reused or distinguished.
  The parent `IndQuasiAffineFpqcDescent` is a different theorem (ind-quasi-affine V);
  it does not supply this invariant-section-ring construction.

No new nodes or dependency repairs were necessary; no statement correction or dispute.

## Second reading by Q78

I reopened the node and signature and checked all hypotheses and clauses above.
This is a self-check, not an independent worker review: the dispatcher explicitly
forbids starting other agents and the maintainer supplies the independent delivery review.
The checks particularly verified the contravariant direction of psi, both A-actions,
that the final F is constrained to Spec psi, and that effectivity includes datum
compatibility. The helper-boundary compiler check found a missing `Hom.mem_preimage`
normalization; explicit scheme/pullback types removed expensive metavariable unfolding.
An unscoped heartbeat option was removed, and the tensor swap was named explicitly
so no local algebra installation is hidden inside the theorem statement. No mathematical
hypothesis or conclusion changed in these typing repairs.

Validation: all compilation uses the prescribed scompile.py against the live build;
final clean per-file compilation and deliver2.py preflight are recorded by the wrappers.
