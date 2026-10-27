## Worker report

The module `Sheaf.AlgebraicGeometry.RationalPointTangentUnramified` states
`AlgebraicGeometry.rationalPoint_tangent_unramified`, with `sorry` as its whole proof.
No definitions, extra nodes, dependency repairs, or statement corrections are needed.

Hypothesis and conclusion correspondence:

- The arbitrary field is `(k : Type u) [Field k]`; the scheme and its specified
  structure map are `(Z : Scheme.{u}) (p : Z ⟶ Spec (.of k))`.
- Local finite type is `[LocallyOfFiniteType p]`. This does not require quasi-compactness.
- The rational section is `(x : Spec (.of k) ⟶ Z)` with
  `(hx : x ≫ p = 𝟙 _)`. In diagrammatic composition this is precisely `p ∘ x = id`.
- Its image `w` is written explicitly throughout as `x (IsLocalRing.closedPoint k)`.
  The source spectrum is a singleton, so this is its image point, without an extra
  choice or point hypothesis.
- Closedness is `IsClosed ({x (IsLocalRing.closedPoint k)} : Set Z)`.
- The structural residue map is the `.hom` of the composite
  `StructureSheaf.toStalk k (p w) ≫ p.stalkMap w ≫ Z.residue w`.
  This is the canonical map from constants through the base stalk and the local
  homomorphism, then to the residue field, as in the recorded cotangent duality.
  `∃ e : k ≃+* Z.residueField w, e.toRingHom = ...` states that this very map
  is an isomorphism, rather than the existence of an unrelated field isomorphism.
- Its inverse is fixed by
  `e.symm.toRingHom = (Z.descResidueField (Scheme.stalkClosedPointTo x)).hom`.
  The right side is the residue map induced by the section's local stalk map,
  followed by the canonical identification of the local ring of `Spec k` with `k`.
- Unramifiedness at `w` is exactly
  `∃ U : Z.Opens, w ∈ U ∧ IsUnramified (U.ι ≫ p)`.
  This uses the recorded dependency, whose definition is the conjunction of local
  finite type with an open-immersion diagonal. It is the neighbourhood meaning
  required by the node, not merely formal unramifiedness of an abstract stalk.
- The final `↔ Subsingleton (schemeTangentSpace k Z p w)` expresses the zero
  vector space. The recorded tangent space has its canonical additive group,
  in particular zero, so subsingleton is equivalent to every vector being zero.
- There is no algebraic-closedness, flatness, separatedness or global finite-type
  hypothesis. The common universe is the existing scheme/tangent-space API's
  universe, admitting arbitrary field and scheme sizes after a common lift.

Recorded statement dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  full signatures and docstrings at Scheme.lean:35–78 were read.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`, the affine-local finite-generation class.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`; also the canonical `Scheme.descResidueField`.
  Their full definitions/docstrings were read, together with
  `Mathlib.AlgebraicGeometry.Stalk`'s `Scheme.stalkClosedPointTo`.
- `Sheaf.AlgebraicGeometry.UnramifiedMorphism`: `AlgebraicGeometry.IsUnramified`.
- `WeilConjectures.AlgebraicGeometry.SchemeTangentSpace`:
  `AlgebraicGeometry.schemeTangentSpace` and its canonical group/module structures.

Proof-only imports are
`Sheaf.AlgebraicGeometry.RationalTangentCotangentDuality`,
`Mathlib.LinearAlgebra.Dual.Lemmas`, and
`Sheaf.AlgebraicGeometry.RationalUnramifiedCotangentCriterion`.
Their recorded declarations and docstrings were read. The stalk composition
proof dependency is already available from the publicly imported Mathlib Scheme
module (`Scheme.Hom.stalkMap_comp`, and `germ_stalkMap`).
`lem-trf-finite-residue-tower-local-geometry` currently has neither a Lean record
nor a Mathlib match, so no import exists for that proof-only dependency; the
complete step using it remains in the theorem docstring for stage 3. It is not
needed to type the statement and is not restated in this delivery.

Source checks: read Stacks varieties.tex at
`lemma-injective-tangent-spaces-unramified` (0B2G), schemes.tex at
`lemma-characterize-points` and its residue-field diagram (01J9), and morphisms.tex
at `lemma-algebraic-residue-field-extension-closed-point-fibre` (01TE).
The theorem docstring records all three node proof steps, including the finite
residue tower specialization and both cotangent comparison lemmas.

Edge cases checked mathematically before writing:

- `Z = Spec k`, identity section: closed point, identity residue maps, zero tangent
  space and unramified identity satisfy all conclusions.
- The origin in `A¹_k`: rational closed point with residue `k`; tangent dimension
  one makes both sides of the unramified/zero-tangent equivalence false.
- `Spec(k[t]/t²)` at its section: the nonzero tangent space detects ramification
  in every characteristic, including characteristic two.
- An arbitrary infinite disjoint union of copies of `Spec k`: local finite type
  holds without global finite type; any section point satisfies the statement.
- Empty `Z` and `Spec L` for a proper extension `L/k`: the requisite section does
  not exist; no nonexistent rational point is silently asserted.
- A nonseparated example such as the affine line with doubled origin is allowed;
  its section points are still closed, with the expected nonzero tangent spaces.

Existing-declaration searches (2026-10-24):

- `msearch.py ... leanfinder` with query "For a locally finite type scheme over a
  field a rational point is closed and has zero tangent space if and only if the
  structure morphism is unramified at the point": eight hits, including
  `AlgebraicGeometry.FormallyUnramified`, `Algebra.unramifiedLocus`, and the
  closed-point/fromSpecResidueField criteria, but no exact combined statement.
- `msearch.py ... loogle '"AlgebraicGeometry", "tangent"'`: zero hits.
- `msearch.py ... grep 'tangent.*unramified|unramified.*tangent|rational.*closed'
  AlgebraicGeometry`: zero hits.
- Local `rg` of the project under both `lean/WeilConjectures` and `lean/Sheaf`
  for rational points and tangent/unramified combinations found tangent-cotangent
  duality, the rational cotangent criterion, a finite-flat criterion, and the
  geometric-fibre criterion. Each concerns different hypotheses or conclusions;
  none states this rational-section lemma. Searching the exact item id under
  `lean/WeilConjectures` found nothing.
- The new declaration name was searched in both project roots and no collision
  was found. Raw wrapper search results remain in sandbox `searches.jsonl`.

Validation: the delivered module passed `scompile.py` against the live published
library, in module mode with the final imports, without errors or warnings.
There are no disputed statements or known node faults.

## Second reading by Q31

A separate self-review pass reopened the node and the completed file and compared
all binders and conjuncts. No other worker was started, as the dispatch brief
explicitly prohibits other agents; the maintainer performs the independent review.
The field, locally finite type structure map, rational section identity, and image
point match directly. The first conjunct is global closedness. The second fixes
both the forward structural residue map and the inverse induced by the section;
thus the inverse clause is not lost in a bare bijectivity assertion. The last
conjunct is a neighbourhood predicate using the actual dependency `IsUnramified`
and is equivalent to subsingleton of the actual dependency tangent space.
Subsingleton is the correct zero-vector-space assertion, not categorical `IsZero`
on a type. No hypotheses or conclusions were added or omitted, and no extra
definition or correction resulted from this pass.
