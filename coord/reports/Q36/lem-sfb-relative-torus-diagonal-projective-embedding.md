## Worker report

The item is stated in `Sheaf.AlgebraicGeometry.RelativeTorusDiagonalProjectiveEmbedding`,
`AlgebraicGeometry.exists_relative_torus_diagonal_projective_embedding`. Its only theorem
proof is `sorry`. There is no statement correction, dependency replacement, or mathematical
dispute. All original fields are retained; `lean` is supplied and `stmt_deps` gains the new
explicit diagonal-action definition. The independent maintainer review is still required.

The source read is Thomason, *Equivariant resolution, linearization, and Hilbert's fourteenth
problem over arbitrary base schemes*, Theorem 3.3 and Corollary 3.4(3), printed p.32, in the
[primary article full text](https://www.researchgate.net/publication/243015730_Equivariant_resolution_linearization_and_Hilbert%27s_fourteenth_problem_over_arbitrary_base_schemes).
The theorem first embeds into a projective vector bundle; the parent node's proof supplies
the split-torus finite-weight enlargement to a free coordinate system. This distinction is
retained in the proof docstring, including the negative sign on the section weights.

Clause-by-clause correspondence:

- A commutative Noetherian ring: `(A : Type u) [CommRing A] [IsNoetherianRing A]`.
  The base is exactly `Spec (.of A)`. No field, domain, reducedness or normality of A
  is assumed.
- Arbitrary rank r, including zero: `(r : ℕ)`.
- The specified split torus and Laurent basis: `DiagonalProjectiveAction.torus A r`
  specializes the existing `ringDiagonalizableGroup A (ULift (Fin r → ℤ))`. Its coordinate
  algebra is `AddMonoidAlgebra A (ULift (Fin r → ℤ))`, with basis
  `AddMonoidAlgebra.single (ULift.up w) 1`. Multiplication adds exponents; the canonical
  Hopf algebra used by `hopfSpec` supplies precisely the stated coproduct, counit and
  antipode. ULift preserves every character and places the finite lattice in A's universe.
  This is the Laurent presentation of the base-changed field torus, rather than using the
  field-only interface of `StandardGroupSchemes.multiplicative` over a general ring.
- An S-scheme with an S-action: `X : CategoryTheory.Mod (Over (Spec (.of A))) (torus A r).X`.
  `X.X` is its underlying scheme over S, `X.X.hom` its structure map, and `X.mod.smul`
  the action. `ModObj.one_smul` and `ModObj.mul_smul` are the unit and associativity
  identities as morphism equalities. Cartesian tensor in `Over S` is the existing fibre
  product, not an independent product construction.
- Separated and finite type: `[IsSeparated X.X.hom]`, `[LocallyOfFiniteType X.X.hom]`,
  and `[QuasiCompact X.X.hom]`. The latter two together are finite type.
- Normal local domains: `hnormal : ∀ p : X.X.left, IsDomain (X.X.left.presheaf.stalk p) ∧
  IsIntegrallyClosed (X.X.left.presheaf.stalk p)`, exactly the recorded inline convention.
- Quasi-projectivity in the stated immersion sense: `hquasiprojective : ∃ (N : ℕ)
  (i : X.X ⟶ space A N), IsImmersion i.left`. An Over morphism already records that i
  commutes with the structure maps. `space A N` is only the Over packaging of the
  existing `Proj.projectiveSpaceOverAffineToSpec (ULift (Fin (N+1))) A`. This is precisely
  Proj of the polynomial ring with total-degree grading, not a different projective model.
- The conclusion's dimension: `∃ n : ℕ`. There are n+1 homogeneous coordinates.
- The conclusion's integral weights: `w : ULift (Fin (n+1)) → Fin r → ℤ`.
- The conclusion's S-immersion: `j : X.X ⟶ space A n` and `IsImmersion j.left`.
- The specified projective action: `a : ModObj (torus A r).X (space A n)` and
  `IsDiagonal A r n w a`. The latter is unpacked below; it fully fixes the homogeneous
  coordinate ring map, its coefficient inclusion and the base-change comparison.
- Equivariance: `X.mod.smul ≫ j = ((torus A r).X ◁ j) ≫ a.smul`. This equality is in
  `Over S`, so includes equality of the underlying scheme morphisms and their structural
  compatibility. Whiskering is the actual product map `id_T ×_S j`. Pullback is a functor
  on morphisms and preserves this equality along every S' → S. Consequently this is
  scheme-theoretic equivariance after arbitrary base change, not only geometric points.

The IsDiagonal interface uses no arbitrary comparison: φ has underlying ring map exactly
`coaction A r n w`, ψ has underlying ring map exactly the coefficient inclusion, and their
graded lifts are unique since GradedRingHom has proof-only extra fields. The irrelevant-ideal
conditions are exactly those required by `Proj.map`. The isomorphism from Proj C[z] to
T ×_S P must have both specified projections: the standard map to Spec C, and `Proj.map ψ`.
These equations determine it uniquely by the pullback property. Under this uniquely fixed
comparison, the actual action morphism equals `Proj.map φ`. Thus `IsDiagonal` cannot encode
an action conjugated by an unconstrained automorphism or an unrelated choice of map.
Its definition is a Prop; its witnesses express the canonical coordinate characterization,
not extra hypotheses on the main theorem. `coaction` is a real `MvPolynomial.eval₂Hom`,
fixing A through the canonical algebra map and sending each variable to `C(t^w_i) * X i`.
There is no existence-based choice, hollow data or auxiliary postponed theorem.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `StandardGroupSchemes.multiplicative`
  and its Laurent Hopf instance, read as the field prototype; imported as the recorded
  statement dependency. For rings the reusable implementation is
  `Sheaf.AlgebraicGeometry.RingDiagonalizableGroup`, `ringDiagonalizableGroup`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `pullback.fst`,
  `pullback.snd`; `Cartesian.Over` realizes the action domain with these same maps.
- `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme`: `Proj`; the polynomial
  specialization `Proj.projectiveSpaceOverAffine` and its map to Spec A are from
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`.
- `Mathlib.Algebra.MvPolynomial.Basic` and `Eval`: `MvPolynomial`, `eval₂Hom`, `map`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`, `Morphisms.ClosedImmersion`, and
  `Morphisms.Immersion`: the existing immersion predicates; no second immersion definition.
- The scheme-conventions node is explicitly a convention collector; its separatedness and
  finite-type phrases use `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`, with `IsDomain`.
- Proof-only imports: `ProjectiveBundleQuotientGeometry.projective_bundle_quotient_geometry`
  in `Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry`;
  `Scheme.Modules.IsRelativelyVeryAmple` in `Sheaf.AlgebraicGeometry.RelativelyVeryAmple`;
  `Scheme.Modules.relative_ample_very_ample` in `Sheaf.AlgebraicGeometry.RelativeAmpleVeryAmple`;
  and the recorded tensor module `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`.
  The four proof dependencies currently lacking Lean records are not invented here:
  relative-normal-line-power-linearization, very-ample-affine-finite-sections,
  relative-linearized-line-sections-coaction, and projective-quotient-comparison.
  They supply no notions needed to type this statement and need no statement-level repair.

Edge cases checked: r=0 makes the character lattice trivial, so all weights are zero and
the torus is canonically the trivial group. n=0 and N=0 retain one coordinate. Empty X
has vacuous normality and its unique immersion into projective zero-space. For the zero
ring A, Spec A and any scheme over it are empty, and every construction still exists.
Nonreduced A is allowed: the coordinate formula uses free Laurent monomials and no
cancellation of coefficients. Disconnected X is not restricted. Normality forces X to be
reduced but no reducedness condition on the base is introduced. All schemes and rings
use universe u; ULift merely lifts finite coordinate and character index sets, with no
restriction excluding any finite rank or dimension. Morphism equality gives arbitrary,
including nonflat and nonreduced, base changes.

Searches performed with msearch.py:

- LeanFinder: “A normal quasi projective scheme over a Noetherian ring with split torus
  action has an equivariant projective immersion with diagonal weights”: 8 hits, consisting
  of Proj, charts and separated/proper facts, no equivariant theorem.
- Loogle: `AlgebraicGeometry.Proj, AlgebraicGeometry.IsImmersion`: no hits.
- Mathlib grep in AlgebraicGeometry: `torus|diagonal.*action|equivariant.*immersion`: no hits.
- LeanSearch: “The diagonal torus action on projective space is induced by scaling each
  homogeneous variable by its Laurent character”: 8 hits, abstract/field projectivization
  actions and representations, no scheme-level notion over rings.
- LeanFinder: “diagonal torus coaction on polynomial ring defining projective action”:
  8 hits, group-ring polynomials, field projectivization and abstract representations.
- Loogle: `"Proj", "action"`: 11 hits, mostly fraction predicates and field actions.
- Mathlib grep: `diagonal.*[Cc]oaction|[Ii]sDiagonalProjective|diagonal.*projective`: two
  abstract Rep projectivity hits, no corresponding scheme construction.
- Project rg in both `lean/WeilConjectures` and `lean/Sheaf`: split tori, torus actions,
  diagonal coactions and projective actions. Found the ring diagonalizable group and
  relative split torus, which are reused; no matching diagonal-projective action predicate
  or equivariant projective-immersion theorem. Searching the exact item id in upstream
  returned no declaration. DAG grep and `tools/blueprint_refs.py search diagonal` found
  the sibling boundary statement, which assumes this action but does not define it.
  `blueprint_refs.py ancestor` confirmed the item's inherited null ancestor.

Validation: both delivered Lean files compiled separately with scompile.py, in dependency
order against the published live library. No errors or warnings remain. Auto implicits and
relaxed auto implicits are both disabled. Definitions contain actual data; the only sorry
is the item's named theorem, with all five natural-language proof steps in its docstring.

## New nodes

`def-sfb-diagonal-projective-action` records the exact coordinate specification of the
projective action required in the item's conclusion. Its module is
`Sheaf.AlgebraicGeometry.DiagonalProjectiveAction`; main declaration
`AlgebraicGeometry.DiagonalProjectiveAction.IsDiagonal`; helpers are `torus` (an abbreviation
specializing existing ringDiagonalizableGroup), `space` (Over packaging of existing polynomial
Proj), and `coaction` (the coefficient-fixing polynomial evaluation). It follows the explicit
coordinate clause in the parent node, based on Thomason p.32 and Stacks polynomial Proj.
The searches above found only abstract/field projectivization actions, while the sibling
boundary node has no definition or recorded declaration for the notion. The ring group and
polynomial Proj are reused rather than reconstructed. The new node is a definition with
empty proof and proof-dependency lists; its source, definition dependencies, searches,
blueprint provenance and explicit-universe Lean signature are recorded in its JSON.

## Second reading by Q36

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
