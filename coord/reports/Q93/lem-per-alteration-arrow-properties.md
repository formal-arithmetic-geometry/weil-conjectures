## Worker report

The module `Sheaf.AlgebraicGeometry.AlterationArrowProperties` states
`AlgebraicGeometry.PrimeToEllAlteration.alterationArrow_properties`, with one named
sorry theorem and no definitions. The node is unchanged apart from `lean`.

The source was read in the local ILO PDF: Exposé II Proposition 1.1.10 proves
maximal dominance and generic residue-field finiteness; Definition 1.2.2 gives
alt/S and §1.2.3 records the arrow property. The finite-type argument follows
Stacks 01T6, 01T8, 01OY and 03GI as detailed in the node and theorem docstring.

Hypotheses and conclusions, clause by clause:

- The base scheme is `{S : Scheme.{u}}`. `[IsNoetherian S]` is exactly the finite
  affine Noetherian-cover condition: Mathlib's `isNoetherian_iff_of_finite_iSup_eq_top`
  identifies it with that condition.
- The prime is `(ell : ℕ) [Fact ell.Prime]`. Although the conclusion is independent
  of ell, the binder preserves the node's stated context.
- The two objects are `{X T : Alt S}` using the recorded dependency's abbreviation.
  Its predicate on `Over S` supplies `LocallyOfFiniteType`, `QuasiCompact`,
  `IsReduced`, and, for every component generic point, the component generic image
  and finiteness of the structural residue-field map. Thus all of the node's
  expanded object hypotheses are present, without repeating their definitions.
- An arbitrary S-morphism is `(u : X ⟶ T)`. `Alt S` is a full subcategory of
  `Over S`, so its arrows include exactly all S-morphisms. The underlying scheme
  arrow is `u.hom.left`, and the over-category commutativity is already part of `u`.
- Finite type is `LocallyOfFiniteType u.hom.left ∧ QuasiCompact u.hom.left`.
- Each component generic point is quantified by
  `∀ x : X.obj.left, closure ({x} : Set X.obj.left) ∈ irreducibleComponents X.obj.left →`.
  Closure of its singleton being a component says precisely that it is that
  component's generic point, without making a choice of generic points.
- The generic-image clause is
  `closure ({u.hom.left x} : Set T.obj.left) ∈ irreducibleComponents T.obj.left`.
- The finite extension through the induced field map is
  `(u.hom.left.residueFieldMap x).hom.Finite`. `RingHom.Finite` means module
  finiteness for the algebra induced by this very ring homomorphism, so over these
  fields it means finite-dimensionality. It does not use an arbitrary algebra.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, interpreted through
  `Mathlib.AlgebraicGeometry.Noetherian.IsNoetherian` and its affine-cover equivalence.
- `Sheaf.AlgebraicGeometry.PrimeToEllAlterationTopology`:
  `AlgebraicGeometry.PrimeToEllAlteration.Alt` (the recorded node's object declaration).
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`, inside `Alt`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`; `QuasiCompact` from its public imports.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, `RingHom.toAlgebra`, via `RingHom.Finite`.

Proof dependencies with recorded modules are imported privately, including
`Sheaf.TraceFormula.FiniteResiduePointClosedInFibre`. Its theorem's complete
signature and docstring were read; it uses finite-dimensionality for the induced
residue-field algebra and concludes that the corresponding point in the fibre
is closed. No dependency repair or new node is needed.

Edge cases: no `Nonempty X` is imposed, so an empty source has a vacuous generic
clause and still has the finite-type conclusion. An empty T forces X empty,
and an empty S forces both empty. Multiple irreducible components are allowed:
the statement quantifies over every point with component closure. Neither
integrality nor separatedness is assumed. No restriction on residue characteristic,
separability, or degree prime to ell is added: this lemma asserts mere finiteness.
The universe `u` is explicit and common to the schemes in the recorded `Alt S`.

Searches performed with `msearch.py Q93 lem-per-alteration-arrow-properties`:

- LeanFinder: "Every morphism between alteration objects over a Noetherian scheme
  is finite type and preserves generic points of components with finite residue
  field extensions". Eight hits, including `IsFinite`, `LocallyOfFiniteType`,
  `LocallyQuasiFinite`, and residue-field preimmersion results; none is the assertion.
- Loogle: `AlgebraicGeometry.LocallyOfFiniteType, "of_comp"`. Two hits:
  `AlgebraicGeometry.locallyOfFiniteType_of_comp` and `AlgebraicGeometry.Etale.of_comp`.
  The first is the finite-type cancellation proof tool, not the full assertion.
- LeanSearch: "Morphisms between alteration objects preserve generic points and
  have finite residue field extensions". Eight hits, including quasi-finite
  residue-field results and `Scheme.Hom.residueFieldMap`, but no matching statement.
- Mathlib grep: `maximally|genericallyFinite|generic.*finite` in AlgebraicGeometry:
  zero hits through the search wrapper.
- Direct `rg` in `lean/WeilConjectures` and `lean/Sheaf` for alteration language,
  `maximally|genericallyFinite|generic.*finite`, and the proposed declaration name:
  alteration constructions and generic-finiteness tools, but no theorem giving
  this conjunction for arrows of `Alt S`. `grep -rn` for the exact node id in
  `lean/WeilConjectures` found no attachment. The existing `Alt` definition was reused.

Validation: `scompile.py` checked both the sandbox and library module names,
with successful exits and no errors or warnings. Only the theorem proof is postponed.
No statement dispute or node fault was found.

## Second reading by Q93

Author's second pass, not an independent agent review: the dispatcher explicitly
forbids starting other agents; the maintainer supplies the independent reading.
Reopened the node, the definition of `Alt`, and the delivered theorem. Checked the
Noetherian and prime binders, both objects' reducedness/finite-type/generic-field
conditions, and the arbitrary S-morphism. Matched the two finite-type conjuncts,
the source generic-point antecedent, the target generic-point conclusion, and
finiteness for the actual induced residue map. The empty-source case is included
because the source-point clause is a universal implication. No mismatch was found
and no statement or dependency changes were made. The proof docstring includes
all four node proof steps, including quasi-compactness without separatedness and
the fibre-topology justification. There are no helper declarations to audit.
