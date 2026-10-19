## Worker report

The module `Sheaf.AlgebraicGeometry.UnramifiedOrdinaryFibreCriterion` states
`AlgebraicGeometry.unramified_of_ordinary_fibre_coproduct_finite_separable`.
It uses Mathlib's scheme-theoretic fibre `h.fiber s`, residue field `B.residueField s`,
and the canonical fibre map `h.fiberToSpecResidueField s`.  Its hypothesis is, for
 every `s : B`, an arbitrary index type `I : Type u`, fields `L : I → Type u`,
field structures and residue-field algebra structures, finite-module and separable
instances for every component, and an isomorphism of the fibre with the coproduct
`∐ (fun i : I ↦ Spec (CommRingCat.of (L i)))` whose composite to the residue-field
spectrum is exactly the canonical fibre map.  The conclusion is exactly
`LocallyOfFiniteType h ∧ IsOpenImmersion (pullback.diagonal h)`.

The theorem has proof `sorry`, as required for stage 2.  The declaration docstring
records the three source proof steps: affine fibre charts are unramified by the
field-fibre decomposition and open restriction; differential base change plus
finite generation and Nakayama force relative differentials to vanish; and the
affine-cover characterization glues to the open-diagonal conclusion.

The statement dependencies and declarations read were:

- `def-weil-finite-type-morphism`: Mathlib `AlgebraicGeometry.LocallyOfFiniteType`.
- `def-pc-scheme-fibre`: Mathlib `AlgebraicGeometry.Scheme.Hom.fiber` and
  `fiberToSpecResidueField`.
- `def-weil-residue-field`: Mathlib `AlgebraicGeometry.Scheme.residueField`.
- `def-weil-pbc-separable-algebraic-extension`: Mathlib `Algebra.IsSeparable`.
- `def-weil-unramified-morphism`: the recorded Mathlib conjunction
  `LocallyOfFiniteType h ∧ IsOpenImmersion (pullback.diagonal h)`.
- `def-pc-field-extension`: Mathlib `Algebra` with field structures.
- `def-weil-affine-spectrum`: Mathlib `AlgebraicGeometry.Spec` and `Spec.map`.

No new node or dependency module was needed.  The proof-only dependency
`lem-trf-unramified-field-fibre-decomposition` remains a proof citation and is not
needed by the statement module import list.

Searches made:

- `msearch.py ... leanfinder "locally finite type morphism ordinary fibre coproduct spectra finite separable fields unramified"`: 8 hits, all generic Mathlib unramified or fibre facts; no exact theorem.
- `msearch.py ... loogle "LocallyOfFiniteType, IsOpenImmersion, fiber, Sigma.desc, IsSeparable"`: 0 hits (service reported unknown identifier for `LocallyOfFiniteType`).
- `msearch.py ... grep "unramified.*ordinary|ordinary.*fibre|ordinary.*fiber" AlgebraicGeometry`: 0 hits.
- `rg` over `WeilConjectures/` and `lean/Sheaf`: no declaration of this theorem; only the separate geometric-fibre criterion cites this item.
- `blueprint_refs.py search lem-trf-unramified-ordinary-fibre-criterion`: 0 blueprint matches.

Edge cases checked: `I` is an unrestricted `Type u`, so the empty coproduct is
allowed; singleton and arbitrary coproducts are allowed; no finiteness or
quasi-compactness of the index is imposed.  A purely inseparable component is
excluded by `Algebra.IsSeparable`, while an identity fibre satisfies the displayed
isomorphism.  The universe is the scheme universe, so the coproduct remains a
scheme of the same universe.

## Second reading by Q07

I re-read the item node and the returned instruction against Stacks Morphisms Tag
02G8(2), and checked the signature produced by `scompile.py`.  The binder
`{Z B : Scheme.{u}} (h : Z ⟶ B) [LocallyOfFiniteType h]` renders the morphism and
its locally-finite-type hypothesis.  The universal fibre clause is rendered by
`∀ s : B`; its arbitrary (possibly empty) decomposition is rendered by
`∃ I : Type u, L : I → Type u`, with each `L i` a field and an explicit algebra
structure over `B.residueField s`.  The two component hypotheses are rendered
separately as `Module.Finite` and `Algebra.IsSeparable` for every `i`.  The fibre
identification is an explicit scheme isomorphism `e`, and the equation after it
uses the canonical `h.fiberToSpecResidueField s`, so it is an isomorphism over the
residue-field spectrum rather than an unrelated scheme isomorphism.  The conclusion
has both required clauses, `LocallyOfFiniteType h` and the open immersion of the
pullback diagonal.  No hypothesis or conclusion was added, dropped, strengthened,
or weakened relative to the returned correction.  The split report was left
unchanged from the current main node.

`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q07 lem-trf-unramified-ordinary-fibre-criterion lean/Sheaf/AlgebraicGeometry/UnramifiedOrdinaryFibreCriterion.lean`
completed cleanly; the only postponed proof is the expected `sorry`.
