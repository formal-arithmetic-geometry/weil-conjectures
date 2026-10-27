## What changed

Proved `AlgebraicGeometry.exists_finite_smooth_integral_base_refinement` in
`Sheaf.AlgebraicGeometry.FiniteSmoothIntegralBaseRefinement`. The public theorem signature,
existing docstrings, and all public imports are unchanged. No other existing module changes.

The proof follows Stacks 057K, `more-morphisms.tex`, from the connected component through
the outer pullback diagram. It applies the existing
`exists_geometricallyIntegral_connectedComponent` and
`exists_geometricallyIntegral_fibre_neighbourhood` declarations. All intervening glue is
proved in private helpers: surjective stalk maps induce residue-field isomorphisms;
finite rational presentations give pure transcendence; the canonical fibre comparison
is an isomorphism when the base residue map is; fixed-pair pullback points are unique;
and finite-variable rational function fields transport along compatible field isomorphisms.

The fibre comparison places the marked point in the supplied open using its exact embedded
fibre equality. The singleton-fibre hypothesis and fixed-pair uniqueness give the new
singleton fibre. Functoriality proves both displayed residue-field squares with the actual
`residueFieldCongr` transports. Polynomial coefficient transport preserves the finite number
of variables, including zero variables. Smoothness, etaleness, and finiteness use Mathlib
permanence instances. Added the private proof import `WeilConjectures.PointCount` for the
geometric characterization of `residueFieldAlgebraMap`.

Updated only the assigned node's proof, proof dependencies, proof origin, and obsolete
`tool_uses` entries to describe this implementation. No definitions or public interfaces
change, so no change record or consumer adaptation is needed.

Single-file server compilation succeeded in 14.5 seconds. The final lint adjustment uses
the compiler's suggested `simp only` list. Delivery runs the final compilation and probes.
A static comparison also confirmed the original theorem signature and public imports are
unchanged, and every Lean line has at most 100 characters.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.exists_finite_smooth_integral_base_refinement`
(node `lem-trf-finite-smooth-integral-base-refinement`).

The item contains zero `sorry`s. Added zero holes and zero split-off statements.
Every new private helper has a complete proof. The two geometric existence declarations
used from existing modules remain the assigned downstream work of those modules.

## No longer needed

Removed these five private proof imports:

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: already available through the unchanged
  public finite-presentation import.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: properness is not used; finite base change
  is supplied by the finite-morphism import.
- `Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres`: the open inclusion is smooth
  of relative dimension zero directly by Mathlib, so no fibre-dimension theorem is needed.
- `WeilConjectures.AlgebraicGeometry.FibreProductPointResidueField`: the canonical fibre
  comparison and surjectivity on stalks replace the tensor residue-field computation.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: Mathlib's
  instance from `LocallyOfFinitePresentation` to `LocallyOfFiniteType` supplies exactly
  the implication used here, without the general cancellation theorem.

Consequently removed these dependencies from the node's `proof_deps` and `tool_uses`:
`lem-a1-map-over-base-finite-presentation`,
`lem-weil-pbc-fibre-product-point-residue-field`, and
`lem-weil-pbc-etale-smooth-zero-dimensional-fibres`.
The pullback point correspondence itself is still needed, as are both geometric existence
nodes. These are dependencies pruned from this item's proof, not a claim that their modules
have no remaining consumers elsewhere. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement correction was necessary. The DAG's route used a general finite-presentation
cancellation result for a direct Mathlib implication and a tensor residue-field computation
where the existing cartesian fibre comparison suffices. These unnecessary dependencies
are removed. The connected-component and spreading steps of the source are retained.
The unit record has no realized statements or steps that this proof bypasses.

An initial elaboration of the connected-component application spent its time inferring
large scheme and field expressions. Supplying its field, over-structure, and permanence
instances explicitly removes that inference search; no shared definition was changed.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
