## Worker report

The module `lean/Sheaf/AlgebraicGeometry/ClosedDominantDimension.lean` states the
closed-dominant dimension formula from Stacks Project Tag 02JX.  It uses Mathlib's
`AlgebraicGeometry.IsIntegral`, `LocallyOfFiniteType`, `IsLocallyNoetherian`,
`Scheme.functionField`, `Algebra.trdeg`, `topologicalKrullDim`, and `IsProper`.

The source introduces a dominant locally finite type morphism `f : V ⟶ U` between
integral schemes and a locally Noetherian target.  The Lean binders
`(U V : Scheme.{u}) [IsIntegral U] [IsIntegral V] (f : V ⟶ U)` with
`[IsDominant f] [LocallyOfFiniteType f] [IsLocallyNoetherian U]` render these
hypotheses without adding assumptions.  The existential witness
`h : f (genericPoint V) = genericPoint U` records the generic-point identification
needed to type the induced function-field map.  The declaration
`Scheme.closedDominantFunctionFieldMap f h` is the stalk map at `genericPoint V`, transported by
`h`; the first conjunct `Function.Injective (Scheme.closedDominantFunctionFieldMap f h).hom`
renders the stated injection.  `Scheme.closedDominantFunctionFieldAlgebra f h` is the corresponding
algebra structure, and `Cardinal.toENat (@Algebra.trdeg U.functionField
V.functionField _ _ (Scheme.closedDominantFunctionFieldAlgebra f h))` is the extended-natural-number
version of the stated transcendence degree.  The next conjunct is exactly
`topologicalKrullDim V ≤ topologicalKrullDim U + r`.  Its implication hypothesis
`IsClosedMap f` and equality conclusion render the closed-map equality.  The final
implication `IsProper f → Scheme.ClosedDominantFunctionFieldFinite f h → ...` renders the proper,
finite-function-field-extension specialization; `ClosedDominantFunctionFieldFinite` is a definition
that installs the canonical algebra and asks for `Module.Finite`.

The declarations used are:

* `Mathlib.AlgebraicGeometry.Properties.AlgebraicGeometry.IsIntegral`;
* `Mathlib.AlgebraicGeometry.Morphisms.FiniteType.AlgebraicGeometry.LocallyOfFiniteType`;
* `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact.AlgebraicGeometry.QuasiCompact`
  (the finite-type family recorded by the dependency; the present statement only needs
  the locally-of-finite-type class);
* `Mathlib.AlgebraicGeometry.Noetherian.AlgebraicGeometry.IsLocallyNoetherian`;
* `Mathlib.Topology.Sober.IsGenericPoint` and `genericPoint`;
* `Mathlib.AlgebraicGeometry.FunctionField.AlgebraicGeometry.Scheme.functionField`;
* `Mathlib.RingTheory.AlgebraicIndependent.Basic.Algebra.trdeg`;
* `Mathlib.SetTheory.Cardinal.ENat.Cardinal.toENat`;
* `Mathlib.Topology.KrullDimension.topologicalKrullDim`;
* `Mathlib.AlgebraicGeometry.Morphisms.Proper.AlgebraicGeometry.IsProper`.

The module's own helper declarations are `AlgebraicGeometry.Scheme.closedDominantFunctionFieldMap`,
`AlgebraicGeometry.Scheme.closedDominantFunctionFieldAlgebra`, and
`AlgebraicGeometry.Scheme.ClosedDominantFunctionFieldFinite`, followed by
`AlgebraicGeometry.closed_dominant_dimension`.  Their definitions contain no `sorry`.
The theorem proof is the single expected `sorry`; its docstring records all five proof
steps from the node: the local dimension bound, the generic-fibre chain, lifting chains
through a closed map, concatenation, and the proper finite-extension case.

Edge cases checked before writing include the empty-scheme case (excluded by
`IsIntegral.nonempty`), zero transcendence degree (the proper finite-extension clause),
zero-dimensional schemes, and infinite topological dimension.  `Cardinal.toENat` keeps
the dimension expression meaningful when a transcendence degree or dimension is
infinite.  The generic-point witness avoids imposing an extra equality of scheme
universes; the map is transported at the stalk level and is canonical under dominance.

Searches for an existing declaration were made as follows:

* `msearch.py ... leanfinder "scheme morphism dominant generic point maps to generic point function field map"`:
  returned generic-point and rational-map declarations, but no dimension formula or
  induced function-field map;
* `msearch.py ... grep "map_genericPoint|genericPoint.*dominant|dominant.*genericPoint" AlgebraicGeometry`:
  no matches;
* `rg -n "genericPoint|functionField|topologicalKrullDim|IsDominant|IsClosedMap"`
  over Mathlib AlgebraicGeometry/Topology and the source tree: found only the Mathlib
  function-field and topology APIs, with no closed-dominant dimension theorem;
* `rg -n "dimension.*trdeg|trdeg.*topologicalKrullDim|alteration.*dimension"`
  over Mathlib and `WeilConjectures`: no matching theorem;
* `grep -rl "lem-trf-closed-dominant-dimension" dag/nodes`: found only this node.

No `STATEMENT-DISPUTED` flag or node fault was found.

## Second reading by Q16

I reread the node, the module, and the dependency records independently.  The
integrality, dominance, local finite type, and local Noetherian hypotheses occur as
class binders; the injection, inequality, closed-map equality, and proper finite
extension equality occur as separate Lean conjuncts/implications.  The only auxiliary
binder is the generic-point equality required to type the canonical stalk map; it is
existentially produced and therefore does not weaken the source statement.  The map,
algebra, and finite-extension helper definitions are real constructions and are listed
in the node's `lean.declarations`.  No mismatch was found.

## Maintainer review fix (cc review service)

The three helper definitions of the delivered module were a second definition of an existing
notion (H4): the source repository already has `AlgebraicGeometry.Scheme.Hom.functionFieldMap`
(WeilConjectures/AlgebraicGeometry/Curve/DivisorPullback.lean, the stalk map at the generic point
after `stalkSpecializes` along `f (genericPoint X) = genericPoint Y`) and
`AlgebraicGeometry.Scheme.Hom.apply_genericPoint_of_isDominant`
(WeilConjectures/AlgebraicGeometry/Morphisms/FiberDegree.lean). The module now imports
`WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback`, installs the algebra
`(f.functionFieldMap f.apply_genericPoint_of_isDominant).hom.toAlgebra` by `letI`, and states the
same four clauses (injection, inequality, closed-map equality, proper finite-extension equality)
without the existential generic-point witness. The theorem docstring now carries the node's five
proof steps. Per-file compile through tools/nt_compile.py: clean.
