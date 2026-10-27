## Worker report

The module `Sheaf.AlgebraicGeometry.BirationalGenericIsomorphismOpen` states
`AlgebraicGeometry.exists_dense_open_isIso_of_proper_birational`. Its proof is `sorry`,
as required in stage 2. There are no definitions, new nodes, dependency repairs, or statement
changes. Only the item's `lean` field changes.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Schemes X and Y: `{X Y : Scheme.{u}}`, with the universe `u` explicitly declared.
- X Noetherian, explicitly meaning locally Noetherian and quasi-compact:
  `[IsNoetherian X]`. Mathlib's class extends exactly `IsLocallyNoetherian X` and
  `CompactSpace X`, the latter expressing quasi-compactness without any Hausdorff condition.
- The specified morphism Y to X: `(f : Y ⟶ X)`.
- Properness: `[IsProper f]`. This is separated, universally closed, and locally of finite
  type; universal closedness supplies quasi-compactness, hence the node's finite-type condition.
- Bijection on component generic points:
  `hgeneric : Set.BijOn f (genericPoints Y) (genericPoints X)`. BijOn includes mapping into
  the target generic points, injectivity there, and surjectivity onto them. Mathlib defines
  `genericPoints X` as the points whose singleton closures are irreducible components, exactly
  the component version of the recorded `IsGenericPoint` definition.
- Isomorphism on every source generic local ring:
  `hstalk : ∀ η : Y, η ∈ genericPoints Y → IsIso (f.stalkMap η)`.
  The map has precisely direction O_(X,f(η)) to O_(Y,η); IsIso is a ring isomorphism of
  this actual map, not merely an abstract isomorphism between the rings.
- The required open subset: `∃ V : X.Opens`.
- Density: `Dense (V : Set X)`.
- Every component generic point belongs to V: `genericPoints X ⊆ (V : Set X)`.
- Isomorphism of the entire inverse image onto V: `IsIso (f ∣_ V)`.
  Mathlib's `morphismRestrict f V` has source `(f ⁻¹ᵁ V).toScheme` and target V;
  this does not replace the whole inverse image by a smaller source open.

Dependency declarations read and used:

- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`; bundled with compactness by `IsNoetherian`.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper`.
- `def-sc-generic-point`: `Mathlib.Topology.Sober`, `IsGenericPoint` and its existing
  component specialization `genericPoints`. No new generic-point predicate is introduced.
- `def-weil-locally-ringed-space-morphism`:
  `Mathlib.Geometry.RingedSpace.LocallyRingedSpace`,
  `AlgebraicGeometry.LocallyRingedSpace.Hom`. Scheme morphisms extend this structure;
  `Scheme.Hom.stalkMap` is its canonical stalk map.

All five recorded dependency modules are public imports. Further statement syntax uses
`Mathlib.AlgebraicGeometry.Restrict`. Proof imports are
`Mathlib.AlgebraicGeometry.Morphisms.FiniteType` (finite-type implication),
`Mathlib.AlgebraicGeometry.Properties` (scheme sobriety),
`Mathlib.Topology.Irreducible` (components and their covering), and
`Sheaf.AlgebraicGeometry.BirationalIsomorphismDenseOpen`
(`AlgebraicGeometry.exists_dense_open_isIso_of_separated_birational`). The remaining proof
dependencies are available from the already public Noetherian, proper, and sober modules:
`finite_irreducibleComponents_of_isNoetherian` and
`LocallyOfFinitePresentation.iff_locallyOfFiniteType`, in particular. The full four-step
natural-language proof is in the theorem docstring, with every proof-dependency ID.

Sources checked locally: Stacks `morphisms.tex`,
`lemma-birational-isomorphism-over-dense-open` (0BAJ), and `varieties.tex`,
`lemma-modification-normal-iso-over-codimension-1` (0BFP), proof (1). The locally finitely
presented alternative in 0BAJ does not require reducedness. The node is unchanged.

Edge cases checked before writing:

- Empty X: any Y admitting f to X is empty, so V empty is dense; the generic-point clauses
  are vacuous and the empty restriction is an isomorphism. No nonemptiness binder occurs.
- Identity on Spec(k[ε]/ε²): allowed; generic local rings are preserved, and V can be all X.
  Neither reducedness nor integrality is assumed.
- Multiple components: BijOn concerns all component generic points, rather than a single
  chosen generic point; the conclusion likewise contains all of them.
- Adding a disjoint exceptional point component mapping to a closed point is excluded by
  the generic-point mapping/bijection condition, as required.
- A reduction map of a generically nonreduced scheme fails the actual stalk-isomorphism
  hypothesis. An abstract residue-field isomorphism would not suffice and is not used.
- A normalization of a nodal integral curve can fail to be an isomorphism globally, but the
  required dense open avoids the singular point. No global-isomorphism clause is added.

Searches made on 2026-10-24 (full wrapper results are in `searches.jsonl`):

- msearch leanfinder: "A proper birational morphism to a Noetherian scheme is an isomorphism
  over a dense open containing every irreducible component generic point". Eight results:
  local isomorphisms, dominance, properness invariance and normalization; no exact theorem.
- msearch loogle: `AlgebraicGeometry.IsProper, AlgebraicGeometry.Scheme.Hom.stalkMap`.
  Zero results.
- msearch grep: `birational.*[Ii]so|[Ii]so.*birational|[Bb]irational`, restricted to
  Mathlib AlgebraicGeometry. Eight reported hits in Birational modules. `Scheme.Birational`
  means existence of a partial isomorphism and does not state the property of this given map.
- msearch leansearch: "proper birational morphism Noetherian dense open isomorphism component
  generic points". Eight hits concerning partial maps, generic points under open immersions,
  properness and dominance; no exact theorem.
- Direct rg of `lean/WeilConjectures` for this item's ID: no match. Direct rg for
  `birational.*[Ii]so|[Ii]so.*birational`: no exact statement.
- Direct rg of `lean/Sheaf` and Mathlib for birational/generic-open terminology found the
  existing separated birational dense-open theorem. Its full docstring and signature were
  read: it assumes finite component sets and local finite presentation, and omits the
  generic-point containment clause. It is the recorded proof input, not an exact existing
  statement of this item. Other curve and normalization matches impose different hypotheses.
- The proposed declaration name was searched in Mathlib, WeilConjectures and Sheaf; no clash.

Validation: prescribed `scompile.py Q09 lem-sfb-birational-generic-isomorphism-open` on the
module succeeded in both sandbox and actual-library module contexts (1.6 seconds each),
with no compiler errors or warnings.

No statement dispute or dependency fault was found.

## Second reading by Q09

The dispatcher explicitly prohibits starting other agents and supplies the maintainer's
independent delivery review. Consequently this section records a second self-reading, not
a claim of an independent worker review. The node and completed module were reopened and
compared: IsNoetherian includes both local Noetherianity and compactness; the explicit f has
properness; BijOn is on the correct source and target component generic sets; stalkMap has
the contravariant local-ring direction required; the existential V has density, containment
of every component generic point, and IsIso on the entire inverse-image restriction.
The statement has no reducedness, nonempty, irreducible, integral, normal, or separated-target
assumption. Universe u is explicitly declared. No mismatch or correction was found.
