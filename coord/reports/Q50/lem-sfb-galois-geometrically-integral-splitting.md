## Worker report

The module `Sheaf.AlgebraicGeometry.GaloisGeometricallyIntegralSplitting` states
`AlgebraicGeometry.exists_finite_galois_geometrically_integral_clopen_components`.
Its only theorem proof is `sorry`. No definitions, helper nodes, dependency repairs,
or statement corrections are needed. The node changes only in `lean`.

Hypothesis and conclusion correspondence:

- A field e: `{e : Type u} [Field e]`.
- The e-scheme B: `{B : Scheme.{u}}` and its structure morphism
  `f : B ⟶ Spec (CommRingCat.of e)`. An explicit morphism is used because the statement
  involves its base changes and their projections.
- Nonempty integral B: `[IsIntegral B]`; this class contains nonemptiness.
- Finite type: `[LocallyOfFiniteType f] [QuasiCompact f]`, exactly the recorded
  conjunction for def-weil-finite-type-morphism. No separatedness is assumed.
- Every local ring an integrally closed domain: `hB`, quantifying over all points b,
  with `IsDomain (B.presheaf.stalk b) ∧ IsIntegrallyClosed (B.presheaf.stalk b)`.
- Geometric reducedness: `[GeometricallyReduced f]`.
- For every field extension F/e: `∀ (F : Type u) [Field F] [Algebra e F]`.
  Its base change is the actual `pullback f (Spec.map (CommRingCat.ofHom
  (algebraMap e F)))`, and the assertion is `IsNoetherian` of that scheme.
  Mathlib's `isNoetherian_iff_of_finite_affine_openCover` identifies this with
  precisely the stated finite cover by affine spectra of Noetherian rings.
- The finite Galois extension: existential e0, Field and Algebra structures,
  `FiniteDimensional e e0 ∧ Algebra.IsSeparable e e0 ∧ Normal e e0`.
  Mathlib Normal means algebraic with every element's minimal polynomial splitting;
  over fields this is the stated equivalent irreducible-polynomial criterion.
- The scheme Y is the literal pullback along `algebraMap e e0`. Its projection p
  is the chosen `pullback.fst`; `IsFinite`, `Etale`, and `Surjective` are asserted
  about that very projection, without introducing an arbitrary map.
- The pieces are `U : Fin n → Y.Opens`, with `0 < n`, so the finite index set is
  nonempty. Each X_i is `(U i).toScheme`, the actual induced open subscheme.
- Closedness: `∀ i, IsClosed (U i : Set Y)`; openness is already in `Y.Opens`.
- Disjointness: `∀ i j, i ≠ j → Disjoint (U i) (U j)`.
- Cover: `(⨆ i, U i) = ⊤`.
- Exactly the irreducible components: the range of the underlying sets of U equals
  `irreducibleComponents Y`. Maximal irreducible subsets are nonempty. Together
  with disjointness this also rules out repetitions.
- Normal local rings on each X_i: the explicit pointwise domain and integrally
  closed conjunction on `(U i).toScheme.presheaf.stalk x`.
- Geometric integrality over e0: `GeometricallyIntegral ((U i).ι ≫ pullback.snd ...)`.
  This uses the induced e0-structure morphism, and means integral after every field
  extension by `geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms`.
  In particular each piece itself is nonempty and integral.
- Conditional properness: `IsProper f → ∀ i, IsProper ((U i).ι ≫ pullback.snd ...)`.
  Properness is not an unconditional hypothesis.

All universes are explicit. The field and schemes are in the same ambient universe u,
as in the recorded geometric-property and generic-component-splitting interfaces;
there is no independent smaller test-field universe. This is a universe-polymorphic
scheme theorem, not a restriction to finite or algebraic test extensions.

Dependency declarations read and used:

| Node | Module | Declaration / encoding |
| --- | --- | --- |
| def-weil-field | Mathlib.Algebra.Field.Defs | Field |
| def-pc-integral-scheme | Mathlib.AlgebraicGeometry.Properties | AlgebraicGeometry.IsIntegral |
| def-weil-finite-type-morphism | Mathlib.AlgebraicGeometry.Morphisms.FiniteType; QuasiCompact | AlgebraicGeometry.LocallyOfFiniteType; QuasiCompact |
| def-pc-geometrically-irreducible | Mathlib.AlgebraicGeometry.Geometrically.Integral | GeometricallyIntegral; GeometricallyReduced |
| def-pc-field-extension | Mathlib.Algebra.Algebra.Defs | Algebra; algebraMap |
| def-pc-fibre-product | Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback | pullback; pullback.fst; pullback.snd |
| def-weil-pbc-noetherian-ring | Mathlib.RingTheory.Noetherian.Defs | IsNoetherianRing, via the scheme IsNoetherian finite-affine-cover criterion |
| def-pc-field-tower | Sheaf.FieldTheory.FieldTower | finite-extension clause is Mathlib Module.Finite / FiniteDimensional, as its module docstring records |
| def-weil-irreducible-components | Mathlib.Topology.Irreducible | irreducibleComponents |
| def-weil-finite-integral-morphism | Mathlib.AlgebraicGeometry.Morphisms.Finite | AlgebraicGeometry.IsFinite |
| def-weil-etale-morphism | Mathlib.AlgebraicGeometry.Morphisms.Etale | AlgebraicGeometry.Etale |
| def-weil-surjective-morphism | Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap | AlgebraicGeometry.Surjective |
| def-weil-proper-morphism | Mathlib.AlgebraicGeometry.Morphisms.Proper | AlgebraicGeometry.IsProper |
| def-weil-pbc-separable-algebraic-extension | Mathlib.FieldTheory.Separable | Algebra.IsSeparable |

The proof dependencies with recorded project modules are imported privately:
`WeilConjectures.AlgebraicGeometry.GenericComponentsSplit`
(`exists_finite_etale_geometric_component_extension`),
`Sheaf.AlgebraicGeometry.EtaleNormalComponents`
(`Etale.exists_clopen_normal_integral_components`),
`WeilConjectures.FieldTheory.FiniteGaloisReceivingSeparableExtensions`
(`finite_galois_receiving_separable_extensions`), and
`WeilConjectures.Mathlib.RingTheory.Etale.Field`
(`Algebra.Etale.of_finite_of_isSeparable`). The other recorded proof inputs are
Mathlib finite-type/base-change, affine Noetherian, etale residue-field, finite,
surjective, open/closed immersion, and properness results, exposed by the imported
Mathlib modules. No project proof-dependency module is omitted for an import cycle.
The docstring follows all seven supplied proof steps and names the relevant nodes.

Source checks: read Stacks varieties.tex Tag 054R and the geometrically integral
and geometrically reduced definitions; inspected the newest blueprint direct-image
proof under literature/blueprint/latest. The node is an auxiliary consequence,
not the blueprint unit's own statement. The normality conclusion is asserted only
for the finite separable splitting extension, not arbitrary inseparable extensions.

Edge cases checked before writing: B = Spec e permits the trivial extension and
one piece. B = Spec L for finite separable L/e permits its normal closure and
several singleton components. Geometrically integral B permits a single component.
The empty scheme is excluded exactly by IsIntegral, and n = 0 is excluded exactly
by 0 < n. No bound on n, characteristic, or algebraic degree of F/e is imposed.
A nontrivial purely inseparable finite field extension gives a normal integral
scheme which is not geometrically reduced, and is correctly excluded. Nonseparated
finite type schemes remain allowed. If B is not proper, the last implication is
vacuous, leaving all the other conclusions intact.

Searches made on 2026-10-24:

- msearch.py leanfinder: “A normal geometrically reduced integral finite type scheme
  over a field splits into normal geometrically integral clopen components over a
  finite Galois extension”. Eight hits on normalization, Galois fields, invariants,
  and proper global sections; no matching theorem.
- msearch.py loogle: `"GeometricallyIntegral", "IsGalois"`: zero hits.
- msearch.py grep, AlgebraicGeometry: `geometrically.*component|component.*geometrically|Galois.*splitt`:
  three hits (geometrically reduced, connected, irreducible APIs); none supplies
  the finite Galois extension or this package of conclusions.
- rg with the same regular expression in lean/WeilConjectures and lean/Sheaf:
  generic-component splitting, alteration, and geometric-component results, none
  with this statement. A search for the exact node id found no existing declaration.
- Read the recorded upstream generic splitting theorem: it only supplies finite
  etale geometric irreducibility, without normal clopen geometrically integral
  components, arbitrary-base-change Noetherianity, or conditional properness.
- msearch.py leansearch: finite Galois splitting of a normal geometrically reduced
  integral finite type scheme into geometrically integral normal clopen components.
  Eight hits: Galois normality/separability/splitting-field equivalences and
  finite_irreducibleComponents_of_isNoetherian; no matching splitting theorem.

No STATEMENT-DISPUTED flag or node fault remains. The module compiled in both sandbox
and library mode through scompile.py, with no errors or warnings.

## Second reading by Q50

Self-check of the final node against the compiled module (the dispatcher forbids
starting another agent; the maintainer supplies the independent review): checked
all fourteen statement dependencies and every clause above against the signature.
In particular the same f defines both field base changes, p is the first canonical
projection, the pieces have the inherited open scheme structures, and the last
properness assertion uses the second projection composed with the inclusion.
Nonemptiness of pieces follows both from the component-set identity and from
geometric integrality; nonemptiness of the family is explicitly 0 < n. Normality
uses all stalks, and geometric integrality tests all field extensions, including
inseparable ones. No clauses were removed or strengthened. The only compile repair
was explicit scheme-to-type coercions in Set/irreducibleComponents and removal of
an unmatched closing parenthesis; it changed no mathematical content.
