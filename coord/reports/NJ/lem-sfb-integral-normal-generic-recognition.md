## Worker report

The module `Sheaf.AlgebraicGeometry.IntegralNormalGenericRecognition` states
`AlgebraicGeometry.Scheme.existsUnique_iso_reducedNormalization_of_integral_normal_generic`
with `sorry`. It introduces no definitions and changes only the item's `lean` field.
The module and theorem docstrings cite Stacks 035Q (3), its reductions footnote,
035Q (4), and 0H7D; the theorem docstring gives all six proof steps and their DAG nodes.
The source was read in `literature/stacks-project/morphisms.tex`, at
`lemma-normalization-normal`, `lemma-normalization-in-terms-of-components`, and
`lemma-normalization-trivial`.

Hypothesis and conclusion correspondence:

- Schemes T and Z and the map a: `{T Z : Scheme.{u}}` and `(a : Z ⟶ T)`.
  The universe `u` is declared explicitly; `autoImplicit` is not used to bind anything.
- T locally Noetherian: `[IsLocallyNoetherian T]`.
- a integral: `[IsIntegralHom a]`; this is not `IsIntegral Z` and does not assume
  that a is finite.
- Every local ring of Z is an integrally closed domain: `hZ` quantifies over every
  `z : Z` and asserts `IsDomain (Z.presheaf.stalk z) ∧
  IsIntegrallyClosed (Z.presheaf.stalk z)`. Scheme stalks are already local rings.
- Bijection of component generic points: `hgeneric : Set.BijOn a` between the
  sets `{z : Z | ∃ C ∈ irreducibleComponents Z, IsGenericPoint z C}` and the
  identical expression for T. `BijOn` includes mapping into the target set,
  injectivity on the source set, and surjectivity onto the target set. Schemes
  are sober, so these are precisely the generic points of their components.
- The induced map κ(a(z)) to κ(z) is an isomorphism at every such z:
  `hresidue` quantifies over z and its component-generic predicate and asserts
  `IsIso (a.residueFieldMap z)`. This is the induced map, not an arbitrary
  isomorphism of the two fields.
- Existence and uniqueness of an isomorphism Z to T^ν: `∃! e : Z ≅
  T.reducedNormalization`.
- Isomorphism over T: `e.hom ≫ T.fromReducedNormalization = a`.
  Thus uniqueness is among exactly the isomorphisms over T, equivalently among
  isomorphisms in the category of T-schemes with these structure maps.
- No local Noetherianity of Z, finiteness of a, excellence, or reducedness of T
  appears in the binders. The source and target may be empty.

Dependency declarations read and used:

- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`.
- `def-weil-finite-integral-morphism`: the recorded
  `Mathlib.AlgebraicGeometry.Morphisms.Finite` is imported, together with
  `Mathlib.AlgebraicGeometry.Morphisms.Integral`, which declares the needed
  `AlgebraicGeometry.IsIntegralHom`.
- `def-weil-pbc-normal-ring`: `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`,
  `IsIntegrallyClosed` and `IsDomain`, in the recorded normal-domain inline form.
- `def-sc-generic-point`: `Mathlib.Topology.Sober`, `IsGenericPoint`.
- `def-weil-irreducible-components`: its `mathlib_match` is
  `Mathlib.Topology.Irreducible`, `irreducibleComponents`; no Lean record repair
  is necessary for a Mathlib match.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `Scheme.residueField` and `Scheme.Hom.residueFieldMap`.
- `def-weil-pbc-reduced-normalization`:
  `Sheaf.AlgebraicGeometry.ReducedNormalization`, `Scheme.reducedNormalization`
  and `Scheme.fromReducedNormalization`. Its construction is the coproduct of
  the normalizations of the reduced induced components, including the empty coproduct.

The already stated proof dependencies are imported: Noetherian component finiteness
from `Mathlib.AlgebraicGeometry.Noetherian` (already a public statement import),
reduced-source factorization from
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, scheme reduction
from `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`, and reduced minimal-prime
localization from `Mathlib.RingTheory.KrullDimension.Zero`. The three proof-only nodes
`lem-sfb-normalization-integral-birational-factor`,
`lem-sfb-normalization-normal-locally-finite`, and
`lem-sfb-component-dominant-normalization-lift` currently have neither a Lean record
nor a Mathlib match; there is no published module to import for them. The statement
needs none of their objects, so no dependency modules or new nodes are required.

Edge cases checked before writing:

- T empty: a morphism to T forces Z empty. Normality and generic-point conditions
  are vacuous, and the empty coproduct normalization gives the unique isomorphism.
- Z empty with T nonempty cannot satisfy `hgeneric`, since a nonempty scheme has
  a component generic point. No nonemptiness binder is introduced.
- Nonreduced T is retained: for example Spec(k[ε]/(ε²)) and Spec(k) have the same
  component generic point and residue field; the normalization is Spec(k).
  Asking for generic stalk-map isomorphisms on T itself would wrongly exclude this
  case. The statement asks for residue-field-map isomorphisms exactly as the node does.
- Reducible T uses the set of component generic points, not the generic point of
  the whole space or an `IsIntegral T` hypothesis.
- Normal sources not known locally Noetherian, and integral maps not known finite,
  remain in scope. There is no finite-type, compactness, or excellence binder.

Searches for an existing statement (2026-10-22):

- `msearch.py ... leanfinder`: “An integral morphism from a normal scheme bijective
  on generic points with isomorphic generic residue fields is its componentwise
  normalization” returned eight hits about relative normalization, including
  `Scheme.Hom.instIsIsoToNormalizationOfIsIntegralHom`.
- `msearch.py ... loogle`: `"normalization", "IsIntegralHom"` returned four
  relative-normalization results, not this absolute recognition theorem.
- `msearch.py ... leansearch`: “An integral morphism from a normal scheme inducing
  a bijection on generic points and isomorphisms on generic residue fields is the
  normalization” returned eight relative-normalization hits.
- `msearch.py ... grep`: `normalization.*[Nn]ormal|[Bb]irational` in
  `AlgebraicGeometry` returned relative normalization and birationality modules.
  These do not identify the componentwise absolute normalization used here.
- `rg -n 'normalization|generic.*[Bb]ij|[Bb]ij.*generic'` in the upstream and project
  algebraic-geometry trees, and the more precise
  `rg -n 'reducedNormalization|fromReducedNormalization|integral_normal_generic'`
  across `lean/WeilConjectures` and `lean/Sheaf`, found the existing normalization
  definition and consumers, including `reducedNormalization_smooth_pullback`,
  but no theorem with the present recognition hypotheses and conclusion.
- `rg -n 'lem-sfb-integral-normal-generic-recognition' lean/WeilConjectures` found
  no occurrence. The existing smooth-pullback theorem cites this item in its
  proof docstring and is a consumer, not an existing statement of this item.

No statement correction, disputed statement, or dependency-interface fault was found.

## Second reading by NJ

A separate rereading of the node and completed signature checked the bijection's
source and target, the direction of `residueFieldMap`, and the direction of the
isomorphism and commuting triangle. `Set.BijOn` includes both injectivity and
surjectivity, and the residue hypothesis is restricted to the same generic-point
predicate. The two stalk conditions apply at every point of Z. The conclusion
uses the recorded componentwise normalization and its actual canonical map.
The nonreduced-target example rules out replacing residue fields by generic
stalks. There are no extra source-Noetherian or finite-map instances. No mismatch
was found and no correction was needed. This rereading was performed by the same
worker; independent review is left to the maintainer as required by the dispatch.
