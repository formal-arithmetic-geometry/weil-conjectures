## Worker report

The module `Sheaf.AlgebraicGeometry.NongenericPointSameFieldDvr` states
`AlgebraicGeometry.Scheme.exists_dvr_subalgebra_at_nongeneric_point` with one
`sorry`. It introduces no definitions or auxiliary theorems. The node is unchanged
except for its `lean` record.

Hypotheses and clauses, read against the node:

- An integral locally Noetherian scheme is `(Z : Scheme.{u}) [IsIntegral Z]
  [IsLocallyNoetherian Z]`. No global Noetherian, affine, separated, dimension,
  finite-type, or base-field assumption is imposed.
- The generic point eta is `genericPoint Z`. In an integral scheme the generic
  point is unique (`genericPoint_spec` and sobriety), so using the canonical
  representative loses no choice of eta in the node.
- The fixed field L is `Z.functionField`, definitionally
  `Z.presheaf.stalk (genericPoint Z)`. Mathlib supplies its field instance.
- A point different from eta is `(z : Z) (hz : z ≠ genericPoint Z)`.
- The ring A inside L containing the image of O_{Z,z} is
  `A : Subalgebra (Z.presheaf.stalk z) Z.functionField`. This is a literal
  subring of the fixed L with the additional containment datum. Its base algebra
  is Mathlib's `stalkFunctionFieldAlgebra`, defined by the specialization stalk
  map sending each local germ to its generic germ. This map is injective by the
  existing stalk fraction-ring instance; no arbitrary embedding is quantified.
- The DVR condition is the existential instance `(_ : IsDiscreteValuationRing A)`.
  The domain instance is inherited from A being a subring of the field L. The
  class includes local, principal ideals and nonzero maximal ideal, as required.
- Fraction field exactly L is `IsFractionRing A Z.functionField`, for A's literal
  inclusion into L. This does not allow an unspecified abstract fraction field
  or a different field extension.
- Domination is the contraction equality
  `(IsLocalRing.maximalIdeal A).comap (algebraMap (Z.presheaf.stalk z) A) =
  IsLocalRing.maximalIdeal (Z.presheaf.stalk z)`. Together with subalgebra
  containment this says exactly that A dominates the given stalk.
- The required map is `a : Spec (CommRingCat.of A) ⟶ Z`.
- Its closed-point value is `a (IsLocalRing.closedPoint A) = z`.
- Its restriction along Spec L to Spec A is expressed by
  `Spec.map (CommRingCat.ofHom A.val.toRingHom) ≫ a =
  Z.fromSpecStalk (genericPoint Z)`. Here `A.val` is the actual inclusion in
  the specified L; the right side is the canonical generic-stalk morphism on
  that same L. Equality of scheme morphisms retains the identity field map,
  rather than merely requiring the generic point to have the right image or
  allowing a field automorphism.

Dependency declarations read and used:

- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsIntegral`.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`.
- `def-sc-generic-point`: `Mathlib.Topology.Sober`, `IsGenericPoint`,
  `genericPoint`, `genericPoint_spec`.
- `def-sc-function-field`: imported the recorded
  `WeilConjectures.AlgebraicGeometry.FunctionField`; its docstring explicitly
  delegates the arbitrary-integral-scheme clause used here to Mathlib's
  `AlgebraicGeometry.Scheme.functionField`. Its `functionFieldOfComponents` is
  for the general component product, which is not needed here. No dependency
  repair is needed: the recorded module supplies the precise integral notion.
- `def-sc-discrete-valuation-ring`: `Mathlib.RingTheory.DiscreteValuationRing.Basic`,
  `IsDiscreteValuationRing`, the node's exact `mathlib_match`.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec`, `AlgebraicGeometry.Spec.map`.

The canonical morphism is the existing `Scheme.fromSpecStalk` from
`Mathlib.AlgebraicGeometry.Stalk`. `Subalgebra` and its actual inclusion `val`
come from `Mathlib.Algebra.Algebra.Subalgebra.Basic`.
Proof imports follow all recorded proof dependencies: affine stalk localization
and spectrum stalk-map formulas in `Mathlib.AlgebraicGeometry.AffineScheme`;
open-immersion stalk isomorphisms in `Mathlib.AlgebraicGeometry.OpenImmersion`;
`IsLocalization.isNoetherianRing` in `Mathlib.RingTheory.Localization.Submodule`;
integral-stalk and affine fraction-field declarations in Mathlib FunctionField
(reexported by the recorded function-field module);
`Scheme.fromSpecStalk_affine_description` and
`Scheme.fromSpecStalk_local_properties` in the recorded
`WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism`; and
`IsLocalRing.exists_dvr_subalgebra_same_fraction_field` in
`Sheaf.RingTheory.LocalDomainSameFieldDvr`. These imports are private when only
needed for the later proof. All five steps of the node's proof are in the
statement docstring.

Source check: read Stacks `properties.tex`, the full lemma and proof labelled
`lemma-locally-Noetherian-specialization-dvr` (054F), especially (2) with L/L;
`limits.tex`, `lemma-Noetherian-dvr-valuative-proper` (0208), the identical-field
boundary-point construction; and `algebra.tex`, `lemma-exists-dvr` (00PH).
The statement retains the prescribed field and domination in these sources.

Edge cases checked before writing:

- Empty schemes are excluded by integral, exactly as in the node.
- For Spec k there is no nongeneric point: the result is correctly vacuous;
  it does not assert a DVR inside k dominating the field stalk itself.
- On Spec of a DVR at its closed point, the original DVR is an admissible A.
- On the affine plane at (x,y), the local ring need not itself be a DVR;
  the existential overring allows the dominating DVR of 00PH. No codimension-one
  restriction was added. At (x), a nonclosed nongeneric point, the same
  statement applies without imposing closedness in Z.
- Nonaffine and nonseparated integral locally Noetherian schemes remain allowed.
- `u` is arbitrary and all the types (stalks, their subalgebras, fixed function
  field and spectra) inherit Z's universe, without a smallness restriction.

Searches for an exact existing statement:

- `msearch.py ... leanfinder`, query: "Every nongeneric point of an integral
  locally Noetherian scheme is the centre of a DVR subring of its function field
  with identity generic morphism". Eight results include the stalk fraction-ring
  instance, `Scheme.functionField`, `stalkFunctionFieldAlgebra`, and the generic
  germ injection. They provide the notions, but no DVR existence or morphism.
- `msearch.py ... loogle`, query: `"AlgebraicGeometry", IsDiscreteValuationRing`.
  One result `AlgebraicGeometry.Scheme.ord_add` assumes a DVR stalk; no match.
- `msearch.py ... grep`, query:
  `exists.*(dvr|discreteValuation)|dominat.*valuation|valuation.*dominat`,
  subdirectory `AlgebraicGeometry`. Zero results.
- `msearch.py ... leansearch`, query: "Every nongeneric point of an integral
  locally Noetherian scheme has a discrete valuation subring of its function
  field dominating its stalk and inducing the identity generic morphism".
  Eight results include the stalk fraction-ring instance, germ injectivity,
  and general DVR/valuation-ring facts. No exact existence theorem.
- `rg -n 'nongeneric|same_field_dvr|same_fraction_field|dominat.*valuation|valuation.*dominat'
  lean/WeilConjectures lean/Sheaf`: found the recorded same-field algebra lemma,
  upstream DVR domination, and unrelated geometric valuation material. Read
  `WeilConjectures/RingTheory/DiscreteValuationRing/Dominating.lean`: the upstream
  `IsLocalRing.exists_isDiscreteValuationRing` asserts an abstract injective local
  map to a DVR, not the specified same fraction field or the scheme morphism.
- `grep -rn 'lem-sfb-nongeneric-point-same-field-dvr' lean/WeilConjectures`: no hits.
- Name/concept grep of `dag/lean_names_upstream.json`, `lean/WeilConjectures` and
  `lean/Sheaf` found no existing declaration named
  `exists_dvr_subalgebra_at_nongeneric_point` or exact nongeneric-DVR statement.
  Search logs are in the sandbox `searches.jsonl`.

Validation: `scompile.py Q144 lem-sfb-nongeneric-point-same-field-dvr` compiled
both the sandbox and library forms cleanly (3.6 s and 2.4 s respectively).
No node fault, statement correction, new node, dependency repair, or
STATEMENT-DISPUTED flag is needed.

## Second reading by Q144

Author's second reading; the maintainer supplies the independent review.
Reopened the node and delivered Lean signature together. Checked integral and
locally Noetherian separately, the arbitrary nongeneric point, the fixed generic
stalk as L, subring containment via the canonical stalk algebra, DVR and exact
fraction field, maximal-ideal contraction, the map a, its closed-point value and
its canonical generic restriction. The generic-point binder uses the unique
canonical representative, so it does not restrict the node. The morphism
restriction uses the literal inclusion A.val and equality with fromSpecStalk,
so it does not replace identity on L by an unspecified isomorphism. A is bound
before its DVR instance, which is available for the maximal ideal and closed
point. All variables and the universe are explicit (`autoImplicit false`).
There are no local notations, local instances, hidden let expressions, data
sorries, extra hypotheses, or missing clauses. No mismatch was found and no
mathematical change was made on this second reading.
