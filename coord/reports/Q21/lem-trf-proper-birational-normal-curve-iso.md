## Worker report

The module `Sheaf.AlgebraicGeometry.ProperBirationalNormalCurveIso` states
`AlgebraicGeometry.isIso_of_isProper_birational_normal_curve`, with `sorry` as its entire
proof. There are no new definitions, helper theorems, dependency modules, statement changes,
or disputed statements.

Hypothesis and conclusion correspondence:

- A field `k`: `{k : Type u} [Field k]`.
- The schemes `C` and `E` over `k`: `{C E : Scheme.{u}}` and the two
  `.Over (Spec (.of k))` instances. All variables and the universe are explicit.
- Each scheme is integral, separated, of finite type, and of dimension exactly one:
  `[IsIntegralCurve (C ↘ Spec (.of k))]` and its counterpart for `E`. The recorded
  upstream predicate extends `IsVariety`, which extends `IsSeparated`,
  `LocallyOfFiniteType`, and `QuasiCompact` and supplies `IsIntegral`. Its additional
  field is `topologicalKrullDim_eq_one : topologicalKrullDim X = 1`.
  Thus these binders contain exactly the node's four scheme conditions.
- The specified morphism is `(p : E ⟶ C)`; its compatibility with the two structure
  morphisms is `[p.IsOver (Spec (.of k))]`.
- Properness is `[IsProper p]`; dominance is `[IsDominant p]`.
- The induced function-field isomorphism is `hbirational`, the bijectivity of
  `p.stalkMap (genericPoint E)`, with codomain explicitly `E.functionField`.
  Mathlib defines the function field as the generic stalk. Since `p` is dominant
  between integral schemes, it sends the generic point of `E` to the generic point
  of `C`. Consequently the source `C.presheaf.stalk (p (genericPoint E))` is
  canonically `C.functionField`. This is the actual pullback on function fields;
  bijectivity is exactly its being an isomorphism. There is no arbitrary field
  equivalence or extra generic-point equality hypothesis.
- Every target local ring is an integrally closed domain: `hnormal` is
  `∀ x : C, IsDomain (C.presheaf.stalk x) ∧ IsIntegrallyClosed (C.presheaf.stalk x)`.
  This is the dependency's normal-domain clause, rather than its different
  normal-ring clause about all prime localizations.
- The conclusion that this particular map is an isomorphism is `IsIso p`.
- The absence of a normality assumption on `E` and of a perfection assumption on
  `k` is reflected by the absence of those binders. No smoothness, projectivity,
  geometric integrality, or algebraic closure is assumed.

Dependency declarations read and used:

- `def-weil-field`: `Field`, in `Mathlib.Algebra.Field.Defs`.
- `def-pc-curve`: `AlgebraicGeometry.IsIntegralCurve` and
  `AlgebraicGeometry.IsVariety`, in
  `WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective`. The older local
  upstream checkout lacks this file; its full current source was read using
  `scompile.py --source WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective`.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper` in
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`, with its recorded parent classes
  `IsSeparated` and `UniversallyClosed` read in their source modules.
- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral` in
  `Mathlib.AlgebraicGeometry.Properties`, supplied by the curve predicate.
- `def-kun-topological-krull-dimension`: `topologicalKrullDim` in
  `Mathlib.Topology.KrullDimension`, used by the curve predicate's dimension field.
- `def-weil-pbc-normal-ring`: `IsDomain` and `IsIntegrallyClosed`; the latter in
  `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed` means integral closure
  inside `FractionRing`. The inline conjunction follows the recorded interface.
- `def-sc-function-field`: imported `Sheaf.AlgebraicGeometry.FunctionField` and
  read its `Scheme.functionFieldOfComponents` and docstring. The node's integral
  specialization expressly reuses `Scheme.functionField`, in
  `Mathlib.AlgebraicGeometry.FunctionField`; that generic-stalk abbreviation is
  used here. `Scheme.Hom.stalkMap`, in `Mathlib.AlgebraicGeometry.Scheme`, supplies
  the canonical induced map, without a second definition.

The two proof dependencies `lem-trf-proper-birational-curve-finite` and
`lem-trf-finite-birational-normal-iso` were read. Both currently have status
`unsplit` and no Lean declaration or Mathlib match, so there is no stated proof
module to import. The theorem docstring records the complete two-step proof and
names both nodes for stage 3.

Source and edge-case checks: read the actual statements and proofs at
`literature/stacks-project/varieties.tex`, labels `lemma-finite-in-codim-1`
(Tag 0AB7) and `lemma-modification-normal-iso-over-codimension-1` (Tag 0BFP),
and `literature/stacks-project/morphisms.tex`, label
`lemma-finite-birational-over-normal` (Tag 0AB1). Integral curves are nonempty;
the empty scheme and zero-dimensional schemes are excluded by the node itself.
The identity of any normal integral curve satisfies the statement, over an
arbitrary field in any characteristic. A punctured-curve open immersion is
excluded by properness. A finite nonbirational cover is excluded by bijectivity
of the induced generic stalk map, even when the two abstract fields happen to
be isomorphic. The normalization of a cusp fails the target-normality condition.
Blowing up a surface does not meet the one-dimensional curve conditions. No
additional assumptions are needed for imperfect fields or positive characteristic.

Searches for an existing statement (all performed for this item through the
prescribed launcher tools where applicable):

- `msearch.py leanfinder`, query "A proper birational morphism of integral curves
  with normal target is an isomorphism": eight hits, principally relative
  normalization statements such as
  `Scheme.Hom.instIsIsoToNormalizationOfIsIntegralHom`; these concern the map to
  a relative normalization, not the given proper curve morphism.
- `msearch.py leansearch`, the same query: eight hits, the relative-normalization
  result and properness properties. None has the node's statement.
- `msearch.py loogle`, query `"birational"`: twelve hits, including
  `Scheme.Birational` and `Scheme.BirationalOver`. These express existence of a
  partial isomorphism, not the assertion that the specified proper morphism is
  an isomorphism.
- `msearch.py grep`, query `birational|Birational` in `AlgebraicGeometry`: eight
  file hits around the rational-map and birationality API; no matching theorem.
- `rg` in upstream `WeilConjectures`, side `lean/Sheaf`, Mathlib algebraic
  geometry, and `dag/lean_names_upstream.json` for the proposed declaration name,
  `isIso_of.*[Bb]irational`, `[Bb]irational.*isIso`,
  `proper.*birational`, and `birational.*normal`: no exact statement or name
  collision. Side normalization and dense-open-isomorphism results concern
  different maps and hypotheses. Searching upstream for this exact node id
  also yielded no hit.
- Read Mathlib's `FunctionField.lean` in full and searched for function-field map
  names; the existing generic stalk and `Scheme.Hom.stalkMap` already express
  the needed canonical map, so no missing-notion node is necessary.

Validation: `scompile.py Q21 lem-trf-proper-birational-normal-curve-iso` compiled
this delivered module both as a sandbox file and at its library module path,
with no errors or warnings (5.0 s and 3.0 s respectively).

## Second reading by Q21

Author's consistency check, not an independent reviewer claim: reread the node,
the compiled file, the curve predicate's full current source, and the generic
stalk interface. The field, both sets of curve conditions, the k-morphism,
properness, dominance, the induced function-field isomorphism, all target local
normal-domain conditions, and the conclusion correspond as listed above. The
stalk map is tied to `p`, so no abstract-field-isomorphism weakening occurs.
Neither target normality nor source integrality was dropped; no source
normality or perfectness was added. The JSON signature is copied verbatim from
the file. No mismatch or correction was found. The maintainer's independent
review is subsequent to this worker delivery, as specified in the dispatcher brief.
