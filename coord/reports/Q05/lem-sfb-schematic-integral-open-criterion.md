## Worker report

The module `Sheaf.AlgebraicGeometry.SchematicIntegralOpenCriterion` states
`AlgebraicGeometry.schematicIntegralOpenCriterion`, with `sorry` as its only proof.
There are no definitions, new nodes, dependency repairs, or statement corrections.
The node copy changes only `lean`.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean |
| --- | --- |
| Schemes Z and V | `{Z V : Scheme.{u}}`, with explicit arbitrary universe `u` |
| Open immersion j: V → Z | `(j : V ⟶ Z) [IsOpenImmersion j]` |
| Quasi-compact: inverse images of affine opens are quasi-compact | `[QuasiCompact j]`; Mathlib's `quasiCompact_iff_forall_isAffineOpen` is exactly this characterization |
| V integral | `[IsIntegral V]` |
| V scheme-theoretically dense in Z, meaning injectivity of the structure-sheaf map | `[IsSchemeTheoreticallyDominant j]`; its kernel-ideal-sheaf condition is equivalent to this injectivity for the assumed quasi-compact morphism |
| Given generic point η of V | `(η : V) (hη : IsGenericPoint η Set.univ)` |
| K = O(V,η) | `V.presheaf.stalk η`, written directly throughout |
| Z integral | First conjunct `IsIntegral Z` |
| K a field | Second conjunct `IsField (V.presheaf.stalk η)`; this asserts the field property of the existing commutative ring, without choosing an inverse operation |
| Every nonempty affine open W in Z | `∀ (W : Z.Opens), IsAffineOpen W → Nonempty W → ...` |
| W ∩ V nonempty | `Nonempty (j ⁻¹ᵁ W)`; the inverse image under the open immersion is precisely the intersection, viewed as an open of V |
| Restriction followed by germ into K injective | `Function.Injective (j.app W ≫ V.presheaf.germ (j ⁻¹ᵁ W) η hηW)` |

The existential `hηW : η ∈ j ⁻¹ᵁ W` supplies the membership proof required by the
canonical germ map. It makes explicit the membership already implicit in the node's
displayed map: a generic point of an integral scheme lies in every nonempty open.
This is a conclusion, not an added assumption. Different proofs of this proposition
produce the same map by proof irrelevance. The arbitrary given generic point is kept;
no canonical-point assumption is imposed. Uniqueness of generic points of schemes
identifies it with `genericPoint V` when using the function-field proof dependencies.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`.
- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsIntegral`. Its all-nonempty-open formulation is equivalent
  to the affine-open formulation in the node, as its dependency record explains.
- `def-nagata-scheme-theoretically-dense-open`: its existing `mathlib_match`,
  `AlgebraicGeometry.IsSchemeTheoreticallyDominant` in
  `Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant`.
  `Scheme.Hom.app_injective` supplies injectivity on opens under quasi-compactness;
  no missing `lean` attachment or private predicate is needed.
- `def-sc-generic-point`: `Mathlib.Topology.Sober`, `IsGenericPoint`, literally
  closure of the singleton equal to the given set.
- `def-weil-pbc-module-stalk`: imported its recorded
  `WeilConjectures.Topology.PresheafModuleStalkFunctor`. For the structure ring
  itself the appropriate existing notion is Mathlib's `TopCat.Presheaf.stalk`,
  as the dependency's statement and `mathlib_match` explicitly specify. Its `germ`
  is the coprojection of the neighbourhood colimit. No module stalk functor is
  applied to a ring object or duplicated.
- Proof dependencies `lem-sc-integral-function-field-affine-fraction` and
  `lem-sc-integral-scheme-stalks-in-function-field`: ordinary (non-public) import
  of `Mathlib.AlgebraicGeometry.FunctionField`, which provides their recorded
  `functionField_isFractionRing_of_isAffineOpen` and
  `germ_injective_of_isIntegral` and the field/fraction-ring instances.
- Proof dependency `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` in the
  already publicly imported `Mathlib.AlgebraicGeometry.Scheme`.

The public imports expose the recorded statement-dependency notions, and the
non-public function-field import supplies the stated proof plan. All signatures
and docstrings were read in the read-only live sources. The theorem docstring
carries the node's four proof steps and their named DAG inputs.

Source checks: read `literature/stacks-project/morphisms.tex`,
`lemma-characterize-scheme-theoretically-dense` (Tag 01RE), including the section
restriction argument, and `lemma-integral-scheme-rational-functions` (Tag 01RV),
including its integral-field clause. These agree with the node's consequence.

Edge cases checked before writing: V cannot be empty by integrality, so its map
also makes Z nonempty. The empty affine W is intentionally excluded, since its
zero section ring cannot inject into a field. A nonempty W with empty intersection
would force its nonzero affine ring to inject into the zero ring, contradicting
schematic density. No nonempty-intersection hypothesis was added. Taking j to be
the identity recovers the existing germ-injectivity result. Taking V = Spec K
handles dimension zero. No Noetherian, reducedness, separatedness, finite-type,
or characteristic assumptions were added. Both schemes use the ordinary common
scheme universe; the statement has no quantification over test schemes and no
universe restriction on such tests. There is no disputed statement or node fault.

Searches for reuse (2026-10-24):

- `msearch.py ... leanfinder`, query: "A scheme with a schematically dense integral
  open subscheme is integral and affine sections embed in its generic stalk".
  Eight hits, including `IsIntegral`, the integral-open instance,
  `instIsGermInjectiveOfIsIntegral`, and domain instances; no theorem with the
  reverse ambient-integrality criterion and all the asserted conclusions.
- `msearch.py ... loogle`, query:
  `AlgebraicGeometry.IsIntegral, AlgebraicGeometry.IsSchemeTheoreticallyDominant`.
  Zero hits.
- `msearch.py ... leansearch`, query: "An integral schematically dense open
  subscheme makes the ambient scheme integral". Eight hits, headed by
  `isIntegral_of_isOpenImmersion`, which goes from integral ambient scheme to
  integral open, the reverse of the required implication. No exact match.
- `msearch.py ... grep`, query
  `isIntegral_of|germToFunctionField_injective|app_injective`, restricted to
  `AlgebraicGeometry/Morphisms/SchemeTheoreticallyDominant.lean`. Three hits:
  `app_injective`, its use in reducedness descent, and a later use. None is the item.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for
  `schematicIntegralOpen|schematic.*[Ii]ntegral|[Ii]ntegral.*schematic|lem-sfb-schematic-integral-open-criterion`:
  only unrelated schematic-density proof text in other modules, no statement match.
- Exact `grep -rn` of the item id in `lean/WeilConjectures`: no hits.
- `rg` for `schematicallyDenseIntegralOpen|integral_of_schematically|integral_of_schemeTheoretically`
  across Mathlib, WeilConjectures, Sheaf, and `dag/lean_names_upstream.json`: no hits.
- Read the matching Mathlib FunctionField, Properties and
  SchemeTheoreticallyDominant declarations and the upstream schematic-dominance
  extension; these give the ingredients, not this combined statement.

Validation: the prescribed `scompile.py Q05 lem-sfb-schematic-integral-open-criterion`
compiled the sandbox and final library module separately, each in 1.3 seconds,
with no errors or unexpected warnings. All binders and the universe are explicit;
`autoImplicit` is disabled in the module. No global or direct local build was run.

## Second reading by Q05

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
