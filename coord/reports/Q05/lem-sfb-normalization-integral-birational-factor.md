## Worker report

Item: `lem-sfb-normalization-integral-birational-factor`, group Q05, stage 2.
The module is `Sheaf.AlgebraicGeometry.NormalizationIntegralBirationalFactor`.
It states `AlgebraicGeometry.Scheme.exists_iso_reducedNormalization_of_integral_birational`
with `sorry`; nothing is proved. It also constructs the canonical helper
`AlgebraicGeometry.Scheme.Hom.reducedRestriction` with real data. That helper is
part of the induced-reduction morphism already named in this node, not another
normalization or a substitute notion. The module and both declarations carry
source/blueprint docstrings. The theorem docstring gives all five proof steps.

Source read: `literature/stacks-project/morphisms.tex`,
`lemma-normalization-normal` (Tag 035Q), especially (3), its reductions footnote
and proof; `lemma-normalization-in-terms-of-components` (Tag 0CDV).
The node is a tool node, not a blueprint unit's own statement.
No statement correction or dependency repair is needed. Only the item's `lean`
record changes; there are no new nodes or dependency modules.

The exact correspondence of hypotheses and conclusions is:

| Node phrase | Lean rendering |
| --- | --- |
| Schemes X and X' and a morphism alpha | `{X X' : Scheme.{u}} (α : X' ⟶ X)` |
| Every quasi-compact open of X has finitely many irreducible components | `hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U.toScheme).Finite` |
| alpha is integral | `[IsIntegralHom α]` |
| Every inverse image of a quasi-compact open has finitely many components | `hcomponents`, using `irreducibleComponents (α ⁻¹ᵁ U).toScheme` |
| The induced map on reductions of the restriction | `α.reducedRestriction U`, from `(α ⁻¹ᵁ U).toScheme.nilradical.subscheme` to `U.toScheme.nilradical.subscheme` |
| This map induces a bijection on their generic points | `hgeneric`, with `Set.BijOn` of that actual scheme morphism on the two `genericPoints` sets |
| It induces local ring isomorphisms at these generic points | `hstalk`, quantifying every generic point eta of the source reduction and requiring `IsIso ((α.reducedRestriction U).stalkMap η)` |
| Componentwise normalizations and their canonical maps | `X.reducedNormalization`, `X'.reducedNormalization`, and `fromReducedNormalization` |
| An isomorphism e between these normalizations | `∃ e : X.reducedNormalization ≅ X'.reducedNormalization` |
| alpha composed with the normalization of X' and e equals the normalization of X | `e.hom ≫ X'.fromReducedNormalization ≫ α = X.fromReducedNormalization` |
| In particular the resulting map to X' is its normalization, up to this isomorphism | The witness e exhibits exactly this: its composite with `X'.fromReducedNormalization` is that normalization transported from its specified source `X'.reducedNormalization` to `X.reducedNormalization`. This clause asks for no further property beyond this witness. |
| No normality or Noetherian hypothesis, empty schemes allowed | No such class binders, and no nonemptiness or irreducibility binder on X or X'. |

`IsCompact` is topological quasi-compactness; it does not assume Hausdorffness.
`genericPoints T` is Mathlib's set `{x | closure {x} ∈ irreducibleComponents T}`.
Thus it is the set of component generic points defined by `IsGenericPoint`, not
the generic point of an assumed irreducible ambient scheme. `Set.BijOn` includes
both preservation of these sets and injectivity and surjectivity on them.
`Scheme.Hom.stalkMap` is the actual induced map from the target stalk at the
image to the source stalk, so its isomorphism is precisely the local-ring
condition, with the correct variance.

The helper's definition first composes the source reduction inclusion with
`f ∣_ U`, then uses `Hom.liftNilradical`. Its source is reduced by the existing
`isReduced_nilradical_subscheme` instance. This gives the canonical induced
map, with the existing `Hom.liftNilradical_subschemeι` equation and uniqueness
through the closed immersion. It introduces no arbitrary map assumption and
contains neither a postponed construction nor a new postponed theorem.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Scheme.Hom.stalkMap`; the category of schemes and its local ring maps.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`, maximal irreducible
  subsets with their inherited closedness (via the public imports).
- `Mathlib.AlgebraicGeometry.Morphisms.Integral`: `AlgebraicGeometry.IsIntegralHom`,
  affine morphism plus integral maps on sections over every affine open.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic` and `.Subscheme`:
  `Scheme.nilradical`, `Scheme.IdealSheafData.subscheme`, and `subschemeι`.
  These are exactly the recorded reduction construction, also for each open.
- `Mathlib.Topology.Sober`: `IsGenericPoint` and `genericPoints`; the latter uses
  closure-singleton membership in `irreducibleComponents`.
- `Sheaf.AlgebraicGeometry.ReducedNormalization`: `Scheme.reducedNormalization`
  and `Scheme.fromReducedNormalization` with its actual component coproduct.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`:
  `Scheme.Hom.liftNilradical`, its factorization equation and the instance
  `Scheme.isReduced_nilradical_subscheme`. This upstream construction supplies
  the canonical map needed to express the node's own hypothesis.
- `Mathlib.AlgebraicGeometry.Restrict`: `morphismRestrict`, written `f ∣_ U`,
  available through the public dependencies.

Stated proof dependencies are imported privately where not already public:
`Mathlib.AlgebraicGeometry.ResidueField` (`Scheme.residueField` and
`Scheme.Hom.residueFieldMap`), `Mathlib.AlgebraicGeometry.Gluing`
(`Scheme.Cover.glueMorphisms`),
`Mathlib.RingTheory.IntegralClosure.Algebra.Basic` (`integralClosure`), and
`Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic`
(`RingHom.IsIntegral.trans`). `Spec` is available through the scheme modules.
`lem-sfb-normalization-generic-residue-affine-charts` currently has no Lean
record or Mathlib match, so no module for that proof-only dependency can be
imported yet. Its statement was read and it is explicitly named in proof steps
4 and 5. No missing statement dependency is left.

Edge cases checked before writing and in the second pass:

- Empty X: existence of alpha forces X' empty. Every generic-point condition
  then concerns an empty set, and the normalization coproduct is empty.
- Empty U in any X: it is compact; its inverse image and both reductions are
  empty, so the finiteness/bijection clauses hold and the stalk clause is
  vacuous. No selected point or inverse nonemptiness assumption occurs.
- Identity morphisms: for any scheme with the stated local component
  finiteness, all hypotheses hold and the identity comparison has the required
  structural equation.
- Nilpotent thickening: `Spec k` to `Spec k[epsilon]/(epsilon^2)` is allowed;
  the unreduced generic stalk map need not be an isomorphism, but the required
  reduced generic stalk map is. The statement deliberately uses the reductions.
- A nontrivial finite field extension is integral and bijective on points but
  fails `hstalk`, as it must. The hypothesis was not reduced to a point bijection.
- Reducible schemes (e.g. `Spec k[x,y]/(xy)`) retain both component generic
  points; no single generic point or `IsIntegral X` binder replaces them.
- No global finiteness of the component set, finite type, excellence,
  separatedness, local Noetherianity, or normality is imposed. All quantified
  opens are retained, not just an affine special case.
- One explicit universe `u` is used for both objects in the same scheme
  category. All variables and universes are bound; `autoImplicit` is disabled.

Searches actually run for this delivery (2026-10-24):

1. `msearch.py ... leanfinder`, query: "An integral morphism inducing a birational
   map on reductions has isomorphic componentwise normalizations". Eight hits,
   including `Scheme.Hom.instIsIsoToNormalizationOfIsIntegralHom`,
   `normalizationDesc` and `fromNormalization`: these are relative normalization
   of a supplied qcqs morphism, not the present absolute componentwise comparison.
2. `msearch.py ... loogle`, query: `"normalizationDesc"`. Six hits, all relative
   normalization. Read the signatures/docstrings around
   `Mathlib/AlgebraicGeometry/Normalization.lean:365-417`; no exact match.
3. `msearch.py ... grep`, query:
   `normalizationDesc|IsIsoToNormalization|normalization.*[Bb]irational`, subpath
   `AlgebraicGeometry/Normalization.lean`. Five hits concerning the same relative
   construction; no exact comparison theorem.
4. `msearch.py ... leansearch`, query: "An integral morphism birational on
   reductions induces an isomorphism of componentwise normalizations". Eight
   hits, again relative normalization and integral morphism properties; no match.
5. `rg -n` over `lean/WeilConjectures` and `lean/Sheaf`, query
   `normalization.*[Bb]irational|[Bb]irational.*normalization|reducedNormalization|lem-sfb-normalization-integral-birational-factor`.
   Read the componentwise construction and the consumer
   `IntegralNormalGenericRecognition.lean`. Other normalization comparisons
   require normal or locally Noetherian schemes, or concern regular pullback;
   none states this general theorem. The consumer only cites this node in its
   proof docstring. No upstream source carries this item id as a declaration.
6. `rg -n` over both libraries and `dag/lean_names_upstream.json`, query
   `exists_iso_reducedNormalization_of_integral|reducedRestriction`: no existing
   declaration of the proposed names. Searching `liftNilradical` found the
   usable upstream canonical construction, which is used directly.

Validation: prescribed `scompile.py Q05 lem-sfb-normalization-integral-birational-factor`
compiled both the sandbox file and the library module successfully (2.0 s and
4.6 s). The only postponed proof is the named item theorem. The dry-run below
also checks the final file with `autoImplicit` disabled.

No STATEMENT-DISPUTED flag or node fault remains.

## Second reading by Q05

A separate second pass by this dispatcher-started worker compared the complete
node text and the final Lean source against Stacks 035Q (3) and 0CDV. No other
agent was started, as the dispatcher's instructions forbid that; independent
review belongs to the maintainer's delivery review.

The second pass checked the quantifier over every quasi-compact open in all
four local hypotheses, finiteness for both the open and its inverse image,
the use of the reductions in both `hgeneric` and `hstalk`, and the induced maps
rather than chosen equivalences. It read `Hom.liftNilradical` and confirmed
that the helper factors the actual restricted morphism through the target
reduction; the source reduction is the recorded nilradical subscheme.
Mathlib's `genericPoints` matches the dependency's closure definition exactly.
The witness e has the requested orientation X-normalization to X'-normalization;
the composition equation has the stated variance. Its composite with the
normalization of X' also explicitly supplies the node's final transported-map
assertion, without a redundant equality or a stronger uniqueness assertion.
The pass rechecked empty opens, nilpotent thickenings and multiple components,
and found no missing or extra hypothesis or clause. No mathematical change was
needed. `set_option autoImplicit false` was added to enforce the explicit-binder
requirement in the final compiler check.
