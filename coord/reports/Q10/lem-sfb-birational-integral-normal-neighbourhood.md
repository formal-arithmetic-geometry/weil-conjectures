## Worker report

The module `Sheaf.AlgebraicGeometry.BirationalIntegralNormalNeighbourhood` states
`AlgebraicGeometry.exists_integral_affine_neighbourhood_of_birational_normal_stalk`.
Its only theorem has proof `sorry`, with the four-step DAG proof in its docstring.
No definition, dependency record, informal statement, or proof plan is changed.

Hypothesis and conclusion correspondence:

- Schemes X and Y, and their morphism: `{X Y : Scheme.{u}}` and `(f : Y ⟶ X)`.
  The universe `u` is explicit and arbitrary, with no smallness restriction.
- Locally Noetherian X: `[IsLocallyNoetherian X]`.
- Reduced Y: `[IsReduced Y]`.
- The chosen point is `(x : X)`; its local ring is exactly `X.presheaf.stalk x`.
- Normal local ring: `hnormal` is precisely the prescribed normal-ring predicate,
  quantified over every prime ideal p of this stalk, requiring
  `IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)`.
  This uses the dependency's general normal-ring definition without replacing it by
  normality of an ambient neighbourhood or by a freely chosen local ring.
- Bijection of component generic points: `hgeneric : Set.BijOn f (genericPoints Y)
  (genericPoints X)`. Mathlib defines `genericPoints T` as the points whose singleton
  closure belongs to `irreducibleComponents T`. Since `IsGenericPoint η C` is exactly
  `closure {η} = C`, this is exactly the set described by the node.
- Isomorphisms of generic local rings: `hstalk` asserts `IsIso (f.stalkMap η)` for
  every η in `genericPoints Y`; this is the actual induced map, in the correct direction.
- Affine open neighbourhood V of x: existential `(V : X.Opens) (hxV : x ∈ V)`
  and `IsAffineOpen V`. Its coordinate ring A is the existing section ring Γ(X,V);
  affineness identifies its spectrum with `V.toScheme`.
- Injective map A → R: `Function.Injective (X.presheaf.germ V x hxV)`.
- V integral: `IsIntegral V.toScheme`.
- Entire inverse image integral: `IsIntegral (f ⁻¹ᵁ V).toScheme`.
- Birationality of the restricted morphism: the last two conjuncts state `Set.BijOn`
  on the component generic points of these two actual open subschemes and `IsIso`
  on each corresponding stalk map of `f ∣_ V`. No smaller source open is substituted.

Statement dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  and `Scheme.Hom.stalkMap` (inherited locally ringed-space map).
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced` and
  `AlgebraicGeometry.IsIntegral`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`;
  `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`, together
  with `IsDomain`, in the exact inline form of `def-weil-pbc-normal-ring`.
- `Mathlib.Topology.Sober`: `IsGenericPoint` and the equivalent component-generic set
  `genericPoints`.
- `Mathlib.Geometry.RingedSpace.LocallyRingedSpace`: `LocallyRingedSpace.Hom`,
  inherited by `Scheme.Hom`; its fields require local stalk maps.
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`: the recorded
  `PresheafOfModules.moduleStalkFunctor` and stalk/germ interface. Here the statement
  uses the structure-ring presheaf's existing stalk and germ, not module coefficients.
- `Mathlib.AlgebraicGeometry.Restrict` supplies the actual inverse-image open subscheme
  and `f ∣_ V`, whose domain is the full inverse image.

Proof dependencies are imported without `public`: `Mathlib.AlgebraicGeometry.SpreadingOut`
(`Scheme.exists_germ_injective`), `Mathlib.AlgebraicGeometry.StructureSheaf`
(`StructureSheaf.IsLocalization.to_stalk`), `Mathlib.AlgebraicGeometry.FunctionField`
(`functionField_isFractionRing_of_affine`), `Mathlib.Topology.Irreducible`
(component coverage, restriction and closure lemmas), and
`Mathlib.AlgebraicGeometry.OpenImmersion`. The scheme sobriety and integral/reduced
criteria belong to the already public Properties import. All recorded proof
interfaces are existing Mathlib/upstream interfaces; no pending proof dependency
requires a new module.

Source check: read `literature/stacks-project/varieties.tex`, Tag 0BFP, lemma
`lemma-modification-normal-iso-over-codimension-1`, first paragraph of proof (4), and
`properties.tex`, Tag 0BX3, `lemma-ring-affine-open-injective-local-ring`, case (2).
The local reduction uses local Noetherianness, reducedness, normality at x and the
stated componentwise birationality; properness and quasi-finiteness are only used
later in the parent argument. The node already isolates this valid local reduction.

Edge cases checked: X need not be irreducible, reduced away from x, quasi-compact,
or globally normal; V meets just the one component through the normal point.
Y need not be Noetherian or quasi-compact. No surjectivity of f on all points is
assumed. The inverse image is nonempty because the target component generic point
in V has a source generic preimage. Empty X supplies no x; empty Y cannot satisfy
birationality when X has x. V cannot be empty since hxV is required; integral schemes
use Mathlib's nonempty convention. Non-normal local domains do not satisfy hnormal
in general. There is no finite-type, separatedness, properness or dimension hypothesis.

Searches for an existing declaration:

- `msearch.py leanfinder`, query "A birational morphism with reduced source over a
  locally Noetherian scheme has an integral affine neighbourhood of a point with
  normal stalk whose entire inverse image is integral": eight hits on normalization,
  integral morphisms and integral schemes; none is this theorem.
- `msearch.py loogle`, query `AlgebraicGeometry.IsBirational,
  AlgebraicGeometry.Scheme.exists_germ_injective`: zero hits; IsBirational is unknown.
- `msearch.py grep`, query `Birational|birational|exists_germ_injective` in
  AlgebraicGeometry: ten hits including `Scheme.exists_germ_injective` and
  `Scheme.Birational`. The former gives only the injective affine germ;
  the latter is existence of a partial isomorphism between schemes, rather than
  the supplied morphism's componentwise generic bijection and stalk isomorphisms.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for birationality and integral
  neighbourhoods found sibling statements, including
  `exists_common_dense_opens_isIso_of_birational` and
  `normal_modification_isomorphism_open_contains`, but not the assigned result.
  Read these signatures to confirm the component-generic conventions. The former
  assumes local finite presentation and finite component sets and has a different
  conclusion; the latter assumes properness and has an isomorphism-locus conclusion.
- `grep -rn` for the exact item ID in `lean/WeilConjectures` found no attachment.
  `rg` for the chosen theorem name in Mathlib, both project libraries, and
  `dag/lean_names_upstream.json` found no collision.

Validation: the prescribed server `scompile.py` checked the module in sandbox and
library positions cleanly (1.9 s and 1.7 s on the first pass). Final imports and the
verbatim node signature are checked again by the delivery dry run.
No statement dispute or node fault was found.

## Second reading by Q10

Author's self-check, not an independent review: reopened the node and final module,
matched each hypothesis and all six conclusion pieces as listed above, and checked
that the inverse-image open is the whole preimage, and that the final stalk maps are
those of its actual restriction. Normality retains the exact inline prime-localization
predicate. No hypothesis or clause mismatch was found, and no statement correction
was made. The maintainer supplies the independent review required by the dispatcher brief.
