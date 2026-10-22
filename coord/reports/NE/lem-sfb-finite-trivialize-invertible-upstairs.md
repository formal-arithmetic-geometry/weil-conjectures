## Worker report

Stated `AlgebraicGeometry.Scheme.Modules.exists_trivialization_over_preimage_of_isFinite`
in `Sheaf.AlgebraicGeometry.FiniteTrivializeInvertibleUpstairs`. The sole theorem's proof
is `sorry`. Only the item's `lean` field changes; no statement correction, new notion,
or dependency repair is needed.

Read the node, its five proof steps, all three statement-dependency records and their
recorded declarations with docstrings. Read the source in
`literature/stacks-project/divisors.tex`, Tag 0BUT,
`divisors-lemma-finite-trivialize-invertible-upstairs`, lines 3617–3652.
Its statement agrees with the node. The docstring preserves all five steps of the
reviewed split, including the finite-set nonvanishing lemma and the closed-image
shrinking argument.

Hypothesis and clause correspondence:

| Node | Lean |
| --- | --- |
| Schemes Y and Z | `{Y Z : AlgebraicGeometry.Scheme.{u}}` |
| Morphism p : Y → Z | `(p : Y ⟶ Z)` |
| p finite | `[AlgebraicGeometry.IsFinite p]` |
| M an O_Y-module | `(M : Y.Modules)` |
| M invertible | `[M.IsInvertible]`, the recorded `Scheme.Modules.IsInvertible` |
| Every z in Z | `(z : Z)` universally bound in the theorem |
| An open neighborhood V of z in Z | `∃ V : Z.Opens, z ∈ V ∧ ...` |
| Inverse image p⁻¹(V) | `p ⁻¹ᵁ V`, with its canonical open immersion `.ι` |
| Restriction of M to that open | `M.restrict (p ⁻¹ᵁ V).ι` |
| Restricted structure sheaf | `SheafOfModules.unit (p ⁻¹ᵁ V).toScheme.ringCatSheaf` |
| Isomorphism as modules on that open | `Nonempty (... ≅ ...)` in its category of modules |

`Scheme.Modules.restrict` is the existing open-immersion restriction functor, not a
new pullback definition or arbitrary map. `restrictUnitIso` identifies restriction of
O_Y with the structure module of the open subscheme, so the right side expresses exactly
the node's O_Y restricted to p⁻¹(V). Invertibility uses the exact upstream scheme
predicate, whose local trivializations are rank one. No additional quasi-coherence,
flatness, surjectivity, Noetherian, affine, or nonemptiness hypothesis is imposed.

Statement dependencies used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom` (read lines 36–47,
  70–79). Available through the finite-morphism public import.
- `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite`,
  `AlgebraicGeometry.IsFinite`, the node's finite clause (read lines 35–40).
- `def-sc-invertible-module`:
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`,
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` (read its full class and docstring).

The module publicly imports these statement interfaces and privately imports
`Mathlib.AlgebraicGeometry.Morphisms.Proper`,
`Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite`, and
`WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes` for the recorded
proof dependencies. The finite-closed-map-finite-fibres node is a Mathlib leaf,
using the properness instance, `Scheme.Hom.isClosedMap`, and
`Scheme.Hom.finite_preimage_singleton`. The nonvanishing-section node's recorded
`Scheme.Modules.nonvanishing_section_trivializes` was read in its upstream source.
`lem-sfb-affine-invertible-finite-set-section` currently has no Lean record and hence
no module to import; its use remains explicitly documented in the proof docstring.
It is a proof prerequisite only and supplies no notion needed for this statement.

Edge cases checked before writing:

- Empty Z: there is no z, as in the source. No `[Nonempty Z]` is added.
- Empty Y or empty fibre over z: finite maps are closed, so shrinking away from
  the image permits an empty inverse image, on which the isomorphism is valid.
  There is no nonempty-fibre or surjectivity restriction.
- p the identity: the conclusion is exactly local triviality of an invertible module.
- M the structure module: V = top works, with the canonical restriction isomorphism.
- Nonclosed z, nonreduced schemes, and arbitrary characteristic are included.
- A disconnected finite fibre requires one trivialization over its entire inverse
  image neighborhood; the conclusion is not weakened to independent source neighborhoods.
- Universe u is explicit and arbitrary, and all variables are explicitly bound.

Searches actually run through `msearch.py NE lem-sfb-finite-trivialize-invertible-upstairs`:

- LeanFinder: “For a finite morphism of schemes every invertible module trivializes on
  the inverse image of a neighborhood of any target point”. Eight hits on
  `Scheme.Hom.finite_app`, `IsFinite.finite_app`, `IsFinite.instMorphismRestrict`,
  finite scheme fibres, local generators of finite-type modules, and `finiteType_appLE`.
  None asserts this simultaneous invertible-module trivialization.
- Loogle: `AlgebraicGeometry.IsFinite, "trivial"`. Zero hits.
- LeanSearch: “An invertible sheaf is trivial over the inverse image of a neighborhood
  under a finite morphism”. Eight hits on ideal-sheaf comap_bot, topological bundle
  pullback trivializations, scheme inverse-section maps and module inverse-section maps.
  None states Tag 0BUT.
- Mathlib grep: `finite.*trivial|trivial.*finite|trivialize.*[Ii]nvertible` in
  `AlgebraicGeometry`. One hit in `Morphisms/AffineAnd.lean:22`, introductory prose.
- Direct `rg` in `lean/WeilConjectures` and `lean/Sheaf` for trivialization and finite
  morphism phrases found other finite-free, finite-etale and norm-chart statements,
  not this theorem. The exact item-id grep in `lean/WeilConjectures` found no hit.
  Searches for `finite_trivialize`, `finiteTrivialize`, `trivialize_invertible_upstairs`
  and the proposed declaration name, including `dag/lean_names_upstream.json`, found none.
  The upstream invertible-module module supplies pointwise local triviality only.

No statement dispute or node fault was found. The previous worker's supersession
claim was mistaken: ledger line 24239 records NU's stage-1 split (one new proof node),
not a stage-2 Lean delivery. The live item has no `lean` field before this work.

Validation: prescribed `scompile.py` succeeded for the sandbox module (2.3 s) and
its final library module name (2.2 s), with no errors or unexpected warnings.

## Second reading by NE

Author's second reading: compared the complete node and Lean signature again.
The quantifier is over every target point, p is finite without surjectivity or
flatness, M uses exactly the recorded invertibility predicate, and the witness V
is an open containing the chosen point. Both sides of the isomorphism are modules
on the same whole inverse image open subscheme. The RHS is the restricted structure
sheaf via `restrictUnitIso`; no generator or section is additionally specified.
No mismatches were found and no statement changes were made. This is a self-check;
the maintainer provides the independent review, as the brief directs.
