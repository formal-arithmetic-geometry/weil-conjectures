## Worker report

Stage 2, Q28. The inherited BLOCKED ending concerned a stage-1 deliver.py attempt
on an already split item. The live stage-2 queue lists this item and the node has
no lean record. No repair note exists for this item. The accepted split is preserved.

The delivery states `AlgebraicGeometry.AlgebraicSpace.exists_blowupPresentation_comp_admissible`
in `Sheaf.AlgebraicGeometry.AlgebraicSpaceComposeAdmissibleBlowups`, with proof `sorry`.
Its definition dependency is `Sheaf.AlgebraicGeometry.AlgebraicSpaceBlowupPresentation`.
Both files compile separately with scompile.py, including their library module names,
against the published server library. There are no compiler errors or warnings.
No proof is supplied, and no definition uses sorry or choice of unspecified data.

Hypothesis and clause correspondence:

- The base scheme is `{S : Scheme.{u}}` and the original space is `X : AlgebraicSpace S`.
  Universe `u` is explicit; the existing framework supplies site objects in `u+1`
  and ring and module sections in `u`, with no additional universe equality.
- Quasi-compactness of X is `hqc`, precisely a surjective representable etale map
  from a scheme V with `CompactSpace V.left`. This uses the node's atlas definition,
  without requiring the specified base S to be quasi-compact or quasi-separated.
- Absolute quasi-separatedness is `hqs : IsAbsolutelyQuasiSeparated X`, the existing
  affine-test definition of the absolute diagonal. It does not assert only that X/S
  has quasi-compact relative diagonal.
- U is `OpenSubspace X`, an actual open subfunctor with inclusion representable by
  scheme open immersions. `hUqc` is exactly the same quasi-compact atlas condition
  on this open subfunctor. No schematicity, density, or nonemptiness is required.
- I is `QuasiCoherentIdeal X`, the existing quasi-coherent O_X-subobject of O_X;
  `hI` is Mathlib `SheafOfModules.IsFiniteType` on that submodule, meaning locally
  finitely many generators, without a finite presentation or Noetherian assumption.
- `hIU : IdealIsUnitAbove I (𝟙 X) U` states I|U = O_U. It tests all small-etale charts
  factoring through the given open; equality of their ideal sections with top is
  equality of ideal sheaves, not merely a claim about global sections of U.
- B is the first blowup. `B.space` is T_1 and `B.projection` is p. Its presentation
  requires every affine etale base change of p to be the ordinary scheme blowup
  of the restricted ideal. This is the explicit etale-descent characterization
  in the node's preamble and Stacks 085Q/085R/085S. Quantification over a presentation
  is a way of naming the blowup already fixed in the node, with its actual map,
  rather than an additional hypothesis about an arbitrary morphism. No arbitrary
  atlas, arbitrary comparison map, line bundle quotient, or regularity assumption
  replaces the blowup.
- J is `QuasiCoherentIdeal B.space`, `hJ` is its local finite generation, and `hJU`
  says exactly J|p^-1(U) = O. In the definition the composite W -> T_1 -> X must
  factor through U, so no arbitrary lift is substituted for p^-1(U).
- C presents the second blowup in J by the same affine etale scheme condition.
- The conclusion existentially produces L as the existing quasi-coherent ideal
  type, its `IsFiniteType` proof, and `IdealIsUnitAbove L (𝟙 X) U`.
- D presents Bl_L X and `e : C.space ≅ D.space` has the requested direction.
  `e.hom ≫ D.projection = C.projection ≫ B.projection` says the isomorphism is over X.
- The s and t in the final clause are the canonical inverse identifications of U
  with the two inverse-image opens. `IsPullback s (𝟙 U.val.toFunctor) ... U.val.ι`
  means precisely that the restriction of the composite projection over U is an
  isomorphism, with inverse s; the analogous square characterizes t. The equation
  `s ≫ e.hom.hom.hom = t` is exactly identity on U in these coordinates.
  These identifications are uniquely determined by the squares and their
  commutativity, so the clause does not quantify over arbitrary identifications.

Existing dependency declarations used, read in full with their docstrings:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: `AlgebraicSpace`, `IsEtale`, `IsSurjective`,
  `IsRepresentableWith`, `EtaleSite`, `etaleForget`, `structureSheaf`, `Modules`.
- Mathlib.AlgebraicGeometry.OpenImmersion: `IsOpenImmersion`, used by OpenSubspace.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: `IsClosedImmersion`, the
  scheme-test meaning of closed immersion from the node's preamble.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties: `MapIsLocally` and the
  flat, finite-type, separated and proper predicates. The module is imported as
  the node requests; none of those morphism hypotheses is added to the theorem.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule: `QCoh` specializes
  the existing Mathlib `SheafOfModules.IsQuasicoherent` predicate on this site.
- WeilConjectures.Blowup.Gluing: `Scheme.IdealSheafData.blowup`, `blowupMap`.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentIdeal: `QuasiCoherentIdeal`.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated:
  `IsAbsolutelyQuasiSeparated`.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace: `OpenSubspace`.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction: `schemeOpens` and
  `schemeOpensRingHom`. The latter is the canonical regular-function comparison.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceArtinRees: `idealSectionImage` (the existing
  section-ideal helper, not the Artin-Rees theorem as a proof input).
- Mathlib.AlgebraicGeometry.IdealSheaf.Basic: `Scheme.IdealSheafData.ofIdeals`.

The size-convention node is metatheoretic and explicitly has no module to import.
The three currently unstated proof nodes (finite-degree-ideal-descent,
blowup-chart-properties and blowup-product-ideal-comparison) have no usable Lean
records, so no import can yet be added for them. Their proof plan is transcribed
in the theorem docstring. The already stated quasi-coherent-module proof dependency
is imported through the definition interface. No dependency record is repaired.

Edge cases checked before writing: U empty makes the unit restrictions vacuous,
including on the empty test where the ring is zero; U = X forces both ideals to
be unit and both blowups to be identities. I = O gives the identity first blowup.
I = 0 permits only empty U unless X is empty, and its blowup is empty; C and the
resulting comparison can also be empty. J = O is the identity second blowup.
For a nilpotent I the Rees Proj is empty, as on the ordinary scheme charts.
No reduction, density, characteristic, separated-base or nonempty-atlas assumption
was added. The presentation admits non-schematic algebraic spaces and arbitrary
quasi-coherent ideals; finite type is imposed only in the main theorem.

Searches actually run via msearch.py (their unmodified records are in searches.jsonl):

- leanfinder, `A composition of admissible blowups of a quasi compact quasi separated
  algebraic space is a single blowup`: 8 hits on scheme quasi-compactness,
  quasi-separatedness and normalization, no composition-of-space-blowups theorem.
- loogle, `"blowup", "comp"`: no hits.
- Mathlib grep, `[Bb]lowup.*comp|comp.*[Bb]lowup`, AlgebraicGeometry: no hits.
- leansearch, `blowup algebraic space finite type ideal etale charts`: 8 unrelated
  ring/scheme etaleness hits.
- leanfinder, `An algebraic space blowup is characterized by its scheme blowup base
  changes on affine etale charts`: 8 scheme etaleness/affine-local-property hits,
  no algebraic-space blowup notion.
- loogle, `"blowup"`: no hits.
- Mathlib grep, `BlowupPresentation|blowupChartIdeal|blowup`, AlgebraicGeometry: no hits.
- rg of lean/WeilConjectures and lean/Sheaf for blowup and composition; rg of the
  item id in lean/WeilConjectures; names search in dag/lean_names_upstream.json:
  ordinary scheme blowups exist upstream, but no general space blowup.
- `tools/blueprint_refs.py search blowup` returned 66 blueprint notions, none a
  general algebraic-space blowup definition. DAG definition searches identify
  scheme blowups, log blowups and coordinate cases, which do not duplicate this
  affine-etale-chart presentation.

No statement correction and no STATEMENT-DISPUTED fault.

## New nodes

`def-sfb-space-blowup-presentation` supplies `blowupChartIdeal`, `BlowupPresentation`
and `IdealIsUnitAbove`. Source: spaces-divisors.tex, Tags 085Q, 085R, 085S and 086B.
It reuses the existing small-etale quasi-coherent ideal, section ideal, open-subspace,
Zariski-restriction and ordinary scheme blowup constructions. The chart ideal uses
`ofIdeals` on the canonically transported section ideals on affine opens: comap by
`schemeOpensRingHom` accounts for the difference between sections on an open and
on its corresponding open subscheme. Quasi-coherence ensures these ideals have
exactly the restriction compatibility which `ofIdeals` saturates. Each affine chart
of the specified projection is required to have a cartesian square with its actual
scheme blowup. This specifies the descended Rees Proj up to isomorphism over X.
No object is chosen from a bare Nonempty or a nonunique existence theorem; the
record is real data with a full chart characterization. The theorem takes the two
given blowups in this presentation-independent sense and supplies such a presentation
for the resulting ideal. Searches above, also recorded in the new node, found no
existing general space-blowup notion or DAG definition owner. Existing nodes for
quasi-coherent ideals, absolute quasi-separatedness and open subspaces are added
to the item's stmt_deps, along with this new node. All other item fields are unchanged.

Validation: the first dry run compiled both files and required the new-node
`import_flags` key. Added the empty list (no import faults) and expanded the two
combined dependency citations into separate exact bracket citations.

## Second reading by Q28

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
