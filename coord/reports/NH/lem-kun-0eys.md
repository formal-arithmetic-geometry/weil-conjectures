## Worker report

The module `Sheaf.AlgebraicGeometry.AbelianDegreeZeroFlatBaseChange` states
`AlgebraicGeometry.Etale.isIso_abelianBaseChangeMap_of_flat`. Its single proof is
`sorry`, with the complete three-step DAG proof in the declaration docstring.
There are no definitions, auxiliary theorems, new nodes or dependency repairs.
The mathematical statement is unchanged and agrees with the current blueprint
(main-20261015, sec-smooth-purity/sk-prop-sf-kunneth-ordinary/lem-kun-0eys.md)
and Stacks etale-cohomology.tex, lemma-fppf-reduced-fibres-base-change-f-star
(Tag 0EYS).

Every hypothesis and clause is represented as follows:

- The four schemes are the explicitly bound `X Y S T : Scheme.{u}`. The four
  edges are `h : Y ⟶ X`, `e : Y ⟶ T`, `f : X ⟶ S`, `g : T ⟶ S`.
- `sq : ChosenCartesianSquare h e f g` supplies commutativity and the chosen
  isomorphism `Y ≅ pullback f g`, respecting both projections.
- Flatness of f is `[Flat f]`.
- Local finite presentation of f is `[LocallyOfFinitePresentation f]`; neither
  quasi-compactness nor quasi-separatedness is imposed.
- Geometric reducedness of EACH scheme-theoretic fibre is precisely
  `hf : ∀ s : S, GeometricallyReduced (f.fiberToSpecResidueField s)`.
  This uses the fibre's canonical morphism to its residue-field spectrum,
  rather than reducedness of the fibre alone.
- Every abelian sheaf on the small etale site of T is covered by the arbitrary
  `F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}` binder, the recorded
  coefficient-size convention.
- The conclusion is `IsIso ((baseChangeMap AddCommGrpCat.{u + 1}
  sq.toCommSq.flip).app F)`. The flip changes `CommSq h e f g` into
  `CommSq e h g f`. Thus its source is f⁻¹g_*F and its target is h_*e⁻¹F.
- This is the exact recorded underived exchange, not an arbitrary morphism:
  `Etale.upperStar_map_baseChangeMap_app_counit` in the same upstream module
  identifies its transpose as h⁻¹f⁻¹g_*F → e⁻¹g⁻¹g_*F → e⁻¹F, using the
  square comparison and e⁻¹ of the counit of g.
- There is no property assumption on g and no torsion assumption on F.
  No separatedness, Noetherian, characteristic, nonemptiness or finiteness
  assumption has been introduced.

Dependency declarations used (full signatures and docstrings read):

- `def-weil-pbc-cartesian-square`: `AlgebraicGeometry.ChosenCartesianSquare`,
  `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`, including `isoPullback`,
  `hom_fst`, `hom_snd`, and inherited `toCommSq`.
- `def-weil-flat-morphism`: `AlgebraicGeometry.Flat`,
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`; its docstring gives the equivalent
  stalk-flatness characterization.
- `def-sbc-locally-finite-presentation`: Mathlib match
  `AlgebraicGeometry.LocallyOfFinitePresentation`,
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`.
- `def-pc-scheme-fibre`: `AlgebraicGeometry.Scheme.Hom.fiber` and
  `fiberToSpecResidueField`, `Mathlib.AlgebraicGeometry.Fiber`.
- `def-pc-geometrically-irreducible`: the reduced variant explicitly specified
  by its Mathlib match, `AlgebraicGeometry.GeometricallyReduced`,
  `Mathlib.AlgebraicGeometry.Geometrically.Reduced`.
- `def-weil-pbc-abelian-etale-sheaves`: `CategoryTheory.Sheaf`,
  `Mathlib.CategoryTheory.Sites.Sheaf`, specialized as recorded to the small
  etale topology and `AddCommGrpCat.{u + 1}`.
- `def-weil-pbc-inverse-image`, `def-weil-pbc-direct-image`:
  `AlgebraicGeometry.Etale.upperStar`, `lowerStar`,
  `upperStarLowerStarAdjunction`,
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.
- `def-weil-pbc-underived-exchange`: `AlgebraicGeometry.Etale.baseChangeMap`,
  `WeilConjectures.SixFunctors.BaseChange.Square`. Its mate definition and
  counit characterization fix the canonical arrow and its orientation.

All recorded proof-dependency modules are imported without `public`:
`WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`
(`AlgebraicGeometry.etaleInverseImageAlgebraicStructures`),
`WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits`
(`AlgebraicGeometry.etaleSetInverseImageCompositionUnits`),
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
(`Etale.lowerStarComp`, `Etale.upperStarComp`; their unit coherence is also
available through the proof imports),
`WeilConjectures.SixFunctors.BaseChange.Pasting`
(`Etale.squareUpperStarIso_paste_horiz_hom`,
`Etale.squareUpperStarIso_paste_vert_hom`), and
`Sheaf.AlgebraicGeometry.EtaleSetDegreeZeroFlatBaseChange`
(`AlgebraicGeometry.isIso_etaleSetDegreeZeroBaseChange_of_flat`). The exchange
and sheaf modules are already public statement imports. The two upstream
algebraic-structures/composition modules missing in the older local checkout
were read using `scompile.py --source`, which returned their current sources.

Edge cases checked before writing:

- Empty S: any morphisms to S have empty source; the fibre condition is vacuous
  correctly, and the map between sheaves on the empty site is invertible.
- Empty X with nonempty S, or empty T: the pullback and sheaf maps still make
  sense; no surjectivity or nonempty-fibre condition has been added.
- Zero sheaf F: exchange is the unique arrow between zero objects and is an
  isomorphism.
- Identity f or g: the canonical exchange specializes under the identity and
  composition comparisons, rather than requiring literal equality of chosen
  pullback functors.
- Non-torsion sheaves, such as the constant integers: allowed explicitly;
  there is no annihilator hypothesis. No characteristic is singled out.
- Arbitrary chosen pullback identification: only its inherited commutative
  square enters the canonical comparison, exactly as in the recorded definition.
- Universe u is explicit; coefficient size u+1 is the project convention for
  arbitrary sheaves on the small etale site, with no extra universe equality.

Searches for an existing exact statement:

- `msearch.py NH lem-kun-0eys leanfinder "Etale sheaf base change isomorphism
  for flat locally finitely presented morphism with geometrically reduced fibres"`:
  8 hits, on etale stability and Kahler differentials; no exact statement.
- `msearch.py NH lem-kun-0eys loogle '"baseChangeMap"'`: successful, 0 hits.
- `msearch.py NH lem-kun-0eys grep 'baseChangeMap|GeometricallyReduced'
  AlgebraicGeometry/Sites`: successful, 0 hits.
- `rg` on upstream WeilConjectures and side-project lean/Sheaf for this node id,
  `isIso_baseChangeMap.*flat`, and abelian-base-change names found
  `Etale.isIso_baseChangeMap_app_of_flat` in
  `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero`, and the
  existing set-valued theorem cited in this node's proof. Reading the full
  upstream signature showed that it quantifies over MODULE sheaves
  `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)`, not the specified
  `AddCommGrpCat` sheaves. The set theorem has Type-valued sheaves. Neither
  has the identical statement and neither is redefined here. The new statement
  uses the already existing abelian exchange and no replacement notion.

No statement dispute or node fault was found. No shared repository or upstream
source was edited, and no direct Git command or global build was run.

## Second reading by NH

I independently read the item JSON, its sandbox Lean module, the current
main-20261015 blueprint statement and proof, and Stacks
`etale-cohomology.tex`, lines 16599--16685, especially
`lemma-fppf-reduced-fibres-base-change-f-star` (Tag 0EYS). The following is my
object/hypothesis/conclusion inventory, matched to the actual signature.

| Node object or clause | Lean rendering | Verdict |
| --- | --- | --- |
| Four arbitrary schemes X, Y, S, T | `{X Y S T : Scheme.{u}}`, with explicit `universe u` | Exact; no field, Noetherian or separatedness assumption. |
| Edges Y → X, Y → T, X → S, T → S | `{h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S}` | Exact orientation and quantification. |
| Cartesian square and chosen Y ≅ X ×_S T | `sq : ChosenCartesianSquare h e f g` | Exact recorded structure: inherited commutativity, `isoPullback`, `hom_fst`, `hom_snd`. |
| f flat | `[Flat f]` | Exact Mathlib flatness; `Flat.iff_flat_stalkMap` identifies it with flat local-ring maps. |
| f locally of finite presentation | `[LocallyOfFinitePresentation f]` | Exact; not global finite presentation, quasi-compactness or quasi-separatedness. |
| Every scheme-theoretic fibre geometrically reduced over κ(s) | `hf : ∀ s : S, GeometricallyReduced (f.fiberToSpecResidueField s)` | Exact: `fiber` is the residue-field pullback and this morphism is its second projection. |
| Every abelian sheaf on T's small étale site | `(F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})` | Exact recorded abelian-sheaf encoding and coefficient size. |
| Canonical arrow f⁻¹g_*F → h_*e⁻¹F | `(baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq.flip).app F` | Exact canonical mate, not an arbitrary map; checked directly in `Square.lean`. |
| The arrow is an isomorphism | `IsIso` of that component | Exact entire conclusion, for each F after the geometric hypotheses. |
| No restriction on g, no torsion on F | No such binders or instances in the signature | Exact; no characteristic or nonemptiness assumption either. |

For the canonical-map check, `CommSq.flip` changes the arguments from
`h e f g` to `e h g f`. Substitution in the recorded `Etale.baseChangeMap`
signature gives `(lowerStar g ⋙ upperStar f).obj F` as source and
`(upperStar e ⋙ lowerStar h).obj F` as target. Substitution in
`Etale.upperStar_map_baseChangeMap_app_counit` gives its h-adjoint transpose
`h⁻¹f⁻¹g_*F → e⁻¹g⁻¹g_*F → e⁻¹F`, with the square comparison and e-inverse
image of the g-counit exactly as the node specifies.

The Stacks section introduction mentions quasi-compact, quasi-separated g
as a motivating setting. I also read the full general lemma 0EZX and its
proof immediately before 0EYS: neither lemma assumes that property of g,
and the proof identifies the four section expressions using the chart
U → V and its base change without it. Thus the unrestricted g in the node,
the current blueprint and this signature agrees with the actual source lemma.

I opened every statement dependency's JSON record and the relevant source
declarations, not just their names: `ChosenCartesianSquare` in the side
library; `Flat`, `LocallyOfFinitePresentation`, `Scheme.Hom.fiber`,
`fiberToSpecResidueField`, `GeometricallyReduced` and `geometrically` in
Mathlib; `Sheaf` and `Scheme.smallEtaleTopology` in Mathlib; `Etale.upperStar`,
`lowerStar`, `upperStarLowerStarAdjunction` in upstream
`UpperLowerStar.Defs`; and `Etale.baseChangeMap`, `squareUpperStarIso` and
its counit characterization in upstream `BaseChange.Square`.
`GeometricallyReduced` unfolds to reducedness after every field-valued
base change, and `geometrically_iff_of_commRing` identifies the maps into
Spec κ(s) with field extensions. It is the reduced variant expressly
recorded by `def-pc-geometrically-irreducible`, not irreducibility or mere
reducedness of the fibre.

I read the proof interfaces too: the complete live sources of
`etaleInverseImageAlgebraicStructures` and
`etaleSetInverseImageCompositionUnits` via `scompile.py --source`, the
composition isomorphisms in `UpperLowerStar.Defs`, the horizontal and
vertical square-comparison pasting signatures in `BaseChange.Pasting`,
and `isIso_etaleSetDegreeZeroBaseChange_of_flat` with its docstring in the
side library. They supply the objects and comparisons named by the
three-step proof docstring. That docstring retains all three DAG steps:
forgetting preserves the adjunction and square comparison; the composite
unit/naturality/triangle calculation identifies the precise set exchange;
the sectionwise inverse is additive and natural. There is one theorem
with proof `sorry`, no new definition, no hollow data, and no proved helper.
All stated proof-dependency modules are imported, privately when used only
in the proof. No new node, dependency module, statement correction or
`statement_change` is present or needed; H12/H13 and the correction-citer
audit consequently do not apply.

Edge cases: empty S, empty X, empty T and empty fibres are all admitted;
the fibre quantifier is correctly vacuous when S is empty. Zero F and
non-torsion F (including constant integers) are admitted. Identity f,
identity g and any compatible chosen pullback identification use the
same canonical comparison; no literal equality of pullback choices is
assumed. There is no degree or index-set binder to exclude degree zero
or an empty family. Every characteristic is allowed. All variables and
the universe are explicitly bound. Scheme size u and abelian coefficient
size u+1 are exactly the recorded small-site convention, without a new
equality of independent universes.

Independent searches, using different terms from the worker's searches:

- `msearch.py NH lem-kun-0eys leanfinder "inverse image along a smooth
  morphism commutes with pushforward abelian etale sheaves"`: eight hits,
  on scheme-module pushforward composition and sheaf-module pullback
  comparisons, with no exact étale abelian flat-base-change theorem.
- `msearch.py NH lem-kun-0eys loogle '"GeometricallyReduced"'`: twelve hits,
  including the definition, base-change instances, and reducedness
  results; no exchange theorem. An earlier two-name query was rejected
  by Loogle's parser and is not evidence of absence.
- `msearch.py NH lem-kun-0eys grep
  'BeckChevalley|beckChevalley|baseChangeMap' AlgebraicGeometry`: zero hits.
  Direct `rg` in Mathlib's algebraic geometry directory and in upstream
  `WeilConjectures` and side `lean/Sheaf`, using `beck.?chevalley`,
  `isIso.*[Bb]ase[Cc]hange`, `0EYS`, reduced-fibre conditions, and the
  proposed declaration name, found no exact duplicate or name collision.
  The upstream-name index has no collision either.
- I opened the nearby upstream theorem
  `Etale.isIso_baseChangeMap_app_of_flat` in
  `SixFunctors.Etale.SmoothBaseChange.DegreeZero`: its F is a
  `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)`, not an abelian sheaf
  in `AddCommGrpCat`. Passing through integer-module equivalence would
  require transporting the functors and canonical map; it is not the
  identical declaration required for an `existing: true` attachment.
  The side set-valued theorem likewise has `Type (u + 1)` coefficients;
  it is reused as the recorded proof dependency, not duplicated.

Result: no mathematical or Lean mismatch found. I changed only this report,
leaving the correct module and node record intact. A direct comparison
confirmed that the node differs from the shared base only in `lean`, and
`lean.statement` is verbatim equal to the module's theorem signature.
The Lean file has no line exceeding 100 characters and no local notation,
local instance, private construction, implicit variable, or hidden `let`.
`scompile.py NH lem-kun-0eys` on the absolute sandbox module path passed:
both the sandbox and library checks completed with no errors or warnings
(1.8 s and 2.4 s respectively).
