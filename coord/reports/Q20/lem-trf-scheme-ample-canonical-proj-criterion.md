## Worker report

Item: `lem-trf-scheme-ample-canonical-proj-criterion`.
Module: `Sheaf.AlgebraicGeometry.SchemeAmpleCanonicalProjCriterion`.
The only postponed theorem is
`AlgebraicGeometry.Scheme.Modules.isAmple_iff_canonical_section_proj_openImmersion`.
Its docstring contains all nine DAG proof steps. Every helper has actual data, with no
choice from an uncharacterized existence assertion and no additional postponed lemma.
No node statement was corrected and no independent definition node was needed.

Source read: `literature/stacks-project/morphisms.tex`, labels
`definition-relatively-ample` (01VH), `lemma-relatively-ample-separated` (01VI),
`lemma-characterize-relatively-ample` (01VJ), including its proof of (3) => (5) and
(4) => (1). Read the item and all twelve statement-dependency statements and records.
Live sources unavailable in the old source checkout were read with prescribed
`scompile.py --source` calls: Ample, GradedSheafStructures, QuasiCoherentAlgebra,
RelativeProj.Basic, RelativeProj.GradedAlgebraData, SpaceLineModuleProjInput and
SpaceLineModuleProjMap. The tensor-pullback section adjunction and comparison sources
were read from the shared side checkout.

Clause-by-clause rendering:

- Schemes and the named morphism: `{X T : Scheme.{u}} (f : X ⟶ T)`.
- Standing quasi-compactness: `[QuasiCompact f]`; there is no standing
  quasi-separatedness, separatedness, finite-type, Noetherian or field assumption.
- Invertible O_X-module: `(L : X.Modules) [L.IsInvertible]` uses the recorded upstream
  `Scheme.Modules.IsInvertible`.
- Condition (1): for every `V : T.Opens` with `IsAffineOpen V`, the module
  `(tensorPullback (f ⁻¹ᵁ V).ι).obj L` satisfies the recorded absolute `IsAmple`.
  The existential `h` supplies its required invertibility proof; it adds no hypothesis.
  Together with the standing quasi-compactness this is exactly relative ampleness.
- Condition (2)'s quasi-separatedness is the first existential witness `_hqs`.
  Only after that witness is `A : RelativeSectionAlgebra f L` introduced.
- The canonical algebra is specified by `A.data : T.GradedAlgebraData`, the existing
  quasi-coherent affine-basis graded algebra accepted by the recorded relative Proj.
  `A.sectionEquiv V n` identifies its WHOLE degree-n component bijectively and additively
  with `Γ(L.tensorPow n, f ⁻¹ᵁ V.1)`. `smul` gives the structural O_T action via `f.app`;
  `one` specifies the degree-zero unit; `mul` is the existing tensor multiplication
  `tensorPowAddIso` applied to `tmulSection`; `restriction` is the actual restriction of
  L^n on inverse-image opens. Thus this is a presentation of the specified algebra,
  not an arbitrary graded algebra assumed to have desirable properties. The affine
  components and restrictions determine the sheaf and its multiplication uniquely.
- The notation `f_*N(V)=N(f^{-1}V)` is rendered literally by those section equivalences
  and by the existing `pushforward` in the canonical comparison.
- Evaluation is specified, including its scalar normalization, by `A.evaluate`: the
  unit of `tensorPullbackSectionAdjunction j` sends s to `1 ⊗ s`, the restriction map
  moves to the entire chart W, and `boundaryPullbackPowIso` identifies the result with
  the tensor power of the pulled-back L. No evaluation map is supplied freely.
- `A.GeneratesEverywhere` renders U(psi)=X. At every x it requires an affine base
  neighbourhood, n>0, and a homogeneous section whose germ is outside the maximal
  ideal times the rank-one stalk. For a map to a rank-one module over a local ring,
  surjectivity is equivalent to some local generator having a unit coefficient.
- Relative Proj and the structural map are exactly `A.data.relProj` and
  `A.data.relProjHom` from the recorded dependency. The arrow `r` has this target.
- `A.IsCanonicalMap r` fixes r over T and on every trivializing open scheme chart
  by `Proj.fromOfGlobalSections` followed by `A.data.relProjι V`. The homogeneous
  ring map must agree on EVERY degree with the evaluated sections after the existing
  `AlgebraicSpace.trivializedPower` trivialization. It cannot be chosen independently.
  This is the scheme chart clause of the recorded `GradedLineMap.IsCanonicalMap`,
  specialized to the specific section algebra and its evaluation, rather than a
  second general relative-Proj construction. The shared lemma's scheme specialization
  supplies this same local map. The helper belongs to the canonical construction
  introduced in this item, as allowed by the missing-helper rule.
- The required property is exactly `IsOpenImmersion r`.
- The alternative algebra description is the first conjunct: for any proof of
  `QuasiSeparated f`, the canonical map
  `relativeSectionAlgebraCoproductComparison f L` is `IsIso`. Its source is
  `∐ n, f_*(L^n)` and target `f_*(∐ n, L^n)`. Its restrictions to the summands are
  `f_*` of the actual coprojections. Since the products on both sides are the tensor
  products of these sections, this is the indicated graded-algebra identification.
- The last conjunct gives `IsSeparated f` from condition (1). Together with the
  equivalence, it gives separatedness from either condition, exactly as requested.

Dependency declarations used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType and QuasiCompact:
  `AlgebraicGeometry.QuasiCompact` (only the quasi-compact clause of the finite-type
  definition node is needed here).
- WeilConjectures.AlgebraicGeometry.Modules.Invertible:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
- WeilConjectures.AlgebraicGeometry.Ample:
  `AlgebraicGeometry.Scheme.Modules.IsAmple`; the generation predicate uses its same
  maximal-ideal-times-stalk definition, allowing sections on a base inverse image.
- Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated: `QuasiSeparated`.
- WeilConjectures.AlgebraicGeometry.GradedSheafStructures: `GradedSheafAlgebra`;
  its homogeneous multiplication is rendered through the existing quasi-coherent
  affine-basis `GradedAlgebraData` rather than copied to a new sheaf algebra structure.
- WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra: `QuasiCoherentAlgebra`;
  quasi-coherence of the input is already built into `GradedAlgebraData`.
- WeilConjectures.AlgebraicGeometry.RelativeProj.Basic:
  `Scheme.GradedAlgebraData.relProj`, `.relProjHom`, `.relProjι`.
- Mathlib.AlgebraicGeometry.OpenImmersion: `IsOpenImmersion`.
- Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction:
  `Scheme.Modules.tensorPullbackSectionAdjunction` and the existing `tensorPullback`.
- Sheaf.TraceFormula.SpaceLineModuleProjMap and its public Input:
  `AlgebraicSpace.space_line_module_proj_map` (proof input),
  `AlgebraicSpace.trivializedPower`, and its `GradedLineMap.IsCanonicalMap` chart formula.
- Mathlib.AlgebraicGeometry.Morphisms.Proper: `IsSeparated`.

The extra helpers listed in `lean.declarations` specify the canonical algebra,
evaluation, generation, chart equations, and coproduct comparison introduced by this
item. They do not redefine an existing general ampleness, tensor, graded-algebra,
quasi-coherence, or Proj notion. The recorded statement and proof dependency modules
are imported; the two new Proj-twist proof lemmas have no Lean module on this base.

Edge cases checked against the definitions and source:

- Empty X: pointwise generation is vacuous, and the unique arrow from the empty
  scheme is an open immersion. No nonemptiness assumption was introduced.
- Empty affine base opens: their inverse images are empty and their section rings
  are zero rings. Neither the algebra presentation nor the chart formula excludes them.
- Arbitrary base scheme T, without separation or quasi-compactness assumptions on T.
- Tensor exponent zero is retained in all algebra identifications and unit equations;
  generation uses n>0, never a degree-one restriction.
- The algebra need not be generated in degree one, finite type, or finitely generated.
  Its degree-zero part is f_*O_X, with its structural O_T map, not necessarily O_T.
- Quasi-compact non-quasi-separated f is permitted at the theorem boundary. The
  forward argument derives separation before constructing the quasi-coherent algebra.
- A quasi-compact open in a general Proj need not have invertible O(1); the proof
  docstring explicitly uses positive common twists, as the repaired DAG does.

Searches actually run using msearch.py with group Q20 and this item:

- leanfinder: "A quasi compact scheme morphism and invertible module is relatively
  ample if and only if canonical map to relative Proj of section algebra is open
  immersion". Eight Proj/chart and quasi-affine hits; no exact criterion.
- loogle: `"Proj", "ample"`. Zero hits.
- grep: `sectionRing|sectionAlgebra|SectionRing|graded.*[Ss]ection` in AlgebraicGeometry.
  Zero Mathlib hits.
- leansearch: "A relatively ample invertible sheaf is characterized by its canonical
  section algebra relative Proj open immersion". Eight Proj construction/fraction hits;
  no relative-ampleness theorem.
- grep: `IsAmple|relative.*ample|ample.*Proj` in AlgebraicGeometry. Zero Mathlib hits.
- rg of upstream WeilConjectures for the item id, sectionRing/sectionAlgebra/SectionRing,
  relativelyAmple, and the proposed declaration names: no exact criterion or relative
  section-algebra presentation. Upstream Modules.Ample is the projective-over-field
  notion, which is not used for absolute ampleness here.
- rg of side lean/Sheaf found the absolute `InvertibleSectionRing`,
  `AmpleProjLocalChart`, the general `SpaceLineModuleProjInput/Map`, and existing
  relative-ampleness statements. Read these interfaces. None already states this item
  or presents the relative pushforward section algebra with its evaluation.
- rg of DAG nodes found this item and its citers, rather than another existing node
  for this particular canonical section algebra presentation.

No STATEMENT-DISPUTED and no source or node fault found.

## Second reading by Q20

This is the author's second pass, with the node and source module open; no other
agent was started, as the dispatcher brief requires. The maintainer supplies the
independent review. Rechecked the twelve dependency records and Stacks 01VH/01VI/01VJ.
The essential order is preserved: only quasi-compactness is assumed; quasi-separatedness
is inside (2), before its algebra witness. The piece equivalences are surjective,
so no subalgebra of the section algebra can pass as the canonical algebra. The scalar,
unit, tensor-product and restriction fields exclude an algebra with incorrect operations.
The map r is over T and fixed by homogeneous images on all trivializing open charts,
not merely asserted to exist as some open immersion. The generation predicate permits
all positive degrees. The separate canonical coproduct comparison accounts for the
alternate algebra expression. The final implication plus the iff gives separatedness
under either condition. No statement correction or dependency-record replacement was
needed in this pass.

Validation: compilation and delivery preflight are recorded below after completion.

Validation completed: `scompile.py Q20 lem-trf-scheme-ample-canonical-proj-criterion`
compiled the module separately in sandbox and final-name modes without errors or
warnings. `deliver2.py Q20 lem-trf-scheme-ample-canonical-proj-criterion --no-push`
then recompiled the final source, checked the delivery against the current server
base, and printed `OK (dry run): commit 322a5101bf passes the preflight and compiles`.
Only the item's node, its owning module, and this report are in the delivery.
