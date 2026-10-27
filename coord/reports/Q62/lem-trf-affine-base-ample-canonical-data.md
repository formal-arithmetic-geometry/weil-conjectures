## Worker report

The delivery states `AlgebraicGeometry.Scheme.Modules.affine_base_ample_canonical_data`
in `Sheaf.AlgebraicGeometry.AffineBaseAmpleCanonicalData`. Its only proof is `sorry`.
There are no new constructions, new nodes, dependency repairs, or statement corrections.
The original statement, proof plan and proof dependencies remain unchanged. The item's
`stmt_deps` gains the already landed definition owner
`def-sfb-relative-section-algebra-canonical-map`, as allowed by the landed-node rule in
brief-stage2 §5. This avoids copying the canonical section-algebra presentation.

The sources read were `morphisms.tex`, lemma-characterize-relatively-ample (01VJ),
its (3) implies (5) proof; lemma-relatively-ample-separated (01VI); and
lemma-pullback-ample-tensor-relatively-ample (0892), clause (2). The statement is the
affine-base specialization of these sources. It needs neither finite type nor
Noetherian hypotheses. No mathematical fault or disputed statement was found.

The correspondence, hypothesis by hypothesis and clause by clause, is:

| Node text | Lean rendering |
| --- | --- |
| Schemes X,T and morphism f:X→T | `{X T : Scheme.{u}} (f : X ⟶ T)` |
| f quasi-compact | `[QuasiCompact f]` |
| T affine | `[IsAffine T]` |
| Invertible module L | `(L : X.Modules) [L.IsInvertible]` |
| L ample on X | `(hL : IsAmple X L)` |
| Every affine open W of T | `∀ W : T.Opens, IsAffineOpen W → ...` |
| Restriction of L to f⁻¹W is ample | The pullback along `(f ⁻¹ᵁ W).ι` is asserted invertible and `@IsAmple` with that invertibility proof. Tensor pullback along an open inclusion is exactly restriction. |
| f separated and quasi-separated | `IsSeparated f ∧ QuasiSeparated f` |
| Canonical quasi-coherent graded algebra ⊕ f_* L^d | `∃ A : RelativeSectionAlgebra f L`. Its `data : T.GradedAlgebraData` is the existing equivalent affine-basis presentation of a quasi-coherent graded algebra, with actual coefficientwise base-change restrictions in each degree. |
| Degree-d sections on W are Γ(f⁻¹W,L^d) | `A.sectionEquiv W d` is an additive equivalence onto exactly `Γ(L.tensorPow d, f ⁻¹ᵁ W.1)`. |
| Canonical section algebra, including multiplication and degree zero | `A.smul`, `A.one`, `A.mul` and `A.restriction` fix scalars, the degree-zero unit, tensor-power multiplication, and every affine restriction. Thus A cannot be an unrelated algebra with merely isomorphic pieces. The grading identifies its underlying algebra with the sum of these pieces. |
| Evaluation ψ uses tensor pullback and adjunction | The existing `A.evaluate` pulls back the actual section using `tensorPullbackSectionAdjunction`, whose unit is `1 ⊗ s`, and applies `boundaryPullbackPowIso`. This is the sectionwise adjoint description of the counit evaluation f^* f_* L^d→L^d. |
| U(ψ) is all X | `A.GeneratesEverywhere` says that each x admits a positive-degree homogeneous section on an affine base neighbourhood whose germ lies outside the maximal ideal times the rank-one stalk. This is exactly surjectivity of that evaluation at x: a rank-one target is generated iff its fibre map is nonzero. No degree-zero generation is counted. |
| Canonical r to relative Proj | `∃ r : X ⟶ A.data.relProj, A.IsCanonicalMap r ∧ ...`. `IsCanonicalMap` requires the structural equality over T and the actual `Proj.fromOfGlobalSections` formula on every trivializing open chart, in every homogeneous degree. |
| r is an open immersion | `IsOpenImmersion r` |

In particular, the existential A is the usual algebra specified up to its
section-preserving graded isomorphism, and r is fixed by its canonical chart formula.
No arbitrary-map hypothesis, unspecified choice of a Nonempty object, or weakened
existence of some embedding is substituted for the canonical map.

Dependency declarations read and reused (names are fully qualified by the namespaces
shown):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType` and the
  imported `QuasiCompact` (only the latter is a hypothesis).
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsSeparated`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: `QuasiSeparated`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, `tensorPow`, `tensorPowAddIso`.
- `WeilConjectures.AlgebraicGeometry.Ample`:
  `AlgebraicGeometry.Scheme.Modules.IsAmple` and `nonvanishingLocus`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `AlgebraicGeometry.Scheme.Modules.tensorPullback`, `tensorPullbackSection`, and
  `tensorPullbackSectionAdjunction`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, with the imported sheaf tensor construction;
  the scheme tensor powers themselves reuse the existing scheme monoidal structure.
- `WeilConjectures.AlgebraicGeometry.GradedSheafStructures`: `GradedSheafAlgebra`;
  `WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra`:
  `Scheme.IsQuasiCoherentAlgebra`, `QuasiCoherentAlgebra`. The present statement uses
  the equivalent affine-basis `GradedAlgebraData`, not a second algebra notion.
- `WeilConjectures.AlgebraicGeometry.RelativeProj.Basic`:
  `AlgebraicGeometry.Scheme.GradedAlgebraData`, `relProj`, `relProjHom`, `relProjι`.
- `Sheaf.TraceFormula.SpaceLineModuleProjMap`:
  `AlgebraicGeometry.AlgebraicSpace.space_line_module_proj_map`; its scheme chart
  specialization is the formula in the reused `RelativeSectionAlgebra.IsCanonicalMap`.
- `Sheaf.AlgebraicGeometry.SchemeAmpleCanonicalProjCriterion` (definition owner
  `def-sfb-relative-section-algebra-canonical-map`):
  `AlgebraicGeometry.Scheme.Modules.RelativeSectionAlgebra`, `.evaluate`,
  `.GeneratesEverywhere`, `.IsCanonicalMap`. The general criterion theorem in this
  module is not applied or restated as this item's proof.

All recorded statement-dependency modules are public imports. Available proof inputs
are ordinary imports: affine permanence and affine-scheme morphisms from Mathlib's
`Morphisms.Affine`, separation cancellation and separated→quasi-separated from
`Morphisms.Separated`, morphism gluing from `Gluing`, and the recorded modules
`AmpleProjLocalChart`, `AmpleSeparated`, `AmplePullback`. The proof-only dependency
`lem-trf-qcqs-line-section-algebra-evaluation` has no recorded Lean module in the read
clone, so there is no import for it. No missing notion is needed to type this theorem.

Edge cases checked before drafting and again against the compiled signature:

- X may be empty; the ample and generation pointwise conditions are vacuous there,
  the section algebra and Proj charts include the zero rings, and no Nonempty instance
  occurs in the statement.
- The affine open W may be empty. No nonemptiness is imposed on its inverse image;
  restriction is still the tensor pullback to that open subscheme.
- T may be empty, in which case a map X→T already forces X empty; the signature does
  not exclude this case.
- All natural tensor degrees occur in the algebra and evaluation, including degree
  zero; generation uses only strictly positive degrees. There is no degree-one
  generation, finite generation, equality A_0=O_T, or fixed power assumption.
- The scheme universe u is explicitly bound and arbitrary. No independent smaller
  universe of test schemes or algebras, or hidden auto-implicit parameter, occurs.
- No claim that an arbitrary open restriction of an ample module is ample is used:
  W and T are affine, so the inverse-image inclusion is affine. This matters because
  ampleness includes quasi-compactness in the recorded definition.

Searches actually run through `msearch.py Q62 lem-trf-affine-base-ample-canonical-data`:

| Tool | Query | Actual outcome |
| --- | --- | --- |
| LeanFinder | `A quasi compact morphism to an affine scheme with an ample invertible module has a canonical open immersion into relative Proj of its section algebra` | 8 hits, including `Proj.fromOfGlobalSections`, `Proj.toBasicOpenOfGlobalSections`, `Proj.instIsOpenImmersionAwayι`, `Scheme.instIsOpenImmersionToSpecΓOfIsQuasiAffine`, `Proj.awayι`, `Proj`, `Proj.instQuasiCompactToSpecZeroOfFiniteTypeSubtypeMemOfNatNat`, and `ProjectiveSpectrum.Proj.toSpec`; no exact theorem. |
| Loogle | `AlgebraicGeometry.Scheme.Modules.IsAmple, AlgebraicGeometry.IsOpenImmersion` | Reported 0 hits and `unknown identifier 'AlgebraicGeometry.Scheme.Modules.IsAmple'`; that project name is not in Loogle's Mathlib index. This is not evidence that the project lacks IsAmple. |
| grep (Mathlib AlgebraicGeometry) | `IsAmple\|ample.*[Pp]roj\|canonical.*[Pp]roj` | 5 hits, all standard-chart descriptions in ProjectiveSpectrum/Basic.lean, no exact theorem. |
| LeanSearch | `An ample invertible sheaf on a scheme over an affine scheme defines a canonical open immersion into the relative Proj of its section algebra` | 8 hits: `Proj.fromOfGlobalSections`, `Proj.instIsOpenImmersionAwayι`, `IsAffineOpen.isOpenImmersion_fromSpec`, `Scheme.IsQuasiAffine.toIsImmersion`, `Scheme.instIsOpenImmersionToSpecΓOfIsQuasiAffine`, `IsAffineOpen.fromSpec_top`, `IsAffineOpen.isoSpec`, and `Proj.basicOpenIsoSpec_inv_ι`; no exact theorem. |

Local `rg` searches were also run in `lean/WeilConjectures`, `lean/Sheaf`, and
`dag/lean_names_upstream.json` for the item id and the proposed declaration name
(no existing declaration), and for `sectionAlgebra`, `SectionAlgebra`,
`section_algebra`, `RelativeSectionAlgebra`, and canonical evaluation. They found the
published `SchemeAmpleCanonicalProjCriterion` module and its definition owner in
`dag/nodes/sec-six-functors-basics/def-sfb-relative-section-algebra-canonical-map.json`.
That definition's full statement and recorded declarations were read. The existing
general relative-ampleness equivalence is not this exact affine-base conjunction.
Mathlib's `Proj.fromOfGlobalSections` source and signature were also read; it
constructs a map from a supplied ring homomorphism and does not assert this theorem.

Validation: `scompile.py Q62 lem-trf-affine-base-ample-canonical-data` compiled the
single delivered file in both sandbox and library module modes on the server, with
no errors or warnings (reported times 1.7 s and 1.6 s). Both auto-implicit options are
false. All lines of the module are at most 100 characters. Delivery dry-run results
are recorded below when available.

## Second reading by Q62

This is the dispatcher's worker's second pass, not a claim of independent review;
the maintainer supplies the independent review after delivery, as the brief specifies.
I reopened the original node and the Lean file and checked every hypothesis and
conjunct against the table above. `IsAmple X L` is the absolute notion required,
`[IsAffine T]` is retained, and the first conjunct quantifies over every affine open,
including the empty open. Its existential h supplies the proof needed to form the
recorded ampleness predicate; it is not an extra restriction on the open.

I read `RelativeSectionAlgebra` again: its additive equivalences alone would be
insufficient to fix an algebra, but the scalar, unit, multiplication and restriction
fields are present. Its data require degreewise coefficient base change, so the
quasi-coherence clause is present. I read `.evaluate`, `.GeneratesEverywhere`, and
`.IsCanonicalMap` again: evaluation uses the normalized tensor adjunction; generation
uses positive degrees and the rank-one stalk condition; the map predicate includes
both the equality over T and all homogeneous-fraction chart formulas. The final
`IsOpenImmersion r` therefore applies to that canonical map. There is no separate
arbitrary embedding. Separatedness and quasi-separatedness are conclusions, never
extra assumptions. No mismatch was found in this pass and no Lean change was needed.
The one dependency addition records the existing definition owner explicitly.

## Import-cycle note

The reused definition owner's module also contains the theorem of
`lem-trf-scheme-ample-canonical-proj-criterion`, whose proof_deps include this item.
This delivery imports that module for its real definitions only. The corresponding
future proof-only import of `AffineBaseAmpleCanonicalData` into
`SchemeAmpleCanonicalProjCriterion` must be omitted under stages/2-statements §3.7,
because it would close an import cycle. No DAG edge to that downstream theorem has
been added, and this item's proof docstring never invokes that theorem. The added
statement edge is to the independent definition node, whose own statement dependencies
do not lead back to this item.

## Delivery validation

The first `deliver2.py --no-push` passed preflight and per-file compilation and printed
`OK (dry run)` for commit `9c065b1db7a`. This report addition records the import-cycle
exception; the final dry run and push use the updated report.
