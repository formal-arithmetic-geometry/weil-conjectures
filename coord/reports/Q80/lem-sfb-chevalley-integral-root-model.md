## Worker report

The delivery states `AlgebraicGeometry.ChevalleyIntegralRootModel.exists_integral_root_model`
in `Sheaf.AlgebraicGeometry.GroupScheme.ChevalleyIntegralRootModel`. Its only postponed proof
is this theorem. The seven preceding helpers contain actual canonical data and carry this
node's blueprint identifier. No node statement, split, or proof plan is changed.

This is a stage-2 assignment: the current live node is split, has no `lean` record, and
`coord/queue.tsv` assigns it to stage 2. The inherited unchanged-item rejection concerned
stage-1 delivery of Q83's already accepted split. The current work records its Lean statement
through `deliver2.py`, following the stage-handoff paragraph of `coord/brief-stage2.md` §0.
There was no retained Lean module or report in the supplied sandbox when this attempt began.

Hypotheses, individually:

- `F : Type u`, `[Field F]`, `[IsAlgClosed F]` are the given algebraically closed field,
  with no restriction on characteristic.
- `S : Grp (Over (Spec (.of F)))` is the group scheme. `hS : IsSemisimpleGroupScheme S.X`
  supplies smoothness, connectedness, affineness, finite type, and precisely the absence of
  nontrivial smooth connected solvable normal closed subgroup schemes. Its definition uses
  the terminating scheme-theoretic commutator series, not solvability of rational points.
- `hsc` quantifies over every semisimple source, group homomorphism, surjectivity, a finite
  scheme-theoretic kernel, and centrality on every commutative F-algebra, and concludes
  `IsIso f`. The finite-morphism predicate is equivalent to finite-dimensional coordinate
  algebra for this affine kernel. This follows the existing interface used by
  `exists_rho_section_modules`; no distinct simply-connectedness predicate is introduced.
- `T B U`, `iT iB jT iU`, and `hTB` give the chosen subgroup diagrams.
- `hT` says maximal torus; `hsplit` supplies its split rank and group isomorphism;
  `hB` says the chosen Borel is a maximal smooth connected solvable closed subgroup.
- Each clause of `hU` gives the closed normal inclusion, smoothness, connectedness and
  unipotence of U; its final universal factorization says it is the largest such subgroup
  of B. This is exactly the radical interface of `reductive_borel_pair_structure`.
- The two commutative-group witnesses expose the character/cocharacter additive Hom groups.
  The two `ModObj` instances and `hconjS`, `hconjB` fix the actual conjugation actions.
- `Φ`, `P`, `[P.IsReduced]`, `b` give the labelled reduced crystallographic root datum
  on the actual character and cocharacter groups and its simple base. `hroot` fixes root
  labels. `hpair` fixes the integer character/cocharacter pairing by composition with
  the integer power map; `hweights` says exactly that the nonzero tangent character
  weights are Φ; `hpos` identifies the Borel tangent roots with the chosen positive system.
- `Ua`, `ia`, and the six clauses of `hua` are the closed, smooth, connected, normalized
  root groups with their specified tangent weight lines and additive-group isomorphisms.
  They use exactly the interface of `reductive_root_subgroup_parametrizations`.
- `x` consists of arbitrary isomorphisms from the recorded additive group to the simple
  root subgroups, indexed by `b.support`. No normalization of the given pinning is imposed.

Conclusion, clause by clause:

- `GZ TZ BZ UZ : Grp (Over integerBase)` are group schemes over Spec Z. The universe lift
  in `integerBase` is a ring-equivalent copy of Z, so it imposes no size restriction on F.
- The four scheme-property conjuncts for each of these four group schemes say smooth,
  affine, locally finite type, and quasi-compact, hence affine finite type over Z.
- `tB`, `bG`, `uB`, and `tB ≫ bG` give the four closed subgroup inclusions. They are
  bundled group homomorphisms; their `IsClosedImmersion` clauses retain scheme structure.
- The existential `GrpObj integralLine` is pinned to coordinate addition on **all test
  schemes** by the two coordinate equations (zero and addition). Thus it is exactly the
  integral additive group, with its actual affine line as underlying scheme. This is
  theorem output; no definition selects an unspecified group structure from a sorry.
- `y` is a homomorphism from that group for every root, and the universal closed-immersion
  conjunct requires every root map, positive and negative, to be a closed immersion.
- `scalarChange R` is `(Over.pullback (integerMap R)).mapGrp`. `integerMap` is Spec of
  the unique integer ring homomorphism. Thus every special or generic fibre is the
  canonical fibre product, not an arbitrary comparison scheme or arrow.
- `aF` and `aQ` identify this pulled-back line with the existing standard additive groups.
  The two coordinate equations fix their affine coordinates to Polynomial.X. Consequently
  these are the canonical additive-group identifications, not freely chosen rescalings.
- `fibreIso` is the required special-fibre group isomorphism. `eT eB eU` and the three
  commutative squares say it carries the chosen integral subgroups onto T, B and U.
- `er`, the root squares, and `er α = x α` on `b.support` preserve every root label and
  give exactly the prescribed simple-root parametrizations, without a residual scalar.
- Positive-root factorization is the quantified `z : Grp.mk integralLine ⟶ UZ` equation.
- `N`, `β` and `θ` give some enumeration of the positive roots and an isomorphism from
  the actual N-dimensional integral affine space to UZ. Its map into GZ is the ordered
  list product of the canonical coordinate projections followed by the corresponding
  root maps. The next equation sends the origin to the identity.
- The rational tangent Lie algebra is the existing `GrpObj.Lie` of the canonical
  generic fibre over `ULift ℚ`. Its existing bracket is fixed throughout. The existential
  `LieAlgebra ℚ` is pinned by `q • v = (ULift.up q) • v`; only scalar restriction is
  exposed as output, with no freedom to alter its module or bracket.
- `FiniteDimensional ℚ` and `HasTrivialRadical ℚ` state finite dimensionality and
  semisimplicity. `H` is identified, as a subset, with the differential image of TZ_Q.
  `IsLieAbelian H` and its maximality clause are the splitting maximal abelian Cartan.
- `Q`, its root-system/crystallographic/reduced witnesses, and its evaluation-pairing
  equation are the rational root system on H, in exactly the form of the Kostant node.
  `bQ.support = b.support` and equality of every integer/rational root-coroot pairing
  identify the based root systems with the original labels.
- The tangent-point equation for every `e α` fixes it to the image of the additive
  dual-number point ε under the generic root map. This is precisely d(y_α)_Q(1).
  The existing `GrpObj.Lie` is the dual-of-cotangent tangent space; for an affine group
  it is canonically the counit derivations on its coordinate ring. Its bracket is the
  usual commutator bracket obtained from left-invariant derivations, with the sign
  fixed by the group commutator xyx⁻¹y⁻¹, as in the upstream Lie/Bracket source.
- The nonzero root-weight clauses, opposite-root equation, ±(chainBotCoeff+1) root-string
  constants, and zero-bracket equation are verbatim the Chevalley normalizations in
  `exists_kostant_integral_pbw_basis`. `C` is the full basis consisting of the simple
  coroots and these root vectors. No choice of a weaker basis normalization is made.
- If Φ is empty, the four integral groups are isomorphic to the trivial group and the
  generic tangent Lie algebra is subsingleton, i.e. zero. This branch is explicitly stated.

Dependencies read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.FieldTheory.IsAlgClosed.Basic`:
  `IsAlgClosed`, the algebraic-closure notion used in this statement.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, `Grp`, `Functor.mapGrp`;
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`: group-scheme interpretation,
  scheme-theoretic kernels, closed subgroups and group morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`; the ordinary locally-finite-type
  and quasi-compact predicates render finite type without changing its meaning.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`:
  `AlgebraicGeometry.reductive_borel_pair_structure` and
  `AlgebraicGeometry.semisimpleGroupScheme_isReductive`; the full signature and proof
  docstring were read. Its `IsSemisimpleGroupScheme`, `IsBorelGroupScheme`,
  `ReductiveTorusCentralizer.IsMaximalTorus`, character weights and root datum are reused.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations`:
  `AlgebraicGeometry.TorusCharacterTangent.reductive_root_subgroup_parametrizations`
  and `additiveParameterPoint`; the complete signature and docstring were read.
- `Sheaf.Algebra.Lie.KostantIntegralPBW`:
  `LieAlgebra.exists_kostant_integral_pbw_basis`; its precise rational root-pairing,
  opposite-root, root-string and basis clauses were read and retained.
- `Mathlib.AlgebraicGeometry.AffineSpace`: `AffineSpace`, `coord`, `homOfVector` and
  `homOfVector_over` construct the actual affine chart and all coordinate arrows.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Basic`, `.Bracket`, `.Differential`,
  `.Ring`, `.Field`: `GrpObj.Lie`, the tangent bracket, differential, and tangentPoint.
- `Sheaf.LinearAlgebra.RootDatumLatticeEmbedding` is a private proof import for the
  already stated proof prerequisite. Other proof prerequisites currently have no Lean
  record; their future proofs are described in the theorem's fourteen-step docstring.

Searches (2026-10-24):

- `msearch.py ... leanfinder` with "Integral Chevalley group scheme over the integers
  realizing a prescribed pinning of a semisimple simply connected group over an
  algebraically closed field": eight unrelated root-pairing/Geck and arithmetic hits;
  no integral group-model theorem.
- `msearch.py ... leansearch` with "A semisimple simply connected group over an
  algebraically closed field has an integral Chevalley group scheme with prescribed
  root parametrizations": eight hits including RootDatum, Weyl groups and Geck
  semisimplicity; no theorem providing the integral model.
- `msearch.py ... loogle` with `CategoryTheory.GrpObj`: twelve hits identify the existing
  group-object structure, its bundled category and transfer operations. An earlier
  comma-separated query containing `AlgebraicGeometry.GrpObj` reported that name unknown;
  the corrected query above uses the actual CategoryTheory namespace.
- `msearch.py ... grep` for `Chevalley|SimplyConnected|baseChange` in AlgebraicGeometry:
  base-change predicates, no integral Chevalley construction. A second Mathlib search
  for `Chevalley|Kostant|SimplyConnected` returned unrelated topology, number theory,
  Jordan-Chevalley and Lie-Rinehart material.
- `rg` of `Chevalley|chevalley|IsSimplyConnected|SimplyConnected` in the project's
  group-scheme and Lie modules found the already recorded rational normalization and
  PBW modules, but no integral group model. Wider project searches found existing
  semisimplicity and the inline simply-connectedness interface in RhoSectionModules.
- The literal blueprint id search in `lean/WeilConjectures` returned no declaration;
  the prospective module/declaration name search in `lean/Sheaf` returned no duplicate.
- Read Milne's local PDF, extracted to the sandbox: equation (153), Theorems 23.72--23.74,
  and the paragraph Reductive groups over Z; these match the integral construction and
  fibre interpretation. The node already records that a full proof of the integral
  root chart is a further Steinberg input. No new claim of a field-only proof is made.

Edge cases checked before finalizing: empty root system, rank zero, empty positive-root
list (`N = 0`, product is identity), arbitrary positive characteristic including 2 and 3,
nonreduced test algebras, arbitrary scales of the given simple root maps, and fields in
any universe. The integral line law is tested on all schemes, hence is not a statement
only about rational points. No extra separability, characteristic or nonemptiness
hypothesis is imposed. No STATEMENT-DISPUTED issue or source-based correction was needed.

## Second reading by Q80

The dispatcher explicitly prohibits starting another agent, and this worker was started
without a lead. This section records a separate in-thread reading, not an independent
worker's approval; the maintainer's independent review remains required.

Read the node and all clauses of the module a second time. Checked that the root chart is
an isomorphism of schemes rather than groups, that y maps are group homomorphisms, that
specialization preserves the coordinate (so the pinning equation has no hidden scalar),
that the generic Lie algebra and bracket are the actual tangent ones, and that root-string
constants are precisely those of the recorded Kostant statement. Confirmed every input
encodes existing chosen Borel/root data, and every output has its corresponding node clause.
Checked the zero-rank branch and the universes of the affine coordinates and test objects.
The only initial compiler repairs renamed symbols conflicting with scoped group/action
notation; they did not alter the mathematical statement.

Validation: `scompile.py Q80 lem-sfb-chevalley-integral-root-model` compiled both the
sandbox module and the real module name cleanly (12.0 s and 12.4 s), with no errors or
unexpected warnings, on 2026-10-24. The missing `ULift` field instance was supplied by
importing the existing `Mathlib.Algebra.Field.ULift`; no new instance was defined.
