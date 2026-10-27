## Worker report

Item: lem-sfb-finite-type-points-detect-open. Group Q33, stage 2.

The module lean/Sheaf/AlgebraicGeometry/FiniteTypePointsDetectOpen.lean states
AlgebraicGeometry.Scheme.finiteTypePoints_meet_locallyClosed_and_detect_open.
It is one theorem with a conjunction of the locally closed existence assertion
and the open detection consequence. Its only proof is `sorry`; no definitions
or additional theorems are introduced. The node changes only in `lean`.

Source checked directly: literature/stacks-project/morphisms.tex,
definition-finite-type-point (Tag 02J1) and lemma-enough-finite-type-points
(Tag 02J4). The latter treats arbitrary schemes and locally closed subsets.
The detection consequence follows by applying it to the closed complement of
an open. The node's existing proof is included step by step in the docstring,
with all cited node ids, including the affine-local argument rather than the
source's reduced locally closed subscheme argument.

Hypothesis and clause correspondence:

- An arbitrary scheme V is the explicit binder `(V : Scheme.{u})`; `universe u`
  is explicit, with no Jacobson, Noetherian, quasi-compactness, separatedness,
  affineness, or nonemptiness assumption on V.
- The underlying point set is the standard coercion of V to a type. Both Z and
  O are universally quantified `Set V`, so every subset in the node is covered.
- Locally closed is `IsLocallyClosed Z`. Mathlib/Topology/Defs/Basic.lean:119
  defines it literally as `∃ U Z', IsOpen U ∧ IsClosed Z' ∧ Z = U ∩ Z'`.
- Nonempty is exactly `Z.Nonempty`; the implication does not assert a point of
  an empty locally closed set.
- The canonical morphism Spec κ(v) → V is `V.fromSpecResidueField v`, from
  Mathlib.AlgebraicGeometry.ResidueField. Its full definition is
  `Spec.map (V.residue v) ≫ V.fromSpecStalk v`, with domain
  `Spec (V.residueField v)`. The residue field is the quotient of the stalk by
  its maximal ideal, as required; no arbitrary field-valued morphism is used.
- Finite type is rendered in both clauses by the exact conjunction
  `LocallyOfFiniteType (V.fromSpecResidueField v) ∧
  QuasiCompact (V.fromSpecResidueField v)`, following the recorded interface of
  def-weil-finite-type-morphism. Thus the quasi-compact clause is retained even
  though it is automatically true for this particular source spectrum.
- The point in Z is `∃ v ∈ Z, ...` in the first conjunct. This includes the
  finite type assertion for that same point v and the same ambient V.
- An open subset O is `∀ (O : Set V), IsOpen O → ...` in the second conjunct.
  Containing every finite type point is the universal implication
  `∀ v : V, (LocallyOfFiniteType ... ∧ QuasiCompact ...) → v ∈ O`.
- The requested equality O = |V| is precisely `O = Set.univ`. Both clauses
  appear as a conjunction for each V; neither is omitted or replaced by density.

Statement dependency interfaces read and used:

- def-pc-scheme: Mathlib.AlgebraicGeometry.Scheme, declarations
  AlgebraicGeometry.Scheme and AlgebraicGeometry.Scheme.Hom.
- def-weil-residue-field: Mathlib.AlgebraicGeometry.ResidueField,
  AlgebraicGeometry.Scheme.residueField; the same module supplies the canonical
  AlgebraicGeometry.Scheme.fromSpecResidueField used in the signature.
  The recorded Hom.residueFieldMap signature and docstring were also checked.
- def-weil-affine-spectrum: Mathlib.AlgebraicGeometry.Scheme,
  AlgebraicGeometry.Spec and AlgebraicGeometry.Spec.map; these are used by the
  domain and defining composite of fromSpecResidueField.
- def-weil-finite-type-morphism: Mathlib.AlgebraicGeometry.Morphisms.FiniteType,
  AlgebraicGeometry.LocallyOfFiniteType; and
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact, AlgebraicGeometry.QuasiCompact.

Proof dependencies are imported non-publicly, with their recorded declarations:

- lem-weil-pbc-affine-opens-basis: Mathlib.AlgebraicGeometry.AffineScheme,
  AlgebraicGeometry.Scheme.isBasis_affineOpens.
- lem-weil-pbc-affine-scheme-qcqs: the same AffineScheme module,
  AlgebraicGeometry.Scheme.compactSpace_of_isAffine; and
  Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated,
  AlgebraicGeometry.quasiSeparatedSpace_of_isAffine.
- lem-weil-pbc-scheme-sober: Mathlib.AlgebraicGeometry.Properties supplies its
  recorded scheme T0Space and QuasiSober instances (and imports the generic
  point uniqueness interface IsGenericPoint.eq).
- lem-sc-quasi-compact-kolmogorov-closed-point:
  Mathlib.Topology.Separation.Basic, IsClosed.exists_closed_singleton.
- def-weil-open-immersion: Mathlib.AlgebraicGeometry.OpenImmersion,
  AlgebraicGeometry.IsOpenImmersion.
- def-weil-pbc-module-stalk:
  WeilConjectures.Topology.PresheafModuleStalkFunctor,
  PresheafOfModules.moduleStalkFunctor.
- lem-trf-closed-point-residue-immersion:
  Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion,
  AlgebraicGeometry.isClosed_singleton_iff_isClosedImmersion.
- def-weil-closed-immersion: the same ClosedImmersion module,
  AlgebraicGeometry.IsClosedImmersion.
- lem-weil-pbc-immersion-base-change-lft:
  Mathlib.AlgebraicGeometry.Morphisms.Immersion,
  AlgebraicGeometry.IsImmersion.isStableUnderBaseChange,
  AlgebraicGeometry.IsImmersion.isImmersion_iff_exists and its instance
  IsImmersion f → LocallyOfFiniteType f.
- Repeated residue-field, affine-spectrum, and finite-type proof dependencies
  are already public imports because they occur in the statement.

Edge cases checked mathematically before writing:

- Empty V: no Z satisfies Z.Nonempty, and every subset O of the empty carrier
  equals Set.univ. No scheme nonemptiness hypothesis is imposed.
- Empty Z: excluded only by the precise Z.Nonempty antecedent.
- Z = V: gives a finite type point whenever V is nonempty.
- A non-Jacobson local scheme, such as the spectrum of a discrete valuation
  ring: the generic point is closed in its open singleton and is a finite type
  point, even though not closed in V. This rules out replacing the finite type
  predicate by IsClosed {v} or adding JacobsonSpace.
- Non-quasi-compact schemes and nonseparated schemes: the proof selects a
  single affine neighbourhood, and the statement makes no global restriction.
- O empty and V nonempty: it cannot contain all finite type points, by the
  first clause with Z = V. O = V is admitted without any extra condition.
- The two finite-type conjunctions are identical; there is no independent
  test-object universe or hidden restriction on residue-field size.

Searches made for an exact existing statement (2026-10-24):

- msearch.py leanfinder, query: “Every nonempty locally closed subset of any
  scheme contains a point whose canonical residue field spectrum morphism is
  of finite type”. Eight hits, including
  AlgebraicGeometry.isClosed_singleton_iff_locallyOfFiniteType (requires
  JacobsonSpace), Scheme.fromSpecResidueField-related instances, and
  LocallyOfFiniteType.jacobsonSpace. No arbitrary-scheme locally closed
  existence or detection theorem was returned.
- msearch.py loogle, query: `"LocallyOfFiniteType", "fromSpecResidueField"`.
  Successful response, zero hits.
- msearch.py grep, query:
  `finiteTypePoint|finite_type_point|fromSpecResidueField`, AlgebraicGeometry.
  Twenty-five reported hits, all canonical-map definitions or uses; no exact
  theorem. Direct source reads confirm the needed canonical map exists.
- rg over lean/WeilConjectures and lean/Sheaf, query:
  `finiteTypePoint|finite_type_point|finite_type_points|lem-sfb-finite-type-points-detect-open`.
  Only a proof-plan mention in ArtinRepresentableDiagonalCriterion.lean:385;
  no declaration states this item. The explicit grep -rn of the item id in
  lean/WeilConjectures also returned no matches.
- rg of Mathlib, WeilConjectures, Sheaf, and dag/lean_names_upstream.json for
  `finiteTypePoints_meet_locallyClosed_and_detect_open`: no name collision.
  DAG finite-type-point searches found this item and its consumers, not an
  additional definition needed here. The predicate is the conjunction already
  supplied by the finite-type morphism dependency; no new notion is necessary.

No STATEMENT-DISPUTED issue, node correction, dependency repair, or new node.
The suggested CompactObject example module is currently withdrawn and contains
no declarations; module layout follows the standing brief and current live
statement modules instead.

Validation: scompile.py Q33 lem-sfb-finite-type-points-detect-open compiled
both its sandbox check and its library module cleanly (6.0 s and 6.7 s), with
no errors or warnings reported. `set_option autoImplicit false` enforces the
explicit binders. The maximum Lean line length is 92 characters.

## Second reading by Q33

This is the worker's separate clause-by-clause rereading; the dispatcher brief
assigns the independent review to the maintainer and forbids starting agents.
I reopened the node and the module and compared the full statement again.
The two conjuncts account for both conclusions; Z has exactly the nonempty and
locally closed premises, O has exactly the open and finite-type containment
premises. In particular the quasi-compact part of finite type appears in both
places, and the canonical residue-field morphism is to V, not merely to an
unspecified affine neighbourhood. There are no extra global scheme hypotheses.
The universe and all quantified variables are explicit. No mismatch was found
and no mathematical statement was changed on this rereading.
