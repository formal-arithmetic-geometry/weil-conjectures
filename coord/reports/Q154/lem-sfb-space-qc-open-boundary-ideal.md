## Worker report

The delivery states `AlgebraicGeometry.AlgebraicSpace.exists_finiteType_ideal_boundary`
in `Sheaf.AlgebraicGeometry.AlgebraicSpaceQcOpenBoundaryIdeal`. Its only postponed proof
is the assigned theorem, with the six DAG proof steps included in its docstring.
It introduces no definitions and no new nodes. The inherited BLOCKED message concerned
stage-1 `deliver.py`, whereas the current assignment is stage 2 and the live node has no
Lean record. There is no repair note for this item. The stage-2 handoff paragraph of
`coord/brief-stage2.md` explicitly authorizes proceeding in this situation.

The source was read at `literature/stacks-project/spaces-limits.tex`,
`lemma-quasi-coherent-finite-type-ideals` (Tag 0855), lines 3166–3213: the implication
(2) to (3) and its proof provide both the vanishing set and the unit restriction.
The latest blueprint is the `latest` link recorded by COMMITS.txt, not an older snapshot.
The assigned node is a supporting input, not the statement of its blueprint unit.

Hypotheses and clauses, in order:

- `S : Scheme.{u}` is the arbitrary scheme base. The explicit `universe u` follows
  the recorded size convention and the existing algebraic-space framework. No base
  quasi-separatedness, Noetherianity, nonemptiness, reducedness or characteristic
  restriction is imposed.
- `T U : AlgebraicSpace S` uses precisely the recorded category of fppf sheaves with
  representable diagonal and representable surjective etale scheme atlas.
- `j : U ⟶ T` is the open-subspace inclusion. Its hypothesis `hj` is
  `IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) j.hom.hom`, exactly the
  node's scheme-base-change definition of open immersion. No arbitrary map replaces it.
- `hTqc` asserts the existence of `W : Over S` and `a : yoneda.obj W ⟶ T.obj.obj`
  with `CompactSpace W.left ∧ IsEtale a ∧ IsSurjective a`. This is exactly the
  node's quasi-compact-scheme-atlas definition of quasi-compactness of T.
- `hTqs : IsAbsolutelyQuasiSeparated T` is the landed affine-test definition of
  absolute quasi-separatedness, equivalent to a quasi-compact absolute diagonal
  by its recorded Tag 0AHR. The existing node `def-sfb-space-absolute-quasi-separated`
  is added to stmt_deps to cite this interface explicitly. A relative diagonal
  over the arbitrary S would not be the stated hypothesis.
- `hUqc` is the same compact-scheme-atlas existential for U. In particular it is
  quasi-compactness of the open space itself, without a substituted relative condition.
- `K : QuasiCoherentIdeal T` is the existing subtype of O_T-module subobjects of
  `SheafOfModules.unit T.structureSheaf` with the recorded Mathlib quasi-coherence
  predicate. The embedding into O_T and quasi-coherence are therefore part of its type.
- `SheafOfModules.IsFiniteType (K.val : T.Modules)` asserts finite local generation,
  using Mathlib's existing module-sheaf finite-type predicate.
- `Z : ClosedSubspace T` is the existing subtype of subobjects with representable
  closed-immersion scheme base changes. The equality
  `K.val = kernelSubobject (moduleStructureMap Z.val.arrow)` identifies Z as V(K)
  by the recorded ideal/closed-subspace correspondence, rather than as an arbitrary
  closed subspace with the same point set. Existence of this Z adds no mathematical
  restriction to K: every quasi-coherent ideal corresponds to such a closed subspace.
- `pointImage Z.val.arrow.hom.hom = (pointImage j.hom.hom)ᶜ` is precisely
  `|V(K)| = |T| \ |U|`, inside the existing field-valued point classes of T.
  Their topology is the recorded atlas topology; no new point model is introduced.
- `IsIso (idealTensorMap j K)` asserts that the canonical map `j^*K → O_U` is an
  isomorphism. Because j is an open immersion, this is restriction to U; requiring
  the canonical inclusion to be an isomorphism means the restricted embedded ideal
  equals the unit ideal, not merely that its underlying module is abstractly isomorphic.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentableWith`, `IsEtale`, `IsSurjective`, `EtaleSite`, `structureSheaf`,
  `Modules`, `pullback` and their scheme-chart construction.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, as used by ClosedSubspace.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally` and
  its morphism-property definitions, imported as required by the statement DAG.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh`, with
  `SheafOfModules.IsQuasicoherent` from Mathlib's module-sheaf Quasicoherent module.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceIdealClosedSubspaceCorrespondence`:
  `ideal_closedSubspace_correspondence`, whose kernel clause identifies V(K).
  Its public dependency modules supply `QuasiCoherentIdeal`, `ClosedSubspace`,
  `idealTensorMap` and `moduleStructureMap`; these declarations and docstrings
  were read in their defining modules.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointImage` and
  `pointTopologicalSpace`, using the existing `Point` classes.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `IsAbsolutelyQuasiSeparated`, the one added landed statement dependency.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`: `SheafOfModules.IsFiniteType`.

Already stated proof dependencies are imported without `public`: the finite-presentation
approximation theorem, scheme etale composition/cancellation, and the concrete filtered
module-colimit interfaces. The other proof dependencies (reduced closed support, point
open calculus, affine atlas, affine-chart calculus) have no recorded Lean declarations;
their IDs remain in the proof docstring and DAG, without speculative module imports.
None is needed to type this statement. The ideal correspondence is a statement dependency
and is therefore imported publicly. No import cycle is introduced.

Edge cases checked before writing:

- U empty: K may be the zero ideal and Z all of T; on the empty space its zero and
  unit module sheaves coincide. An empty compact scheme atlas is allowed.
- U = T: K is the unit ideal and Z empty; its tensor ideal map is the identity
  under the canonical unit identification.
- T empty: the hypotheses allow empty atlases; both point sets and their complement
  are empty, and all ideal restrictions are the unique module sheaf.
- Nonreduced affine tests, such as dual numbers, and non-Noetherian polynomial rings
  in infinitely many variables are included. The ideal is finite type without any
  radicalness requirement. A reduced closed support is used only for J in the proof.
- S need not be quasi-separated: hTqs uses the absolute definition, not the diagonal
  over S. No independent test universe can make its quantifiers vacuous.

Searches actually run with msearch.py for Q154 and this item:

- leanfinder: "A quasi compact open subspace of a quasi compact quasi separated
  algebraic space is the complement of a finite type quasi coherent ideal" — 8 hits,
  including scheme quasi-separated section lemmas and the scheme subscheme-inclusion
  quasi-compactness instance; no algebraic-space boundary-ideal theorem.
- loogle: `AlgebraicGeometry.Scheme.IdealSheafData, "support"` — 12 hits on scheme
  ideal support, radicals, powers and the support/vanishing-ideal correspondence.
  These neither quantify over arbitrary algebraic spaces nor give the required ideal.
- grep in Mathlib/AlgebraicGeometry:
  `finiteType.*[Ii]deal|[Ii]deal.*[Cc]omplement|[Ii]dealSheafData` — 25 hits on
  scheme ideals and their subschemes, without the algebraic-space result.
- leansearch: "Finite type quasi coherent ideal defining complement of a quasi
  compact open algebraic space" — 8 hits, notably
  `PrimeSpectrum.isCompact_isOpen_iff_ideal` (the affine case only) and scheme
  compact-open criteria, without the assigned statement.
- rg in both `lean/WeilConjectures` and `lean/Sheaf` for boundary ideals, algebraic-space
  ideals, the proposed name and this node ID: no existing algebraic-space theorem.
  Read `Scheme.exists_finiteType_ideal_coe_support_eq_compl` in
  `WeilConjectures/Blowup/AdmissibleBlowup.lean`: it takes a scheme and a scheme open,
  so is a special case and cannot serve as an existing declaration for this node.
  The existing algebraic-space ideal and closed-subspace notions are reused unchanged.

No statement dispute or source correction was needed. The node changes only in lean
and by adding the already landed absolute-quasi-separatedness definition to stmt_deps.
The UTC date for the record is 2026-10-23, as returned by `date -u +%F` on this machine.

Validation: scompile.py compiled both its sandbox module and final library module cleanly
(3.4 s and 2.4 s respectively), with no errors or unexpected warnings.

## Second reading by Q154

This section records a second pass by the same worker, not an independent agent review;
the dispatch brief assigns the independent review to the maintainer and forbids spawning
agents. I reread the source node and final signature together. Both compactness binders
use compact scheme atlases, the absolute-quasi-separatedness binder uses the landed
definition, and the open immersion uses scheme base changes. The four conclusion clauses
respectively give finite type, identify the closed subspace by its exact kernel ideal,
give the complementary point image, and make the canonical restricted ideal map invertible.
The ideal type already supplies quasi-coherence and its actual inclusion. No clauses or
edge cases were removed, and no arbitrary map or extra finiteness condition was inserted.
This pass found no mismatch requiring a change. Independent maintainer review remains
part of normal delivery review.
