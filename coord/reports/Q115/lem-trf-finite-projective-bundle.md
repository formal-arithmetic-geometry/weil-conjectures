## Worker report

The module `Sheaf.AlgebraicGeometry.Morphisms.FiniteProjectiveBundle` states
`AlgebraicGeometry.isProjectiveBundle_of_isFinite`, with its proof postponed by `sorry`.
It introduces no definition, helper theorem, extra hypothesis, or statement correction.
The theorem docstring contains all six steps of the node's proof and names their DAG inputs.

Hypothesis and conclusion correspondence:

- The schemes T and S are `{T S : Scheme.{u}}`, with the universe explicitly declared.
- The morphism h:T → S is `(h : T ⟶ S)`.
- Finiteness, the sole hypothesis, is `[IsFinite h]`. The recorded Mathlib class extends
  `IsAffineHom h` and requires a finite ring map on every affine open of S.
- Projectivity in the specified convention is the conclusion `IsProjectiveBundle h`.
  Reading its definition, this is exactly the existence of `E : S.Modules`, a proof
  `hE : E.IsQuasicoherent`, and `E.IsFiniteType`, together with a morphism
  `i : T ⟶ (@SymmetricAlgebraSheaf.gradedAlgebraData S E hE).relProj` satisfying
  `IsClosedImmersion i` and
  `i ≫ (@SymmetricAlgebraSheaf.gradedAlgebraData S E hE).relProjHom = h`.
  This is a closed subscheme of the canonical projective bundle P_S(E), over S.
  An isomorphism to a closed subscheme is equivalently a closed immersion from T.
  The definition neither asks that E be locally free nor chooses an independent grading.

Statement dependency declarations used:

- `Mathlib.AlgebraicGeometry.Morphisms.Finite`, `AlgebraicGeometry.IsFinite`.
  Its complete class signature and docstring were read in the pinned Mathlib source.
  `IsIntegralHom` was also inspected; it is not a hypothesis of this node.
- `Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism`,
  `AlgebraicGeometry.IsProjectiveBundle`. Its complete definition and docstring were read
  both in the shared source and through `scompile.py --source`; they agree.

The source `literature/stacks-project/morphisms.tex` was read at
`definition-projective` and `lemma-finite-projective` (Tags 01W8 and 0B3I).
Definition 01W8(1) uses a quasi-coherent finite-type module; 0B3I applies to every finite
morphism with no extra hypotheses on either scheme. It supplies E = h_*O_T.
The node's explicit graded-quotient proof uses the same module and conclusion.
All recorded proof-dependency modules are imported, with ordinary imports when they are
only used by the planned proof. The shared library already supplies the canonical symmetric
algebra, its grading, and relative Proj; this delivery makes no duplicate construction.

Edge cases checked before writing:

- Empty T, empty S, and the empty-to-empty morphism are included: there are no nonemptiness
  assumptions. In the affine zero-algebra case both the relevant Proj chart and Spec A
  are empty, exactly as explained in proof Steps 4–5.
- A finite algebra need not be reduced, flat, or locally free. The homogeneous-prime and
  localization calculations use none of these properties, and no such assumption occurs.
- The base may be non-Noetherian, non-quasi-compact, or disconnected. The theorem has no
  corresponding restriction; finite-type E is a sheaf condition, not a global free basis.
- Identities and zero-dimensional examples require no separate case or positive rank.
- `universe u` is explicit. Both schemes use the common universe used by the recorded
  predicates, and the statement contains no auto-bound variables or test-object universe.

Searches for an existing declaration:

- `msearch.py leanfinder`, query “Every finite morphism of schemes is projective in the
  projective bundle sense”: eight hits, including `IsProper.instOfIsFinite`,
  `instIsProperOfIsFinite`, `IsFinite.toIsAffineHom`, and properness results for Proj.
  None states the projective-bundle conclusion.
- `msearch.py leansearch`, query “Finite morphisms of schemes admit a closed immersion into
  a projective bundle”: eight hits concerning `IsFinite`, closed immersions, and the
  finite-monomorphism characterization. No matching theorem.
- `msearch.py loogle`, query `AlgebraicGeometry.IsFinite, AlgebraicGeometry.IsProjectiveBundle`:
  no hits, with the project predicate unknown to the Mathlib search service.
- `msearch.py grep`, query `IsProjectiveBundle|IsFinite.*IsProjective|finite.*projective`,
  subdirectory `AlgebraicGeometry`: no Mathlib hits.
- `rg` in upstream `WeilConjectures`, project `lean/Sheaf`, and Mathlib algebraic geometry
  for `IsProjectiveBundle`, `isProjectiveBundle_of_isFinite`, and finite/projective phrases:
  the project predicate occurs only in its defining module. Other finite-projective hits
  concern modules or different projectivity results, not this theorem.
- `rg` in `dag/lean_names_upstream.json` for the same predicate and proposed theorem name:
  no recorded upstream declaration. Searching upstream `WeilConjectures` for the exact item
  id likewise found none.

No node fault or disputed statement was found. Only the item's `lean` field changes.

Validation: `scompile.py Q115 lem-trf-finite-projective-bundle
lean/Sheaf/AlgebraicGeometry/Morphisms/FiniteProjectiveBundle.lean` completed successfully.
The wrapper compiled the dependency overlay, sandbox file, and library-position file
separately within their limits, with no compiler errors or warnings.

## Second reading by Q115

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
