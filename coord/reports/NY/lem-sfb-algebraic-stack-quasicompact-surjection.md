## Worker report

Stage 2, NY, 2026-10-24. The module
`Sheaf.AlgebraicGeometry.AlgebraicStackQuasicompactSurjection` states
`CategoryTheory.algebraic_stack_quasicompact_surjection`, with one `sorry` and no
new definition or proved theorem. Its three conjuncts are the three equivalences
in the unchanged natural-language statement. Source read: the complete lemma and
proof of Stacks 04YC, `literature/stacks-project/stacks-properties.tex`,
`lemma-quasi-compact-stack`, and the statement and field-extension argument of
04XI, `lemma-characterize-surjective`. In particular the representability
hypothesis of 04XI is not imposed on the arbitrary map in condition (5).

Clause-by-clause rendering:

- The base scheme is `{S : Scheme.{u}}`. Every stack lies over `Over S`.
- The given algebraic stack is `F : BasedCategory.{v₁, w₁} (Over S)` with
  `hF : IsAlgebraicModuliStack F`. This uses the general smooth-atlas definition,
  rather than the Deligne--Mumford predicate.
- Quasi-compactness of the target is `IsQuasiCompactModuli F`, the recorded
  existential quasi-compact smooth-atlas predicate, in all three equivalences.
- The first equivalence quantifies `V` and `f : BasedFunctor V F`, and requires
  exactly `IsAlgebraicModuliStack V ∧ IsQuasiCompactModuli V ∧
  IsSurjectiveModuliMap f`.
- `IsSurjectiveModuliMap` is the existing predicate in
  `Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus`: for each field K,
  S-structure b and target object y it supplies L, a field homomorphism K → L,
  an object x on Spec L, and a `ModuliTwoIso` between `x.comp f` and the actual
  restriction of y along Spec(K → L). Its full definition and docstring were read.
  It does not require representability, smoothness, quasi-compactness or finite
  type of f. The already landed definition node `def-sfb-surjective-moduli-map`
  is added to `stmt_deps`, as authorized for landed dependencies; no node is
  created or rebound.
- The second equivalence quantifies `U : Over S` and the actual atlas functor
  `a : BasedFunctor (discreteModuli (yoneda.obj U)) F`, and requires
  `IsAffine U.left ∧ IsSmoothModuliAtlas F U a`.
- The third equivalence uses the same actual atlas and requires
  `CompactSpace U.left ∧ IsSmoothModuliAtlas F U a`. `CompactSpace` has no
  Hausdorff requirement. `IsSmoothModuliAtlas` includes representability and
  smoothness and surjectivity of the actual projection after every scheme
  base change; those conditions apply to a, not to f.
- The conjunction of the three iff statements expresses all the stated
  equivalences with no extra topological or representability assumption.
- Universes are explicitly `u v₁ w₁ v₂ w₂`, with `autoImplicit false`.
  The witness V has morphism universe `max u v₁ v₂` and object universe
  `max (u + 1) w₁ w₂`. These bounds include the base site, F and any chosen
  additional witness bounds, so no independent smaller universe makes existence
  vacuous. They impose no equality on the target's object/morphism universes.
  A universe lift of the identity witness realizes the forward implication at
  the indicated larger bounds. Test fields remain in the scheme universe u,
  exactly as in the landed surjectivity definition.
- There is no nonemptiness assumption. Empty stacks, empty atlases and the
  affine empty scheme Spec(0) are included.

Dependency interfaces read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `Scheme.Hom`; affine schemes use the Mathlib
  predicate `AlgebraicGeometry.IsAffine` in `Mathlib.AlgebraicGeometry.AffineScheme`.
- `def-weil-size-convention`: its record explicitly denotes a metatheoretic
  convention, with no declaration. The theorem binds all five universe levels.
- `def-sfb-algebraic-moduli-stack`:
  `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`,
  `CategoryTheory.IsAlgebraicModuliStack`, `IsSmoothModuliAtlas`,
  `SpaceMapIsSmooth`. Full signatures, bodies and docstrings read.
- `def-sfb-stack-qcqs-morphism`:
  `Sheaf.AlgebraicGeometry.StackQcqsMorphism`,
  `CategoryTheory.IsQuasiCompactModuli`. Full signature, body and docstring read;
  the node's primary quasi-separated-map declaration is not substituted for the
  needed quasi-compact-object declaration listed in `lean.declarations`.
- `def-weil-pbc-quasi-compact-scheme`:
  `Mathlib.Topology.Defs.Filter`, `CompactSpace`, including its no-separation
  convention and `isCompact_univ` field.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `Spec.map`; signatures and docstrings read. The
  theorem uses `IsAffine`, rather than choosing a ring presentation of the atlas.
- Added landed dependency `def-sfb-surjective-moduli-map`:
  `Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus`,
  `CategoryTheory.IsSurjectiveModuliMap` (existing declaration, not duplicated).

The module also imports every currently stated proof-dependency module, with
plain proof imports where it is not already a public statement import:
`StackPointTopology`, `StackPointTopologyFlatLfpOpen`, `EnlargedEtaleRingedSite`,
`StablePointedModuliGroupoids`, and the Mathlib modules `Cover.Open`, `Limits`,
`Morphisms.Etale`, `AffineScheme` and `Morphisms.QuasiSeparated`.
`StackChartwiseSmoothEtaleCalculus` is public because it also owns the reused
surjectivity predicate. `AlgebraicModuliStack` is publicly imported through
`StackQcqsMorphism`. The proof-only nodes
`lem-sfb-smooth-atlas-open-image`,
`lem-sfb-stack-diagonal-space-source-representability`, and
`lem-sfb-representable-stack-point-surjectivity` currently have no Lean record
or Mathlib match, so there is no module to import for them. They are not needed
for elaboration of this stage-2 statement. Their exact roles remain in the full
five-step proof docstring.

Edge cases checked before writing:

- Empty F: the lifting condition has no field objects to test; the empty scheme
  gives both atlas conditions. The empty finite affine family has product ring 0.
- Identity on a quasi-compact F: each field object lifts without extension;
  changing universe bounds uses the equivalent universe lift, not an additional
  hypothesis on F.
- Smooth positive-dimensional stabilizers, e.g. BG for a smooth group over a
  field: no DM or etale-atlas restriction appears.
- An infinite disjoint union of points: the node does not claim quasi-compactness
  without a quasi-compact surjective source. No finite type assumption has been
  accidentally substituted for quasi-compactness.
- Nonrepresentable f is permitted by its exact type and predicate; no chartwise
  representability test is attached to it.
- K → L is an arbitrary unital field homomorphism; the reused predicate neither
  requires a finite extension nor algebraic closure, and includes L = K.

Searches actually run with the authorized `msearch.py` wrapper:

- LeanFinder: `An algebraic stack is quasi compact if and only if it admits a
  surjection from a quasi compact algebraic stack and an affine smooth atlas`.
  Eight results, all scheme results; e.g. `compactSpace_iff_exists` and
  `quasiCompact_over_affine_iff`. No algebraic-stack statement.
- Loogle: `IsQuasiCompactModuli, IsSmoothModuliAtlas`.
  Zero hits, with diagnostic `unknown identifier 'IsQuasiCompactModuli'`.
  These project identifiers are not in the Mathlib search index; this is not
  evidence that the project lacks the predicates.
- Mathlib grep: `IsQuasiCompactModuli|IsSmoothModuliAtlas|IsAlgebraicModuliStack`.
  Zero hits.
- LeanSearch: `An algebraic stack is quasi compact if and only if it has an
  affine smooth surjective atlas`. Eight scheme results, including
  `quasiCompact_iff_forall_affine`; no algebraic-stack theorem.
- Source/project `rg`: searched `IsQuasiCompactModuli`, quasi-compact-surjection
  and atlas names and field-surjectivity names under `lean/WeilConjectures` and
  `lean/Sheaf`; searched the exact item id in `lean/WeilConjectures` with
  `grep -rn`. No existing theorem was found. This found the qcqs definitions,
  `FlatAffineActionStackPresentation` as a consumer, and led to the existing
  `IsSurjectiveModuliMap` in `StackChartwiseSmoothEtaleCalculus`.
- Searched `dag/nodes` for `IsSurjectiveModuliMap`, finding its already landed
  owner `def-sfb-surjective-moduli-map`; opened the complete record and the
  recorded source declaration. No new definition node is needed.
- Searched `dag/lean_names_upstream.json` for quasi-compact declaration names and
  Mathlib/project source for the proposed theorem name; no duplicate.

No statement correction or STATEMENT-DISPUTED flag is needed. The natural-language
statement and proof are unchanged. The only node changes are `lean` and the added
landed definition dependency. Compilation with `scompile.py` on 2026-10-24 passed
both sandbox and library module compilation, with no errors or non-sorry warnings.

## Second reading by NY

The dispatched worker reread the completed module against the node and the actual
definitions; no additional agent was started, as the dispatcher expressly forbids
that. This is a second pass by the author, not a claimed independent review. The
maintainer's independent review remains the delivery review.

The given S and algebraic F are present. The first iff has an algebraic,
quasi-compact V and an unrestricted field-extension-locally surjective f. The
second iff has an affine smooth surjective scheme atlas, and the third has a
quasi-compact smooth surjective scheme atlas. `IsAffine` is the Mathlib scheme
notion, `CompactSpace` is the recorded quasi-compactness notion, and every atlas
is over S. Inspecting the predicate bodies confirms there is no missing actual
projection, no arbitrary replacement map, no DM assumption and no exclusion of
the empty source. The upper universe bounds were checked to contain both F and
the base site, without equating their levels. No mathematical mismatch was found.
The five-step proof docstring follows the node including the finite affine
coproduct and descent steps, and no missing proof-only node was invented or
postponed as a new theorem.
