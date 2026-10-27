## Worker report

The delivery states `CategoryTheory.adequate_geometricFibres_submersion` in
`Sheaf.AlgebraicGeometry.AdequateGeometricFibresSubmersion`, with its whole proof `sorry`.
The only other declaration is `CategoryTheory.moduliScalarPoint`, a concrete canonical
map from an object over Spec Ω to the underlying point of the actual scalar extension.
Its data is an explicit iso-comma triple and its field-object quotient class; it uses
no choice or postponed existence theorem. No new independent notion is introduced.

Source read: Alper, *Adequate moduli spaces and geometrically reductive group schemes*,
[arXiv:1005.2398v3](https://arxiv.org/pdf/1005.2398v3), Section 2, printed p.7, and
Theorem 5.3.1(1)--(5), printed pp.29--30. Section 2 supplies the diagonal conventions.
Parts (3) and (5) supply the two assertions of this node. The informal node, its proof,
and its proof dependencies are unchanged. Its statement dependencies gain existing
landed definition nodes owning the canonical constructions used in the signature.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The field k is `(k : Type u) [Field k]`, reusing Mathlib's `Field`.
- The algebraic stack over k is `F : BasedCategory.{v,w} (Over (Spec (.of k)))`,
  with `hF : IsAlgebraicModuliStack F`. The stack and the base site retain their
  independent object and morphism universes.
- The algebraic space over k is `Y : AlgebraicSpace (Spec (.of k))`.
- The given morphism is `φ : BasedFunctor F (discreteModuli Y.obj.obj)`.
- Adequacy is exactly `hφ : IsAdequateModuliSpace F hF Y φ`, including the recorded
  qcqs, canonical structure-sheaf map and power-lifting conditions. No extra exactness
  or descent hypothesis is introduced.
- `hFdiag` and `hYdiag` test the absolute diagonals over k: `moduliBaseStructure`
  is the actual projection to the base scheme, represented by the identity category
  over Sch/k, and `moduliRelativeDiagonal` is its canonical relative diagonal.
  Every scheme test `T,t` has an algebraic-space presentation `Z,p` through
  `HasSpaceBaseChange`. This condition pins the projection p to the diagonal base
  change by a specified 2-isomorphism; it is not an arbitrary equivalent space.
  `MapIsQuasiCompact p` is quasi-compactness of this projection.
  `MapToSchemeIsSeparated Z T p` means representability of its relative diagonal
  by closed immersions. These are precisely the two requested properties for
  each of the diagonals of F and Y, with no properness or finite-type condition.
- For every algebraic space `Y'` and `g : Y' ⟶ Y`, the actual 2-fibre product is
  `moduliTwoFiberProduct φ (discreteModuliMap g.hom.hom)`. Its projection is
  `moduliTwoFiberSnd φ (discreteModuliMap g.hom.hom)`, and its point map is
  `moduliPointMap` of this projection. `Function.Surjective` is the first clause;
  `∀ V, IsOpen V ↔ IsOpen (pointMap ⁻¹' V)` is exactly the quotient-topology clause.
  The Y' binder has no diagonal restriction. The established smooth-atlas topology
  on discrete algebraic spaces agrees with their usual étale-atlas topology.
- The field extension is `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
  (g : Spec (.of Ω) ⟶ Spec (.of k))`. A scheme map between field spectra is exactly
  a field embedding in the opposite direction, so this ranges over all the stated
  extensions in the big-site universe, without choosing an algebraic closure or
  restricting to algebraic extensions.
- `moduliFiberMap φ (Over.mk g)` is the actual induced functor on Ω-objects.
  `Function.Surjective (...mapSkeleton.obj)` is surjectivity on their isomorphism
  classes. Since the target is the discrete groupoid of Y, its fibre isomorphism
  classes are precisely Y(Ω), by Yoneda. No further field extension is used here.
- For `x₁ x₂ : Functor.Fiber F.p (Over.mk g)`, the displayed `Nonempty` is an
  isomorphism between their image objects in that same discrete fibre. This means
  equality in Y(Ω), rather than equality only after quotienting field extensions.
- `moduliScalarPoint F Ω g xᵢ` is a point of `moduliSchemeBaseChange F g`, whose
  base is Spec Ω. The helper's triple is `(xᵢ, Spec Ω over itself, canonical base
  identity comparison)`. Thus `closure {point₁} ∩ closure {point₂}` is computed
  in |F_Ω|, not in |F|. `.Nonempty` is intersection of these closures, and `↔`
  preserves both directions of the required classification.
- There is no finite-type, reducedness, characteristic, Noetherian or finite-inertia
  hypothesis anywhere in the signature.

Dependency declarations used, with source modules opened and signatures read:

- `Mathlib.Algebra.Field.Defs`: `Field` (def-weil-field, Mathlib match).
- `Sheaf.AlgebraicGeometry.AdequateModuliSpace`: `IsAdequateModuliSpace`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith` (through separatedness).
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `IsAlgebraicModuliStack`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`: `discreteModuli`,
  `discreteModuliMap`, `moduliTwoFiberProduct`, `moduliFiberMap`, `HasSpaceBaseChange`.
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`: `ModuliPoints`,
  `ModuliFieldRelation`, `moduliPointMap`, `moduliRelativeDiagonal`.
  These point and diagonal constructions themselves apply to general based categories;
  their use here does not assume a Deligne--Mumford stack or use the étale-only
  `ModuliPointIsClosed` predicate.
- `Sheaf.AlgebraicGeometry.RelativeModuliInertia`: `moduliBaseStructure`.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `AlgebraicSpace.MapIsQuasiCompact`,
  `AlgebraicSpace.MapToSchemeIsSeparated`.
- `Sheaf.AlgebraicGeometry.ModuliSchemeBaseChange`: `moduliSchemeBaseChange`.
- `Sheaf.AlgebraicGeometry.OpenModuliSubstack`: `moduliTwoFiberSnd`.
- `Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen`:
  `moduliPointTopologicalSpace` and its canonical smooth-atlas topology. This is the
  recorded declaration of def-sfb-stack-point-topological-space; it is reused.

Statement modules re-export the definitions they use, so some owning modules above
are available through the direct public import of AdequateModuliSpace. The explicit
public imports also expose RelativeModuliInertia, ModuliSchemeBaseChange,
OpenModuliSubstack and StackPointTopologyFlatLfpOpen to downstream consumers.

Proof dependencies already stated are imported privately:
`Sheaf.AlgebraicGeometry.SmoothPresentationClosedSubsets` (the recorded theorem
`smooth_presentation_closed_subsets`);
`Mathlib.RingTheory.Flat.Basic` (`Module.Flat.of_free`, `lTensor_exact`, `rTensor_exact`);
and `Mathlib.LinearAlgebra.Basis.VectorSpace` (`Module.Free.of_divisionRing`).
The other proof nodes have no Lean record or Mathlib match on the read base:
lem-sfb-adequate-moduli-universally-submersive,
lem-sfb-adequate-moduli-topological-images, lem-sfb-adequate-flat-base-change,
lem-sfb-universally-closed-stack-rational-point and
lem-sfb-qs-space-rational-point-topology. They are not needed to type this stage-2
statement, and no speculative imports of absent modules are added.
`def-sfb-stack-qcqs-morphism` is public through the adequacy module.
The docstring carries the node's four proof steps and their named dependencies.

Edge cases checked before writing and again against the signature: empty source and
empty target (the adequate empty map has empty base changes and vacuous field fibres);
empty Y' over nonempty Y; empty and full V in the quotient criterion; identity base
change; the identity adequate space; identical x₁ and x₂ (their common point belongs
to both closures); distinct geometric points with intersecting orbit closures;
nontrivial stabilizers (the source fibre is not replaced by a discrete category);
nonreduced stacks and spaces; positive and zero characteristic; transcendental Ω/k;
and bases Y' without quasi-compact diagonals. Both diagonal conditions concern F and
Y only. No arbitrary atlas or quotient topology is assumed as extra data.

Searches actually run:

- `msearch.py ... leanfinder "Adequate moduli spaces universally submersive geometric
  points equivalent intersecting closures"`: eight hits, including valuative criteria,
  universally closed schemes and closed-singleton criteria; none state this stack lemma.
- `msearch.py ... leansearch "Adequate moduli space surjective quotient topology and
  closure equivalence of geometric points"`: eight hits, including quotient maps of
  modules, flat scheme maps and generic quotient-map definitions; no exact statement.
- `msearch.py ... loogle '"adequate"'`: zero hits.
- `msearch.py ... grep 'adequateModuli|adequate_moduli|closureEquivalent|closure_equivalent'`:
  zero Mathlib hits.
- `rg` on `lean/WeilConjectures`, `lean/Sheaf` and Mathlib for adequate-moduli names,
  the proposed theorem name and `moduliScalarPoint`: the existing project adequacy
  definition was found and reused; no existing theorem or scalar-point helper matched.
- `grep -rn 'lem-sfb-adequate-geometric-fibres-submersion' lean/WeilConjectures`:
  no existing blueprint-tagged declaration.
- `rg` of `dag/lean_names_upstream.json` for the proposed two declaration names:
  no clash. DAG and project searches located and reused the already recorded
  scalar-base-change, point-topology, second-projection and base-structure definitions.

No statement correction, new definition node, dependency repair or
STATEMENT-DISPUTED finding is needed.

## Second reading by Q55

This is the author's second pass, not a claim of an independent agent review.
The dispatcher expressly required a single worker without subagents; independent
review is the maintainer's delivery review.

Reopened the node and module and compared all hypotheses and conclusions. Checked
that hFdiag/hYdiag concern absolute diagonals over k, that their projection comparisons
are retained, and that separatedness is a closed-immersion relative diagonal rather
than properness. Rechecked that Y' has no added diagonal hypothesis. Rechecked the
same-field skeleton surjectivity against the strict Ω-fibre, and image equality against
isomorphism in that discrete fibre. The closure sets are in moduliSchemeBaseChange F g,
not F. The explicit helper contains only the given object and canonical identity data.
No mismatch requiring an informal-node change was found.

The first compiler pass found that the second projection was only privately imported;
added its owning module as a public import, and its existing node to stmt_deps. It also
found no object-extensionality theorem for Over in the helper; replaced that attempt by
unfolding the two Over.mk objects and rewriting identity composition. These were
visibility/elaboration repairs and changed no mathematical clause.
