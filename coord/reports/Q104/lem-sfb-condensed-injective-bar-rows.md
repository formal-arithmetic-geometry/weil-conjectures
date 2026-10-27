## Worker report

The module `Sheaf.CategoryTheory.CondensedInjectiveBarRows` states
`CategoryTheory.CondensedBar.nonempty_injectiveRows`, with its sole proof `sorry`.
`InjectiveRows` packages the complete assertion about the existing bar diagrams;
`parameterGenerator` and `parameterPullback` are real constructions from the recorded
free adjunction and tensor isomorphisms, not choices from an existence theorem.
No statement correction, dependency repair, new independent notion, or disputed
statement is needed. The original JSON changes only in `lean`.

Source read: main-20261015 blueprint, six-functors basics, unit
sk-thm-sf-ctf-stability, direct-images.proof.md, paragraph (3). The source gives the
open-direct-image application; the node explicitly labels this internal-bar lemma
and its eight-step proof as an agent expansion, with an external reference wanted.
The complete eight-step proof is transcribed into the theorem docstring.

Hypotheses and clauses, checked against the node:

- Arbitrary commutative condensed ring: `{A : CondensedBar.Ring.{u}}` is the bundled
  commutative monoid in abelian sheaves on `coherentTopology Profinite.{u}`. Its
  `A.toMon` is the dependency's `Profinite.CondensedRing`, with `ringComm A` supplying
  precisely commutativity. No topological presentation or flatness is imposed.
- Profinite group: `{G : Type u}` with `Group`, `TopologicalSpace`,
  `IsTopologicalGroup`, `CompactSpace`, `T2Space`, `TotallyDisconnectedSpace`.
  This is the standard compact Hausdorff totally disconnected realization of a
  profinite group, with every continuous generalized element retained.
- Internal modules, action modules and equivariant maps are the dependency aliases
  `Modules A`, `Equivariant A G`, and the existing category on `ActionModule`.
  Forgetting the action is the recorded `forgetAction`.
- Invariants fixed after all base changes: `(V : Invariants A G)` is the existing
  normalized invariants datum; its `image` is exactly `FixedAll`, not pointwise
  invariants on just the terminal profinite set. `(a : Augmentation V B)` is the
  normalized constant-function inclusion of this same datum.
- The free representable modules and internal Hom are the dependency's
  `freeParameter A S`, `InternalFunctions A`, and `F.internalHom`. No copied free
  module or internal Hom is introduced. `parameterGenerator` uses the unit of
  `InternalBar.freeAdjunction` directly.
- The normalized homogeneous resolution is `(E : Resolution A.toMon G)`.
  Its `objects`, `freeIso`, `diagonal`, `boundary_generator`, and
  `augmentation_generator` specify precisely P_p, diagonal action, alternating
  deletion, and generator-sum augmentation. All normalized models are covered;
  no arbitrary model is chosen from `exists_resolution`.
- Injectivity is `[Injective I]`, for each `I : Equivariant A G`, with no assumption
  about underlying injectivity, abelian structures, projectivity of A[S], or its
  flatness. The theorem covers every compatible F, B, V, a, E.
- Parametrized homogeneous Hom and its sheaf property: `homEquiv I n S` identifies
  the section group of the existing inhomogeneous cochain sheaf with
  `E.tensorObjects (freeParameter A S) n ⟶ I`. These are P_n tensor A[S]; the
  node's A[S] tensor P_n is canonically the same by relative tensor symmetry,
  with trivial action on A[S] specified by `E.tensor_action`. Using this order
  follows the recorded resolution API, rather than adding a different tensor.
  `homEquiv` is additive; `restriction` identifies the presheaf restrictions with
  `parameterPullback`, so this is a representation of the specified Hom presheaf
  by an actual internal module sheaf. Its R(S)-linearity follows from the displayed
  generator formula, F.smul and linearity of the action and the free/tensor maps.
- Homogeneous-to-inhomogeneous identification: `coordinates` states exactly
  f(s;g_0,...,g_n) = g_0*c(s;g_0^(-1)g_1,...,g_(n-1)^(-1)g_n), using
  `basis`, `pureTensor`, `parameterGenerator`, `F.evaluate`, and `tupleMap`.
  All S, T and s:T→S are quantified; these are parametrized generators.
- All three coface formulas and insertion-of-1 codegeneracies are exactly the
  existing fields `B.face` (first, interior via `mergeTuple`, last) and
  `B.degeneracy`. They are retained by requiring this same `B : BarDiagram F`.
  `cochains B` is the existing `alternatingCofaceMapComplex`, whose differential
  is the sum of (-1)^i times these faces. `differential` asserts its compatibility
  with precomposition by E's alternating homogeneous boundary.
- The zero-degree formula is explicitly `degreeZero`, evaluated on every s:T→S
  and g:T→G: action on the degree-zero value minus that value. `@id` makes the
  section encoding explicit in this subtraction; it adds no mathematical datum.
- The invariant augmentation is `augmentation`, constant on homogeneous
  generators with value the pullback of `V.inclusion`. This also fixes its
  compatibility with the generator-sum augmentation. Its internal and sectionwise
  injectivity are `mono` and `mono_sections`.
- Exactness at degree zero is `exact_zero` internally and
  `exact_sections_zero` on each S; at all positive degrees it is `exact_succ`
  and `exact_sections_succ`. This includes the kernel assertion for gm-m.
- Profinite-base-change compatibility is `restriction`; compatibility with every
  equivariant map between injectives is `naturality`. The existing functors B and
  a already retain naturality of the differential, faces and augmentation.

Dependency declarations read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `ModObj`, `Mod.Hom`.
- `Sheaf.CategoryTheory.CondensedActionModule`: `Modules`, `sectionModule`,
  `ActionModule`, `Equivariant`, `forgetAction`, `trivial`, `FixedAll`, `Invariants`
  in `Profinite.CondensedAction`.
- `Sheaf.CategoryTheory.CondensedEquivariantBarData`: `Ring`, `Modules`, `sections`,
  `InternalFunctions`, `power`, `tupleMap`, `mergeTuple`, `BarDiagram`, `cochains`,
  `Augmentation`, `freeParameter`, `Equivariant`, `Invariants` in CondensedBar.
- `Sheaf.CategoryTheory.CondensedInternalBarResolution`: `free`, `freeAdjunction`,
  `basis`, `onSections`, `pureTensor`, `Resolution`, `exists_resolution` in
  Profinite.CondensedAction.InternalBar. The free-module-adjunction node records
  exactly this existing `freeAdjunction`.
- `WeilConjectures.CategoryTheory.ModuleObjects.Monoidal`: `Mod.monoidalCategory`,
  `Mod.tensorObjπ`, `Mod.tensorObj_X`, `Mod.isColimitTensorπ` (via public imports).
- `Sheaf.CategoryTheory.Monoidal.ModuleEqualizerInternalHom`:
  `Mod.nonempty_equalizerInternalHomAdjunction` and the reexported internal Hom API.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`: `CategoryTheory.Injective`;
  resolution signatures read in Preadditive.Injective.Resolution. The size node
  is metatheoretic; explicit universe u implements its convention.

The proof-only nodes `lem-sfb-condensed-group-algebra-exact-forgetful` and
`lem-sfb-condensed-free-linearization-tensor` have no recorded Lean declaration
in this checkout, so no imaginary import is added. They are named in the proof
plan and are not additional assumptions in the statement.

Edge cases checked: n=0 uses the singleton homogeneous tuple and terminal
inhomogeneous power, with two faces gm and m; n=1 preserves the noncommutative
order of adjacent ratios and products. G=1 gives identity action and the usual
alternating trivial-group bar. S and T may be empty profinite sets: all arrows,
generators and natural-family evaluations still make sense; no Nonempty is
required. The zero coefficient ring and zero injective module are allowed.
Sectionwise exactness is proved using injectivity against image inclusions in the
equivariant category, not by assuming section evaluation is exact.

Searches actually run with msearch.py for Q104 and this item:

- leanfinder: “For an injective internal condensed equivariant module the augmented
  homogeneous bar Hom sheaves are exact and identify naturally with inhomogeneous
  cochains”. Eight hits, including Rep.barResolution.extIso,
  groupCohomology.inhomogeneousCochainsIso, groupCohomology.shortComplexH0_exact,
  and CochainComplex.isKInjective_of_injective_aux. They concern ordinary
  representations or general homological algebra and do not state this result.
- loogle: `"Condensed", "bar"`: zero hits.
- grep: `(bar|inhomogeneous).*(injective|Condensed)|(injective|Condensed).*(bar|inhomogeneous)`:
  zero hits in Mathlib.
- rg of lean/WeilConjectures and lean/Sheaf for the node id and
  `bar.*[Ii]njective|[Ii]njective.*[Bb]ar`: no exact declaration. Existing product
  bar comparison uses related rows as an ingredient; it does not give this
  homogeneous Hom representation and exactness assertion.
- rg for the new declaration names: no conflicting fully qualified declaration.

Validation: every compile uses scompile.py, with no local Lake or global build.
The prescribed deliver2.py dry run and delivery are run after the clean compile.

## Second reading by Q104

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
