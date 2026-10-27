## Worker report

The new module `Sheaf.AlgebraicGeometry.StackQcqsAtlasAffineDiagonal` states
`CategoryTheory.stack_qcqs_of_atlas_comp_quasiCompact_of_affine_diagonal`.
Its sole proof is `by sorry`. No definition, helper theorem, dependency repair,
new node, or statement correction is needed. Only the item's `lean` record changes.

The source was read in `literature/stacks-project/stacks-morphisms.tex`,
`lemma-surjection-from-quasi-compact` (Tag 050X), and `definition-separated`,
clause (4) (Tag 04YW). The former descends quasi-compactness along a surjection;
the latter requires the relative diagonal to be both quasi-compact and
quasi-separated. The theorem docstring gives all four steps of the accepted
node proof, including arbitrary quasi-compact algebraic-space tests in step 4.

Clause-by-clause translation:

| Node clause | Lean rendering |
| --- | --- |
| S is an arbitrary scheme | `{S : Scheme.{u}}` |
| Z is an algebraic stack over S | `Z : BasedCategory.{v, w} (Over S)` and `hZ : IsAlgebraicModuliStack Z` |
| Y and U are S-schemes | `Y U : Over S` |
| f is a morphism Z → Y | `f : BasedFunctor Z (discreteModuli (yoneda.obj Y))` |
| p is a scheme atlas U → Z | `p : BasedFunctor (discreteModuli (yoneda.obj U)) Z` |
| p is representable, smooth and surjective | `hp : IsSmoothModuliAtlas Z U p`; its definition quantifies over every scheme test and gives `HasSpaceBaseChange`, `SpaceMapIsSmooth`, and `SpaceMapIsSurjective` for its actual projection |
| The scheme composite f p is quasi-compact | `hqc : ∃ q : U ⟶ Y, Nonempty (ModuliTwoIso (p.comp f) (discreteModuliMap (yoneda.map q))) ∧ QuasiCompact q.left` |
| The relative diagonal uses the given 2-fibre product | `moduliRelativeDiagonal f : BasedFunctor Z (moduliTwoFiberProduct f f)` |
| Pullback of the diagonal along every affine scheme test is represented by an affine scheme | `hdiag` quantifies over `T : Over S`, `IsAffine T.left`, and every `t` into `moduliTwoFiberProduct f f`, and asserts `∃ R : Over S, IsAffine R.left ∧ IsRepresentedByScheme (moduliTwoFiberProduct t (moduliRelativeDiagonal f)) R` |
| f is quasi-compact | `IsQuasiCompactAlgebraicModuliMap.{u, v, w, u, u + 1, v₁, w₁} f` |
| f is quasi-separated | `IsQuasiSeparatedAlgebraicModuliMap f` |
| No finite-type, Noetherian or nonempty assumption | No such binder appears; the only hypotheses are `hZ`, `hp`, `hqc`, `hdiag` |

In `hqc`, q is not an arbitrary substitute map. The displayed vertical natural
isomorphism identifies its discrete-groupoid map with the actual composite
p followed by f. Yoneda and the discrete target identify a scheme-to-scheme
map uniquely in this way. Existence of q expresses that very composite;
it adds no representability condition on f itself.

In `hdiag`, `IsRepresentedByScheme` is the existing equivalence over Sch/S,
not a bijection of isomorphism classes. Its argument is the actual 2-pullback.
The node asks that this source be an affine scheme. An equivalence over S
is enough for this source property: composing it with the canonical first
projection recovers the induced map R → T by Yoneda. The condition therefore
needs neither an arbitrary map nor an extra projection hypothesis. It is
exactly the affine-test meaning of affineness in the node, and retains
all automorphism groups. No duplicate affine-morphism predicate is introduced.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`:
  `CategoryTheory.IsAlgebraicModuliStack`, `IsSmoothModuliAtlas` (including
  `SpaceMapIsSmooth` and `SpaceMapIsSurjective` in the atlas definition).
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.discreteModuli`, `discreteModuliMap`, `ModuliTwoIso`,
  `moduliTwoFiberProduct`, `IsRepresentedByScheme`, `HasSpaceBaseChange`.
  Their full signatures and source docstrings were read, including the
  equivalence and projection compatibility in `HasSpaceBaseChange`.
- `Sheaf.AlgebraicGeometry.StackQcqsMorphism`:
  `CategoryTheory.IsQuasiCompactAlgebraicModuliMap`,
  `IsQuasiSeparatedAlgebraicModuliMap`, and the smooth-atlas notion
  `IsQuasiCompactModuli` used by the first predicate.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: the node's quasi-compact
  notion is `AlgebraicGeometry.QuasiCompact`, defined in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, with the recorded
  affine-open criterion. `LocallyOfFiniteType` is not assumed.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `AlgebraicGeometry.IsAffineHom`
  is the recorded affine-morphism notion. The node itself spells its stack
  hypothesis by affine scheme tests, so `hdiag` uses `IsAffine` on their sources.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsEtale`, `IsSurjective`, and `IsRepresentableWith` supply the actual
  algebraic-space projections in the imported atlas and qcqs predicates.
- `CategoryTheory.moduliRelativeDiagonal`, already public through
  `StackQcqsMorphism`, is owned by
  `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`; it sends x to
  `(x,x,id)` and is reused rather than reconstructed.

Already stated proof dependencies are imported without `public`:
`Sheaf.AlgebraicGeometry.AlgebraicStackFibreProducts`,
`Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus`, and Mathlib's
`Morphisms.QuasiSeparated`, `Morphisms.FinitePresentation`, and
`Morphisms.ClosedImmersion`. Statement dependencies are public imports.
The proof dependency `lem-sfb-space-affine-locality` has no recorded Lean
module in the read repository, so no import can yet be added for it. This
unstated proof input is named in the docstring and does not prevent stating
the present theorem; the statement needs no declaration from that lemma.
No import is omitted to avoid a cycle.

Edge cases checked mathematically before writing:

- Empty Z has an empty smooth atlas; its composite is quasi-compact and its
  diagonal tests have empty affine scheme source (Spec of the zero ring).
  The hypotheses and conclusions allow these cases.
- Empty Y forces the source stack and atlas to be empty; no `Nonempty`,
  `Nontrivial`, `IsConnected`, or inhabited instance excludes this case.
- An atlas U may be non-quasi-compact globally when Y is non-quasi-compact;
  `hqc` only requires quasi-compactness of U → Y. No `CompactSpace U.left`
  or `CompactSpace Y.left` is present.
- A nonseparated or non-Noetherian base S, non-finite-type schemes, and positive
  characteristic are unrestricted. The conclusion is relative to Y, not an
  assertion of absolute separatedness over S.
- Classifying stacks of affine smooth groups illustrate why f need not be
  representable: the theorem assumes representability of p only, and an affine
  diagonal, retaining nontrivial stabilizers.
- The stack Z has arbitrary morphism/object universes v,w; test universes
  v₁,w₁ remain independent. The qc predicate uses maxima including u and u+1,
  as defined by the dependency. No universe equality or small-test restriction
  has been imposed.

Searches (2026-10-24; all required `msearch.py` calls use group Q20 and this item):

1. `leanfinder`, query:
   `An algebraic stack morphism with affine diagonal and a smooth surjective scheme atlas whose composite is quasi compact is quasi compact and quasi separated`.
   Result: OK, 8 hits, including scheme `QuasiCompact.of_comp`,
   `quasiSeparated_eq_diagonal_is_quasiCompact`, `QuasiCompact`, and the instance
   `instQuasiCompactOfIsAffineHom`. All are scheme statements; no stack-atlas theorem.
2. `loogle`, query: `"QuasiCompact", "QuasiSeparated"`.
   Result: OK, 7 hits; scheme diagonal and postcomposition properties only.
3. `grep`, query:
   `algebraicStack|algebraic_stack|affine.*diagonal|diagonal.*affine`,
   restricted to `AlgebraicGeometry`.
   Result: OK, 15 hits, all scheme affine/diagonal definitions or lemmas in
   Affine, FormallyUnramified, Constructors, and QuasiSeparated.
4. `leansearch`, query:
   `A morphism of algebraic stacks with affine diagonal is quasi compact and quasi separated when its composite with a smooth surjective scheme atlas is quasi compact`.
   Result: OK, 8 hits, all scheme quasi-separatedness/diagonal statements.
5. `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and
   `dag/lean_names_upstream.json`, queries including
   `qcqs.*atlas|atlas.*qcqs|[aA]ffine[Dd]iagonal`, then the full proposed name.
   The proposed name is absent. Existing `algebraicStack_qcqs_permanence`
   assumes absolute quasi-separatedness of source and target; it is not this
   relative theorem. `flat_affine_action_stack_presentation` treats a specific
   quotient by an affine group with finite-type assumptions; it is not this
   general statement. Their signatures were opened and read.
6. `grep -rn` for `lem-sfb-stack-qcqs-atlas-affine-diagonal` in
   `lean/WeilConjectures`: no hits. Targeted searches for affine diagonal tests
   in `lean/Sheaf/AlgebraicGeometry` found the existing quotient theorem and
   existing `ModuliSchemeTest` vocabulary, but no statement of this node.

The requested example `lean/Sheaf/CategoryTheory/CompactObject.lean` currently
contains only `module` and the withdrawal notice. Its owning node records the
existing Mathlib compact-object predicate. Current active stack modules supplied
the applicable module header, public-section, namespace and universe conventions.
No released repair note exists for this item. No statement dispute was found.

Validation: `scompile.py Q20 lem-sfb-stack-qcqs-atlas-affine-diagonal <file>`
compiled both sandbox and library views successfully (3.2 s and 3.3 s), with
no errors or warnings. The signature was copied verbatim into `lean.statement`;
maximum Lean line width is at most 100; `autoImplicit` is false.

## Second reading by Q20

I reread the node and the complete module in a separate checking pass.
The checks were the composite orientation (Lean `p.comp f` is f after p),
vertical compatibility of its scheme representation, and the diagonal-test
orientation (`moduliTwoFiberProduct t (moduliRelativeDiagonal f)` is the
actual pullback used by the qcqs dependency). I checked that the affine test
restricts T, not the whole target Y, and that the affine representative R
represents this exact pullback, rather than an arbitrary groupoid. Both
qcqs conjuncts use the recorded predicates without an extra DM or absolute
quasi-separatedness assumption. Empty schemes and the enlarged test universes
remain included. All four proof steps, including the quasi-compact-space tests,
are in the theorem docstring. No mathematical mismatch or change was found.
This is a local rereading by the worker; the maintainer's independent review is
performed on the delivery as required by this dispatch, which forbids subagents.

Delivery dry run: `deliver2.py Q20 lem-sfb-stack-qcqs-atlas-affine-diagonal
--no-push` reported `OK (dry run)` at 3a2522c2000, passing server preflight and
per-file compilation. The staged set contained exactly this report, the item
node, and its Lean module.
