## Worker report

The delivery states `AlgebraicGeometry.Scheme.Hom.exists_qcqs_arrow_absoluteApproximation`
in `Sheaf.AlgebraicGeometry.QcqsArrowAbsoluteApproximation`. It has one theorem with
proof `sorry`, no definitions, and no changes to the node except its `lean` record.
The source was read in `literature/stacks-project/limits.tex`, label
`lemma-approximate-morphism`, Tag 0GS1. The existing stage-1 proof already repairs
the direction of the target bound in the printed directedness argument. Its eight
steps, including the partial-order reindexing and cofinality arguments, are included
in the theorem docstring.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| A morphism of schemes `f : X → S` | `{X S : Scheme.{u}} (f : X ⟶ S)` |
| `X` quasi-compact and quasi-separated | `[CompactSpace X] [QuasiSeparatedSpace X]` |
| `S` quasi-compact and quasi-separated | `[CompactSpace S] [QuasiSeparatedSpace S]` |
| A small nonempty directed partially ordered set `I` | Existential `(I : Type u) (_ : PartialOrder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))` |
| Schemes `X_i`, `S_i` | `(D E : Iᵒᵖ ⥤ Scheme.{u})`, with stages `D.obj (op i)`, `E.obj (op i)` |
| Both stages of finite type over `Spec ℤ` | For each stage, `LocallyOfFiniteType (specULiftZIsTerminal.from ...) ∧ QuasiCompact (specULiftZIsTerminal.from ...)` |
| Both stages qcqs | The explicit `CompactSpace` and `QuasiSeparatedSpace` conjuncts for both `D.obj i` and `E.obj i` |
| Stage morphisms `f_i` | Components `F.app i` of `(F : D ⟶ E)` |
| Transition maps for `j ≥ i` | The functor maps on the arrow `op j ⟶ op i` of the opposite poset category |
| Identity and composition laws | `D.map_id`, `D.map_comp`, `E.map_id`, `E.map_comp`, built into the functor types |
| Affine transitions on both sides | `∀ (i j : Iᵒᵖ) (a : i ⟶ j), IsAffineHom (D.map a) ∧ IsAffineHom (E.map a)` |
| `f_i a_ji = b_ji f_j` | Naturality of `F`: `D.map a ≫ F.app j = F.app i ≫ E.map a` for `a : i ⟶ j` in `Iᵒᵖ` |
| Compatible projections `p_i`, `q_i` | Natural transformations `p : (Functor.const Iᵒᵖ).obj X ⟶ D` and `q : (Functor.const Iᵒᵖ).obj S ⟶ E`; their naturality is projection compatibility |
| `f_i p_i = q_i f` | `∀ i : Iᵒᵖ, p.app i ≫ F.app i = f ≫ q.app i` |
| `X` with these projections is a limit | `Nonempty (IsLimit (Cone.mk X p))` |
| `S` with these projections is a limit | `Nonempty (IsLimit (Cone.mk S q))` |
| Unique factorization of every test cone | The `lift`, `fac`, and `uniq` fields of each `IsLimit`; cones range over arbitrary test schemes in `Scheme.{u}` |
| No finite-type assumption on `f` | Its only binder is `(f : X ⟶ S)`, with the four qcqs assumptions on the schemes |
| The target stages may vary | `E` is existentially quantified as an arbitrary diagram, without any constancy requirement |

The integer base is the existing Mathlib terminal scheme
`Spec (CommRingCat.of (ULift.{u} ℤ))`; `specULiftZIsTerminal.from` is its canonical
structure morphism. The lift merely places the integer ring in the same universe
as the schemes. Finite type uses exactly the recorded conjunction, rather than
assuming a bundled finite-type predicate or substituting local finite type alone.
The index type is in the schemes' universe, not an independent smaller universe.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-pbc-scheme-conventions`: the record explicitly fixes no declaration;
  use `CompactSpace` and `QuasiSeparatedSpace` for schemes. The equivalence with
  intersections of affine opens is `quasiSeparatedSpace_iff_forall_affineOpens` in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, and `AlgebraicGeometry.QuasiCompact`
  in `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` (publicly available through
  the finite-type module), used as the recorded conjunction on each structure map.
- `pqf-def-affine-morphism`: `AlgebraicGeometry.IsAffineHom`, in
  `Mathlib.AlgebraicGeometry.Morphisms.Affine`.
- The canonical integer structure map is supplied by
  `AlgebraicGeometry.specULiftZIsTerminal`, `Mathlib.AlgebraicGeometry.Limits`.
- The universal properties use `CategoryTheory.Limits.Cone.mk` and
  `CategoryTheory.Limits.IsLimit`, including its `lift`, `fac`, `uniq` fields.

The recorded proof-dependency modules are imported privately:

- `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit` supplies
  `AlgebraicGeometry.Scheme.nonempty_noetherianApproximation` for
  `prop-nagata-noetherian-inverse-system`.
- `Mathlib.CategoryTheory.Presentable.Directed` supplies
  `CategoryTheory.IsFiltered.exists_directed` for
  `lem-weil-pbc-cofiltered-limit-directed-reindex`.
- `Mathlib.CategoryTheory.Limits.Final` supplies
  `CategoryTheory.Functor.initial_op_of_final` and
  `CategoryTheory.Functor.Initial.isLimitWhiskerEquiv`, used by the directed reindexing
  and `lem-weil-pbc-initial-functor-limit`.
- `Mathlib.AlgebraicGeometry.Noetherian` supplies
  `AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian.quasiSeparatedSpace`, and
  `AlgebraicGeometry.LocallyOfFinitePresentation.iff_locallyOfFiniteType` for
  `lem-weil-pbc-finite-type-over-noetherian`,
  `lem-weil-pbc-locally-noetherian-quasi-separated`, and `pqf-lem-lft-fp-locnoeth`.
  The accompanying `QuasiCompact.compactSpace_of_compactSpace` was also read in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.AffineTransitionLimit` supplies
  `AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`
  and `AlgebraicGeometry.Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType`,
  for the recorded factorization and eventual-equality proof dependencies.

Edge cases checked before writing: the empty source is allowed (empty source
stages work); an empty target forces an empty source, also allowed; finite-type
arrows admit constant systems; arbitrary non-finite-type arrows, such as
`Spec ℤ[x₀,x₁,…] → Spec ℤ`, retain the required finite-subalgebra approximations.
No assumption of inhabited underlying spaces, separatedness, affineness of `f`,
or finite type of `f` appears. Empty indexing is excluded exactly by `Nonempty I`.
Identities and arbitrary characteristics are included. Universal properties use
the actual vertices `X` and `S`, so the result is stronger than merely giving
unidentified objects isomorphic to some chosen limits, as the node requires.

Searches for an existing exact statement (2026-10-24):

- `msearch.py ... leanfinder "Every morphism between quasi compact quasi separated
  schemes is a directed inverse limit of morphisms between finite type schemes
  over the integers with affine transitions"`: 8 hits, including normalization,
  existing-limit map equality, and eventual affineness; no simultaneous arrow
  approximation theorem.
- `msearch.py ... leansearch "A morphism between quasi compact quasi separated
  schemes is an inverse limit of morphisms of schemes of finite type over the
  integers"`: 8 hits on `QuasiCompact`, `QuasiSeparated`, and standard morphism
  properties; no exact result.
- `msearch.py ... loogle "NoetherianApproximation, Scheme.Hom"`: no hits,
  `NoetherianApproximation` unknown to the Mathlib search index.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme, AlgebraicGeometry.LocallyOfFiniteType"`:
  12 hits, finite-type properties and essential smallness of affine stages;
  no simultaneous approximation.
- `msearch.py ... grep "approximate.*[Mm]orphism|[Aa]rrow.*[Aa]pproximation|simultaneous.*approximation"
  AlgebraicGeometry`: no hits in Mathlib.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `0GS1|approximate.*[Mm]orphism|[Aa]rrow.*[Aa]pproximation|simultaneous.*approximation`,
  and the literal item id: no matching arrow-approximation statement; the few
  semantic hits discuss other approximation constructions. The existing individual
  `Scheme.NoetherianApproximation` and its existence theorem were read in full.
- `rg` of `dag/lean_names_upstream.json`, both project roots and Mathlib for the
  chosen declaration and module names: no existing declaration with these names.

No statement correction, disputed statement, new definition node, dependency
repair, or source fault was needed. The stale example module named in the brief
is withdrawn; its node now records the upstream module
`WeilConjectures.CategoryTheory.CompactObject`, which was read for conventions.
There is no maintenance repair note for this item.

Validation: prescribed `scompile.py` passed both sandbox and library compilation
of the delivered module, 1.5 seconds each, with no diagnostics. All variables and
the sole universe `u` are explicitly bound. The expected stage-2 `sorry` is the
whole proof of the named theorem.

## Second reading by Q50

The assigned worker reread the node and the full module in a separate pass;
no additional agent was started, following the dispatcher's explicit instruction.
The maintainer performs the independent review. This rereading checked the four
qcqs hypotheses, the universe of the existential index, partial order rather than
preorder, nonemptiness and directedness, both finite-type conjunctions and both
qcqs stage clauses, both affine transition conditions, the direction of each
naturality square, compatibility of both projection families, the square with
`f`, and the two limit universal properties. Every clause is accounted for in the
table above. Functor laws and naturality are structure fields rather than extra
tautological conjuncts; limit data are wrapped in `Nonempty` because `IsLimit` is
a type of universal-property data. No mismatch or change was found.
