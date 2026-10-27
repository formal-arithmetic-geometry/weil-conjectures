## Worker report

The module `Sheaf.AlgebraicGeometry.TorusTorsorPicardRationalSurjectivity` states
`AlgebraicGeometry.torus_torsor_picard_rational_surjectivity`. Its sole proof is
`sorry`; there are no definitions, auxiliary postponed theorems, new nodes or
dependency repairs. The accepted stage-1 statement and split are preserved.
The old BLOCKED ending concerned stage 1; the current node has a passing stage-1
review and no Lean record, and `coord/queue.tsv` lists it in stage 2. The stage-2
handoff in brief-stage2 §0 applies. There is no repair note for the item.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| k is an arbitrary field | `{k : Type u} [Field k]` |
| X is a k-scheme | `X : Over (Spec (.of k))` |
| X is smooth | `[Smooth X.hom]` |
| X is separated | `[IsSeparated X.hom]` |
| X is of finite type | `[LocallyOfFiniteType X.hom] [QuasiCompact X.hom]` |
| X is geometrically integral | `[GeometricallyIntegral X.hom]` |
| T is a k-torus | `T : Grp (Over (Spec (.of k)))`, `hT : MultiplicativeType.IsTorus T` |
| q:Y -> X is a represented right T-torsor | `P : RepresentedRightTorsor T X`, with `Y = P.space.left` and `q = P.projection.left` |
| q is faithfully flat | `P.flat`, `P.surjective` |
| q is of finite presentation | `P.lfp`, `P.qc`, `P.qs` |
| right T-action over X | `P.action`, `P.one_action`, `P.mul_action`; commutation over X is part of `P.torsor.w` |
| (y,t) -> (y,yt) is the specified torsor isomorphism | `P.torsor : IsPullback (fst P.space T.X) P.action P.projection P.projection`; this is the square with these exact two projections, so it identifies the actual map with the pullback |
| L is any invertible module on Y | `L : P.space.left.Modules`, `[L.IsInvertible]` |
| there exists an integer c >= 1 | `∃ c : ℕ, 1 ≤ c ∧ ...`; positive natural exponents are exactly positive integer exponents |
| there exists an invertible module M on X | `∃ M : X.left.Modules, M.IsInvertible ∧ ...` |
| q^*M is isomorphic to L tensor c | `Nonempty ((Scheme.Modules.tensorPullback P.projection.left).obj M ≅ L.tensorPow c)` |

The existing torsor structure is not an extra assumption: it bundles precisely the
map, action, laws, finite presentation and cartesian square specified in the node.
It does not demand a chosen local section, a split torus, a rational point, or
Zariski triviality. `P.space` carries the k-structure forced by q and X. Finite
presentation is the project's locally-finite-presentation + quasi-compact +
quasi-separated convention. The group is the arbitrary torus T, not necessarily
split over k. The existential isomorphism has no normalization condition.

Dependency declarations used (their defining sources and docstrings were read):

- `def-weil-field`: Mathlib `Field` (`Mathlib.Algebra.Field.Defs`).
- `def-pc-scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`
  (`Mathlib.AlgebraicGeometry.Scheme`). Bundled objects over Spec k use `Over`.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`
  (`Mathlib.AlgebraicGeometry.Morphisms.Smooth`).
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` and
  `QuasiCompact` (the finite-type and quasi-compact morphism modules).
- `def-sc-invertible-module`: `Scheme.Modules.IsInvertible` and
  `Scheme.Modules.tensorPow`
  (`WeilConjectures.AlgebraicGeometry.Modules.Invertible`).
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `pullback.fst`,
  `pullback.snd` (`Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`).
  The existing torsor structure expresses its universal property as `IsPullback`.
- `def-pc-fppf-site`: `Scheme.fppfPrecoverage`, `Scheme.fppfTopology`
  (`Mathlib.AlgebraicGeometry.Sites.Fpqc`); the represented torsor has the
  flat, surjective and locally-finitely-presented singleton cover prescribed there.
- `def-sfb-tori-multiplicative-type`: `MultiplicativeType.IsTorus`, with the
  actual algebraic-closure base change and finite split product
  (`Sheaf.AlgebraicGeometry.ToriMultiplicativeType`).
- Existing landed `def-sfb-split-solvable-right-torsors`:
  `AlgebraicGeometry.RepresentedRightTorsor`
  (`Sheaf.AlgebraicGeometry.SplitSolvableTorsorDefinitions`). Its name includes
  split solvability, but the represented torsor definition itself is for any
  group over any base. This landed definition owner is added to `stmt_deps`.
- Existing landed `def-pc-module-pullback`: `Scheme.Modules.tensorPullback`
  (publicly exported by its recorded module
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`, constructed in
  `WeilConjectures.AlgebraicGeometry.TensorPullback`). This already-used proof
  dependency is added to `stmt_deps` since the conclusion uses its construction.
- Geometric integrality is the existing Mathlib `GeometricallyIntegral`
  (`Mathlib.AlgebraicGeometry.Geometrically.Integral`): all field-valued base
  changes are integral. No duplicate predicate is introduced.

The module publicly imports statement dependencies and privately imports the
recorded modules of the stated proof dependencies. In particular it retains the
finite-field fpqc, affine/local-finite-type/quasi-compact descent, character
antiduality, field-degree, proper/smooth base change, algebraic-space fppf
calculus, and qcqs permanence modules. The separated/finite-type base-change
instances are already in public statement imports. At the time of writing,
`lem-sfb-split-torus-torsor-line-pullback` and
`lem-sfb-finite-field-picard-norm-base-change` have neither a Lean record nor a
Mathlib match. They are proof inputs only, introduce no object needed to type
this theorem, and have no module to import yet. The docstring retains their
names and exact roles for stage 3 and the maintainer's later proof-import update.

Sources: the current latest blueprint unit
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`
was read. This is an auxiliary node, not that unit's own statement. The Sansuc
PDF named by the node is still WANTED, as recorded by the passing NX stage-1
report; no claim to have read that PDF is made. The accepted proof has four
steps and is transcribed into the theorem docstring. The locally read Stacks
`divisors.tex`, `lemma-norm-invertible` (0BCY) and
`lemma-finite-locally-free-has-norm` (0BD2) give the degree identity and arbitrary
base-change property used by its last step. No source or split is changed.

Edge cases checked before writing:

- Rank zero is allowed by `IsTorus` and `splitTorus ... 0`. A torsor under the
  trivial group is an isomorphism and the conclusion permits c = 1.
- Nonsplit tori remain allowed: no split-isomorphism hypothesis appears.
  The finite separable splitting degree may exceed one, so the conclusion asks
  only for a positive tensor power, not for integral Picard surjectivity.
- For a splitting field of degree one, c = 1 is included. c = 0 is excluded;
  its trivial tensor power would not assert rational surjectivity.
- The structure sheaf is included among L. No nontriviality assumption on L
  or injectivity of q^* on Picard classes is asserted.
- Empty X is excluded exactly by geometric integrality, as in the node. No
  extra nonemptiness, properness, projectivity or affine hypothesis is imposed.
- Imperfect fields and every characteristic are included. Neither characteristic
  nor a perfectness hypothesis appears, and no separability is imposed on k.
- There is no bound on torus rank and no dimension bound on X. `u` is explicitly
  declared and all variables are bound; `autoImplicit` is disabled. Over k the
  schemes, group and module categories use the established project size convention.

Searches (all executed for this item; the wrapper retains `searches.jsonl`):

- LeanFinder: "Every invertible module on a torus torsor over a smooth geometrically
  integral variety has a positive tensor power pulled back from its base".
  Eight hits: ring-module invertibility, tensor products, ring Picard classes and
  a pullback carrier instance. Their displayed types do not state this scheme
  torsor assertion.
- Loogle: `"Pic", "tensor"`. Two hits, `CommRing.Pic.mk_tensor` and
  `CommRing.Pic.mul_eq_tensor`: ring Picard multiplication, not surjectivity
  along an arbitrary torus torsor.
- LeanSearch: "Picard group pullback along a torus torsor is surjective after
  tensoring with the rationals". Eight hits on ring Picard scalar extension and
  a group-object base-change instance, none on this assertion.
- msearch grep: `TorusTorsor|torus.*[Pp]icard|[Pp]icard.*torus`: zero Mathlib hits.
- Project/source rg: `torus.*[Pp]icard|[Pp]icard.*torus` and the exact item id in
  `lean/WeilConjectures` and `lean/Sheaf`: no existing declaration of the item.
  Searches for `Torus`, `SplitTorus` and represented torsors located the existing
  `ToriMultiplicativeType` and `SplitSolvableTorsorDefinitions`, which are reused.
- Mathlib/project rg for `GeometricallyIntegral` located the exact Mathlib class;
  its definition and documentation were read. Searches for `tensorPow` located
  the existing recursive tensor power in `Modules.Invertible`.

Validation: scompile.py compiled this one delivered module in sandbox and library
module modes with exit 0 and no messages other than timings. No local Lean, Lake,
global build, direct Git command or live-file edit was used.

## Second reading by Q117

I reread the live statement alongside the final signature and unfolded the
existing `RepresentedRightTorsor` and `IsTorus` definitions. This is the worker's
second pass; the maintainer supplies the independent delivery review, as the
assignment requires. No second agent was started.

The field, all five geometric conditions on X, arbitrary nonsplit torus, full
right-action laws, over-X compatibility, faithful flatness, finite presentation
and specified torsor square match. The square uses (first projection, action),
so its comparison is (y,t) -> (y,yt), not an arbitrary isomorphism. The conclusion
keeps L on the torsor's actual scheme, M on the actual base, positive c and tensor
inverse image along its actual projection. `Nonempty` is used only for existence
of the requested isomorphism, not to choose any construction. No mismatch or
statement correction was found. The only node changes are the Lean attachment
and citations of the two already landed definition owners described above.
