## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteFiberDegreeBaseChange` states the pointwise finite
fibre degree result and its bound-preservation consequence. Both proofs are `sorry`; no
definition or proof is supplied. The node statement is unchanged; no new or dependency nodes
are needed. Server compilation succeeded without errors or warnings.

Hypotheses and clauses, matched individually:

- Schemes X, S, T: `{X S T : Scheme.{u}}`, with an explicitly bound arbitrary universe `u`.
- Morphisms f and g: `(f : X ⟶ S) (g : T ⟶ S)`; no further property of either is assumed.
- Fibre product X_T and its projection f_T: `pullback f g` and `pullback.snd f g`.
- Point t and s = g(t): `(t : T)` and `g t`. The latter replaces the node's local abbreviation s.
- Residue fields and scheme-theoretic fibres: `fiberToSpecResidueField (g t)` and
  `(pullback.snd f g).fiberToSpecResidueField t` have sources `f.fiber (g t)` and
  `(pullback.snd f g).fiber t` and targets `Spec (S.residueField (g t))` and
  `Spec (T.residueField t)` respectively.
- The old fibre is finite over its residue field: the explicit hypothesis
  `hf : IsFinite (f.fiberToSpecResidueField (g t))`.
- Degree d is the dimension of the old fibre's global sections:
  `(f.fiberToSpecResidueField (g t)).finrankΓ`. The node defines d by this expression;
  using the expression directly removes a local abbreviation, not a hypothesis.
- Finiteness of the new fibre: the first conjunct
  `IsFinite ((pullback.snd f g).fiberToSpecResidueField t)`.
- Equality of dimensions to d: the second conjunct equates the new fibre's `finrankΓ`
  with the old fibre's `finrankΓ`. That definition uses exactly the scalar action induced
  by the structure morphism on global sections, not a separately chosen algebra structure.
- A nonnegative integer bound n: `(n : ℕ)` in `boundsFiberDegrees_pullback_snd`.
- The hypothesis that n bounds every finite fibre degree of f:
  `hf : BoundsFiberDegrees f n`, using the recorded dependency definition.
- The same bound for f_T: `BoundsFiberDegrees (pullback.snd f g) n`. This includes both
  finiteness and the dimension inequality at every point, also when the target is empty.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.snd`; scheme pullbacks exist in Mathlib.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.Hom.residueFieldMap`; the former is the local-ring residue field and the latter
  induces the extension map used in the natural-language proof.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber` and `fiberToSpecResidueField`;
  the source is the pullback along the canonical residue-field point.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`, the affine
  morphism with finite ring maps on affine opens. The node's integral notion is not used.
- `Sheaf.AlgebraicGeometry.FiberDegreeBound`: `Scheme.Hom.BoundsFiberDegrees`, whose body
  requires finiteness of each fibre projection and the upper bound on its `finrankΓ`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`: `Scheme.Hom.finrankΓ` and
  `ΓAlgebra`. These are imported through the recorded bound module. `ΓAlgebra` is the
  algebra induced by `ΓSpecIso.inv` followed by `appTop`; `finrankΓ` takes its dimension.

All required notions are available through the one direct import. No private definitions
are introduced. All variables and universes are explicit. The theorem docstrings carry
steps 1--7 and step 8 of the node's proof, respectively, including the cited DAG nodes.

Edge cases checked: an empty old fibre is finite of degree zero, and base change stays
empty with degree zero. A bound n = 0 therefore permits empty fibres. An empty T makes
bound preservation vacuous; the pointwise statement needs an actual t. An empty S admits
no t through g. Arbitrary residue-field extensions and every characteristic are included;
there is no separability, reducedness, or flatness assumption on f. Nonreduced finite fibres
are measured by vector-space dimension, including multiplicities, rather than point count.

Source check: the local literature checkout does not contain `morphisms.tex`, so I opened
[Stacks 03J5](https://stacks.math.columbia.edu/tag/03J5) and
[Stacks 03J7](https://stacks.math.columbia.edu/tag/03J7) directly. Their proof and statement
identify the field-valued fibre as a residue-field base change and preserve the same bound.
The tensor-product dimension argument is expanded in the DAG proof.

Searches performed (logged by msearch.py in searches.jsonl):

- LeanFinder: "Degree of a finite scheme theoretic fiber is unchanged by arbitrary base
  change, and bounds on degrees of fibers are preserved". Eight hits: stability of finite
  morphisms and related finite-type properties, finiteness of fibre carriers, and affine
  ring-map base-change results; no degree equality with only a finite-fibre hypothesis.
- Loogle: "AlgebraicGeometry.Scheme.Hom.fiber, Module.finrank". Zero hits.
- LeanSearch: "degree of a finite scheme fiber unchanged under base change". Service returned
  Internal Server Error; recorded unavailable, with no absence verdict inferred from it.
- Mathlib grep: "finrank_pullback|fiberDegree|finrankΓ" in AlgebraicGeometry. Five hits in
  FlatRank. Its `Scheme.Hom.finrank_pullback_snd` requires global finite flatness, so it does
  not state this node.
- Source rg: "lem-weil-pbc-fibre-degree-base-change|fiberDegree_of_isPullback|finrankΓ.*[Bb]ase|
  finrankΓ.*[Pp]ullback" in WeilConjectures. The existing `fiberDegree_of_isPullback` requires
  global `IsAffineHom` on the original and base-changed morphisms; full signature read.
  No blueprint-id hit and no matching general finite-fibre declaration.
- Project rg: "fiberDegree|finrankΓ|BoundsFiberDegrees" in lean/Sheaf. The recorded definition
  module and a composition-bound statement exist; neither supplies the base-change theorem.
- New full names checked by rg in dag/lean_names_upstream.json, Mathlib, WeilConjectures and
  lean/Sheaf: "finite_fiber_degree_pullback|boundsFiberDegrees_pullback_snd". No hits.

No statement dispute or node fault was found. The second reader will supply the independent
second-reading section and deliver; this worker only runs the dry run.

## Second reading by M1

I independently opened the sandbox node and module, all six statement-dependency nodes,
their recorded declarations, the upstream degree definitions and candidate theorem, and
the Stacks source. No statement mismatch was found; the Lean and node are unchanged.

Objects, hypotheses and conclusions, listed from the node and matched to the Lean:

1. Arbitrary schemes X, S, T and morphisms f : X -> S, g : T -> S are
   `{X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)`. Exact: Scheme and Scheme.Hom
   are the recorded locally ringed space notions. No affineness, flatness, finite type,
   Noetherian, separatedness, reducedness or global finiteness instance is assumed.
2. X_T = X ×_S T and its projection to T are `pullback f g` and `pullback.snd f g`.
   Exact: I read pullback and its projections in HasPullback.lean and the Scheme
   HasPullbacks instance in Pullbacks.lean. Choosing this pullback loses no case.
3. A point t of T and s = g(t) are `(t : T)` and `g t`. Exact: s is an abbreviation,
   so no extra independent s or equality hypothesis is needed.
4. The residue fields κ(s), κ(t) are `S.residueField (g t)` and `T.residueField t`.
   Exact: ResidueField.lean defines them as the residue fields of the stalks and defines
   `g.residueFieldMap t` from the local stalk map. There is no chosen unrelated field action.
5. The old fibre with its κ(s)-structure is `f.fiber (g t)` with
   `f.fiberToSpecResidueField (g t)`. The new fibre with its κ(t)-structure is
   `(pullback.snd f g).fiber t` with `(pullback.snd f g).fiberToSpecResidueField t`.
   Exact: Fiber.lean defines these as the pullbacks along fromSpecResidueField and their
   second projections. Neither fibre is just a set-theoretic preimage.
6. The sole substantive pointwise hypothesis, that the old fibre is finite over κ(s), is
   `(hf : IsFinite (f.fiberToSpecResidueField (g t)))`. Exact: IsFinite in Finite.lean
   means affine with finite ring maps on affine opens, as the dependency node requires.
   Its integral companion is irrelevant to this statement.
7. The degree d = dim over κ(s) of the old global sections is
   `(f.fiberToSpecResidueField (g t)).finrankΓ`. Exact: FiberDegree.lean defines
   ΓAlgebra using `ΓSpecIso.inv ≫ h.appTop`, and finrankΓ is Module.finrank with this
   algebra structure. Since the fibre is finite, this natural number is the stated
   finite vector-space dimension. Eliminating the abbreviation d is exact.
8. The new fibre is finite over κ(t): the first conjunct is
   `IsFinite ((pullback.snd f g).fiberToSpecResidueField t)`. Exact.
9. Its global-section dimension over κ(t) equals d: the second conjunct is
   `((pullback.snd f g).fiberToSpecResidueField t).finrankΓ =
   (f.fiberToSpecResidueField (g t)).finrankΓ`. Exact, including the structure-map
   scalar actions. No point-count or reduced-fibre replacement occurs.
10. For a nonnegative integer n bounding all fibres of f, the second lemma has
    `(n : ℕ) (hf : BoundsFiberDegrees f n)`. Exact by the cited definition node,
    which explicitly uses n ≥ 0: BoundsFiberDegrees requires every fibre to be finite
    and its structure-map finrankΓ to be ≤ n. The node's final word "integer" refers
    to this defined notion, not to an independently defined predicate on negative integers.
11. That same n bounds the fibres of f_T: the conclusion is
    `BoundsFiberDegrees (pullback.snd f g) n`. Exact: both finiteness and the inequality
    hold at every t. The pointwise lemma quantifies over f, g, t before its finite-fibre
    hypothesis; the bound lemma quantifies over f, g, n before its bound hypothesis.

Source reading: literature/stacks-project is absent locally. I read the official pages
[03J4](https://stacks.math.columbia.edu/tag/03J4),
[03J5](https://stacks.math.columbia.edu/tag/03J5), and
[03J7](https://stacks.math.columbia.edu/tag/03J7), then fetched and read their labelled
blocks in the official [morphisms.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/morphisms.tex),
including the section context. There are no extra standing hypotheses on these schemes.
03J5 explicitly uses the residue-field fibre base-change identity; 03J7 preserves the
same bound under arbitrary base change. Attribution clarification to the worker report:
the current 03J5 TeX does not literally spell out the tensor-product dimension equality.
That equality is the valid linear-algebra expansion in the DAG's steps 2--7, not a direct
quotation of current 03J5. This does not require a statement correction.

Edge cases: the empty scheme has zero global-section vector space, is finite over a field,
and stays empty under field extension. Thus zero degree and n = 0 are included. Empty T
makes the bound conclusion vacuous, and the first lemma only applies when t exists.
If S is empty then a morphism T -> S forces T empty. Nonreduced finite fibres retain
multiplicities in the dimension. All characteristics, inseparable residue-field extensions,
and zero global-section rings are allowed. No index set is introduced. The arbitrary
explicit universe u is the universe of the recorded Scheme category and its pullbacks;
there are no unbound universes or implicit variables, and no small-universe restriction.

Independent searches (also recorded by msearch.py):

- LeanFinder: "finite scheme fibre global sections dimension invariant residue field
  extension arbitrary pullback". Eight hits, for finite fibre carriers, fibre projections,
  residue maps and quasi-finite algebra fibres; none gives the degree equality here.
- Loogle: "AlgebraicGeometry.Scheme.Hom.finrankΓ". The service does not know this project
  identifier, so this lookup gives no absence evidence for project declarations.
- LeanSearch: "finite fibre vector space dimension preserved after base change of schemes".
  Internal Server Error; recorded unavailable, with no absence conclusion from it.
- rg on Mathlib AlgebraicGeometry for finrank/baseChange/pullback and on the source
  WeilConjectures/AlgebraicGeometry/Morphisms and WeilConjectures/Mathlib/AlgebraicGeometry
  for finrankΓ and fibre-degree base-change declarations; rg on project AlgebraicGeometry
  for fiberDegree, BoundsFiberDegrees and the proposed full names; checked upstream names.
  I opened the closest signatures: Mathlib finrank_pullback_snd needs [Flat f] [IsFinite f]
  globally; upstream fiberDegree_of_isPullback has [IsAffineHom g] and [IsAffineHom g'].
  Neither states this arbitrary-morphism, single-finite-fibre result. The landed project
  composition bound is also different. Existing ΓAlgebra, finrankΓ and BoundsFiberDegrees
  are reused through the single relevant import. No duplicate notion or theorem was found.

H5/H6/H8/H9/H12/H13: there are no definitions, new nodes or dependency modules in this
sandbox. Both theorem bodies are exactly `by sorry`; no theorem is proved. Every declaration
has its source and blueprint marker. The first docstring follows proof steps 1--7 with their
DAG references, including the compatible field action; the second gives step 8. The
namespace, explicit universe, import and line lengths satisfy the conventions. The node's
lean.statement agrees verbatim with the first signature. No statement_change is present,
so correction-citer review is inapplicable. The only change from this second reading is this
report section, including the source-attribution clarification; correct Lean was preserved.
