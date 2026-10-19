## Worker report

Repaired the saved packet for returned head `38cd83ca0f1f`. The initial required
`deliver2.py --no-push` passed at `128171dc8a`; the subsequent mathematical self-check
found that its proposed HEq repair still failed H3. This delivery replaces those
heterogeneous equalities by composed, canonically transported isomorphisms. It also
requires realization of the supplied transitions, and uniqueness of a *global* scheme
and module isomorphism between realizations. All 17 owning declarations are listed in
`lean.declarations`. The generic theorem belongs in
`Sheaf.AlgebraicGeometry.PolarizedSchemeEtaleDescent`; the old TraceFormula module is
not delivered.

The original natural statement on current main is already the correct descent theorem.
It specifies the identity, composite lambda cocycle, compatible realizations, and
unique compatible pair isomorphism. The saved packet's statement_change confused
faults of its Lean with faults of that prose. I restored the original statement
verbatim and removed that correction record. No natural statement or proof was
changed. Three already landed prerequisites were added to stmt_deps for the actual
tensor pullback, its sectionwise pinned adjunction, and its canonical composition
comparison. There are no new nodes or dependency-module repairs.

Clause-by-clause correspondence (D is the datum, d a candidate pair):

* A scheme S and a family indexed by any set: `(S : Scheme.{u}) (I : Type v)`,
  with independent, explicitly bound universes u and v. `U`, `uMap`, `X`, `f`, `L`
  supply exactly the named local schemes, structure maps and modules.
* Jointly surjective etale covering: `D.isEtale : ∀ i, Etale (uMap i)` and
  `D.jointlySurjective : ∀ x : S, ∃ i, ∃ y : U i, (uMap i).base y = x`.
* Invertible local modules: `hL : ∀ i, Scheme.Modules.IsInvertible (L i)`.
* The specified overlap: `polarizedOverlap` is literally
  `pullback (f i) (pullback.fst (uMap i) (uMap j))`. `polarizedOverlapX`,
  `polarizedOverlapUi`, and `polarizedOverlapUj` are its canonical projections.
  The right-hand local overlap is written with swapped factors, R_ji; this is
  the canonical symmetry identification of the paper's second pullback over U_ij.
* Scheme overlap isomorphisms: `D.theta i j : R_ij ≅ R_ji`.
  `theta_over_left` and `theta_over_right` impose both base-projection equations.
  `theta_identity` is equality after the explicitly constructed diagonal map.
  `theta_cocycle` quantifies maps a,b,c,d from a test scheme T and all five
  compatibility equations. The conclusion `c ≫ (theta i k).hom = d` compares
  transition directly from i to k with transition through j, including the base maps.
  Testing schemes in the same universe as X is sufficient: the representing
  triple overlaps themselves lie there. No smaller independent test universe is used.
* Line overlap isomorphisms: `D.lambda i j` is an actual isomorphism
  `P_(theta_ij;p_ji) L_j ≅ P_p_ij L_i`, with P the tensor-formula pullback.
  The canonical composition comparison identifies this with theta_ij^* of the
  pullback of L_j, exactly as in the natural statement.
* Line identity: `lambda_identity` equates the diagonal pullback of lambda_ii
  with equality transport along `theta_identity`. Both ends are normalized to
  composite maps by `polarizedPullIso`; after identifying diagonal projection
  with the identity this is the identity of L_i.
* Line cocycle: `lambda_cocycle` quantifies a:T→R_ij, b:T→R_jk, c:T→R_ik
  and equations `hmid`, `hend`, `hstart` identifying their three chart endpoints.
  The left side is the normalized pullback of lambda_ik. The right side is
  equality transport, then the pullback of lambda_jk, middle equality transport,
  then the pullback of lambda_ij, then final equality transport. Thus it is
  lambda_ij composed with lambda_jk, not equality of those individual transitions.
  These endpoint equations describe exactly compatible triple-overlap test maps:
  the theta base equations identify their U_i,U_j,U_k maps. The theta cocycle
  identifies the last chart endpoint. Conversely such test maps yield that triple.
* Ampleness on every affine inverse image: `ample_local` quantifies every
  `V : (U i).Opens` and `IsAffineOpen V`, then applies the recorded
  `Scheme.Modules.IsAmple` to `(f i ⁻¹ᵁ V).toScheme` and the tensor pullback
  along its inclusion. Its existential h supplies only the proof of invertibility
  required by the IsAmple API. It adds no module data or geometric condition:
  restriction of the given invertible L_i is invertible. Proof irrelevance makes
  the chosen invertibility proof immaterial.
* Existence: `∃ d : PolarizedDescentPair ...` supplies `d.Y`, `d.g`, `d.M`,
  `d.isInvertible`, and charts `pullback d.g (uMap i) ≅ X i`, their over-U_i
  equations, and actual module comparisons from pulled-back M to pulled-back L_i.
* Realization of the *given* theta and lambda: the conclusion includes
  `IsPolarizedDescentRealization D d`. Its theta equation says the two overlap
  maps to Y agree. Since each chart is Y×_S U_i ≅ X_i over U_i, this says its
  induced overlap transition is exactly D.theta. Its lambda equation expresses
  D.lambda as the inverse j-chart trivialization, transport through that same
  pulled-back global M, and the i-chart trivialization. `polarizedChartLine`
  is constructed from the stored moduleIso, inverse chart, and canonical tensor
  composition/identity comparisons; it is not a new arbitrary trivialization.
* Unique compatible isomorphism: the second candidate d' is quantified with
  the hypothesis `IsPolarizedDescentRealization D d'`. The conclusion gives an
  `e : PolarizedDescentPairIso d d'` and `∀ e', e' = e`. This structure contains
  one `schemeIso`, its over-S equation, one global
  `moduleIso : P_(schemeIso.hom) d'.M ≅ d.M`, and compatibility with every chart
  (`chart`) and every local module identification (`line`). Both routes in line
  are typed from the same global-module pullback to L_i. Uniqueness includes the
  global module isomorphism, not merely its existence separately on each chart.

Dependency declarations used:

* Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme` and its morphisms.
* Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: `pullback`,
  `pullback.fst`, `pullback.snd`, `pullback.lift`, `pullback.diagonal`.
* Mathlib.AlgebraicGeometry.Sites.Etale and Morphisms.Etale:
  `Scheme.smallEtaleTopology`, `Scheme.Etale`, `Etale`; the cover conditions
  are the etale-arrow and pointwise-surjectivity criterion of this site.
* WeilConjectures.AlgebraicGeometry.Modules.Invertible:
  `Scheme.Modules.IsInvertible` (its signature and definition were read).
* WeilConjectures.AlgebraicGeometry.Ample: `Scheme.Modules.IsAmple`, the
  quasi-compactness and positive tensor-power affine-nonvanishing-locus predicate.
* WeilConjectures.AlgebraicGeometry.TensorPullback: `Scheme.Modules.tensorPullback`;
  read the current source through `scompile.py --source`.
* The recorded sectionwise adjunction `Scheme.Modules.exists_tensorPullbackAdjunction`
  and `Sheaf.AlgebraicGeometry.TensorPullbackCompositionIso`:
  `Scheme.Modules.tensorPullbackCompositionIso`; read its current source through
  `scompile.py --source`. The identity comparison uses the pinned adjunction and
  `pushforwardId`, not a choice from a bare Nonempty set of natural isomorphisms.
* Stated proof prerequisites are imported non-publicly: the recorded
  `Sheaf.AlgebraicGeometry.AlgebraicSpace` and
  `WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf`.
  Other proof prerequisites currently have no Lean records and are not imported.

Every helper has a source/blueprint docstring. The sole postponed theorem has a
six-step proof docstring matching the node: etale relation, algebraic-space
quotient, recovery of charts, invertible-module descent, representability by
local ampleness, and uniqueness by scheme and module full faithfulness. No
helper theorem or definition contains sorry. `lean.statement` is the verbatim
main signature. Definitions have explicit data, and all universes/variables
are bound with autoImplicit disabled.

Searches: the saved searches.jsonl records Mathlib grep
`polarized|ample.*descent|descent.*ample` (no hit), Loogle
`Scheme Modules IsAmple Etale descent` (unknown identifier), and LeanFinder
`effective etale descent polarized schemes compatible ample invertible modules`
(ordinary etale and affine-transition-limit hits, no matching theorem).
Repair searches repeated LeanFinder with `Effective descent of schemes with
relatively ample line bundles and a unique compatible global scheme and module
isomorphism`: eight affine-transition-limit hits, no match. Loogle for
`AlgebraicGeometry.Scheme.Modules.tensorPullbackCompositionIso` had no indexed
identifier; the exact recorded project declaration was found by rg and read
instead. rg for all eight new helper names and the item id across upstream
WeilConjectures and shared lean/Sheaf found no duplicate. The canonical tensor
pullback and composition comparison were reused rather than redefined.

Sources read directly in the local Stacks tree: spaces.tex theorem-presentation
(Tag 02WW), spaces-descent.tex definitions descent-datum-quasi-coherent and
descent-datum-effective-quasi-coherent and proposition-fpqc-descent-quasi-coherent
(Tag 04W8), lemma-descending-property-ample (Tag 0D3C), and descent.tex
lemma-fpqc-universal-effective-epimorphisms (Tag 023Q). Tag labels were checked
in tags/tags. They support the actual composition diagram, realization, and
full-faithfulness clauses, not the returned HEq formulation.

## Second reading by Q98

I re-read the unchanged natural statement against the final file, after the
initial dry run, without launching another agent (the launcher explicitly
forbids other agents in this session). This is a documented self-check; the
maintainer's independent review remains separate.

The saved packet still had the exact H3 fault: HEq of the three separately
pulled transitions. On identity covers of Spec Q with trivial lines, choose
chart scalars 1, 2, 6. The valid descent transitions have scalars 2, 3, 6 for
(1,2), (2,3), (1,3). The cocycle is 6 = 3*2, while the saved condition forced
2 = 3 = 6. The final equation passes this case because its two successive
isomorphisms are composed. Diagonal transitions are 1; reversing transitions
gives reciprocal scalars, also as required. This checks that lambda is neither
unrestricted nor made artificially equal across overlaps.

The saved conclusion allowed charts with unrelated transitions and compared
all pairs. I followed each final realization.theta and realization.lambda
path; both use D and exactly the stored charts. I followed the final global
pair-isomorphism line equation from P_(chartMap_i;schemeIso) M' to L_i: the
left route uses the pullback of its single global moduleIso followed by d's
chartLine, while the right uses equality transport and d's chartLine. There
is no HEq, no per-chart existential substitute, and uniqueness is for this
whole compatible structure. For a singleton identity cover, arbitrary scalar
chart comparisons determine the unique global scalar comparison rather than
forcing those scalar comparisons themselves to be equal.

Empty index set: jointlySurjective forces S to be empty, and Y can be empty;
uniqueness is then the unique empty-scheme and module comparison. Empty local
schemes and empty overlaps impose only their canonical equations. Empty affine
opens use the recorded ampleness predicate on the empty restriction. No
nonemptiness, finiteness, Noetherian, separatedness or flatness hypothesis was
added. Independent index universe v permits arbitrary-sized families; test
schemes use u and include the actual diagonal and triple overlaps. The original
statement and proof are unchanged; no STATEMENT-DISPUTED issue remains.

Additional returned defects repaired: all 17 helpers/theorem are recorded; the
missing Uj docstring is supplied; the module has source and main-definition
lists; the theorem proof docstring gives all six node steps; all lines are at
most 100 columns; the generic module moved to AlgebraicGeometry; all module
pullbacks now use tensorPullback; the non-public imports include the available
proof prerequisites. A direct citer audit found exactly
`lem-trf-polarized-fine-log-etale-descent` in stmt_deps/proof_deps. Its steps 1
and 5 need the compatible scheme/line realization and unique global comparison
provided here, so its use still holds. It was not edited.

Validation: scompile.py compiled the repaired file cleanly both as a sandbox
file and at its library module path. The final dry run and delivery repeat
per-file compilation and server preflight after the record and report updates.
