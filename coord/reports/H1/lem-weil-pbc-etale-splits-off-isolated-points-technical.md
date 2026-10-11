## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleSplitsOffIsolatedPoints` states
`AlgebraicGeometry.exists_etale_splits_off_isolated_points`, with exactly one theorem and
its proof `sorry`. No new definitions, new nodes, dependency modules or statement corrections
are needed. All variables and the universe `u` are explicitly bound.

Source checked: Stacks Project, More on Morphisms, Lemma 37.41.4, Tag 02LN,
https://stacks.math.columbia.edu/tag/02LN . The local literature checkout is absent, so the
source statement and proof were read on the Stacks site. The node agrees with the source,
using points of X corresponding to points of the fibre as its source record explains.

Hypotheses and conclusions, clause by clause:

- Schemes X and S and their morphism: `{X S : Scheme.{u}} (f : X ⟶ S)`.
- Locally of finite type and separated: `[LocallyOfFiniteType f] [IsSeparated f]`.
- The base point, nonnegative integer and the n points: `(s : S) (n : ℕ)
  (x : Fin n → X)`. `Function.Injective x` means pairwise distinctness.
- All points lie over s: `h_over : ∀ i : Fin n, f (x i) = s`.
- The unique corresponding fibre point is isolated: `h_isolated` gives a point
  `ξ : f.fiber s` with `f.fiberι s ξ = x i` and `IsOpen ({ξ} : Set (f.fiber s))`.
  Uniqueness is already inherent in the projection's embedding/homeomorphism, not an
  omitted extra assumption. This avoids equality transport in the statement.
- Elementary étale neighbourhood: the conclusion quantifies `U : Scheme.{u}`, `φ : U ⟶ S`
  and `t : U`, requiring `Etale φ`, `φ t = s` and `IsIso (φ.residueFieldMap t)`.
  The distinguished point is named t to keep the universe name u separate. The induced
  map has source κ(φ t), identified with κ(s) by the displayed equality.
- Base change in the node's order U ×_S X: `pullback φ f`. Its q is `pullback.fst φ f`
  and its p is `pullback.snd φ f`.
- Open subschemes: `W : (pullback φ f).Opens` and `V : Fin n → (pullback φ f).Opens`.
  `Disjoint W (V i)` and `i ≠ j → Disjoint (V i) (V j)` give all pairwise
  disjointness. `W ⊔ (⨆ i : Fin n, V i) = ⊤` gives coverage. Because the family is
  finite, each complement is a union of the other opens and is open: all pieces are
  closed as well. Thus the asserted open-and-closed decomposition is fully expressed.
- (i) Each piece is finite over U: `IsFinite ((V i).ι ≫ pullback.fst φ f)`.
- (ii) Exactly one point over t in V i: `∃ v : V i`, with
  `pullback.fst φ f v.1 = t` and
  `∀ v' : V i, pullback.fst φ f v'.1 = t → v' = v`.
- (iii) Its image is x i: `pullback.snd φ f v.1 = x i`; the induced residue-field
  map is an isomorphism: `IsIso ((pullback.snd φ f).residueFieldMap v.1)`.
  This is the induced map of the projection on the ambient pullback. The residue field
  at the corresponding point of the open subscheme is canonically the same field.
- (iv) `∀ w : W, pullback.fst φ f w.1 = t → ∀ i : Fin n,
  pullback.snd φ f w.1 ≠ x i` excludes all specified images in the distinguished
  fibre of W.

Dependency declarations read and used:

- def-pc-scheme: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme` (transitively imported).
- def-weil-finite-type-morphism: `AlgebraicGeometry.LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` (via Fiber).
- def-weil-pbc-scheme-conventions is a convention record, not a separate notion;
  its separated clause is `AlgebraicGeometry.IsSeparated`,
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`.
- def-pc-scheme-fibre: `Scheme.Hom.fiber`, `Scheme.Hom.fiberι`, and the
  `Scheme.Hom.fiberHomeo` identification, `Mathlib.AlgebraicGeometry.Fiber`.
- def-weil-etale-morphism: `AlgebraicGeometry.Etale`,
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- def-weil-residue-field: `Scheme.residueField`, `Scheme.Hom.residueFieldMap`,
  `Mathlib.AlgebraicGeometry.ResidueField` (via Fiber).
- def-pc-fibre-product: `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` (transitive).
- def-weil-finite-integral-morphism: `AlgebraicGeometry.IsFinite`,
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`.

Edge cases checked before writing: n = 0 is included, with no points or isolation assumptions;
V is the empty family, all indexed conclusions are vacuous and coverage forces W = ⊤.
Use U = S with the identity neighbourhood. Empty X is allowed when n = 0; when n > 0
there is no x family. Empty S supplies no base point, as in the mathematical statement.
Repeated points are excluded exactly by injectivity. Nonclosed isolated fibre points are
not silently ruled out: the hypothesis is openness of the singleton, not a separate
closedness assumption. No affine, Noetherian, quasi-compact, positive-n or characteristic
assumption is imposed. Scheme universe u is arbitrary.

Searches made (msearch.py, group H1 and this item):

- LeanFinder query: “elementary etale neighbourhood splits off finite disjoint open closed
  pieces at several isolated fibre points”. Eight hits: etale loci, etale field-algebra
  decompositions, and the ring-level one-prime finite-algebra splitting theorem
  `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`; no matching scheme statement.
- Loogle query: `AlgebraicGeometry.exists_etale_isCompl_of_quasiFiniteAt`. One hit in
  `Mathlib.AlgebraicGeometry.ZariskisMainTheorem`. Full statement read: one point only,
  no trivial residue extension at a chosen base point, no singleton fibre or clause (iv).
  It is strictly weaker and its source explicitly says it is weaker than Stacks 02LN.
- Mathlib grep query: `02LN|exists_etale_isCompl|splits.*isolated` in AlgebraicGeometry.
  Three hits, all for that weaker Zariski-main theorem or its use.
- LeanSearch query: “separated locally finite type scheme morphism elementary etale
  neighbourhood disjoint finite pieces isolated fibre points”. Service unavailable:
  Internal Server Error; no result or mathematical verdict assigned to this service.
- rg query `isolated|splits_off|02LN|exists_etale_isCompl` over the project's
  `lean/Sheaf` and upstream `WeilConjectures`: unrelated isolated-point mentions and
  ring-level material, no matching theorem. Upstream grep for this node's exact id
  found nothing.
- rg for `exists_etale_splits_off_isolated_points` in `dag/lean_names_upstream.json`,
  Mathlib, upstream `WeilConjectures` and `lean/Sheaf` found no collision.

The docstring carries all five proof steps and their named dependencies. No node fault or
STATEMENT-DISPUTED issue was found. Server compile via scompile.py succeeded in 1.8 seconds,
exit code 0, with no warnings. The independent second reading remains for the second worker.

## Second reading by H1

I independently read the sandbox node, its Lean module, all eight statement-dependency
nodes and the Mathlib declarations they record. The node has no statement_change, new
nodes or dependency modules. No mismatch was found; the Lean and node are unchanged.

Source: [Stacks 02LN](https://stacks.math.columbia.edu/tag/02LN), and the actual
[more-morphisms.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/more-morphisms.tex)
source, label lemma-etale-splits-off-quasi-finite-part-technical (currently lines
11115–11150), together with the introduction to section-etale-localization (10931–10954).
The section assumes no additional global finiteness, base field or Noetherian hypothesis.
The shifted line numbers do not change the label or statement. The source's fibre points
are transported to X by the homeomorphism specified in the node.

Object/hypothesis/conclusion checklist, written from the node before comparison:

- Schemes X, S and f : X → S: `{X S : Scheme.{u}} (f : X ⟶ S)`. PASS.
  Scheme.lean:42 gives locally ringed spaces locally isomorphic to affine spectra.
- f locally of finite type: `[LocallyOfFiniteType f]`. PASS. FiniteType.lean:43
  gives finite-type ring maps on affine pairs, equivalent to the dependency's cover form.
- f separated: `[IsSeparated f]`. PASS. Separated.lean:44 means its diagonal is
  a closed immersion. The conventions dependency collects this notion, not a new one.
- s ∈ S, n ≥ 0, n points in X: `(s : S) (n : ℕ) (x : Fin n → X)`. PASS.
- Pairwise distinct: `(h_distinct : Function.Injective x)`. PASS.
- Points lie over s: `(h_over : ∀ i : Fin n, f (x i) = s)`. PASS.
- Scheme-theoretic fibre, projection and isolated corresponding points:
  `h_isolated : ∀ i, ∃ ξ : f.fiber s, f.fiberι s ξ = x i ∧ IsOpen ({ξ} : Set _)`.
  PASS. Fiber.lean:38/41 are exactly the recorded fibre and projection; fiberHomeo
  at line 103 identifies it with f⁻¹{s}. Thus existence identifies the unique fibre
  point; the omitted explicit uniqueness follows from the embedding and adds no premise.
- Elementary neighbourhood U, φ, t above s with trivial residue extension:
  `∃ (U : Scheme.{u}) (φ : U ⟶ S) (t : U), Etale φ ∧ φ t = s ∧
  IsIso (φ.residueFieldMap t) ∧ …`. PASS. Etale.lean:41 defines affine-local étaleness;
  ResidueField.lean:45/123 give the actual stalk residue field and induced map
  κ(φ(t)) → κ(t). Equality φ(t) = s supplies exactly the source's identification.
- X_U = U ×_S X, q and p: `pullback φ f`, `pullback.fst φ f`,
  `pullback.snd φ f`. PASS. HasPullback.lean:95/111/115 record the universal pullback
  and its correctly ordered projections; no private product or chosen base change.
- Open subschemes W and V_i: `W : (pullback φ f).Opens` and
  `V : Fin n → (pullback φ f).Opens`. PASS. Restrict.lean:45/52 identify Opens with
  restricted schemes and their canonical open immersions.
- Pairwise disjoint decomposition covering X_U: `∀ i, Disjoint W (V i)`,
  `∀ i j, i ≠ j → Disjoint (V i) (V j)`, and `W ⊔ (⨆ i, V i) = ⊤`. PASS.
  W has open complement ⋃ᵢ V_i; each V_i has open complement W ∪ ⋃_{j≠i} V_j.
  These follow as set equalities from coverage/disjointness. Hence every piece is closed,
  with exactly the open-and-closed decomposition of the node, not a weaker conclusion.
- (i) Finite V_i → U: `∀ i, IsFinite ((V i).ι ≫ pullback.fst φ f)`. PASS.
  Finite.lean:39 defines affine inverse images and finite maps on affine sections.
- (ii) Unique point of V_i over t: `∀ i, ∃ v : V i, q v.1 = t ∧
  (∀ v' : V i, q v'.1 = t → v' = v) ∧ …`. PASS. Fibre-point homeomorphisms
  identify this set-theoretic preimage with the topological scheme fibre.
- (iii) Image x_i and induced residue isomorphism: `p v.1 = x i ∧
  IsIso (p.residueFieldMap v.1)` for that same v. PASS. This is the ambient projection;
  the open inclusion has an isomorphism on residue fields (ResidueField.lean:177).
  By residueFieldMap_comp, the induced map for the restricted projection is its composite
  with this isomorphism, so the assertion is exactly κ(x_i) → κ(v_i) being an isomorphism.
- (iv) No point of W above t maps to a specified point:
  `∀ w : W, q w.1 = t → ∀ i : Fin n, p w.1 ≠ x i`. PASS.
  This is exactly nonmembership in the finite set of the x_i, with no restriction on
  W away from the distinguished fibre.

Quantifiers: f, s, n and x precede all neighbourhood choices; one common U, φ, t,
W and family V serve all points; each selected v_i satisfies both uniqueness and
clause (iii). No extra instance is required beyond the two morphism hypotheses.
Universe u is explicitly declared and arbitrary; all schemes lie in the same arbitrary
scheme category, including U and the canonical pullback. No variable is unbound.

Edge cases: Fin 0 is empty, so indexed hypotheses and clauses are vacuous and coverage
forces W = ⊤; the identity neighbourhood works. Empty X is permitted for n = 0,
while n > 0 cannot supply x. Empty S cannot supply s. No nonempty scheme, positive n,
closedness of the chosen points, field characteristic, affine, quasi-compact or Noetherian
assumption is introduced. No additive zero object is involved in this scheme statement.

Independent H4 searches, through msearch.py under this item:

- LeanFinder: “separated scheme morphism finite clopen decomposition elementary etale
  neighborhood with singleton fibers”. Eight hits, on étale loci, étale morphisms and
  field-algebra decompositions; no matching scheme statement.
- Loogle: `"exists_etale"`. Ten hits. I opened
  AlgebraicGeometry.exists_etale_isCompl_of_quasiFiniteAt in ZariskisMainTheorem.lean:49:
  it selects one point, requires only s in the range of U → S, and has no elementary
  residue-field condition, singleton assertion or W-fibre exclusion. It is not this node.
  I also opened Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq
  in RingTheory/Etale/QuasiFinite.lean:613: it assumes Module.Finite R S and is a
  ring-level idempotent decomposition, not this locally finite type scheme statement.
  An earlier malformed Loogle query `"etale" "exists"` returned a parser error;
  it was replaced by the successful query above and is not evidence of absence.
- LeanSearch: “finite clopen pieces of a scheme after elementary etale base change
  at distinct isolated fiber points”. Internal Server Error; recorded as unavailable,
  not a mathematical no-match verdict.
- rg with independent terms `elementary|singleton|isCompl|02LN` in the Mathlib Zariski
  main module and `etale.*(split|finite.*point)|splits_off|02LN|elementary.*neigh`
  across WeilConjectures and repository lean/Sheaf found only the weaker theorem and
  upstream ring-level PropertyC/FiniteSplitting material. Exact-name searches in Mathlib,
  WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json found no collision.

H5/H6/H8/H9: one named theorem with sole proof `sorry`, no definition data or extra
proved declaration. The source and blueprint id occur in both docstrings; the theorem
proof narrative includes all five node steps (empty case/02LL; proper finite pieces in a
separated base change; removal of closed intersection images and persistence; complementary
W; fibre-product residue tensor uniqueness for (iv)). Each import supplies a notion used
in the statement; topic, namespace and 100-character lines meet the contract.

Validation: scompile.py with the absolute sandbox module path compiled on the server in
1.8 seconds, exit code 0, no warnings. An initial call with a path relative to the read-only
repository failed to locate the sandbox file; rerunning with its absolute path succeeded.
A direct extraction verified lean.statement is verbatim equal to the theorem signature
up to `:=`, and all lines have at most 100 characters. No repair to correct Lean was needed;
this second reading adds only this report section and its independent search evidence.
