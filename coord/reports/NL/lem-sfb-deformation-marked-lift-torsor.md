## Worker report

The module `Sheaf.AlgebraicGeometry.DeformationMarkedLiftTorsor` states
`AlgebraicGeometry.ArtinDeformation.deformation_marked_lift_torsor` with one `sorry`.
All helper definitions contain real data; no auxiliary theorem is postponed.
The DAG copy changes only `lean`. No statement correction, new node, or dependency
module is needed. The helpers belong to the marked-lift notion introduced by this
item, and are listed in `lean.declarations` as the brief permits.

Source read: `literature/stacks-project/formal-defos.tex`, lines 5245–5465,
definition-lifts (06JE), remark-lift-bijections (06JH), lemma-free-transitive-action
(06JI), remark-free-transitive-action-functorial (06JJ). The source's difference
map and the specified markings are retained, rather than asserting an arbitrary
action or an arbitrary bijection of sets.

Hypothesis and clause correspondence:

* The field is `{k : Type u} [Field k]`. Both bases of `CofibredGroupoids k k`
  are k, so the test category is exactly Art_k = C_(k,k). No extra Noetherian or
  finite-type hypothesis is added: those instances for k over itself are inferred.
* `F : CofibredGroupoids.{u,v,w} k k` is the recorded groupoid-valued covariant
  pseudofunctor. `hpreF : IsPredeformation F` says its fibre at k is nonempty and
  every hom set there is a singleton, exactly equivalence to the terminal groupoid.
  `hrsF : IsRimSchlessinger F` is the recorded equivalence for the literal ring
  fibre product with a surjective leg. G has exactly the same hypotheses.
* `MarkedLift F p x = CostructuredArrow (push F p) x` has an object y over B
  with an arrow p_* y -> x. This arrow is an isomorphism since the fibre is a
  groupoid. Its morphism equation is p_* u followed by the second marking equals
  the first marking. All compatible arrows are isomorphisms. `markedLiftClasses`
  is the quotient by `isIsomorphicSetoid`, retaining exactly marked classes.
* `p : B ⟶ A`, `hs : Function.Surjective (map p)` render A' ->> A.
  `liftKernel p = LinearMap.ker (map p).toLinearMap` is the actual kernel I with
  its inherited k-module structure. `hk` states, element for element, that
  every b in the maximal ideal of B kills every i in the ring-map kernel.
  There is no one-dimensionality or nonzero-kernel hypothesis.
* The tangent set is the dependency's exact `tangentSet F`, namely π₀F(k[k]).
  `MarkedLiftTangentData` packages the vector structures and tensor equivalences
  from `artinRS_tangent_tensor`, with its pure-tensor transport, normalization
  over k, and naturality in every finite-dimensional parameter vector space.
  This is packaging of the recorded dependency's result, not a replacement
  tangent set or an arbitrarily assumed vector structure. The theorem provides
  these data existentially, so none is an extra hypothesis. The formulas uniquely
  normalize the operations: over k they prescribe scalar multiplication; for
  k² the two projections and the sum prescribe addition, and pure tensors span.
* The theorem also proves `FiniteDimensional k (liftKernel p)` rather than
  assuming it. It supplies `actF` and `actG` as `AddAction` structures on the
  exact marked-lift-class sets for every base object x. `∃! t, act.vadd t z = w`
  is freeness and transitivity. This implies the requested conditional conclusion
  when the set is nonempty, and also handles the empty case by its unique action.
* `IsCanonicalMarkedLiftAction` pins the action to the source: the existential
  test arrow g is required pointwise to send (a,b) to (residue(a),b-a), using the
  explicit real function `markedDifferenceValue`. This specification determines
  g uniquely, so it is not an unconstrained comparison map. For marked z,w it
  tests every gluing y whose comparison image is isomorphic to the triple
  (z,w,alpha_z followed by alpha_w inverse). Transport of y along g equals the
  normalized tensor class of t if and only if t translates z to w. (RS) supplies
  such y, so this characterization is nonvacuous for every pair of marked lifts.
  The use of any gluing and any representatives makes the action canonical.
* `DeformationMorphism F G` has fibre functors and base-change natural
  isomorphisms app_A followed by G(p) ≅ F(p) followed by app_B, together with
  explicit unit and composition coherence. NatIso already includes naturality
  in fibre arrows; the test category is locally discrete, so no further
  nonidentity 2-cell coherence is omitted. This is the component presentation of
  a pseudonatural transformation and allows independent universes v,w and v',w'.
* `markedLiftMorphismFunctor` is Mathlib's `CostructuredArrow.map₂` on that
  specified base-change isomorphism and identity at H(x); `markedLiftMorphism`
  is its actual quotient map. `deformationTangentMap` is the quotient map on
  the fibre functor over the dual numbers. The final conjunct provides a linear
  map dH equal pointwise to that quotient map, then says H(t +ᵥ z) equals
  `(TensorProduct.map dH LinearMap.id t) +ᵥ H(z)`, exactly the node's equation.
  H is universally quantified after both actions are chosen, so the action on
  F does not depend on a subsequently chosen H. The symmetric two-functor
  presentation simultaneously asserts the torsor statement for each: choosing
  G=F recovers the assertion for an arbitrary single F, without an added
  mathematical hypothesis. For a specified H these same actions are equivariant.

Dependency declarations read in full and used:

* `Mathlib.Algebra.Field.Defs`: `Field`, extending CommRing and DivisionRing.
* `Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory`:
  `TestCategory`, `ring`, `map`, `residue`, `CofibredGroupoids`, `fibre`, `push`,
  `IsPredeformation`, `IsRimSchlessinger`, `tangentSet`, `squareZeroAlgebra`,
  `squareZeroTest`, `fibreProductAlgebra`, `fibreProductTest`,
  `fibreProductFst`, `fibreProductSnd`, `fibreProduct_condition`, `comparison`,
  `unitIso`, `compIso`. These are used through the public tangent-tensor import.
* `Sheaf.AlgebraicGeometry.ArtinRSTangentTensor`: `squareZeroMap`,
  `isoClassesMap`, `artinRS_tangent_tensor`. The normalized tangent package
  records precisely the needed part of that theorem's existential conclusion.
* `Mathlib.LinearAlgebra.TensorProduct.Defs`, `.Basic`, `.Map`:
  `TensorProduct`, `TensorProduct.tmul`, `TensorProduct.lift`, `TensorProduct.ext'`,
  `TensorProduct.map` and `LinearMap.rTensor`; the actual statement uses
  `TensorProduct` and `TensorProduct.map`, with identity on the actual kernel.
* `Mathlib.CategoryTheory.Comma.StructuredArrow.Basic`: `CostructuredArrow`,
  its morphism equation, and `CostructuredArrow.map₂`. Mathlib supplies the exact
  marked lift category, so it is not reconstructed privately.
* `Mathlib.Algebra.Group.Action.Defs`: `AddAction`, its zero and addition laws.

Proof dependencies: the recorded test-category and tangent-tensor modules are
publicly imported because their constructions occur in the statement.
`lem-sfb-rs-marked-lift-pullback-bijections` has no Lean record or upstream audit
and consequently no module to import at this time. Its natural-language statement
and all seven proof steps were read; the main proof docstring cites its gluing
bijections. The present statement does not need its theorem as data: the canonical
action characterization uses the already recorded (RS) comparison directly.

Edge cases checked: I=0 (identity extension allowed; no nonzero assumption), A=k,
empty lift sets (the unique empty action and vacuous pair condition), tangent
space zero, tangent space infinite-dimensional, nontrivial automorphisms (the
costructured-arrow marking prevents their accidental quotient), characteristic 2
(the difference formula and triple cocycle use addition/subtraction, never divide
by 2), and source and target groupoid fibres in different universes. Parameter
spaces and the kernel live in Type u, as do the test algebras; all fibre universes
are bound explicitly and `autoImplicit` is false.

Searches performed for the statement and helper notions:

* `msearch.py ... leanfinder "For a deformation groupoid satisfying Rim Schlessinger,
  marked lifts across an Artinian square zero extension form a functorial tangent
  space torsor"`: eight hits about derivationToSquareZeroEquivLift,
  Algebra.Extension.H1Cotangent.map and infinitesimal cotangent extensions;
  none concerns arbitrary deformation pseudofunctors or marked lift classes.
* `msearch.py ... leansearch "The tangent space tensor the kernel acts freely and
  transitively on marked lifts of a deformation groupoid"`: AddTorsor and
  manifold tangent spaces; no deformation theorem. Mathlib's action interface
  is reused as AddAction plus explicit unique translation.
* `msearch.py ... loogle "AddTorsor, Pseudofunctor.StrongTrans"`: zero hits
  (the service did not recognize Pseudofunctor.StrongTrans). Read the local
  Mathlib definition directly: it requires a common Cat universe for both
  pseudofunctors. A compiler check confirmed this limitation. The componentwise
  coherence definition avoids excluding different fibre universes.
* `msearch.py ... grep "Schlessinger|marked.*lift|deformation.*torsor"`: zero hits.
* `rg -n 'Schlessinger|marked.*lift|deformation.*torsor' lean/WeilConjectures`
  found only unrelated occurrences of marked geometric lifts; direct
  `grep -rn 'lem-sfb-deformation-marked-lift-torsor' lean/WeilConjectures` had no hit.
* Searched `lean/Sheaf/AlgebraicGeometry/Artin*.lean`, then all `lean/Sheaf`,
  `lean/WeilConjectures`, Mathlib AlgebraicGeometry and CategoryTheory, and
  `dag/lean_names_upstream.json` for retained helper names: no duplicate.
  Other marked scheme/curve lifts concern different notions; the abstract
  marked pullback-bijection DAG node is an unstated theorem, not a duplicate
  definition module. No private copy of its theorem is made here.

Validation: only the prescribed scompile.py wrapper was used. The final source
compiled in sandbox and module mode without errors or warnings. No global build
or direct repository edit or git command was run. No disputed statement found.

## Second reading by NL

Author's separate second pass (the dispatcher expressly forbids starting another
agent; the maintainer supplies the independent review). Reopened the node,
source Tags 06JE/06JI/06JJ, dependency signatures, and the entire final module.
The field, Art_k, terminal fibre and (RS) hypotheses correspond exactly to the
recorded declarations. The extension uses a surjection with annihilated actual
kernel, not the stricter one-dimensional IsSmallExtension. The marking equation
is the CostructuredArrow equation and hence has the correct composition direction.
The canonical-action predicate uses alpha_z followed by alpha_w inverse, so the
ring difference is b-a and `t +ᵥ z = w` has the source's sign. The last equation
uses the same coherent H for the marked map and dH, and the tensor factor I is
unchanged. Independent groupoid universes are retained. The tensor vector data
are supplied in the conclusion, not silently assumed. No conclusion or source
hypothesis is missing, and no new object is selected from an unspecified mere
existence theorem. The only sorry is the requested theorem. The preliminary
extra algebra-law lemma was removed: the theorem now existentially bundles g
with its exact pointwise formula, so no unmatched postponed theorem remains.
