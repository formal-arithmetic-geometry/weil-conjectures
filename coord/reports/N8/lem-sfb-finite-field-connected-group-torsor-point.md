## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteFieldConnectedGroupTorsorPoint` states
`AlgebraicGeometry.finiteField_connectedGroup_torsor_nonempty`, with its entire proof
postponed by `sorry`. There are no definitions or auxiliary theorems and no node corrections.

Source read: Milne, Algebraic Groups (2017), Definition 2.66 and Proposition 2.69,
printed p.60; Proposition 3.50, p.80; Corollary 17.98 and its proof, p.383.
The definition is the right-action torsor definition in the node. Corollary 17.98
is the connected-group Lang theorem, and Proposition 3.50 identifies smooth-group
torsors with the stated cohomology classes. The module docstring contains the
node's four-step direct proof, including the factor order for the right action
and the final affine-open descent of the Frobenius-fixed point.

Hypothesis and conclusion correspondence:

- A finite field k: `(k : Type u) [Field k] [Finite k]`.
- A k-group scheme H: `(H : Over (Spec (.of k))) [GrpObj H]`. The group-object
  structure contains multiplication, identity, inverse and their diagram laws.
- Affine H: `[IsAffine H.left]`.
- Smooth H over k: `[Smooth H.hom]`.
- Geometrically connected H: `[GeometricallyConnected H.hom]`. Mathlib defines
  this using `ConnectedSpace` on every field-valued base change, including
  nonemptiness, exactly as required; plain connectedness would not be substituted.
- H of finite type: `[LocallyOfFiniteType H.hom] [QuasiCompact H.hom]`, precisely
  the two conditions in the recorded finite-type dependency.
- An arbitrary k-scheme Y: `(Y : Over (Spec (.of k)))`.
- Flat, surjective, locally finitely presented structure map:
  `[Flat Y.hom] [Surjective Y.hom] [LocallyOfFinitePresentation Y.hom]`.
- Right action over k: `(act : Y ⊗ H ⟶ Y)`. In the scheme over-category,
  `(Y ⊗ H).left` is definitionally `Limits.pullback Y.hom H.hom`.
- Unit identity: `lift (𝟙 Y) (toUnit Y ≫ MonObj.one (X := H)) ≫ act = 𝟙 Y`,
  which is the scheme-map equation y e = y.
- Associativity: `(act ▷ H) ≫ act =
  (α_ Y H H).hom ≫ (Y ◁ MonObj.mul (X := H)) ≫ act`, both maps from
  `(Y ⊗ H) ⊗ H` to Y, respectively (y h1) h2 and y (h1 h2).
- The specified torsor map is an isomorphism: `[IsIso (lift (fst Y H) act)]`.
  The underlying map is exactly the pullback lift with components the first
  projection and act, hence `(y,h) ↦ (y,yh)`. An isomorphism here is an isomorphism
  of k-schemes. Conversely a scheme isomorphism of this over-morphism has an
  inverse over k, so the hypothesis is no stronger than the node's condition.
- Nonempty rational points: `Nonempty (Over.mk (𝟙 (Spec (.of k))) ⟶ Y)`.
  The source over-object is exactly Spec k over itself, so this is Hom_k(Spec k,Y).
- No reductivity, commutativity or rational basepoint assumptions occur.
  Y is not required to be affine, quasi-compact, separated or finite type.

Dependency declarations used (full signatures and their docstrings were read):

- `Mathlib.Algebra.Field.Defs`: `Field` (via scheme and morphism imports).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`; the specialization
  to `Over (Spec (.of k))` was checked against the terminology in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, used by
  `Mathlib.AlgebraicGeometry.Geometrically.Connected`'s
  `AlgebraicGeometry.GeometricallyConnected`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Spec`, scheme Hom.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, its projections and universal lift, used
  through `Mathlib.CategoryTheory.Monoidal.Cartesian.Over` and
  `Mathlib.AlgebraicGeometry.Pullbacks`. Read `Over.tensorObj_left`, `lift_left`,
  `fst_left`, `tensorUnit_left`, `tensorUnit_hom`: these identify every Cartesian
  tensor expression above with the dependency's actual chosen fibre product.
- Surjectivity uses `AlgebraicGeometry.Surjective` in
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`.

Proof dependencies with recorded modules are imported privately: algebraic closure,
base-change images, finite-type base change and Jacobson spaces (FiniteType already
public for the statement), closed-point residue fields, finite fields, Frobenius and
`Sheaf.FieldTheory.UniqueSubfieldOfClosure`. The Lang-surjectivity node has neither
a Lean record nor a Mathlib match in the read snapshot, so it has no module to import;
it is named in the proof docstring and is needed only for the eventual proof.

Edge cases checked before writing: the empty Y has a uniquely defined action and
can satisfy the empty torsor-map condition, but fails surjectivity over the nonempty
spectrum of a field. Thus no rational point was assumed in a torsor structure.
The trivial group is allowed and its torsors give the expected conclusion.
Noncommutative groups are allowed; the associativity diagram and proof preserve
factor order. Finite fields of every characteristic, including F_2, are allowed.
Disconnected groups are excluded exactly by geometric connectedness; this matches
Milne's counterexample to the disconnected variant. No test-algebra quantifier
with a too-small independent universe occurs. The common universe `u` covers
arbitrary sizes by enlarging the finite base field together with the schemes.

Searches actually performed using the prescribed msearch.py wrapper:

- LeanFinder: "Every torsor under a smooth geometrically connected affine algebraic
  group over a finite field has a rational point". Eight hits, chiefly affine-space
  surjectivity, Ax-Grothendieck, Galois-category connectedness and abstract additive
  torsors; none states the scheme-torsor result.
- Loogle: "GrpObj, IsIso, Nonempty". No hits; the service reported unknown identifier
  GrpObj. This is not evidence of absence; direct source inspection supplied the API.
- Mathlib grep: `Lang.*[Tt]heorem|langMap|[Tt]orsor`, subdirectory AlgebraicGeometry:
  no hits.
- LeanSearch: "Lang theorem torsors over finite fields connected smooth affine group
  rational point". Eight hits in abstract additive torsor theory and affine spaces.
  In particular AddTorsor.nonempty assumes nonemptiness as structure data and cannot
  provide this theorem.
- rg of both `lean/WeilConjectures` and `lean/Sheaf` for
  `langMap|[Ll]ang_[^ ]*|finite_field.*torsor|` followed by this node's id: no hits.
- rg of Mathlib, WeilConjectures, Sheaf and `dag/lean_names_upstream.json` for the
  full proposed declaration's final name: no hits.

## Second reading by N8

A separate second pass reread the original node, the final signature and the cited
source excerpts. The nine statement dependencies supply the existing notions;
no dependency needs a replacement interface. Checked all field/group hypotheses,
that finite type has BOTH local finite type and quasi-compactness, and that
geometric connectedness includes nonemptiness on field-valued base changes.
Unfolding the documented Over Cartesian structure gives exactly Y ×_k H and
Y ×_k Y. The unit section is composed with Y's structure morphism, not an arbitrary
section. The associator has source (Y ×_k H) ×_k H and target Y ×_k (H ×_k H), so
its displayed equation is the right-action associativity law. The map declared
IsIso has precisely components (first projection, act). Finally the conclusion's
Over identity object gives a k-morphism, rather than an unstructured scheme
morphism or a point over an extension. No missing or extra clause was found and
no statement change was made. This is a self-contained second pass by the dispatched
worker; the delivery receives the maintainer's separate independent review as
specified by the dispatch brief.
