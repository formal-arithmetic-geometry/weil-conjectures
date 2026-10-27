## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteConstantComponentQuotient` states
`AlgebraicGeometry.GrpObj.exists_finiteConstantComponentQuotient`, with its only proof
`sorry`. It introduces no definitions, auxiliary theorems, new nodes, dependency repairs,
or changes to the informal statement. All universes and variables are explicit, with
`set_option autoImplicit false`.

Source read: Milne, Algebraic Groups (2017), Section 2(g), printed pp.51-52,
construction before Proposition 2.37, Proposition 2.37(b),(d), and Remark 2.39(a).
The source identifies the kernel with the identity component, and the topological
fibres with all connected components. Its finite etale component group becomes constant
over the algebraically closed field. Its proof and our node's five-step construction
are recorded in the theorem docstring, retaining the original nonreduced component
subschemes throughout.

Hypotheses and conclusion, clause by clause:

- The algebraically closed field k is `(k : Type u) [Field k] [IsAlgClosed k]`.
- A k-group scheme is `(G : Over (Spec (.of k))) [GrpObj G]` using the recorded
  def-sc-group-scheme interface, with its actual group-object diagrams.
- Affineness is `[IsAffine G.left]`; finite type is
  `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`, exactly the recorded
  def-weil-finite-type-morphism convention.
- The finite abstract group is `P : GrpCat.{u}` with `Finite P`. The bundle carries a
  general group, not a commutative group. A finite component group can be represented
  in the same universe as the scheme, so this choice excludes no group size here.
- The quotient target is `Q : Grp (Over (Spec (.of k)))`. Its field `Q.X` is the
  underlying k-scheme, and its `grp` field supplies the genuine group-scheme structure.
- The inclusions `j : P → (𝟙_ (Over (Spec (.of k))) ⟶ Q.X)` and
  `Nonempty (IsColimit (Cofan.mk Q.X j))` say exactly that Q is the coproduct of
  P copies of the terminal k-scheme, Spec k. Forgetting from Over to Scheme creates
  this coproduct, so the summands are the usual disjoint open copies of Spec k.
- The operations induced by P are `j 1 = 1`,
  `∀ a b, j (a * b) = j a * j b`, and `∀ a, j a⁻¹ = (j a)⁻¹`.
  The Hom group law is the existing group-object law, hence these are equalities of
  k-scheme morphisms from Spec k. They specify multiplication on every pair of
  summands of Q ×_k Q (each such summand is Spec k), inverse on each summand, and
  the unit section. This determines the actual scheme operations, not merely a
  condition on a chosen arbitrary collection of rational points.
- The over-category isomorphism
  `e : Q.X ≅ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (P → k))))`
  identifies Q over k with Spec(k^P), with the diagonal structure homomorphism.
  The equation `(j a).left ≫ e.hom.left = Spec.map
  (CommRingCat.ofHom (Pi.evalRingHom (fun _ : P ↦ k) a))` identifies each labelled
  summand with the canonical coordinate-evaluation inclusion. Thus neither the
  underlying constant scheme nor its labels are unspecified.
- The stated affine finite-type property of the constant target is
  `IsAffine Q.X.left ∧ LocallyOfFiniteType Q.X.hom ∧ QuasiCompact Q.X.hom`.
- The k-group-scheme homomorphism is `c : G ⟶ Q.X` with `IsMonHom c`, the recorded
  group-scheme-homomorphism interface. Surjectivity is `Surjective c.left` on spaces.
- For each a, its singleton point in Q is written `Set.range (j a).left`, since
  Spec k has exactly one point. Therefore `c.left ⁻¹' Set.range (j a).left` is
  exactly the fibre over that label, with no imposed reduced scheme structure.
- Nonemptiness of every labelled fibre is the `.Nonempty` conjunct. For every
  point x in that fibre, the next equality says it equals `connectedComponent x`,
  Mathlib's maximal connected subset containing x. Conversely every point of G
  maps to a unique summand because j is the coproduct cocone, so every component
  occurs among these fibres. This is precisely 'exactly the connected components'.
- The final equality identifies the fibre over `j 1` with
  `connectedComponent (GrpObj.onePoint G)`, the identity component.
- There is no smoothness, reducedness, commutativity, or characteristic-zero binder.

Dependency declarations read and used:

- def-weil-field: Mathlib.Algebra.Field.Defs, `Field` (line 180).
- def-weil-algebraic-closure: Mathlib.FieldTheory.IsAlgClosed.Basic,
  `IsAlgClosed` (line 62), the relevant part of the recorded closure terminology.
- def-sc-group-scheme: Mathlib.CategoryTheory.Monoidal.Grp,
  `CategoryTheory.GrpObj`, `CategoryTheory.Grp`; Mathlib.CategoryTheory.Monoidal.Mon,
  `CategoryTheory.IsMonHom` (line 213). The full group-object and homomorphism
  signatures/docstrings were read, as was the explanatory module docstring in
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- def-weil-finite-type-morphism: Mathlib.AlgebraicGeometry.Morphisms.FiniteType,
  `AlgebraicGeometry.LocallyOfFiniteType` (line 43), and
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact, `AlgebraicGeometry.QuasiCompact`
  (line 43). These are publicly available through GroupScheme.Basic.
- def-weil-affine-spectrum: Mathlib.AlgebraicGeometry.Scheme,
  `AlgebraicGeometry.Spec` (line 470), `AlgebraicGeometry.Spec.map` (line 479).
- def-weil-connected-scheme: Mathlib.Topology.Connected.Basic, `ConnectedSpace`
  (line 705) and `connectedComponent` (line 495), whose docstring explicitly says
  maximal connected set containing the point. The theorem uses the latter for
  the node's maximal connected subsets. These are publicly available through Basic.
- WeilConjectures.AlgebraicGeometry.GroupScheme.Basic,
  `AlgebraicGeometry.GrpObj.onePoint` supplies the original identity point.
- Mathlib.Algebra.Category.Grp.Basic, `GrpCat`; Mathlib.AlgebraicGeometry.Limits,
  the coproduct API and `sigmaSpec`/`ι_sigmaSpec`/the finite IsIso instance;
  Mathlib.Algebra.Ring.Pi, `Pi.evalRingHom` supplies the product projections.

Proof imports retain the already stated proof dependencies:
Sheaf.AlgebraicGeometry.GroupNeutralComponentTranslates,
Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent,
Sheaf.AlgebraicGeometry.IrreducibleProductOverField,
Mathlib.AlgebraicGeometry.Geometrically.Integral,
Mathlib.AlgebraicGeometry.Gluing, and Mathlib.AlgebraicGeometry.Pullbacks.
The spectrum/coproduct and open-immersion APIs are also supplied by the imports.
No proof import was omitted for a cycle.

Edge cases checked before finalizing the signature:

- A group scheme over a field is nonempty because it has a unit. An empty component
  group is impossible because P is a group, rather than merely a finite type.
- For connected G, P is the one-element group and c is the structure map to Spec k;
  every fibre clause then describes the whole connected underlying space.
- For a finite constant group scheme, including a nonabelian one, take P to be its
  group of labels and c the identity. The components are singleton summands.
- In positive characteristic the infinitesimal connected example μ_p has trivial P,
  while its nilpotents remain in G and in its identity component. No reduction,
  reducedness, smoothness or etaleness hypothesis has been smuggled into G.
- Finite groups of order divisible by the characteristic are permitted: the constant
  scheme is still a disjoint union of copies of Spec k. No order-invertibility condition.

Searches for an existing statement/notion:

- msearch LeanFinder: 'An affine algebraic group over an algebraically closed field has
  a finite constant quotient group scheme whose fibres are its connected components'.
  Eight hits on Galois-category decompositions, abstract profinite quotients, and affine
  finite discrete schemes; none is the component quotient of a group scheme.
- msearch Loogle: `"GrpObj", "ConnectedComponents"`: zero hits.
- msearch grep: `(componentGroup|componentQuotient|constantGroupScheme)` in
  Mathlib/AlgebraicGeometry: zero hits.
- msearch LeanSearch: 'finite constant component group quotient of an affine group
  scheme over an algebraically closed field': eight abstract finite-group quotient hits;
  none states the scheme quotient or connected-component fibres.
- rg of lean/WeilConjectures, lean/Sheaf and Mathlib/AlgebraicGeometry for
  `finiteConstantComponentQuotient|finite_constant_component|componentQuotient|componentGroup`:
  only unrelated TraceFormula/derived-category component quotients. The chosen name is new.
- rg of lean/WeilConjectures for the item id: no existing declaration.
- Searches for constant group constructions found
  WeilConjectures.AlgebraicGeometry.ConstantGroupScheme. Its entire source was read.
  It supplies the underlying coproduct but its multiplication requires AddCommGroup;
  it does not supply a general noncommutative GrpObj structure. The DAG node
  def-weil-pbc-constant-group-scheme explicitly only specifies an abelian group and
  does not assert the group-scheme axioms. We introduce no copy: the result uses
  Mathlib's existing Grp, coproduct universal property, and coordinate-evaluation maps
  directly. This follows the existing coproduct-plus-operation-equations encoding
  in Sheaf.AlgebraicGeometry.ActionGroupoidQuotientCriterion.

Validation: scompile.py compiled the module both as a sandbox and under its library
module name, without errors or unexpected warnings. No statement fault or dispute found.

## Second reading by Q29

This is the author's second reading; the maintainer provides the independent review
under the direct-delivery brief. I reopened the node statement and the module and checked
both directions of the component description: nonempty fibres identify with the maximal
connected set of each contained point, while the coproduct property ensures every point
lies in a labelled fibre. The last equality uses the group identity label and the original
unit point of G. I checked that Q is a group object over the same base, that the spectrum
isomorphism is over k and sends each j to the prescribed evaluation map, and that the
multiplication and inverse equations determine scheme morphisms on all the coproduct
pieces. This avoids the erroneous shortcut of assuming P abelian to use the existing
constant-group multiplication module. The field, affine, finite-type and general-group
hypotheses all match; positive characteristic and nonreduced cases remain allowed.
No mismatch was found and no informal statement or dependency record was changed.
