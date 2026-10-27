## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.ContractingLineTorsorRigidity`
states `AlgebraicGeometry.exists_equivariantRightTorsorIso_contractingLine` with
one `sorry` and no proved theorem. Its docstring gives all five steps of the
node's proof. The definition module contains real data and no `sorry`.
The original mathematical statement and proof have not changed.

Source read: the author-hosted Alper--Halpern-Leistner--Heinloth paper,
https://sites.math.washington.edu/~jarod/papers/iwahori.pdf, Section 2 Claim 3
(printed p.3) and Lemma 3.6, implication (2) implies (1) (printed p.6).
The former supplies the graded infinitesimal lifting and algebraization argument;
the latter compares a torsor on the contracting line with its fibre at zero.
The node's weight +1 convention follows by interchanging s and t.

Hypothesis and clause correspondence:

- The field is `(k : Type u) [Field k]`, with an explicitly bound universe.
- The k-group is `H : Grp (Over (Spec (.of k)))`, the bundled form of `GrpObj`
  recorded by def-sc-group-scheme. Multiplication, unit and inverse obey the
  usual internal group diagrams. No connectedness or reductivity is required.
- Smoothness is `[Smooth H.X.hom]`; affineness is `[IsAffine H.X.left]`;
  finite type is `[LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]`,
  exactly the conjunction recorded by def-weil-finite-type-morphism.
- The multiplicative group is `Grp.mk (StandardGroupSchemes.multiplicative k)`.
  Its underlying scheme is Spec of LaurentPolynomial k and its existing group
  law is Mathlib's Laurent Hopf law, not an arbitrary group object.
- The affine line is `StandardGroupSchemes.additive k`, whose underlying scheme
  is Spec k[u]. Its additive group law is not used as its scaling action.
  `ContractingLine.scaling k` is explicitly the contravariant Spec of
  `Polynomial.aeval (LaurentPolynomial.T 1 ⊗ₜ[k] Polynomial.X)`, preceded by
  the canonical affine-product comparison of `algSpec`. Thus u maps to z⊗u.
- `P Q : EquivariantRightTorsor ...` each contain the existing
  `RepresentedRightTorsor H L`: a represented right action, faithfully flat
  finitely presented projection, and the cartesian torsor square. The new
  `leftAction : ModObj G.X torsor.space` supplies the left G_m-action with
  its unit and associativity laws. `covers` says that the projection covers
  precisely the displayed scaling map; `commutes` says z.(p.h) = (z.p).h
  on every test scheme. These equations impose no trivialization.
- `ContractingLine.origin k` is the exact origin map induced by evaluation at
  zero, using `StandardGroupSchemes.identitySection`.
- `α₀ : EquivariantRightTorsor.FibreIso P Q (ContractingLine.origin k)`
  is an actual isomorphism of `pullback P.projection origin` and
  `pullback Q.projection origin`, in schemes over Spec k. Since the base of
  the fibre is the terminal object in this slice, this is over k.
  The two equivariance fields preserve action graphs after canonical fibre
  inclusions, on every test scheme. At zero these are exactly the induced
  actions: scaling fixes zero, so every translate factors through the fibre;
  the fibre inclusion is mono, giving a unique such factorization. Consequently
  graph preservation is equivalent to the ordinary two equivariance equations,
  and is not a weaker condition or a restriction to rational points.
- `∃ α : EquivariantRightTorsor.EquivariantIso P Q` gives an actual isomorphism
  over L. Its `over`, `left_equivariant`, `right_equivariant` fields respect
  the projection and both actions.
- The conclusion `pullback.fst ... ≫ α.iso.hom = α₀.iso.hom ≫ pullback.fst ...`
  says precisely that restriction is the specified α₀. The induced map on
  pullbacks is determined uniquely by this equation and the terminal second
  projection. No uniqueness of the extension is asserted.
- Neither fibre is assumed trivial. No rational point, section, algebraic
  closure, splitting or characteristic hypothesis was added.

Dependency declarations used, with source signatures and docstrings read:

- Mathlib.CategoryTheory.Monoidal.Grp: `CategoryTheory.GrpObj`, `CategoryTheory.Grp`;
  Mathlib.CategoryTheory.Monoidal.Cartesian.Grp: the group laws on test points.
  The upstream WeilConjectures.AlgebraicGeometry.GroupScheme.Defs docstring
  confirms precisely this group-scheme convention.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `AlgebraicGeometry.Smooth`.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: `AlgebraicGeometry.LocallyOfFiniteType`;
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact: `AlgebraicGeometry.QuasiCompact`.
- Mathlib.Algebra.Field.Defs: `Field`.
- Sheaf.AlgebraicGeometry.SplitSolvableTorsorDefinitions:
  `AlgebraicGeometry.RepresentedRightTorsor`; only its arbitrary-base right torsor
  structure is used, not the split-solvable restriction on other declarations.
- Sheaf.AlgebraicGeometry.StandardGroupSchemes: `multiplicative`, `multiplicativeGroup`,
  `additive`, `map`, `identitySection` in `AlgebraicGeometry.StandardGroupSchemes`.
- Mathlib.CategoryTheory.Monoidal.Cartesian.Mod: `CategoryTheory.ModObj`.
- Mathlib.AlgebraicGeometry.Group.Affine: `AlgebraicGeometry.braidedAlgSpec`;
  Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Spec` and `Spec.map`.
- The new definition node supplies `EquivariantRightTorsor`, `EquivariantIso`,
  `FibreIso`, `ContractingLine.scaling`, and `ContractingLine.origin`.

Proof-dependency imports: the affine-spectrum and smoothness modules are already
exposed by statement imports. `lem-sfb-smooth-affine-torsor-isom-scheme` has no
recorded Lean declaration or module in the read repository, so there is no module
to import for this proof-only dependency. Its full mathematical statement is read
and used in the proof docstring; it is not assumed as a theorem parameter and
is not needed to type the stage-2 statement.

Edge cases checked before writing: arbitrary field, including finite fields and
positive characteristic; the trivial group; nontrivial fibre torsors; the same
torsor with an arbitrary specified equivariant fibre automorphism; empty test
schemes; test schemes without rational points. All action conditions quantify
on all test schemes of the ambient universe. A field can be placed in any larger
ambient universe; there is no independent smaller test universe. Degree zero
and negative degrees are treated separately in the proof sketch. In particular
neither uniqueness nor an identification of k[u] with k[[u]] is asserted.

Searches actually run through msearch.py:

- leanfinder: “Equivariant isomorphism of smooth affine group torsors over affine
  line extends from the origin under multiplicative group scaling”: eight hits
  about AffineEquiv, homotheties, and DilationEquiv, no matching scheme theorem.
- loogle: `"torsor"`: twelve hits including Torsor, AddTorsor and their component
  declarations; these are unbundled ordinary group torsors, not scheme torsors.
- grep: `torsor|principal.*bundle`, subdirectory AlgebraicGeometry: zero hits.
- leansearch: “A represented right group scheme torsor with a commuting left
  group scheme action and equivariant fibre isomorphisms”: eight hits including
  AddTorsor, Action.HomSubtype, Equiv.vaddConst and MulActionHom instances; no match.
- leanfinder: “A multiplicative group action on the affine line by scaling and
  equivariant right group scheme torsor isomorphisms”: eight hits about ordinary
  affine maps, AffineEquiv and homotheties, no scheme-torsor match.
- grep: `EquivariantRightTorsor|contractingLine|scaleCoaction`: zero hits.

Direct rg searches of lean/WeilConjectures and lean/Sheaf found the standard
scheme group/action and represented torsor component APIs listed above, and
related action-groupoid torsors. The latter have one acting group and an
invariant torsor projection; they do not give the second commuting left action
covering a moving base that this statement needs. The item id has no match in
lean/WeilConjectures. Searches of the DAG and `blueprint_refs.py search` for
“equivariant torsor” and “contracting affine line” found no matching definition
node. `blueprint_refs.py ancestor` reports the inherited null ancestor; the new
node preserves that null ancestor, the detailed source-place chain and via path.

Compilation: both delivered modules compile separately in dependency order with
scompile.py against the live published library. There are no compiler warnings
or errors. The initial probe exposed the scoped `braidedAlgSpec` instance needed
by the affine-product comparison; the definition now installs that exact existing
instance within its body. There are no private definitions, local notation,
file-local instances or auto-bound variables. No statement dispute or correction.

## New nodes

`def-sfb-equivariant-right-torsor-fibre-isomorphism` supplies the missing composite
notion: a represented right H-torsor with a commuting left G-action covering a
specified base map, equivariant isomorphisms, actual fibre isomorphisms with
preservation of the action graphs, and the canonical scaling/origin maps for the
standard affine line. Its sources are Section 2 Claims 1 and 3 and Lemma 3.6 of
the paper. The statement explicitly defines graph preservation for arbitrary
points and explains its usual equivariant meaning at fixed points. This makes
the fibre definition fully meaningful even without an invariant-point assumption.
The new definition uses the existing RepresentedRightTorsor, ModObj, Spec and
standard G_m/G_a declarations and contains no theorem or postponed proof.
The searches above, also recorded individually in mathlib_searches, exclude a
matching existing definition. The item gains this definition in stmt_deps.

## Second reading by Q108

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
