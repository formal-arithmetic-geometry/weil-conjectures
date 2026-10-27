## Worker report

States `AlgebraicGeometry.existsUnique_reduced_closedSubscheme_of_dense_rational_points`
in `Sheaf.AlgebraicGeometry.DenseRationalClosedSubschemeDescent`. Its only proof is
`sorry`; no definitions or auxiliary theorems are introduced. The node is unchanged
except for its Lean record. No statement correction, dependency repair, new node,
or statement dispute is needed.

Hypothesis and conclusion correspondence:

- Any field extension F ⊆ L is `(F L : Type u) [Field F] [Field L] [Algebra F L]`.
  The embedding is `algebraMap F L`; no separability, algebraicity, finite degree,
  perfection or algebraic closedness is imposed.
- An F-scheme X is `{X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of F))`.
  Its finite type hypothesis is exactly `[LocallyOfFiniteType f] [QuasiCompact f]`.
  The explicit structure map is appropriate because the statement concerns base
  change and the recorded rational-point declaration takes that map.
- X_L is `pullback f (Spec.map (CommRingCat.ofHom (algebraMap F L)))`, with
  `pullback.fst` its projection to X. This is the dependency's scheme base change,
  not its distinct module-base-change operation.
- Z ↪ X_L is `(Z : Scheme.{u}) (i : Z ⟶ pullback ...) [IsClosedImmersion i]`.
- Reducedness of Z is `[IsReduced Z]`. Mathlib defines reducedness by reduced rings
  of sections, with `isReduced_of_isReduced_stalk` and
  `isReduced_stalk_of_isReduced` establishing equivalence with reduced local rings.
- S ⊆ X(F) is `(S : Set (f.fieldPoints F))`. These are sections of f, not arbitrary
  maps to X with the field-structure compatibility omitted.
- Each base-changed point factors through Z is `hfactor`: for every `p ∈ S`, a
  scheme morphism `q : Spec L ⟶ Z` satisfies
  `q ≫ i = (f.baseChangeFieldPoint L p).1`. Composing this equality with the
  projection to Spec L shows q is automatically an L-point, so no extra over-base
  structure on q is required. Existence does not choose noncanonical data.
- The density hypothesis is `hdense : Dense (i ⁻¹' (... '' S))`. The image set is
  exactly the underlying points of `f.baseChangeFieldPoint L p`, evaluated at
  `default : Spec L`, its unique point. Taking its preimage along i gives precisely
  the points in Z: a closed immersion is injective and hfactor supplies their lifts.
  `Dense` means every closed subset of Z containing this set is all of Z.
- The unique reduced closed subscheme over F is `∃! I : X.IdealSheafData,
  IsReduced I.subscheme ∧ ...`. Quasi-coherent ideal sheaves classify closed
  subschemes, with canonical closed immersion `I.subschemeι`. Using ideal sheaves
  expresses uniqueness of the closed subscheme rather than equality of arbitrary
  isomorphic scheme representatives.
- `(Z_F)_L = Z` as closed subschemes is the equality
  `I.comap (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap F L)))) = i.ker`.
  `IdealSheafData.comap` is the actual pullback ideal sheaf, defined from a fibre
  product, and `comapIso` identifies its subscheme with that fibre product over X.
  `i.ker` is the ideal of the given closed immersion. Thus the equality includes
  the full scheme structure, and not just the underlying closed set.
- Empty Z, X, and S are allowed: no Nonempty hypothesis appears. For S empty the
  factorization hypothesis is vacuous, while density of the empty preimage forces
  Z empty. The unique model is then the empty closed subscheme, represented by the
  unit ideal. Identity extensions L = F, finite fields, positive characteristic,
  inseparable extensions, nonseparated X, and reducible reduced Z are included.
  Nonreduced Z is correctly excluded. The finite type assumption is retained even
  though the coefficient-basis proof works more generally.

Dependency declarations read and used:

- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, with `algebraMap`; `Field` is the
  standard class in `Mathlib.Algebra.Field.Defs`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, scheme morphisms,
  `Spec`, and `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the recorded pullback
  convention and `baseChange_morphism_projections`,
  `baseChange_section_characterization`. These reuse `Limits.pullback`, with
  `pullback.fst` to the original scheme and `pullback.snd` to the new base.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `WeilConjectures.AlgebraicGeometry.DensePoints`:
  `AlgebraicGeometry.Scheme.Hom.baseChangeFieldPoint`, whose full signature and
  docstring were read; its domain is `f.fieldPoints F` and output is a section of
  `pullback.snd` over L.
- The already available ideal interfaces are `Scheme.IdealSheafData`,
  `Scheme.Hom.ker` (recorded by def-sbc-closed-immersion-ideal-sheaf),
  `IdealSheafData.subscheme`, `subschemeι`, `comap`, and `comapIso` in Mathlib's
  IdealSheaf Basic, Subscheme and Functorial modules. They supply real canonical
  constructions; none is replaced by a private copy.

The statement dependencies' recorded modules are public imports. Stated proof
interfaces are plain imports: `ReducedInducedClosedSubscheme`,
`AffineChartBaseChangeIso`, `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine`,
Mathlib tensor-product Maps/Map, and PullbackCarrier. The remaining Mathlib proof
interfaces (basic opens, radicals, reduced affine schemes, closed-immersion lifts,
field-spectrum surjectivity) are available through these imports. The proof-only
node `lem-sfb-common-linear-kernel-field-extension` has no recorded Lean declaration
in the read checkout, so it has no import yet. It is not needed to type this
statement; its future import belongs to the maintainer's normal proof-import update.
The docstring carries all five proof steps and names the DAG interfaces they use.

Source reading: extracted and read Milne, Algebraic Groups (2017), printed
pp. 571–572 and 581 (PDF pages 583–584 and 593): A.24 gives closed subschemes by
ideal sheaves, A.27–28 give reducedness and determination of sections by their
values, and A.65 gives uniqueness of a field model. A.65's existence assertion is
Galois descent; arbitrary-field existence here is the node's explicit independent
coefficient-basis argument, not incorrectly attributed to that Galois assertion.
On an affine chart the evaluation-kernel formula and scalar-extension of a common
linear kernel identify the ideals; the reduced closure glues those ideals.

Searches for an existing statement (all through the prescribed msearch wrapper,
with direct source searches in the named read-only trees):

- LeanFinder: `A reduced closed subscheme of a field base change with dense rational
  points over the base field descends uniquely`. Eight hits: geometric reducedness,
  SpecToEquivOfField, dominant-morphism extensionality and the field of global
  sections of a universally closed integral scheme. None states this descent result.
- Loogle: `AlgebraicGeometry.Scheme.IdealSheafData, AlgebraicGeometry.IsReduced`.
  Two hits: `Scheme.nilradical_eq_bot` and
  `Scheme.IdealSheafData.support_eq_top_iff`. Neither is the descent assertion.
- LeanSearch: `A reduced closed subscheme with dense rational points over a subfield
  descends uniquely to that subfield`. Eight hits concern reducedness constructors,
  geometric reducedness, dominant-morphism extensionality and rational maps;
  none is an exact statement match.
- Mathlib grep: `descen.*(closed|subscheme)|rational.*dens|dens.*rational`, restricted
  to AlgebraicGeometry. Twelve hits in FlatDescent and birational/rational-map
  modules concern descent of morphism properties or dense open domains, not this
  theorem.
- Direct `rg` with the same pattern over `lean/WeilConjectures` and `lean/Sheaf`:
  DensePoints gives the induced points and smooth separably closed density;
  flat-descent modules give descent of properties. References in
  SubvarietySeparableDefinition and GeometricSemiabelianSplitQuotient name this
  item only in proof docstrings. No declaration states this result.
- Direct `grep -rn` for the exact node id in `lean/WeilConjectures`: no hit.
- Direct `rg` for the proposed declaration name in the upstream-name index and
  both source trees: no hit.

Validation: the prescribed `scompile.py NY lem-sfb-dense-rational-closed-subscheme-descent`
compiled the module as both the private sandbox and its delivered module path,
with no errors or warnings (1.8 and 2.3 seconds respectively). Every type variable
and universe is explicitly bound; no local notation, private definition, local
instance or statement let-binder is used. Maximum source line width is 92.

## Second reading by NY

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
