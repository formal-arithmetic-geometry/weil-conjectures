## Worker report

The delivery states `SheafOfModules.ringedExchangeTensorCoherence` in
`Sheaf.Paper.RingedExchangeTensorCoherence`, with a real-data presentation of its
ringed square in `Sheaf.Paper.RingedTensorSquarePresentation`. The item's natural
statement is unchanged. Only its `lean` record and the additional definition-node
statement dependency change. No dependency record is replaced.

Hypotheses and objects, matched to the node:

- Four ringed topoi on sites small in the chosen universe are `Y X Y' X' :
  RingedTensorCorner.{u,w}`. Each corner carries its actual category, topology,
  commutative ring sheaf, `HasDerivedCategory.{w}`, and tensor bifunctor.
  `RingedTensorModel.representative` identifies that bifunctor with the existing
  total tensor on precisely the flat-term K-flat full subcategory. It uses
  Mathlib's `ObjectProperty.ι`, not a duplicate derived category or tensor complex.
- The four edges are `f : RingedTensorEdge Y X`, `g : RingedTensorEdge Y Y'`,
  `h : RingedTensorEdge X X'`, `k : RingedTensorEdge Y' X'`. Thus `h` is the node's
  g-prime and `k` is its f-prime. The edge structure is written in inverse-image
  direction. Its `inverse`, `direct`, `adjunction`, and `finiteLimits` specify
  exactly a geometric morphism. `algebraic` is the existing algebraic inverse-image
  presentation. `ringMap` is an arbitrary structural ring homomorphism, not
  an isomorphism or a flat map. `pullback`, `object_eq`, and `map_eq` specify
  precisely extension of scalars after algebraic inverse image, on both objects
  and morphisms.
- `left`, `epsilon`, and `isLeftDerived` specify the canonical total left derived
  module pullback by its universal property. `right` and `derivedAdjunction`
  present its derived direct image. As for any derived adjunction, a model of the
  right adjoint is canonically identified, compatibly with the adjunction, with
  the right derived module direct image. The statement works with any such model;
  it does not select an independent map or assume an exchange isomorphism.
- `s : RingedTensorSquare Y X Y' X' f g h k` specifies the commutation isomorphism
  on sheaves of sets (`sets`) and its linear module comparison (`modules`).
  `insertion` identifies the comparison on all scalar-extension generators,
  through the existing `AlgebraicInverseImage.moduleUnderlying` identifications.
  This is the module presentation of the ringed commutation condition: apply
  linearity and the insertion equation to scalar multiples, including the
  coefficient module. Conversely a ring-compatible geometric square induces
  precisely this module comparison by scalar-extension associativity. No derived
  tensor compatibility is supplied as a hypothesis.
- `ordinaryTensor` uses the existing `CanonicalRingedTensorComparison`, including
  its generalized pure-tensor formula. `tensorComparison` calls exactly
  `ringedTopoiCanonicalDerivedTensorComparison` with both corners' representative
  isomorphisms. It is not an arbitrary natural isomorphism with the right type.

Constructions and clauses, matched to the node:

- `RingedTensorSquare.complexComparison` is the existing ordinary module square
  applied termwise using `NatIso.mapHomologicalComplex`.
- `derivedComparison_existsUnique` states that there is a unique derived square
  whose map on every flat-term K-flat P agrees with that termwise square under
  the four explicit `derivedPullbackComplexComparison` arrows. It is Step 1 of
  the item's proof, with that proof in its docstring. `derivedComparison` selects
  this unique object. This is a permitted uniqueness-determining theorem choice,
  not a choice from a bare `Nonempty` isomorphism assertion.
- `exchange` is `CategoryTheory.mateEquiv f.derivedAdjunction k.derivedAdjunction`
  applied to `derivedComparison.hom` as a `TwoSquare`, exactly the specified Ex.
- `RingedTensorEdge.projection` is `derivedAdjunction.homEquiv` of tensor comparison
  followed by `tensor.map (Prod.mkHom counit identity)`, exactly pi_u with the
  orientation of Tag 07A4. No projection is assumed invertible.
- `projectionFirst` is `g.left.map (f.projection ...)`, then exchange at
  `E tensor f.left Q`, then `k.right.map` of h's tensor comparison followed by
  tensor of identity and `derivedComparison.inv.app Q`. Thus its target is
  exactly `Rf'_*(L(g')^* E tensor L(f')^* Lg^* Q)`.
- `exchangeFirst` is g's canonical tensor comparison, tensor of exchange and
  identity, then k's projection at `(h.left E, g.left Q)`. It has the same target.
- The first conjunct of `ringedExchangeTensorCoherence` states the equality for
  every E and Q in the exact unbounded derived categories. The second states
  simultaneous naturality for arbitrary `v : E → E'`, `z : Q → Q'`, with the
  source and target bifunctor maps written explicitly. Naturality for the second
  route follows from the first conjunct. Taking either morphism to be identity
  gives naturality in either variable separately.
- The docstring carries all five proof steps: representative construction,
  representative tensor coherence, the mate/projection transpose identities,
  the calculation of the first transpose, and cancellation giving the second
  transpose and naturality. It names every proof dependency.

Dependency declarations read and used:

- `Sheaf.Paper.RingedTopoiCanonicalTensorPullback`:
  `SheafOfModules.CanonicalRingedTensorComparison`,
  `SheafOfModules.ringedTopoiCanonicalDerivedTensorPullback`,
  `SheafOfModules.ringedTopoiCanonicalDerivedTensorComparison`, and
  `CategoryTheory.derivedPullbackComplexComparison`. The recorded complete
  signature and docstring were read, including representative normalization.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `CategoryTheory.mateEquiv`, with
  `TwoSquare`, `.natTrans`, and the actual unit/counit orientation. This is the
  `mathlib_match` of `def-weil-pbc-adjunction-mate`, which needs no lean repair.
- `Sheaf.CategoryTheory.AlgebraicInverseImage`:
  `SheafOfModules.AlgebraicInverseImage`, including its graph laws and
  `moduleUnderlying`. The definition node and full declaration were read.
- Proof imports: `Sheaf.Algebra.Homology.KFlatResolution`,
  `Sheaf.Paper.RingedTopoiDerivedPullback`,
  `Sheaf.Algebra.Homology.SiteDerivedTensorDescent`, and
  `Sheaf.CategoryTheory.ModulePullbackTensorIso`; the tensor dependency and mate
  dependency are public through the presentation import.

Edge cases checked before finalizing:

- Identity edges and identity square give the usual projection expression;
  inverse comparison orientation is forced by the final `k.left (g.left Q)` target.
- Zero objects, zero coefficient ring, empty sites, and arbitrary unbounded
  complexes remain allowed. There is no nonempty, bounded, perfect, proper,
  cartesian, exact-pullback, ring-isomorphism, or flatness hypothesis.
- Noncartesian squares are admitted: only a specified inverse-image commutation
  isomorphism and its ring-compatible module comparison occur in the data.
- Tensor coherence is proved in the main theorem, not assumed of the square.
  The ordinary insertion equation prevents arbitrary scalar rescalings of theta.
- Site and coefficient universe u and derived localization universe w are
  explicitly bound and independent. The corner is a bundle, so its type lives
  in their maximum; only that declaration disables the checkUnivs linter for
  intentionally bundled universes. No equality of universe levels is imposed.
  The larger instance-search size is needed for the two-variable representative
  tensor expression, following the recorded dependency's elaboration convention.

Searches made (no matching existing statement):

- `msearch.py leanfinder`, query “Projection formula and exchange mate compatibility
  for a commutative square of ringed topoi”: eight hits on Mayer–Vietoris sheaf
  conditions and presheafed-space gluing, none states this diagram.
- `msearch.py loogle`, query `CategoryTheory.mateEquiv, CategoryTheory.Adjunction`:
  mateEquiv and its counit/unit/composition lemmas, but no tensor-exchange coherence.
- `msearch.py grep`, query `projectionFormula|projection_formula|baseChange.*tensor`
  in CategoryTheory: zero hits.
- `rg` in upstream WeilConjectures for the item id: no hit; `rg` for tensor/exchange
  coherence and ringed squares in upstream and `lean/Sheaf`: no general matching
  declaration. Scheme-only mixed-square tensor coherence is not this ringed-topos
  projection/exchange theorem.
- New-presentation searches are recorded verbatim in the new definition node:
  LeanSearch unavailable (Internal Server Error); LeanFinder returns ordinary
  module pullback composition for continuous site functors; grep finds no proposed
  names in Mathlib/upstream/project/DAG; `blueprint_refs.py search 'ringed square'`
  returns zero blueprint nodes. DAG statement search found the pro-etale-only
  ambient-ringed-exchange and proetale-derived-pullback-composition nodes, which
  do not supply the arbitrary ringed-topos square of this theorem. Their
  coefficient-isomorphism restriction is not imposed here.
- The underlying Stacks source was read locally at remark-compatible-with-diagram
  (Tag 0E48), including the precise t/b/p/c diagram. Mathlib's pullbackComp was
  read: it concerns continuous site functors and has no derived tensor/exchange
  equality, so it is not an exact existing match.

Both modules passed scompile.py, separately in dependency order, with no errors
or warnings. Stage 2 leaves exactly two named theorem proofs as sorry:
`RingedTensorSquare.derivedComparison_existsUnique` and
`ringedExchangeTensorCoherence`; both are clauses of the item's construction and
conclusion, with source and complete proof docstrings. All definition data is
written in full. No STATEMENT-DISPUTED flag or statement correction is needed.

## New nodes

`def-weil-pbc-ringed-tensor-square-presentation` supplies the general square
presentation absent from the DAG/library. Its module reuses Mathlib sites,
sheaf modules, derived categories and total tensor, plus the recorded algebraic
inverse image and canonical tensor comparison, rather than copying these
notions. It bundles four small ringed corners and the relevant edge data; the
square itself is the specified geometric commutation isomorphism with the
linear scalar-insertion-normalized ordinary module comparison. This expresses
structural-ring compatibility on generalized elements and adds no derived
coherence hypothesis. The source is Stacks 0E48, 0D6D, 07A4 and the ordinary
module tensor construction 03EL. The node records the three required search
kinds and its correct blueprint ancestry. It has no postponed theorem or hollow
construction. Its additional helpers are listed in `lean.declarations`.

## Second reading by NY

I independently read the item node, both delivered modules and the new definition
node, with the Stacks source open. No mathematical mismatch was found. The Lean
and node statements are retained; this reading adds the present report and fresh
search evidence. There is no statement correction or dependency-module repair.

Object/hypothesis/conclusion checklist, in the order of the node:

1. Four ringed topoi: `Y X Y' X' : RingedTensorCorner.{u,w}` contain their
   actual small site, Grothendieck topology and commutative ring sheaf. The module
   categories are the existing `SheafOfModules`, and their unbounded derived
   categories are the existing `DerivedCategory`, with localization size `w`.
   `RingedTensorModel.representative` identifies each corner's bifunctor with
   ordinary total tensor on the full subcategory of K-flat flat-term complexes.
   Verdict: the same derived tensor models as the dependency, not a second tensor
   construction and not an arbitrary unnormalized tensor comparison.
2. Four morphisms: `f : RingedTensorEdge Y X`, `g : RingedTensorEdge Y Y'`,
   `h : RingedTensorEdge X X'`, `k : RingedTensorEdge Y' X'`. Thus `h` denotes
   g-prime and `k` denotes f-prime; the structure's order follows inverse image,
   opposite the geometric arrows. `inverse`, `direct`, `adjunction` and
   `finiteLimits` give a geometric morphism on sheaves of sets. `algebraic` is
   exactly the recorded `AlgebraicInverseImage`; `ringMap` is a general ring map.
   Verdict: no coefficient-ring isomorphism or flatness assumption is introduced.
3. Ordinary and derived operations: `object_eq` and `map_eq` impose extension of
   scalars after algebraic inverse image on both objects and maps. The additive
   instance and module adjunction are available for that actual pullback.
   `epsilon` and `isLeftDerived` specify its left derived functor, rather than
   merely an unspecified functor on the derived categories. `right` with
   `derivedAdjunction` presents its right adjoint. A right adjoint of this left
   derived functor identifies uniquely, compatibly with its adjunction, with
   the derived direct image. Consequently allowing adjunction models does not
   replace the canonical counit by an unrelated map. Verdict: matches the node.
4. Specified ringed commutation: `s.sets` is the inverse-image isomorphism
   `g.inverse ⋙ k.inverse ≅ f.inverse ⋙ h.inverse`. `s.modules` is its linear
   ordinary module square. `s.insertion` fixes this comparison on the images of
   every module's scalar-extension generators. The edge insertion is explicitly
   `algebraic.moduleUnderlying.inv.app M ≫ ordinaryTensor.q M`; the dependency's
   `q_one` fixes q as insertion of 1. Testing scalar multiples, including in the
   coefficient module, enforces structural-ring compatibility. Conversely the
   compatible ringed square gives this linear isomorphism by scalar-extension
   associativity. Verdict: an equivalent presentation of the given square,
   with no cartesianness and no derived tensor coherence assumed.
5. Induced theta: `complexComparison` applies precisely `s.modules` termwise.
   `derivedComparison_existsUnique` characterizes theta by its square with the
   four explicit `derivedPullbackComplexComparison` maps, for every K-flat
   flat-term P. The directions were checked: theta goes from `g.left ⋙ k.left`
   to `f.left ⋙ h.left`. `derivedComparison` chooses from this uniqueness
   theorem. Verdict: the representative-induced canonical comparison, not a
   choice from an undetermined existence assertion. This auxiliary postponed
   theorem is exactly the construction in Step 1 of this item's DAG proof.
6. Tensor comparisons and projection maps: `tensorComparison` calls the recorded
   `ringedTopoiCanonicalDerivedTensorComparison`, with both representative
   identifications and the pure-tensor-normalized ordinary comparison.
   `projection` uses `derivedAdjunction.homEquiv` on that comparison followed
   by tensor of the counit with identity. Verdict: precisely the stated pi,
   with no invertibility of pi assumed.
7. Exchange: `exchange` applies Mathlib `mateEquiv` to theta, with adjunctions
   for f and k. Reading `Mates.lean` confirms the unit/theta/counit orientation
   and the resulting type `f.right ⋙ g.left ⟶ h.left ⋙ k.right`.
   Verdict: the specified exchange map, with no base-change-isomorphism assumption.
8. First route: `projectionFirst` is g of f's projection, then exchange at
   `E tensor f.left Q`, then k of h's tensor comparison and tensor of identity
   with `derivedComparison.inv.app Q`. Verdict: the upper/right route of 0E48,
   including the final c-arrow. The inverse is required because the final target
   is `k.right (h.left E tensor k.left (g.left Q))`.
9. Second route: `exchangeFirst` is g's tensor comparison, tensor of exchange at
   E with identity at `g.left Q`, and k's projection. Verdict: exactly the
   lower/left route to the same target.
10. Equality and naturality: the first conjunct of `ringedExchangeTensorCoherence`
    quantifies over every E in D(O_X) and Q in D(O_Y) and equates those routes.
    The second conjunct is the naturality square for arbitrary simultaneous
    `v : E ⟶ E'` and `z : Q ⟶ Q'`, with the actual source and target bifunctor
    maps. Equality of the routes transfers this naturality to the second route;
    identity morphisms recover naturality in either variable. Verdict: every
    conclusion clause is present, without a stronger geometric hypothesis.

Source and dependency review: read `sites-cohomology.tex` at
`remark-compatible-with-diagram` (0E48), including all t/b/p/c arrows, the
preceding definition of the projection arrow, and the proofs of
`lemma-derived-pullback-composition` (0D6D) and
`lemma-pullback-tensor-product` (07A4). The perfectness hypothesis of the preceding
projection-formula *isomorphism* lemma is not an assumption of this remark or of
its projection map. Read the complete recorded canonical tensor interface in
`RingedTopoiCanonicalTensorPullback.lean`, its representative equation and
`derivedPullbackComplexComparison`; the algebraic lift's ring/module graph laws
and underlying natural isomorphism; and Mathlib's `mateEquiv`. Also checked the
imported ringed derived-pullback and site tensor-descent signatures. They apply
to arbitrary small ringed sites with exactly the sizes used here. The main
statement docstring follows all five DAG proof steps; the construction theorem
carries its own Step 1 proof, and every helper has the owning blueprint/source.

New-node review (H12): `def-weil-pbc-ringed-tensor-square-presentation` is a
definition node with the required status, chapter/unit, ancestor/via, worker
creation record, empty proof fields, null match, none audits and three search
kinds. Its statement cites exactly its two statement dependencies. Reading its
Lean fields gives the corner/edge/square presentation described above; it adds
no postponed theorem or hollow data. This is a presentation of the source's
ringed square using the already defined algebraic and tensor ingredients.
There are no delivered dependency modules to review under H13.

Edge cases: all complex degrees are integers and no boundedness is required.
Zero modules, zero coefficient rings and empty sites are admitted; there are no
nonempty-index, positive-degree, characteristic, field, finiteness, properness,
perfectness or exact-pullback assumptions. Identity edges and squares preserve
the displayed orientations. Noncartesian ringed squares are included. The site
and coefficient size u is the chosen common universe of the recorded dependency;
w is independently bound as the derived localization size. No extra equality
between universe levels is imposed. There are no unbound universe or object
variables, hidden `let` binders, private duplicate constructions or proof-bearing
definitions with `sorry` data. Exactly two named theorem proofs remain postponed.

Fresh independent searches:

- LeanFinder: "Commutativity of projection formula with base change natural
  transformation under adjunction" returned exponentiable-morphism evaluation
  and coevaluation naturality and ordinary pullback-composition results, not
  this general derived ringed-topos statement.
- Loogle: `CategoryTheory.mateEquiv` returned the mates bijection and its
  unit/counit/composition identities; these supply the reused mate, not the
  theorem under review.
- LeanSearch: "Ringed topoi commutative square projection formula exchange
  compatibility" was unavailable with Internal Server Error; no negative
  mathematical conclusion is inferred from that service failure.
- msearch grep: `rightAdjointProjectionMap_mate|RingedTensorSquare|tensor.*mate`
  returned six rigid-monoidal mate implementation hits, no match.
- Direct `rg` on Mathlib, upstream `WeilConjectures`, project `lean/Sheaf` and
  DAG found no existing general square presentation or this statement. The
  upstream `Etale.rightDerivedLowerStarProjectionMap_derivedBaseChangeMap` in
  `LowerStarProjectionBaseChange.lean` was opened and read: it concerns schemes'
  small etale sites with a fixed coefficient category and its additional
  resolution/flatness structures, not general ringed-topos morphisms or arbitrary
  structural ring maps. Its abstract input
  `Adjunction.rightAdjointProjectionMap_mate` in `ProjectionMapCompat.lean` was
  also opened: it assumes the tensor-compatibility equation h-sigma, which is
  constructed here from the ringed square. It is a possible stage-3 proof tool,
  not an existing statement of this node. The DAG's ambient ringed exchange
  notion is pro-etale and requires coefficient-ring identifications; it cannot
  replace the square presentation here.

Validation: both delivered modules were compiled separately, in dependency
order, through the prescribed `scompile.py` wrapper with no errors or warnings.
No Lean edit was needed. The node's recorded main signature and the new node's
structure signature agree with their module text (whitespace normalized by the
project convention). `deliver2.py --no-push` passed preflight and compilation
with OK (dry-run commit c4df6c5c18); the second reader then invoked the
prescribed delivery wrapper for publication.
