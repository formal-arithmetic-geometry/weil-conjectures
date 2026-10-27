## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothAffineConcentrator` states
`AlgebraicGeometry.exists_smooth_affine_concentrator`, with one postponed proof
and no new definitions. The node's statement, dependencies and proof are unchanged.

Source read: Milne, Algebraic Groups (2017), Definition 13.21 and Propositions
13.22--13.24, printed pp.261--262, with the graded-local argument in Lemmas
13.25--13.27, printed pp.262--263. In particular Proposition 13.24 tests all
k-algebras, and its orbit is explicitly allowed to be a k-morphism to X in place
of the equivalent R-morphism to X_R. The seven-step proof docstring preserves
all steps and dependency names from the accepted split.

Hypotheses and clauses, matched individually:

- A field k: `{k : Type u} [Field k]`.
- The k-schemes X and Z: `(X Z : Over (Spec (.of k)))`. Bundled Over morphisms
  include compatibility with the structure maps.
- X affine: `[IsAffine X.left]`.
- X finite type: `[LocallyOfFiniteType X.hom] [QuasiCompact X.hom]`, exactly
  the recorded finite-type convention.
- X and Z smooth over k: `[Smooth X.hom] [Smooth Z.hom]`.
- The multiplicative group action on X: `a : ModObj
  (StandardGroupSchemes.multiplicative k) X`. Mathlib's `ModObj` supplies the
  action morphism `a.smul` and its unit and associativity identities, with the
  canonical Laurent Hopf group law on the recorded multiplicative group.
- Closed subscheme: `(i : Z ⟶ X) [IsClosedImmersion i.left]`.
- Invariance is the existence of an action `aZ` on Z with
  `(𝟙 _ ⊗ₘ i) ≫ a.smul = aZ.smul ≫ i`. This is exactly scheme-theoretic
  stability: restriction of the action factors through Z. Conversely a
  factorization inherits both action identities because a closed immersion is
  a monomorphism, so this adds no mathematical assumption.
- Representing closed subscheme: existential `Y : Over (Spec (.of k))` and
  `j : Y ⟶ X`, with `IsClosedImmersion j.left`.
- Smoothness: `Smooth Y.hom`; finite type:
  `LocallyOfFiniteType Y.hom ∧ QuasiCompact Y.hom`.
- R-points of Y identify with precisely the prescribed subset of X(R): for each
  `(R : CommAlgCat.{u} k)` and `x : StandardGroupSchemes.affine k R ⟶ X`,
  `(∃ y, y ≫ j = x)` is equivalent to existence of an affine-line morphism q
  satisfying the displayed orbit-restriction equation and whose zero value
  factors as `z ≫ i`. Since j is a closed immersion it is a monomorphism, so
  this image equality gives a bijection on each Hom set. Composition with j
  is natural in R; thus this is representability of the subfunctor, rather
  than an arbitrary collection of pointwise bijections.
- Orbit restriction: `𝟙 (affine k R) ⊗ₘ map k Polynomial.toLaurentAlg`
  is the actual open inclusion Spec R × Gm → Spec R × A1. The other side
  `lift (snd _ _) (fst _ _ ≫ x) ≫ a.smul` is (t,r) ↦ t·x(r), with product
  factors ordered Spec R first. A k-morphism from this product to X is
  canonically the corresponding R-morphism to X_R, so no base-linearity
  condition is lost by avoiding an additional pullback in the notation.
- Existence and value of the limit: the zero section is
  `lift (𝟙 _) (map k (Polynomial.aeval (0 : R)))`. Its second component is
  Spec of the k-algebra map k[t] → R evaluating t at zero. The first conjunct's
  `∃ z, zeroSection ≫ q = z ≫ i` says the value lies in Z(R), with its full
  scheme structure, not merely its underlying closed set.
- Uniqueness of extension: the second universally quantified conjunct says
  any two q and q' restricting to the orbit of the same x are equal. It covers
  all extendable x, including those whose limit is outside Z.
- Evaluation morphism: existential `π : Y ⟶ Z`, with the final conjunct
  `zeroSection ≫ q = y ≫ π ≫ i` for every y and every extension of its orbit.
  The representability clause supplies such an extension for each y;
  uniqueness of q and monicity of i identify its value with y ≫ π in Z(R).
- All test algebras, including nonreduced ones: each quantifier ranges over
  arbitrary `CommAlgCat.{u} k`, in the same universe as the schemes and field.
  There is no reducedness, domain, field or nontriviality assumption on R.
  The theorem is universe-polymorphic; all variables and universes are explicit.

Dependency declarations read and used:

- `Field` in `Mathlib.Algebra.Field.Defs` (the Mathlib match for def-weil-field).
- `AlgebraicGeometry.Scheme` and its morphisms in
  `Mathlib.AlgebraicGeometry.Scheme` (def-pc-scheme).
- `AlgebraicGeometry.LocallyOfFiniteType` in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, and `QuasiCompact` in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
  (def-weil-finite-type-morphism).
- `AlgebraicGeometry.Smooth` in `Mathlib.AlgebraicGeometry.Morphisms.Smooth`
  (def-sbc-smooth-morphisms), with its actual affine-local ring-map definition.
- `StandardGroupSchemes.multiplicative`, `multiplicativeGroup`, `additive`,
  `affine`, and `map` in `Sheaf.AlgebraicGeometry.StandardGroupSchemes`
  (def-sc-gm-ga). Full signatures and their coordinate-map docstrings were read.
- `AlgebraicGeometry.IsClosedImmersion` in
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
  (def-weil-closed-immersion).
- Mathlib `CategoryTheory.ModObj` in `CategoryTheory.Monoidal.Mod` and
  cartesian `lift`, `fst`, `snd`, tensoring morphisms, with
  `Polynomial.toLaurentAlg` and `Polynomial.aeval`, give the existing actions
  and canonical coordinate maps. No copy of those notions is defined.

The proof imports the stated dependencies: Proper and Smooth for base-change
stability; upstream Regular for `IsRegular.of_smooth`; FiniteType,
Spectrum.Prime.Noetherian and Topology.NoetherianSpace for affine Noetherianity;
`Sheaf.RingTheory.GradedLocalAttractionRegularity`; upstream
`Mathlib.RingTheory.Smooth.Local` for smoothness at regular closed points;
RingHomProperties (publicly supplied by Smooth), scheme source-local smoothness
(supplied by Smooth), FinitePresentation, Flat and PullbackCarrier; and
`Sheaf.AlgebraicGeometry.LfpSmoothFlatBaseChange`. The sole unstated proof
prerequisite `lem-sfb-scheme-large-algclosed-jacobson` has no module to import;
it remains named in the proof docstring. It is not needed to type this statement.

Edge cases checked before writing:

- Empty X or Z is allowed: there is no nonemptiness assumption, and the empty
  closed subscheme represents the empty condition (on the zero algebra its
  unique empty-spectrum point is retained).
- Zero test algebra is allowed. Its spectrum is empty and all equations of
  maps out of it hold uniquely; the representability equivalence retains this.
- Trivial action gives Y = Z, with constant orbit extension and π the identity.
- Z = X imposes just existence of the limit. Positive weight on A1 gives all
  of A1; negative weight gives the zero subscheme, including its scheme-level
  point condition over rings with nilpotents.
- For R = k[ε]/(ε²), a negative-weight orbit εt⁻¹ is not polynomial unless
  ε = 0; the statement tests the Laurent equality itself, so nilpotents are
  not accidentally discarded by geometric-point conditions.
- No characteristic restriction: Laurent coefficient injectivity works also
  in positive characteristic, independently of differentiating the action.
- Smooth Z need not be pointwise fixed: invariance requires the restricted
  action only. For a trivial action this still gives the correct Y = Z.

Searches (via the prescribed msearch.py, and direct rg):

1. LeanFinder query: "The attracting concentrator of a smooth invariant closed
   subscheme of a smooth affine scheme with multiplicative group action is
   smooth". Eight hits were the general Smooth/relative-dimension APIs; none
   stated a concentrator result.
2. Loogle query: `AlgebraicGeometry.IsClosedImmersion,
   AlgebraicGeometry.IsSmooth`. Zero hits, with the service reporting unknown
   IsSmooth (the local pinned declaration is Smooth).
3. LeanSearch query: "Representability and smoothness of the attracting functor
   of a smooth invariant closed subscheme under a multiplicative group action".
   Eight hits included generic local representability, Smooth constructors,
   invariants functors, and relatively representable morphisms; none matches.
4. msearch grep `concentrator|attractor|attracting|GmAction` in AlgebraicGeometry:
   zero hits. Direct rg of project Sheaf and upstream WeilConjectures and DAG
   found only this node, downstream cocharacter-limit uses, and different
   projective attracting-cell statements, not the general affine statement.
5. Direct rg of the internal category modules found the existing `ModObj` with
   exactly the unit and multiplication laws needed here. The downstream
   `CocharacterLimit.IsOrbitExtension` is specifically a conjugation-orbit
   predicate and does not state this theorem; its product convention confirmed
   the coordinate maps used here. Direct search for this item's id in upstream
   WeilConjectures and for the new declaration name in Mathlib, upstream,
   Sheaf and dag/lean_names_upstream.json gave no declaration match.

Validation: prescribed scompile.py compiled both the sandbox and library module
cleanly (1.9 seconds each); the only theorem proof is `sorry`. No hollow data,
no local notation, no private helper, no new node, no dependency-interface
repair and no statement correction. No STATEMENT-DISPUTED issue remains.

## Second reading by Q45

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
