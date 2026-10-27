## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.SplitReductiveDVRCartanDecomposition`
states `AlgebraicGeometry.splitReductive_dvr_cartan_decomposition`, with `sorry` as
its only theorem proof. No theorem is proved. The item's natural-language statement,
accepted stage-1 split and proof dependencies are unchanged. Its statement dependencies
gain the new ring-base split-torus definition and the already landed reductivity and
maximal-torus terminology. There is no released repair note for this item. The inherited
BLOCKED result concerned stage-1 duplicate splitting; the current item is stage 2, is
queued there, and has no previous usable Lean record.

Clause-by-clause correspondence:

- The commutative domain R is bound by `(R : Type u) [CommRing R] [IsDomain R]`;
  `[IsDiscreteValuationRing R]` gives local PID and nonzero maximal ideal. The field
  case is excluded by this existing DVR definition, exactly as the node requires.
- `(L : Type u) [Field L] [Algebra R L] [IsFractionRing R L]` specifies its fraction
  field and the actual inclusion. There is no topological, completeness, henselianity
  or residue-characteristic hypothesis.
- `D : Grp (Over (Spec (.of R)))` supplies the scheme over R, multiplication, unit,
  inverse and every group diagram. `[Smooth D.X.hom]`, `[IsAffine D.X.left]`,
  `[LocallyOfFiniteType D.X.hom]` and `[QuasiCompact D.X.hom]` are precisely smooth,
  affine and finite type over R, including quasi-compactness.
- `hred` quantifies over every algebraically closed field Ω in the schemes' universe
  and every ring map `f : R →+* Ω`. The functor
  `(Over.pullback (Spec.map (CommRingCat.ofHom f))).mapGrp` is actual geometric
  base change, with its induced group structure. Its `IsReductive` predicate is the
  landed one: affine finite type, smooth, connected after algebraic closure, and
  every smooth connected closed normal unipotent subgroup after algebraic closure
  is trivial. `SolvableGroupStructure.IsUnipotent` uses a faithful closed matrix
  representation, with nilpotent matrix minus identity on geometric points, and
  includes smoothness. For an already algebraically closed Ω this is equivalent
  to the node's geometric-fibre definition, with no extra hypothesis. In particular
  both the geometric generic and special fibres are tested. Using `Type u` for
  R, D and Ω does not introduce an unrelated smaller test universe: algebraic
  closures of their residue fields have representatives in the same universe.
- `T : Grp (Over (Spec (.of R)))` and `i : T ⟶ D` make T an R-group scheme and i a
  group homomorphism. `[IsClosedImmersion i.hom.hom.left]` is precisely its closed
  subgroup inclusion; no arbitrary set-theoretic subgroup replaces it.
- `(r : ℕ)` and `(e : T ≅ RingGroupSchemes.splitTorus R r)` give the specified
  finite-rank split torus, with group-scheme isomorphism, not just a scheme
  isomorphism. The new construction uses Spec of the Laurent Hopf algebra, whose
  multiplication is multiplication of units, and its finite cartesian powers.
- `hmax` uses the same Ω and f tests and `mapGrp.map i`. The existing
  `ReductiveTorusCentralizer.IsMaximalTorus` says this is a closed torus with no
  strictly larger torus: every factorization into another closed torus is an
  isomorphism. Thus maximality holds in every geometric fibre.
- The generic fibre G is the pullback along `Spec L → Spec R`. Its L-points are
  canonically the morphisms `Over.mk (Spec.map (CommRingCat.ofHom
  (algebraMap R L))) ⟶ D.X`, by the pullback universal property. The binder `g`
  uses this equivalent description of the SAME points, without choosing another
  generic group or an identification as an additional hypothesis. The same
  universal property identifies the type of `t` with the L-points of the given
  generic torus.
- `k₁ k₂ : 𝟙_ (Over (Spec (.of R))) ⟶ D.X` are the integral points D(R).
  `toUnit` from the Spec L test object is its structure map to Spec R, so
  `toUnit ... ≫ k₁` and `toUnit ... ≫ k₂` are their canonical restrictions.
  `t ≫ i.hom.hom` is the canonical image of t in the generic group. The final
  equality is exactly `g = k₁ t k₂`, in that order. The scoped `MonObj` operations
  are the group law on morphisms induced by the group-object multiplication.
  No arbitrary comparison maps or choices of point groups occur.
- The images mentioned in the node are encoded by these canonical restriction
  maps rather than quotient types. Affineness and injectivity of R into L make
  integral restriction injective; closed immersion gives injectivity for T.
  Existence of a factorization therefore has exactly the node's meaning.

Dependency declarations read and used:

- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`,
  with its domain, local ring, principal ideals and non-field clause.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, `Grp`, and
  the group on Hom into a group object (exposed through the construction imports).
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, including nonemptiness;
  reused inside the existing reductivity predicate.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` (closed embedding, surjective stalk maps).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  its projections and universal property. The existing cartesian `Over.pullback`
  functor induces `mapGrp` on group schemes.
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`:
  `AlgebraicGeometry.ReductiveTorusCentralizer.IsReductive` and `IsMaximalTorus`.
  Read their bodies and the underlying `SolvableGroupStructure.IsAlgebraic`,
  `IsUnipotent`, `MultiplicativeType.IsTorus` and `baseChange` before reuse.
- The new module below supplies `RingGroupSchemes.splitTorus`.
- The definition module reuses `LaurentPolynomial`,
  `LaurentPolynomial.instHopfAlgebra` and
  `AlgebraicGeometry.instGrpObjSpecAsOverSpec` from Mathlib, together with the
  cartesian tensor and unit of group objects. All group data is real data.

Proof imports include the stated completion-DVR theorem, local/completeness
modules, proper/smooth base-change, and the finite-type and affine-pullback APIs
(already public through statement imports). The three proof nodes
`lem-sfb-complete-dvr-cocharacter-cartan`,
`lem-sfb-complete-dvr-torus-cocharacter-conjugacy` and
`lem-sfb-split-reductive-local-quotient-points` have no recorded declarations yet;
there is no module to import for them. Their full roles remain in the six-step
proof docstring. These are proof prerequisites, not missing statement notions.

Edge cases checked before writing:

- r=0: the new finite product is the monoidal unit, so t is the identity; there
  is no positivity hypothesis on r or omitted trivial group case.
- D=T=G_m: choose t=g and both integral factors equal to one. More generally
  this holds for a split torus in any rank.
- GL_n with diagonal T gives the familiar DVR elementary-divisor factorization,
  over non-complete DVRs as well as complete ones.
- Arbitrary residue characteristic and finite/imperfect residue fields remain
  allowed. Geometric fibres are tested after algebraic closure, not assumed
  already split over the residue field as a stronger hypothesis.
- A disconnected smooth affine group is excluded by reductivity, not silently
  admitted. Empty schemes cannot be group schemes over this nonzero base:
  their unit section would have no image.
- The new torus definition itself allows zero rings: it is formed by actual
  Spec, Hopf operations and empty product. Its use in this theorem has R a DVR.

Searches for the item (all performed with msearch.py; exact evidence in
searches.jsonl):

- LeanFinder: `Cartan decomposition split reductive group scheme over discrete
  valuation ring integral points fixed split maximal torus` returned Lie Cartan
  subalgebras and Geck constructions, no group-scheme factorization.
- Loogle: `"GrpObj", "IsDiscreteValuationRing"` returned zero hits.
- LeanSearch: `Cartan decomposition split reductive group over discrete valuation
  ring` returned scalar valuation-ring facts and unrelated Lie objects.
- Mathlib grep: `Cartan.*decomposition|ReductiveGroup|MaximalTorus|SplitTorus|Unipotent`
  found projective linear stabilizers and biproduct upper unipotent maps, no match.
- rg over WeilConjectures and Sheaf for the item id and Cartan decomposition
  found no previous statement. Searches for reductivity and tori found and reused
  the existing field predicates rather than duplicating them.

Source check: read the author-hosted AHLH PDF at
https://sites.math.washington.edu/~jarod/papers/iwahori.pdf. Theorem 4.1 and Remark
4.2 cover a split reductive model over an arbitrary DVR; Remark 3.5 supplies the
fixed-torus formulation. The node's more explicit smooth/affine/finite-type and
geometric-fibre hypotheses are retained verbatim in meaning. No correction or
STATEMENT-DISPUTED flag is needed.

Validation: both files compiled cleanly on the server through scompile.py. Every
universe and binder is explicit and autoImplicit is false. The statement is copied
verbatim into the lean record. Delivery preflight and repeated per-file compile
are run before pushing.

## New nodes

`def-sfb-split-torus-over-ring`, module
`Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing`, defines
`AlgebraicGeometry.RingGroupSchemes.multiplicative` and `splitTorus` for an arbitrary
commutative ring. Source: AHLH Remark 3.5, p.5. It supplies the ring-base notion
explicitly needed by the item's torus, not an alternative definition of field
reductivity or of geometric maximality. The two existing project constructions
`StandardGroupSchemes.multiplicative` and `MultiplicativeType.splitTorus` require
`[Field k]`; a DVR cannot satisfy that constraint. The general affine Hopf-algebra
API is reused directly. No group axioms are postponed and no arbitrary existence
choice is made. The field Laurent-polynomial node's Mathlib match is already the
general `LaurentPolynomial`, so it can be used over R without restating it.

Searches: msearch LeanSearch and LeanFinder with query `Split torus over a commutative
ring spectrum Laurent polynomial Hopf algebra finite product multiplicative group`
found precisely the Laurent Hopf algebra, comultiplication, counit and antipode,
which are used. msearch grep `splitTorus|SplitTorus|LaurentPolynomial|GrpObj` in
`AlgebraicGeometry/Group` found the generic affine group API, which is also used.
The new node records those original search records and their digests. Local rg
read the existing StandardGroupSchemes and ToriMultiplicativeType definitions,
found the field restriction, and checked the upstream multiplicativeGroup names:
the zeta example is field-only and the étale affine-line datum is an open subscheme
without a group structure. DAG and blueprint searches found no ring-base split-torus
definition (blueprint_refs search: zero blueprint nodes). This new node cites its
four underlying notion nodes and is itself added to the item's stmt_deps.

## Second reading by Q74

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
