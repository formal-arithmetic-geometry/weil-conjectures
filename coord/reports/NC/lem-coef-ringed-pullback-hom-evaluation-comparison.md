## Worker report

The module `Sheaf.Paper.RingedPullbackHomEvaluationComparison` defines the requested
comparison by actual tensor-Hom transposition and states its four compatibility
identities. Its only postponed theorem is
`CategoryTheory.RingedDerivedComparisons.ringedPullbackHomEvaluationComparison`.
Every definition has explicit data; the theorem's proof is `sorry`.

I read the item, all five original statement dependencies and their recorded
signatures/docstrings, the additional presentation dependencies, and the proof
dependencies. There is no repair note for this item. The source places read are
`sites-cohomology.tex`, `lemma-pullback-tensor-product` (07A4),
`lemma-internal-hom` (08J9), `lemma-internal-hom-composition` (0A98),
`section-hom-complexes` (0A8X), `lemma-compose` (0A90), and `lemma-composition`.
The compatibility identities follow the item's agent calculation, rather than
being attributed verbatim to one of those Stacks lemmas.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Small ringed sites with commutative coefficient sheaves | `X Y : Site.{u,w}`: `C : Type u`, `SmallCategory C`, topology `J`, and `A : Sheaf J CommRingCat.{u}`. `u` and the derived-category universe `w` are explicit. |
| A morphism f from the B-site to the A-site | `f : Morphism X Y`, the existing `RingedToposMorphism X.ring Y.ring`; source coefficients B are `X.A`, target coefficients A are `Y.A`. This includes the geometric adjunction, finite-limit preservation and structural ring map. |
| Use Lf* on the unbounded module derived categories | `l : AdjointLift f` and `l.edge.left : Y.D ⥤ X.D`. `Site.D` is the ordinary unbounded `DerivedCategory` of the recorded module category. The edge includes the universal left-derived comparison for scalar-extension module pullback. |
| Fixed closed derived tensor-Hom structures | `X.closed`, `Y.closed`, `X.model`, `Y.model`, the signed coherence records and symmetries are the existing witnesses recorded by the closed-structure dependency. `pullbackHomFunctor Z` is only an abbreviation of `derivedInternalHomOfUniverses Z.J Z.A`, not a new Hom construction. |
| Canonical derived tensor comparison | `pullbackHomTensorModel Z` restricts `Z.model.comparison` along the actual inclusion from flat-term K-flats into all K-flats. `pullbackHomTensorator l U V` is the inverse component of `l.edge.tensorComparison` for these two restricted models. It is therefore exactly the canonical map FU tensor FV to F(U tensor V), with the representative characterization retained. |
| Define beta on P,Q in D(A) | `ringedPullbackHomComparison l P Q`, for arbitrary `P Q : Y.D`. Its type is F(H_A(P,Q)) to H_B(FP,FQ). Its body is `X.closed.transpose` applied to `pullbackHomTensorator l (H_A(P,Q)) P ≫ F.map (Y.closed.evaluation P Q)`. |
| Natural in both inputs | First conjunct, for every `a : P' ⟶ P` and `b : Q ⟶ Q'`. The source Hom morphism is `Prod.mkHom a.op b`; the target Hom morphism uses `(F.map a).op` and `F.map b`. Thus the first variable is contravariant. |
| Preserves evaluation as derived morphisms | Second conjunct: tensor `(beta,identity)` followed by `X.closed.evaluation` equals the canonical tensorator followed by the image of `Y.closed.evaluation`. All its maps are in `X.D`. |
| Preserves tensor-Hom transposition | Third conjunct, for every `T P Q : Y.D` and every `t : Y.closed.tensor.obj (T,P) ⟶ Q`. It states F(transpose_A(t)) followed by beta equals transpose_B(c followed by F(t)). The arbitrary parameter T is retained. |
| Preserves internal composition | Fourth conjunct: `c ≫ F.map (Y.closed.composition P Q T) ≫ beta` equals tensor of the two betas followed by `X.closed.composition`. The existing `CoefficientClosedStructure.composition` is exactly transposition of the associator and two evaluations. |
| Representative evaluation and composition use the usual signed total tensor and Hom-complex differentials | Last two conjuncts, `RingedHomSignedRepresentatives X` and `RingedHomSignedRepresentatives Y`. For all ordinary complexes L,M,N they assert existence of actual chain maps from `coefficientTotalTensor (homComplex L M,L)` to M and from `coefficientTotalTensor (homComplex M N,homComplex L M)` to `homComplex L N`, with the pure-generator equations h tensor x maps to h(x), and g tensor h maps to gh. Actual Hom product projections are used by `ringedHomSectionApply`. Being morphisms of these fixed signed complexes enforces the chain-map identities with d(h)=d h-(-1)^r h d and d_total=d tensor 1+(-1)^s 1 tensor d; the formulas insert no extra sign. The existing `model.uncurry_model` pins the derived evaluation to this componentwise evaluation, and derived composition is defined by iterating that same evaluation. |
| No invertibility of beta claimed | Neither the definition nor the theorem has an `IsIso` condition or an inverse for beta. The inverse used in its definition belongs only to the canonical tensor comparison. |

`AdjointLift f` is a presentation witness for the Lf* already named in the node,
not a flatness, boundedness, or Hom-preservation assumption. The already recorded
`adjointLift_exists f` provides it for every ringed-topos morphism. The theorem
holds for every such witness, so it does not select an arbitrary functor from a
bare existence assertion. Likewise, the tensor-model restriction is constructed
from the fixed comparison rather than chosen from a `Nonempty` result. The
canonical tensor comparison is determined by its representative universal
property. No full monoidal lift is assumed: the proof plan obtains its
coherence from `tensorLift_exists` on the explicitly restricted models.

The already landed `def-sfb-ringed-derived-comparison-data` and the new
`def-sf-ringed-derived-adjoint-lift-data` are added to `stmt_deps`, since their
presentation types occur in the signature. The existence theorem
`lem-sfb-ringed-derived-adjoint-lift` remains in `proof_deps` only. All helpers
belong to this item's single comparison and are listed in its `lean.declarations`.
The mathematical statement and Lean module are unchanged.

Dependency declarations used, with their defining modules:

- `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`:
  `CategoryTheory.ringedDerived_closed_symmetric_monoidal` and
  `CategoryTheory.RingedDerivedTensorCoherence`. Its public tensor-Hom-model
  interface supplies `WeilConjectures.CoefficientClosedStructure.evaluation`,
  `.transpose`, `.composition`, and `CoefficientTensorModels.comparison`.
- `Sheaf.Paper.RingedTopoiDerivedPullback`:
  `SheafOfModules.ringedTopoiDerivedPullback`, represented in the signature by
  the existing edge and its `isLeftDerived`/`epsilon` fields.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`.
  Its uniquely characterized comparison is used through
  `SheafOfModules.RingedTensorEdge.tensorComparison` from
  `Sheaf.Paper.RingedTensorSquarePresentation`, publicly imported by the
  recorded comparison-data module.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`;
  `coefficientTotalTensor` is its existing sheaf-tensor bifunctor formulation.
- `WeilConjectures.Algebra.Homology.HomComplex`:
  `CategoryTheory.homComplex`; its actual projections are exposed by the
  existing `coefficientHomComponent` from
  `Sheaf.Paper.CoefficientHomRepresentativeEvaluation`, publicly imported by
  the recorded closed-structure and comparison-data modules.
- `Sheaf.SixFunctors.RingedDerivedComparisonData`:
  `CategoryTheory.RingedDerivedComparisons.Site`, its `.D` and `.corner`, and
  `Morphism`.
- `Sheaf.SixFunctors.RingedDerivedAdjointLift`:
  `CategoryTheory.RingedDerivedComparisons.AdjointLift`, `adjointLift_exists`.
- Proof imports also retain the recorded
  `Sheaf.SixFunctors.RingedDerivedTensorLift.tensorLift_exists` (declaration
  namespace `CategoryTheory.RingedDerivedComparisons`),
  `CategoryTheory.RingedDerivedNative.closedAdjunction` from
  `Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction`,
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients` from
  `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`, and
  `CategoryTheory.derivedInternalHomOfUniverses` from its recorded module
  `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`.

Searches actually run:

- `msearch.py leanfinder`, query “Strong monoidal functor internal Hom comparison
  defined by evaluation preserves currying and internal composition”: eight hits,
  including `expComparison_ev`, `uncurry_expComparison`, and cartesian closed
  functors. These require cartesian tensor, unlike the module derived tensor.
- `msearch.py loogle`, query
  `CategoryTheory.Functor.LaxMonoidal.ihomComparison`: unknown identifier in the
  service's Mathlib index; no usable result (unavailable for that identifier).
- `msearch.py grep`, query `ihomComparison|homComparison`, restricted to
  `CategoryTheory/Monoidal`: zero Mathlib hits.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for Hom/evaluation comparison
  names located the upstream generic lax-monoidal `ihomComparison`. I read
  `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic`, in particular
  `ihomComparison`, `ihomComparison_ev`, `ihomComparison_app_eq_curry`, and
  `map_pre_app_comp_ihomComparison_app`. This API uses tensor-left closed
  structure and its chosen `ihom`, whereas the dependency fixes tensor-right
  transposition with the recorded sheaf-derived Hom bifunctor. It does not
  itself state this ringed-site comparison with the representative normalization
  and internal-composition clause. The new definition applies the existing
  recorded transpose directly; it defines neither tensor nor Hom again.
- `rg` for the seven new full-name suffixes in `lean/WeilConjectures`,
  `lean/Sheaf` and `dag/lean_names_upstream.json`: no matches.
- `grep -rn` for this item's id in `lean/WeilConjectures`: no matches.
- Searches for evaluation/composition of Hom complexes found the existing
  Hom product projections and the fixed componentwise uncurrying interface;
  these are reused, rather than replacing the actual complexes by arbitrary
  complexes with the same names.

Edge cases checked before finalizing the statement:

- Identity morphism: the comparison is the transpose of the existing evaluation
  after the canonical identity tensor identification, with the stated orientation.
- Zero P, Q or parameter T: all expressions remain typed and reduce to zero maps
  on representatives. No nonzero hypothesis appears.
- Arbitrary coefficient maps, including nonflat maps on a point: the scalar
  extension edge is derived on K-flats; no exactness or flatness of the ring map
  is assumed. A general beta need not be an isomorphism.
- Empty site: the universal section equations have no test objects, and all the
  categorical maps still have their correct domains. No terminal object of the
  site is assumed.
- Unbounded complexes: Hom uses all integer product factors and tensor uses all
  integer direct-sum summands. There is no boundedness or perfectness restriction.
- Odd and negative degrees: for s odd the chain-map composition identity is
  d(gh)=(dg)h-g(dh); for even s its second summand is positive. The actual
  integer-indexed signed complexes enforce these signs, also below degree zero.
- Variance/orientation: a goes from P' to P, the first Hom variable uses a.op,
  the tensorator goes from FU tensor FV to F(U tensor V), and composition starts
  with H(Q,T) tensor H(P,Q), in that order.

Validation: `scompile.py NC lem-coef-ringed-pullback-hom-evaluation-comparison`
compiled both the sandbox module and its library-path presentation successfully,
with no errors or warnings (15.4 seconds and 21.4 seconds, respectively).
No theorem was proved, and there is no STATEMENT-DISPUTED finding.

## Return repair

The independent review of immutable head `6bf4bda2afc2` returned one H2 point:
`l : AdjointLift f` uses a structure, not the conclusion of `adjointLift_exists`.
Added the requested definition node on that exact existing structure; replaced
the theorem in `stmt_deps` and retained it in `proof_deps`. No dependency record
or Lean source is modified. The initial saved-packet dry run passed at
`e8728218bc2`; this repair is substantive metadata work beyond that dry run.

## New nodes

`def-sf-ringed-derived-adjoint-lift-data` records the existing
`CategoryTheory.RingedDerivedComparisons.AdjointLift` in
`Sheaf.SixFunctors.RingedDerivedAdjointLift`, with `existing: true`, the verbatim
structure header, and only `def-sfb-ringed-derived-comparison-data` as its
statement dependency. Its sources are Stacks 03D7 (ordinary module adjunction),
06YY (flat-term K-flat derived pullback), and 07A6 (derived adjunction). Read
those statements and proofs locally and the entire structure/docstring both
locally and through `scompile.py --source`. LeanSearch and LeanFinder each
returned eight generic derived/ordinary adjunction hits. The Mathlib grep
returned two unrelated lifting-square hits. Searches of the upstream source,
Sheaf and DAG found the existing structure and its existence theorem, but no
definition node for the structure. The exact search logs are stored in the new
node. This attachment introduces no duplicate definition or new Lean module.

## Second reading by NC

Repair self-check, using the supplied independent review as the external
reading: I reread the item and the unchanged Lean module. Beta is the transpose
of the canonical restricted-model tensorator followed by pulled-back evaluation.
The first conjunct quantifies over `a : P' ⟶ P` and `b : Q ⟶ Q'`, so its first
input is contravariant; the second is the evaluation identity; the third keeps
arbitrary `T` and `t`; the fourth is the internal-composition identity. The last
two conjuncts give the stated signed representative formulas. There is no
invertibility condition on beta. These clauses and all original hypotheses are
unchanged, as accepted by the independent return.

For the new definition I matched every field: `edge`; `inverse_eq`, `direct_eq`,
`geometric_adjunction`, `pushforward_eq`; `structural_map`;
`ordinary_adjunction`; `right_additive`; `eta`, `isRightDerived`,
`eta_injective`; `epsilon_flat`; and `canonical_adjunction`, respectively, to
the edge, identifications, structural-ring normalization, underlying-sheaf Hom
formula, additivity, universal right-derived comparison with K-injective
invertibility, flat-term K-flat invertibility, and inverse-transpose formula
in its node. All variables and universes are explicitly bound in the existing
structure header and owning module. No tensor coherence or existence claim is
added to the definition. Identity morphisms, empty sites, zero complexes,
unbounded complexes and nonflat coefficient maps introduce no extra restriction.
The H2 mismatch is repaired by the new definition dependency; the existence
theorem is retained for the proof. The review's representative-evaluation
advisory is recorded: `RingedHomSignedRepresentatives` itself is not tied to
`X.closed.evaluation`; the unchanged proof plan uses the existing
`model.uncurry_model` normalization for that identification.
