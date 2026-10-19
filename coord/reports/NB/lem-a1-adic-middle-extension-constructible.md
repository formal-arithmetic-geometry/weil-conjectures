## Worker report

The module is `Sheaf.Paper.AdicMiddleExtensionConstructible`; its main statement is
`WeilConjectures.adic_middleExtension_constructible`. No statement correction, dependency
replacement, new independent notion, proof, or existing attachment is proposed. All four
recorded statement-dependency modules are publicly imported and their actual interfaces used.
The helpers in this module only spell out this node's geometric notation, finite-stage input,
and coefficient presentation. Every postponed proof is a named theorem with a source and
natural-language proof; the definitions have actual data.

Read the current node and its three proof steps; all four statement-dependency nodes and the
full recorded declarations; `CurveMiddleExtension.lean`, `SfConstructibleHeart.lean`,
`SfWeilSheafComplex.lean`, the common-stage pullback in `DerivedPullbackTensorHom.lean`;
the current blueprint `main-20261015/.../prop-a1-curve-boundary-sequence.proof.md`; and
Bhatt--Scholze Section 6.8, especially 6.8.4, 6.8.6, 6.8.8, 6.8.11, 6.8.14, 6.8.15.
The existing normalized coefficient comparison was read in
`IntegralStratifiedPerfectCharacterization.lean`, lines 340--480. Its inverse is used at
module-sheaf level, before applying the degree-zero single functor.

Hypothesis correspondence:

* The finite field, characteristic, chosen algebraic closure, and specified inclusion are
  `D : FiniteFieldDatum.{u}`. The prime is `l` with `[Fact l.Prime]` and `hl : l ≠ D.p`.
  `Ω` has `[Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]`, using exactly the size
  convention of the recorded lisse and middle-extension declarations.
* `c : MiddleExtensionCurve D` is the dependency's own bundle: `c.C` and `c.U` are over
  `Spec D.k₀`, separated and finite type; `c.j` is an open immersion with `DenseRange`;
  `c.C.hom` is smooth and `c.C.left.IsPureDimension 1`. No connectedness, properness,
  geometric irreducibility, nonemptiness or extra geometric condition is assumed.
* `Z₀`, `i₀`, `[IsClosedImmersion i₀.left]`, `[IsReduced Z₀.left]`, and `_complement`
  specify exactly the reduced closed complement. Finite type and quasi-compactness of
  `Z₀.hom` are consequences in `adicMiddleExtensionBoundaryProperties`, not binders.
* `D.geometricFiber` and `adicMiddleExtensionGeometricMap` use the same `Over.pullback`
  along `Spec (algebraMap D.k₀ D.k)`; `adicMiddleExtensionBoundaryFiber` only supplies
  the derived finite-type instances. Thus all of U, C, Z, j and i are the prescribed
  geometric base changes. No arbitrary geometric square is supplied by a caller.
* `E : Padic.FiniteCoefficientFields l Ω` and `F : AdicMiddleExtensionLattice ... E`
  present the lisse algebraic-coefficient input at an arbitrary finite stage. The lattice
  is precisely the existing `LisseIntegralSheaf`, not a newly defined lissity predicate.
  The recorded `LisseAlgebraicSheaf` is a localization of coefficient pairs, whose objects
  retain such finite-stage integral models (`lisseAlgebraicPair`,
  `lisseCoefficientPairModel`). The theorem quantifies over every model; no preferred
  representative or stable Frobenius lattice is required.
* `_θ` is the given isomorphism from the recorded common-stage geometric Frobenius
  pullback of `adicMiddleExtensionLisseObject` to that object. This is the exact fixed-pair
  Weil convention of `sfCommonStageWeilComplex`. In particular the Weil morphism and its
  inverse can live over a larger field than E, and theta need not preserve F integrally.
  Restricting theta to an integral automorphism would be an incorrect extra hypothesis;
  that restriction is not present here.

Conclusion correspondence:

* The witness `A` is an integral representative at E. Its displayed equality fixes its
  underlying derived object to `adicMiddleExtensionIntegralComplex ... j F.obj`.
  This inserts in degree zero the actual ordinary `middleExtensionIntegralSheaf` of
  the dependency, after scalar restriction by the inverse of the existing normalized
  completed coefficient comparison. It contains no Rj_* or right-derived functor.
  Thus the witness is the specified ordinary A, not an arbitrary constructible replacement.
* Its rationalization is `sfRationalConstructibleLocalization` and its algebraic-closure
  realization is `GeneralAlgebraicallyClosedCoefficients.inclusion E`. The first
  `sfCommonStageHeartProperty` is precisely A[0] in Sh_c(C,Ω). The integral witness is
  the explicit representative required to form this same recorded coefficient-category
  object; it is not a different conclusion about a freely chosen sheaf.
* The second heart predicate is on `commonStageDerivedPullback` along the geometric i,
  applied to that same A. This is exactly B=i*A in the recorded dependency convention.
  For the closed immersion this operation is ordinary inverse image on degree-zero
  sheaves, as Bhatt--Scholze Remark 6.8.15 and the node's open-closed interface specify.
* The node prescribes the induced Weil structures by reindexing and composition. Those
  prescriptions are retained in the theorem docstring. The assertion being formalized is
  their membership in `Sh_c`, whose recorded definition is a property of the underlying
  scalar complex, not a property of a chosen structure map. Consequently theta_A and
  theta_B do not occur in either heart predicate: forgetting their specified structures
  reduces the two membership assertions to exactly these two propositions. The module
  does not choose arbitrary replacement Weil isomorphisms, nor claim a new functor on
  fixed pairs. The explicit input `_θ` retains the source's Weil hypothesis.

Dependency declarations used:

* `Sheaf.Paper.CurveMiddleExtension`: `MiddleExtensionCurve`,
  `middleExtensionIntegralSheaf`, with its finite-level ordinary sections and module action.
* `Sheaf.Paper.SfConstructibleHeart`: `sfCommonStageHeartProperty` and its two recorded
  cohomological standard classes, on the intrinsic common-stage category.
* `Sheaf.Paper.SfWeilSheafComplex`: `sfCommonStageWeilFrobeniusPullback` and
  `sfWeilPrimeInvertible`; the latter derives prime invertibility on the actual fibres.
* `Sheaf.Paper.DerivedPullbackTensorHom`: `commonStageDerivedPullback`, with the
  canonical coefficient identifications and the source's finite-stage object formula.
* `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`:
  `integralDetailedCoefficientComparison`, uniquely fixed by all finite projections.
  Its finite-stage coefficient model is definitionally the recorded common-stage
  `AlgebraicallyClosedCoefficients.Coefficient` (the canonical Shrink model).
* The proof imports retain the recorded smooth-relative-dimension permanence and
  universally-open geometric tools. The rational open-closed cohomology node has no
  recorded module yet, so there is no module to import for that proof dependency.

Edge cases: c.j=id gives the same ordinary lisse sheaf and empty boundary; empty C gives
empty U and Z and vacuous density without a nonempty hypothesis; disconnected curves and
varying component ranks are allowed; the zero lisse lattice is allowed; integral torsion
is not silently ruled out; l=p is excluded exactly by hl; Frobenius eigenvalues need not
be integral units; identity coefficient stages and enlargement for the Weil morphism
remain available. All universes and binders are explicit, with autoImplicit=false.

Searches (actually run via msearch.py and direct rg):

* LeanSearch, "A lisse adic sheaf on a dense open smooth curve has constructible ordinary
  direct image and constructible boundary inverse image": eight hits, including
  Scheme.Modules.restrictAdjunction, TopCat.Sheaf.pullbackPushforwardAdjunction,
  Functor.IsDenseSubsite.full_sheafPushforwardContinuous, and constant-sheaf lemmas;
  none states this adic finite-stage theorem.
* LeanFinder, "The ordinary direct image of a lisse adic sheaf on a dense open smooth
  curve and its closed boundary inverse image are constructible Weil sheaves": eight
  hits about constructible scheme images/preimages and affine sections, no exact match.
* Loogle, `"middleExtension", "Constructible"`: zero hits.
* Mathlib grep, `middleExtension|constructible.*lowerStar|IsConstructibleSheaf` in
  AlgebraicGeometry: zero hits.
* Upstream rg for `middleExtension|ordinary.*[Dd]irect|lisse.*[Cc]onstructible` and grep
  for the item ID: upstream WeilSheaf.directImage uses its adic sheaf/derived-of-Weil
  presentation, not the recorded common-stage category and finite-extension convention;
  the item ID has no hit. Read WeilSheaf/OpenImmersion.lean and Adic/Constructible.lean.
* Project rg for the same ordinary-direct-image words, `middleExtension`, and intersections
  of the PBC and intrinsic constructible interfaces: found and reused
  CurveMiddleExtension and the normalized IntegralStratifiedPerfectCharacterization
  transport. No declaration already has the item's two intrinsic heart conclusions.

Validation: prescribed scompile.py, both sandbox and final module views. The initial full
module compiled cleanly; the final boundary-domain repair is compiled again before delivery.
No proofs were filled, and no live source or repository Git state was modified directly.

## Second reading by NB

Author's second pass under the direct-dispatch instruction forbidding other agents;
this is a self-check, not an independent review. The maintainer performs the independent
reading. Compared the node, current blueprint proof and actual dependency source to each
binder and conclusion above. The first draft had redundant finite-type and quasi-compact
binders on Z₀: removed them and supplied the derived boundary properties explicitly.
Checked that the equality fixing A uses j rather than id (id occurs only in the input's
lisse realization), that B pulls back the same A, and that the scalar transport is in
the inverse direction at module level. Checked arbitrary common-stage theta rather
than a lattice automorphism, no Rj_* in A, no additional geometric assumptions, no
file-local notation or instance, no hidden auto-bound parameters, and no non-sorry theorem
proofs. The heart-carrier interpretation above is essential: this is a constructibility
statement, and does not redefine the canonical Weil pushforward operation.
