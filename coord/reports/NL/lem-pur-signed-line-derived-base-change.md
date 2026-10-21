## Worker report

Module: `Sheaf.Algebra.Homology.SignedLineDerivedBaseChange`.
Main declaration:
`SheafOfModules.SignedLineDerivedBaseChange.signed_line_derived_base_change`.
One postponed theorem, with all eleven proof steps in its docstring; eleven transparent
helpers with actual data or propositions. No definition contains sorry. The node's
mathematical statement, proof and proof dependencies are unchanged.

### Hypotheses and every clause

- The sites are `C D : Type u`, with `Category.{v}`; their object and morphism
  universes remain independent. Ring sheaves and module sheaves have universe
  `max u v w`, with independent derived morphism universe `z`. Both sites fit in
  the coefficient universe. The sheaf-compose, sheafification and locally-bijective
  equivalence instances (including on slices) are the ordinary small-site structures,
  not restrictions on the ring or the lines. The size node is a metatheoretic convention.
- The presenting site functor is `U`, with `HasFiniteLimits C`, `HasFiniteLimits D`,
  `PreservesFiniteLimits U` and `_hcover : CoverPreserving J K U`.
  `U.IsContinuous J K` is the induced continuity used by Mathlib's pullback API.
- `R` and `S` are sheaves of commutative rings. The structural map is written
  in adjunct form `a : R_ring → U_* S_ring`. `rInv` and `rAdj` present the induced
  inverse image on ring sheaves, and `_ha` says its transpose `f⁻¹R → S` is an
  isomorphism. This is the source's structural ring isomorphism, not an assertion
  that the adjunct `R → U_*S` itself is invertible. Left-adjoint uniqueness identifies
  any such ring inverse-image presentation with the one induced by the geometric
  morphism. Thus no independent or arbitrary module pullback is assumed.
- `P` and `Q` use the recorded general-site module category. `_hP` and `_hQ`
  give a `CoversTop` family on whose slices the module is isomorphic to `unit`.
  This is precisely rank-one local freeness. A family indexed in the object
  universe suffices: all objects on which a trivialization exists form such a
  covering family, regardless of the size of an initially supplied family.
- `pull a` is the existing `ringedSitePullbackFunctor` with the published proof of
  existence of its adjunction. Its data are Mathlib's actual left adjoint to module
  pushforward. This is `S ⊗_{f⁻¹R} f⁻¹(-)`, characterized by that adjunction;
  `ringedSitePullbackSection` is insertion `1 ⊗ f⁻¹(x)`. `t` is its given line iso.
- The signed powers are the existing `signedLinePower`, with `scalarTensorPower`
  in nonnegative degrees and `homObj` into the unit in negative degrees. The stored
  powers are left associated. They encode the node's stipulated brackets through
  the canonical tensor associators, as explicitly allowed in proof step 3; no
  commutation or permutation of factors is used. Under these canonical rebracketings
  the recursion and evaluation maps are the same ordered tensor maps.
- The conclusion first supplies `hAdd`, `hLim` and `hCol`: F is additive and exact.
  These are conclusions, not extra exactness hypotheses. `F.mapDerivedCategory`
  and `F.mapDerivedCategoryFactors` consequently give the termwise unbounded D(F).
- The existential `T` is the integer-indexed family of isomorphisms. Its predicate
  `SignedLinePullbackNormalized` is the existing unit, degree-one, positive recursion
  and negative evaluation condition. The explicit clause
  `∀ T', SignedLinePullbackNormalized ... T' → T' = T` proves uniqueness from
  normalization alone, independently of the other properties in the existential.
- The unit condition tests every coefficient section on every site object and is
  multiplication by the structural map. The degree-one condition is exactly `t`.
  The positive condition tests all pure tensors and is therefore the canonical
  sheaf tensor comparison followed by the two preceding line maps. Adjunction
  and the tensor universal property extend these section formulas to sheaf maps;
  they do not assume that all sections of sheafification are globally pure tensors.
- The negative condition evaluates every pulled functional on every pulled positive
  section and equals the coefficient image of the original evaluation. It is the
  stated equation with sigma inverse and the unit comparison. All site objects
  are tested, hence all restrictions. Substitution of a local basis and its dual
  gives exactly the dual-basis assertion, including value 1 after coefficient pullback.
- `IsoNaturality` quantifies `b : P ≅ P'`, `c : Q ≅ Q'`, the commuting degree-one
  square, and any normalized target family. `signedIsoHom` is the recorded tensor
  map in positive degrees, identity on coefficients in degree zero, and
  precomposition with the inverse positive tensor map in negative degrees.
  The conclusion is precisely `T'_d F(b_d) = c_d T_d`.
- `ScalarNaturality` quantifies arbitrary `α : R → R'` and `β : S → S'`, a
  compatible `a'` with invertible transpose under the same ring inverse-image
  adjunction, the literal scalar extensions of P and Q, and their induced `t'`.
  The premise `SignedLineScalarPullbackSquare ... t t'` is exactly the degree-one
  induced comparison under balanced-tensor reassociation. The families B and E
  are arbitrary normalized canonical signed-power scalar identifications, not
  arbitrary isomorphisms. The conclusion is that same square in every integer
  degree. This is equivalent to the scalar extension of T under those canonical
  identifications. Neither α nor β is assumed flat or invertible.
- For each integer d, `γ` is a natural isomorphism
  `(- ⊗ P^[d]) ⋙ F ≅ F ⋙ (- ⊗ Q^[d])`. Its universally quantified pure-tensor
  formula is the canonical tensor-pullback comparison followed by `1 ⊗ T_d`.
  It is specified on all modules and all local sections, not just a free basis.
- `DerivedAction` uses exactly `KFlatFixedTensor.derivedTensor`, which abbreviates
  the published `siteDerivedTensorIndependentCoefficients`. Its fixed right
  argument is the degree-zero complex of the signed line. It asserts K-flatness
  and flat terms for both one-term lines. These facts are conclusions and place
  no restriction on the varying complex K.
- `collapse` is the existing total-tensor/degree-zero collapse followed by
  `siteSheafTensorRightIso` to the recorded sheafified sectionwise tensor.
  `ResolvingNormalization` fixes both localization isomorphisms by the actual
  `KFlatFixedTensor.representativeIso` on every K-flat flat-term representative.
  In formulas it says `c_E ; Q(collapse_E)⁻¹ = representative_E⁻¹`.
- `DerivedAction` now stores the final natural iso η and its uniqueness equation. It is
  `derivedLine R L ⋙ D(F) ≅ D(F) ⋙ derivedLine S M`. Its square on **every**
  `E : CochainComplex ... ℤ` identifies η with the termwise image of γ under Q,
  using the exact-functor factorization and the two normalized c's. Thus it is the
  canonical derived tensor-pullback map followed by `1 ⊗ T_d[0]`, rather than a
  bare existence of some isomorphism. Naturality is naturality in the full ordinary
  unbounded derived category. No boundedness, constructibility or finite-Tor
  assumption occurs. The representative normalizations and localization square
  pin this same map. The explicit family coherence clauses below separately assert
  its unit, tensor-power and evaluation equalities.
- The two `HEq` formulas express equality of morphisms whose endpoints are
  definitionally the same but presented by different total-complex functors.
  This avoids expensive elaboration of total-complex data. They assert equality,
  not merely existence of an identification of the endpoints or equality up to
  an unspecified automorphism.

### Dependencies used

The original statement dependencies were read with their signatures and docstrings:
`RingedToposMorphism` and `ringedSiteModules` in their recorded CategoryTheory modules;
Mathlib's `SheafOfModules.over`, `overFunctor`, `overMap` and `GrothendieckTopology.over`;
`cochainModulesMonoidal` in `CochainTensorUniverses`; `SheafOfModules.homObj` in
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`; Mathlib's
`DerivedCategory`/`HasDerivedCategory`; and
`site_derived_tensor_descent_independentCoefficients` with
`siteDerivedTensorIndependentCoefficients` in its recorded module.
The size convention has no declaration and is rendered by explicit universes.

The H2 repair replaces all four theorem edges that had been added merely to obtain
plain definitions. The item now directly cites these definition owners:

- `def-pur-signed-line-scalar-normalization-data` (new existing:true):
  `Sheaf.Paper.SignedLineScalarTensorTower`, `SheafOfModules.signedLinePower` and
  `SheafOfModules.SignedLineComparisonNormalized`.
- `def-pur-signed-line-pullback-normalization-data` (new existing:true):
  `Sheaf.Paper.SignedLineScalarPullbackSquare`, `SheafOfModules.SignedLinePullbackNormalized`
  and `SheafOfModules.SignedLineScalarPullbackSquare`.
- `def-sf-ringed-kflat-tensor-representative-data` (live existing:true):
  `Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated`, the five published
  `SheafOfModules.KFlatFixedTensor` definitions Modules, ordinaryTensor, totalTensor,
  derivedTensor and representativeIso.
- `def-pur-site-sheaf-tensor-presentation-data` (new existing:true):
  `Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients`,
  `SheafOfModules.siteSheafTensorRightIso`, siteTensorRightIso and tensorRightPresentation.
- `def-pc-flat-sheaf-modules`: `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`,
  `SheafOfModules.IsFlatOnSite`.
- `def-pc-kflat-complex`: `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`,
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `def-sp-scalar-tensor-comparison-data`:
  `Sheaf.Paper.InvertibleTensorScalarExtensionDefinitions`,
  `SheafOfModules.scalarTensorPowerMap` (and scalarTensorPower).

The original proof and proof_deps remain verbatim. Theorem nodes used by that proof
remain there, including site-derived-tensor descent. The four removed additions were
never used as theorem assertions in the proof and therefore are not substituted as
artificial new proof dependencies. All theorem-only module imports are retained as
ordinary imports; imports providing signature definitions are public. No dependency
record or published Lean module is changed.

### Edge cases

Checked before and during transcription: d=0 is the coefficient comparison;
d=1 is t; d=-1 is the evaluation-defined dual; positive recursion begins at 2
and negative degrees cover every `Int.negSucc`. For t multiplication by a unit b,
the comparison is multiplication by b^d, with b inverse in degree -1. Identity
site/coefficient/line maps remain allowed. The nonflat square Z → Z/2 on both
coefficient rings satisfies ScalarNaturality with identity structural maps: no
flatness premise was introduced. Zero coefficient rings and the zero module
(which is a rank-one line over the zero ring) remain allowed. Empty covers in
the degenerate topos remain allowed by CoversTop. The variable E in the derived
square is an entirely unbounded complex. Object, Hom, coefficient and derived
morphism universes were kept explicit, with no equation u=v.

### Searches

- `msearch.py ... leanfinder` with “An isomorphism of pullback line sheaves extends
  uniquely to signed tensor powers and unbounded derived tensor”: eight hits,
  mostly `pullbackObjFreeIso`, its naturality and `pullbackIso`; none states this node.
- `msearch.py ... loogle` with `SheafOfModules.homObj, Functor.mapDerivedCategory`:
  no hits; the service does not index the project's `homObj` name.
- `msearch.py ... grep` with `signedPower|signedLine|signed.*tensor`: no Mathlib hits.
- `msearch.py ... leansearch` with “Signed tensor powers of a line sheaf pull back
  compatibly with derived tensor products”: eight ordinary module tensor-power,
  linear-equivalence and complex-sign results, none for this sheaf/derived assertion.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf` and the upstream-name index for the
  item id and prospective full declaration names found no exact declaration.
- Concept searches `signedPower|signed.*[Pp]ower|Signed.*[Pp]ower|signedLine|SignedLine`
  in both source trees found the existing signed-line tower and scalar/pullback
  interfaces. These are reused; their theorem is an ordinary scalar square and
  does not contain the exact unbounded derived action stated here.
- Read the current main-20261015 Powers and duals paragraph and the complete local
  Stacks 07A4 statement/proof (sites-cohomology.tex, lemma-pullback-tensor-product),
  as well as the recorded finite-free-dual-pullback proof and its local evaluation
  characterization. No statement correction or STATEMENT-DISPUTED flag is needed.

## Second reading by NL

This is a second pass by the dispatcher-started worker; no other agents were started,
as instructed. The maintainer performs the independent reading on the delivery.
I reopened the node and the complete module, matched each hypothesis and clause as
listed above, and checked the structural-iso orientation, all signs and all four
normalization clauses. The second pass added explicit uniqueness among **all**
normalized families, so the outer existential's additional derived properties do
not accidentally weaken the normalization uniqueness assertion. It also checked
that the scalar premise uses the actual induced degree-one square, rather than
assuming the desired square in every degree; that inverse duals are contravariant;
that exactness and K-flatness are conclusions; and that the derived functors are
the published K-flat ones with their representative normalization. The sole use of
HEq changes elaboration of endpoint presentations, not the equality asserted.
That earlier pass missed the explicit derived coherence equations; the repair self-check below supersedes that claim.

### Previous validation (before the return)

Compiled using scompile.py only. Both the sandbox and actual library module name
passed with no warnings. The final import set took 37.6 and 33.2 seconds respectively,
within the unchanged 60-second limit. `deliver2.py --no-push` then passed server
preflight and compilation (dry-run commit a29a0b5cca6). The delivery wrapper repeats
these checks when pushing the packet.

## Repair of H2 and H3

H2 is repaired by the seven definition-owner edges listed above, including three new
existing:true nodes. No definition is copied and no theorem node is added just to own
a helper. The live node has no lean record; comparison with it confirms that only
stmt_deps and lean change. The saved returned module is retained except for the derived
coherence interface, and the accepted hypotheses, scalar and iso naturality, exactness,
pure-tensor gamma formula, collapse and ResolvingNormalization are preserved.

H3 is repaired by choosing gamma and DerivedActionData simultaneously for all integer
degrees, and conjoining `DerivedFamilyCoherence` for this same family. DerivedActionData is the ordinary product of cR, cS and eta (projections .1, .2.1,
and .2.2). DerivedAction is a proposition on those data, with the former witnesses
hL/hM/hLf/hMf, representative normalizations, localization square, and explicit eta
uniqueness. This avoids generating expensive auxiliary structure declarations.
No proof or data is manufactured.
`DerivedLineConstraints` is a proposition specifying the following canonical constraints on each side:

- The ordinary-unit pure-tensor equation pins x tensor r to r*x, and the right-unitor localization equation pins
  the derived right unitor after Q using c_0 and that actual ordinary map.
- The ordinary-product pure-tensor equation pins ((x tensor y) tensor q) to x tensor (y tensor q),
  so `product` is precisely the derived associator followed by the one-term
  identification of P^[m] tensor P with P^[m+1], for m=n+1. Its normalization
  equation uses c_m, c_1 and c_(m+1), with the existing collapse and
  representativeIso normalizations carried by DerivedAction.
- The ordinary-evaluation pure-tensor equation pins ((x tensor phi) tensor y) to phi(y)*x on every
  object and every restriction. The evaluation localization equation pins its derived
  contraction through c_(-m) and c_m. It is the ordered negative-positive
  evaluation in the node, with no symmetry or factor permutation introduced.

`DerivedFamilyCoherence` then asserts on EVERY derived object X:
(a) eta_0 ; rightUnitor_S = D(F)(rightUnitor_R);
(b) D(F)(product_R,m) ; eta_(m+1) = eta_1 at (X tensor P^[m]) ;
    (eta_m tensor 1) ; product_S,m;
(c) D(F)(evaluation_R,m) = eta_m at (X tensor P^[-m]) ;
    (eta_(-m) tensor 1) ; evaluation_S,m.
Here m=n+1 ranges over every positive integer. These are equalities of morphisms
with identical endpoints; naturality is inherited from the stored natural maps.
The normalizations of the constraints are explicit on every complex, and on K-flat
flat-term representatives c is exactly representativeIso/collapse. Thus existential
constraints cannot absorb a noncanonical automorphism. These clauses supply precisely
the compatibilities used by det-prop-sfb-cartesian-coefficients-twists, proof step 4.
No new boundedness, flatness of coefficient maps, or restriction on X is added.

## New nodes

`def-pur-signed-line-scalar-normalization-data` owns the two existing definitions of
signed powers and normalized scalar comparisons in SignedLineScalarTensorTower.
It cites the existing power-map and canonical scalar-map owners and internal Hom.
Source: Stacks 03EK, 04TT, 0GMX and the blueprint Powers and duals paragraph.

`def-pur-signed-line-pullback-normalization-data` owns the two existing predicates
for normalized pullback families and scalar/pullback squares in SignedLineScalarPullbackSquare.
It cites the first new owner and existing ringed morphism/module definitions. Source:
Stacks 03EL, 0GMX and the blueprint Powers and duals paragraph.

`def-pur-site-sheaf-tensor-presentation-data` owns the existing siteTensorRightIso,
tensorRightPresentation and siteSheafTensorRightIso in TensorColimitsIndependentCoefficients.
It asserts no colimit-preservation theorem. Source: Stacks 03EK, tensor by sheafification.

For all three, the additional searches are stored verbatim in mathlib_searches:
LeanSearch “Signed powers of a line sheaf with normalized scalar and pullback comparisons”
gave 8 unrelated vector-field/sign/presheaf-pullback hits; Loogle “SheafOfModules,
tensorRight” gave 0 (unknown identifier tensorRight); LeanFinder “Canonical comparison
of sheafified sectionwise tensor and monoidal sheaf tensor” gave 8 generic sheaf
monoidal/sheafification hits, without these module presentation isomorphisms; Mathlib
grep “signedLinePower|SignedLine.*Normalized|siteSheafTensorRightIso” gave 0.
Project rg located the reused definitions; definition-node rg found no owner of these
names; blueprint_refs search “signed line” and “tensor presentation” each gave 0.
The live representative-data node was found and reused, not duplicated.

### Repair self-check

Reopened the node, complete file and source Powers and duals paragraph. The source
states exact monoidal pullback, and the node explicitly requires the three derived
normalizations. The previous report had claimed these followed implicitly from the
localization square; the returned H3 correctly requires their equations in the
statement. Those equations are now explicit for the same eta, and each ordinary and
derived constraint has its normalization. Checked n=0 gives m=1, degrees 0, 1 and -1;
all higher positive and negative degrees are included. The zero ring, empty covers,
nonflat scalar maps and unbounded X cases listed above are still admitted. There is
no statement correction, changed proof plan or disputed clause. As instructed no
other agent was started; this is the worker self-check, and the maintainer performs
the independent review.

### Repair validation

The final proposition/product presentation compiled cleanly with scompile.py only:
49.6 seconds under the sandbox module name and 46.6 seconds under the actual library
module name, within the unchanged 60-second limit. No warning was emitted. The temporary
profiler option and structure-generation experiments were removed. There is one theorem
sorry, no hollow definition, no auto-bound variable, and no line over 100 characters.
The failed dry run's two new-node citation diagnostics were repaired by separating the
ringed-morphism and module-category citations into their individual [id] references.
The item changes only lean and stmt_deps; statement, proof and proof_deps are identical
to the current live node. The three new nodes bind existing declarations only.
