## Worker report

The module `Sheaf.SixFunctors.RingedFiniteFreeHomBaseChange` states
`CategoryTheory.ringedFiniteFreeHomBaseChange`, with `sorry` as its only theorem
proof. The helper `CategoryTheory.ringedFiniteFreeScalarSection` is a real
construction: the module-sheafification unit on `s ⊗ x`, transported by the
specified ordinary scalar-extension object equality. It introduces no independent
notion or unspecified section map.

The item statement is unchanged. Its statement dependencies gain only the already
landed `def-coef-ringed-tensor-hom-model`. That node supplies the canonical
representative characterization of the derived tensor and its evaluation; it is
reused, not copied. No new node or dependency repair is needed.

Hypotheses and objects, clause by clause:

- The small site is `{C : Type c} [Category.{v} C]` with
  `J : GrothendieckTopology C`. The module/coefficient universe is `max c v r`;
  it contains both site universes, without equating them. Sheafification,
  locally-bijective equivalences, and `HasSheafCompose` are the standard
  infrastructure for the abelian module category, not extra geometric
  hypotheses. A precoverage site is used through its generated Grothendieck
  topology, as in the recorded site definition.
- The commutative ring sheaves and their homomorphism are
  `{R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S)`.
- Global finite freeness is exactly `hfree : ∃ d : ℕ, Nonempty (...)`:
  restrict the scalar sheaf `SheafOfModules.unit` over S by φ and identify
  it with `SheafOfModules.free (ULift (Fin d))` over R. Mathlib's `free` is
  the coproduct of copies of the unit sheaf. `ULift` only puts this finite
  index in the module universe. No positive-rank condition occurs.
- `SheafOfModules` with `derivedChangeRingIndependentCoefficients` is the
  recorded general-site module category, and `DerivedCategory` with its
  explicit `HasDerivedCategory.{w}` instances is the ordinary unbounded
  localization at quasi-isomorphisms.
- The existential ordinary functor `E` is fixed on objects by `h` and on
  maps by `_hm` to `changeOfRings` and `changeOfRingsHom`, including the
  equality transports. `_hE` makes its termwise complex functor available.
  These are specifications of the ordinary construction, not assumptions
  about P or Q. The existential `T`, `ε`, `_hT` give its universal left
  derived functor relative to `DerivedCategory.Q`. The recorded dependency
  expresses the same universal pair through the homotopy category; the
  quotient comparison transports that pair to Q. The second conjunct also
  states the canonical counit is invertible on all K-flat inputs.
- `AR` and `AS` are the existing closed tensor structures for the actual
  `derivedInternalHomOfUniverses`. `MR` and `MS` are their existing
  `CoefficientTensorModels`: they identify tensors naturally on K-flat
  representatives and normalize transposition by the actual Hom-complex
  evaluation and localized K-injective augmentation. Thus these are the
  ordinary derived tensor and tensor-Hom adjunction of the node, not
  freely chosen evaluations. Their existence is asserted in the conclusion,
  so it is not an extra hypothesis on the ringed site.

Conclusions, clause by clause:

- The natural isomorphism `α` has source `H_R ⋙ T` and target
  `T.op.prod T ⋙ H_S`. Its components are precisely
  `T(H_R(P,Q)) ≅ H_S(TP,TQ)`. A natural isomorphism makes every component
  invertible and includes contravariant naturality in P and covariant
  naturality in Q.
- `κ` is the total-complex scalar/tensor comparison. The first conjunct
  fixes it on every actual sheafified pure-tensor summand:
  `1 ⊗ (x ⊗ y)` goes to `(1 ⊗ x) ⊗ (1 ⊗ y)`.
  The maps are S-linear, so this fixes all scalars as well. Total-sum
  inclusions and the universal property of sheafification determine the
  chain maps from these values. Its inverse is the balanced multiplication
  formula `(s ⊗ x) ⊗ (t ⊗ y) ↦ st ⊗ (x ⊗ y)`.
- `μ` is the derived strong tensor comparison. The second conjunct fixes
  its square on every pair of K-flat complexes using the canonical
  counits `ε`, the tensor representative isomorphisms `MR.iso`, `MS.iso`,
  and the chain comparison `κ`. It also records that scalar extension
  preserves K-flatness, so the S-representative comparison has its stated
  domain. K-flat resolutions and localization determine the comparison
  on all derived objects; this is not an arbitrary natural isomorphism.
- The last conjunct, for all unrestricted derived P,Q, is the exact
  evaluation condition:
  `α.hom.app (op P,Q) = AS.transpose ... (μ.inv.app ... ≫ T.map (AR.evaluation P Q))`.
  This is the transpose of the extended evaluation pairing. The existing
  closed structure tensors as `H(P,Q) ⊗ P`; the node writes `P ⊗ H(P,Q)`.
  The signed symmetry of total tensors identifies these conventions, and
  their respective evaluations correspond under that symmetry. No sign or
  scalar factor is freely chosen in this equation.
- No basis is passed to the comparison: the only finite-free datum is the
  propositional existence `hfree`. The unique evaluation transpose and
  normalized tensor comparison establish the requested basis independence.
- P,Q range over the full derived categories. There is no boundedness,
  completeness, constructibility, Tor-amplitude, or perfectness hypothesis.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`; the module explains
  passage to `Precoverage.toGrothendieck` and its sheaves.
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`, transparently `SheafOfModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q`, and the
  comparison `DerivedCategory.quotientCompQhIso`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`:
  `SheafOfModules.derivedChangeRingIndependentCoefficients` and
  `SheafOfModules.derivedChangeOfRingsIndependentCoefficients`; objects,
  maps, universal derived pair and K-flat counit characterization are reused.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses`, the actual Hom-complex
  localization with independent site universes.
- `Mathlib.Algebra.Homology.BifunctorShift`:
  `CochainComplex.mapBifunctor`, used through `coefficientTotalTensor`.
- `Sheaf.Algebra.Homology.KFlat`:
  `CochainComplex.IsKFlatIndependentCoefficients`, the total-tensor
  acyclicity predicate; no private K-flat predicate is introduced.
- `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`:
  `CategoryTheory.ringedInternalHom_tensor_adjunction` (proof import and
  the source of the internal adjunction); its small-category API is not
  used to collapse the independent universes in this statement.
- `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`:
  `CategoryTheory.rhom_global_sectionsOfUniverses`, the Hom-set
  interpretation of the internal adjunction.
- `Sheaf.Paper.CoefficientRingedTensorHomModel`:
  `WeilConjectures.CoefficientClosedStructure`, `.tensor`, `.evaluation`,
  `.transpose`, `CoefficientTensorModels`, `.iso`,
  `coefficientTotalTensor`, and `coefficientTensorGenerator`; both tensor
  and evaluation are normalized on the recorded representatives.
- Proof dependencies also import `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
  (`CochainComplex.exists_isKFlatResolutionIndependentCoefficients`),
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality` (the
  recorded sheaf tensor interface), and Mathlib's sheaf change-of-rings
  (`SheafOfModules.restrictScalars`). The proof-only
  `lem-sfb-dc-hom-scalar-adjunction` has no Lean record yet, so there is
  no module to import for that proof step. Its complete node statement was
  read and its normalized adjunction/conservativity is named in the proof
  docstring; no missing statement object is assumed from it here.

Edge cases checked mathematically before finalizing:

- Rank zero: S is the zero module/ring sheaf, its module derived category
  is zero, and the comparison is the unique isomorphism. `Fin 0` and the
  empty coproduct are admitted.
- Identity map and rank one: the normalized comparison specializes to
  identity transport and extended evaluation, without a basis parameter.
- P=0, Q=0 and the empty site: both sides are zero, and the same tensor
  and Hom universal properties apply.
- Unbounded inputs: the argument only interchanges finite sums with
  products; it does not require an infinite-product exactness assumption.
  For a point site and S=R[ε]/(ε²), the comparison is the two-copy Hom
  comparison even for unbounded P and Q.
- Independent object and morphism universes remain independent throughout.

Searches for an existing statement:

- `msearch.py` LeanFinder, query “Finite free extension of ring sheaves
  commutes with derived internal Hom of arbitrary unbounded complexes”:
  eight hits, including `SheafOfModules.freeHomEquiv_comp_apply`,
  `mapFree`, and light-condensed monoidal structures. None states this
  unbounded derived change-of-rings comparison. Repeated in this resumed
  turn with the same result.
- `msearch.py` Loogle, query `"internalHom", "baseChange"`: zero hits.
- `msearch.py` Mathlib grep,
  `(internalHom|derivedHom|rhom).*(baseChange|finiteFree)|finiteFree.*(internalHom|derivedHom|rhom)`:
  zero hits.
- The retained LeanSearch query “Derived internal Hom commutes with finite
  free extension of a sheaf of commutative rings” returned eight ordinary
  sheaf-Hom/free-module results, including `CategoryTheory.sheafHom` and
  `SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom`; none
  gives the required arbitrary-unbounded statement.
- Direct `rg` in upstream `WeilConjectures` and the project's `lean/Sheaf`
  for `ringedFiniteFree(HomBaseChange|ScalarSection)` and finite-free
  derived-Hom/base-change patterns found no duplicate. The nearby
  `finiteFree_internalHom_exact_sequence` is an underived exact-sequence
  theorem; the strictly-perfect Hom lemma imposes perfectness and does
  not express this result. Upstream search for the exact item id found
  nothing. The existing coefficient tensor-Hom model was found, read in
  full at its used signatures, and reused as a landed dependency.

Source checked directly: `literature/stacks-project/sites-cohomology.tex`,
`lemma-internal-hom` (08J9) and `lemma-section-RHom-over-U` (08JA), lines
8874–8930. As the node explains, these tags supply the adjunction, while
this auxiliary finite-free specialization follows by the finite-biproduct
argument recorded in the node and the module's proof docstring.

Resumed-work repairs: the retained sandbox contained the module and search
log but no node copy or report and no completed delivery. The first compile
exposed a redundant `EssentiallySmall` inference path and missing explicit
universe arguments on the scalar-section helper calls. The final source
uses the canonical sheaf-composition infrastructure and supplies those
universe arguments explicitly. The normalized coefficient model already
covers the current statement; its representative characterization was
retained. Long lines were wrapped. No mathematical statement correction
or disputed statement is needed.

## Second reading by Q139

Independent maintainer reading of immutable delivery
b70a4c3bd2688e6a3a51d856a8c05487aef04793, performed on 2026-10-17.
This section records the maintainer's reading, not an assertion that the original
worker had a separate second reader.

I read the item and all ten statement-dependency records in the immutable
snapshot, the complete delivered Lean module, and the Worker report. I opened
the used declarations and their docstrings in the read-only Q139 clone and pinned
Mathlib/upstream source. In particular I read CoefficientClosedStructure,
CoefficientTensorModels and its uncurry_model, coefficientTensorGenerator,
CoefficientTensorModels.iso, and the underlying Hom representative evaluation
and fixed localization/augmentation maps. These supply actual normalized
representatives, rather than arbitrary comparison maps.

Clause-by-clause findings:

- Site and rings: C : Type c, Category.{v} C, J, R, S and phi give an arbitrary
  ringed site and commutative ring-sheaf homomorphism. Passing from covering
  families to their Grothendieck topology does not change module sheaves.
  The sheafification, locally-bijective and ring-forgetting instances are
  standard infrastructure on a site small in max c v r, not geometric
  restrictions. The object and morphism universes are independent.
- Finite freeness: hfree restricts the unit S-module to R and identifies it
  with free (ULift (Fin d)). Mathlib Free.lean:39 defines free as a coproduct
  of units. Thus this is precisely global finite freeness, with d any natural
  number, including zero; no basis is supplied to the comparison itself.
- Module and derived categories: ringedSiteModules is transparently
  SheafOfModules. DerivedCategory and HasDerivedCategory are Mathlib's
  ordinary localization at quasi-isomorphisms, not a bounded or completed
  subcategory. The common morphism universe w is a choice of size for the two
  derived categories; it does not equate c and v.
- Scalar extension: existential E has both its objects and maps fixed to
  changeOfRings/changeOfRingsHom by h and _hm. T and epsilon satisfy the
  left-derived universal property for this precise termwise functor. The
  second conjunct makes epsilon invertible on K-flat representatives.
  This is the recorded derived-change-of-rings construction, presented
  through Q rather than Qh; the homotopy-quotient comparison transports it.
- Tensor and internal Hom: H is the recorded derivedInternalHomOfUniverses,
  computed by actual Hom complexes and K-injective replacement. AR, AS, MR
  and MS are existential output data, not hypotheses. MR/MS require the
  canonical representative uncurrying equation, so evaluation cannot be
  replaced by an unspecified pairing. The older internal-Hom adjunction
  dependency uses SmallCategory; the statement does not force the current
  independent site universes to fit that legacy API.
- Canonical tensor comparison: kappa is fixed on all actual total-complex
  pure-tensor summands by the first conjunct. S-linearity fixes arbitrary
  scalars; sheafification and total-sum universal properties determine the
  maps. The scalar-section helper is exactly the sheafification unit on
  s tensor x, followed by the object-equality transport, with real data.
  The second conjunct fixes mu through kappa, epsilon and MR/MS on every
  pair of K-flat complexes. K-flat resolutions then determine it on the
  derived category. No arbitrary isomorphism is substituted for this map.
- Conclusion and variance: alpha is a natural isomorphism H_R followed by T
  to T.op.prod T followed by H_S. Hence all components are invertible and
  have exactly the contravariant/covariant naturality claimed. Its final
  equation is the transpose of mu inverse followed by T of evaluation.
  The tensor order is Hom tensor P, as in Stacks equation-internal-hom;
  signed symmetry gives the node's P tensor Hom convention. This changes
  neither the canonical map nor its normalization.
- Basis independence and unrestricted inputs: the equation defining alpha
  contains no chosen basis, and P,Q range over all derived objects. There
  is no boundedness, completeness, constructibility or perfectness premise.

Source and proof checks: I read sites-cohomology.tex, section-internal-hom
and equation-internal-hom (starting at line 8836), lemma-section-RHom-over-U
(08JA, line 8874) and lemma-internal-hom (08J9, line 8899). These prove the
unbounded adjunction used here; the item correctly calls its finite-free
specialization an auxiliary assertion. I also checked definition-K-flat
(06YN, line 2999), lemma-derived-tor-quasi-isomorphism-other-side (06YT,
line 3233), lemma-derived-base-change (06YY, line 3585), the module-sheaf
definition in sites-modules.tex:782, the site definition in sites.tex:679,
and the signed total complex in homology.tex:4195.

The five item proof steps are sound: the finite-free basis gives UTX = X^d;
the scalar-Hom adjunction gives U H_S(TP,TQ) = H_R(P,UTQ); the tensor-Hom
right adjoint preserves finite products; the normalized comparison has
matrix entries delta_ij; conservativity proves invertibility, with naturality
and basis independence coming from the original transpose. I read the
statement of lem-sfb-dc-hom-scalar-adjunction in sec-six-functors-basics:
it supplies precisely the normalization and conservativity used. It is a
proof dependency, not a missing object needed to type this stage-2 statement;
its lack of a Lean record does not justify adding an assumption or blocking
this delivery. The docstring records each of these proof steps and the
representative construction required for kappa and mu.

Edge cases: Fin 0 is allowed, and gives the zero S-module category; the
matrix argument remains the empty-biproduct identity. Zero inputs and the
empty site require no nonemptiness assumption. Identity and rank-one scalar
extension use the same normalization. The finite-rank argument also covers
nonreduced finite free algebras, such as R[e]/(e^2), and arbitrary unbounded
inputs: it only exchanges finite products and finite sums. No characteristic
restriction or equality of site object and arrow universes was inserted.

One-definition check: I inspected the report's LeanSearch, LeanFinder,
Loogle and grep records and independently searched pinned Mathlib,
WeilConjectures and Q139 lean/Sheaf using ringedFiniteFree and the patterns
finiteFree.*(internalHom|derivedHom|rhom) and
(internalHom|derivedHom|rhom).*(baseChange|finiteFree). The nearby
finiteFree_internalHom_exact_sequence is underived and the strictly-perfect
comparison has a perfectness hypothesis; neither duplicates this theorem.
All used notions come from the recorded dependencies. The only new helper
is the explicit scalar-section construction listed in lean.declarations.

Mechanical checks: lean.statement matches the theorem signature verbatim,
excluding its proof. autoImplicit is false; c, v, r and w are bound; there
are no lines over 100 characters. Both declarations have source/blueprint
docstrings. The one theorem has exactly the proof `by sorry`; the helper
contains no sorry. No new node, dependency rewrite, statement correction,
pro-etale substitute or citer audit is required.

Compiler evidence: reproduced with
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q139
lem-sf-ringed-finite-free-hom-base-change
snapshot/lean/Sheaf/SixFunctors/RingedFiniteFreeHomBaseChange.lean`.
The installed wrapper currently dispatches its overlay check to the server.
It returned exit 0, no warnings or errors: sandbox check 3.0 s, library
Sheaf/SixFunctors/RingedFiniteFreeHomBaseChange.lean 4.7 s. It reported its
private /dev/shm overlay; each invocation retained the 60-second limit.
No lake build, live Lean edit, direct ssh command, delivery or Git mutation
was performed. The earlier successful worker compile is not independently
recorded in the immutable report; this reproduced result supplies concrete
compiler evidence without inventing a historical run.

Findings and correction: the original second-reading section was only a
placeholder, and the report lacked a successful per-file compiler result.
Those are report defects (H1/H11), repaired here by this independent reading
and compiler evidence. The mathematical statement, Lean module and JSON
record need no changes. The full Worker report above is preserved.
