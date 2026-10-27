## Worker report

The module `Sheaf.AlgebraicGeometry.AffineEtaleNaiveCotangentPresentation` states
`AlgebraicGeometry.AlgebraicSpace.affine_etale_naive_cotangent_presentation` with
`sorry`. It compares the intrinsic algebraic-space naive cotangent object with the
termwise associated étale sheaf of the existing two-term polynomial-presentation
complex, by `Nonempty (… ≅ …)` in the SAME unbounded derived module category.
The mathematical statement, source, proof and proof dependencies are unchanged.
Four already landed definition nodes are added to `stmt_deps` to record actual owners:
`def-sfb-abelian-space-poincare-data` owns `Poincare.schemeModule` and the identity
chart; `def-trf-naive-cotangent-comparison-data` owns `Naive.Presentation` and
`Naive.complex`; `def-sfb-smooth-integral-group-space` owns `groupSchemeMap`;
`def-trf-scheme-algebraic-space` owns `schemeSpace`.
These declarations are used directly, without a second identity-chart construction,
second conormal module, second differential, or second two-term ring complex.

Clause-by-clause correspondence:

- Commutative rings R and B and their homomorphism: `{R B : Type u}`, `[CommRing R]`,
  `[CommRing B]`, `[Algebra R B]`. The map is `algebraMap R B`; every ring homomorphism
  gives this datum by `RingHom.toAlgebra`.
- Arbitrary set T and P=R[x_t]: `{T : Type u}` and `MvPolynomial T R`. There is no
  `Finite`, `Fintype`, enumeration or finite-presentation hypothesis. A common
  ambient universe bounds the input sets; it can be taken as large as necessary.
- Surjective R-algebra homomorphism alpha: `(α : MvPolynomial T R →ₐ[R] B)` and
  `(hα : Function.Surjective α)`. `affineCotangentPolynomialPresentation` packages
  precisely this map with the polynomial coefficient map and its actual commuting
  triangle; its data are explicit, not chosen from a theorem.
- I=ker alpha and its B=P/I action: `Naive.conormal` in the imported `Naive.complex`
  is `Algebra.Extension.Cotangent` for the extension of alpha. This is Mathlib's
  actual kernel conormal quotient, with its action descended along the surjection.
  No arbitrary ideal or identification is a hypothesis.
- U=Spec B and V=Spec R: the occurrences of `Spec (CommRingCat.of B)` and
  `Spec (CommRingCat.of R)`. The map is
  `Spec.map (CommRingCat.ofHom (algebraMap R B))`.
- Arbitrary scheme S and map V to S: `{S : Scheme.{u}}` and the binder `v`.
  `Over.mk (Spec.map … ≫ v)` and `Over.mk v` supply U and V over S.
  `groupSchemeMap (Over.homMk … rfl)` is the EXISTING Yoneda construction of their
  algebraic-space morphism. It adds no group structure or assumption despite its
  historical name.
- Degree minus one is I/I² and degree zero is B tensor_P Omega[P/R]: these are the
  imported `Naive.conormal` and `Naive.differentials`. The latter uses the recorded
  Kähler differential and tensor product, in the order B tensor_P Omega.
- Differential [h] maps to 1 tensor dh: `Naive.differential` is the Mathlib
  `Algebra.Extension.cotangentComplex`; its value on every kernel class is exactly
  `Algebra.Extension.cotangentComplex_mk`. Well-definedness and B-linearity are
  bundled in this genuine linear map, not assumed. Mathlib constructs it by
  `kerCotangentToTensor`, factoring the derivation through the square using Leibniz,
  followed by extension of scalars along the surjection.
- Zero outside -1,0 and zero other differentials: the imported `Naive.complex` is
  `CochainComplex.of (Naive.term P) (Naive.boundary P) …`, whose `if` branches have
  exactly these degrees and zeros. `affineCotangentEtaleComplex` applies the
  associated étale functor termwise to this very complex, including its differential.
- Associated small-étale module sheaf of tilde M: `representedAffineEtaleAssociated`
  is `tilde.functor B` followed by `representedSchemeModuleExtension`.
  The latter is the canonical left adjoint of the EXISTING identity-chart Zariski
  restriction `Poincare.schemeModule`. Under the existing affine-basis equivalence
  it is exactly epsilon tensor pullback, hence (tilde M)_et by Stacks 03DX/03FH.
  Thus the target is a sheaf of modules, not just the associated abelian sheaf.
  Restriction is the actual Zariski-open restriction, including its scalar map.
  The adjunction determines its left adjoint up to the natural isomorphism used
  downstream. It is not a freely chosen functor or mere uncharacterized Nonempty.
- NL and the displayed derived comparison: `naiveCotangent` is the recorded
  `def-sfb-space-naive-cotangent-complex` object's localization; the other side is
  `DerivedCategory.Q.obj (affineCotangentEtaleComplex α hα …)`. Both have coefficients
  in `(schemeSpace (Over.mk …)).SmallModules`, with its actual regular functions
  in the original section universe. `HasDerivedCategory.{w}` specifies the
  localization size, with w independent of u. No category structure is chosen from
  a sorry or replaced by a second abelian instance.
- No finiteness, Noetherian, flatness or regular-sequence hypothesis: none occurs.
  There is no perfectness assertion or replacement by cohomology groups.

Dependency declarations read and used:

- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`; its universal-property
  declarations `MvPolynomial.aeval` (Eval) and `MvPolynomial.algHom_ext` were read.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Spec`, `Spec.map`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, and its module/site
  construction, reached through the intrinsic complex import.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`, `D`, the universal
  `linearMapEquivDerivation`, and the conormal factor `kerCotangentToTensor`.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`, via the existing
  differential term; `def-weil-pbc-module-tensor-product` is a Mathlib leaf whose
  `mathlib_match`, not a missing lean record, supplies its declaration.
- `Mathlib.AlgebraicGeometry.Modules.Tilde`: `tilde`, `tilde.toOpen`,
  `tilde.toOpen_res`, `tilde.functor`, `tilde.adjunction`, and
  `Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent`.
- `Sheaf.AlgebraicGeometry.SpaceNaiveCotangentComplex`: `naiveCotangentComplex`,
  `naiveCotangent`, with its actual conormal quotient and differential.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`.
- `Sheaf.AlgebraicGeometry.AbelianSpacePoincareData`:
  `AlgebraicSpace.Poincare.schemeIdentityChart`, `Poincare.schemeModule`.
  The reused map `groupSchemeMap` comes from its public import `RegularGroupSpace`;
  it simply maps a scheme morphism by the fppf Yoneda functor.
- `Sheaf.RingTheory.NaiveCotangentComparison`:
  `Algebra.CotangentResolution.Naive.Presentation`, `conormal`, `differentials`,
  `differential`, `term`, `boundary`, and `complex` (all read in full). Their
  definition owner is `def-trf-naive-cotangent-comparison-data`; the existence
  theorem `exists_comparison` is neither used nor chosen from.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`, owned by
  `def-trf-scheme-algebraic-space`. Its actual Yoneda sheaf data are reused.

Proof imports are `Sheaf.RingTheory.PresentationsHomotopyEquivalent`,
`Sheaf.AlgebraicGeometry.DerivedEtaleZariskiEquivalence`, and
`Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence`.
The recorded statements `Algebra.Extension.presentations_homotopy_equivalent`,
`Scheme.Modules.derived_etale_zariski_equivalence`, and
`Scheme.Modules.scheme_zariski_etale_quasiCoherent_equivalence` were read.
The two additional proof-only nodes
`lem-sfb-zariski-naive-cotangent-affine-comparison` and
`lem-sfb-scheme-naive-cotangent-etale-comparison` currently have no Lean record;
there is no fabricated import for them. They are named in the complete proof
plan in the main docstring. Their absence does not prevent stating this item.

There are two auxiliary postponed proof obligations, both belonging to the
associated-sheaf construction in this node and listed in its lean.declarations:
`representedSchemeModule_isRightAdjoint` (existence of the canonical tensor
adjunction) and `representedAffineEtaleAssociated_additive` (additivity, to map
complexes). Each has a source and complete natural-language proof docstring.
All definitions have real data. In particular choosing the left adjoint of a fixed
restriction is the permitted universal-property construction, not arbitrary
module data taken from an existential theorem. The remaining sorry is the main
comparison statement itself. No theorem is proved in this delivery.

Edge cases checked against the definitions and Stacks sources:

- T empty: alpha can be a quotient of R, so a nonzero I/I² remains possible;
  the construction does not assume a polynomial basis is inhabited.
- I=0 and polynomial B: the minus-one term is zero and the differential vanishes;
  the degree-zero differential module is retained.
- Identity ring map: any redundant polynomial presentation is allowed, and the
  resulting two-term complex is derived-isomorphic to zero, not asserted
  termwise zero.
- B the zero ring: Spec B is empty, allowed by the genuine scheme and ring types;
  the conormal and tensor module over B vanish, as does its module topos object.
- Dual numbers in characteristic 2: [epsilon²] can have zero differential;
  the statement retains H^{-1}, never replaces NL with Omega in degree zero.
- Infinite T, arbitrary ideals and nonflat I/I²: no finite or flatness instance
  is required; the proof transports a chain homotopy through an additive functor,
  which does not require the conormal term to be flat.
- S and v arbitrary: no separatedness or structure over a field is assumed.

Searches (through the prescribed msearch.py wrapper; original output is preserved
in the sandbox searches.jsonl):

- leanfinder: "The naive cotangent complex of an affine scheme morphism on the small
  etale site is the sheaf complex of the conormal differential of any polynomial
  presentation". Eight hits, including `Extension.cotangentComplex`,
  `Extension.Cotangent`, H1Cotangent, and presheaf differentials. None is this
  derived small-étale comparison.
- loogle: `"cotangentComplex"`. Twelve ring-theoretic hits; the useful exact
  differential is `Algebra.Extension.cotangentComplex`. No small-étale statement.
- grep: `naiveCotangent|cotangentComplex` in Mathlib/AlgebraicGeometry: zero hits.
- leansearch: "naive cotangent complex polynomial presentation etale associated
  sheaf". Eight ring-theoretic hits; no affine étale derived comparison.
- rg in lean/WeilConjectures and lean/Sheaf for the item id and
  `affine.*[Cc]otangent|cotangent.*[Aa]ffine`: no exact statement. Existing full
  cotangent-resolution comparisons and the two-term ring-complex definitions
  were inspected; the ring complex is reused, rather than reconstructed.
- grep -rn of the exact item id in lean/WeilConjectures: no match.
- rg for `schemeIdentityChart|affineEtaleAssociated|polynomialPresentation`
  located and led to reuse of the identity chart and ring complex. The affine
  derived-realization module targets a different presented module category; its
  theorem is not used as an undocumented identification of that category.
- rg of new declaration names in lean/WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json found no clashes.

Sources opened: Stacks more-morphisms.tex lemma-NL-affine (0D0I),
spaces-more-morphisms.tex lemma-NL-compare-spaces-schemes (0D0X), and
algebra.tex lemma-NL-homotopy (00S1), with their proofs. No source-based statement
correction was necessary. No STATEMENT-DISPUTED issue remains.

Validation: scompile.py compiled both the sandbox file and its actual library module
path cleanly (3.2 seconds and 6.5 seconds in the successful pass). Explicit autoImplicit
and relaxedAutoImplicit are false. All lines are at most 100 characters. The first
compiler passes diagnosed a missing zero-preservation instance while elaborating
an opaque affine expression; the final construction fixes the canonical additive
instance explicitly inside its data definition, without adding a statement hypothesis.
No diagnostic #check/#synth commands remain.

## Second reading by Q142

A second clause-by-clause reading was performed in this worker session; no other
agent was started, as the dispatch brief forbids it. The maintainer's independent
review remains the independent reading of the delivery. I reopened the node and
final module and checked the binders, coefficient categories, degree convention,
and functor data. The first draft incorrectly wrapped a sheaf-Yoneda morphism in
an extra constructor; this was repaired by using the existing `groupSchemeMap`.
The first draft also attempted to infer zero preservation through the full affine
expression; the final `affineCotangentEtaleComplex` supplies the named canonical
additivity instance locally in its definition. Neither repair changes any
mathematical hypothesis or conclusion.

The reread specifically checked that the right-hand differential is the image of
the SAME conormal differential, that I/I² is not replaced by a free module, that
no finite-generators hypothesis is hidden, that the arbitrary S and v binders are
retained, and that the result is an isomorphism in the SAME derived category as
`naiveCotangent`. Reusing the Poincare helper imposes no abelian-variety or group
hypothesis: the two reused declarations take only `T : Over S`. Reusing the
Naive ring complex imposes no smoothness, resolution-coherence or derived-category
binder: its constructor takes only an ordinary surjective presentation. There are
no added definition nodes, dependency repairs or mathematical statement corrections.


## Repair of returned head 975916e07e55

H2 repaired: replaced `lem-trf-lci-naive-cotangent-model` in `stmt_deps` by the
existing definition node `def-trf-naive-cotangent-comparison-data` (Q41, 2026-10-22).
I opened its statement and full `lean` record on the current main branch and
reread the recorded `Naive.Presentation`, `conormal`, `differentials`,
`differential`, `term`, `boundary`, and `complex` declarations. The declaration
list of this definition node owns precisely the definitions used here; this
module never chooses `exists_comparison` or invokes that existence theorem.
The report's owner attribution is corrected accordingly.

Both advisory points were also addressed. The unused public import
`WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf` was removed; its
associated-sheaf convention remains implemented by the accepted canonical left
adjoint. The existing definition owners `def-sfb-smooth-integral-group-space`
(`groupSchemeMap`) and `def-trf-scheme-algebraic-space` (`schemeSpace`) were added
to `stmt_deps`, after reading their records and source declarations. They add
no group hypothesis or new scheme assumption.

The retained sandbox was compared with current main without direct Git commands:
only `lean` and `stmt_deps` differed. The repair changes only those allowed node
fields, this report, and the unused import line. Every Lean declaration,
definition body and theorem signature is identical to returned head 975916e07e55;
the mathematical statement, proof and proof dependencies are unchanged. The
prescribed delivery wrapper refreshes the base and performs its rebase bookkeeping.
The maintainer's independent return accepts the semantic clause matching and both
helper obligations; this repair specifically fixes the metadata defect rather than
resubmitting the unchanged record.

Repair validation: the prescribed scompile.py compiled the repaired module both as
sandbox `Sheaf.Stage2.Sandbox0` (9.6 s) and under its actual library module path
(3.8 s), with no errors or warnings. The recorded main signature was checked
verbatim against the retained source. No declaration or data construction changed.
