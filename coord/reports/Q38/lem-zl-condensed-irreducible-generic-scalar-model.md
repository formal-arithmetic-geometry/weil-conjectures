## Worker report

The delivery states `AlgebraicGeometry.ProEtale.condensed_irreducible_generic_scalar_model`
in `Sheaf.AlgebraicGeometry.CondensedIrreducibleGenericScalarModel`. Its only postponed
proof is this theorem. The node's mathematical statement, dependencies and proof are
unchanged. All auxiliary declarations belong to this one statement: they are transparent
composites of existing functors, forwarding of existing instances, or structures of its
existential witnesses. No new mathematical notion or dependency module is introduced.
Every declaration is listed in the node's `lean.declarations`.

Source read: the local Hemo--Richarz--Scholbach PDF, Theorem 4.13, irreducible case,
diagram (4.4), and the paragraph following it (printed p. 12), together with Lemma 4.1
and Proposition 4.3(3). In particular the proof says ANY isomorphism on the geometric
generic point induces one over the chosen cover using the section; it does not replace
its perfect scalar complex. The current node has no blueprint_update or released repair
note. The current blueprint location is literature/blueprint/latest; the node's direct
mathematical source is HRS rather than a separate blueprint assertion.

Hypothesis and clause correspondence:

- Arbitrary commutative condensed ring: `Λ : Profinite.CondensedRing.{u}` and
  `[IsCommMonObj Λ.X]`. This uses the actual ring object of abelian sheaves, without
  requiring a presentation by a topological ring. `condensedScalarRing Λ.X` is its
  reconstructed commutative section ring evaluated at the terminal profinite set.
- Schemes and small pro-etale sites: `Scheme.{u}` and `Scheme.ProEt.topology`. All
  internal module categories are `Mod (Sheaf ... Ab.{u + 1}) (condensedRingObj Λ.X T)`.
  These are the canonical pulled-back coefficient ring objects, not constant rings
  substituted for condensed rings. The recorded sectionwise/internal module equivalence
  in the scalar realization identifies this encoding with ordinary module sheaves.
- Ordinary unbounded derived category: `DerivedCategory` of these module categories,
  with the published ordinary relative derived tensor; no bounded or completed category
  is substituted. `Nonempty (HasRightDual K)` is the standard evaluation/coevaluation
  datum with both triangle identities. The published symmetric ordinary derived tensor
  makes this equivalent to the node's dualizability convention.
- The scalar functor is exactly `condensedScalarRealization Λ.X T`. It is the recorded
  derived constant realization, derived extension along the constant-section counit,
  sectionwise/internal equivalence and actual inverse image from the condensed point.
  `pointRealization` merely names its common initial composite for the comparison
  formulas, without redefining the scalar functor.
- Nonempty irreducible affine X: `[IsAffine X] [Nonempty X] [IrreducibleSpace X]`.
  Algebraically closed geometric generic point: `(Ω : Type u) [Field Ω]
  [IsAlgClosed Ω] (η : Spec (.of Ω) ⟶ X)` and
  `hη : ∀ x : Spec (.of Ω), η x = genericPoint X`.
- Dualizable K: the displayed ordinary derived-category binder K and `hK`.
- Existence of a perfect generic scalar model: the first conjunct is `∃ P,` followed
  by `DerivedCategory.IsPerfectRingComplex P` and `Nonempty (η* K ≅ L_eta(P))`.
  The perfect predicate means a bounded complex with every term finite and projective,
  as the recorded definition requires.
- EVERY such P and alpha: the second conjunct universally quantifies P, its perfectness
  proof, and the actual derived isomorphism `α`. These binders precede the cover U and f.
  Thus the scalar complex is fixed once and for all before the prescribed cover.
- Affine faithfully flat ind-etale f with w-contractible source: U is a scheme with
  `[IsAffine U]`, f is `U ⟶ X`, and the three hypotheses are
  `f.appTop.hom.FaithfullyFlat`, `RingHom.IndEtaleAcrossUniverses f.appTop.hom`, and
  `IsWContractibleRing Γ(U, ⊤)`. For affines faithful flatness and ind-etaleness are
  exactly these properties of global section rings. Affineness of f follows because
  source and target are affine; no extra geometric condition is required.
- The conclusion `Nonempty (CoverModel Λ f Ω η K P α)` existentially packages the
  full precise conclusion. This is an output witness, never an additional hypothesis.
- S and S_eta: `affineComponentSpace U` and
  `affineComponentSpace (pullback f η)` are precisely the connected-component quotient
  spaces with the profinite topology, as in the recorded spectral-components theorem.
  r is `affineComponentMap (pullback.fst f η)`, the actual continuous map on quotients.
  `fiberAffine` forwards the existing affine pullback instance; it adds no assumption.
- D(S,Lambda) and L_S: `CondensedRing.Evaluation.D` on the coherent profinite slice
  with `CondensedRing.profiniteCoefficient Λ.X S`, and the existing
  `CondensedRing.profiniteScalarRealization Λ.X S`. These use the restricted ring object.
- The component inverse images are the existing `ComponentDerivedSquare.Corner`
  witnesses `cornerU`, `cornerV`. Their inverse functors are fixed by `inverse_eq`,
  their coefficient identifications by `coefficient_eq`, and their monoidal comparisons
  by adjunction mates on the actual relative tests. Their `derived` functors are
  termwise localization of `CondensedRing.componentModules`, the same inverse image
  used by the recorded w-contractible lisse evaluation theorem. `square` is the
  existing actual component pullback square.
- Dualizable M and pi_U* M isomorphic to K|U: fields `M`, `dualizable`, `beta`.
- Induced generic-fibre isomorphism r* M isomorphic to L_Seta(P): field `delta`.
  Crucially `generic_induced` equates its image under pi_V* with the composite of
  the actual square theta inverse, pullback of beta, `genericRestriction`, pullback
  of the FIXED alpha, and the scalar comparison. `genericRestriction` is real data
  composed from `schemeComposition` and equality of the two pullback composites.
  The scalar comparisons are not arbitrary maps: `scalarV_underlying` and
  `scalarH_underlying` fix their ordinary underlying maps to the absolute-point
  comparisons, and `cornerScalarComparison` / `schemeScalarComparison` localize
  those precise module maps before precomposing the common scalar realization.
- Existence of a continuous section: `splitting` supplies a morphism of profinite
  spaces s with `s ≫ r = 𝟙 S`. Morphisms are continuous maps; this is exactly r∘s=id.
- Inverse image along ANY section identifies M with L_S(P): `sections` universally
  quantifies s and this equality, then gives `SectionComparison` and gamma. Its final
  equality says the pullback of the very same delta, followed by the scalar comparison,
  equals the identity comparison followed by gamma. `SectionComparison` uses the
  existing `Slice` (fixed actual inverse image and canonical coefficient transport);
  its identity comparison is normalized by the two pullback projections via the
  adjunction mate, and its scalar comparison has underlying map `inverse.beta`.
  `identityDerived` and `scalarDerived` are explicit localization composites of these
  ordinary comparisons. Therefore this clause cannot be satisfied by choosing
  unrelated derived identifications or by assuming a section.
- The cover isomorphism with the same P is `CoverModel.model`. It lies in D(U,Lambda)
  with the canonical pulled-back ring, and still uses the P quantified before f.
- No reducedness or coefficient-flatness hypothesis occurs. Neither the scalar complex
  nor the module-sheaf complex is restricted to bounded complexes.

Dependency declarations read and used:

| Node | Module and declaration |
| --- | --- |
| sk-def-sfb-condensed-ring | Sheaf.Topology.ProfiniteCondensedRing, Profinite.CondensedRing |
| def-pc-scheme | Mathlib.AlgebraicGeometry.Scheme, AlgebraicGeometry.Scheme and Scheme.Hom |
| def-weil-pbc-proetale-site | Mathlib.AlgebraicGeometry.Sites.Proetale, Scheme.ProEt and ProEt.topology |
| sk-def-sfb-pulled-back-coefficients | WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic, coefficientRing and condensedRingObj |
| def-weil-sheaf-of-modules-category | Sheaf.CategoryTheory.RingedSiteModules, ringedSiteModules; the recorded internal/sectionwise equivalence used by scalar realization |
| def-weil-abstract-derived-category | Mathlib.Algebra.Homology.DerivedCategory.Basic, DerivedCategory and Q |
| def-pc-perfect-ring-complex | Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral, DerivedCategory.IsPerfectRingComplex |
| def-sfb-site-derived-constant-module-functor | Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor, commutativeSiteDerivedConstantModuleFunctor |
| def-zl-condensed-scalar-realization | Sheaf.AlgebraicGeometry.CondensedScalarRealization, condensedScalarRing, condensedScalarRealization and condensedScalarExtensionModel |
| sk-def-pe-wlocal | WeilConjectures.RingTheory.ProEtale.WContractible, IsWContractibleRing |
| def-weil-geometric-point | Mathlib.FieldTheory.IsAlgClosed.Basic, IsAlgClosed, with the explicit Spec morphism |
| def-weil-irreducible-components | Mathlib.Topology.Irreducible, IrreducibleSpace and irreducibleComponents (this dependency is a Mathlib leaf, not a missing Lean record) |
| def-weil-pbc-faithfully-flat-ring-map | Mathlib.RingTheory.Flat.FaithfullyFlat.Basic, Module.FaithfullyFlat, via its exact specialization RingHom.FaithfullyFlat |
| def-weil-pbc-ind-etale-algebra | Sheaf.RingTheory.IndEtaleUniverseTransport, RingHom.IndEtaleAcrossUniverses |
| lem-pe-spectral-components-profinite | Sheaf.Topology.SpectralSpace.ConnectedComponentsProfinite, spectralSpace_connectedComponents_profinite, used by affineComponentSpace |
| lem-zl-condensed-wcontractible-lisse-evaluation | Sheaf.AlgebraicGeometry.CondensedWContractibleLisseEvaluation, CondensedRing.condensed_wcontractible_lisse_evaluation and its publicly reexported evaluation model |

All seven stated proof dependencies are directly imported: CondensedLisseProEtaleLocality,
GeometricFieldProEtaleEvaluation, CondensedWContractibleLisseEvaluation,
GenericFiberComponentsSection, ComponentDerivedPullbackSquare, CondensedScalarRealization,
and RingedDerivedMonoidalComparisons. The component square is public because its canonical
witness types occur in this statement. Other solely proof imports are plain imports.
All dependency signatures and docstrings were read, including the full generic-fibre
section theorem and the component/evaluation witness records.

Edge cases checked mathematically: X a geometric point and f the identity gives the
one-point scalar evaluation theorem; P=0 and Lambda=0 give zero derived objects and the
same formulas; nonreduced irreducible affines are permitted; infinitely many components
of U are permitted because S is an arbitrary profinite object, not a finite set. Empty
X is expressly excluded by the node. A faithfully flat cover of nonempty X cannot be
empty, but the auxiliary fibre-affineness and component constructions do not impose a
spurious nonemptiness restriction. There is no coefficient characteristic restriction,
no Noetherian hypothesis and no coefficient flatness. All universes and variables are
explicit (`set_option autoImplicit false`); schemes and profinite spaces live in u,
coefficient modules in u+1, with the published derived-category localization conventions.
The canonical maps and sections use no independent lower test universe.

Searches for an existing theorem:

- msearch.py leanfinder: “A dualizable condensed complex on an irreducible affine scheme
  has the same perfect generic scalar model on every weakly contractible ind etale cover”.
  Eight hits, including AlgebraicGeometry.AffineScheme, AlgebraicGeometry.Scheme.Etale,
  exists_appTop_map_eq_zero_of_isLimit and exists_appTop_pi_eq_of_isLimit, concerned affine
  limit geometry, not this derived condensed scalar theorem. No exact match.
- msearch.py leansearch: “A dualizable sheaf with condensed coefficients on an irreducible
  affine scheme has a perfect generic model on every weakly contractible cover”. Eight
  hits on CondensedMod.isDiscrete_tfae, Condensed, LightCondensed and condensed limits.
  None states generic scalar descent.
- msearch.py loogle: `CondensedMod, DerivedCategory`: zero hits.
- msearch.py grep: `generic.*condensed|condensed.*generic|scalar.*w[Cc]ontract`:
  zero Mathlib hits.
- rg of lean/WeilConjectures and lean/Sheaf for
  `generic.*(condensed|lisse)|condensed.*generic|scalar.*w[Cc]ontract` found the existing
  generic lisse cocycle, comparison and finite pushforward modules, and the evaluation
  interfaces used here; none states this theorem. Searching the exact node id in the
  upstream source found none. Exact searches of the proposed main name and namespace
  in both project source roots and dag/lean_names_upstream.json returned no matches.

No STATEMENT-DISPUTED issue, source correction, new node, or dependency repair was needed.
The initial draft compiled. The final correspondence check tightened the comparison
witnesses to termwise-localized maps with explicit underlying-sheaf normalizations;
the tightened module also compiled cleanly under the 60-second limit in both sandbox
and library module modes (40.1 and 41.4 seconds). The final import-complete version is
checked again by scompile.py and the required deliver2.py dry run before push.

There is no independent worker second reading in this delivery: the dispatcher brief
forbids starting other agents and assigns independent review to the maintainer.

The first dry run identified a namespace-scanner mismatch after a partial dotted
namespace close. The namespace commands now explicitly open the outer ProEtale namespace
and the inner CondensedGenericScalarModel namespace separately, so the compiler and
preflight agree on the main theorem name. No mathematical statement changed.

## Second reading by Q38

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
