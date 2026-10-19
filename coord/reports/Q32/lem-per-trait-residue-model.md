## Worker report

The module `Sheaf.Paper.TraitResidueModel` states
`AlgebraicGeometry.Etale.exists_traitResidueModel`, with `sorry` as its entire proof.
Its conclusion packages the canonical tame quotient, augmentation basis, stalk data,
three-term exact functor, Tate evaluation, natural homotopies, derived comparison and
residue transformation. The component bundles are conclusions, not assumptions added
to the theorem. No object is obtained by choosing data from this postponed theorem.
Every auxiliary definition has actual data; every declaration belongs to this node
and is listed in `lean.declarations`. No statement correction or new node is needed.

The retained earlier draft was repaired rather than replaced. The former missing
published completed-algebra artifact is now available: its import-only probe passed.
Disabling automatic generation of unused injectivity and size-specification lemmas
for the dependent bundles repaired the compile timeout. The final module compiled
cleanly with scompile.py in both sandbox and library positions (24.2 and 25.2 seconds),
with no errors or warnings other than the permitted postponed-proof diagnostic.

Hypotheses and clauses, matched against the node and ILO XVII pp. 259–262:

- Prime ell: `(ell : ℕ) [Fact ell.Prime]`. Coefficients are exactly the prime field,
  `TraitCoefficients ell = ULift (ZMod ell)`, with the actual lifted field structure.
  The lift puts coefficients and modules in universe u+1 on the small etale site.
- The trait is `Spec (.of R)` with `[CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R] [IsStrictlyHenselianLocalRing R]`.
  Invertibility is `_hell : IsUnit (ell : R)`. There is no completeness,
  excellence, algebraic-closedness of the residue field, or finiteness assumption.
- The chosen geometric generic point is `[Field Ω] [IsAlgClosed Ω]
  [Algebra (FractionRing R) Ω]`. `TraitSeparableField` is the actual separable
  closure inside Ω and `TraitGaloisGroup` its fraction-field automorphism group
  with Mathlib's Krull topology. The separably closed representative
  `traitGenericPoint` gives the same geometric stalk; `traitClosedPoint` uses the
  separably closed residue field. Both actual sheaf fibers are used.
- The residue exponent is `traitCharacteristicExponent = ringExpChar` of
  `IsLocalRing.ResidueField R`, including exponent one in characteristic zero.
  `TraitResidueAlgebra.tame` targets the existing `TameRoots.limitSubgroup`,
  with `TameRoots.limitTopology`. Its fields assert continuity, surjectivity,
  the uniformizer-root formula, p-power order of every finite continuous quotient
  of its kernel, trivial kernel for p=1, and existence of a dense cyclic generator.
  `traitIsGenerator` is exactly density of integral powers.
- The completed algebra and augmentation ideal are the landed
  `Rep.CompletedAugmentation.Algebra` and `.Ideal`; their augmentation is the
  sum-of-coefficients map at the trivial quotient. `augmentationBasis` is an
  A-linear equivalence A ≃ I for every generator, and its formula specifies
  multiplication by `1 - groupElement σ`, including its sign.
- `TraitResidueStalkData.action` is the actual generic stalk action, specified on
  every etale germ by `action_germ`, natural on sheaf maps, with open stabilizers.
  The global-section-to-closed-stalk isomorphism is fixed by the actual germ map.
  Specialization is fixed by the equality of the two global germ maps.
  `inclusion_injective` and `inclusion_range` identify the invariant functor with
  precisely the wild-fixed submodule of that same generic stalk.
  `specializationInvariant_formula` says specialization factors through it.
- The tame action is characterized by descent of the actual H-action.
  `invariantsModule`, the scalar tower and commuting scalars give the completed
  A-module on invariants. `completedAction_formula` is its finite-quotient group-ring
  formula on each vector fixed by an open normal subgroup, so this is the canonical
  completed action, not an unrelated action. `completedAction_natural` fixes its maps.
- `TraitIdealHomFunctor` specifies Hom_A(I,N) by an injective evaluation with image
  exactly all additive A-linear maps I → N. Evaluation respects addition and Λ-scalars,
  and its naturality fixes functoriality. `TraitResidueIdealData` specializes it to
  the actual completed algebra, ideal and invariant action just described.
- `TraitResidueComplexCore.F` is additive. Its `degree0`, `degree1`, `degree2`
  identify the terms with the closed stalk, wild invariants and that Hom_A module.
  `outside` kills all other degrees. `firstDifferential` is specialization and
  `lastDifferential` sends m to `(a ↦ a • m)`. The complex structure includes d²=0.
  `exact` asserts finite-limit and finite-colimit preservation in every degree,
  the componentwise expression of exactness. `preservesQuasiIso` states the
  quasi-isomorphism clause for the actual totalization.
- `traitTotalFunctor` and `traitTotalTransformation` use Mathlib's signed coproduct
  total complex of the termwise double complex. The horizontal support is 0,1,2,
  so every relevant degree has finite width, even for an arbitrary bounded below K.
- `TraitResidueDerivedData.augmentation` is normalized in degree zero by inclusion
  of supported sections and the closed germ. `totalAugmentation_formula` fixes its
  termwise totalization. `comparison` identifies the totalized F(K), naturally on
  `CochainComplex.Plus`, with the existing `derivedSupportedEtaleSections`.
  `comparison_normalization` identifies this comparison with the right-derived
  functor unit and the displayed augmentation; an arbitrary comparison is insufficient.
- The support is exactly the closed point: `traitGenericOpen` is its open complement.
  The existing supported section functor is the kernel of restriction to this open.
  The existing bounded below derived functor has values in the full derived category;
  this is the standard full inclusion of D⁺ and does not alter the assertion in D⁺.
- `TraitTateLine` is the lifted additive group of the actual ell-th roots of unity.
  `rootProjection_formula` fixes the tame projection at ell.
  `twistHom` identifies the actual internal Λ-linear Hom from this line with
  continuous additive maps from G to the discrete underlying additive module N.
  Its formula is precomposition with the root projection: no equivariance condition
  or action is imposed on N for this Hom.
- `averaging` is natural, is a retraction of the invariant inclusion, and satisfies
  the precise finite-normal-quotient formula `|S/U|⁻¹ • ∑ g • v` on every vector
  fixed by U. This specifies the canonical wild-inertia projector, including p=1.
- `TraitResidueTwistData.sourceFormula` is M_generic(-1) placed in degree two.
  Its `sSigma` is thus the shifted equivalent of M_generic(-1)[0] → F(M)[2].
  `sSigma_formula` evaluates at `augmentationBasis σ h 1 = 1 - σ` and gives the
  average of f(σ). Since that element freely generates I, the formula specifies
  precisely inverse evaluation at 1-σ after evaluation at σ and averaging.
- `uniqueNaturalHomotopy` quantifies over both generators and asserts existence of
  a unique family of homotopies satisfying naturality for every sheaf morphism.
  It does not assert uniqueness of homotopies for an isolated module.
- `genericDerived` and `tensorDerived` are fixed by `genericFactor` and `tensorFactor`
  to the actual generic stalk and termwise tensor with the Tate line on representatives.
  `evaluation_formula` normalizes the totalized tensor-Hom evaluation on every summand.
  `negativeResidue` is the natural transformation K_generic[-2] → RΓ_s(K)(1).
  `residue_formula` identifies it on EVERY bounded below representative and for EVERY
  generator with tensoring and totalizing `sSigma`, through the fixed comparisons.
  Thus localization and natural homotopy give both kinds of independence in the node.
  `traitResidueTransition` is the actual positive-shift transformation
  K_generic → RΓ_s(K)(1)[2], defined from it using the canonical shift isomorphisms.
  The final transformation forgets the generic Galois action, as the node requires.

Dependencies read and used:

- `WeilConjectures.Mathlib.RingTheory.Henselian`:
  `IsStrictlyHenselianLocalRing` and its separably closed residue field instance.
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic` and `Mathlib.AlgebraicGeometry.ResidueField`:
  `IsAlgClosed`, `Scheme.SpecToEquivOfField`, `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`; affine trait residues use `IsLocalRing.ResidueField`.
- `Sheaf.AlgebraicGeometry.EtaleSupportedSections`: `supportedEtaleSections`,
  `supportedEtaleSectionsι`, `derivedSupportedEtaleSections`, their additive instance.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: the existing etale coefficient
  encoding and Mathlib `DerivedCategory.Plus` and its localization functors. Read the
  current source through `scompile.py --source` because the old checkout lacks it.
- `Sheaf.FieldTheory.TameRootsProduct`: `TameRoots.Order`, `limitSubgroup`, `limitTopology`.
  Its definition node `def-per-tame-root-limit` is added to stmt_deps.
- `Sheaf.RepresentationTheory.CompletedAugmentationAlgebra`:
  `Rep.CompletedAugmentation.Algebra`, `Ideal`, `groupElement`, and its canonical
  action interface. Its definition node is added to stmt_deps. No duplicate inverse
  limit, augmentation, group basis vector or augmentation ideal is defined here.
- Proof imports `Sheaf.FieldTheory.CanonicalTraitTameCharacter`:
  `IsDiscreteValuationRing.exists_canonical_tame_character`, and
  `Sheaf.AlgebraicGeometry.TraitSheafGluing`:
  `AlgebraicGeometry.Etale.traitSheaves_equiv_specialization`.
  Both complete signatures and proof docstrings were read. They are already published,
  so the obsolete saved prerequisite drafts were not promoted into this delivery.

Searches for an existing complete statement were retained and repeated:

- msearch.py leanfinder, `canonical residue morphism strictly henselian trait supported
  etale cohomology tame inertia augmentation ideal`: eight residue-field/etale-algebra
  hits, none giving this theorem.
- msearch.py loogle, `HomologicalComplex₂.totalFunctor, Homotopy`: zero hits.
  The earlier `MonoidAlgebra.augmentation, CochainComplex, Homotopy` query also had
  zero hits and found no identifier `MonoidAlgebra.augmentation`.
- msearch.py grep, `TraitResidue|traitResidue|residue.*trait`, Mathlib AlgebraicGeometry:
  zero hits. Earlier grep `trait.*residue|TraitResidue|CompletedGroupAlgebra|Procyclic`
  found no complete statement.
- rg for `TraitResidue|traitResidue|residue.*[Tt]rait|trait.*residue` in the source
  WeilConjectures tree and shared lean/Sheaf found only unrelated trait-section residue
  separability results. rg for this node id in WeilConjectures found no declaration.
- Earlier searches of the DAG and published sources located the genuine completed
  algebra and tame-root definitions now imported; the obsolete scratch constructions
  are outside delivered lean/. The retained source extract `ilo-xvii-residue.txt` was
  read again against the displayed differentials, evaluations and uniqueness clause.

Edge cases checked: p=1 gives trivial wild inertia and identity averaging; residue
characteristic p>1 stays distinct from ell by the unit hypothesis. The choices ell=2,
zero modules, closed-supported sheaves, generic sheaves with closed stalk zero,
nonconstructible/infinite stalks, and complexes with arbitrarily low finite lower bounds
are all admitted. Fields are excluded as traits by `IsDiscreteValuationRing` itself.
Only the actual geometric stalk action occurs; there is no replacement by a trivial
H-action. No generator is an extra input to the theorem. No fault or disputed statement
was found.

## Second reading by Q32

The dispatcher forbids starting another agent and assigns the independent delivery
review to the maintainer. This is the required worker self-check, not a claim that
another worker reviewed the packet. I re-read the node and module in a separate pass.
The full hypothesis/clause correspondence is above. In particular I checked the sign
1-σ, the inverse direction of evaluation, the actual stalk and quotient action, p=1,
continuous additive rather than equivariant Hom, natural-family homotopy uniqueness,
the supported-section normalization, and the formula for every generator and bounded
below representative. The positive-shift residue is defined from its equivalent
negative-shift form. The only postponed proof is `exists_traitResidueModel` and its
complete proof docstring follows all steps of the existing DAG proof.

The earlier typeclass timeout was repaired by avoiding unused generated equalities;
no limit was raised and no clause was removed. The sealed lifted prime-field type
uses the actual `ULift.field` instance. All universes and binders are explicit, with
`autoImplicit false`. The node changes only `lean` and adds the two already landed
notion nodes to `stmt_deps`. Its natural-language statement and proof are unchanged.
