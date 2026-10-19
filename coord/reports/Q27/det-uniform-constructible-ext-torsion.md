## Worker report

The module `Sheaf.Paper.UniformConstructibleExtTorsion` states
`AlgebraicGeometry.ProEtale.CondensedRing.uniformConstructibleExtTorsion` with `sorry`.
There is one postponed theorem, owned by this item. No theorem is proved. The helper
definitions have actual data: they assemble existing scalar extension, support, inverse
image, derived tensor and dimension constructions. The only new instance is pointwise
commutativity of the already constructed finite quotient ring, obtained from the existing
commutativity instance. The statement and proof plan of the DAG node are unchanged.

The resolved stage-1 repair note was read. It asks to retain the statement and the
comparison/fiber/hypercohomology route and split the former long opening step. The current
node has those nine steps, which are all included in the theorem's proof docstring.
There is no released stage-2 interface repair in that note.

Hypothesis and clause correspondence:

- The prime ell is `ℓ : ℕ` with `[Fact ℓ.Prime]`. The finite coefficient extension is
  `E : Type u`, `[Field E]`, `[Algebra (Padic ℓ) E]` and
  `[FiniteDimensional (Padic ℓ) E]`. These are explicit section variables used by the
  theorem. The integer ring, its spectral topology, uniformizer and quotient are the
  original `Padic.coefficientExtension*` objects, through `DerivedNakayama.integerRing`,
  `quotientRing` and `reductionRing`. No arbitrary topological coefficient ring is used.
- The field of characteristic p>0 different from ell is `k : Type u`, `[Field k]`,
  `p : ℕ`, `[Fact p.Prime]`, `[CharP k p]`, `hpℓ : p ≠ ℓ`. A field of positive
  characteristic necessarily has prime characteristic, so `Fact p.Prime` records exactly
  the source setting. No finite-field or finite cohomological-dimension hypothesis is added.
- Every scheme is an object of `Over (Spec (.of k))`. Each of S, Z, V, X, T, B has
  `[LocallyOfFiniteType _.hom]`, `[QuasiCompact _.hom]`, `[IsSeparated _.hom]`.
  Every displayed morphism is a morphism in that Over category, so is a k-morphism.
  This is the node's explicit standing convention for all schemes and morphisms, including
  the chosen factors. There is no added compactification or smoothness assumption.
- `u : S ⟶ Z` and `i : Z ⟶ X` with open and closed immersion instances render
  `a = i ∘ u`. Its composite is the specified a, so a redundant separately named a and
  equality are unnecessary. `j : V ⟶ X`, open, and
  `hij : Set.range i.left.base = (Set.range j.left.base)ᶜ` give the open complement.
- `vb : T ⟶ B`, open, and `kb : B ⟶ X`, closed, render the node's chosen
  factorization `b = kb ∘ vb`. The support definition uses exactly
  `(lowerStar A kb.left).obj ((openImmersionLowerShriek A vb.left).obj ...)`.
  Thus b_! is the specified closed direct image after open extension by zero.
- `L₀` and `M₀` are `FormalSupportModules (DerivedNakayama.integerRing ℓ E)` on S and T.
  This category is the existing internal module category over `condensedRingObj`, namely
  the coefficient ring pulled back from the point, not a discrete substitute for O_E.
  `hL₀` and `hM₀` use `IsLisseCoefficientModule`: a pro-etale cover with finite-free
  restrictions. Reading `Mod.IsFree` confirms that its rank is a natural number and may
  be zero, and may vary between cover members.
- `n : ℕ`, `hn : 1 ≤ n` render every positive exponent. Level n means π^n, not
  π^(n+1); this is the convention of `DerivedNakayama.quotientRing` and
  `Padic.coefficientExtensionRing` used here.
- `torsionStratumReduction ℓ E Y n` is ordinary `Mod.extendScalars` along
  `coefficientMap (DerivedNakayama.reductionRing ℓ E n) Y`. This is M/π^n with its
  actual quotient coefficient action, not an arbitrary sheaf isomorphic to a reduction.
- `torsionStratumSupport` is the existing `formalClosedSupport A i j` right derived
  functor applied to the degree-zero sheaf kb_* vb_!(M₀/π^n). The first conjunct says
  its homology is zero whenever `q < 0` or `cd_ℓ(j)+1 < (q.toNat : WithTop ℕ)`.
  For nonnegative integer q the latter is exactly q>cd_ell(j)+1. For negative q only
  the first disjunct matters. This is precisely amplitude [0,cd_ell(j)+1].
- The other part of clause (1) is `∀ q : ℤ, IsClassicalAbelian (...homology... ).X`:
  every underlying abelian cohomology sheaf is pulled back from the etale site.
  Over the finite constant quotient coefficient ring this is also module-sheaf descent:
  full faithfulness of exact comparison lifts the action map uniquely and reflects its
  action identities. Thus this is the node's etale-origin condition, including the
  coefficient action, and does not add constructibility of the cohomology sheaves.
- In `torsionStratumTwist` the dual is exactly `(ihom L₀).obj (𝟙_ ...)`, internal Hom
  into O_{E,S}. Ordinary scalar extension then gives L₀^∨/π^n. It is placed in
  degree zero and tensored using the existing `derivedTensor` with the derived exact
  inverse image along u of the support complex. The reduced dual is locally finite
  free, so this is the ordinary exact tensor in the node, without an extra flatness
  assumption on either lattice.
- Clause (2) applies `(formalClosedSupportSections A S.left).rightDerivedFunctor` to
  this twist and asserts zero q-th homology whenever
  `cd_ℓ(j)+cd_ℓ(S)+1 < (q.toNat : WithTop ℕ)`. Global sections is the existing
  composite of module forgetting and abelian global sections. Thus this is exactly the
  specified hypercohomology group. For negative q the premise is false, just as q cannot
  exceed a nonnegative endpoint.
- `torsionStratumDimension` and `torsionStratumRelativeDimension` call the recorded
  `cohomologicalDimension` and `relativeCohomologicalDimension`. The former supplies
  compactness by `QuasiCompact.compactSpace_of_compactSpace S.hom` and local
  Noetherianity by `LocallyOfFiniteType.isLocallyNoetherian S.hom`. The latter derives
  local Noetherianity of X similarly, giving qcqs for the open j. These are actual
  applications of existing facts inside definitions, not extra theorem hypotheses.
  Both endpoints are `WithTop ℕ`; comparison against top is false. Thus infinity never
  imposes an upper bound, and clause (2) is vacuous if either dimension is infinite.

Dependency declarations used (read with signatures and documentation):

- `Sheaf.AlgebraicGeometry.CohomologicalDimension`:
  `ProEtale.cohomologicalDimension`, `relativeCohomologicalDimension`,
  `IsClassicalAbelian`. The two dimensions have the node's extended nonnegative convention.
- `Sheaf.Paper.FormalClosedSupport` and its public imported
  `Sheaf.AlgebraicGeometry.FormalClosedSupportAdjunction`:
  `CondensedRing.formalClosedSupportAssertions`, `formalClosedSupport`,
  `FormalSupportModules`, `formalSupportPullback`, `formalClosedSupportSections`.
  The support definition is the original i^* kernel construction, not a second functor.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  the existing separated finite-type scheme setting and chosen compactification interface.
  The setting is spelled out as theorem binders; no compactification is needed in this
  stratum lemma. The module is imported as the recorded statement dependency.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, importing `CoefficientExtension`:
  `Padic.finite_coefficientExtensionRing`, the actual spectral absolute value, integer ring,
  chosen uniformizer, ideal and quotient coefficient ring.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `ProEtale.coefficientRing`, `condensedRingObj`, and the strong monoidal
  `upperStarFromPoint` which constructs the pulled-back ring.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `CondensedRing.lowerStar` (mapMod of abelian direct image followed by scalar restriction).
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`:
  `CondensedRing.openImmersionLowerShriek` (the specified scalar restriction and linear
  extension by zero, with the recorded exactness instances).
- Existing coefficient construction from `det-pe-derived-nakayama-resolution`, module
  `Sheaf.Paper.DerivedNakayamaResolution`: `DerivedNakayama.integerRing`, `quotientRing`,
  `reductionRing`; the new definition node below records these existing coefficient data in stmt_deps.
- Already landed definition `def-sfb-lisse-coefficient-module`, module
  `Sheaf.Paper.CoefficientHeartCommonStratification`: `IsLisseCoefficientModule`;
  its definition uses the existing finite-rank `Mod.IsFree`. This node too is added to
  stmt_deps. The coefficient data and the lisse predicate introduce no dependency on this theorem.
- The scalar map is the existing `CondensedRing.coefficientMap` from `ChangeOfCoefficients`;
  the tensor is `CondensedRing.derivedTensor` from `ModuleObject.Derived.Tensor`.
  All statement-dependency modules are direct imports; available proof-dependency modules
  are imported non-publicly, subject to the incompatible-import exclusion below. Mathlib proof leaves also have
  their recorded source modules imported. The unstated integral constant-coefficient
  criterion and formal-closed-support-ii have no module to import yet.

Edge cases checked before writing and during the final reading: rank-zero lattices use
`Mod.finiteFree _ 0`; empty S or T and empty covers are allowed; Z empty and Z=X (j empty)
remain legal. When S or T is empty no phantom nonempty-cover hypothesis appears. The n=1
case is the first quotient level; n=0 is excluded only by the original hn. The p=ell case
is excluded by exactly the source assumption. The base field need not be finite, perfect,
or have finite ell-cohomological dimension. Finite and infinite dimension endpoints were
checked, including the negative q/toNat interaction explained above. All site objects use
Scheme.{u} and Ab.{u+1}; no equality between object and morphism universes is imposed.

Searches (using the required msearch wrapper, group Q27, item id):

- LeanFinder: `local cohomology of a lisse torsion sheaf along a closed subscheme is bounded
  by the cohomological dimension of the open complement plus one`. Eight results, including
  `localCohomology.isoSelfLERadical`, `Module.supportDim_le_supportDim_quotSMulTop_succ`,
  and qcqs scheme section-localization facts. None states this two-clause pro-etale bound.
- Loogle: `formalClosedSupport, cohomologicalDimension`. Zero hits; unknown identifier
  formalClosedSupport in the remote Mathlib search environment.
- LeanSearch: `Proetale local cohomology closed support torsion sheaf cohomological dimension
  bound`. Eight results: module support/Krull dimension, closed ideal-sheaf support, and
  cochain-complex lower-bound facts. No matching theorem.
- msearch grep: `localCohomology|cohomologicalDimension` in Mathlib/AlgebraicGeometry.
  No match. The local grep searches below separately inspected the project's interfaces.
- `rg` of `det-uniform-constructible-ext-torsion|torsionStratum|uniformConstructibleExt|
  torsion_stratum` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and
  `/home/ubuntu/weil-newtargets-shared/lean/Sheaf`: no existing declaration of this item.
  DAG/upstream-name search by cd and torsion/support also gives no matching theorem.
- Concept searches for lisse/lattice, coefficientExtensionRing/Integers, quotientRing,
  reductionRing and FormalSupportModules in the project found the exact reusable notions
  listed above. Reading Mod.IsFree checked finite rank rather than arbitrary free rank.
  Reading the source signatures avoided duplicating integral or finite coefficient objects,
  the reduction homomorphism, locally free predicate or support functor.

Proof import exclusion: the recorded
`Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison` imports the reorganized
`FiniteCoefficient.Derived.LowerShriek`. Combining it with the required dimension module's
original `ProEtale.Derived.LowerShriek` fails with “environment already contains
AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactification”. As authorized by the
brief's duplicate-import repair rule, the file instead imports the smaller compatible
`WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekComparison`. Its existing
`openImmersionLowerShriekComparisonUpperStarIso` is the canonical open comparison used
in proof step 4. The full recorded composition/identity coherence theorem is not required
by this item's proof. No dependency record or upstream file is edited; the maintainer
can restore the larger proof import once its duplicate import closure is retired.

Validation: the full theorem and all helper definitions passed scompile.py, with no errors
or warnings, before adding the complete proof-import plan. The final import-complete file
is recompiled and the delivery dry run is required before pushing. No global build, direct
Git command, live source edit or launcher script edit is used.

No STATEMENT-DISPUTED flag or source correction is needed. There is one new existing-declaration definition node (below), and no repairs to dependency Lean records.

## Second reading by Q27

The dispatcher explicitly instructs this worker not to start other agents; no independent
worker reading is claimed. The maintainer's independent delivery review remains required.
I reopened the node and the complete Lean module for a separate self-check of the matching
above: both support bounds and classicality are present, the hypercohomology twist uses the
integral dual before reduction, and all factors are the source's actual canonical functors.
No extra finite-cd, constructibility of support cohomology, or nonzero-rank hypothesis was
introduced. The two finite-type-to-qcqs adapters use existing proofs and preserve infinity.
The ordinary quotient exponent is n on both sides. No statement mismatch was found.

## New nodes

`def-sfb-torsion-stratum-coefficients` records the continuous integral and finite quotient
condensed rings, with the canonical quotient postcomposition map, by existing declarations
in `Sheaf.Paper.DerivedNakayamaResolution`. The source is the current torsion lemma's
coefficient convention and its proof's opening finite coefficient reduction; the explicit
construction is also in the derived Nakayama resolution source. LeanSearch returned eight
p-adic integer quotient facts, Loogle returned zero hits, and Mathlib/upstream grep found
no corresponding condensed constructions. Project grep found the six existing declarations.
A DAG search confirmed that these appeared under a theorem node, without a standalone
definition node. Generic continuous ring/map and ring-object nodes already exist and
are its statement dependencies. This node introduces no module and no duplicate definition.
The earlier dry run correctly rejected adding the derived Nakayama theorem node as a
statement dependency; this definition-node binding repairs that issue. The lisse predicate
has an already landed definition-node binding `def-sfb-lisse-coefficient-module`, which
replaces the common-stratification theorem node in the item's added dependencies.
The preflight also showed that lean.statement excludes the terminating :=; its record
was corrected to match the file signature exactly. No Lean statement changed.

The separate self-check also read the new coefficient node against lines 73--119 of the
existing source: both topologies, the quotient exponent, pointwise operations and quotient
postcomposition match. The n=0 zero ring is defined, while the item's theorem uses n>=1.
