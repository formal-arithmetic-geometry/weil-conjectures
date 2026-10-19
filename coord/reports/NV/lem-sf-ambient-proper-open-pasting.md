## Worker report

The module `Sheaf.SixFunctors.AmbientProperOpenPasting` states
`AlgebraicGeometry.ProEtale.AmbientProperOpen.ambientProperOpenPasting` with `sorry`.
It uses the existing constant-ring operations registered by
`def-sp-semilinear-constant-ring-operations`, and the existing canonical comparison
data now registered by `def-sf-semilinear-proper-open-comparisons`. It does not
depend on the semilinear mate-pasting theorem.
Its other declarations construct the canonical operations and package explicit equations;
they do not assume those equations. Definitions have actual data. The theorem docstring
contains the ten-step natural-language proof of the node.

Repair of independent-review return L on immutable head `42365e336230`: H2 identified
that the preceding repair registered the base constant-ring operations but left the
canonical compositors, open adjunction and intrinsic alpha without a definition owner.
The prescribed initial saved-packet dry run passed at `8189c27753`; this mechanical
success did not resolve the returned ownership fault. The correction adds one
`existing: true` definition node and one item statement dependency. The Lean is unchanged:
SHA-256 `af74586e245d25bd48f28e96e776a6c036321af54892452ce9d316e5e7454ccd`,
matching the returned head. The current base has no item Lean record; its only
non-Lean difference from this packet is the authorized statement-dependency addition.
NB's landed constant-ring node is byte-for-byte unchanged and omitted from the packet.

Hypotheses and clauses, read against the current DAG statement:

- The fixed algebraic closure of a finite field is `F : WeilConjectures.FiniteFieldDatum`;
  `Spec (.of F.k)` is the base. The prime and unequal characteristic are `[Fact l.Prime]`
  and `_hl : l ≠ F.p`. The field extension is `E`, `[Field E]`, `[Algebra ℚ_[l] E]` and
  `[FiniteDimensional ℚ_[l] E]`. The recorded valuation ring/uniformizer quotient is
  `Padic.coefficientExtensionRing l E (n + 1)`. Its `ULift` changes only the carrier universe;
  it has the same ring operations. `n : ℕ` ranges over all positive levels through `n+1`.
- Finite-type schemes and all morphisms over this base are `Spaces F`, the full subcategory
  of `Over (Spec (.of F.k))` cut out by `LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom`.
  No separatedness condition occurs. `geometry F` forgets to the actual schemes.
- In case (a), `ordinary F Λ` uses `ProperOpenDerived`, `ProperOpenPull`,
  `ProperOpenPush`, and `ProperOpenShriek`, on the small `Scheme.ProEt` sites. These are
  ordinary unbounded derived categories of module-valued sheaves with constant coefficients.
- In case (b), `systems F C τ` uses `SemilinearProperOpen.Derived`, `P`, `R`, and `J`.
  `Modules C τ` is the recorded strict semilinear system category on the vertical sequence
  site, with its actual coefficient transitions. The theorem specializes `C,τ` to
  `IntegralSystemRealization.scalarRings` and `scalarTransitions`, starting at level one.
  This is not a derived category of completed integral coefficients or a diagram of derived
  categories. Pullback and open extension are exact; right image is derived simultaneously.
- `Calculus.adj` and `openAdj` are the actual derived inverse/direct and open adjunctions.
  `pComp` is oriented from composite to successive pullbacks, so its inverse is the node's
  `d`. `Calculus.sComp` is its `conjugateIsoEquiv` under the composite adjunction.
  `Calculus.jComp` is `Adjunction.leftAdjointCompIso` applied to inverse `pComp`.
  These constructions fix adjunction compatibility, including the units and counits.
  Their naturality is part of being natural isomorphisms. The explicit associativity and
  two unit equations are `Laws.p_assoc`, `p_unit`, `s_assoc`, `s_unit`, `j_assoc`, `j_unit`.
- The canonical tensor-composition equation in (a) is `OrdinaryTensorComposition`.
  It compares the two routes using `leftDerivedUpperStarTensorIso`, the actual tensor
  bifunctor, and `pComp` on the two inputs. The equation in (b) is
  `SystemTensorComposition`: the published `pullbackTensorSystemComparison`, normalized
  on K-flat representatives, and `Compositors.pullComp`. This is quantified over all
  presentations `o,c` of the recorded canonical operations and compositors. Their
  `sections`, `conjugate`, and `pullComp_model` fields fix the ordinary section formula,
  adjunction normalization and localization, rather than permitting arbitrary isomorphisms.
  The assertion therefore adds no hypothesis about an input derived object. It takes
  place on the full `coefficientSequenceDerived` category before evaluation or limits.
- Every square has objects `U,V,W,Z` in `Spaces F`, maps `k,r,p,i`, and
  `h : k ≫ p = r ≫ i`. Its hypotheses are precisely `IsOpenImmersion` and `QuasiCompact`
  on the mapped horizontal arrows and `IsProper` on the mapped vertical arrows.
  There is no pullback-square hypothesis.
- `ordinary.alpha` is exactly `properOpenAlpha`. Its definition uses `pullback p i`,
  `StrictTower.squareLift`, canonical `properOpenBeta`, `properOpenClopenProjection`,
  and canonical open/pullback compositors. The projector is the direct-image unit followed
  by the canonical clopen direct-image/open-extension identification. It is identity on
  the selected image and zero on the complementary open. The lift is clopen by the
  existing strict-tower geometry; there is no extra clopenness assumption.
- `systems.alpha` is the published `SemilinearProperOpen.alpha` on the actual ringed
  sequence site. It uses its `pi` clopen projector and open-unit-normalized `beta`, with
  ordinary section formulas before exact localization. No arrows are selected by derived
  evaluations. `Calculus.gamma` is `mateEquiv c.adj c.adj c.alpha`, which expands to precisely
  the displayed proper unit/alpha/counit word of the node.
- The intrinsic alpha's vertical/horizontal pasting is `Laws.alpha_vertical` and
  `alpha_horizontal`. The mate's two pasting equations are `gamma_vertical` and
  `gamma_horizontal`. All insert the specified `pComp`, `sComp`, `jComp` components;
  the equations are componentwise for every derived object, hence natural-transformation
  equalities. `gamma_vertical_id` and `gamma_horizontal_id` are the two identity squares.
- Refinement squares and intermediate compactification towers are included by these
  universal quantifiers: identity left proper edges and the proper refinement maps satisfy
  the same hypotheses; composite maps have the displayed composition instances.
  No restriction to Cartesian squares or to a specific compactification is imposed.
- `M,N` range over entire unbounded categories. No Tor, constructibility, etale-origin,
  normalized-system or boundedness binder occurs. No `IsIso gamma` conclusion occurs.

Dependency declarations read and used (directly or through the published specializations):

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, and imported `coefficientExtensionRing`.
- The convention node `def-weil-scheme-morphism-properties` has no declaration of its own:
  its named Mathlib notions `LocallyOfFiniteType`, `QuasiCompact`, `IsOpenImmersion`,
  `IsProper`, and `IsClosedImmersion` are used.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`, topology.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`:
  `Scheme.proEtaleConstantRingDerivedPullback` and the canonical ring/module adjunction.
  The ordinary finite presentation is reused through `ProperOpenProjectionMate`.
- `Sheaf.Paper.SemilinearDerivedSections`:
  `WeilConjectures.SemilinearSections.semilinearDerivedSections`, `Systems`, and `DS`.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`:
  `SheafOfModules.localizedSystemExact`, extension and restriction.
- `Mathlib.CategoryTheory.Adjunction.Basic`: `CategoryTheory.Adjunction.comp`;
  `Mathlib.CategoryTheory.Adjunction.Mates`: `mateEquiv` and `conjugateIsoEquiv`;
  `Mathlib.CategoryTheory.Adjunction.CompositionIso`: `leftAdjointCompIso`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`;
  the ordinary and system tensor maps retain its K-flat representative characterization.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, projections.
- `Sheaf.SixFunctors.OpenTensorNormalization`: `SheafOfModules.openTensorNormalization`,
  exact derived adjunction and finite/system comparison normalizations.
- `Sheaf.SixFunctors.ProperOpenProjectionMate`: `properOpenAlpha`, `properOpenMate`,
  `properOpenAdj`, `ProperOpenDerived/Pull/Push/Shriek/Tensor` and clopen projection.
- `WeilConjectures.Compactification.Refinement`: `Compactification.Refinement`, whose
  `hom` is proper and whose equations include the refinement square in the universal laws.
- `def-sp-semilinear-constant-ring-operations` owns the published `Modules`, `Derived`,
  `P`, `R`, `J` and `adj` operations. Its reviewed NB record stays unchanged.
- New existing-definition owner `def-sf-semilinear-proper-open-comparisons` owns the
  canonical comparison declarations in `Sheaf.SixFunctors.SemilinearProperOpenMatePasting`
  listed below, including `jAdj`, `pComp`, `pId` and `alpha` used by `systems`.
  The theorem `semilinearProperOpenMatePasting` is not a statement dependency.

Edge cases checked: `n=0` represents coefficient level one, and all positive levels occur.
Identity proper/open arrows and both unit equations are explicitly included. Empty opens
are allowed and the clopen projector is zero on the empty selected component. Non-Cartesian
squares and nonseparated finite-type schemes are admitted. System transitions are not
assumed flat; equations are in the simultaneous derived category, without using faithfulness
of evaluation. Coefficient, site-object, site-morphism and localization universes remain
those of the published constructions; no new equality of site universes was imposed.

Searches retained from the earlier attempt (`searches.jsonl`): msearch leanfinder query
“canonical proper open interchange clopen projection vertical horizontal pasting unbounded
proetale derived sheaves” returned eight unrelated gluing/limit hits. Loogle query
`CategoryTheory.mateEquiv_vcomp` returned the generic mate theorem, which does not identify
the intrinsic clopen comparison. Mathlib grep query `proper.*open.*past|properOpen|shriek.*comp`
in CategoryTheory returned zero hits. Project/upstream ripgrep searches for the item id,
properOpen, proper/open pasting and shriek composition found the recorded finite and
semilinear dependencies and older etale statements, not the entire ambient assertion
including tensor-composition coherence. Rechecked the current canonical finite module with
`scompile.py --source`; read the current semilinear, tensor, section and compositor sources.
The Stacks source Tags 0F7B--0F7D was read locally; its etale theorem is a source for the
normalization/pasting, not a claim that Stacks supplies the ambient-system domains.

No statement correction or STATEMENT-DISPUTED issue is claimed. No dependency module
is added and no published Lean declaration is changed.

## New nodes

`def-sf-semilinear-proper-open-comparisons` is an `existing: true` definition node in
`sec-six-functors`, built on the unchanged
`def-sp-semilinear-constant-ring-operations`. Its main declaration is
`AlgebraicGeometry.ProEtale.SemilinearProperOpen.pComp`. The `lean.statement` is
copied verbatim from `def pComp` through its type, before `:=`, including the newline.
Its `lean.declarations` owns exactly the 24 declarations requested in the return,
all in the unchanged published `Sheaf.SixFunctors.SemilinearProperOpenMatePasting`:

- `pushComp_existsUnique`, `pushComp`, `pullComp`, `pComp`, `sComp`: section-normalized
  direct-image composition, ordinary adjoint composition, exact localization and
  derived adjunction conjugation.
- `pushId_existsUnique`, `pId`, `sId`: section-normalized identities and conjugates.
- `jAdj`, `jComp`, `J_congr`, `jCongr`, `jId`: localized ordinary open adjunction,
  its canonical composition, proof-independent equality transport and identity.
- `squareP`: inverse pullback compositor, equality transport, pullback compositor.
- `betaInvApp`, `betaInvApp_naturality`, `betaInv`, `betaInv_isIso`, `beta`:
  the specified open-unit transpose, its naturality and Cartesian invertibility,
  and the inverse base-change isomorphism.
- `jAdj_unit_isIso`, `openToS`, `openToS_isIso`, `pi`: inverse open unit, its
  inverse/direct adjunction mate, clopen invertibility and unit-defined projector.
- `alpha`: canonical beta, clopen projector, canonical compositors and equality
  transports, for any commutative proper/quasi-compact-open square.

The new natural statement describes every one of these constructions. It allows
arbitrary coefficient transitions and all derived objects, and distinguishes the
Cartesian hypothesis needed for beta from the general non-Cartesian square used
for alpha. It asserts none of the item's pasting laws. The source is the existing
ringed-diagram specialization of Stacks 0F7B--0F7D and the adjunction/open-unit
normalizations recorded in the source docstrings, serving the composition/refinement
sentence of `fix-prop-projection-formula.proof.md`.

Searches for this new owner were repeated with the prescribed tools. LeanSearch and
LeanFinder, query `canonical semilinear coefficient system proper open pullback
compositor clopen projector`, each returned eight unrelated results (locally constant
maps/clopen sets and profinite Nobeling projections). Mathlib grep
`SemilinearProperOpen|pushComp_existsUnique|betaInvApp` in `CategoryTheory` returned
zero hits. The raw results are recorded in `mathlib_searches`. Upstream WeilConjectures
has no such namespace; the project source gives these exact declarations. DAG search
for their qualified names finds only the old theorem owner, while NB's definition
record lists none of these 24 helpers. `blueprint_refs.py search "semilinear proper
open"` found zero blueprint nodes; `ancestor` returned `fix-prop-projection-formula`.
The new node uses that ancestor and prepends the item to its inherited via list.

## Second reading by NV

This is the required self-check; the dispatcher forbids other agents and the
maintainer supplies the independent review. Re-read the unchanged item module,
its node statement and the published source of all 24 comparison declarations.
The hypothesis/clause match above carries over from the accepted substance review.
Checked the `systems` fields at module lines 153--175: its `openAdj`, `pComp`,
`pId` and `alpha` now have the new definition-node owner, and their transitive
helpers are all included. Verified the unique section formulas fix `pushComp`
and the identity before localization; `betaInvApp` uses the open unit;
`openToS` uses its inverse; `pi` uses the pull/direct-image unit and inverse
clopen comparison; `alpha` uses exactly beta, pi and the pinned compositors.
No isomorphism or transformation is assumed from a pasting theorem.

Checked all identity, empty-open, arbitrary-system and non-Cartesian cases again
against these definitions. The definition node imposes no finite-ring, flatness,
boundedness or finite-type/separatedness assumption on the general canonical data.
The item's finite-type base remains exactly as reviewed. The finite `ProperOpen*`
definition-owner issue in the return was advisory; its existing theorem dependency
and all finite Lean definitions remain unchanged.

## Final validation

The initial retained-packet dry run passed at `8189c27753`. The repaired packet
changes no Lean source or NB record. The item retains its 24-declaration inventory;
the new definition node records the separate 24-declaration inventory above.
Only the item's `lean` and `stmt_deps` fields differ from the current DAG, plus the
new definition node and this report. Compilation and the final dry run are performed
through the prescribed `scompile.py` and `deliver2.py` wrappers.
