## Worker report

The module Sheaf.Paper.SupportedNormAlgclModelRigidityTransfer states
AlgebraicGeometry.ProEtale.CondensedRing.supported_norm_algcl_model_rigidity_transfer.
Its only theorem proof is `sorry`. The repair adds one definition DAG node owning
four existing published declarations, with no new Lean definitions or axioms and
no changes to the accepted natural-language statement or proof split.

The immutable-head review of 263ef528ab52 returned this packet for H2:
the statement dependency added for `closedRestrictionRho` was a theorem node,
although its four companion definitions do not depend on that theorem. This
repair supplies the requested definition owner and changes that dependency.
The saved packet first passed the required dry run at b7403def3f6; passing the
mechanical check did not remove the independent reviewer's ownership finding.

Source read: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-sf-comp-coherence/det-sf-comp-coherence-refinement.proof.md, (2), first
paragraph. The current DAG extracts this conditional norm-coefficient obligation
from the closed-fibre comparison. As explicitly recorded in its source and proof
origin, the exact full-generality references for the derived-generation and topology
defect inputs remain WANTED. The Lean statement does not assume those inputs:
they belong to the postponed proof, whose six steps are copied into its docstring.
The framework conventions were checked in coord/pefw-upstream-framework.md.

Clause-by-clause correspondence:

- The fixed prime is `(ℓ : ℕ) [Fact ℓ.Prime]`. The fixed norm-topological algebraic
  closure is `PadicAlgCl ℓ`. The finite intermediate fields are quantified by
  `E : PadicAlgCl.FiniteIntermediateField ℓ`, the subtype of intermediate fields
  of `ℚ_[ℓ]` in this same closure with `FiniteDimensional ℚ_[ℓ] E`.
  Thus the quantifier includes the base field and every finite subextension.
- The coefficient is literally `Profinite.continuousMapRingObj E` in the premise
  and `Profinite.continuousMapRingObj (PadicAlgCl ℓ)` in the conclusion. The
  constructor uses all continuous maps; no finite-subextension-valued condition
  is placed on the algebraic-closure coefficient. The finite A, integral rings,
  and general Λ in the introductory convention are context for the coefficient
  family, not additional quantified premises of this conditional implication.
  Neither A nor a separately selected finite E occurs in its conclusion. The
  general convention is imported through LocalizingAdmissibleCoefficients;
  the theorem selects precisely its continuous norm algebraic-closure case.
- On each V, `condensedRingObj R V` is the pulled-back ring `p_V^*R` and
  `Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) ...` is the actual internal
  module category. `DerivedCategory.singleFunctor _ 0` embeds a module in degree
  zero in the ordinary uncompleted derived category. No completion or subcategory
  of complete objects is used.
- The schemes are `{T₀ T : Scheme.{u}}` with both `CompactSpace` and
  `QuasiSeparatedSpace` instances. The closed pair is `(t : T₀ ⟶ T)` with
  `[IsClosedImmersion t]`. There is no condition on the complement of t.
- `ht` quantifies over every abelian sheaf on `T.smallEtaleTopology` satisfying
  `Scheme.IsTorsionAbelianSheaf`. This is the colimit-of-positive-integer-kernels
  definition of locally torsion; there is no common annihilator. It requires
  `Function.Bijective (Etale.cohomologyMap t F q)` for every `q : ℕ`, including
  zero. This is the recorded actual cohomological restriction, not the existence
  of an unspecified group isomorphism.
- An allowed chain is `(tree : QcqsOpenClosedTree T) (p : tree.Path S)`. Its open
  steps are quasi-compact open immersions and its closed steps have complementary
  quasi-compact opens. A path can stop at any vertex; there is no leaf condition.
  `p.extension R` is definitionally the iterated actual open lower shriek/closed
  lower star, and the root path gives identity, exactly J in the node.
  Conversely, any node chain embeds in such a tree by adjoining complementary
  children as one-vertex subtrees. Every chain vertex is qcqs, inductively from T:
  quasi-compact opens in qcqs schemes are qcqs and closed subschemes of qcqs
  schemes are qcqs. Its complementary siblings are likewise qcqs. Closed
  immersions are quasi-compact, so the tree adds no restriction on a chain.
  Complementary closed structures do not affect a path's actual edge maps.
- `HasFiniteConstantLocalModel R S L` is the dependency's existing definition:
  a pro-etale cover, finitely presented scalar modules chosen on the point,
  and local isomorphisms to their pullbacks. Finite presentations on the point
  are finite scalar matrices; this is the node's `R_S ⊗_R P`. No arbitrary
  local finite-presentation matrices, global trivialization, rank, or common
  field of definition for transition maps is imposed.
- The arrow is `(closedRestrictionRho R t).app
  ((DerivedCategory.singleFunctor _ 0).obj ((p.extension R).obj L))`.
  This helper is transparently `Functor.rightDerivedPullback` of the module
  adjunction-unit section restriction and uses the actual total derived
  `condensedModuleSections` to abelian groups. Its source is RΓ(T,JL[0]) and
  target is RΓ(T₀,t*JL[0]); the inverse image is exact termwise upperStar.
  No preservation of K-injectives under pullback is assumed.
- `hfinite` quantifies over every finite intermediate E, every scheme S, every
  tree and path, and every finite scalar local model L; its IsIso assertion is
  exactly B_E(t). The conclusion repeats the full scheme/tree/path/L quantifier
  for the all-continuous algebraic-closure ring, hence exactly B_Ω(t). The B
  notation is expanded directly and has no additional definition node.
- The theorem has no properness, regularity, Noetherianity, invertibility-of-ℓ,
  common finite field of definition, or image-comparison hypothesis/conclusion.
  It does not identify the all-continuous coefficient with the finite-field
  colimit and does not use the completed field PadicComplex.

All variables and universes are explicit; `set_option autoImplicit false` is on.
The small sites are Scheme.{u} small sites with abelian groups in universe u+1,
as in the recorded framework. The indexing universe remains that convention;
there is no extra universe equality or smaller test-object universe.

Dependency declarations read and used (each module is imported publicly):

- `sk-def-localizing-closure`: `Sheaf.Paper.LocalizingAdmissibleCoefficients`, `AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient`; companions `CategoryTheory.IsLocalizingSubcategoryOfSize`, `CategoryTheory.localizingClosureOfSize`.
- `sk-def-sfb-module-derived-pushpull`: `Sheaf.Paper.CondensedModuleDerivedPushpull`, `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward`; companions `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPullback`, `AlgebraicGeometry.ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction`, `CategoryTheory.Functor.rightDerivedFunctor`, `CategoryTheory.Functor.rightDerivedFunctorPlus`, `CategoryTheory.Functor.leftDerivedFunctor`, `CategoryTheory.Functor.leftDerivedFunctorCounit`, `CategoryTheory.Functor.isIso_leftDerivedFunctorCounit_app_of_kFlat`, `AlgebraicGeometry.ProEtale.CondensedRing.preservesKFlatQuasiIso_upperStar`, `AlgebraicGeometry.ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunctionPlus`, `AlgebraicGeometry.ProEtale.CondensedRing.rightDerivedLowerStarIso`, `AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarIso`.
- `def-sfb-condensed-module-sections`: `Sheaf.Paper.CondensedQcqsPushforwardContinuity`, `AlgebraicGeometry.ProEtale.condensedModuleSections`.
- `def-weil-pbc-etale-site`: `Mathlib.AlgebraicGeometry.Sites.Etale`, `AlgebraicGeometry.Scheme.smallEtaleTopology`; companions `AlgebraicGeometry.Scheme.Etale`.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`, `AlgebraicGeometry.Scheme.ProEt`.
- `def-weil-size-convention`: metatheoretic/convention node; no Lean declaration to import.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`; companions `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `AlgebraicGeometry.IsClosedImmersion`.
- `def-weil-pbc-scheme-conventions`: metatheoretic/convention node; no Lean declaration to import.
- `def-weil-pbc-torsion-etale-sheaf`: `WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf`, `AlgebraicGeometry.Scheme.IsTorsionAbelianSheaf`.
- `def-weil-pbc-etale-cohomology`: `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`, `AlgebraicGeometry.Etale.cohomology`; companions `AlgebraicGeometry.Etale.rightDerivedGlobalSections`.
- `def-weil-pbc-cohomology-pullback`: `Sheaf.AlgebraicGeometry.ModuleDerivedCohomologyPullback`, `AlgebraicGeometry.Etale.abelianDerivedCohomologyPullback`; companions `AlgebraicGeometry.Etale.cohomologyMap`, `CategoryTheory.Sheaf.H.mapFunctor`, `AlgebraicGeometry.Etale.moduleDerivedCohomologyPullback`, `AlgebraicGeometry.Etale.moduleLerayPlus`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`, `AlgebraicGeometry.IsOpenImmersion`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`; companions `AlgebraicGeometry.QuasiCompact`.
- `def-sfb-module-open-lower-shriek`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`, `AlgebraicGeometry.ProEtale.CondensedRing.openImmersionLowerShriek`; companions `AlgebraicGeometry.ProEtale.CondensedRing.openImmersionLowerShriek_comp_forget`, `AlgebraicGeometry.ProEtale.CondensedRing.openImmersionLowerShriek_additive`, `AlgebraicGeometry.ProEtale.CondensedRing.preservesFiniteLimits_openImmersionLowerShriek`, `AlgebraicGeometry.ProEtale.CondensedRing.preservesFiniteColimits_openImmersionLowerShriek`, `AlgebraicGeometry.ProEtale.CondensedRing.preservesHomology_openImmersionLowerShriek`.
- `def-sfb-module-lower-star`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`, `AlgebraicGeometry.ProEtale.CondensedRing.lowerStar`; companions `AlgebraicGeometry.ProEtale.CondensedRing.lowerStar_comp_forget`, `AlgebraicGeometry.ProEtale.CondensedRing.lowerStar_obj_X`, `AlgebraicGeometry.ProEtale.CondensedRing.lowerStar_obj_smul`, `AlgebraicGeometry.ProEtale.CondensedRing.lowerStar_additive`, `AlgebraicGeometry.ProEtale.CondensedRing.preservesFiniteLimits_lowerStar`.
- `sk-def-sfb-constructible`: `Sheaf.Paper.CondensedConstantConstructibility`, `AlgebraicGeometry.ProEtale.IsConstantModelConstructible`; companions `AlgebraicGeometry.ProEtale.HasFiniteConstantLocalModel`, `AlgebraicGeometry.ProEtale.IsFiniteConstantStratified`, `AlgebraicGeometry.ProEtale.ConstantModelConstructible`, `AlgebraicGeometry.ProEtale.constantModelBoundedConstructible`, `AlgebraicGeometry.ProEtale.ConstantModelBoundedConstructible`, `AlgebraicGeometry.ProEtale.ConstantModelConstructibleFiniteTor`.
- `def-sfb-qcqs-open-closed-tree`: `Sheaf.Paper.QcqsOpenClosedTree`, `AlgebraicGeometry.ProEtale.QcqsOpenClosedTree`; companions `AlgebraicGeometry.ProEtale.QcqsOpenClosedTree.Path`, `AlgebraicGeometry.ProEtale.QcqsOpenClosedTree.Path.toRoot`, `AlgebraicGeometry.ProEtale.QcqsOpenClosedTree.Path.IsLeaf`, `AlgebraicGeometry.ProEtale.QcqsOpenClosedTree.Path.extension`.
- Statement owner `def-sfb-closed-restriction-actual-map`: `Sheaf.Paper.ClosedRestrictionDerivedOperations`, the four definitions `AlgebraicGeometry.ProEtale.CondensedRing.closedRestrictionSections`, `AlgebraicGeometry.ProEtale.CondensedRing.closedRestrictionPhi`, `AlgebraicGeometry.ProEtale.CondensedRing.closedRestrictionPsi`, and `AlgebraicGeometry.ProEtale.CondensedRing.closedRestrictionRho`. Proof-only node `lem-sfb-closed-restriction-derived-operations` uses the same module: `AlgebraicGeometry.ProEtale.CondensedRing.closed_restriction_derived_operations`; companions `AlgebraicGeometry.ProEtale.CondensedRing.closedRestrictionSections`, `AlgebraicGeometry.ProEtale.CondensedRing.closedRestrictionPhi`, `AlgebraicGeometry.ProEtale.CondensedRing.closedRestrictionPsi`, `AlgebraicGeometry.ProEtale.CondensedRing.closedRestrictionRho`, `AlgebraicGeometry.ProEtale.CondensedRing.ClosedRestrictionProducts`, `AlgebraicGeometry.ProEtale.CondensedRing.HasClosedRestrictionFilteredModel`, `AlgebraicGeometry.ProEtale.CondensedRing.ClosedRestrictionFilteredRepresentatives`.

The two added statement dependencies are definition owners:
`def-sfb-qcqs-open-closed-tree` is already landed and supplies the support-path
packaging; the new `def-sfb-closed-restriction-actual-map` owns the unchanged
published `closedRestrictionSections`, `closedRestrictionPhi`,
`closedRestrictionPsi`, and `closedRestrictionRho`. Its Lean attachment is
`existing: true` on `Sheaf.Paper.ClosedRestrictionDerivedOperations`.
`lem-sfb-closed-restriction-derived-operations` remains in `proof_deps` for
continuity and compatibility, and has been removed from the saved packet's
added statement dependencies. The same public module import still supplies the
four definitions, so the Lean file stays byte-identical to the returned packet.
All recorded proof dependencies with usable Lean records or Mathlib matches
remain imported (plain imports except where the same module supplies a statement
definition).
The two newly split proof inputs (finite-field derived generation and coefficient
topology-defect rigidity) have no recorded declarations; they are left in the DAG
and the proof docstring. They are not required to type this stage-2 statement.

Edge cases checked before writing: zero local modules (rank zero allowed), empty
schemes (leaf trees and empty covers allowed), length-zero chains (`Path.root`,
identity extension), chains stopping at internal vertices, varying local ranks,
E equal to the base field, arbitrary characteristics (including ℓ), closed pairs
with non-quasi-compact complementary open, and arbitrary transition maps for Ω
models. None is excluded by a binder or predicate. For t the identity, restriction
is the canonical identity comparison; no strict containment or nonempty support
is imposed. These are statement checks, not new proof claims about the transfer.

Searches actually run for this item:

- msearch leanfinder: "Closed immersion torsion cohomology rigidity supported finite
  scalar local models norm topology algebraic closure finite l adic extensions".
  Eight hits on qcqs sections, proper schemes and module support; no transfer theorem.
- msearch leansearch: "Restriction cohomology supported local systems norm
  topological algebraic closure transfer finite extensions". Eight hits on algebraic
  closure restriction and normed scalar restriction; no scheme-level theorem.
- msearch loogle: `"Condensed", "ContinuousMap"`: zero hits.
- msearch grep: `rigidity|Condensed.*AlgebraicClosure|AlgebraicClosure.*Condensed`:
  four unrelated hits in intermediate value theory and complex manifolds.
- rg on lean/Sheaf and lean/WeilConjectures for supported rigidity, support-chain
  names, and NormAlgCl: found the rational transfer, three-term scalar rigidity,
  and supported image comparison modules. Their hypotheses/conclusions differ:
  none states the conditional finite-field-to-all-continuous-Ω implication.
- Exact node-id grep on lean/WeilConjectures: no hit. The Sheaf three-term theorem
  cites this item only in its proof plan; it is not a declaration of the item.
- Read QcqsOpenClosedTree, CondensedConstantConstructibility and
  ClosedRestrictionDerivedOperations in full for their used definitions; read
  the coefficient constructor and finite intermediate field signatures. These
  supply the needed notions. The repair adds an owning definition node with an
  existing attachment, rather than introducing any new Lean declaration.

No established counterexample or untypable clause was found, and no statement
correction was made. The source's WANTED full-generality references remain openly
recorded; the proof is postponed as requested.

Validation of the repair: the unchanged item file passed scompile.py in both
sandbox and library module modes, without warnings (4.6 s and 3.7 s). The new
node uses existing declarations and has no delivered module to compile. The
initial saved-packet dry run passed at b7403def3f6. The first corrected-packet dry run found the newly required `import_flags`
field missing on the new definition node. The live validator (updated
2026-10-23) requires it, so `import_flags: []` is now included. No Lean change
was needed. The corrected-packet dry run printed OK at a59510ad13b: server preflight
and compilation passed; nothing was pushed by that dry run. The required
deliver2.py push follows this validation.

## New nodes

`def-sfb-closed-restriction-actual-map` owns the actual uncompleted derived
restriction and its three companion definitions already in
`Sheaf.Paper.ClosedRestrictionDerivedOperations`, with `lean.existing: true`.
Its source is the current blueprint's refinement proof (2), closed-fibre
comparison, with the canonical construction documented by Stacks 09AA/015F in
the existing module. It introduces a commutative condensed coefficient, schemes
and their morphism; uses the pulled-back coefficient/module categories,
underived sections and the canonical module adjunction; defines section
restriction, Phi = ordinary derived sections, Psi = exact termwise pullback
followed by ordinary derived sections, and Rho = universal derived descent.
The construction is available for arbitrary scheme morphisms, including the
closed immersion used by the item. No preservation or continuity theorem is
asserted by this node.

Fresh LeanSearch query "Actual natural restriction from ordinary derived global
sections to derived sections after exact module pullback on pro etale sites"
returned eight general section/pullback hits. LeanFinder query "Canonical right
derived restriction natural transformation obtained from adjunction unit and
exact inverse image" returned eight general derived-adjunction hits. Mathlib
grep `closedRestriction(Sections|Phi|Psi|Rho)|rightDerivedPullback` in
CategoryTheory returned no hits. Upstream grep found the general concrete
`Functor.rightDerivedPullback`; Sheaf grep found exactly the specialized four
definitions being attached. DAG grep found only companion names on the
compatibility theorem, not an owning definition node. `blueprint_refs.py search
'closed restriction'` found one unrelated open/closed detection theorem;
`ancestor` returned `det-sf-comp-coherence-cocycle`. Exact output of the three
search-tool calls and source/DAG greps is retained in `mathlib_searches` of the
new node. These searches justify an existing-definition attachment, not a copy.

Clause check against the existing module: `closedRestrictionSections` is the
whiskered adjunction unit followed by the terminal-object base-change
restriction; `closedRestrictionPhi` abbreviates
`(condensedModuleSections Λ V).rightDerivedFunctor`;
`closedRestrictionPsi` abbreviates `(upperStar Λ t).mapDerivedCategory ⋙
closedRestrictionPhi Λ T₀`; and `closedRestrictionRho` is exactly
`Functor.rightDerivedPullback (upperStar Λ t) (closedRestrictionSections Λ t)`.
The upstream constructor descends `rightDerivedPullbackAux` using the universal
right-derived property. It does not select any data from
`closed_restriction_derived_operations`. The node therefore has definition-only
statement prerequisites and empty proof/proof_deps. Its statement does not
require qcqs, a nonempty scheme, a strict closed inclusion, or a complement
condition. Empty schemes, identity morphisms, zero modules/complexes, and
unbounded complexes remain included.

## Second reading by Q03

The dispatcher forbids starting another agent, so no independent second reader
was started. The maintainer's supplied independent immutable-head review found
all mathematical clauses correct and H11 advisory. This repair retains that
reviewed Lean file byte-for-byte (SHA-256
`6dbc4b5f04ad2d2ee1cd86be87667c1a58496d1227579267e84bc0d2cc88f31d`).

Self-check with the saved node, current live node, item file and definition
source open: compared to live, the item changes only `lean` and the addition of
two definition owners in `stmt_deps`. Compared to the returned saved packet,
only the dependency ownership record/report changes: the theorem dependency is
replaced by `def-sfb-closed-restriction-actual-map`, and `proof_deps` is unchanged.
The theorem signature still matches `lean.statement` verbatim; all coefficient,
torsion, qcqs, support-path, finite local model and IsIso clauses above remain
unchanged. The new definition node cites exactly its prerequisite notions and
attaches the existing four definitions without copying their module or importing
the structural theorem as a statement prerequisite.
