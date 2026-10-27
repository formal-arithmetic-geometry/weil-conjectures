## Worker report

Item: lem-exc-finite-quotient-constructible-reduction. Module:
`Sheaf.Paper.FiniteQuotientConstructibleReduction`. The theorem is
`AlgebraicGeometry.Scheme.finiteQuotient_constructible_reduction`; its proof is `sorry`.
Two transparent helpers belong to this same quotient-label construction and are listed
in lean.declarations: Mathlib scalar restriction along the published constant quotient
coefficient map, and the actual quotient label M/IM with its canonical quotient action.
There is no new mathematical notion, no hollow data, and no new DAG node.

Hypothesis and clause correspondence:

- An arbitrary scheme T: `(T : Scheme.{u})`. No separation, Noetherian, nonemptiness,
  or quasi-compactness hypothesis is introduced.
- A finite commutative ring A: `(A : Type u) [CommRing A] [Finite A]`.
  A finite ring can be represented in the scheme universe; module labels and sections
  live in `Type (u+1)`, as required by the site's object universe. Zero rings are allowed.
- An arbitrary ideal and B=A/I: `(I : Ideal A)` and the literal type `A ⧸ I` throughout.
  No free ring B, arbitrary quotient map, or chosen presentation is substituted.
- Constant rings A_T and B_T: `proEtaleConstantRing`, i.e. Mathlib `constantSheaf`
  with lifted coefficients. `proEtaleConstantRingMap (T := T) (Ideal.Quotient.mk I)` is the existing
  constant sheaf map, from `def-sp-proetale-constant-coefficient-ring-map`, now cited
  in stmt_deps. The `sheafCompose` forgetful functor maps it to a ring-sheaf map.
- A sheaf F of B_T-modules: `F : proEtaleRingModules T
  (proEtaleConstantRing T (A ⧸ I))`. This is `ringedSiteModules`, transparently
  Mathlib `SheafOfModules`, rather than an arbitrary category or fixed-module replacement.
- Restriction of scalars: `proEtaleQuotientRestrict` is exactly
  `SheafOfModules.restrictScalars` of that canonical quotient map. It does not replace
  the underlying sections or restriction maps.
- Intrinsic A-constructibility: the binder `hF` uses the already published
  `IsConstructibleProEtaleModuleSheaf` on that restriction. The live superset dependency record is retained unchanged.
- Intrinsic B-constructibility: the first conjunction uses the same intrinsic predicate
  with `A ⧸ I` and F. The needed finite-ring evidence is the existing theorem
  `Finite.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective` supplied
  directly as an explicit predicate argument. It is not an added hypothesis or a new
  theorem proved in this stage, nor a statement-level `let`/hidden `have`.
- Any witnessing finite constructible locally closed stratification: universal `S :
  Stratification T` with `0 < S.n`. Its inherited `Topology.Stratification` supplies
  the finite partition, constructibility, local closedness and disjointness; the scheme
  fields supply the domains and immersions. The displayed stalk-finiteness premise
  says this particular S witnesses the original sheaf's finite stalks.
- Any chosen trivializing cover: dependent families `J i`, `U i`, `f i`, with
  `Presieve.ofArrows (U i) (f i)` in the actual `ProEt.precoverage` coverings.
  Neither an alternative cover nor a refinement is existentially chosen in the conclusion.
- Finite A-module labels M: dependent `ModuleCat (ULift A)` labels and
  `∀ i j, Finite (M i j)`. The chart premise is a module-sheaf isomorphism on the
  localized site from the pullback of Res F to
  `proEtaleConstantModuleSheafOverOfUniverses ... (M i j)`.
- The same strata, covers, and quotient labels: the last conclusion uses the literal
  `S.immersion i`, `U i j`, and `proEtaleQuotientLabel A I (M i j)`. It asserts finiteness
  of that label and `Nonempty` of the B-module-sheaf isomorphism. `Nonempty` wraps the
  existence of an isomorphism; no constant sheaf or quotient data is chosen from it.
  The original constant chart used the A-pullback of Res F; the final chart uses
  the canonical B-pullback of F, precisely as in the node's step 1.
- M/IM: the helper restricts the original lifted action along A→ULift A, forms
  `M ⧸ (I • (⊤ : Submodule A M))`, uses Mathlib's canonical `Module (A ⧸ I)` instance
  from `Mathlib.Algebra.Module.Torsion.Basic`, and restricts along ULift B→B.
  In particular its action on representatives is [a] [m] = [a*m]. Every definition
  contains real data; all local instance bindings are inside this data construction.
- Empty strata and members remain covered by the quantifiers; no Nonempty type,
  nonzero model, or IM=0 assertion occurs. No Tor amplitude, flatness, derived object,
  or complex is a hypothesis.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its Hom.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`,
  `ProEt.precoverage` and `ProEt.mk` (transitively publicly imported).
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`;
  the published coefficient map is its map on the actual quotient homomorphism.
- `Sheaf.Paper.StratumScalarExtension`: `Scheme.proEtaleConstantRingMap`,
  applied to `Ideal.Quotient.mk I` and mapped by the forgetful sheaf functor.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  `Sheaf.AlgebraicGeometry.ProEtaleOperations`: `Scheme.proEtaleRingModules`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`, exactly the recorded general ring-sheaf dependency.
- `Sheaf.Paper.ProEtaleFixedModuleConstructible` publicly imports
  `Sheaf.Paper.ProEtaleConstructibleSheaf`:
  `Scheme.IsConstructibleProEtaleModuleSheaf`, retained in the dependency record.
  Its full definition uses positive Stratification, canonical pullbacks, local
  module-sheaf charts, and finite geometric module stalks.
- `Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses`:
  `proEtaleConstantModuleSheafOverOfUniverses`, the actual sheafification on the
  localized ringed site specified by the recorded dependency. Its same-universe
  predecessor and predicates were also read; the theorem uses the recorded generalized
  constant-model constructor directly.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `proEtaleConstantRing`, `proEtaleConstantModulePullback` with its canonical
  `proEtaleCoefficientInverseImageMap`. `ProEtaleGeometricStalk` supplies the
  actual varying-ring `proEtaleGeometricModuleStalk` used in the witness premise.

The proof-plan modules are imported without `public`: the constant coefficient comparison
(`ProEtaleBoundedConstructibleTriangulated`), constant exactness
(`FiniteTypeConstantExact`), and module stalk functor. Mathlib `CoverLifting` is imported
for the localization/sheafification compatibility leaf. The other cited module-sheafification
and inverse-image modules are already public transitive imports; there is no import cycle.
The complete six-step accepted node proof, including B-linearity and the empty-member
qualification, is in the theorem docstring.

Sources opened: `literature/stacks-project/sites-modules.tex`, section-constant and
lemma-constant-exact (093I/093J), and the current main-20261015
`thm-exc-explicit-preservation.proof.md`. The present task's expanded, reviewed six-step
quotient-label argument is its precise extracted statement; no unit statement is altered.
No statement correction or disputed mathematical claim is needed.

Edge cases checked mathematically before writing: I=0 (ordinary unchanged labels),
I=A (zero quotient ring; on nonempty members the quotient label is zero),
A=0, M=0, A=Z/4 and I=(2), an empty scheme T, empty strata, an empty cover of an empty
stratum, and an empty member carrying M with IM nonzero. The final chart is meaningful
in all these cases because it is about constant sheaves, not faithfulness of the abstract
constant-module functor on an empty site. Positive S.n is the existing convention even
for T empty. No finite cover index type is required.

Searches made (2026-10-23):

- msearch leanfinder: "A constructible sheaf of modules over A that is a module over A/I
  remains constructible over A/I with local quotient models M/IM". Eight hits, including
  localCohomology.ringModIdeals, sheaf finite presentation, and AdicCompletion's quotient
  module action; no pro-etale constructibility or preserved-cover theorem.
- msearch loogle: `"SheafOfModules", "restrictScalars"`. Twelve hits, principally
  presheaf scalar-restriction implementations. The recorded exact sheaf restriction
  was read in its Mathlib source and used directly; no matching conclusion exists.
- msearch grep: `constructible.*(quotient|scalar)|locallyConstant.*quotient`.
  One hit, Mathlib/Topology/DiscreteQuotient.lean:418 (`LocallyConstant` lift);
  unrelated to module-sheaf constructibility.
- msearch leansearch: "A constructible module sheaf over a finite ring A whose action
  factors through A/I is constructible over A/I with the same cover and quotient labels".
  Eight hits: general SheafOfModules, module_finite_of_liesOver and quasi-coherent
  constructions, none the desired assertion.
- rg in both lean/WeilConjectures and lean/Sheaf for quotient/constructible combinations,
  finiteQuotient, quotient labels, and the exact node id; existing derived preservation,
  etale scalar-change and different finite-level results do not give this node's
  intrinsic assertion with these labels and unchanged covers. Exact helper/theorem-name
  search in those trees and dag/lean_names_upstream.json found no declarations.
- `grep -rn` of the exact node id in lean/WeilConjectures returned no hits.
- Mathlib quotient-action search found the exact existing instance
  `Module (R ⧸ I) (M ⧸ I • ⊤)` in Algebra/Module/Torsion/Basic.lean:648; it is reused.

Validation: scompile.py compiled both the sandbox module and its intended library module
cleanly after the returned-delivery repair (13.2s and 10.2s), with no errors or
non-sorry warnings. Self-check confirmed that the theorem signature matches lean.statement
verbatim, only lean and the added landed stmt_dep differ from the live item, the
constructibility dependency copy equals live byte for byte, the duplicate helper is gone,
and exactly the theorem proof remains sorry. All Lean lines are at most 100 characters.

## Second reading by Q30

A second pass through the node, the dependency definitions, and the final file matched
all binders and both conclusions as detailed above. In particular, S and each U i j occur
unchanged on both sides; the final constant label is the literal quotient of the original
M by ideal multiples. The finite-stalk witness belongs to the original scalar restriction,
not to F as an extra assumption. Stratification already includes constructibility and
local closedness, so no duplicate predicate is necessary. Quotient finiteness is derived
from A's finiteness, not assumed. The scalar map is the canonical one; no arbitrary map
or arbitrary B-action is quantified. All universes and variables are explicitly bound,
and autoImplicit is false. The live Q150 constructibility record remains unchanged;
its declarations already expose the intrinsic predicate used here. No statement-level lets,
file-local notation, private objects,
or additional axioms occur. This is the worker's self-audit; the dispatcher's maintainer
review supplies the independent reading, and no other agent was started.

## Returned-delivery repair

- H13: retained the live Q150 superset record of
  `def-weil-proetale-constructible-sheaf` byte for byte, including both declaration names;
  removed the dependency-module report section. No dependency rebind is delivered.
- H4/H12: deleted the duplicate `proEtaleQuotientCoefficientMap`. The scalar restriction
  now uses `(sheafCompose ... (forget₂ ...)).map
  (proEtaleConstantRingMap (T := T) (Ideal.Quotient.mk I))` directly, publicly imports
  `Sheaf.Paper.StratumScalarExtension`, and cites its owning definition node in stmt_deps.
  The theorem signature, quotient-label construction, and six-step proof docstring
  are unchanged. The removed helper is also removed from lean.declarations.
