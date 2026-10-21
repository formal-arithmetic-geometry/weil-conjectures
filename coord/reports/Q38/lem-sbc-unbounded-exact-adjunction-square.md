## Worker report

This delivery states lem-sbc-unbounded-exact-adjunction-square in
Sheaf.CategoryTheory.UnboundedExactAdjunctionSquare. The declarations are in namespace
CategoryTheory.UnboundedExactTower. The main theorem gives clauses (1)-(3), and the
second theorem unboundedExactAdjunctionSquare_mates gives clause (4). Both proofs are
sorry. Every auxiliary definition contains real data; the Prop definitions simply
spell out the assertions. The H2 ownership repair below adds a definition node for the already existing
exact evaluation interchange and its preservation instances; no statement correction
or dependency module is proposed.

Hypotheses and objects, clause by clause:

- The small ringed sites are C,D : Type u with SmallCategory, topologies J,K, and
  R : Sheaf J RingCat.{u}, S : Sheaf K RingCat.{u}. The existing ringedSiteModules
  is the actual SheafOfModules category, without a second abelian instance.
- ExactMorphism R S packages the given RingedToposMorphism, IsIso of its actual
  structural ringMap, the given module inverse image inverse, its Additive and
  finite-limit/finite-colimit preservation, and inverse ⊣ ringed.modules. The direct
  image is the recorded induced module direct image, not an arbitrary functor. The
  left adjoint is supplied with its ordinary adjunction, as the node's u^* is; any
  left adjoint of this induced direct image is its module inverse image up to the
  unique adjunction-compatible comparison. The coefficient isomorphism is retained.
- Four independent explicit HasDerivedCategory universe parameters choose the derived
  categories of the two module categories and their towers. The mate theorem uses
  another four at the other two corners. There is no equality imposed on these sizes.
- moduleResolutions and towerResolutions use the existing Grothendieck resolution
  construction. The latter applies smallModuleDiagrams_isGrothendieckAbelian to
  AsSmall.{u} ℕᵒᵖ and transports along Equivalence.congrLeft AsSmall.equiv. This handles
  the dependency's same-universe index interface without restricting the site universe
  or changing the actual tower category. Neither theorem adds a resolution hypothesis.
- J = positive natural numbers in the opposite order is represented by ℕᵒᵖ, with
  op n meaning positive level n+1. Towers are literally functors into ringedSiteModules,
  constants are Functor.const, and evaluation is CategoryTheory.evaluation.
- Clause (1) is TowerProperties at R and S: Nonempty of ev_(op 0) ⊣ const, preservation
  of finite limits and colimits for constants and every evaluation, and preservation
  of CochainComplex.IsKInjective by both functors on all unbounded cochain complexes.
- The first part of clause (2) is the actual data constantInterchange and the existing
  towerDerivedEvaluationInterchange. They are composed of mapDerivedCategoryCompIso
  and the localization of the ordinary identity-component comparison. The two maps
  constantComparison and evaluationComparison are mateEquiv applied to these exact
  left squares and the canonical mapDerivedCategoryRightDerivedAdjunction. In particular
  they are specified maps, not arbitrary comparisons supplied as extra hypotheses.
- ComparisonsCompatible first asserts IsIso for these two natural transformations,
  giving the b^Delta and b^n natural isomorphisms in clause (2). Its next two conjuncts
  are their identity normalizations on K-injective complexes. cochainUnit is the actual
  canonical rightDerivedFunctorUnit, transported from homotopy categories by the
  quotient comparison isomorphisms. Each equation says that applying the comparison
  between the two universal units gives the other universal unit. Since those units
  are invertible on K-injectives (and constants and evaluations preserve them), this
  is precisely identity on Δu_*I, respectively u_*I_n, including the localization factors.
  The constant equation explicitly includes Q of the cochain-level identity-component
  compConstIso for G: the two constant/direct-image composites are canonically isomorphic,
  and this factor identifies their sources.
- Clause (3) is the next pair of conjuncts: for every M,N and every derived morphism t,
  the homEquiv of the transformed t equals the transformed homEquiv followed by the
  specified comparison. The exact inverse-image interchange is included on the left.
  The final four conjuncts state the constant and evaluation unit and counit equations
  explicitly. These imply no assumption about the faithfulness of derived evaluation.
- For clause (4), the four sites R,S,R',S' have ExactMorphism data f,f',g,h and the
  square's given inverse-image comparison θ : g.inverse ⋙ f'.inverse ≅
  f.inverse ⋙ h.inverse. This is the comparison specifying commutativity used by
  Stacks 07A7. localizedSquare localizes this very θ. towerSquare has component θ
  at each tower level, so it is the required termwise composition comparison.
  SquareCompatible has two conjuncts, universally quantified over derived K and
  over derived towers K and all levels n. Each uses mateEquiv for the ordinary or
  termwise canonical derived adjunctions and the localized θ. The first is the
  constant mate equation, the second the evaluation mate equation. The displayed
  interchange factors only make their sources and targets literally identical.
  No invertibility of either square mate is asserted.

Dependency declarations used:

- def-weil-size-convention: its recorded universe convention, implemented by explicit
  universes and HasDerivedCategory binders, not a new data object.
- Sheaf.CategoryTheory.RingedSiteModules: CategoryTheory.ringedSiteModules.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: DerivedCategory, HasDerivedCategory,
  DerivedCategory.Q, DerivedCategory.Qh, DerivedCategory.quotientCompQhIso.
- Mathlib.Algebra.Homology.HomotopyCategory.KInjective: CochainComplex.IsKInjective.
- Mathlib.CategoryTheory.Functor.OfSequence: the recorded ℕᵒᵖ inverse-system convention.
- Sheaf.CategoryTheory.DiagramSiteRealization: exists_diagramSite_realization, imported
  for the proof's diagram-site realization; the towers themselves remain functor categories.
- Mathlib.CategoryTheory.Adjunction.Mates: CategoryTheory.mateEquiv and TwoSquare.
- Sheaf.CategoryTheory.RingedToposMorphism: CategoryTheory.RingedToposMorphism, especially
  its structural map and its induced module direct image.
- Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization:
  towerDerivedEvaluationInterchange and the exact termwise preservation instances.
- Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck:
  smallModuleDiagrams_isGrothendieckAbelian, used to obtain tower resolutions.
- WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction:
  Adjunction.mapDerivedCategoryRightDerivedAdjunction.
- WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor:
  Functor.mapDerivedCategoryCompIso and Functor.mapDerivedCategoryNatIso.
- The existing proof interfaces are imported: RingedSiteKInjectiveResolutionsOfUniverses,
  KInjectiveTotalDerived, ResolvingDerivedAdjunction, the Mathlib localization and
  K-injective Hom interfaces, and upstream TowerEvaluationKInjective. The derived
  adjunction import already imports the homotopy adjunction and exact-right-adjoint
  K-injective-preservation interfaces. Their node proof plans are in the two docstrings.

The already-landed RingedToposMorphism and SmallModuleDiagramsGrothendieck nodes
are cited in stmt_deps. The H2 repair replaces the originally added normalization
theorem stmt_dep with the new definition node documented below. All original node
fields apart from lean and these additions are retained verbatim.

Sources read: derived.tex, lemma-pre-derived-adjoint-functors-general (0FND),
lemma-pre-derived-adjoint-functors (0DVC), lemma-K-injective (070I), and
lemma-adjoint-preserve-K-injectives (08BJ); sites-cohomology.tex,
remark-base-change (07A7). The constant/evaluation application is the node's
agent-supplied application of these results, not attributed to an unstated Stacks theorem.

Edge cases checked mathematically: positive level 1 is op 0 and is terminal in the
index category; every other positive level is included. Identity index arrows and
identity ringed morphisms are included. Zero ring sheaves and zero complexes are
allowed. No injectivity or surjectivity of transitions is imposed. No boundedness
condition is imposed on either source or target complex. Noninvertible square mates
are allowed. The site category may be empty. The theorem is not inferred by testing
derived tower morphisms at each level: its two mate equations are actual derived Hom
equalities. No STATEMENT-DISPUTED issue was found.

Searches for existing declarations:

- Retained msearch leanfinder query: Constant towers and evaluation preserve K-injective
  complexes and commute with derived adjunction units counits and square mates.
  Eight hits concerned derived adjunction units/counits and derived degree-zero tools;
  no complete match. Retained loogle query CategoryTheory.Adjunction.derived,
  CategoryTheory.conjugateEquiv returned zero hits. Retained grep for derived_unit,
  derived_counit, constAdjunction, evaluationAdjunctionRight and
  preservesKInjectiveComplexes in CategoryTheory found only evaluation adjunction tools.
- Repeated leanfinder query: Constant towers and evaluations preserve unbounded derived
  adjunctions with identity comparisons on K-injective representatives and transport
  the square mate. Eight hits were general derived-adjunction normalization lemmas.
- Repeated loogle query: CategoryTheory.mateEquiv, CategoryTheory.Adjunction.derived.
  Zero hits. Repeated msearch grep for unboundedExactAdjunctionSquare,
  constantComparison, towerDerivedEvaluationInterchange and
  preservesKInjectiveComplexes in CategoryTheory found zero Mathlib matches.
- Local rg of lean/WeilConjectures and lean/Sheaf for the item id and proposed declaration
  names found none. Broader constant/evaluation/mate searches located the reused
  adjunction and evaluation-normalization APIs, DerivedExactMate, MapDerivedCategoryMate
  and StrictConstantTowerOperations. The last concerns scheme constant coefficients;
  the others do not state all four clauses for arbitrary ringed sites.

Validation: only the prescribed scompile.py and deliver2.py wrappers were used. No
library file, published artifact, launcher script or shared Git state was directly changed.
On 2026-10-21 the required initial dry run reached the retained module: the earlier
missing published prerequisites no longer blocked compilation. It reported one source
mismatch in the constant representative-normalization equation. The repair inserts
DerivedCategory.Q.map of NatTrans.mapHomologicalComplex applied to the hom of the
ordinary identity-component compConstIso for G. This identifies constant after G with
termwise G after constant before the tower derived unit. No hypothesis, conclusion or
comparison was changed. The prescribed scompile.py then compiled both the sandbox and
library-named module cleanly (5.3 seconds each), with no warnings. The primary theorem's
lean.statement was checked against the file verbatim; all lines are at most 100 columns,
all universes and variables are bound, and the only two sorry proofs belong to the two
named statement theorems. The deliver2.py --no-push dry run passed preflight and compilation on 2026-10-21.
The final delivery uses the same prescribed wrapper.

## Second reading by Q38

The single worker re-read the node, its twelve proof steps and this module clause by
clause. The earlier retained helpers alone omitted every theorem, and the old report
correctly said they were not deliverable. This attempt added both statement theorems,
all representative normalization equations, both all-adjunct equations, four explicit
unit/counit equations and the two square-mate equations. The first compiler diagnostics
also exposed missing public imports for Grothendieck resolutions and constant-functor
additivity, the dependency's same-universe index restriction, two expression field
notations for IsKInjective, and the need for explicit naturality in towerSquare. These
were repaired by the existing public APIs, the AsSmall transport, qualified predicates
and θ.hom.naturality respectively. During this reading the
constant square's leading factor was corrected: it is the inverse interchange for g,
then termwise g applied to the constant comparison, then the tower mate. The transpose
formula for evaluation uses the inverse left interchange, while its final counit
formula uses the forward one. All proof docstrings now include the node's complete
proof plan. No independent worker was started, as the dispatch brief explicitly forbids
it; the maintainer performs the independent delivery review.

Retained-packet self-check, 2026-10-21: re-read the current node's four clauses, the
complete saved module, the current dependency interfaces and Stacks 0DVC/0FND/08BJ/
070I/07A7. Clause (1) is exactly TowerProperties at both corners, including level one
and every evaluation. Clause (2) uses constructed exact interchanges and specified
mates; its constant K-injective equation now includes the necessary canonical cochain
comparison, while evaluation's cochain composites are definitionally identical.
Clause (3) quantifies over every derived morphism, then states all four unit/counit
identities. Clause (4) uses the same given θ and its explicitly termwise towerSquare
in both actual mate equations. Checked all sources and targets of these formulas;
no mate invertibility or evaluation faithfulness is added. Compared the node copy
against current repository JSON: only lean and the authorized stmt_deps additions
differ (after the H2 repair, two landed nodes and the new definition node below). Current project-source searches find no other declaration of
this theorem or its namespace. No further mathematical mismatch was found.


## New nodes

def-sbc-tower-derived-evaluation-interchange owns the existing declarations
CategoryTheory.towerDerivedEvaluationInterchange,
CategoryTheory.towerNormalization_preservesFiniteLimits and
CategoryTheory.towerNormalization_preservesFiniteColimits in the unchanged module
Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization. Its lean.existing is true;
no new Lean module or duplicate definition is supplied. Its statement gives the
pointwise preservation structures under precisely their finite-(co)limit hypotheses
and the exact additive abelian specialization with four independent derived-category
universes. The displayed interchange is exactly the inverse composition comparison
followed by the forward one across the strict evaluation identity. Its signature is
extracted verbatim from the existing definition. The sources are the diagram-topos
proof of Stacks 0A07 and the exact-localization construction used in clause (2).
The new node cites the existing inverse-system, finite-exactness, abelian-category
and derived-category definition nodes.

The required searches were run through msearch.py: LeanSearch for exact tower
functors commuting with derived evaluation returned eight generic results, including
ordinary whiskeringRightCompEvaluation and exact derived single-functor tools.
Loogle for CategoryTheory.Functor.mapDerivedCategoryCompIso returned seven generic
composition-comparison results. Mathlib grep for towerDerivedEvaluationInterchange,
towerNormalization_preservesFinite and mapDerivedCategoryCompIso in CategoryTheory
returned zero hits. Local source/DAG searches found the exact reusable declaration
and its helpers in TowerDerivedEvaluationNormalization, recorded only under the
normalization theorem node; no definition node owns them. blueprint_refs.py search
for evaluation interchange returned zero matching blueprint nodes. These results
are recorded in the new node; existing declarations are reused, never redefined.

## Return repair: H2

The independent return on immutable head ecb7b1291dae identified one defect:
lem-weil-pbc-tower-derived-evaluation-normalization was a statement dependency
although only its module's plain def and preservation instances occur in the item.
Added def-sbc-tower-derived-evaluation-interchange with existing:true ownership of
those three declarations and replaced that theorem in the item's stmt_deps. The
normalization theorem's conclusion is not used and nothing is chosen from it.
Retained lem-weil-pbc-small-module-diagrams-grothendieck: towerResolutions actually
uses its conclusion to construct a Grothendieck instance and hence the Prop instance
HasKInjectiveResolutions. No theorem statement, helper, proof or import was changed.

Second reading of this repair by Q38: opened all three existing declarations and
their docstrings, their composition-comparison implementation, the new node and the
item's constant/evaluation comparison definitions. The new node states the exact
explicit composite and general finite-(co)limit assumptions of those declarations;
it makes no assertion of derived right-adjoint normalization. It allows arbitrary
object/hom universes at both corners and all four derived morphism universes.
The index op 0 remains level one; identity functors, zero abelian categories and
all other tower levels are included. The item still states all four reviewed
clauses unchanged. The initial saved-packet dry run passed (commit a3496b81e06),
then this actual metadata repair was applied as required by the independent return.
