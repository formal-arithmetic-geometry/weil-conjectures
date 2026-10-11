## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteEtaleTrace` defines
`AlgebraicGeometry.Etale.finiteEtaleRestriction` and
`AlgebraicGeometry.Etale.finiteEtaleTrace`. No theorem is added or proved, and neither
definition contains `sorry`. The trace selects data from the existing named existence theorem.
The item node changes only in `lean`; no new or dependency modules are needed.

Hypothesis and clause correspondence:

- Schemes and their morphism: `{X Y : Scheme.{u}} (f : Y ⟶ X)` introduces exactly
  `f : Y → X`. Finiteness and étaleness are `[IsFinite f] [Etale f]`, the meanings
  collected by def-weil-pbc-scheme-conventions.
- The abelian sheaf on the small étale site is
  `(F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})`. This is precisely the
  abelian-sheaf category in the mixed lean record of def-weil-pbc-etale-sheaves.
  Its set-valued predicates in EtaleSheaves.lean are not used by this item and
  consequently that module is not redundantly imported.
- Inverse and direct image are the recorded `upperStar` and `lowerStar` at
  `AddCommGrpCat.{u + 1}`. Their composition in both result types is literally
  `(lowerStar ... f).obj ((upperStar ... f).obj F)`.
- Clause 1: `finiteEtaleRestriction` is exactly
  `(upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app F`, with type
  `F ⟶ f_* f⁻¹ F`. Its finite and étale binders restrict its domain to the
  morphisms in the node even though the construction itself works more generally.
- Clause 2: `finiteEtaleTrace` has type `f_* f⁻¹ F ⟶ F` and its body is
  `Classical.choose existsUnique_finiteEtaleTrace.exists X Y f inferInstance inferInstance F`.
  This selects one entire family, then evaluates it at `(X, Y, f, F)`; it does not
  choose unrelated pointwise morphisms. The chosen family's defining predicate
  is the dependency theorem's conjunction of (0) naturality, (1) étale localization,
  and (2) the split sum formula. Thus all three clauses are inherited from the
  very family the node tells us to use, without adding new theorem statements.
- The final coefficient paragraph specifies using the underlying abelian sheaf,
  so these same definitions apply without another trace notion. For `n ≥ 1`,
  additivity of upperStar and lowerStar preserves `n • 𝟙 F = 0`. At every site
  object their morphisms are additive homomorphisms. Mathlib's `ZMod.map_smul`
  and `AddMonoidHom.toZModLinearMap` (Mathlib.Algebra.Module.ZMod) express exactly
  that every such map with ZMod-module source and target is linear. The paragraph
  is a construction convention, not a separately postponed theorem in this
  definition node; it is explained in the module docstring. No restriction to
  prime coefficients or exclusion of `n = 1` is introduced.

Dependencies read and used:

- Mathlib.AlgebraicGeometry.Sites.Etale: `Scheme.smallEtaleTopology` and `Scheme.Etale`.
- The convention node has no declaration of its own; its `IsFinite` and `Etale`
  declarations in Mathlib.AlgebraicGeometry.Morphisms.Finite and .Etale are used.
- def-weil-pbc-etale-sheaves: its recorded existing `CategoryTheory.Sheaf` and
  `AddCommGrpCat` encoding, rather than its unrelated predicates.
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs:
  `AlgebraicGeometry.Etale.upperStar`, `.lowerStar`, `.upperStarLowerStarAdjunction`.
  Their full signatures and docstrings were read in the read-only source checkout.
- Sheaf.AlgebraicGeometry.FiniteEtaleTraceExists:
  `AlgebraicGeometry.Etale.existsUnique_finiteEtaleTrace`; its complete theorem and
  docstring were read. The single direct import supplies all used dependencies.

Source checked: the local Stacks TeX is not present on this machine. Opened the official
https://stacks.math.columbia.edu/tag/03SH instead, especially Definition 03SE and the
following characterization. It explicitly permits defining trace from the localization
and split-sum characterization without constructing lower shriek.

Edge cases checked before writing: the dependency's split formula permits an empty finite
index set, giving trace zero for the empty covering (degree zero). No surjectivity,
positive degree, connectedness, nonempty scheme, or nonzero sheaf is assumed. Identity
coverings give the one-summand trace, and zero sheaves admit the same constructions.
`n = 1` gives zero coefficient modules and is included. Universe `u` is explicitly bound;
sheaf coefficients have universe `u + 1` as in the dependency theorem, with no independently
smaller coefficient universe. The family ranges over all schemes in the same arbitrary
universe, so its choice is coherent within that universe.

Searches for existing declarations:

- msearch.py leanfinder: "restriction and trace of finite etale morphism on abelian
  sheaves, trace chosen from unique natural family": eight hits concerning algebraic
  étaleness, scheme restriction and the forgetful functor, no sheaf trace.
- msearch.py loogle: `"trace", CategoryTheory.Sheaf`: zero hits.
- msearch.py grep: `finiteEtaleTrace|etaleTrace|traceMap|restrictionMap` under
  Mathlib/AlgebraicGeometry: zero hits.
- msearch.py leansearch: "trace of finite etale morphism on sheaves of abelian groups":
  unavailable (Internal Server Error); no mathematical verdict inferred from this failure.
- rg over WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json for
  `finiteEtaleTrace|etaleTrace|traceMap|def-weil-pbc-finite-etale-trace`: the project's
  existence theorem and unrelated Poincaré-duality/Tate-orientation trace maps only.
  The latter are cohomological orientation traces, not morphisms `f_*f⁻¹F → F`.
- Mathlib/Algebra/Module/ZMod.lean was read for the existing coefficient linearity API.

No statement fault or STATEMENT-DISPUTED finding. Server compile via scompile.py passed
with exit code 0 in 1.9 seconds and no warnings.

## Second reading by C1

I read the item node, its sandbox module, all six statement-dependency nodes and
all the declarations used, independently of the worker report. There is no
`statement_change`, no new definition node, and no dependency module in this
delivery. The node's mathematical statement requires no correction.

Source: the local Stacks TeX is absent. I read the official Section 03SH at
https://stacks.math.columbia.edu/tag/03SH and fetched and read the original TeX
https://raw.githubusercontent.com/stacks/stacks-project/master/etale-cohomology.tex
from `section-trace-method` through `definition-trace-map` and its characterization.
The definition assumes finite etale morphisms of arbitrary schemes, without a
field, Noetherian, connectedness, surjectivity, or positive-degree hypothesis.
The later hypotheses on locally constant sheaves and primes belong to later
lemmas, not this definition. The characterization permits degree zero and
explicitly permits constructing the trace without the lower-shriek comparison.

Object, hypothesis and clause list, with Lean correspondence and verdict:

1. Schemes X and Y and a morphism f:Y -> X: `{X Y : Scheme.{u}} (f : Y ⟶ X)`
   in both definitions. PASS: no base scheme or field is imposed.
2. f finite and etale: `[IsFinite f] [Etale f]`. PASS: I opened the Mathlib
   classes in Morphisms/Finite.lean and Morphisms/Etale.lean; the first uses
   affine inverse images and finite ring maps, the second etale maps on affine
   opens. These are the meanings collected by def-weil-pbc-scheme-conventions,
   a convention node with no separate declaration.
3. The small etale site X_et and an abelian sheaf F:
   `F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}`. PASS: I opened
   Sites/Etale.lean, including smallEtaleTopology and the jointly-surjective
   covering criterion, and the EtaleSheaves.lean module of the mixed dependency
   record. That record explicitly uses this existing category for abelian
   sheaves; the module's new set-valued predicates are irrelevant here.
4. The inverse and direct image functors and their adjunction:
   `upperStar AddCommGrpCat.{u + 1} f`, `lowerStar AddCommGrpCat.{u + 1} f`, and
   `upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f`. PASS: I read their
   signatures, bodies and coefficient-category binders in the upstream
   UpperLowerStar/Defs.lean. Direct image is precomposition with base change;
   inverse image is left Kan extension followed by sheafification. Their
   Grothendieck abelian category requirements are instances for AddCommGrpCat,
   not extra hypotheses on f or F. They are exactly the recorded declarations.
5. Clause 1, restriction F -> f_*f^{-1}F equals the unit component:
   `finiteEtaleRestriction` has that arrow type and its entire body is
   `(upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app F`.
   PASS: no different restriction or module pullback is substituted.
6. Clause 2, trace f_*f^{-1}F -> F is a component of the unique entire family:
   `finiteEtaleTrace` has that arrow type and body
   `Classical.choose existsUnique_finiteEtaleTrace.exists X Y f inferInstance inferInstance F`.
   PASS: choose is applied to existence of a family before the arguments are
   applied, not separately to an existential for each f,F. I read the full
   FiniteEtaleTraceExists.lean statement against its node. Its T quantifies
   over all X,Y,f, finiteness, etaleness and F in that order.
7. Clause 2(0), naturality in F: the first conjunction of the selected family's
   predicate is `tr ... F ≫ φ = lowerStar.map (upperStar.map φ) ≫ tr ... G`.
   PASS: Lean's composition order renders precisely the node's equation.
8. Clause 2(1), compatibility with etale localization: the second conjunction
   uses etale g, f' = pullback.snd f g, F' = upperStar.obj F, the localization
   restriction isomorphism rho, and a kappa characterized by both projections.
   PASS: its component equation has rho_g after the localized bar trace on
   the left and rho_g, F.map kappa.inv.op, original bar trace on the right.
   This is exactly the dependency node's componentwise formula; the two
   projection conditions identify the canonical pasting isomorphism.
9. Clause 2(2), sum for the disjoint union of d copies of X: the third
   conjunction quantifies over finite J, a coproduct cocone, clopen pieces
   and inverses t of their maps to X. Its sum is F.obj.map of the sections
   `pullback.lift (𝟙 W.left) (W.hom ≫ t j ≫ i j)`, after converting via rho.
   PASS: it is the dependency node's split-sum formula, including ordinary
   copies of X and d=0, with no prechosen degree or enumeration imposed here.
10. Final coefficient paragraph, n>=1 and a Z/n-module sheaf: the node specifies
    using its underlying abelian sheaf, so both definitions above apply as-is.
    PASS: no extra trace or module structure is introduced. The module explains
    annihilation preservation by additive inverse/direct image and linearity
    of each additive component. I opened Mathlib.Algebra.Module.ZMod:
    AddCommGroup.zmodModule supplies the canonical structure from annihilation,
    ZMod.map_smul and AddMonoidHom.toZModLinearMap give component linearity.
    This is the node's construction convention, not an omitted extra definition.

Edge cases: both signatures admit empty schemes and the zero sheaf; no
nonemptiness or surjectivity binder occurs. The selected family's split sum
allows an empty Fintype J, so an empty finite cover has zero trace. Identity
covers give one summand. Coefficients n=1 give zero groups and remain included;
n=0 is outside the node's coefficient paragraph, while the underlying abelian
sheaf maps themselves remain defined. No characteristic restriction occurs.
Universe u is explicitly declared, all schemes use Scheme.{u}, and coefficients
use the dependency's AddCommGrpCat.{u+1}. Arbitrary u covers larger schemes
and coefficients by choosing a sufficiently large common universe; no test
object is quantified in an independent smaller universe. No unbound variable
or auto-implicit universe remains.

Independent searches, with different conceptual vocabulary from the worker:

- msearch leanfinder: `transfer morphism for abelian sheaves on a finite covering,
  additive sum over sheets`: eight Mayer-Vietoris square/short-complex/gluing
  results, no finite-cover transfer or trace definition.
- msearch loogle: `"trace", CategoryTheory.Sheaf`: zero results.
- msearch leansearch: `transfer for a finite covering on sheaves of abelian groups
  given by summing restrictions`: service unavailable, Internal Server Error;
  no no-match verdict inferred.
- Independent rg for trace, transfer, normmap in upstream six functors, Mathlib
  sites and project algebraic geometry; further rg for definition names using
  trace/transfer/norm and restriction, counit, lowerShriek. Existing hits are
  the dependency existence statement and unrelated smooth/Poincare/exceptional
  or linear-algebra traces. I opened the upstream lower-shriek/open-immersion
  API: it does not define this finite-etale trace. There is no duplicate notion
  to record as existing and no missing notion needing a new node.

Mismatch and repair: no mathematical mismatch was found. The declaration
comments did not spell out the choice-independence argument and did not carry
all four construction steps together. I expanded only the docstrings: step 1
for the adjunction unit, steps 2-3 for Stacks' characterization and uniqueness
of the chosen family, and step 4 for coefficient linearity. Bodies, signatures,
imports, node statement and dependencies are unchanged. Every declaration has
its source and blueprint tag; the sole import is used; no theorem is added,
no proof is supplied, and no definition contains sorry. The named dependency
existence theorem postpones only a proof, not the data of these definitions.
The node's lean.statement remains verbatim the main definition's signature
from `def` through its result type, excluding `:=`.

Validation: scompile.py compiled the final module cleanly on the server; delivery
preflight and dry run are run after this reading, before delivery.
