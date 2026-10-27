## Worker report

This is the stage-2 statement of lem-sf-cartesian-stratum-module-restriction.
The accepted Q116 stage-1 split is retained. The 2026-10-22 handoff in
coord/brief-stage2.md §0 specifically permits this stage-2 assignment despite
its inherited stage-1 live-wins refusal: the live node has no Lean record.
This packet repairs the maintainer return on immutable head 0e4ac3a170dc.
No live source was edited.

The delivered module is Sheaf.Paper.CartesianStratumModuleRestriction. Its only
postponed result is AlgebraicGeometry.Scheme.proEtale_cartesianStratum_moduleRestriction.
Its proof is sorry. Four helper definitions have actual data: the specialized
forgetful functor, the abelian transpose of the underlying normalized module
unit, its two-step composite, and the canonical underlying cartesian comparison.
These are helpers of this node's specified canonical map, not new independent notions.

The statement is rendered hypothesis by hypothesis and clause by clause:

| Node text | Lean rendering |
| --- | --- |
| Schemes S,Y,X; g:Y→X | `{S Y X : Scheme.{u}}`, `(g : Y ⟶ X)` |
| Immersion s:S→X | `(s : S ⟶ X) [IsImmersion s]` |
| A finite commutative ring | `(A : Type u) [CommRing A] [Finite A]` |
| Actual S'=S×_X Y, s':S'→Y, g':S'→S | `pullback s g`, `pullback.snd s g`, `pullback.fst s g` |
| Small pro-etale sites; A_T constant coefficient rings | `ProEt.topology T`, `proEtaleConstantRing T A` |
| Every A_X-module sheaf M | `M : proEtaleRingModules X (proEtaleConstantRing X A)` |
| Actual tensor module inverse images with the specified scalar maps | Each vertex is literally `proEtaleConstantModulePullback`, whose definition is `SheafOfModules.changeOfRings (proEtaleCoefficientInverseImageMap ...) ((proEtaleModuleInverseImage ...).obj M)` |
| Isomorphism theta_M from (s')* g* M to (g')* s* M | The existential family `theta`, with the displayed isomorphism in the category of actual A_{S'}-module sheaves |
| Naturality in M | First conjunct, for every `a : M ⟶ N`, using the two iterated `proEtaleConstantModulePullbackMap` maps |
| Underlying inverse-image composition comparison | Second conjunct: both `proEtaleIteratedConstantModuleUnderlyingComparison` maps are invertible, and the square with the forgotten `theta` commutes with `proEtaleCartesianStratumSheafComparison AddCommGrpCat ...` |
| Canonical, rather than arbitrary, underlying identifications | `proEtaleConstantModuleUnderlyingComparison` transposes the forgotten unit of `proEtaleConstantRingAdjunction A f` through the abelian `proEtaleSheafAdjunction`; that module adjunction is the uniquely tensor-unit-normalized adjunction, already published by the dependency |
| Comparison associated to g∘s'=s∘g' | `proEtaleCartesianStratumSheafComparison` is first the inverse of the published composition mate for `(s',g)`, then `eqToIso` of the actual `pullback.condition.symm`, then the published composition mate for `(g',s)` |
| Both coefficient paths agree with the canonical map of the common composite | Third and fourth conjuncts are explicit equalities to `proEtaleCoefficientInverseImageMap (pullback.snd s g ≫ g) A`; the latter uses the identical square comparison in commutative-ring sheaves |
| Each constant section a is sent to the same section | The right sides are the literal canonical coefficient maps defined as the adjuncts of the sheafification extensions of the constant-section maps, not selected isomorphisms. Equality to these maps includes their constant-section normalization |
| Intertwines module action maps | Each `theta M` is an isomorphism in `SheafOfModules`. Its hom and inverse are sectionwise linear over the same actual A_{S'} section rings. Thus this is linear for arbitrary local coefficient sections, not just for constant scalars |
| s* M locally constant | Antecedent of the last conjunct uses exactly `IsLocallyConstantProEtaleModuleSheafOfUniverses S A (proEtaleConstantModulePullback s A M)` |
| Finite stalks at every geometric point of S | Antecedent quantifies `Ω : Type u`, `[Field Ω] [IsAlgClosed Ω]`, `y : Spec (.of Ω) ⟶ S`, and `Finite ((geometricRingModuleStalkFunctor y ...).obj ...)` |
| The two same properties for (s')*g* M on S' | Consequent of the last conjunct repeats these precise predicates and geometric-point quantifiers at `pullback s g` and the left-hand actual pullback vertex |
| No reduction, Noetherianity or invertibility hypotheses | The signature contains none of these; the schemes remain the chosen fibre products of the original schemes |
| Empty S' and zero ring | There is no nonempty-scheme or nontrivial-ring binder, and geometric-point claims are universally quantified |

Universes: the original small pro-etale category has objects in u+1 and Homs in u;
modules and coefficient sheaves use u+1. The value category D of the helper has
its explicitly bound object universe v and morphism universe u+1. The local
constancy definition is the recorded OfUniverses version, specialized to the
same coefficient universe used by the actual inverse-image interface. No site
object/Hom universe equality is imposed. The geometric field bound is exactly
the recorded geometric-stalk convention. All universes and variables are bound;
`set_option autoImplicit false` is in force.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme` and scheme morphisms.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion and .Immersion:
  `IsClosedImmersion`, `IsImmersion`; the dependency's mathlib_match explicitly
  includes `IsImmersion` for its immersion clause.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback:
  `pullback`, `pullback.fst`, `pullback.snd`, `pullback.condition`;
  scheme pullbacks are the existing Mathlib pullbacks.
- Mathlib.AlgebraicGeometry.Sites.Proetale: `Scheme.ProEt`, `ProEt.topology`.
- Mathlib.CategoryTheory.Sites.ConstantSheaf: `CategoryTheory.constantSheaf`.
- Sheaf.AlgebraicGeometry.ProEtaleInverseImage: `proEtaleSheafInverseImage`,
  `proEtaleSheafAdjunction`, `proEtaleConstantRing`,
  `proEtaleCoefficientInverseImageMap`, `proEtaleConstantModulePullback`,
  `proEtaleConstantModulePullbackMap` and their actual tensor definitions.
- Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses:
  `IsLocallyConstantProEtaleModuleSheafOfUniverses`; this is the exact recorded
  coverwise module-isomorphism predicate, with varying unrestricted models.
- Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor:
  `geometricRingModuleStalkFunctor`; its object is the recorded module colimit,
  so `Finite` concerns the underlying set of the module stalk.
- Sheaf.CategoryTheory.RingedSiteModules: `ringedSiteModules`, publicly imported
  by the inverse-image and operation interfaces and used in their module categories.
- Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations:
  `proEtaleRingModules`, `proEtaleConstantRingAdjunction`, and its actual
  `proEtaleConstantRingComparison`. This is the newly current recorded module
  of def-weil-pbc-proetale-operations, not a private adjunction choice.
- Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence:
  `ProEtale.supportSiteProEtaleComparisonComp`, the published canonical mate.

The last two owning nodes, def-weil-pbc-proetale-operations and
def-per-site-comparison-pullback-data, are added to stmt_deps as already landed
interfaces (brief-stage2 §5). No dependency record is changed. The originally
recorded statement dependencies retain their modules, objects and definitions.
Stated proof-dependency modules are imported without public: constant-ring map,
constant-ring composition, site inverse-image tensor, the recorded tensor-product
interface, and finite-local-constancy pullback. Statement-dependency imports
already cover ringed modules, fibre products, inverse image, local constancy,
and geometric stalks.

Edge cases checked before writing: s or g an identity; empty S or empty fibre
product; the zero module; the zero coefficient ring; a finite non-prime-field
coefficient ring, such as F_4; nonreduced schemes; arbitrary g. The square
comparison keeps the canonical equality transport even for identities. Empty
sources have only zero module sheaves and no geometric points. Unital modules
over the zero ring are zero. No passage to reduced schemes is performed. The
immersion assumption is retained even though the comparison works for arbitrary s.
No statement dispute or source correction was needed.

Searches for duplication:

- msearch.py leanfinder, query “Canonical constant coefficient proetale module
  pullbacks in a cartesian square preserve locally constant modules with finite
  geometric stalks”: 8 hits (condensed constant modules, scheme Zariski modules,
  etale pullbacks and presheaf pullback infrastructure); none states this result.
- msearch.py loogle, query `SheafOfModules.pullbackComp, AlgebraicGeometry.IsImmersion`:
  successful search, 0 hits.
- msearch.py grep, query `pullbackComp|locallyConstant.*pullback`, Mathlib/CategoryTheory:
  25 hits, principally generic Over/Subobject pullback composition; no match.
- msearch.py leansearch, query “Cartesian square of schemes canonical constant
  ring module inverse image commutes with restriction and preserves finite locally
  constant sheaves”: 8 hits, all Zariski-module or constant-section infrastructure.
- rg over lean/WeilConjectures and lean/Sheaf for cartesian stratum, stratum
  restriction, constant module pullback composition, and the published comparison
  names. The existing proEtaleConstantModulePullback_comp gives a Nonempty
  composition isomorphism but does not state the required underlying
  normalization, cartesian coefficient equations or finite-stalk preservation.
  proEtale_finiteLocalConstancy_pullback is the preservation input, not the square
  comparison. No exact existing statement was found.
- The prescribed rg for this item id in lean/WeilConjectures has no hits.
  All five introduced names were also searched in Mathlib, WeilConjectures and
  Sheaf; none was already declared.

Source checked directly: literature/stacks-project/sites-modules.tex,
lemma-pullback-locally-constant, lines 8435 onward, says inverse image of locally
constant fixed-ring module sheaves is locally constant. The coefficient and
composition refinements are exactly the accepted node's five-step argument and
its already-recorded Tags 03D2/03D8. The module docstring records all five steps.

Validation: the delivered file is compiled by scompile.py in module mode,
with sandbox and library checks under the prescribed 60-second per-file limit.
The first pass identified a missing import for a general coefficient comparison;
this was replaced by the current dependency's constant-ring adjunction. No
statement was weakened, no theorem was proved, and no new axiom was introduced.
Validation on 2026-10-22: the standalone scompile.py pass completed both
sandbox and library checks without errors or warnings. The resumed
`deliver2.py Q73 lem-sf-cartesian-stratum-module-restriction --no-push`
returned `OK (dry run)` at b6ba242f30b: preflight and compilation both passed.
The final delivery wrapper repeats these checks before pushing.

## Second reading by Q73

A second pass by this same dispatched worker reread the entire node, the real
helper bodies and the full theorem signature side by side. The dispatcher
explicitly forbids starting other agents; independent review is the maintainer's
subsequent review, not claimed here as an independent worker reading.

The pass checked both projection directions (snd is s', fst is g'), the source
and target of every theta, the direction of both composition mates, and the
transport from snd≫g to fst≫s. It checked that the underlying equality uses
canonical, real-data tensor-unit comparisons and requires their invertibility,
that both coefficient paths equal the literal c of the same common composite,
and that module isomorphisms supply linearity over arbitrary local sections.
It also checked naturality on every module morphism, preservation of both
properties in the final implication, all geometric-point binders and the
absence of nontriviality or nonempty assumptions. The current dependency module
for ordinary operations was reread and its public constant-ring adjunction used
in place of an indirect import of an equivalent coefficient-isomorphism theorem.
There are no additional nodes, dependency repairs or statement changes.

## Repair of maintainer return

The H2 return on immutable head 0e4ac3a170dc is repaired by replacing
`lem-weil-pbc-comparison-pullback` in the packet's additional statement
dependencies with `def-per-site-comparison-pullback-data`. The live definition
node has `existing: true`, owns the already imported module
`Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`, and explicitly
lists `AlgebraicGeometry.ProEtale.supportSiteProEtaleComparisonComp` and
`supportSiteProEtaleComparisonSquare` in its declarations. Reading the Comp
body confirms that it constructs the composition isomorphism as an adjoint
mate of the restriction composition isomorphism. The statement only uses this
plain definition; it never selects a witness from the comparison-pullback
theorem and needs none of its coherence conclusions. Thus the added dependency
is the owning definition, as the return requires. The Lean module and theorem
signature are unchanged. There is no change to the mathematical node statement,
proof, proof dependencies, or any dependency record.

The initial resumed dry run of the saved packet passed at cc61a3be11e. Its
mechanical success did not address this semantic H2 return, so the dependency
replacement above was then made before delivery. The five private proof imports
are retained under stages/2-statements.md §3.7: they are the stated proof
dependencies used by the documented future proof. The specialized square helper
is retained as reviewed; the return explicitly requires no Lean change.

The repair self-check reread the node and full module: all hypotheses and clauses
still match the table above, including both projection directions, canonical
tensor-unit comparisons, naturality, both coefficient equations, local constancy
and finite geometric module stalks. The signature matches the Lean record
verbatim, all Lean lines have at most 100 characters, and there is exactly one
postponed theorem. Empty fibre products, the zero ring and identity arrows
remain included. No further mathematical mismatch was found.

Repair validation on 2026-10-22: the prescribed standalone scompile.py pass
completed both sandbox (21.0 s) and library (17.2 s) checks without errors or
warnings. The node comparison against the current read clone confirms that
only `lean` and the authorized additional `stmt_deps` differ; all original
statement dependencies remain. The final dry run and delivery wrapper perform
the server preflight and compilation again on the repaired packet.
