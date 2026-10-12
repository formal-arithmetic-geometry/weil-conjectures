## What changed

Replaced the sole `sorry` in `AlgebraicGeometry.Scheme.constructible_torsion_modules_agree`
with a complete proof from two local comparison interfaces. The theorem's signature and all
existing definitions are unchanged. Added `FiniteLocalAbelianForget.lean` and
`FiniteLocalCyclicModuleForget.lean`, one public theorem per module, each with its source,
complete proof in words and matching DAG node.

The main proof uses the already proved ModuleCat-valued lift, proves full faithfulness by
integer scalar multiplication, constructs inverse-image/forgetting isomorphisms using
filtered Kan extensions and sheafification, proves both fixed-stratification comparisons,
and converts the same partition/domains/immersions in both constructibility definitions.
All private helpers are proved; neither new interface asserts constructibility, module-lift
existence, uniqueness, or the original curve theorem.

Added proof imports for the two interfaces, `KilledSheafModuleLift`, and
`WeilConjectures.ConstructibleSheaf.Pullback`. Kept the three original public imports and the unit-route import `TorsionEtaleSheaf`.
The unit's realized statement and steps are unaffected: this comparison is below that level.

## Proved and sorry left

`AlgebraicGeometry.Scheme.constructible_torsion_modules_agree` is proved from named
interfaces; it contains no `sorry`. The five private helpers are proved.

Exactly two new sorries remain in the delivery:
- `AlgebraicGeometry.Scheme.finite_local_abelian_forget_iff`, node
  `lem-weil-pbc-finite-local-abelian-forget`.
- `AlgebraicGeometry.Scheme.finite_local_cyclic_module_forget_iff`, node
  `lem-weil-pbc-finite-local-cyclic-module-forget`.

Checked the new statements mathematically on empty schemes, empty cover members, zero
sheaves, n=1 and disconnected schemes. Empty members are discarded before inferring a
finite/annihilated constant value from a stalk. For the first interface, finite operations
are trivialized after refining the set trivialization; no connectedness assumption is used.
For cyclic modules additive maps are automatically linear, including n=1. No positive
characteristic, noetherian or quasi-compact hypothesis is added to either local interface.

The main reduction compiles cleanly with the permitted local launcher; final delivery dry
run checks local and server compilation and the preflight. The theorem still depends on
the two named interfaces and existing upstream sorries: no claim of axiom-free closure.

## No longer needed

Removed eight original proof imports from the main module:
- `Sheaf.AlgebraicGeometry.ConstantSheafGeometricStalk`
- `Sheaf.AlgebraicGeometry.CurveCoefficientPair`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.AlgebraicGeometry.EtaleSheaves`
- `Sheaf.AlgebraicGeometry.LocallyClosedStratification`
- `Sheaf.Paper.SheavesKilledByNZmodModules`
- `WeilConjectures.ConstructibleSheaf.Defs`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`

The CurveCoefficientPair, EtaleSheaves, LocallyClosedStratification,
ConstructibleSheaf.Defs and UpperLowerStar.Defs notions remain visible through necessary
public imports; removing their redundant direct imports does not remove those notions.

The main node no longer directly needs:
`def-weil-pbc-curve-setting`,
`lem-weil-pbc-sheaves-killed-by-n-zmod-modules`, `def-weil-constructible-subset`,
`prop-weil-pbc-inverse-image-modules-exact`, `def-constructible-locally-constant`,
`def-weil-pbc-constant-sheaf`, `def-weil-geometric-point`,
`lem-weil-pbc-constant-sheaf-geometric-stalk`, `def-weil-pbc-geometric-stalks`,
`lem-weil-pbc-constant-module-sheaf-underlying`, `def-constructible-constant`,
`lem-weil-pbc-etale-cover-geometric-point-lift`.

Some of these definitions remain statement dependencies, and the constant/stalk/cyclic
module facts remain proof dependencies of the two local interfaces. They are not claimed
to disappear from the project's whole closure. The heavy
`prop-weil-pbc-inverse-image-modules-exact` interface is unnecessary on this route:
its needed ModuleCat comparison is proved directly in the main module.

## Where the brief, the DAG or earlier work was wrong

The planned `sheaves_killed_by_n_zmod_modules` interface supplies `SheafOfModules` over
the constant ring sheaf, while the item's theorem quantifies over `ModuleCat`-valued
sheaves. It cannot directly provide this theorem's lift. The existing proved
`exists_module_sheaf_of_nsmul_id_eq_zero` supplies the required lift exactly.
The inverse-image interface likewise concerns `SheafOfModules`; no equivalence between
these implementations is needed here.

The plan also did not expose a statement comparing finite set local systems to abelian
local systems, even though the curve definition uses the underlying set sheaf. This is
split off locally, with its finite-operation refinement argument written in the docstring.
`LocallyClosedStratification` currently inherits constructible parts from
`Topology.Stratification`, despite its introductory prose saying otherwise. Both
stratification structures therefore have the same fields; the explicit constructibility
conjunct on module constructibility is redundant but unchanged.

Searches ran through msearch (Lean Finder, Loogle and grep); LeanSearch returned HTTP 500
for both local comparisons and is recorded as unavailable. Loogle found constant-sheaf
interfaces and AddCommGroup.zmodModule; none gives the whole local comparisons. Searched
the existing DAG and both library roots and the imported blueprint before adding nodes.
Read Stacks [03RU](https://stacks.math.columbia.edu/tag/03RU) and
[03RW](https://stacks.math.columbia.edu/tag/03RW) for the three coefficient notions;
the local comparison proofs are agent-formulated from those definitions and the parent plan.

## New nodes

`lem-weil-pbc-finite-local-abelian-forget`: arbitrary-scheme comparison of finite local
constancy for an abelian sheaf and its underlying set sheaf. The missing argument is
local trivialization of the finitely many group-operation values.

`lem-weil-pbc-finite-local-cyclic-module-forget`: arbitrary-scheme comparison of finite
abelian local constancy for the underlying sheaf of a cyclic module sheaf and module
trivializations with finite values. This isolates the parent plan's constant/stalk
argument (steps 4--6). Neither new node restates the parent or a constructibility clause.
No definition/statement was changed and no change record is required.

## Second reading by K1

1. Compared the delivered main module with the repository version. The theorem signature
and all existing declarations are unchanged byte for byte; only proof code and proof-only
imports changed. The two added declarations are new split-off interfaces recorded by nodes.
Verdict: pass.
2. Compiled all three delivered modules with the local launcher. They compile without errors;
the only remaining `sorry`s are the two named split-off interface theorems. No definitions
contain `sorry`, and no forbidden declarations were added. Verdict: pass.
The scratch-copy `#print axioms` checks for the main theorem and both interfaces show
only `propext`, `Classical.choice`, `Quot.sound`, and the expected `sorryAx`.
3. Checked both split-off statements against the underlying set, abelian, and cyclic-module
definitions, including empty schemes and covers, zero modules, disconnected schemes, and
`n = 1`. They are true and strictly local comparisons, not restatements of the parent.
Their docstrings, nodes, sources, and proof dependencies agree. Verdict: pass.
Independent Loogle and Lean Finder searches used `constantCommuteCompose` and simultaneous
trivialization of finite group operations; neither supplies either full local comparison.
Repository searches also inspected `ConstructibleModuleUnderlyingSets`,
`ConstructibleIntegralCoefficientsBackward`, and `FiniteLocallyConstantModuleValues`:
these give different constructibility or finitely-generated-stalk comparisons, not the
two interfaces here.
4. The proof follows the shortest available route through the existing ModuleCat lift,
direct cyclic full faithfulness, filtered Kan-extension comparisons, and the two local
interfaces. Redundant proof imports and their direct node dependencies are listed above;
the unit route and realized fields are unchanged. Verdict: pass.
5. The DAG proof steps and `proof_deps` match the Lean proof, and both new nodes carry the
required metadata and `split` status. Verdict: pass.

Changed only the report after this reading; no Lean repair was necessary.
