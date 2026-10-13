## What changed

Preserved the signature of
`AlgebraicGeometry.RingedSpace.exists_stalk_internalHom_linearEquiv_of_finitePresentation`.
Its proof now obtains the canonical linear evaluation map and finite-coordinate stalk kernel
data, proves their evaluation triangle commutes, proves injectivity and surjectivity, and applies
`LinearEquiv.ofBijective` with the original germ formula.

Added `Sheaf.AlgebraicGeometry.StalkInternalHomEvaluation`, containing a complete proof of
`AlgebraicGeometry.RingedSpace.exists_stalk_internalHom_linearMap` without finiteness hypotheses.
Its private, proved helpers establish evaluation compatibility with restriction, independence
of both germ representatives, common representatives, and linearity in both variables. Its
choices use proved Mathlib germ-existence theorems, with independence proved explicitly;
there is no definition containing postponed data or proofs.

Added `Sheaf.AlgebraicGeometry.FinitePresentationStalkKernel`, isolating the remaining
localization and finite-coordinate stalk-kernel construction as a public named theorem.
It contains no canonical comparison map and makes no assertion that that map is bijective.
The final comparison and the linear map construction are outside this remaining hole.
The original node now records this route. The unit sk-thm-p1 and its realized steps are unchanged.

All three modules compiled cleanly via lcompile.py. The new lemma was checked against
rank zero, zero relations, zero modules, the zero ring, and intersections of neighborhoods.
When n=0 the surjective presentation forces F_x=0 and the injective coordinate map forces
the internal-Hom stalk to vanish; when m=0 the relation kernel is the entire coordinate
module. The empty space has no point x. The formula uses U intersect W, so it also covers
representatives whose original neighborhood is not contained in U.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.RingedSpace.exists_stalk_internalHom_linearEquiv_of_finitePresentation`
(node `lem-weil-pbc-stalk-internal-hom-finite-presentation`). This is a decomposition,
not an axiom-free proof of the full finite-presentation theorem: one lower hole remains.

Completely proved the new theorem
`AlgebraicGeometry.RingedSpace.exists_stalk_internalHom_linearMap`
(node `lem-weil-pbc-stalk-internal-hom-evaluation`) and all of its private helpers.

Added exactly one hole:
`AlgebraicGeometry.RingedSpace.exists_finitePresentation_stalk_kernel`
(node `lem-weil-pbc-finite-presentation-stalk-kernel`). Its proof is wholly `by sorry`,
in its own module, with source and complete proof in words. It isolates original plan
steps 2–4, together with the source stalk presentation from step 5. The original module
and the evaluation module have no direct sorry. Holes closed: 1; holes added: 1; net: 0.

## No longer needed

Removed direct imports from the original module:

- `Sheaf.Topology.PresheafModuleStalkFunctor`: the proofs use Mathlib's existing germ API
  and the existing RingedSpace module stalk functor directly; this auxiliary presheaf
  stalk functor is unnecessary for this argument.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.HomFinitePresentationKernel` and
  `Sheaf.Algebra.Homology.ModuleStalkExact`: retained as dependencies of the new kernel
  item, where their conclusions are required. They are not globally pruned.

The old direct `proof_deps` omitted from the new top-level node are
`def-pur-sheaf-hom`, `def-pur-localized-ringed-site`, `def-weil-pbc-module-stalk`,
`def-weil-pbc-module-finite-type-presentation`, `lem-weil-pbc-module-stalk-exact`,
and `lem-weil-pbc-sheaf-hom-finite-presentation-kernel`. Each remains a dependency
of the evaluation or kernel node; none is globally pruned. The old
`lem-weil-pbc-module-hom-left-exact` remains a direct dependency, through free
coordinate evaluation and injectivity of precomposition.

No original mathematical dependency node has become globally unnecessary. The local
presentation, stalk exactness and internal-Hom kernel route is preserved in the lower item.
The full Hom-left-exact middle-exactness theorem is unnecessary in the final comparison:
precomposition injectivity, free evaluation, and b composed with a equal to zero suffice.
The existing multi-clause node `lem-weil-pbc-module-hom-left-exact` is still used for its
other clauses. No claim is made that the removed module is unreachable from other targets.

## Where the brief, the DAG or earlier work was wrong

The Mathlib leaf `lem-weil-pbc-module-hom-left-exact` names `LinearMap.piRing`;
in this Mathlib the declaration is `LinearEquiv.piRing` (LinearAlgebra/Pi.lean:548).
The delivered code uses the actual declaration. No statement was changed or disputed.

The original plan correctly describes the mathematics, but its two proved dependency
modules do not directly furnish the localized presentation, cofinal restriction
identifications, or coordinate stalk isomorphisms. Those operations are now one explicit
lower item; its docstring explains precisely what still has to be formalized.

The cited local literature/stacks-project/modules.tex file is absent on this machine.
I read the source proofs on the official Stacks pages for Tags 01CP and 01CO:
https://stacks.math.columbia.edu/tag/01CP and https://stacks.math.columbia.edu/tag/01CO.
LeanSearch returned HTTP Internal Server Error for both new-node searches; the records
say unavailable. LeanFinder and grep searches ran, and found no exact match. The whole
blueprint searches for 'stalk internal hom', '01CP', and 'finite presentation stalk kernel'
returned no matching blueprint nodes.

## New nodes

`lem-weil-pbc-stalk-internal-hom-evaluation`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-stalk-internal-hom-evaluation.json`, records
canonical bilinear germ evaluation, proved without a finiteness assumption, in
`Sheaf.AlgebraicGeometry.StalkInternalHomEvaluation`. The statement is strictly below
finite-presentation bijectivity: it only constructs the map and characterizes evaluation.

`lem-weil-pbc-finite-presentation-stalk-kernel`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-presentation-stalk-kernel.json`, records
a local finite presentation, an exact stalk presentation, and an injective internal-Hom
coordinate map with the prescribed relation kernel and germ formula, in
`Sheaf.AlgebraicGeometry.FinitePresentationStalkKernel`. This is the unproved part of the
source's local-presentation argument; it excludes canonical map construction and the
comparison proof. Both new nodes inherit the original chapter, unit and blueprint ancestor.
There are no statement changes, forced adaptations, or change records.

## Second reading by V3

1. Compared every delivered module with the repository. The two auxiliary modules
   are new; the original module changes only private proof imports, an elaboration
   option, and its proof. Independently extracted the original declaration signature
   and verified byte-for-byte equality. No public import, definition, hypothesis,
   conclusion, or visibility changed. Verdict: passes.
2. Compiled all three files together in dependency order through `lcompile.py`:
   no errors or warnings. Read every evaluation helper and the comparison proof.
   A scratch-copy `#print axioms` check gives only `propext`, `Classical.choice`,
   and `Quot.sound` for the evaluation theorem; the original theorem and kernel
   theorem additionally have `sorryAx`, accounted for by the single named kernel
   hole. No prohibited declaration, hollow definition, or unproved witness chosen
   as definition data occurs. The evaluation choice uses a fully proved theorem
   and its representative-independence proof. Verdict: passes as a decomposition.
3. Checked the kernel statement and its docstring against Stacks Tags 01CP and
   01CO, and against the existing finite-presentation kernel and stalk-exactness
   declarations. Tested the mathematical cases n=0, m=0, F=0, G=0, the zero ring,
   an empty space, and unrelated initial neighborhoods. Intersections supply the
   required comparison neighborhood; empty coordinate products cause no exception.
   The lower theorem constructs a presentation and sheaf-side coordinates; the
   target still needs the separately proved canonical map and an explicit
   injectivity/surjectivity argument. It is a proper part of the argument, not a
   renamed target. Independent LeanFinder search for “sheaf Hom finite generators
   relations stalk exact sequence” found local presentation APIs, which were read,
   but no stalk-kernel theorem. Loogle query `"stalk", "hom"` found ring-localization
   declarations, not sheaf-Hom comparison; launcher grep for
   `homObj.*stalk|stalk.*homObj|stalk.*finite.*product` found no match. Direct searches
   of Mathlib, the upstream source, and lean/ likewise found no replacement.
   Closing the remaining kernel hole requires the localization and finite-product
   stalk constructions, rather than a short lemma application. Verdict: passes.
4. Checked the proof from the original target downwards. It uses proved Mathlib
   germ and linear-map APIs, proves evaluation independently of finiteness, and
   leaves only the presentation-to-stalk-kernel step. The final comparison uses
   only b surjective and b composed with a zero; it needs no additional Hom exactness
   theorem. All public imports supply statement vocabulary; the two new comparison
   imports and the lower kernel's planned dependency imports are private. Checked
   all old proof dependencies and clarified their disposition above. Read
   dag/units/sk-thm-p1.json: its realized statement and steps remain unchanged,
   and this refinement bypasses none of them. Verdict: passes.
5. Checked the existing node changes: only `proof`, `proof_deps`, and `proof_origin`
   differ. Their steps describe the actual evaluation triangle and bijectivity
   proof. Both new nodes have matching Lean records, sources, natural-language
   proofs, dependency unions, searches, creation data, and the inherited chapter,
   unit and blueprint ancestry. Exactly one new named theorem remains sorry.
   Verdict: passes.

Second reading changed only this report: made the disposition of every removed
old direct proof dependency explicit and recorded the independent review and
validation. The Lean proofs and statements needed no repair. Original holes closed:
1 of 1; lower holes added: 1; net holes closed: 0. No global pruning is claimed.
