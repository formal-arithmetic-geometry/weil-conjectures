## Worker report

The item module states the ringed-space module category property through `ringedSpaceModuleCategory`, characterizes epimorphisms by zero cokernel and by local lifting on open covers, and characterizes exactness of a two-arrow complex by local lifting of sections killed by the second map. Covers are encoded by `I : Type u`, opens `V : I → Opens X`, inclusions `hV`, and `⨆ i, V i = W`; restriction is `G.val.map (homOfLE (hV i)).op`.

The dependency declaration `AlgebraicGeometry.RingedSpace.ringedSpaceModuleCategory` in `Sheaf.Topology.RingedSpaceModuleCategory` states that `SheafOfModules (moduleRings X)` is abelian and that the range of the kernel inclusion on each open is exactly the sectionwise kernel.

Edge cases checked: the index type is allowed to be empty (so the cover equation forces the covered open to be empty), zero sections and zero morphisms are admitted, and arbitrary ringed spaces including the empty space are quantified. Universes use `Type u` for cover indices and `SheafOfModules.{u}`.

Searches: `msearch.py leanfinder` and `loogle` for sheaf-module epimorphisms and exactness found only concrete sheaf or presheaf results; grep of Mathlib `ModuleCat/Sheaf` and project `lean/Sheaf` found no statement matching this ringed-space local-lifting theorem. The existing `SheafOfModules` declaration was therefore not sufficient for the dependency specialization.

## Dependency modules

`def-weil-sheaf-of-modules-category`: its recorded Mathlib declaration is generic in a site and does not provide the ringed-space abelian and sectionwise-kernel statement required here. The dependency module supplies `ringedSpaceModuleCategory` with exactly that specialization.

## Earlier second reading (a previous round; superseded)

The item statement has three parts: the specialized abelian/kernel category fact, the two equivalent descriptions of epimorphism (zero cokernel and local lifts), and the exactness/local-lifting equivalence for a complex. Each hypothesis (`X`, module sheaves, morphisms, and `χ ≫ φ = 0`) and each local-cover clause is rendered explicitly in the Lean signature. The dependency module gives the category and sectionwise-kernel clause cited by the item.

## Second reading by G1

The node introduces a ringed space `(X, O_X)`, the category of sheaves of modules,
a module morphism `φ : G ⟶ H`, and a complex `F ⟶ G ⟶ H` with `χ ≫ φ = 0`.
The module renders `X : RingedSpace.{u}` and `SheafOfModules.{u} (moduleRings X)`;
its first conjunct is `RingedSpaceModuleCategory X`, whose dependency module gives the
abelian category and sectionwise kernel. For each `φ`, Lean states separately
`Epi φ ↔ IsZero (cokernel φ)` and the equivalence between `Epi φ` and local lifting
on an arbitrary index type `I : Type u`, opens `V i ≤ W`, and `⨆ i, V i = W`.
The final conjunct quantifies `χ`, `φ`, and `h : χ ≫ φ = 0`, and states
`ShortComplex.mk χ φ h).Exact` iff local lifts of every section `g` with
`φ_W g = 0`. Restrictions are rendered by `G.val.map (homOfLE (hV i)).op`.
All clauses and quantifier order match the node after correcting the conjunction
parentheses. Empty covers, empty and zero ringed spaces, zero morphisms, and zero
sections remain admitted; the cover index has the sheaf universe `Type u`.

Searches were repeated with `msearch.py` LeanFinder, Loogle, and Mathlib grep, and
with project/source grep. They found only generic `SheafOfModules` abelian instances,
presheaf local-surjectivity infrastructure, and unrelated exactness lemmas; no theorem
matching this ringed-space local-lifting statement exists.

The dependency module specializes the generic Mathlib module-sheaf category to the
ringed-space abelian and sectionwise-kernel property required by the node. The only
mismatch found was the original Lean grouping of the two epimorphism clauses; I
separated the equivalences and recorded the correction and citer checks in
`statement_change`.

## Statement corrected

The original signature parsed `(Epi φ ↔ IsZero (cokernel φ)) ∧ (local lifting) ↔ Epi φ`,
which is not the node's two separate descriptions. Parentheses now make the local
lifting condition itself equivalent to `Epi φ`; all citers continue to hold.

Citers: lem-sc-local-section-quotient-finite-free; lem-sc-p1-proj-sheafification-exact; lem-weil-pbc-coherent-finite-type-sub-kernel; lem-weil-pbc-coherent-modules-kernel-cokernel-sum; lem-weil-pbc-finite-presentation-kernel-surjection-finite-type; lem-weil-pbc-formal-systems-proper-support-serre; lem-weil-pbc-module-finite-presentation-cokernel; lem-weil-pbc-module-finite-presentation-extension; lem-weil-pbc-module-finite-type-image-extension; lem-weil-pbc-module-finite-type-surjective-on-stalk; lem-weil-pbc-module-pullback-finite-type; lem-weil-pbc-module-stalk-exact; lem-weil-pbc-sheaf-hom-finite-presentation-kernel.

## Dependency modules

`def-weil-sheaf-of-modules-category` uses `Sheaf.Topology.RingedSpaceModuleCategory`:
Mathlib's recorded declaration is generic and does not state the ringed-space
sectionwise-kernel specialization, so the delivery supplies that exact specialization.

## Reviewer R-ell (FIX, 2026-10-11)

Superseding the sections above where they differ. The dependency module
`Sheaf.Topology.RingedSpaceModuleCategory` is left out and
def-weil-sheaf-of-modules-category is kept as on sheaf-dag (`--revert-nodes`): it re-recorded a
definition node at a Prop-valued theorem bundle (abelian + sectionwise kernels), which is not the
notion the node defines (H13) and replaced the landed record (`SheafOfModules` / `Scheme.Modules`).
The module also did not compile (`moduleRings` not imported). The item's first conjunct now states
the sectionwise kernel inline over `SheafOfModules.{u} (moduleRings X)` (abelian is Mathlib's
`SheafOfModules.instAbelian`). The statement correction is reverted (`--revert-statement`): the
node text only gained the word "independently"; the actual fault was a Lean parenthesisation, which
needs no node change.
