## Worker report

Module `Sheaf.AlgebraicGeometry.ConstantEtaleSheafShortExact` states
`AlgebraicGeometry.Scheme.constantEtaleSheaf_shortExact`. Its only proof is `sorry`;
there are no new definitions, dependency modules, or statement corrections.

Hypothesis and conclusion correspondence:

- A scheme X: `(X : Scheme.{u})`; no nonempty, connected, Noetherian, or separated assumption.
- A finite ring Λ: `(Λ : Type (u + 1)) [Ring Λ] [Finite Λ]`. `Ring` permits noncommutative rings; neither commutativity nor nontriviality is added.
- The modules K, L, N and their two specified linear maps: `(S : ShortComplex (ModuleCat.{u + 1} Λ))`, with `S.X₁ = K`, `S.X₂ = L`, `S.X₃ = N`, and maps `S.f`, `S.g`. `ModuleCat` uses left modules.
- Each module finite: `[Finite S.X₁] [Finite S.X₂] [Finite S.X₃]`. These refer to the underlying sets, not a chosen enumeration. Over a finite ring this is also equivalent to finite generation, so the source's finite-type convention gives the same hypothesis.
- Exactness of `0 → K → L → N → 0`: `(hS : S.ShortExact)`. This includes middle exactness, `Mono S.f`, and `Epi S.g`, hence the two zero endpoints. `S.zero` is already implied by exactness, not an additional mathematical restriction.
- The small etale site of X: `X.smallEtaleTopology`, on `X.Etale`; the recorded Mathlib definition is used verbatim.
- Associated constant sheaves and their induced maps: `S.map (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))`. By the actual definition of `constantSheaf`, each object and map is the sheafification of the corresponding constant presheaf. `ShortComplex.map` maps the original two maps, rather than asserting that some unrelated exact sequence exists.
- Conclusion `0 → K_X → L_X → N_X → 0` exact: the mapped complex's `.ShortExact`, again including both endpoints. No splitness, sectionwise surjectivity after sheafification, or local constancy hypothesis is imposed.

Coefficient categories: `Sheaf J (ModuleCat Λ)` is the standard fixed-coefficient
realization of sheaves of left Λ-modules in the source (`ConstructibleSheaf/Defs.lean`
and `ConstructibleSheaf/KernelCokernel.lean`). This is the same mathematical category
as `SheafOfModules ((constantSheaf J RingCat).obj (RingCat.of Λ))` in the dependency
record, not a change of coefficients. To pass from a ModuleCat-valued sheaf to a
module over the constant ring sheaf, represent a section of that ring sheaf locally
by elements of Λ, act locally, and glue; separatedness gives independence of the
representatives. Conversely, restrict the action to the canonical constant Λ scalars
on each object. These operations are inverse on objects and linear morphisms and
preserve kernels, cokernels, and exactness. In particular the fixed-coefficient
realization retains the constant-ring action; it is not a sheaf of modules over an
unrelated structure sheaf. No duplicate category or constant-sheaf definition is introduced.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`, `Mathlib.AlgebraicGeometry.Scheme`; read the locally affine locally ringed space data and morphism signature.
- `def-weil-pbc-etale-site`: `AlgebraicGeometry.Scheme.smallEtaleTopology`, `Mathlib.AlgebraicGeometry.Sites.Etale`, with `Scheme.Etale` in `Mathlib.AlgebraicGeometry.Morphisms.Etale` and `ofArrows_mem_smallEtaleTopology_iff` for the jointly-surjective-cover clause. Imported transitively through the existing source sheafification module.
- `def-weil-pbc-etale-sheaves`: read `Sheaf.AlgebraicGeometry.EtaleSheaves` and its record in full. Only its underlying fixed-coefficient sheaf category is relevant; the locally constant, constructible, and derived torsion predicates are not used or imported. Its record itself directs coefficient sheaves to Mathlib `Sheaf`, `constantSheaf`, and `SheafOfModules`.
- `def-weil-sheaf-of-modules-category`: read `SheafOfModules`, `Mathlib.Algebra.Category.ModuleCat.Sheaf`, including its object and morphism data. The equivalent fixed-coefficient realization above uses Mathlib `ModuleCat` and `CategoryTheory.Sheaf`; neither is redefined. The module imports no unused variable-ring sheaf API.
- `def-weil-pbc-constant-sheaf`: `CategoryTheory.constantSheaf`, `Mathlib.CategoryTheory.Sites.ConstantSheaf` (imported by `Mathlib.CategoryTheory.Sites.Abelian`), whose complete definition is `Functor.const Cᵒᵖ ⋙ presheafToSheaf J D`.
- Exact sequence language: `CategoryTheory.ShortComplex`, `.map`, and `.ShortExact`, Mathlib `Algebra.Homology.ShortComplex.Basic` and `ShortExact`. Read all data and the `ShortExact.map_of_exact` signature.

The imports supply ModuleCat's Grothendieck abelian structure, existing small-etale
sheafification, additive constant sheaves (needed to form `S.map`), and short exactness.
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify` supplies the existing
sheafification instance at coefficients in universe `u + 1`, matching the source
constructible-sheaf convention. All universes and variables are explicitly bound.

Source checked online because `literature/stacks-project/` is absent on this machine:
[03RX](https://stacks.math.columbia.edu/tag/03RX),
[093U](https://stacks.math.columbia.edu/tag/093U), and
[03EI](https://stacks.math.columbia.edu/tag/03EI). In the extension proof of 093U the
upper row of the pushout diagram is precisely the constant sheaf sequence obtained
from a module presentation. Tag 03EI supplies exactness of module sheafification.
The module docstring includes all three steps of the node's proof, with its DAG
references; no proof step or hypothesis is changed.

Edge cases checked mathematically before writing:

- Empty X: sheafification makes these sheaves zero, so the conclusion is still valid; no `Nonempty X` binder.
- All-zero sequence, or K = 0 or N = 0: `ShortExact` has the usual endpoint meaning and includes these cases.
- The zero ring is allowed. Its unital modules are zero; the same formulation still applies.
- Noncommutative finite rings are allowed: only `Ring`, not `CommRing`, is required, and actions are left actions.
- Nonsplit finite sequence `0 → 2ℤ/4ℤ → ℤ/4ℤ → ℤ/2ℤ → 0`: no splitness is demanded, and sectionwise exactness before sheafification suffices.
- A disconnected scheme has no connectedness requirement. Local scalar functions are handled by gluing, so the constant ring sheaf need not have sections literally equal to Λ on every object.
- Arbitrary characteristic and arbitrary universe `u` are included; the source convention uses coefficient universe `u + 1`.

Searches for an existing statement (actual service records in `searches.jsonl`):

- `msearch.py leansearch`: “An exact sequence of finite modules gives an exact sequence of constant sheaves on the small etale site”. Service unavailable, HTTP Internal Server Error; no positive or negative mathematical verdict assigned.
- `msearch.py leanfinder`: “constant sheaf functor preserves short exact sequences of modules”. Eight hits about condensed modules, module-sheaf abelian categories and forgetful functors; no theorem with this finite constant-etale statement.
- `msearch.py loogle`: `CategoryTheory.constantSheaf, CategoryTheory.ShortComplex.ShortExact`. Nine hits about cohomology long exact sequences and connecting maps, not the node's statement.
- `msearch.py grep`: `constant.*exact|exact.*constant|constantSheaf`, `CategoryTheory/Sites`. Twenty-one hits including the constant-sheaf definition and its additive instance; no matching finite-module theorem.
- `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`: `constant.*[Ee]xact|[Ee]xact.*constant|lem-constructible-constant-exact|constantSheaf.*ModuleCat|SheafOfModules.*constant|constant.*SheafOfModules`. Found generic exactness instances in `Mathlib/CategoryTheory/Sites/ConstantSheafOver.lean`, and specialized sequences in `CategoryTheory/DerivedCategory/Complete/Principal.lean`. Neither has the node's scheme/finite-ring/three-finite-module signature. Read the generic finite-limits and finite-colimits instances in full; these will support the stage-3 proof.
- `rg` with the same expression in repository `lean/Sheaf`: no matching theorem.
- `rg` for `constantSheaf.*shortExact|shortExact.*constantSheaf|constantSheaf_shortExact` in the source, project Lean, and `dag/lean_names_upstream.json`: only the special integer-coefficient surjectivity result on a separably closed field; no conflict with the chosen declaration name.

No statement dispute was found. Server compilation of the final file and delivery
preflight are recorded by the tooling; the independent second reader still needs to
read this statement and supply their own section before delivery.

## Second reading by E1

I independently opened the sandbox node and module, all five statement-dependency
nodes and their recorded declarations, and the source constructible-sheaf conventions.
Verdict: the Lean states precisely this node. No signature, module, dependency record,
or mathematical node field needed repair; this reading adds only this report section.
There are no new definition nodes or dependency modules to review and no statement
correction or citer verdicts to audit.

### Objects, hypotheses, and conclusion, item by item

1. An arbitrary scheme X: `X : Scheme.{u}`. PASS. Read Mathlib's `Scheme`
   (locally affine locally ringed space) and `Scheme.Hom`, recorded by `def-pc-scheme`.
   No connectedness, nonemptiness, separatedness, or Noetherian scheme hypothesis.
2. A finite ring Lambda: `Λ : Type (u + 1)`, `[Ring Λ]`, `[Finite Λ]`.
   PASS. No field, commutativity, characteristic, or nontriviality assumption added.
   Finite rings already satisfy the ascending-chain finiteness used in the source.
3. Three finite left Lambda-modules K, L, N: `S : ShortComplex (ModuleCat.{u + 1} Λ)`
   supplies `S.X₁`, `S.X₂`, `S.X₃`, and the three `[Finite S.Xᵢ]` binders give their
   finite underlying sets. PASS. I read `ModuleCat`'s carrier, additive-group and
   `Module Λ` fields, and its linear morphisms. For a finite coefficient ring,
   finite underlying set and finite generation agree, including the zero module.
4. The specified module maps and exact sequence with both zero endpoints:
   `S.f`, `S.g`, and `hS : S.ShortExact`. PASS. Read `ShortComplex`'s zero-composite
   field and `ShortExact`'s exact, mono_f, epi_g fields. The zero-composite field is
   implied by exactness and adds no mathematical hypothesis. Bundling the sequence
   does not reverse or change any quantifier: every given short exact sequence can
   be bundled this way. Neither map is chosen afresh in the conclusion.
5. The small etale site of X: `X.smallEtaleTopology`. PASS. Read its Mathlib
   definition on `X.Etale`, `Scheme.Etale`'s etale-over-X category, and
   `ofArrows_mem_smallEtaleTopology_iff`, which says covers are jointly surjective.
   These are exactly the declaration recorded by `def-weil-pbc-etale-site`.
6. The three associated constant sheaves and induced arrows:
   `S.map (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))`. PASS.
   Read `constantSheaf = Functor.const _ ⋙ presheafToSheaf _ _`, recorded by
   `def-weil-pbc-constant-sheaf`, and `ShortComplex.map`: its arrows are precisely
   the functor images of `S.f` and `S.g`.
7. Exactness as sheaves of left Lambda-modules, with both zero endpoints:
   the displayed mapped complex's `.ShortExact`. PASS. The target category is
   Mathlib's `Sheaf X.smallEtaleTopology (ModuleCat Λ)`, not just set-valued or
   abelian sheaves. It retains the linear arrows and coefficient action.
   I read the mixed `def-weil-pbc-etale-sheaves` record and its whole module,
   and `SheafOfModules` and its `Hom` in the module-category dependency.
   The latter is the general variable-ring-sheaf notion; the present constant-ring
   case is equivalently realized by ModuleCat-valued sheaves. Explicitly, sections
   of the constant ring sheaf are locally represented by Lambda scalars. Act on
   restrictions locally and glue: the sheaf condition makes the result unique and
   independent of scalar representatives. Conversely restrict that action along
   constant scalars. The constructions are inverse on objects and morphisms,
   commute with constant sheafification, and preserve short exact sequences.
   Thus using the existing fixed-coefficient category does not change the node's
   notion or require a duplicate definition or an unused import.

### Source and proof audit

The local Stacks checkout is absent. I fetched the actual `etale-cohomology.tex`
and `sites-modules.tex` from the official Stacks repository into the sandbox's
`scratchpad`, and read `lemma-kernel-finite-locally-constant` in both files,
including its complete proof. I also checked the official pages
[03RX](https://stacks.math.columbia.edu/tag/03RX),
[093U](https://stacks.math.columbia.edu/tag/093U), and
[03EI](https://stacks.math.columbia.edu/tag/03EI).
The first two concern finite-type locally constant modules over a Noetherian ring;
093U's extension diagram uses the constant sheaves of a module presentation.
The current node isolates the exactness of that constant sequence, with a finite
ring and three finite modules. No further condition on X or local splitting is
assumed. Tag 03EI allows any presheaf of rings and states exactness of module
sheafification, so the proof covers the node's left-module convention.

The theorem docstring follows the node's three steps in order: sheafify the
constant presheaves and arrows (constant-sheaf/site dependency nodes); evaluate
sectionwise to the original exact module sequence (presheaf module exactness
node, clause (1)); apply exact sheafification (same node, clause (2)). The module
and declaration both carry the correct source and blueprint id. Its sole theorem
has `by sorry`; it contains no new definition, hollow data, hidden proof, or axiom.
All four imports serve coefficient categories, sheafification/site instances,
additive constant sheaves, or short exactness. All variables and `u` are bound;
there are no overlong Lean lines.

### Edge cases

PASS for the empty scheme (empty covers force the sheaves to be zero), the zero
ring and zero modules, and either zero endpoint module. PASS for disconnected
schemes and the nonsplit finite sequence from Z/4 to Z/2: no connectedness,
splitness or sectionwise-surjectivity conclusion is imposed. Arbitrary
characteristic, including finite rings of nonprime characteristic, is covered.
There is no integer n or index-set parameter; the zero-generator presentation
and empty covers are included by the zero-module and empty-scheme checks.
The universe u is arbitrary. The u+1 coefficient convention matches the existing
small-site sheafification instance; all finite ring/module isomorphism classes
admit representatives there, so no finite mathematical case is lost. The
source's `hasSheafify_smallEtaleTopology` supplies sheafification rather than
adding an existence hypothesis to the theorem.

### Independent searches and validation

- LeanFinder: `sheafification of a constant diagram preserves exact module sequences`.
  Eight hits, including `SheafOfModules.instAbelian` and module sheafification's
  forgetful composite preserving finite limits. None states this node.
- Loogle: `CategoryTheory.ShortComplex.ShortExact.map_of_exact`. Twelve hits;
  I opened `ShortExact.map_of_exact` in Mathlib. It is the generic preservation
  theorem with an arbitrary functor and preservation instances, not this
  scheme/finite-ring/finite-module constant-sheaf statement.
- LeanSearch: `constant presheaf sheafification sends an exact module sequence to a
  short exact sheaf sequence`. Service returned Internal Server Error; unavailable,
  so this is not a negative mathematical search verdict.
- Direct rg in Mathlib's Sites and ModuleCat trees for exact/constant and
  ShortExact/constant in both orders: no specialized theorem. Opened
  ConstantSheaf, Sites.Abelian, ShortComplex.Basic, and ShortComplex.ShortExact.
- Direct rg in the source WeilConjectures tree, repository lean/Sheaf, and
  dag/lean_names_upstream.json for constant/shortExact and constant/exact in
  both orders: only generic constant-sheaf exactness instances and a special
  integer-coefficient sequence over a separably closed field. I read the two
  generic preservation instances in ConstantSheafOver in full; they do not
  have the node's signature. No name collision or duplicate notion was found.

`scompile.py E1 lem-constructible-constant-exact` compiled the delivered module
cleanly on the server in 1.8 seconds (exit code 0), with no warnings.
The node's `lean.statement` was compared verbatim with the theorem signature.
No mismatch was found; the existing statement and module are retained.
