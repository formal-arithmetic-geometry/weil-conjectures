## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceCoherentKernelCokernelExtension`
states `AlgebraicGeometry.AlgebraicSpace.coherent_kernel_cokernel_extension`, with
`sorry` as its entire proof. No definition or auxiliary theorem is introduced.
The item statement is unchanged.

Source checked: `literature/stacks-project/spaces-cohomology.tex`, the section
“Coherent modules on locally Noetherian algebraic spaces”, especially
`lemma-coherent-Noetherian` (07UB) and `lemma-coherent-abelian-Noetherian` (07UC).
07UB explicitly identifies coherent modules, quasi-coherent finite-type modules,
finitely presented site modules, and coherent pullbacks on every scheme chart.
Combining its affine specialization with the finite-module criterion and tilde
base-change formula gives exactly the finite affine-chart tensor formula in the
node. Thus the existing Mathlib `SheafOfModules.IsFinitePresentation` is used,
as in the landed `AlgebraicSpaceCoherentAbelian` and
`AlgebraicSpaceClosedCoherentModules` modules, rather than a private predicate.

Clause-by-clause correspondence:

- The scheme S is `{S : Scheme.{u}}`, and the space Z over S is
  `(Z : AlgebraicSpace S)`.
- Local Noetherianity of every etale scheme chart is precisely
  `hln : ∀ T : Z.EtaleSite, IsLocallyNoetherian (Z.etaleForget.obj T)`.
  Mathlib's scheme predicate tests Noetherian rings on all affine opens.
- The ambient category is `Z.Modules`, transparently the established
  `ringedSiteModules Z.structureSheaf`, hence the actual category of module
  sheaves on the small etale ringed site. Morphisms are its linear natural maps.
- Coherence of each object is its existing `IsFinitePresentation` predicate,
  with the equivalence to the node's affine formula explained above. Over each
  Noetherian R, a finite R-module is finitely presented, and conversely; the
  affine associated sheaf has value B tensor_R N and its natural restrictions.
  The formula is not replaced by arbitrary, unrelated sectionwise isomorphisms.
- The zero clause is `SheafOfModules.IsFinitePresentation (⊤_ Z.Modules)`.
  In this module-sheaf category the terminal object is the zero module, just
  as in the landed coherent-abelian theorem.
- Every morphism of coherent modules is quantified by
  `∀ (F G : Z.Modules) (f : F ⟶ G), F.IsFinitePresentation →
  G.IsFinitePresentation → ...`.
- Kernel coherence is `∀ k : KernelFork f, IsLimit k → k.pt.IsFinitePresentation`.
  This states coherence of every object satisfying the ambient kernel universal
  property, and so of its chosen kernel; it introduces no extra hypothesis on f.
- Cokernel coherence is the corresponding
  `∀ c : CokernelCofork f, IsColimit c → c.pt.IsFinitePresentation`.
  Both universal properties are in all module sheaves, not in QCoh or Coh.
- A short exact sequence with coherent endpoints is a
  `c : ShortComplex Z.Modules` with `c.ShortExact`, followed by
  `c.X₁.IsFinitePresentation → c.X₃.IsFinitePresentation →
  c.X₂.IsFinitePresentation`. The middle term has no prior quasi-coherence or
  finiteness assumption.
- Isomorphism invariance is `∀ (F G : Z.Modules) (_e : F ≅ G),
  F.IsFinitePresentation ↔ G.IsFinitePresentation`. The equivalence records both
  directions, including application to the inverse isomorphism.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its `Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `EtaleSite`, `etaleForget`, `structureSheaf`, and `Modules`, including their
  definitions and source docstrings.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  which is the transparent Mathlib module-sheaf category.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`; this is the ring
  predicate within `IsLocallyNoetherian`, not an additional ring choice.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`; the finite-generation
  predicate in the affine interpretation of coherence, not a new definition.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule` supplies the
  already-landed specialization of the Mathlib site predicates, including
  `etaleModuleOverHasWeakSheafify` and
  `etaleModuleOverWEqualsLocallyBijective`. Its owning node
  `def-trf-space-quasi-coherent-module` is added to `stmt_deps`, using the
  authorization to add landed statement dependencies. This is needed for the
  exact existing finite-presentation interface; no new node is needed.

Plain proof imports retain the available proof plan: localized exact module
restriction (`SheafOfModules.localizedSystemExact`), the scheme Zariski/etale
quasi-coherent equivalence, tilde sections and adjunction, tilde pullback base
change, the affine finite-type criterion, locally Noetherian scheme coherence,
scheme coherent kernel/cokernel/extension closure, and quasi-coherent scheme
kernels and cokernels/images. The two proof dependencies
`lem-sfb-scheme-etale-module-exact-finiteness-comparison` and
`lem-sfb-space-qcoh-extension-closed` have no recorded module in the read clone
and are therefore not imported. Neither is needed to type this statement.
No downstream coherent-abelian module is imported: its proof uses this item.

Edge cases checked: the empty space and empty charts are permitted; no nonempty,
quasi-compact, separated or global Noetherian hypothesis is imposed. Zero is
covered explicitly and has the zero finite-module affine model. Zero maps,
isomorphisms and split short exact sequences have precisely the asserted
kernels, cokernels and middle terms. Non-affine etale charts are tested for local
Noetherianity; the coherence criterion is compatible with their affine covers.
The base scheme S need not be locally Noetherian. Universe u is explicit, and
all binders are explicit under `set_option autoImplicit false`. No independent
small test universe or additional categorical instance assumption is introduced.

Searches (2026-10-24):

- `msearch.py ... leanfinder "Coherent sheaves of modules on a locally
  Noetherian algebraic space are closed under kernels cokernels and extensions"`:
  eight hits including scheme module abelianness, general site abelianness,
  `SheafOfModules.IsFinitePresentation`, and `IsQuasicoherent`; no exact theorem.
- `msearch.py ... loogle "SheafOfModules.IsFinitePresentation, Module.Finite,
  IsLocallyNoetherian"`: no hits; unknown identifier `IsLocallyNoetherian` in
  that search service. The actual declaration was read directly in Mathlib.
- `msearch.py ... leansearch "Coherent modules on locally Noetherian algebraic
  spaces are closed under kernels cokernels extensions"`: eight hits, concerning
  scheme module abelianness, finite module categories and module finiteness;
  none states this algebraic-space theorem.
- `msearch.py ... grep "coherent|IsCoherent" Algebra/Category/ModuleCat/Sheaf`:
  quasi-coherent/locally free presentation machinery, no exact closure theorem.
- Direct `rg` of `lean/WeilConjectures/AlgebraicGeometry` for `IsCoherent` and
  coherent kernel/cokernel names: scheme/ringed-space theorems only.
  `grep -rn` for this exact node id in `lean/WeilConjectures` found nothing.
- Direct `rg` of `lean/Sheaf` for coherent kernel/cokernel names located
  `AlgebraicSpaceCoherentAbelian`. Its signature and docstring were read in
  full. It also asserts finite sums and does not explicitly assert isomorphism
  invariance; its natural-language proof depends on this item. It is therefore
  not an exact existing match or a permissible proof import. Its finite-
  presentation encoding and universal-property formulation are reused.
- Read `dag/lean_names_upstream.json` search results for the chosen name and
  algebraic-space names: no collision with the new declaration.

No statement correction, new definition node, dependency replacement, or
STATEMENT-DISPUTED issue is needed.

## Second reading by Q26

A second clause-by-clause self-reading was performed with the node and completed
module open; no second agent was started, as required by the dispatcher brief.
The base, space and hln quantifiers match the first two sentences of the node.
07UB(3) justifies the existing finite-presentation predicate for the exact affine
finite-module formula, so no condition on coherent objects is missing. The zero
conjunct, both universal-property conjuncts, the free middle term of each short
exact sequence, and the final iff match all four closure/invariance sentences.
Kernel and cokernel universal properties range over the ambient category. They
do not presuppose finite presentation of their candidate objects. No finite-sum
conclusion from the nearby coherent-abelian theorem was copied into this item.
The source docstring reproduces all four proof steps, including the separate
quasi-coherence argument for the extension middle term. No mismatch or change
was found on this reading.
