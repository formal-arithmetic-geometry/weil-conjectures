## Worker report

The module `Sheaf.Algebra.Homology.SliceScalarHomChainAdjunction` states
`SheafOfModules.StrictScalarHom.exists_sliceScalarHomChainAdjunction`. Its only
postponed proof is `sorry`. Its three structures package this node's conclusions;
they do not construct another scalar extension, tensor, internal Hom or complex.
The item copy changes only `lean`. No statement correction or dependency repair
is needed, and there are no new independent definition nodes.

Hypotheses and clauses, read against the full node:

- A site small in the module universe: `C : Type c`, `Category.{v} C`, and
  `J : GrothendieckTopology C`, with rings and modules in `max c v u`.
  This bounds both site universes by the module universe while retaining separate
  object and morphism universes. The base and slice `HasSheafCompose`,
  `WEqualsLocallyBijective`, and `HasWeakSheafify` instance parameters expose
  the sheafification infrastructure available for a small site. In particular
  the slice object universe is `max c v`, not silently identified with `v`.
- A morphism of commutative ring sheaves: `{R S : Sheaf J CommRingCat.{max c v u}}`
  and `(φ : R ⟶ S)`. The result quantifies over every such morphism.
- E is actual ordinary extension: the reused `Extension` records its functor's
  objects as `changeOfRingsOfUniverses φ M` and its maps as
  `changeOfRingsHomOfUniverses φ M f`, with transported object equalities.
  Its additive instance permits `Extension.complex`, exactly termwise extension.
  `restriction` is the existing Mathlib `restrictScalars.mapHomologicalComplex`.
- Every object W and arbitrary module sheaves on C/W: `slices W` has type
  `NormalizedOrdinaryAdjunction` for `(J.overPullback CommRingCat W).map φ`.
  The `forward` and `inverse` fields quantify over arbitrary slice modules M,L,
  every object of the slice, every section x, and every scalar s. They state
  precisely g(1 tensor x) and s h(x). `adjunction.homEquiv` is an equivalence
  with inverse laws and pre/postcomposition naturality. `additive` states its
  additive law; inverse additivity and preservation of zero follow from this
  equivalence. The explicit `@id` casts only expose the unchanged underlying
  section type when using the S-action after scalar restriction.
- Compatibility with slice restriction: `overIso` identifies restricted global
  extension with extension of the restriction; `over_pure` normalizes it on
  every s tensor x. The forward formula and naturality of the restricted maps imply
  compatibility of the bijections.
  `furtherIso` and `further_pure` give the same compatibility
  for every arrow V to W and arbitrary modules on C/W, using Mathlib `overMap`.
  Thus this is not restricted to slice modules coming from the original site.
  Inverse compatibility follows from the inverse laws of the equivalences.
- T(A) is the reused `tensor` functor, tensoring on the left by S regarded as
  an R-module, termwise. `chains.nu` is a natural isomorphism
  `tensor φ ≅ ordinary.extension.complex ⋙ restriction φ`;
  `nu_pure` sends the actual `tensorSection` to `Extension.section` unchanged.
- Arbitrary unbounded P and N: `Complex R` and `Complex S` are all cochain
  complexes indexed by integers, with no boundedness predicate. `chains.theta`
  has exactly source U Hom_S(EP,N) and target Hom_R(P,UN).
- Product Hom, local coordinates and evaluation: both source and target are
  the recorded `CategoryTheory.homComplex`; the reused `evaluate` is
  `homComplexπ`, applied to the local section and then evaluated at
  `op (Over.mk (𝟙 V.unop))`. `theta_forward` says g maps to g(1 tensor x).
  `theta_inverse` quantifies over every section of the full product term and
  says its inverse evaluated at s tensor x is s times the corresponding
  R-linear coordinate. These formulas over every V also specify evaluation
  at arbitrary further slice objects, by restriction of a section to V.
- The differential is exactly the recorded product-Hom differential
  `d_N f - n.negOnePow • (f d_P)` (`homComplex_d_π`, Stacks 0A8X).
  `theta` is an isomorphism in the category of complexes, so both directions
  commute with this differential; it is not merely a degreewise bijection.
- `theta_natural` is the chain-map equation for every a:P' to P and b:N to N',
  using the actual componentwise `homMap` and termwise extension/restriction.
- No flatness, boundedness, support restriction, K-injectivity or preservation
  of products by E is a binder or field. Local formulas quantify over arbitrary
  product sections, not a direct sum or finitely supported family.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently Mathlib `SheafOfModules`, its module-linear maps and category.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal` and its public tensor APIs,
  in particular the existing sectionwise tensor/sheafification construction.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`, unchanged sections with restricted action.
- `WeilConjectures.Algebra.Homology.HomComplex` and `HomComplexComponents`:
  `homComplex`, `homComplexFunctor`, `homComplexπ`, `homComplex_d_π`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous` and
  `Mathlib.CategoryTheory.Sites.Over`: `overFunctor`, `over`, `Hom.over`,
  `overMap`, `overFunctorMap`, `GrothendieckTopology.over`, `Sheaf.over`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`:
  `SheafOfModules.homObj`, the actual local linear-map sheaf.
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`:
  `PresheafOfModules.sheafification` and `sheafificationAdjunction`.
- Proof imports: `Sheaf.Algebra.Homology.SliceModuleSheafification`
  (`sliceSheafificationComparison_isIso`, `sliceSheafificationIso`) and
  `Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction`
  (`sheafRingCoefficientOrdinaryAdjunction`). The tensor universal property
  is Mathlib `TensorProduct`, `TensorProduct.lift`, `TensorProduct.ext'`.

The existing helpers in `Sheaf.Algebra.Homology.StrictScalarHomChain` were read
in full and reused: `Complex`, `Extension`, `Extension.complex`,
`Extension.section`, `restriction`, `scalarModule`, `tensor`, `tensorSection`,
`evaluate`, `homMap`. Its stronger `Data` and existence theorem do not state
this node: they include alpha, sigma, a strict square and coefficient coherence,
and omit the arbitrary-module slice adjunctions and explicit inverse theta.
No theorem from that module is used to supply our existence assertion.

Import-plan note for the maintainer: the older parent owns these already landed
helper definitions, so importing it is necessary to avoid private copies.
Do not add the reverse proof import to `StrictScalarHomChain` automatically:
that would close an import cycle. This is the stage-2 rule-7 exception for
proof imports that close a cycle. A future proof-side factorization can move
these existing helper declarations to their own module without changing them.
This delivery neither assumes nor invokes the parent's existence theorem.

Edge cases checked before drafting and again on the completed statement:
identity R=S; zero target ring S; R=Z and S=F₂ (no flatness); characteristic 2
(the integer negOnePow sign retains the right differential); zero complexes;
complexes with nonzero terms in every integer degree; arbitrary infinite
product families; empty site; a slice with only identity restrictions; repeated
slice restriction and arbitrary modules on a slice. All are admitted by the
binders. The inverse formula uses the original S-action, not an R-action
on an S scalar; the compiler probe exposed and fixed this typing detail.

Searches actually run:

- `msearch.py ... leanfinder`: "Extension restriction scalar adjunction on every
  slice induces natural normalized isomorphisms of unbounded internal Hom
  complexes of sheaves". Eight hits concerned ordinary sheaf pullback,
  global-sections naturality, module sheafification and light-condensed internal
  Hom; none is the statement. Relevant source interfaces were read.
- `msearch.py ... loogle`: `"changeOfRings", "hom"`: zero hits.
- `msearch.py ... grep`: `changeOfRings|homComplex|extendRestrictScalarsAdj`,
  subdirectory `Algebra/Category/ModuleCat`: 22 hits, ordinary scalar change
  infrastructure; none supplies the slice-normalized internal Hom chain result.
- `msearch.py ... leansearch`: "Extension restriction of scalars of sheaves
  induces a normalized isomorphism of unbounded internal Hom complexes":
  eight hits on module extension/restriction and presheaf restriction; no match.
- Local `rg` of `lean/WeilConjectures` and `lean/Sheaf` for scalar Hom chain
  comparisons found `StrictScalarHomChain`; its definitions are reused as above.
  `grep -rn` of the exact item id in `lean/WeilConjectures` found no match.
  The upstream name table was searched as well. No exact existing declaration.

Sources opened: local Stacks `sites-modules.tex` at 03CZ
(`lemma-adjointness-tensor-restrict`, including its sheafification proof), and
`sites-cohomology.tex` at 0A8X (`section-hom-complexes`, full product and signed
formula); the node's seven proof steps were read in full and are reproduced in
the theorem docstring, with their cited proof dependencies.

## Second reading by Q77

No second agent was started, as the dispatcher explicitly forbids that; the
maintainer supplies the independent review. I performed a separate rereading
with the node and final module open. Each clause is matched above. This caught
that restriction compatibility must cover arbitrary slice modules, not just
restrictions of global modules; the final field `further_pure` quantifies over those modules. Both theta directions are stated,
and its naturality is contravariant/covariant in the correct inputs. No auxiliary
alpha/sigma or coefficient coherence conclusion is smuggled into this node.
The site and module universes remain independent up to their required maximum;
explicit slice sheafification instance arguments repair inference without an
extra equality of universes. All object data referenced are existing genuine
constructions. The only proof body is the node's named `sorry` theorem.

Validation: `scompile.py Q77 lem-sfb-slice-scalar-hom-chain-adjunction`
compiled the final module cleanly in both modes (sandbox 16.2 s, library
20.4 s). Earlier timeout diagnostics were repaired by suppressing unnecessary
constructor-injectivity/size-specification generation and keeping canonical
section-evaluation definitions opaque during elaboration. No timeout limit
was raised, no theorem was proved, and the mathematical statement was retained.
