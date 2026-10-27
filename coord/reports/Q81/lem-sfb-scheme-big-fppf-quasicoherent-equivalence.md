## Worker report

The item is stated by `AlgebraicGeometry.Scheme.scheme_big_fppf_quasicoherent_equivalence`
in `Sheaf.AlgebraicGeometry.SchemeBigFppfQuasicoherentEquivalence`. Its statement is
unchanged. It asserts existence of the equivalences together with fully normalized
section comparisons, rather than choosing an arbitrary equivalence to define data.
All theorems in this delivery have `sorry` proofs. Definitions contain real data.
The module docstring reproduces the nine proof steps and their DAG dependencies.

Read source: `literature/stacks-project/descent.tex`, the associated-sheaf discussion,
`lemma-fully-faithful-associated` (0GN7), `proposition-equivalence-quasi-coherent`
(03DX) with its proof, `proposition-equivalence-quasi-coherent-functorial` (03LC),
and `lemma-equivalence-quasi-coherent-limits` (06VE), including its nonexactness example.
No correction or disputed statement is needed.

Clause-by-clause correspondence:

- Universes/sites: explicit `universe u`, `Scheme.{u}`, `Over V`, and the existing
  `fppfTopology.over V`; site objects are in u+1, maps and sections in u. Small
  colimit indices are `I : Type u` with `[SmallCategory I]`, matching the module
  universe; no finiteness restriction is imposed. The item-owned size helpers below
  supply actual sheafification at this size instead of an extra size hypothesis.
- Arbitrary scheme V: the witness `e` is a family over every `V : Scheme.{u}`.
  No Noetherian, separated, flat, or finite-presentation binder is introduced.
- Structure sheaf: `sfbFppfStructureSheaf` is the restriction of the existing
  global-functions sheaf `Scheme.Γ`; its objects and maps are exactly
  `Γ(U.left, ⊤)` and `h.left.appTop`. `sfbFppfRings` only forgets commutativity.
- Scheme quasi-coherence: `SfbZariskiQCoh V` is the full subcategory for the
  existing `SheafOfModules.IsQuasicoherent`, without a finite-type condition.
  `pqf-def-coherent` now records a finite-type conjunction; its module is imported,
  but only its publicly imported Mathlib quasi-coherence predicate is used here.
- Site quasi-coherence: `SfbFppfQCoh` uses the same Mathlib predicate on the big
  site. Read `QuasicoherentData` and `Presentation`: arbitrary small free generators
  and relations on covering slices, with no finite-type or finite-presentation
  assumption. The recorded algebraic-space `QCoh` specialization is imported but
  not misapplied to a big scheme site; its general Mathlib match is used directly.
- A(M)(u) = Γ(T,u*M): the additive equivalences `s V M U` give this formula;
  the first conjunct says they preserve the full scalar action, hence are module
  comparisons. The associated sheaf has these actual sections up to the specified
  canonical isomorphism, with no extra sheafification clause.
- Restrictions: the second conjunct explicitly gives section pullback by
  `sfbSectionPullback`, followed by `tensorPullbackSectionComp.inv` and transport
  along `h.w`. These are the dependency's uniquely section-normalized comparisons.
- Every module map: the third conjunct gives `Γ(T,u*v)` for every `v : M ⟶ N`.
  Both categories are full subcategories: zero and noninvertible maps are retained.
- Equivalence: `e V : SfbZariskiQCoh V ≌ SfbFppfQCoh V` includes full faithfulness,
  essential surjectivity, and the triangle identity. Its inverse is restriction to
  Zariski opens, specified by `r V G W` on every open, with the following three
  conjuncts enforcing map naturality, scalar action via `W.topIso.inv`, and
  restriction along every inclusion of opens.
- Canonical unit/counit, identity on opens: the next two conjuncts give their
  evaluations using `s`, `r`, and `sfbOpenSection`. Thus under the canonical
  identification of pullback to an open with original sections, each is identity.
- Every scheme map f: the family `q V T f M` supplies quasi-coherence of the actual
  tensor pullback. The family `b V T f M` compares restriction of A_V(M) along
  `Over.map f` with A_T(f*M). Its displayed normalization is the canonical
  `tensorPullbackSectionComp` on every test object. The next conjunct is naturality
  for all M-maps. The next two are identity and composition compatibility, using
  `sfbFppfIdArrow`, `sfbFppfCompArrow`, and the recorded pullback identity/composition.
- All small colimits into ambient module sheaves: for every small diagram D the
  ambient Zariski colimit is quasi-coherent, and the displayed `c` is the iso from
  its A-image to the ambient big-site colimit. Its equation with every colimit
  injection specifies the canonical comparison. `sfbAssociated` explicitly forgets
  the quasi-coherence condition in the target and `sfbZariskiInclusion` in the source.
- Cokernels: both `cokernel v.hom` and `cokernel (A.map v)` are in their ambient
  module categories; the comparison commutes with the actual cokernel projections.
  No kernel or exactness assertion is made.
- Structure module: the following conjunct supplies its quasi-coherence, an iso
  A(O_V) ≅ O, and its formula on every test object's sections, using the normalized
  pullback-to-regular-module iso `sfbPullbackUnit`.
- Tensor: the final conjunct supplies quasi-coherence of the ordinary scheme tensor,
  the iso A(M tensor N) ≅ A(M) tensor A(N), and the canonical scheme pullback tensor
  comparison `p`, normalized on all local pure tensors. `siteSheafTensorRight` is
  the recorded independent-universe sheaf tensor (sectionwise tensor followed by
  module sheafification). The last equation specifies the inverse on every local
  pure tensor through `siteSheafTensorTmul`, the inverse of `p`, and `tmulSection`.
  This does not require the entire big site to be essentially u-small merely to
  invoke a monoidal-category convenience API.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage`,
  `Scheme.fppfTopology`; `Mathlib.CategoryTheory.Sites.Over`: the over topology,
  `Sheaf.over`, `Sheaf.pushforwardOverMapIso`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType` and the Mathlib Quasicoherent module:
  `Scheme.Modules.IsQuasiCoherentFiniteType` was read; only its quasi-coherent
  predicate `SheafOfModules.IsQuasicoherent` is appropriate to this item.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullbackSectionAdjunction`, `tensorPullbackSection`,
  `tensorPullbackSectionComp`, `tensorPullbackSectionId` (the tensor data themselves
  remain from `WeilConjectures.AlgebraicGeometry.TensorPullback`).
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`:
  `AlgebraicSpace.QCoh` and its Mathlib `IsQuasicoherent` general-site match.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` and its public
  imports: `SheafOfModules.siteSheafTensorRight`, `siteSheafTensorTmul`. The recorded
  cochain monoidal wrapper needs `EssentiallySmall`; the underlying tensor does not.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.isSheaf_Γ`.
- `WeilConjectures.AlgebraicGeometry.Modules.TensorSection`: `Modules.tmulSection`.

All already stated proof dependencies' modules are imported, including the Mathlib
matches for fppf versus fpqc, Zariski versus fppf, tilde free modules, and left-adjoint
colimit preservation. `lem-sfb-big-fppf-zariski-ringed-comparison` currently has no
Lean record or module, so no import can be written for it; it is a proof dependency,
not an unstated notion used by this Lean signature.

Edge checks: the empty scheme is allowed, and all section formulas then concern
zero modules; no nonempty-cover or nonempty-index binder excludes it. Zero modules
and all linear maps are retained. The empty diagram, infinite small coproducts,
and arbitrary relations are allowed. The nonflat map Spec(F_2) → Spec(Z) is allowed;
06VE's multiplication-by-2 example explains why the theorem asserts colimits and
cokernels and does not assert exactness. Identity and two successive base maps are
explicit clauses, including their changes of structure arrows. Tensor comparison
uses local generators, never an assertion that global sections of a tensor are
always a tensor product of global sections. No affine-intersection hypothesis appears.

Searches run (through the prescribed logged wrapper):

1. leanfinder query `Quasi coherent modules on the big fppf site of a scheme are
   equivalent to Zariski quasi coherent modules`: eight hits, all local-presentation
   `SheafOfModules.IsQuasicoherent`/`QuasicoherentData` infrastructure, no equivalence.
2. loogle query `SheafOfModules.IsQuasicoherent, Scheme.fppfTopology`: zero hits;
   service reports unknown identifier `Scheme.fppfTopology`, so this query does not
   establish absence. The direct source search below supplies that check.
3. grep query `fppf|IsQuasicoherent`, subdirectory `AlgebraicGeometry/Sites`: five
   hits, the existing fppf precoverage/topology infrastructure, no module equivalence.
4. `rg` of project `lean/Sheaf` and `lean/WeilConjectures` for bigFppf/bigFPPF,
   fppf/quasi-coherent and associated-module variants found the small-etale section
   functors and algebraic-space fppf comparison; none states this big-scheme theorem.
   Direct search of the item's id in `lean/WeilConjectures` returned no match.
5. Direct Mathlib/source reads found `Scheme.restrictFunctor`, `Scheme.Γ`,
   `Scheme.Modules` and the general-site local-presentation predicate; they are used,
   not copied. The small-etale associated sections are not definitions on Over V.

Validation of the returned packet: both original files compiled separately through
`scompile.py`. The repaired packet contains one module. It compiled cleanly through `scompile.py`
in sandbox mode (9.6 s) and at its actual module path (9.9 s). The recorded statement
is the exact, unchanged signature in that file. Source checks confirm the item
changes only `lean`, all 26 declarations are recorded, and the topology node is
byte-identical to the live version.

## Repair of return L / H13

The returned head `4b23f0948951` incorrectly rebound Q05's already usable topology
record to auxiliary size instances. The initial saved-packet dry run passed at
`038120a4eef`, but that automated success did not resolve the independent review.

The repair preserves `def-pc-fppf-site.json` byte for byte from the current live
repository, including its existing Mathlib `fppfTopology`/`fppfPrecoverage` record.
There is no dependency-record change in this delivery and no dependency module.
`FppfModuleSiteInfrastructure.lean` has been removed from the packet. Its ten
instances now appear before their users in the item's own module, carry the item's
blueprint id in every source/proof docstring, and are listed in `lean.declarations`:

- `sfbFppfCommRingToRing`, `sfbFppfCommRingToRingOver`,
  `sfbFppfCommRingToRingOverOver`: forgetting commutativity preserves sheaves on
  the fppf site and its first and second slices.
- `sfbFppfRingToAdd`, `sfbFppfRingToAddOver`, `sfbFppfRingToAddOverOver`:
  forgetting multiplication preserves sheaves on the same three sites.
- `sfbFppfHasWeakSheafify`, `sfbFppfWEqualsLocallyBijective`: small-valued additive
  sheafification and detection of its equivalences on the big site over a scheme.
- `sfbFppfOverHasWeakSheafify`, `sfbFppfOverWEqualsLocallyBijective`: the same
  facts on its slices.

Their source is Stacks Tags 021S, 021L, 00WB, 00WK; their proof docstrings retain
the elementwise gluing, shrinking using `fppf_small_of_local_representatives`,
and cover-preserving slice-equivalence arguments. Their signatures and sorry-only
proofs are unchanged. The small-refinement lemma's module is a proof-only import.
The public Mathlib topology, slice, and quasi-coherence imports formerly supplied
through the removed module are now explicit statement imports of the item.
No new node, hypothesis, universe constraint, or topology is introduced.
The main theorem and all its clause equations are byte-identical to the returned
packet, as allowed by the review's clause-by-clause acceptance.

## Second reading by Q81

This is the author's final rereading, not an independent worker's review: the
dispatcher explicitly forbids starting other agents and assigns independent review
to the maintainer. I reread the complete node, the merged item module and the cited source.
The first draft omitted explicit base-map identity/composition equations; these
were added using actual identity and associativity arrows. The ten item-owned size interfaces preserve scheme and section
universe u; the topology dependency retains Q05’s exact existing declaration. An ambient cokernel instance-search issue was repaired by naming the
ambient cokernel-existence obligation instead of restricting the diagram or adding
a hypothesis. The signature's clauses now correspond to every node clause as
listed above. No statement/dependency list or proof text in the DAG was changed. For this repair
I checked that all ten moved instances have the same types and proofs, precede
the definitions that need them, use the item blueprint id, and occur in the item
declarations list. The current topology node matches the live bytes exactly.
The prior H13 claim that the topology record itself needed repair is withdrawn.
