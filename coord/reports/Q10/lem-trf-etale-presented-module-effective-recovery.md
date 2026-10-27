## Worker report

The module `Sheaf.AlgebraicGeometry.EtalePresentedModuleEffectiveRecovery` states
`AlgebraicGeometry.Scheme.Modules.etalePresentedModule_effectiveRecovery`, with one
`sorry`. The node's statement, dependencies and proof are unchanged. There are no
new DAG nodes and no dependency repairs. `EtalePresentedRecovery` is a transparent
bundle of this theorem's witnesses and equations, not a replacement definition of
quasi-coherence, descent, a free module or a cokernel. Its local cokernels are
specified by their full categorical universal properties. The five helper definitions
construct the missing canonical restriction and coordinate maps from existing APIs;
none chooses an arbitrary map or has postponed data.

Source read: `literature/stacks-project/descent.tex`,
`proposition-equivalence-quasi-coherent`, lines 2498–2620, Stacks Tag 03DX. The proof
lifts free presentation maps by full faithfulness, takes their cokernels, lifts the
overlap identifications, invokes fpqc effectivity, and glues the comparison maps.
The last paragraph applies the same argument to the small etale site. The theorem
docstring reproduces all eight proof steps of the assigned DAG node, including the
cocycle/diagonal check and the canonical counit normalization.

Hypotheses and conclusions, clause by clause:

| Node clause | Lean rendering |
| --- | --- |
| Scheme T, Zariski site, small etale site, actual structure rings | `T : Scheme.{u}`; `T.Modules` and `SmallEtaleModules T`, with the existing `smallEtaleModuleRing T` |
| Canonical tensor extension L and open restriction R | `c : ∀ X : Scheme.{u}, ZariskiEtaleModuleContext X`; its existing `.extension`, `.restriction`, `.adjunction` |
| Site quasi-coherence of G | `G : SmallEtaleModules T` and `[G.IsQuasicoherent]`, exactly Mathlib's site-local arbitrary free-presentation predicate |
| Jointly surjective etale family | `I : Type w`, `U : I → T.Etale`, `cover : ∀ x, ∃ i y, (U i).hom.base y = x` |
| Specified presentations on every V_i | `K J : I → Type u`, `d`, `q`, `zero`, and `presentation : ∀ i, Nonempty (IsColimit (CokernelCofork.ofπ (q i) (zero i)))` |
| Restriction of G to V_i, including its scalars | `presentedEtaleRestriction (U i)`, the module pushforward for `etaleToOver (U i) ⋙ Over.forget (U i)` and the identity on regular-function rings |
| Canonical identifications of extension of free modules with free etale modules | `freeIso` and `freeIso_hom`; `presentedEtaleFreeMap` is the adjoint of the map specified by the actual free generator sections under open restriction |
| Existence of the maps h_i | `lift` and `lift_image` |
| Uniqueness of every h_i | `lift_unique` for every map with the displayed image |
| F_i are the cokernels of h_i | `localModule`, `localQuotient`, `localZero`, and `localCokernel`, the full `IsColimit` universal property of the cokernel cofork |
| Zariski quasi-coherence of F_i | `localQC` |
| Isomorphisms b_i with projection compatibility | `localIso` and `local_projection` |
| The canonical tensor-section coordinates for b_i | `localTensor`, `local_linear`, `local_unit`; naturality is part of the sheaf isomorphism; linearity is explicit and the unit is identity on every open |
| Unique isomorphism phi_ij on overlaps lifting b_j inverse b_i | `overlap`, `overlap_image`, `overlap_unique`; `presentedEtaleLocalMap` writes the restriction of b_i in tensor coordinates, with the actual composition comparison and identity-scheme transport |
| Triple cocycle with canonical pullback identifications | `cocycle` on every common etale test scheme W; use the pairwise or triple fibre product for W. The intermediate pullbacks have already been transported to W via `tensorSectionsComp` |
| Effective descent to quasi-coherent F on T | `globalModule`, `globalQC`, `chartIso`, `effective`; `presentedTensorOverlap` supplies the canonical comparison between the two iterated pullbacks of F |
| Global b extending the local maps | `gluedIso` and `glued_local`, on every etale object of every chart, using `globalTensor`, `global_linear`, `global_unit` and tensor composition |
| Uniqueness of the glued map | `glued_unique` quantifies over all module maps with these same restrictions |
| Restriction of b identifies F with R G | `restrictionIso` and `restriction_hom`, explicitly R(b) composed after the adjunction unit |
| R G is quasi-coherent | `restrictionQC` |
| The canonical counit is invertible | `counitIso : IsIso ((c T).adjunction.counit.app G)` |
| The counit is identity on every open under the prescribed coordinates | `restrictionTensor`, `restriction_linear`, `restriction_unit`, `counit_open` |

The context parameter supplies only proofs of continuity and existence of the
canonical left adjoint. Its two fields are propositions, not arbitrary chosen
functors or maps. Thus quantifying over it adds no geometric hypothesis. The
recorded tensor-sections dependency provides such contexts. The overlap formulation
uses arbitrary etale W over T with etale maps to two charts: this is the usual
localized description of the pairwise fibre product, and it retains the canonical
identifications rather than asking for an unconstrained overlap isomorphism.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and scheme morphisms.
- `Mathlib.CategoryTheory.Sites.Spaces`: `TopologicalSpace.Opens.grothendieckTopology`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.Etale`, `Scheme.smallEtaleTopology`.
- `Sheaf.AlgebraicGeometry.ZariskiEtaleTensorSections`: `zariskiEtale_tensorSections`,
  publicly available through the free-presentation dependency, and its recorded
  `ZariskiEtaleModuleContext` interface from
  `Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the
  transparent specialization of `SheafOfModules`, also imported transitively.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: the recorded
  `SheafOfModules.IsQuasicoherent` part of `pqf-def-coherent`; no finite-type or
  coherence hypothesis is imposed. This record was read including its latest repair.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: the recorded general
  `SheafOfModules.IsQuasicoherent` predicate and slice interfaces; this statement
  concerns schemes, so it uses the scheme slice instances already published by the
  context module, not a private algebraic-space specialization.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: `tensorPullback`,
  `tensorPullbackSectionAdjunction`, and the recorded canonical composition interface.
  `WeilConjectures.AlgebraicGeometry.EtaleTensorSections.tensorSectionsComp` is the
  existing normalized comparison used by the associated tensor-section sheaves.
- `Sheaf.AlgebraicGeometry.EtaleExtensionFreePresentationsHom`:
  `etaleExtension_free_presentations_hom`, the Hom, colimit and normalized local
  tensor-section comparison theorem used in the eight-step proof.
- Proof imports: `WeilConjectures.AlgebraicGeometry.Descent`
  (`exists_isQuasicoherent_toDescentData_iso`),
  `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel`
  (`isQuasicoherent_cokernel`, with `isQuasicoherent_sigma` available through its
  public import of `QuasicoherentKernel`),
  `Sheaf.AlgebraicGeometry.FpqcFinerThanEtale` (`fpqcCover_of_smallEtaleCover`), and
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing`
  (`SheafOfModules.existsUnique_hom_of_cover`). The Mathlib leaf
  `tildeSelf`, `tildeFinsupp`, `isoTop` was read in
  `Mathlib.AlgebraicGeometry.Modules.Tilde`, available through these proof imports.

Edge cases checked before writing: empty T and empty I; an empty cover forces T
empty and every recovery condition remains meaningful. Empty K_i or J_i and the
zero module are covered by `free` and the cokernel cofork universal property without
positivity or nonemptiness assumptions. Infinite presentation sets and arbitrarily
indexed etale covers are retained; the family index has independent universe w.
No affine, separated, Noetherian, finite-presentation-rank, or quasi-compact-chart
assumption appears. Repeated indices are included in the cocycle. The empty open is
included in each unit/counit normalization. Both sites retain objects in u+1 and
sections/morphisms in u; no size equality is imposed.

Searches actually run via `msearch.py Q10 lem-trf-etale-presented-module-effective-recovery`:

- LeanFinder: `Recover a quasicoherent etale sheaf from local cokernels by effective descent`.
  Eight hits, including `SheafOfModules.QuasicoherentData.presentation`, `.I`,
  `presentationOfIsCokernelFree`, `quasicoherentDataOfIsFinitePresentation`, and
  `IsQuasicoherent.nonempty_quasicoherentData`. They describe local presentations,
  not this recovery theorem with the specified cokernels and gluing maps.
- Loogle: `SheafOfModules.IsQuasicoherent, CategoryTheory.IsIso`.
  Three hits: `isQuasicoherent_pushforward_of_isLeftAdjoint`,
  `isIso_fromTildeΓ_of_isQuasicoherent`, `isQuasicoherent_iff_isIso_fromTildeΓ`.
  None states etale recovery.
- Mathlib grep: `etale.*(recovery|cokernel)|effective.*quasicoherent`: zero hits.
- LeanSearch: `Quasicoherent modules on the small etale site are recovered by descent of local cokernel presentations`.
  Eight hits, all generic `SheafOfModules` presentations/quasi-coherence declarations,
  including `Presentation` and `presentationOfIsCokernelFree`; no exact recovery theorem.
- Local rg in `lean/WeilConjectures`, `lean/Sheaf`, Mathlib and
  `dag/lean_names_upstream.json` for all seven proposed declaration names: no matches.
  Exact item-id rg likewise finds no prior declaration. Broader searches find the
  parent Zariski/etale equivalence theorem and the free-presentation sibling, which
  do not state the explicit local-cokernel witnesses of this item.
- Local rg for `etaleToOver.*Over.forget` finds only the sibling's presheaf restriction
  comparison and other non-module restrictions; there is no existing module
  restriction functor to duplicate. The helpers use the recorded site equivalence
  and Mathlib's actual `pushforward`, `freeHomEquiv`, `pushforwardSections`, and
  `tensorSectionsComp` constructions.

No statement dispute or source correction is needed. Compile diagnostics were used
to replace expensive repeated chosen `cokernel` expressions by explicitly typed
cokernel objects with the identical full universal property. This is an encoding
change only. No compiler limit is raised and no diagnostic commands are delivered.

## Second reading by Q10

A separate clause-by-clause self-audit was made with the node and final module open;
the dispatcher explicitly forbids starting another agent, so this does not claim an
independent worker reading. The maintainer supplies the independent delivery review.
The audit matched each hypothesis and conclusion in the table above and checked:
`lift_image` and `local_projection` have the correct directions; overlap maps go
from the i pullback to the j pullback and compose in that order; `effective` says
that the chart identifications induce those maps; `glued_local` uses the inverse
composition comparison from the pullback along A → T to the iterated pullback;
`restriction_hom` is unit followed by R(b); and `counit_open` states identity after
both the open tensor comparison and the inverse normalized extension comparison.
The audit added explicit scalar equations to the three families of additive
comparison isomorphisms, so no arbitrary additive coordinates can replace module
coordinates. It also checked the cokernel universal property after the elaboration
repair, all seven declaration docstrings, explicit variable/universe binding, and
100-column formatting. No mathematical mismatch remains.

Import-graph note: the context-owning parent module is necessarily imported through
the recorded tensor-sections dependency. Adding a proof import of this delivery to
that parent would close a cycle; the standing stage-2 cycle exception applies to
that future import. This delivery changes no parent source and removes no DAG edge.
