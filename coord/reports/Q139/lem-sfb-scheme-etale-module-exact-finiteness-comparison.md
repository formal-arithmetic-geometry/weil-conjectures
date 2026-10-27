## Worker report

The module `Sheaf.AlgebraicGeometry.SchemeEtaleModuleExactFinitenessComparison`
states the ambient exactness and both finiteness equivalences of
`lem-sfb-scheme-etale-module-exact-finiteness-comparison`. The sole postponed
proof is `AlgebraicGeometry.Scheme.Modules.scheme_etale_module_exact_finiteness_comparison`.
Its docstring follows all five accepted DAG proof steps. The node's statement,
statement dependencies, proof and proof dependencies are unchanged. No new nodes
or dependency repairs were required. No statement dispute was found.

Sources read: `literature/stacks-project/descent.tex`,
`lemma-equivalence-quasi-coherent-limits` (Tag 06VE), especially (3), (4), (5),
(6) and their proofs, and `lemma-equivalence-quasi-coherent-properties`
(Tag 05VG), including the local-properties proof using fpqc descent. The tag-to-label
mapping was verified in `literature/stacks-project/tags/tags`.
06VE(5) states exactness into all small-etale module sheaves; (6) explicitly
excludes a corresponding claim on the big site. 05VG includes both finite type
and finite presentation without a Noetherian hypothesis. Its extra Noetherian
condition concerns coherence, which is not asserted by this item.

Hypotheses and clauses, individually:

- An arbitrary scheme is `T : Scheme.{u}`, with `u` explicitly declared.
  There are no Noetherian, quasi-compact, separated or characteristic hypotheses.
- Zariski modules are exactly `T.Modules`, with the existing
  `SheafOfModules.IsQuasicoherent` predicate. For a sequence all three objects
  are required to be quasi-coherent by the three explicit implications
  `S.X₁.IsQuasicoherent`, `S.X₂.IsQuasicoherent`, `S.X₃.IsQuasicoherent`.
  For the finiteness clause this is `[F.IsQuasicoherent]`.
- The associated-module functor is `schemeEtaleModuleComparison T`. This is a
  transparent abbreviation of the existing context's `.extension`, not a second
  construction of associated sheaves. The context is extracted from
  `scheme_zariski_etale_quasiCoherent_equivalence`. Its only fields are proofs:
  continuity of the actual inclusion of Zariski opens and existence of the
  right adjoint to the actual restriction functor. Consequently the choice
  changes no ring, module, map or mathematically arbitrary functor. Extension
  remains the recorded Mathlib ringed-site tensor pullback. In particular, this
  use of a theorem determining its proof data is not hollow data chosen from
  an unconstrained existence claim.
- The section formula and restriction maps are those already identified by the
  dependency theorem: its `e` identifies the additive sheaf with
  `etaleTensorSectionsSheaf F`; its scalar equation makes the identification
  linear, and its morphism equation identifies the functor on module maps.
  The latter associated sheaf's definition uses the actual tensor-section
  presheaf with the unit/composition restriction maps and its descent proof.
- The ambient codomain is the existing `SmallEtaleModules T`, definitionally
  `SheafOfModules.{u} (smallEtaleModuleRing T)`. In particular the target
  `ShortComplex.mk` belongs to all module sheaves, not the quasi-coherent full
  subcategory. Its quasi-coherent essential image is the one established by
  the recorded comparison theorem, using the same Mathlib quasi-coherence
  predicate as `def-trf-space-quasi-coherent-module`.
- Every short exact sequence is `S : ShortComplex T.Modules` with
  `S.ShortExact`. Mathlib's `ShortExact` means exact in the middle, mono first
  arrow, and epi second arrow. The conclusion constructs the short complex
  with exactly `(schemeEtaleModuleComparison T).map S.f` and `.map S.g`, and
  asserts its `.ShortExact`. The existential `h` supplies just the proof that
  these very arrows compose to zero, which is required to construct a
  `ShortComplex`; it neither changes the arrows nor adds a hypothesis. It avoids
  depending on an unregistered preservation-of-zero instance for the extension.
- The finite-type equivalence is
  `F.IsFiniteType ↔ ((schemeEtaleModuleComparison T).obj F).IsFiniteType`.
  `SheafOfModules.IsFiniteType` is Mathlib's local finite generating-section
  predicate: a covering with generating sections, each indexed by a finite
  type. `GeneratingSections.π` is an epimorphism from the corresponding free
  module, so these are precisely the local finite-free epimorphisms in the node.
- The finite-presentation equivalence is
  `F.IsFinitePresentation ↔ ((schemeEtaleModuleComparison T).obj F).IsFinitePresentation`.
  The predicate supplies local `Presentation` objects whose generators and
  relations have finite index sets. A presentation consists of an epimorphism
  from a free module and generators of its kernel, precisely the node's exact
  finite-free presentation. A finite set is equivalent to some `Fin n`, so the
  predicates do not restrict the allowed finite ranks.
- In these predicates the covering topology is the topology of the module's
  site: Zariski opens for `T.Modules`, and `T.smallEtaleTopology` for the target.
  Mathlib's `CoversTop` formulation is equivalent to objectwise-local
  presentations; on this scheme site the terminal object is the identity map.
  The comparison module's named slice-sheafification instances retain section
  universe `u`, despite the etale site's object universe `u+1`. No universe
  equation or extra sheafification assumption was added.

Recorded statement dependencies used (full source signatures and docstrings read):

| Node | Module and declarations used |
| --- | --- |
| `def-pc-scheme` | `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its module category |
| `pqf-def-coherent` | `Sheaf.AlgebraicGeometry.CoherentFiniteType`: publicly exposes the exact `SheafOfModules.IsQuasicoherent` and `.IsFiniteType` predicates; its conjunction wrapper is not an extra hypothesis |
| `def-sc-etale-qcoherent-module` | `WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf`: `AlgebraicGeometry.Scheme.Modules.etaleTensorSectionsSheaf` |
| `def-weil-pbc-etale-site` | `Mathlib.AlgebraicGeometry.Sites.Etale`: `AlgebraicGeometry.Scheme.smallEtaleTopology` and `Scheme.Etale` |
| `lem-trf-scheme-zariski-etale-quasi-coherent-equivalence` | `Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence`: `scheme_zariski_etale_quasiCoherent_equivalence`, `ZariskiEtaleModuleContext.extension`, `SmallEtaleModules`, `smallEtaleModuleRing` in `AlgebraicGeometry.Scheme.Modules` |
| `def-weil-sheaf-of-modules-category` | `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, transparently the Mathlib `SheafOfModules` used by `SmallEtaleModules` |
| `def-trf-space-quasi-coherent-module` | `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`, with the node's recorded Mathlib match `SheafOfModules.IsQuasicoherent` from `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent` |

All already stated proof dependencies are imported without `public` when not
already statement dependencies. This includes the adjunction, colimit preservation,
quasi-coherent kernels and cokernels, flat pullback, left-exact global sections,
sectionwise module-sheaf limits, tensor composition, preservation of quasi-coherence,
etale/fpqc covers, finite-type descent and fpqc descent. Etale composition and
cancellation are in the imported Mathlib etale module. No import was omitted.

Edge cases checked before writing: the empty scheme permits empty local covers
in `CoversTop`; there is no `Nonempty` cover assumption. Zero objects and ranks
zero are allowed by the generating-section/presentation finite-index predicates.
The zero short exact sequence is included. Schemes and rings of every
characteristic are allowed; no reducedness or Noetherianity is used. For an
identity etale cover this specializes to the same local finiteness property.
Infinite-rank modules are not asserted to have either finite property. Exactness
is only asserted on the small site, where the test morphisms are flat; it does
not make the false big-site claim of 06VE(6).

Searches actually made:

- `msearch.py ... leanfinder`: "The Zariski small etale quasi coherent module
  comparison is exact and preserves and reflects finite type and finite
  presentation". Eight hits, on `Scheme.Etale.forgetFullyFaithful`, general
  quasi-coherent finite-presentation data, and etale morphism composition;
  none states the comparison theorem.
- `msearch.py ... loogle`: `SheafOfModules.IsFiniteType, SheafOfModules.IsFinitePresentation`.
  One hit, `SheafOfModules.instIsFiniteTypeOfIsFinitePresentation`; it relates
  the two properties on one site, not their comparison across the two sites.
- `msearch.py ... grep`: `zariskiEtale|smallEtale.*IsFinite|IsFinite.*smallEtale|etale.*[Ee]xact`
  in `AlgebraicGeometry`. Zero hits.
- `msearch.py ... leansearch`: "The association from Zariski quasi coherent
  modules to small etale modules is exact and preserves finite generation and
  finite presentation". Eight hits, all constructors or fields of Mathlib's
  quasi-coherence and finite-presentation data; no comparison statement.
- Direct `rg` searches of `lean/WeilConjectures`, `lean/Sheaf`, and the relevant
  Mathlib directories for the item id, `schemeEtaleModuleComparison`,
  `scheme_etale_module_exact_finiteness_comparison`,
  `smallEtale.*IsFinite(Type|Presentation)`,
  `IsFinite(Type|Presentation).*smallEtale`, and `zariskiEtaleModuleExtension`.
  The existing extension definition was found and reused; the item id occurs
  in downstream proof docstrings but no existing declaration states its result.
  The proposed helper and theorem names were absent, including from
  `dag/lean_names_upstream.json`.
- Read Mathlib `Sheaf/Generators.lean` and `Sheaf/Quasicoherent.lean` for the
  exact finite-type and finite-presentation definitions, and
  `ShortComplex/Basic.lean` and `ShortComplex/ShortExact.lean` for mapped arrows
  and ambient exactness. These notions are reused, not copied.

Validation: `scompile.py Q139 lem-sfb-scheme-etale-module-exact-finiteness-comparison`
compiled the delivered module as both sandbox and library module, with no errors
or warnings. The first compile exposed the Unicode short-complex field spelling
and absence of a registered zero-preservation instance for the context extension;
these were repaired using `X₁`, `X₂`, `X₃` and the explicit mapped short complex.
No theorem proof was filled. All variables and universes are explicitly bound;
`autoImplicit` is disabled. The final source has no scratch checks or local notation.

## Second reading by Q139

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
