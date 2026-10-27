## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleProEtaleGraphSheafSquare` states
`AlgebraicGeometry.ProEtale.etale_proEtale_graph_sheaf_square`. Its only postponed
proof is this theorem. All helper definitions contain actual constructions. The
natural pro-etale graph map is extracted from a uniquely specified natural
transformation, rather than from existence of an unspecified map.

Sources read: Stacks `proetale.tex`, lemma-jshriek-comparison (09AF), including its
common-right-adjoint proof; `etale-cohomology.tex`,
lemma-shriek-into-star-separated-etale (0F4L), including the graph/complement
construction; and the current blueprint's `det-sp-tower-gluing`, Local pairs and
Levels paragraphs. The six steps of the accepted DAG proof are retained in the
main theorem's docstring. No mathematical statement correction is needed.

Hypotheses and objects, individually:

- A finite commutative ring is `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  This is the existing fixed-coefficient encoding, also used by
  `comparisonPullbackExact` and the recorded open comparison.
- The schemes are `{U T : Scheme.{u}}` and the map is `(e : U ⟶ T)`.
- Etaleness is `[Etale e]`, separatedness is `[IsSeparated e]`, and finite
  type is `[LocallyOfFiniteType e] [QuasiCompact e]`.
- `(c : Compactification e)` supplies the actual intermediate scheme `c.Z`,
  proper map `c.g`, open immersion `c.i`, and factorization `c.comm`.
  The open immersion is quasi-compact because e is quasi-compact:
  `Compactification.quasiCompact_openImmersion_iff` in the existing source.
  No Noetherian, absolute quasi-compactness or characteristic hypothesis is added.
- Constant-A module sheaves are `Sheaf ... (ModuleCat.{u + 1} A)` on the
  original small sites. This is the established fixed-ring presentation of
  modules over the constant ring sheaf, not modules over the structure sheaf.
  `comparisonPullbackExact` identifies its pullback and scalar action with the
  intrinsic constant-ring module inverse image.
- Comparison inverse/direct images and their actual unit are
  `comparisonUpperStar`, `comparisonLowerStar`, and `comparisonAdjunction`.
  The pro-etale site retains scheme universe u, object universe u+1 and Hom
  universe u. There is no additional equality of universes.

Clauses, individually:

- The etale sheafified sum is the existing `Etale.etaleLowerShriek`.
  `etaleSumExtension` is the same sheafified left Kan construction for the
  pro-etale localization functor, with no monomorphism requirement. The
  existing `ProEtale.localizationLowerShriek` is restricted to monomorphisms;
  that restriction cannot be imposed on this item. The generic localized
  module extension and the weakly-etale slice equivalence explain the sum
  description of this fixed-coefficient construction. No copy of the general
  module category, sum presheaf or sheafification is introduced.
- The two finite-limit and two finite-colimit preservation conjuncts state
  exactness of both sum functors. `etaleSumAdjunction` is the actual pro-etale
  sum/restriction adjunction; the etale adjunction is the existing
  `Etale.etaleLowerShriekAdjunction`.
- `etaleSumComparisonRestrictionIso` is `Iso.refl` on the two restriction
  composites: they literally restrict along the same site inclusion and
  composition with e. It is the specified localized direct-image comparison.
- `etaleSumComparisonIso` constructs sigma from those composite adjunctions by
  `Adjunction.leftAdjointUniq`. The next theorem conjunct characterizes it
  uniquely by `conjugateIsoEquiv` taking sigma to the inverse of the specified
  right-adjoint comparison. This fixes the adjunction normalization and orientation.
- For every etale input M, every `b : U.Etale`, and every `m : M(b)`, the next
  conjunct evaluates sigma after the comparison unit on the generator
  supplied by the etale sum-adjunction unit. Its value is the pro-etale
  sum-unit generator at `toProEt U b`, applied to the actual comparison unit
  of m. A test object W/T together with a lift t:W→U is exactly such a b,
  since cancellation of etale morphisms makes W→U etale. Its image under the
  localization functor is W/T. Thus this quantifies over every original
  `(W,t,m)` generator, with the identical lift on the two sides.
- These are images of raw summand generators under the sheafification unit.
  The sum-adjunction unit is the Kan-unit inclusion followed by the
  sheafification unit. No assertion describes all sheaf sections as an
  objectwise direct sum.
- The etale G is the existing `Etale.etaleCompactificationGraphMap A e c`.
  Its source was read in full: it constructs the clopen graph projection,
  sum base change, the adjunction-preserving composition, and the transpose
  under c.g inverse image/direct image. It is not an arbitrary comparison.
- `IsCompactifiedProEtaleGraphMap A e c G` specifies the pro-etale G by its
  precise section values. For every pro-etale input M and test object b over
  U, the test object H is base change of the image of b/T along c.g. The two
  projection equalities fix gamma as the graph `(id, b.hom ≫ c.i)` in H.
  `IsOpenImmersion gamma.left` and `IsClosedImmersion gamma.left` state that
  this graph is clopen. Restriction of the image of the sum generator along
  gamma equals the open-extension unit applied to m. Restriction along every
  open test object whose image is the complement of gamma is zero. In
  particular the actual open complement is among these test objects.
- `∃! G` gives a natural transformation satisfying that graph description and
  the square. The graph and complement form a disjoint open cover, so these
  conditions determine each generator image uniquely; the sheafification
  universal property determines G uniquely. `compactifiedProEtaleGraphMap`
  exposes that unique map for downstream consumers. Its only choice is from
  this unique characterization, which determines the entire natural map
  up to equality, as required by the no-hollow-definition rule.
- The existing `openImmersionLowerShriekComparisonUpperStarIso ... c.i` is o.
  The existing `comparisonCoefficientPullbackIso ... c.g` is a^0.
  `graphComparisonDirectImageMate` applies `mateEquiv` to its **inverse**
  and the specified etale/pro-etale inverse-image/direct-image adjunctions.
  It is d, in the required direction, with no invertibility assumption on d.
- The final `∀ M` equation reads, in Lean composition order,
  `sigma.hom.app M ≫ G.app (nu_U^* M) = nu_T^*(G_et.app M) ≫ d.app(j_! M)
  ≫ p_*.map(o.hom.app M)`. This is precisely the displayed square in the node.
  Every factor is a natural transformation, so the equation is natural in M.

Dependency declarations read and used:

- Mathlib's `AlgebraicGeometry.Scheme`, `IsProper`, `IsSeparated`,
  `IsOpenImmersion`, `Etale`, `LocallyOfFiniteType`, `QuasiCompact`,
  `CategoryTheory.Limits.pullback` and its projections are the geometric
  primitives in their recorded modules.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and
  `Scheme.ProEt.topology`; `Mathlib.CategoryTheory.Sites.ConstantSheaf`:
  `constantSheaf`; `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`
  is the intrinsic module presentation behind the fixed-ring one.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparisonModules`; the same underlying
  `comparisonAdjunction`, `comparisonUpperStar`, `comparisonLowerStar` are
  used explicitly throughout.
- `Sheaf.Paper.ComparisonPullbackExact`: `comparisonPullbackExact`, including
  its constant-ring identification and exact fixed-coefficient specialization.
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`:
  `SheafOfModules.extensionByZeroPresheaf`; Mathlib's module sheafification
  and its adjunction identify the raw summand units used here.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`:
  `Etale.etaleLowerShriek`; its restriction adjunction is in
  `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection`.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`:
  `localizedSystemExtension`, `localizedSystemRestriction`,
  `localizedSystemExact`, `localizedSystemAdjunction`.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`:
  `Scheme.ProEt.weaklyEtale_localization` and its actual slice equivalence.
- `Sheaf.Paper.LocalizeRingedSiteMorphismGeneral`:
  `localize_ringed_site_morphism_general`, whose direct-image comparison is
  sectionwise identity, not an unspecified natural isomorphism.
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`:
  `openImmersionLowerShriekComparisonUpperStarIso` and its coherence theorem.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `mateEquiv`,
  `conjugateIsoEquiv`, `unit_conjugateEquiv_symm`;
  `Mathlib.CategoryTheory.Adjunction.Basic`: `Adjunction.comp`.
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`:
  the canonical `comparisonCoefficientPullbackIso`, definitionally the
  recorded support-prefixed interface, normalized as conjugate of the
  sectionwise identity on direct-image composites.
- The remaining stated proof dependencies are imported plainly, including
  `EtaleAmbientAdjointLocality`, `ProEtaleInverseImage`,
  `OpenComparisonUnitNormalization`, `ComparisonPullbackOpenUnit`,
  `ProEtaleIntrinsicOpenUnit`, and `WeilConjectures.SixFunctors.OpenClosed.Complex`.
  The graph-evaluation proof dependency has no Lean record, so there is no
  module to import for it. The main theorem's proof remains postponed.

The item additionally cites the already landed nodes
`def-f7-etale-compactification-graph-map` and `def-nagata-compactification`,
whose recorded constructions it uses. These are additions to stmt_deps only;
no new node, dependency repair, statement change or proof change is delivered.

Edge cases checked mathematically before writing: U empty (all input sheaves
and graph generators give zero); zero ring (zero section modules); identity
compactification (graph is the diagonal and the comparison reduces to its
unit normalization); an open immersion with proper projection the identity;
and the fold T disjoint-union T → T, for which the two lifts remain distinct
summands. In particular no Mono e assumption is present. The complement can
be empty; it is still a site object and the zero restriction is valid. None of
the tests requires that every sheaf section lift globally from a presheaf sum.

Searches for reuse:

- `msearch.py` LeanFinder, query “The canonical etale to pro etale sum extension
  comparison sends a lift summand to the same lift and commutes with
  compactification graph maps”: 8 hits, including standard-etale algebra
  lift lemmas and CompHausLike.sigmaComparison; no matching sheaf theorem.
- `msearch.py` Loogle, query `etaleLowerShriek, comparisonUpperStar`: 0 hits,
  unknown identifier etaleLowerShriek in that Mathlib service.
- `msearch.py` grep, query `etaleLowerShriek|graph.*[Ss]heaf|sumExtension`,
  AlgebraicGeometry: 0 Mathlib hits.
- `msearch.py` LeanSearch, query “Comparison of etale and pro etale sheaf sum
  extension preserves each lift generator and compactified graph extension”:
  8 hits, including sheafifyLift.congr_simp, Subfunctor.to_sheafify_lift_unique,
  Scheme.Etale and site definitions; no matching theorem.
- Repository `rg` for graph maps, sum extensions, localizationLowerShriek,
  comparison names and the node id over WeilConjectures and Sheaf found the
  etale compactification graph map, open-only site comparison, and generic
  localization interfaces used above. It found no exact graph square or
  general-etale pro-etale sum comparison. Searching all proposed full names
  and the upstream name index found no collision (substring hits are the
  different etaleSumExtensionTensorPullbackIso).
- `blueprint_refs.py search 'proetale sum extension'`: 0 blueprint matches;
  the original generic sum-presheaf and localized-module nodes already
  provide the underlying notion. Helpers in this module merely specialize
  it to the original pro-etale site and fix the maps of this item.

Validation: every compile used scompile.py with the default 60-second per-file
limit. The final module compiles cleanly with explicit universe u and
`autoImplicit false`; no warning remains. No local or global library build
was run. The theorem is intentionally sorry, as required in stage 2.

## Second reading by Q77

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
