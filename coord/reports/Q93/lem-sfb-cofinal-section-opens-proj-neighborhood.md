## Worker report

Stage 2, Q93, 2026-10-24. The module
`Sheaf.AlgebraicGeometry.CofinalSectionOpensProjNeighborhood` states
`AlgebraicGeometry.Scheme.Modules.exists_cofinal_section_opens_proj_neighborhood_iso`.
There is one theorem, with whole proof `sorry`, and no new definitions. Its docstring
contains the seven-step proof from the accepted DAG split. Only the item's `lean`
field changes; the natural-language statement, statement dependencies, proof and proof
dependencies remain verbatim.

The inherited ending was a stage-1/stage-2 mismatch, not an unresolved delivery failure:
Q96's 2026-10-24 PASS is `reviewed`, approving the DAG split, and there is no `lean` or
`reviewed_lean`. The queue row is stage 2, action `state`. There is no repair-note file
for this item. The stage-handoff rule at the start of `coord/brief-stage2.md` explicitly
permits stating such an accepted split. This delivery preserves that split.

Each hypothesis and conclusion of the node is rendered as follows:

| Node text | Lean |
| --- | --- |
| Affine scheme B | `(B : Scheme.{u}) [IsAffine B]` |
| Scheme Y and morphism q:Y→B | `(Y : Scheme.{u}) (q : Y ⟶ B)` |
| Y quasi-compact | `[CompactSpace Y]`, without a Hausdorff assumption |
| Y quasi-separated, i.e. intersections of affine opens quasi-compact | `[QuasiSeparatedSpace Y]`; `quasiSeparatedSpace_iff_forall_affineOpens` in Mathlib's `Morphisms.QuasiSeparated` is precisely the equivalence with the node's formulation |
| Invertible O_Y-modules L,K | `(L K : Y.Modules) [L.IsInvertible] [K.IsInvertible]` |
| A_L and A_K are their nonnegative graded section rings | the existing `InvertibleSectionRing` with grading `sectionRingGrade L` and `sectionRingGrade K`, used as the rings underlying `Proj` |
| Tensor-power sections of positive degree | `s : sectionRingGrade L d` with `0 < d`, and `t : sectionRingGrade K n` with `0 < n`; these graded components are the ranges of `DirectSum.of`, so evaluation `s.val d` / `t.val n` identifies them with all sections of the relevant tensor power, without restriction |
| Y_s and Y_t are the nonvanishing opens | `nonvanishingLocus (L.tensorPow d) (s.val d)` and its K analogue, using the dependency's germ/maximal-ideal definition |
| Each family covers Y | `hL` and `hK`, each quantifying over every point and giving a section of strictly positive degree nonvanishing there |
| For every positive K-section t and y∈Y_t, some positive L-section s has y∈Y_s⊆Y_t | `hLK`, with the positive-degree premise, arbitrary `t` and `y`, membership premise, and the positive-degree, membership and subset conclusions |
| For every positive L-section s and y∈Y_s, some positive K-section t has y∈Y_t⊆Y_s | `hKL`, the reverse direction with all the same quantifiers |
| P_L=Proj(A_L), P_K=Proj(A_K) | `Proj (sectionRingGrade L)` and `Proj (sectionRingGrade K)` |
| r_L,r_K are the canonical maps of lem-sc-ample-proj-canonical-map | `(exists_sectionRing_proj_morphism Y L hL).choose` and its K counterpart, using that dependency's actual declaration and its full chart characterization, rather than only a nonvanishing-preimage condition |
| The B-structures are induced by q | `pL`, `pK` with `hpL`, `hpK`, their defining triangles with those canonical maps; the uniqueness and existence justification is given below |
| Open subschemes V_L⊆P_L, V_K⊆P_K | `VL : (Proj (sectionRingGrade L)).Opens` and `VK` analogously; `VL.toScheme`, `VK.toScheme` are the actual open subschemes and `VL.ι`, `VK.ι` their canonical open immersions |
| The opens contain the respective canonical images | the first two conclusion equations give factorizations `rL : Y ⟶ VL.toScheme`, `rK : Y ⟶ VK.toScheme` through the open inclusions; this is equivalent to the image-containment assertions |
| An isomorphism θ:V_L≅V_K | `θ : VL.toScheme ≅ VK.toScheme`, including both inverse identities in the categorical isomorphism data |
| θ∘r_L=r_K after factoring | `rL ≫ θ.hom = rK` |
| θ is over B | `θ.hom ≫ VK.ι ≫ pK = VL.ι ≫ pL`; the inverse is automatically over B by the isomorphism identities |

Canonical-map and base-structure details: the source map is not an arbitrary map with a
preimage property. The witness of the dependency theorem has both the exact preimages
and the fraction formula for every homogeneous fraction. This formula determines each
map on an affine chart and therefore determines the global morphism uniquely. Thus
using `.choose` here takes data from a characterization determining the object up to
equality, as permitted by AGENTS.md §5. No additional choice of a merely existing
noncanonical object is used.

Likewise `pL` and `pK` are NOT unconstrained maps or stronger structural hypotheses.
The normalization equations are an alternative presentation of the induced base
structures. For a qcqs source, the fraction maps on every positive-degree standard
chart are ring isomorphisms by `sectionRing_localization_bijective`. The sheaf-on-basis
criterion identifies the whole structure sheaf of P_M with `(r_M)_* O_Y`. In particular
`r_M.appTop` is an isomorphism. Any morphism `q : Y ⟶ B` to affine B therefore induces
one map `P_M ⟶ B`: on global functions its ring map is q's ring map followed by the
inverse of `r_M.appTop`. The affine-target correspondence gives the morphism and its
triangle. This is exactly the structure induced from q through degree zero in the
section ring. Uniqueness also follows by scheme-theoretic dominance and separatedness
of B. Consequently hpL/hpK describe structures that exist for every datum covered by
the node, exclude none, and determine the base maps uniquely. The result applies to
the canonical induced structures, and introduces no unspecified replacement map.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, in
  `Mathlib.AlgebraicGeometry.Scheme`; the scheme and morphism structures and docstrings
  were read. `IsAffine` uses the standard Mathlib affine-scheme convention.
- `def-weil-pbc-quasi-compact-scheme`: `CompactSpace`,
  `Mathlib.Topology.Defs.Filter`; its sole field is compactness of the entire space.
- `def-sc-invertible-module`: `Scheme.Modules.IsInvertible`,
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`; its local trivialization
  condition and tensor-power interface were read, not privately redefined.
- `def-sc-invertible-section-ring`: `InvertibleSectionRing`, `SectionRingComponent`,
  `sectionRingGrade`, `sectionRingGradedRing`, in
  `WeilConjectures.AlgebraicGeometry.InvertibleSectionRing`.
- `def-weil-pbc-ample-invertible-module`: `Scheme.Modules.nonvanishingLocus`,
  `WeilConjectures.AlgebraicGeometry.Ample`. Only this dependency's nonvanishing notion
  is used; no ampleness assumption is introduced.
- `def-pc-proj`: `AlgebraicGeometry.Proj`, `Proj.basicOpen`,
  `Proj.basicOpenIsoSpec`, `Proj.basicOpenIsoAway`, in Mathlib's
  `AlgebraicGeometry.ProjectiveSpectrum` files. This node is a Mathlib leaf and requires
  no additional Lean record.
- `lem-sc-ample-proj-canonical-map`:
  `Scheme.Modules.exists_sectionRing_proj_morphism`,
  `WeilConjectures.AlgebraicGeometry.AmpleProjCanonicalMap`. Its full signature and
  docstring were read; it supplies exactly the canonical chart-normalized morphism.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`,
  `Mathlib.AlgebraicGeometry.OpenImmersion`; standard `Scheme.Opens.toScheme` and `.ι`
  realize the open-subscheme clause.

These are exposed by the public imports, including their transitive public imports.
All the accepted proof-dependency modules are also imported, privately when only the
proof needs them: `SectionRingLocalizationBijective`,
`Mathlib.Topology.Sheaves.SheafCondition.Sites`,
`Mathlib.AlgebraicGeometry.GammaSpecAdjunction`,
`Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated`, and
`Mathlib.AlgebraicGeometry.Gluing`. Their localization bijection, sheaf-on-basis,
affine-target adjunction, Proj separatedness, scheme-theoretic dominance extensionality
and gluing signatures were inspected. There is no import-cycle omission.

Edge cases checked mathematically before writing:

- Empty Y: the covers and refinements are vacuous, and its section-ring Proj is empty.
  Empty neighborhoods and the unique isomorphism satisfy every triangle. No point or
  nonempty-cover hypothesis is silently added.
- Empty B forces Y empty; the same case applies.
- L=K: identical section opens refine each other using the original degree and section;
  the common canonical image admits the identity comparison.
- O(1) and O(2) on projective space: the cofinality permits different positive degrees;
  no degree-one generation or equality of the rings is assumed.
- O(1,0) and O(0,1) on P1×P1 fail the refinement assumptions, as they should; neither
  single refinement direction was omitted.
- Zero or nilpotent homogeneous sections have empty nonvanishing open; the universal
  point condition is then vacuous. The result does not assume their opens affine.
- Degree zero is excluded only from section-cover and refinement indices, as stated;
  it remains part of each full section ring. No noetherian, reduced, separated-Y,
  finite-generation, or ampleness hypothesis was added.
- One explicit universe `u` is used for schemes and their module sections; there are
  no auto-bound universes, independent undersized test types or file-local definitions.

Searches actually run, with Q93/item logged through msearch.py:

1. LeanFinder: `Section ring Proj targets are isomorphic on open neighborhoods of the
   canonical images when nonvanishing opens of two invertible modules mutually refine
   each other`. Eight hits, including `Proj.fromOfGlobalSections_morphismRestrict`,
   `Proj.awayMap_awayToSection`, and `Proj.basicOpenIsoAway`: single-ring chart formulas
   and localization maps, not this two-section-ring comparison.
2. Loogle: `AlgebraicGeometry.Proj, CategoryTheory.Iso`. Four hits:
   `Proj.basicOpenIsoSpec`, `Proj.stalkIso`, `Proj.basicOpenIsoAway`,
   `Proj.pullbackAwayιIso`; these compare a chart or stalk with its localization or
   identify a chart pullback, not neighborhoods in different section-ring targets.
3. Mathlib grep: `cofinal.*section|sectionRing.*[Nn]eighborhood|[Pp]roj.*[Nn]eighborhood`
   under `AlgebraicGeometry`. Zero hits.
4. LeanSearch: `Proj of section rings of two invertible sheaves with mutually refining
   nonvanishing opens are isomorphic near the canonical images`. Eight hits on
   structure-sheaf basic-open localization, open-immersion section isomorphisms,
   the union sheaf condition and projective structure-sheaf sections. None states the
   required comparison.
5. Source `rg` of `lean/WeilConjectures` and `lean/Sheaf` for section-ring base/zero/
   canonical maps, cofinal section opens and Proj neighborhoods found the existing
   canonical-map and section-ring coefficient interfaces and unrelated neighborhoods,
   not this theorem. Exact item-id `grep -rn` in `lean/WeilConjectures` found nothing.
   The new declaration name has no existing source or upstream-name-index match.

The Stacks source was read locally in `literature/stacks-project/properties.tex`,
labels `lemma-invert-s-sections` and `lemma-map-into-proj`. As the accepted node itself
says, 01PW does not state the neighborhood comparison verbatim; the comparison follows
its localization isomorphism by the seven-step chart-gluing proof, which is retained.
No new node, dependency repair or statement correction was necessary. No
STATEMENT-DISPUTED issue remains.

Validation: scompile.py compiled the delivered file both as the sandbox module and
under its intended library module name, in 2.8 and 2.7 seconds respectively, with no
errors or warnings. The dry-run and delivery results are recorded by the wrapper.

## Second reading by Q93

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
