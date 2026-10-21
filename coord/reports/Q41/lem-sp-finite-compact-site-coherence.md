## Worker report

Statement delivery for `lem-sp-finite-compact-site-coherence`. The module is
`Sheaf.Paper.FiniteCompactSiteCoherence`, namespace `AlgebraicGeometry.ProEtale`.
It has eight real map/isomorphism definitions and eleven theorems, each with proof
`sorry`. No existing source or dependency node is edited. The statement, proof,
proof_deps and source of the item are unchanged.

Source read: `literature/stacks-project/more-etale.tex`, Tags 0F7I
(`lemma-shriek-well-defined`, including its non-Cartesian comparison), 0F7J
(`lemma-shriek-composition`, tower formula and five-square independence argument),
and 0F7K (`lemma-pseudo-functor`, associativity). The item's eight proof steps are
expanded in the docstring of `finiteCompactSiteCoherence`; individual clauses have
their corresponding proof plans as well. This is the site's stated deduction from
the recorded refinement and proper/open site-square dependencies, not an additional
claim that those site squares occur verbatim in Stacks.

Hypotheses and objects, clause by clause:

| Node | Lean |
| --- | --- |
| Any finite commutative ring R | Explicit section binder `(R : Type (u + 1)) [CommRing R] [Finite R]`, captured in each declaration; no nontriviality or coefficient-presentation hypothesis. |
| Schemes | `Scheme.{u}`, the recorded Mathlib notion. |
| All schemes Noetherian in the finite affine-cover sense | `[IsNoetherian X]`, `[IsNoetherian Y]`, `[IsNoetherian Z]`, and `[IsNoetherian W]` for a triple. Mathlib `isNoetherian_iff_of_finite_affine_openCover` identifies this with the node's stated notion. Noetherianity of tower ambients is supplied inside the map definition by the existing named `isNoetherian_of_locallyOfFiniteType` applied to their proper structure maps. It is not an additional theorem hypothesis. |
| Compactifiable separated finite-type maps | Each map has `[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]` and an explicitly supplied `c : Compactification f`. The latter records the open immersion, proper morphism and factorization equality; no chosen compactification or field-existence theorem is assumed. |
| Ordinary constant-R module derived categories | `DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))` and the same construction on `Scheme.ProEt.topology X`. These are the fixed-scalar presentations of the recorded ring-sheaf module categories; `finiteCoefficientEtaleRealization` and `finiteCoefficientRealization` in the dependency provide the canonical equivalences. No condensed/completed or constructible-only category is substituted. |
| E in D+ | Every input is an arbitrary `DerivedCategory.Plus` object. All equations lie in D+ and therefore also in the ordinary unbounded category under its fully faithful inclusion. They do not assert preservation by coefficient extension or preservation of etale origin on arbitrary pro-etale inputs. |
| F_h = Rr_* j_! on each site | The existing `Etale.rightDerivedLowerShriekOfCompactificationPlus` and `ProEtale.rightDerivedLowerShriekOfCompactificationPlus`, whose bodies are exactly the composite of the two specified derived functors. |
| N_T = nu_T^* | Existing `comparisonUpperStar (ModuleCat.{u + 1} R) T`, descended by `mapDerivedCategoryPlus`. |
| C_h = Rr_*(e_j) after d_r(j_!(-)) | Existing `compactSupportSiteComparisonPlus R c`. Its definition uses `fixedComparisonDirectImageMatePlus R c.g` and `properOpenSiteExtensionIso R c.i`, with the functor associators. The former is the specified counit mate. |

Conclusions, clause by clause:

| Node | Lean |
| --- | --- |
| C_h(E) invertible | `finiteCompactSiteComparison_isIso`. The map is already a component of the recorded canonical natural isomorphism, rather than an arbitrary isomorphism between endpoints. |
| Proper refinement with normalized rho | `r : c.Refinement d` means fine c to coarse d; etale rho is `(Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso R r).hom`, and pro rho is `(properTransportRefinementPlus R r E).inv`. Their direction is coarse to fine, exactly as in proof step 3. |
| C_c' N(rho_et) = rho_pro N C_c | `finiteCompactSite_refinement`. Lean uses left-to-right composition, so the displayed equation is `N.map rho_et >> C_fine = C_coarse >> rho_pro`. No Cartesian condition is assumed on r. |
| Every common refinement gives the same comparison | First conjunct of `finiteCompactSite_common_refinement`, quantified over arbitrary b and both refinement legs, equates their computed pro-etale composite with `finiteCompactSiteChangePlus`. Its second conjunct gives the site square with the canonical etale change. |
| Identity refinements and composition of refinements | `finiteCompactSite_refinement_coherence`. |
| Coherence of common-refinement changes | `finiteCompactSite_change_coherence` gives the identity and cocycle equations. |
| The composition is the proper/open paste on a compatible tower | `finiteCompactSiteTowerPlus` uses `properOpenSiteInterchange R T.isPullback.flip` at the etale witness `J_a E`. That map is the dependency's specified open adjunct of inverse transported restriction. Insert `e_a` and its inverse to retain this witness, apply `P_q`, then the named proper direct-image compositor and open-extension compositor, with `T.p_g` and `T.i_q` transports. This definition never references the etale composition arrow or the desired site equation. |
| Arbitrary compactifications of f, g and gf | `finiteCompactSiteCompositionPlus R c d e T E` changes the supplied candidates to T via computed proper/open common-refinement arrows, applies that tower map, and changes back. The intermediate input to the change of d is witnessed by `F_f^et E` and `C_f(E)`. `finiteCompactSiteChangeAtWitness` and `finiteCompactSiteCompositionAtWitness` retain the explicit witness and transport the functor images of that witness, without choosing any unrelated isomorphism. |
| C_gf N(alpha_et) = alpha_pro N F_g(C_f) C_g(F_f E) | `finiteCompactSiteCoherence`, using the existing general `coherenceEtaleCompositor R c d e` for alpha_et and the independently computed map above for alpha_pro. Its equation is precisely the node's second equation in Lean's left-to-right composition order. |
| Computed maps coincide with transport through C | The two displayed site equations and invertible source/target C solve uniquely for rho_pro and alpha_pro. Their exact independently computed maps are used on the right sides; no square commutativity is assumed in the data. |
| Every common refining tower and all choices | `finiteCompactSite_tower_independence`, quantified over arbitrary T and T', with both equality and invertibility of the computed composition. A common refining tower is included among these arbitrary choices. |
| Natural in E | `finiteCompactSite_naturality` states the explicit naturality equations for both computed refinement and composition, for every morphism `a : E -> E'`. Naturality of C itself is built into `compactSupportSiteComparisonPlus`. |
| Identity normalization of C | `finiteCompactSite_identity`, using the proper/direct-image and open-adjunction identity isomorphisms of the actual identity compactification. |
| Identity maps in composition | `finiteCompactSite_composition_units` gives both unit equations for every supplied left/right unit tower, using equality copies of c along `Category.id_comp` and `Category.comp_id`. |
| Associativity | `finiteCompactSite_associativity` permits arbitrary c_f, c_g, c_h, c_fg, c_gh, c_fgh and four independently supplied towers. The second inner input retains the etale witness `F_f^et E` via C_f(E). The left target is copied along `Category.assoc`, retaining precisely the same ambient scheme, open and proper maps. |
| No special coefficients or algebraically closed field | There is no prime, p-adic extension, coefficient quotient, nonzero-ring, field, or algebraic-closedness parameter in any theorem. |

Dependency declarations read and used (full signatures and source docstrings checked):

- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: the `Etale.DerivedCategoryModule` encoding and Mathlib `DerivedCategory.Plus`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `finiteCoefficientRingSheaf`, `FiniteCoefficientModules`, `FiniteCoefficientDerivedCategoryPlus`, `finiteCoefficientEtaleRealization`, `finiteCoefficientRealization`, and `finiteCoefficientComparison` identify the ordinary constant-ring coefficient presentations.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek` and the finite-coefficient pro-etale counterpart: `rightDerivedLowerShriekOfCompactificationPlus` on both sites and their compatibility with the unbounded functors.
- `Sheaf.AlgebraicGeometry.CompactifiableOverField`: its recorded definition clause uses `AlgebraicGeometry.Compactification`/`HasCompactification` from `WeilConjectures.Compactification.Defs`. Those full structures are reused; its additional field-existence theorem is not imposed here.
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`: `openImmersionLowerShriekComparisonUpperStarIso`, `proEtaleOpenExtensionComp`, `openImmersionLowerShriekComparison_coherence`.
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`: `fixedComparisonDirectImageMatePlus` and its invertibility/counit normalization.
- `Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons`: `etaleCompactSupport_refinementComparison_eq` and the upstream refinement/change/composition isomorphisms listed in that node's lean record.
- `Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower`: `exists_compactifiable_compatible_tower` and its `Compactification.Triangle` data, including arbitrary tower refinements.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`; `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` and its finite-generation equivalence.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: `Scheme.proEtaleSiteComparison` and `proEtaleSiteComparisonModules`; the fixed-module inverse image is the existing `comparisonUpperStar`.
- `Sheaf.AlgebraicGeometry.ProperOpenComparison`: `Etale.properOpenIdentification` and `Etale.properOpenComparison`, with their explicit restriction/base-change/component construction and adjunction formula.
- `Sheaf.Paper.RefinementCoefficientMate`: `refinementCoefficientMate`, in particular its site conjunct with `properOpenProEtaleIsoPlus`. The refinement comparison reuses that recorded map.
- `Sheaf.Paper.ProperOpenCoefficientMate`: `properOpenSiteRestrictionInverse`, `properOpenSiteInterchange`, `properOpen_site_mate`, and its naturality. The interchange is built by the open adjunction, as required.

Three already-landed definition owners are added to stmt_deps under the explicit
permission to add landed statement dependencies:
`def-sf-compact-support-site-comparison-construction` for
`compactSupportSiteComparisonPlus` in `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`;
`def-sf-refinement-comparison-isomorphism` for `properTransportRefinementPlus` and
`properTransportDirectImageCongr` in `Sheaf.Paper.RefinementComparisonIsomorphism`;
and `def-pur-chosen-compactification-compositors` solely for its general finite-ring
`coherenceEtaleCompositor` helper in `Sheaf.Paper.CompactSupportSiteCoherence`.
That helper has no field or coefficient-presentation hypothesis; the specialized
purity theorem is not used. All three additions were checked by read-only traversal
of the current DAG and none creates a cycle. This reuses the existing notions
rather than adding duplicate candidate/comparison definitions. All recorded proof
dependency modules, including Mathlib matches, are directly imported as required.
No new DAG node or dependency module is needed.

Edge cases checked before finalizing: the zero finite ring is permitted (there is
no `Nontrivial R`); the zero complex and every lower bound are admitted; empty
schemes and empty opens are permitted; identity open/proper maps are covered by
the explicit units; a refinement need not be Cartesian or dense; all towers and
all common refinements are quantified; a composite is copied only along its
associativity/identity equality, with the same geometric maps. No existence claim
for an arbitrary pro-etale witness or a noncanonical map has been substituted.
Universes: schemes are `Scheme.{u}`, the small sites have object universe u+1 and
morphism universe u, and coefficient modules are in u+1. Any finite coefficient
ring has this presentation after the usual universe lift; no equality between
site object and morphism universes is imposed. The only newly provided instance
data inside a definition is derived from the existing named Noetherian theorem.
All theorem proofs are exactly `by sorry`.

Searches actually run:

- `msearch.py ... leanfinder "Finite ring compact support etale proetale comparison coherent refinement composition"`: 8 unrelated hits (affine transition limits and stability of etaleness), no match.
- `msearch.py ... loogle "rightDerivedLowerShriekOfCompactification, comparisonUpperStar"`: 0 hits, explicitly reporting unknown identifier `rightDerivedLowerShriekOfCompactification` in its Mathlib index.
- `msearch.py ... grep "compact.*[Ss]ite|[Ss]ite.*[Cc]oherence"`: 0 Mathlib hits.
- `rg` on both `lean/WeilConjectures` and `lean/Sheaf` for the item id, compact-support/site coherence and comparison names: found `CanonicalCompactSupportSiteComparison`, `RefinementComparisonIsomorphism`, `ProperOpenCoefficientMate`, and `CompactSupportSiteCoherence`. Read their definitions. The existing final coherence theorem requires `PurityFiniteSetting` and field-over-scheme data, so it is not this arbitrary finite-ring statement. Its general etale compositor helper is reused.
- `rg` on Mathlib Noetherian definitions and the project compactification/refinement/derived-functor modules resolved the exact finite affine-cover condition, refinement orientation, and identity/composition interfaces. `rg` for `finiteCompactSite` in both project source roots and `dag/lean_names_upstream.json` found no declaration-name collision.

No statement dispute or source correction was found. The only elaboration repairs
were to use the existing open compositor in its inverse orientation, transport
open-immersion instances along equality, name the identity functor's category, and
supply ambient Noetherianity from the existing finite-type theorem. No new
hypothesis was added to make the equation elaborate.

Validation: the complete module, with all proof imports and eleven statement
clauses, compiled on the server through scompile.py in both its sandbox and
library-module checks, with no errors or warnings (last results 9.8 s and 10.2 s).
The prescribed delivery dry run and push follow this report.


## Returned-delivery repair

The independent review of immutable head `67a0b64dece2` returned H2/H12 for
citing theorem nodes solely to obtain plain definitions. Replaced
`lem-sf-class-compact-support-comparison` by its already-landed definition owner
`def-sf-compact-support-site-comparison-construction`, whose `lean.declarations`
contains `AlgebraicGeometry.ProEtale.compactSupportSiteComparisonPlus`. Replaced
`lem-pur-compact-support-site-coherence` by the already-landed definition owner
`def-pur-chosen-compactification-compositors`, whose primary declaration is
`AlgebraicGeometry.ProEtale.coherenceEtaleCompositor`. Both owners have
`existing: true`. Kept `def-sf-refinement-comparison-isomorphism`.

Read both owners' statement and Lean records and checked the full definitions
and source docstrings. `compactSupportSiteComparisonPlus` is the explicit
composite of associators, `asIso (fixedComparisonDirectImageMatePlus A c.g)`
and `properOpenSiteExtensionIso A c.i`. `coherenceEtaleCompositor` is the
canonical composite of compactification changes and the chosen etale
compositor. Neither is chosen from the former theorem node's conclusion.
The recorded modules and the imported declarations are unchanged.

The saved packet passed the prescribed initial `deliver2.py --no-push` against
current main (dry-run commit `0ecc433d0c7`). Comparison with the current read
clone found changes only in the authorized `lean` and `stmt_deps` fields.
This repair changes only the two entries of `stmt_deps` and this report; the
Lean module, its eleven statements and eight definitions remain byte-identical
to the saved packet independently accepted on all mathematical points by L.
No statement correction, new node or dependency module is required.

Repair validation (2026-10-21 UTC): `scompile.py Q41
lem-sp-finite-compact-site-coherence` compiled the unchanged complete module
without errors or warnings (sandbox 9.8 s; library module 10.2 s). Read-only
traversal of both statement and proof dependencies found no path from either
replacement definition owner back to this item. Only `lean` and `stmt_deps`
differ from current main; the source, statement and proof plan are preserved.

## Second reading by Q41

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
