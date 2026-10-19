## What changed

Validation (2026-10-19): the retained lcompile.py --all result compiled all three
modules cleanly against the current server build: CompactificationRefinementIdentity
in 2.4 s, NonrationalCompositionSeed in 2.9 s, and the assigned module in 4.2 s.
The fresh required dry run built commit 715b95e682 and passed preflight with
review class CODEX. The tool deferred the parent module's axiom probe after a
60-second timeout, explicitly saying the merge reruns it; this probe is not counted
as passed. Earlier saved dry runs also passed, with an identity-helper probe
sometimes deferred for lack of a server answer. On resumption, the interrupted
delivery log had no DELIVERED result and no delivery process remained; the fresh
dry run completed before submitting this packet.

The retained implementation was checked against the current item source, dependency
signatures, blueprint proof and DAG. The item's theorem signature (including every
binder and universe) and public imports are unchanged. No sorry occurs in the delivered
Lean sources.

The parent theorem is proved from one composition seed and identity normalization of the actual refinement component, together with the existing exceptional-adjoint and compactification-cocycle declarations. Its signature and all definitions are unchanged. A private generic categorical lemma performs transport from one seed triple to every triple, using naturality and the three cocycle equations. Full-subcategory inclusions lift the ambient comparisons without choosing new underlying maps.

## Proved and sorry left

Closed: AlgebraicGeometry.ProEtale.CondensedRing.exists_nonrationalLocalizingLowerShriekComposition (one original hole).

Proved new helper: AlgebraicGeometry.ProEtale.CondensedRing.exists_nonrationalLocalizingLowerShriekCompositionSeed (lem-sfb-nonrational-composition-seed). Its proof constructs the three compactifications, proves naturality of the normalized interchange, composes the proper and open isomorphisms, and lifts to the full localizing subcategory. This adds no hole.

Proved new helper: AlgebraicGeometry.ProEtale.CondensedRing.compactificationRefinementComponent_id (lem-sfb-compactification-refinement-component-id). The existing dense-refinement normalization supplies the open identity equation. A complete private categorical proof of the derived unit law then cancels it against the derived compositor. The helper is stated only for the dense compactifications in the standing scheme/coefficient setting, exactly as used by the parent.

Totals: one original hole closed, zero holes added or left in any delivered module. The two new nodes have complete proofs from the existing declarations; neither is a remaining split-off obligation. Transitive sorries in those existing declarations remain for their assigned items.

## No longer needed

Removed proof imports from the parent module:

- Sheaf.Algebra.Homology.KInjectiveRestrictLocalized
- Sheaf.AlgebraicGeometry.ProEtaleInverseImage
- Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
- Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
- Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
- Sheaf.Compactification.BoundaryRefinement
- Sheaf.Compactification.CommonDenseRefinement
- Sheaf.Compactification.DenseRefinementMorphisms
- Sheaf.Paper.CartesianCoefficients
- Sheaf.Paper.CompactificationLocalizing
- Sheaf.Paper.CompactificationRefinementLocalizing
- Sheaf.Paper.LocalizeRingedSiteMorphismGeneral
- Sheaf.Paper.OpenImmersionLocalizing
- Sheaf.Paper.ProEtaleProperOpenInterchange
- WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
- WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
- WeilConjectures.Compactification.Dense
- WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
- WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
- WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs

The parent no longer needs the independent auxiliary/source/target refinement arguments of old steps 6–8. Their role is replaced by transport through the existing cocycle: the statement asks for a compatible family, and a seed transported through that cocycle gives one. Accordingly the parent no longer directly uses det-sf-comp-coherence-refinement, det-nagata-refinement-common-dense, det-nagata-refinement-morphisms, det-sf-comp-composition-interchange, det-proper-image-localizing-open, det-sf-comp-coherence-single, or the old derived/open comparison dependencies. These geometric and derived inputs needed to construct the seed remain in that new node's proof dependencies; they are not claimed globally pruned. Public imports are retained. No module is withdrawn. The identity helper's
DAG proof dependencies now name the actual refinement compositor, derived-category
API, and K-injective preservation used in its proof; the separate
lem-weil-pbc-ringed-topoi-derived-pushforward-composition theorem is not used. In particular, the unit-route module `Sheaf.Compactification.BoundaryRefinement` remains in the proof import closure through `Sheaf.Paper.CompactificationCoherenceCocycle` → `Sheaf.Paper.CompactificationRefinementLocalizing` and through `Sheaf.Paper.NonrationalCompositionSeed` → `Sheaf.Paper.ProEtaleProperOpenInterchange`; both latter existing modules publicly import the boundary-refinement module. Dropping its redundant direct parent import bypasses no unit statement or proof step.

Complete list of former direct parent proof dependencies transferred to the seed or made unnecessary by transport:

- sk-thm-nagata-compactification
- lem-weil-pbc-proper-fp-permanence
- sk-def-nagata-sketch-data
- sk-def-sfb-dc-setting
- sk-def-sfb-module-lower-shriek
- sk-prop-sfb-cartesian-coefficients
- lem-weil-pbc-exact-functor-derived-factorization
- lem-weil-pbc-termwise-adjunction-homotopy
- lem-weil-pbc-localization-universal-property
- sk-def-sfb-derived-categories
- sk-def-sfb-module-pushforward-pullback
- lem-weil-pbc-ringed-topoi-derived-pushforward-composition
- def-weil-proetale-inverse-image
- lem-weil-pbc-right-adjoint-preserves-kinjective
- def-sfb-module-lower-star-comp
- def-sfb-module-lower-star
- lem-weil-pbc-localize-ringed-site-morphism
- lem-weil-proetale-weakly-etale-localization
- def-sfb-finite-extension-by-zero-adjunction
- def-sfb-finite-lower-star
- lem-pur-kinjective-restrict-localized
- det-proper-image-localizing-open
- det-sf-comp-composition-interchange
- det-sf-comp-coherence-single
- det-sf-comp-coherence-refinement
- det-nagata-refinement-common-dense
- det-nagata-refinement-morphisms


## Where the brief, the DAG or earlier work was wrong

Earlier attempts recorded delivery-tool worktree capacity and a stalled cycle-graph
check, followed by successful dry runs. This resumption retained the completed zero-hole
proof set and checked it against the current sources and node records. Its initial
validation requests received no answer from the compile server, as recorded above.
No launcher script was modified or bypassed. This resumption also corrected the
identity helper's DAG proof dependencies to match its source-library calculation;
no separate ringed-site derived-composition theorem is invoked.

The old nine-step plan is valid but needlessly checks the construction's compatibility separately in three directions for this existential statement. The cocycle transports any single-triple isomorphism to a compatible family. Its current Lean statement does not explicitly include identity normalization of compactificationRefinementComponent, so that unitor calculation is proved separately using the existing dense-refinement identity clause. No statement is marked disputed. Explicit compactification binder types avoid Lean unfolding nested projections during type inference; the resulting parent checks in seconds. There are no definition or interface changes and no consumer adaptations.

## New nodes

lem-sfb-nonrational-composition-seed (proved): existence for just one triple, without any refinement or compactification-independence assertion; follows old steps 1–5 and is strictly less than the parent's all-triples compatibility claim. Identity maps, two opens, two proper maps, empty source and zero objects have the stated expected composition isomorphisms.

lem-sfb-compactification-refinement-component-id (proved): canonical identity refinement on every ambient unbounded object for dense compactifications in the standing setting. It uses the identity clause of localizingRefinement_coherence, then a categorical derived-compositor unit calculation. Empty schemes and the zero object are included. This is a new helper, so no existing library signature or definition changes and no change records are needed.

The seed proof directly uses the existing exact derived adjunction and compositor APIs; it does not separately reprove the old plan’s K-injective, localization, ringed-site restriction, or associativity calculations. Those dependencies remain behind the APIs that construct them, and are not claimed globally pruned.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
