## Worker report

The item states Stacks Project, sites-cohomology.tex, Tag 08FX(1),
`lemma-finite-cohomology`, for arbitrary commutative ringed sites. The theorem is
`SheafOfModules.isFiniteType_top_homology_of_isMPseudoCoherentOnRingedSite` in
`Sheaf.Algebra.Homology.RingedSitePseudoCoherentTopFiniteType`. Its only proof is `sorry`.
The item's natural-language statement and reviewed proof are unchanged.

Hypothesis and clause correspondence:

- The site is `{C : Type u} [Category.{v} C] {J : GrothendieckTopology C}`.
  Object and morphism universes are independent. The coefficient sheaf is
  `R : Sheaf J CommRingCat.{max u v r}`. Its ordinary ring sheaf is the existing
  `sheafCompose J (forget₂ CommRingCat RingCat)` applied to R, without changing its data.
- Module sheaves are Mathlib's `SheafOfModules`, the very category exported by
  `CategoryTheory.ringedSiteModules`. The base and slice `HasSheafify` and
  `WEqualsLocallyBijective` instances make these categories abelian. They express the
  standing size/sheafification conventions of the recorded module category, not
  coherence, Noetherianity, quasi-coherence or a geometric restriction on the site.
- `HasDerivedCategory.{w}` for the base and `HasDerivedCategory.{w'}` for each slice
  express the chosen localizations. `K : DerivedCategory ...` is unbounded; no bounded
  derived subcategory is used. These two localization universes remain independent.
- The integer is the unrestricted binder `m : ℤ`.
- `hK : IsMPseudoCoherentOnRingedSite.{u, v, r, w, w'} R m K` is precisely the local
  approximation condition stated in the item. Unfolding the existing definition gives
  `∀ U, ∃ S : Sieve U, S ∈ J U ∧ ...`; for every arrow `f : V ⟶ U` in S it gives
  a cochain complex P on the ringed slice C/V, a finite interval of nonzero terms,
  and `Nonempty (StrictPerfectCoefficientPackageOnSite ... P)`. That existing package
  gives a finite rank and maps `P.X i → O^N → P.X i` with composite identity in each
  degree. It imposes no chain-map splitting. The morphism is
  `α : DerivedCategory.Q.obj P ⟶ ringedSiteDerivedRestrictionOfUniverses ... V K`.
  Its cohomology maps satisfy `∀ i, m < i → IsIso ...` and `Epi ...` at m.
  Thus it is not an arbitrary perfect object, a ring-level approximation or a
  scheme-level notion. The bounds and ranks are inside the cover quantifiers.
- `hvan : ∀ i : ℤ, m < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj K)`
  renders exactly the assumed vanishing above m, with no assertion at m or below it.
- The conclusion is Mathlib's
  `IsFiniteType ((DerivedCategory.homologyFunctor _ m).obj K)`.
  I read Generators.lean:44–48, 95–96, 113–144: this is local generating-section data
  over a family covering the terminal sheaf, with finite index type of generators
  on every member and an epimorphism from the free module sheaf. A family covering
  the terminal sheaf covers every site object after refinement; finite free sheaves
  and their quotient maps restrict to the resulting slice. Conversely covers on every
  object give that global local-generator family by taking all covering members.
  Hence this is exactly finite type on covers of every object, also when C has no
  final object. It asserts no finite presentation or coherence condition.

Declarations read and reused:

- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`:
  transparent abbreviation of Mathlib's module-sheaf category, with its abelian instance.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`; and `.HomologySequence`,
  `DerivedCategory.homologyFunctor` and `homologyFunctorFactors`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`,
  `SheafOfModules.overFunctor`, `.over`, `.overMap`, `.overFunctorMap`:
  the localized site and actual module restriction, not an arbitrary map.
- `Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses`,
  `CategoryTheory.ringedSiteDerivedRestrictionOfUniverses`: restrict the canonical
  localization representative termwise and apply the slice localization.
- `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses` reexports
  `SheafOfModules.StrictPerfectCoefficientPackageOnSite` from
  `Sheaf.Paper.StrictPerfectPackageOnSite`. I read the full package, including the
  degreewise ranks, inclusion, retraction and splitting equation, and the recorded
  `StrictPerfectCoefficientRepresentationOfUniverses` signature and docstring.
- Proof imports are `Sheaf.Algebra.Homology.SitePerfectModelRestriction`
  (`SheafOfModules.overFunctor_exact_ofUniverses`) and
  `Sheaf.Algebra.Homology.SitePerfectUpperModel`
  (`SheafOfModules.exists_strictPerfect_upper_model`). The latter is applied to the
  strictly perfect approximation, not to K. The theorem docstring preserves all
  three reviewed proof steps. Its published upper-model interface uses coefficient
  size max u v; the identical proof at max u v r follows by universe transport or
  generalizing that helper during stage 3, without imposing r ≤ max u v here.

Sources and edge cases: I read the local Stacks definitions `definition-strictly-perfect`
(terms are finite-free retracts), `definition-pseudo-coherent` (08FT), its following
independence-of-representative lemma (derived local maps), and `lemma-finite-cohomology`
(08FX), including the cancellation proof of (1). I also read the current blueprint
`latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and its
`sk-thm-sf-ctf-stability-direct-images.proof.md`; this node is the existing Stacks
prerequisite on that route, not the unit's own statement. No statement correction
is needed. Rank zero, the zero complex, the zero ring, negative m, an empty site,
and empty covering sieves allowed by the topology are all retained. No `Nonempty C`,
final object, global upper/lower bound, positive rank or inequality a ≤ b is imposed.
With a > b, the displayed boundedness simply forces all terms zero, as it should.
A noncoherent ring is allowed, and the conclusion remains finite type rather than
finite presentation.

Searches (all run through the prescribed msearch.py, with results in searches.jsonl):

- LeanFinder, "Top nonzero cohomology of an m pseudo coherent complex on a ringed site
  is a finite type sheaf of modules": 8 hits, headed by `SheafOfModules.IsFiniteType`;
  no approximation/cohomology theorem.
- Loogle, `SheafOfModules.IsFiniteType`: 4 hits, the exact conclusion predicate,
  its constructor/local generators projection and finite-presentation instance.
- Grep of Mathlib, `pseudo.?coher|IsMPseudo|finite_homology`: 0 hits.
- LeanSearch, "An m pseudo coherent derived object on a ringed site locally admits
  strictly perfect approximations": 8 hits about quasicoherent sheaf presentations
  and `HasDerivedCategory.standard`; none defines the approximation condition.
- LeanFinder, "m pseudo coherent complexes of sheaves of modules on an arbitrary
  ringed site": 8 hits about quasicoherent sheaf presentations; no such definition.
- The original searches of `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` did not reveal the concurrently delivered definition.
  The repair search now finds and reuses `IsMPseudoCoherentOnRingedSite` in
  `Sheaf.Algebra.Homology.RingedSitePseudoCoherent`; no theorem matching the item was found. The ring
  theorem `DerivedCategory.finite_homology_of_isMPseudoCoherent` concerns ordinary
  modules; I read its ring approximation definition and did not reuse it for sites.
  The recorded scheme definition `Scheme.IsMPseudoCoherent`, its all-m analogue,
  and the algebraic-space definition have their respective geometric inputs and
  do not define the arbitrary-site notion. Searching the item's id found only
  docstring references in its existing consumers.
- The original DAG search found the item and triangle theorem. The current DAG
  additionally contains the landed definition owner
  `def-sfb-ringed-site-pseudocoherent-complex`, which the repaired item cites.
  `tools/blueprint_refs.py search 'pseudo-coherent'` returned 0 nodes; the broader
  search 'pseudo' returned only an unrelated filtered two-colimit model.
  `ancestor` returned the item's existing null blueprint ancestor, retained in the
  original proposed node; that proposed node is now removed.

## Repair of returned head 67ba64582794

The return has one point: `SheafOfModules.IsMPseudoCoherentOnRingedSite` duplicates
an existing declaration in `Sheaf.Algebra.Homology.RingedSitePseudoCoherent`.
I read that entire current module locally and through `scompile.py --source`, and
read its owning node `def-sfb-ringed-site-pseudocoherent-complex` including its Lean
record and source. The definition agrees clause by clause with the removed one:
same independent u/v/r/w/w' universes and sheafification assumptions, commutative
ring sheaf, every site object, covering sieve, bounded cochain complex on each
slice, existing finite-free splitting package, canonical derived restriction,
cohomology isomorphisms above m and an epimorphism at m. Its `ringedSiteModules`
is the existing transparent abbreviation for `SheafOfModules`. Bound-variable
names and explicit versus inferred universe arguments do not change the notion.

The repaired theorem publicly imports `Sheaf.Algebra.Homology.RingedSitePseudoCoherent`
and uses that existing declaration under its original name. Its full signature,
proof docstring and sole sorry proof are unchanged from the returned delivery.
I removed `RingedSiteMPseudoCoherent.lean` and the proposed node
`def-sfb-ringed-site-m-pseudocoherent` from the sandbox packet, and replaced that
stmt_dep with the landed owner `def-sfb-ringed-site-pseudocoherent-complex`.
There are no new nodes or dependency modules. The item node was refreshed from
current main; only its lean record and added stmt_dep differ. The delivery wrapper
rebases the packet on current main. No rename or replacement definition is used.
The original source statement, all hypotheses, finite-type conclusion and edge
cases described above are unchanged.

Validation of the repair: scompile.py compiled the single delivered module against
the live published library with exit code 0 and no warnings or errors. This checks
that the unchanged theorem signature elaborates using the imported existing
definition and its exact universe interface.

## Second reading by Q100

Independent reading by the maintainer's reviewer (NT-cc), replacing the author's
self-audit section. The node, Stacks 08FX(1), the owner definition and the Lean were
read clause by clause.

1. Site with a sheaf of commutative rings: `{C : Type u} [Category.{v} C] {J}`,
   `R : Sheaf J CommRingCat.{max u v r}`, ring sheaf via `sheafCompose (forget₂ ..)`.
   Sheafification / `WEqualsLocallyBijective` on J and every `J.over U` are the same
   standing instances as the owner `def-sfb-ringed-site-pseudocoherent-complex`. Exact.
2. Unbounded derived category: `HasDerivedCategory.{w}` base, `.{w'}` slices,
   `K : DerivedCategory (SheafOfModules ..)`; no boundedness. Exact.
3. `m`-pseudo-coherence: `IsMPseudoCoherentOnRingedSite.{u, v, r, w, w'} R m K`
   (side-live `Sheaf.Algebra.Homology.RingedSitePseudoCoherent`, listed in the owner's
   `lean.declarations`): ∀ U, covering sieve, ∀ f : V ⟶ U in it, bounded P on C/V with
   `StrictPerfectCoefficientPackageOnSite` (degreewise finite-free retract, no chain
   splitting) and α : Q P ⟶ K|_V by the canonical derived restriction, H^j(α) iso for
   j > m, epi at m. Equals the node's inline definition. The owner is now cited in
   stmt_deps (added, statement text unchanged; the owner node is byte-identical to live).
4. `H^i(K)=0` for `i>m`: `hvan : ∀ i, m < i → IsZero (homologyFunctor i K)`. Exact.
5. Conclusion: Mathlib `SheafOfModules.IsFiniteType (H^m K)` = local generators over a
   family with `J.CoversTop`, finitely many sections on each member, epi from free
   module. CoversTop ⇔ every object is covered by the family's sieve, so this is
   "on a covering of every site object a surjection from a finite free module". Not
   finite presentation; no coherence assumption. Exact.

Edge cases: m arbitrary in ℤ (negative included), zero ring, zero complex/rank 0,
empty C, empty covering sieves; all admitted; no Nonempty, final object or extra
universe equality. Universe argument order of the owner def is u, v, r, w, w' (from
occurrence C, morphisms, R, base and slice derived categories), matching the call.

Records: item statement/title/source/proof unchanged vs live; only `lean` set and
stmt_dep owner added. `lean.statement` equals the file signature. Module docstring
and theorem docstring carry Tag 08FX(1) and `(blueprint: ...)`; the docstring carries
the three proof steps. Proof is `sorry` only. No duplicate: the removed
`RingedSiteMPseudoCoherent` copy is gone; Mathlib has no pseudo-coherence; ring and
scheme variants are different notions. Imported proof helpers
`SitePerfectModelRestriction` / `SitePerfectUpperModel` exist in side-live.
No compile repeated (per maintainer instruction); the worker's scompile of the
module is recorded above. Verdict: correct.
