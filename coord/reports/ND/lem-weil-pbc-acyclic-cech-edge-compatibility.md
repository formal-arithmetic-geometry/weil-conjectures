## Worker report

The item is stated in `Sheaf.CategoryTheory.AcyclicCechEdgeCompatibility`, with three
sorry-only theorem declarations: `CategoryTheory.exists_acyclicCechEdge`,
`CategoryTheory.acyclicCechEdge_siteChange`, and
`CategoryTheory.acyclicCechEdge_forgetModules`. Nothing is proved. The item statement,
proof, proof dependencies, and source are unchanged. Its statement dependencies gain the
new normalization definition described below.

Sources read: `literature/stacks-project/sites-cohomology.tex`, the complete construction
and proof of `lemma-cech-cohomology` (03AX), the acyclic spectral-sequence application
03F7, and the statement and universal-delta-functor argument of
`lemma-cohomology-modules-abelian-agree` (03FD). The original node's ten detailed proof
steps and their named dependencies are reproduced in the appropriate declaration
docstrings. The three theorem signatures together render the node's three paragraphs.

Hypotheses and clauses:

- Small sites are `C D : Type u` with `SmallCategory`, and `J K : Precoverage` with
  `HasIsos`, `IsStableUnderComposition`, `IsStableUnderBaseChange`, and `HasPullbacks`,
  exactly the covering presentation prescribed by the sites dependency. The topology
  for sheaves is `J.toGrothendieck`. `hU : IsTerminal U` and `huU` specify the final
  objects. There is no assumption of all finite products in either category.
- A finite covering is `T : Type u`, `[Finite T]`, `f`, `hom`, and
  `hcover : Presieve.ofArrows f hom ∈ J U`. The chosen products are the existing
  `S : SiteCechComplex f hom`. Tuples are `Fin (p + 1) → T`, including repeated indices.
- Abelian coefficients are `Sheaf J.toGrothendieck AddCommGrpCat`. Evaluation is
  `sheafToPresheaf ... ⋙ (evaluation ...).obj (op V)`. Its `rightDerived r` is the
  source's definition of cohomology at V. Thus `hA`, and `hB` on the second site,
  say exactly that every positive derived evaluation at every nonempty tuple is zero.
  `IsZero` is on an abelian-group object, not on a bare type.
- `exists_acyclicCechEdge` produces exactly one family `e A hA q`, with `q : ℕ`,
  normalized for every injective resolution and `IsIso` in every degree. The predicate
  `S.IsNormalizedEdge` includes existence of the two prescribed augmentation maps,
  `QuasiIso alpha`, and the equation
  `e ≫ isoRightDerivedObj.hom ≫ homologyMap alpha q = homologyMap beta q`.
  This is precisely beta followed by the inverse of alpha, transported back from the
  resolution. Quantification over every resolution and uniqueness give resolution
  independence without choosing data from a sorried existence theorem.
- Additive coefficient naturality is the second conjunct of the first theorem,
  quantified over every `g : A ⟶ B` with both acyclicity witnesses. The left side is
  `S.cohomologyFunctor.map g.hom ≫ e B hB q`; the right side is the edge followed by
  the right-derived evaluation map of g. A sheaf morphism here is merely an additive
  natural transformation. No coefficient ring, linearity, or semilinearity assumption
  is imposed.
- In `acyclicCechEdge_siteChange`, `hc` and `hp` are the two Stacks continuity conditions
  on coverings and their pullbacks; `u.IsContinuous` supplies the existing sheaf
  pushforward. Preservation of finite limits and colimits by the set-valued
  `sheafPullback` is exactly the recorded morphism-of-sites condition. `huU` expresses
  preservation of the final object. The isomorphisms `c p t` and equations `hcpr`
  express preservation of the chosen tuple products. The mapped family is a covering
  by `hc` applied to `hcover`; no separate stronger covering hypothesis is added.
- The map `h : A ⟶ u.sheafPushforwardContinuous.obj B` is the additive sheaf map in the
  node. For *every* pair of injective resolutions, the site theorem asserts existence
  of an augmentation-preserving adjoint lift v. It then quantifies over every such v.
  The produced chain map w is fixed in every degree by
  `w.f n = (v.f n).hom.app (op U)`. Consequently the transported map
  `I.isoRightDerivedObj.hom ≫ homologyMap w q ≫ L.isoRightDerivedObj.inv`
  is the node's canonical h_H, computed by the lift described in its proof step 6.
  It is not a free parameter standing in for the canonical map.
- The produced `hC` is fixed on every section of every tuple by
  `B.obj.map (c n t).inv.op (h.hom.app ... (s t))`. This is exactly the sectionwise
  map h_C after the canonical product identifications. The final equation is
  `eA ≫ h_H = homologyMap hC q ≫ eB`, in Lean's left-to-right composition order.
  Since this holds for every resolution and every augmentation-preserving lift, no
  arbitrary resolution choice enters the square.
- The module clause uses the existing `SheafOfModules R` and `SheafOfModules.toSheaf R`.
  Right-derived evaluation has **module sheaves as its source category**, so its
  resolutions are injective module resolutions, not injective abelian resolutions.
  Its output is an abelian group: evaluation is followed by forgetting scalar
  multiplication. This is the underlying group of module-valued derived evaluation,
  since forgetting modules to abelian groups is exact. No new cohomology is defined.
- Module injectives are supplied without an extra hypothesis: the existing upstream
  `SheafOfModules.isGrothendieckAbelian` is registered globally as an instance in the
  module, and Mathlib's Grothendieck enough-injectives instance applies. No local
  notation, local instance, or new private category is introduced.
- The family `c q` in `acyclicCechEdge_forgetModules` is a natural isomorphism from
  module-derived sections to underlying-abelian-derived sections. Its first conjunct
  makes it the identity on degree-zero sections, using `toRightDerivedZero`.
  Its second conjunct supplies universal delta-functors G and H with exactly these
  functors (via natural isomorphisms g and h), and the unique delta-functor morphism
  realizing c. The following conjunct specifies c on *every* strict comparison from
  a forgotten injective module resolution to an abelian injective resolution, by the
  induced section-cohomology map. This also pins its canonical resolution normalization.
- Finally, `hM` and `hA` impose both module and underlying-abelian tuple acyclicity.
  For each q and normalized abelian edge eA, the last conjunct produces the unique
  normalized module edge eM, asserts `IsIso eM`, and states
  `eM ≫ (c q).hom.app M = eA`. Both edges have the same existing underlying section
  Čech complex as domain. Thus the identification of the Čech complexes is literally
  the identity; it is not an additional arbitrary comparison map.

Dependency declarations used:

- `Sheaf.CategoryTheory.SiteCechComplex`: `CategoryTheory.SiteCechComplex`, its `W`,
  `pr`, `complex`, `cochainsMap`, `complexFunctor`, `cohomologyFunctor`.
- `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`: existing sites/sheaves framework;
  the node's cohomology is stated via its defining right-derived evaluation. The landed
  `Sheaf.CategoryTheory.Sites.CohomologyRightDerivedSections` theorem
  `CategoryTheory.Sheaf.nonempty_cohomologyPresheafFunctor_eval_iso_rightDerived`
  identifies this with the recorded `Sheaf.H'` form, naturally in coefficients.
- `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`:
  `CategoryTheory.InjectiveResolution`, `cocomplex`, `ι`.
- `Mathlib.CategoryTheory.Abelian.RightDerived`: `Functor.rightDerived`,
  `InjectiveResolution.isoRightDerivedObj`, and `Functor.toRightDerivedZero`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf`: `SheafOfModules`, `toSheaf`;
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian` provides its abelian instance.
  The upstream `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`
  provides the actual small-site Grothendieck theorem used for injectives.
- `Mathlib.Algebra.Homology.HomologicalBicomplex` and `TotalComplex`:
  `HomologicalComplex₂.flip`, `total`, and `ιTotal`. These are the actual declarations
  in the `def-sp-double-complex-total` record. Its recorded Sheaf module is imported,
  and the upstream natural-number total instance gives finite diagonals and the same
  signs without any boundedness assumption on Čech degree.
- `Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor` and its public delta-functor
  module: `CohomologicalDeltaFunctor`, `Hom`, `IsUniversal`. All available recorded
  proof-dependency modules are imported for stage 3. The only unstated proof dependency
  is `lem-weil-pbc-ring-sheaves-grothendieck`; its notion is already supplied by the
  upstream theorem just named. No dependency module is needed.

Edge cases checked before stating: degree zero is included (`q : ℕ`), zero coefficients
are allowed, no nonzero/characteristic condition is present, empty covering index types
are allowed (`Finite`, not `Nonempty`), and every tuple has positive length while all
Čech degrees are present. Empty products are the existing dependent-function abelian
groups. Repeated covering indices are retained. Each total diagonal has n+1 summands
regardless of whether the complex is bounded above. The site and coefficients share a
universe containing their objects, morphisms, and covering indices, as prescribed by the
sites dependency; both sites are otherwise arbitrary. Neither forgetting injectives nor
exactness of tensoring with the ring sheaf is assumed.

Searches made using msearch.py (logged in searches.jsonl): LeanSearch query
`Cech cohomology acyclic covering canonical edge naturality injective resolution augmentation`
returned service unavailable (Internal Server Error), not a negative mathematical result.
LeanFinder query `Cech cohomology acyclic cover edge comparison compatible change of sites forgetting modules`
returned eight Mayer–Vietoris/sheaf-condition results, none stating this normalized edge.
Loogle query `"InjectiveResolution", "isoRightDerivedObj"` returned five resolution
identification/naturality declarations, which are reused. Mathlib grep
`cech.*(edge|augmentation)|augmentation.*cech` in CategoryTheory returned zero hits.
Source searches by the exact item ID returned none. Source and Sheaf rg searches for
`acyclic|Cech|canonical.*edge|site change|Cech.*edge` found the existing complex and
specialized scheme/open-cover comparisons, not this general-site theorem. A further
`resolutionDoubleComplex|IsNormalizedEdge|structure Augmentations` search found no
preexisting general-site normalization declaration. The relevant existing declarations
were read, including their full signatures and docstrings.

Validation: the two delivery files have compiled together on the server in dependency
order, separately, with no errors or warnings, nice 19, two threads, 60 seconds per file.
The theorem module uses a declaration-scoped heartbeat budget for the module comparison;
the final compile took approximately eight seconds. No local compiler or lake command
was run. No source checkout or live library was edited. No statement dispute or correction.

## New nodes

`def-weil-pbc-site-cech-edge-normalization` defines only the missing normalization
notion, not the acyclic-edge assertion. Its module
`Sheaf.CategoryTheory.SiteCechEdgeNormalization` constructs the termwise bicomplex from
existing functors, records the actual two axis formulas in `Augmentations`, and defines
`IsNormalizedEdge` by quantification over all resolutions. There are no sorrys or chosen
objects extracted from sorried existence in this definition module. Its source is the
two augmentation maps of Stacks 03AX. It works for the two coefficient categories needed
by the item without redefining sites, Čech complexes, module sheaves, totalization,
cohomology, or injective resolutions.

DAG searches covered the whole node tree for Cech edge/augmentation and the blueprint
searches `Cech augmentation` (zero) and `Cech` (nine imported nodes, read for relevance).
`def-sc-cech-complex-augmentations` and `def-sc-module-cech-comparison` concern scheme
open covers, and `def-pbc-etale-additive-cech-normalization` concerns the single fixed
lifted additive structure sheaf; none gives the general-site construction on chosen
`SiteCechComplex` products. `CechResolutionDoubleComplex` additionally assumes finite
wide pullbacks. The three kinds of Mathlib searches above apply also to this missing
normalization notion and are recorded verbatim by query in the new node. Existing
Mathlib total and resolution operations are reused; no duplicate of a usable notion is
introduced. The blueprint ancestry command returned
`lemma-weil-pbc-smooth-curve-artin-schreier`, and the new node records its specified final
proof paragraph through this item and `lem-weil-pbc-coherent-frobenius-comparison`.

## Second reading by ND

Independent reading of the node and both delivery modules, against the full proof of
Stacks `lemma-cech-cohomology` (03AX), `lemma-cech-spectral-sequence-application`
(03F7), `lemma-injective-module-trivial-cech` (03FC), and the universal-delta-functor
argument in `lemma-cohomology-modules-abelian-agree` (03FD). The source assumes a
site, and in the last clause a sheaf of rings; it does not assume a field,
Noetherianity, nonempty cover, or preservation of injectives by forgetting.

Object/hypothesis/conclusion inventory and verdicts:

1. Small sites C and D: `C D : Type u`, `SmallCategory`, and `Precoverage` with
   `HasIsos`, `IsStableUnderComposition`, `IsStableUnderBaseChange`, `HasPullbacks`.
   These are exactly the recorded sites dependency's covering presentation. Pass.
2. Final objects: `U`, `hU : IsTerminal U`, and, for change of sites,
   `huU : IsTerminal (u.obj U)`. Evaluation at these objects computes global
   sections. Pass.
3. Finite covering: `T : Type u`, `Finite T`, `f`, `hom`, and `hcover`.
   `S : SiteCechComplex f hom` supplies the chosen tuple products, rather than
   imposing all finite products on the site. Its actual structure has `universal`,
   `W_zero`, `pr_zero`, and compatible index maps. Pass.
4. Abelian coefficient and tuple acyclicity: `A : Sheaf ... AddCommGrpCat`,
   `p : ℕ`, `t : Fin (p+1) → T`, `r : ℕ`, `0 < r`, and `IsZero` of
   right-derived evaluation at `S.W p t`. Repeated indices are included. Pass.
5. Canonical edge in all degrees: `exists_acyclicCechEdge` gives a unique family
   `e A hA q` with `IsNormalizedEdge ... q (e A hA q)` and `IsIso`.
   `InjectiveResolution.isoRightDerivedObj` points from derived evaluation to
   cohomology of the evaluated resolution, as used in the normalization equation.
   Pass.
6. Specified normalization: `resolutionDoubleComplex` applies `P ⋙ S.complexFunctor`
   to the resolution and flips the two indices. Thus the first index is Cech
   degree. The existing natural-index total and its `TensorSigns (up ℕ)` instance
   give horizontal sign +1 and vertical sign (-1)^t. `Augmentations.alpha_f`
   restricts to all length-one tuples and includes at (0,n); `beta_f` applies
   `I.ι.f 0` componentwise and includes at (n,0). `IsNormalizedEdge` asserts
   quasi-isomorphism of alpha and `e ≫ resolutionIso.hom ≫ H(alpha) = H(beta)`.
   This is exactly the specified inverse-alpha/beta normalization. Pass.
7. Independence and additive naturality: normalization quantifies over every
   injective resolution. The unique family and the equation for every `g : A ⟶ B`
   assert resolution independence and coefficient naturality without scalar
   linearity. No extra coefficient structure is required. Pass.
8. Morphism of sites: `u`, `hc`, `hp`, `u.IsContinuous`, and preservation of finite
   limits and finite colimits by set-valued `sheafPullback` are exactly the recorded
   dependency's Stacks continuity and exact-inverse-image conventions. `hc` carries
   `hcover` to a covering; `c` and `hcpr` identify all chosen tuple products by
   their projections. Pass.
9. Second coefficient and map: `B`, its separate `hB` acyclicity, and
   `h : A ⟶ u.sheafPushforwardContinuous.obj B`. These are the node's additive
   coefficients and map, with the stipulated direction. Pass.
10. Canonical site cohomology map and square: for arbitrary `I` and `L`, the first
    conjunct supplies an augmentation-preserving lift `v`, and the second quantifies
    over every such lift. `w.f n = (v.f n).hom.app (op U)` fixes the global map;
    the sectionwise formula fixes `hC` using restriction along `(c n t).inv`.
    Conjugating `homologyMap w q` by the two resolution identifications gives h_H.
    The final equality is exactly `eA ≫ h_H = H(hC) ≫ eB`. This uses a computed
    canonical map, not an unconstrained parameter. Pass.
11. Ring and module coefficients: `R : Sheaf ... RingCat` and `SheafOfModules R`
    are the general ringed-site category, with no commutativity assumption. I read
    the current recorded `ringedSiteModules` abbreviation: it is transparently
    `SheafOfModules R`, not a different category. Replaced the direct Mathlib import
    by its recorded `Sheaf.CategoryTheory.RingedSiteModules` import. Pass after repair.
12. Module cohomology and forgetting: right-derived evaluation is taken on
    `SheafOfModules R`, using `SheafOfModules.toSheaf R` only inside the evaluation
    functor. Thus it uses module injective resolutions. The upstream small-site
    `SheafOfModules.isGrothendieckAbelian` supplies injectives; there is no new
    hypothesis that forgetting preserves injectives. Pass.
13. Canonical comparison: the natural isomorphisms `c q`, the equation with
    `toRightDerivedZero`, and the equation for every strict resolution lift `k`
    identify module cohomology with abelian cohomology, with identity in degree zero.
    Found a mismatch in the delta-functor conjunct: its old `∃! t` quantified
    uniqueness only among maps already prescribed in every degree. Changed it to
    existence of `t` realizing all `(c q).hom`, and uniqueness among every `t'`
    with the same degree-zero component. This now explicitly renders the node's
    unique extension of the identity on sections. Pass after repair.
14. Module edge square: `hM` and `hA` are both required tuple acyclicity assumptions.
    For every normalized `eA` and every `q`, the final unique `eM` is normalized,
    invertible, and satisfies `eM ≫ (c q).hom.app M = eA`. Both source complexes
    are literally the same underlying section Cech complex. Pass.

Edge cases: `T` may be empty, including an empty covering when the site permits it;
no `Nonempty T` was introduced. The dependent function groups then are trivial.
Zero sheaves and zero modules are allowed. `q = 0` is included, and the comparison
is explicitly the identity on sections. No characteristic or nonzero-ring condition
is present. Empty schemes are included through their sites; nothing imposes points.
All universe variables are bound. The single site/coefficient universe is the recorded
small-site convention; enlarging it includes sites and coefficient values of any
specified sizes. Finite index types can be represented in that universe. Each total
diagonal is finite independently of boundedness above in Cech degree.

Independent searches: LeanFinder query `Leray theorem Cech resolution comparison
natural under coefficient forgetting and change of site` found eight plus-construction
and cover-lifting naturality results, not this assertion. Loogle query
`"homologyMap", "rightDerived"` found zero hits. LeanSearch query `Acyclic covering
comparison from Cech cohomology to derived sections respects scalar restriction`
was unavailable (Internal Server Error), not a negative result. These searches are
logged by msearch.py. Grep with `cech.*(augmentation|comparison|edge)|leray.*cover`
across Mathlib CategoryTheory, upstream WeilConjectures, and project Sheaf found
specialized open-cover/scheme comparisons and the finite-wide-pullback construction.
I opened `InjectiveCechTotalSections`, `ModuleCechComparison`, and
`EtaleAdditiveCechNormalization`: the first requires `HasFiniteWidePullbacks`, the
second is for scheme open covers with module-valued coordinates, and the third fixes
the lifted additive structure sheaf. None supplies the general chosen-product site
normalization or the three squares here. A separate exact-name search for
`resolutionDoubleComplex|IsNormalizedEdge|structure Augmentations` found no prior
project/upstream/Mathlib declaration. The DAG's `def-sc-cech-complex-augmentations`
and `def-pbc-etale-additive-cech-normalization` were read against the proposed new
node: both are specialized as just described, so neither replaces it.

New-node reading (H12): `def-weil-pbc-site-cech-edge-normalization` describes the
termwise double complex and the two actual axis maps in 03AX. Its generalized
additive coefficient category packages the same construction without asserting
existence of the augmentations for arbitrary presheaves. Its normalization predicate
requires their existence and invertibility of alpha. All new-node fields, cited
notions, source, ancestry, empty proof lists, search records, and Lean record were
checked. It constructs actual double-complex data and predicates; no data are chosen
from a sorried existence theorem. No dependency module or statement correction is
needed. No unit statement or natural-language node statement changed.

H5/H6/H8/H9: only the three public theorem proofs are `sorry`; the normalization
module has none. The declaration docstrings identify their own blueprint and sources;
the theorem docstrings carry all ten DAG proof steps with their named dependencies.
No private definition, file-local notation, local instance, or unbound variable was
introduced. The primary node signature still agrees verbatim with the file.

Validation after repairs: scompile.py compiled both delivered modules separately on
the server, also building the recorded ringed-site import in the private overlay,
with nice 19, two threads, and a 60-second per-file limit. Times were 1.3 seconds
for normalization, 0.9 seconds for the imported ringed-site module, and 8.2 seconds
for compatibility. No errors or warnings. No local compiler or global build was run.
