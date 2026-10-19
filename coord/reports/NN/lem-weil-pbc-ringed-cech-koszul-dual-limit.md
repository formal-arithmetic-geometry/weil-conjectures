## Worker report

The delivery states `lem-weil-pbc-ringed-cech-koszul-dual-limit` in
`Sheaf.CategoryTheory.RingedCechKoszulDualLimit`. All theorem proofs are `sorry`.
The construction module `Sheaf.CategoryTheory.RingedKoszulSystem` supplies the
missing finite strict Koszul diagram, its actual dual and tensor towers, and the
canonical degree-zero unit. Definitions contain real data, not postponed choices
of a complex or map. Its postponed coherence proofs are named theorems with
source and complete proof docstrings in the new definition node's module.

Hypotheses, clause by clause:

- A small site is `{C : Type u} [SmallCategory C] {J : GrothendieckTopology C}`.
  The coefficient is `O : Sheaf J CommRingCat.{u}`. Modules are exactly
  `SheafOfModules` / `ringedSiteModules`, not modules on an assumed scheme.
- The integer `r : ℕ` and `b : Fin r → (O.obj ⋙ forget CommRingCat).sections`
  are precisely the finite list of global sections. No nonemptiness, regularity,
  Noetherian, or ideal-generation hypothesis is added.
- `HasDerivedCategory.{w}` instances select the size of localization morphisms
  for the original module category, its strict tower category, and all slices.
  They are the recorded abstract-derived-category convention, not restrictions
  on coefficients or geometry. No site universe is identified with a larger one.
- `ringedKoszulFactor` uses Mathlib `HomologicalComplex.double` in degrees 0,1
  with multiplication by `b_i^(m+1)`. `ringedKoszulDiagram` is its ordered total
  tensor diagram. The zero-based index `m` corresponds to the paper's positive
  exponent `m+1`, retaining every stage. Its forward factor maps are `(1,b_i)`;
  tensor functoriality therefore gives multiplication by the subset product.
- `ringedKoszulDualTower` is literally `homComplex(P_m,O[0])` with the actual
  contravariant chain maps. The Hom differential and ordered tensor signs give
  exactly the stated negative-degree factors and inverse maps `(b_i,1)`; this
  equivalence is explained in proof step 1, without replacing the dual by an
  unrelated object or arbitrary inverse diagram.
- `ringedExtendedCech` and its augmentation are reused verbatim. Its owning
  definition constructs the ordered localization tensor, whose subset terms
  are sheafified sectionwise localizations with the alternating differential.
- The first conjunct of `ringed_cech_koszul_dual_limit` is a complex isomorphism
  `alpha : colimit P ≅ C_b`. Its equation with `colimit.desc` is augmentation
  compatibility, with the actual Koszul projection cocone.
- The same conjunct supplies the telescope map `t`, fixes its restriction to
  the unshifted direct sum, and asserts `QuasiIso t`. Thus the degreewise
  filtered colimit represents the homotopy colimit, not merely an unrelated
  derived isomorphism.
- The next conjunct asserts `IsKFlat` of every actual dual complex. This
  guarantees that `Tot(N tensor Q_m)` represents the derived tensor for every
  representative `N`, including unbounded representatives.
- `RingedKoszulLimitPresentation.tensorTower` and `tensorFactors` descend the
  actual functor of strict tower complexes to the derived category, including
  its strict transitions and maps in `N`. This supplies representative
  independence under the specified localization comparisons, rather than
  assuming an arbitrary tower in the derived category.
- `inverseLimit`, `comparison`, `isRightDerived`, and `comparison_isIso`
  specify total right derived inverse limit by its universal property and
  computation on K-injective strict towers. No exactness of products is
  assumed. The strict-tower theorem in the recorded dependencies supplies this
  interface. Its further Roos and pro-zero clauses are not new hypotheses.
- `RingedKoszulCechComparison.theta` is a natural isomorphism of functors on
  the entire unbounded derived category, from the recorded derived internal
  Hom of the actual Cech complex to the strict derived-limit presentation.
  `unit` and `theta_unique` specify the canonical normalized comparison.
  Uniqueness is a specification of the canonical map, not a choice of some
  isomorphism: both sides represent derived completion, so a normalized map
  into a complete object is determined by its composite with the completion
  unit. The existing global extended Cech completion model supplies this
  independent universal-property interpretation (Stacks 099F).
- `ringedKoszulDualUnit` dualizes the actual positive augmentation, using
  evaluation at one. Tensoring it gives the literal degree-zero maps into
  `Tot(N tensor Q_m)`. `ringedKoszulLimitUnit` factors their compatible family
  through the ordinary degreewise inverse limit. `unitOnComplex` then applies
  the total-derived-functor comparison and the specified tensor factorization;
  `unit` transports by the localization representative isomorphism. The
  comparison's `unit` field equates this actual strict unit with `epsilon*`
  composed with `N ≅ RHom(O,N)` from the recorded Cech completion-unit module.
- `slicePresentation U`, `sliceTheta U`, and `slice_unit` give the corresponding
  strict construction on every slice, with the actual restrictions of `b`.
  `sourceRestriction` and `targetRestriction` are natural isomorphisms for
  derived slice restriction. `source_unit` and `target_unit` normalize them;
  `restriction_square` states that theta restricts to the slice theta.
- `furtherTarget` and `further_unit` use the actual derived `overMap` functor
  for every `f : V ⟶ U`. `further_coherence` uses the canonical derived
  `overFunctorMap` composition isomorphism, and states agreement with direct
  restriction to V. The source counterpart is obtained by conjugating this
  equality by `sliceTheta`; `restriction_square` makes this the comparison
  already specified on the root. `target_coherence` also records the general
  normalized naturality equation. These maps are not hypothetical arbitrary
  site transports.
- `empty_identity` asserts invertibility of the strict unit for r=0.
  The positive system is definitionally constant O[0], its dual is O[0]
  under evaluation at one, and C_b is definitionally O[0] with identity
  augmentation. The unit equation then says theta becomes identity under
  these unit/constant-tower identifications.

Dependency declarations read and reused:

- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`.
- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`.
- `def-pc-tensor-complex-sheaves`: `Mathlib.Algebra.Homology.BifunctorShift`, `CochainComplex.mapBifunctor`.
- `def-pur-derived-internal-hom`: `Sheaf.Algebra.Homology.DerivedInternalHom`, `CategoryTheory.derivedInternalHom`.
- `lem-weil-pbc-ringed-strict-tower-homotopy-limit`: `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit`, `CategoryTheory.ringedStrictTowerHomotopyLimit`.

Additional existing notions are the exact `ringedExtendedCech`,
`ringedCechCompletionFunctor`, `ringedCechCompletionUnit`,
`ringedHomUnitEvaluationIso`, `ringedDerivedRestriction`, and the general
`ringedSite_overMap_*` exactness declarations. The latter live in
`Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`; the helpers use
Mathlib's actual `overMap`, `mapDerivedCategory`, and `overFunctorMap`.

Edge cases checked: r=0; a zero section; an invertible section; the zero
coefficient ring; an empty underlying site; arbitrary unbounded N; and
positive exponent 1 at m=0. No flatness assumption on N, exact-products
assumption on sheaves, or boundedness assumption is present. For a zero
section localization is the zero module; for an invertible section the
localization factor is contractible. These agree with the Koszul colimits
and dual towers, including their units.

Searches: `msearch.py` LeanFinder query "Extended Cech complex as colimit of
Koszul complexes and derived Hom as inverse limit of duals" returned eight
unrelated local-cohomology/evaluation/derived-functor declarations; Loogle
`CochainComplex.mapBifunctor, SheafOfModules.free` returned zero hits.
Mathlib grep `Koszul|koszul|extended.*Cech` returned three TODO/unrelated
hits. LeanSearch for strict finite Koszul tensor towers was unavailable
(Internal Server Error), recorded without treating this as a negative result.
`blueprint_refs.py search Koszul` found thirteen blueprint matches; the
existing ring Koszul complex and pro-etale intrinsic completion have different
objects. Direct rg of upstream `WeilConjectures`, project `lean/Sheaf`, and
all DAG nodes found no general finite ringed-site strict Koszul diagram.
Direct searches also found and reused the existing Cech construction and
completion-unit/restriction modules. No duplicate tensor, derived category,
module category, Cech complex, or internal Hom is introduced.

Compilation: both delivered modules passed scompile.py with no errors or
warnings. Delivery preflight is checked by deliver2.py --no-push. No statement
correction or STATEMENT-DISPUTED issue is claimed.

## New nodes

`def-weil-pbc-ringed-koszul-system` defines the finite positive Koszul diagram,
its dual inverse tower, the strict tensor tower as a complex of towers, its
actual degree-zero unit, and the universal-property specifications of its
strict derived-limit presentations. Source: Stacks 0913, 0A0A and 0941.
The searches above distinguish it from the ring-only exterior Koszul complex,
pro-etale adic intrinsic completion, and the existing localization Cech
complex. The helper module reuses the latter's coefficient and complex
notions, and Mathlib's double, tensor, localization and limit constructions.

This worker has not performed or signed the independent second reading.


## Second reading by NN

I independently read the node, both delivery modules, the new definition node,
and the recorded dependency signatures. I also read Stacks more-algebra.tex
`lemma-extended-alternating-Cech-is-colimit-koszul` (0913), sites-cohomology.tex
`lemma-colim-and-lim-of-duals` (0A0A), `lemma-derived-limit-is-ok` (0941),
`lemma-restriction-RHom-to-U` (08JB), and derived.tex `lemma-colim-hocolim`
(0949), including their proofs and surrounding setup. The sources do not
assume regularity, Noetherian coefficients, bounded N, or exact products.
The ring calculation in 0913 is applied sectionwise and then sheafified;
0A0A and 08JB apply to general ringed sites. The exact filtered-colimit
hypothesis in 0949 holds for the module-sheaf category used here.

The statement checklist, with the actual Lean rendering and verdict, is:

1. Small site, topology, commutative coefficient sheaf: `{C : Type u}`,
   `[SmallCategory C]`, `{J : GrothendieckTopology C}`, and
   `O : Sheaf J CommRingCat.{u}`. These are precisely the objects in the
   node; there is no geometric specialization. PASS.
2. Finite global list, including length zero: `r : ℕ` and
   `b : Fin r → (O.obj ⋙ forget CommRingCat).sections`. Global sections
   are compatible families, so a terminal object of the site is not assumed.
   There is no regular-sequence or generation hypothesis. PASS.
3. Module category and unbounded derived category: `ringedSiteComplex O`
   is the integer cochain category of `SheafOfModules`; `ringedSiteModules`
   in its owning module is exactly that Mathlib category. `ringedSiteDerived`
   and `DerivedCategory` are its localization at quasi-isomorphisms.
   The displayed `HasDerivedCategory.{w}` instances for the root, towers,
   slices, and slice towers select localization sizes; they add no
   mathematical restriction. All variables and universes are bound. PASS.
4. Positive Koszul diagram and transitions: `ringedKoszulFactor` is
   `HomologicalComplex.double` of the scalar endomorphism to power `m+1`,
   in degrees zero and one. `ringedKoszulFactorStepF` is identity in degree
   zero, scalar b in degree one, and zero elsewhere. `ringedKoszulDiagram`
   takes their ordered total tensor, with constant O[0] for zero factors.
   The zero-based m denotes the source's positive exponent m+1; none of
   the positive stages is omitted. Tensor transitions give the product
   over the subset indexing a summand. PASS.
5. Dual tower and signs: `ringedKoszulDualTower` is literally the opposite
   positive diagram followed by `homComplexFunctor` with target O[0].
   Reading the Hom-complex signature and differential confirms that this
   is internal sheaf Hom, not the abelian-group complex of global maps.
   In one factor the differential from degree -1 is positive b^(m+1),
   and dual transitions are (b,1); ordered tensor duality supplies the
   stated multi-factor signs. PASS.
6. Extended Cech object and augmentation: `ringedExtendedCech O r b` is
   reused from its owning node. I read that construction and
   `ringedSectionLocalization`: the latter sheafifies the actual
   sectionwise `Localization.Away`, and the former tensors [O → O[1/b]].
   Thus finite subset terms, alternating differential, and degree-zero
   augmentation agree with the node, including the finite-product versus
   finite-direct-sum identification. PASS.
7. Augmented colimit identification: `alpha` in the first conjunct is an
   isomorphism of complexes, and its equation with `colimit.desc` of
   `ringedKoszulAugmentationCocone` is exactly augmentation compatibility.
   The additional telescope witness t restricts on the unshifted sum to
   `telescopeToColimit ... ≫ alpha.hom` and is a `QuasiIso`. This expresses
   the asserted homotopy-colimit representation. The published telescope
   compiled endomorphism is named `telescopeShiftColimit`; see the interface check below.
   PASS.
8. Actual strict derived tensor tower: `ringedKoszulTensorTowerFunctor`
   transposes N tensor Q_m, including transitions and maps of N, into a
   complex of towers. The second conjunct is K-flatness of each actual Q_m.
   `presentation.tensorFactors` identifies the descended `tensorTower`
   with that functor after localization, naturally on all complexes.
   Thus every representative gives the specified derived tensor tower,
   and changing representatives gives the specified comparisons. PASS.
9. Total right derived inverse limit: `RingedKoszulLimitPresentation`
   supplies `inverseLimit`, its `comparison`, `isRightDerived`, and
   `comparison_isIso` on every K-injective tower. I checked these against
   `ringedStrictTowerHomotopyLimit`; both use the same strict functor
   category and right-derived-functor convention. The definition is a
   specification of this canonical construction, not a freely chosen
   unrelated functor. No exact-products hypothesis is present. PASS.
10. Comparison for every derived N and morphisms of N: `theta` is a
    natural isomorphism from `ringedCechCompletionFunctor` (the actual
    `derivedInternalHom` with fixed Cech first argument) to
    `presentation.completion`. This gives every theta_N at once and
    enforces naturality in N. The outer `Nonempty` asserts existence of
    this fully specified structure; it is not a hollow definition. PASS.
11. Canonical unit: `ringedKoszulDualUnit` dualizes the actual projection
    and uses evaluation at one. `ringedKoszulTensorUnitCone` and
    `ringedKoszulLimitUnit` factor its compatible family by the ordinary
    limit universal property. `unitOnComplex` then uses the derived-limit
    comparison and tensor factorization. `unit` transports the same map
    to a derived object. The comparison's `unit` equation identifies it
    with epsilon-star after `ringedDerivedHomUnit`, whose definition I
    read. `theta_unique` fixes the normalized comparison: uniqueness is
    justified by the Cech completion-reflector universal property, not
    an additional hypothesis on O or N. PASS.
12. Restrictions and coherence: `slicePresentation` uses the actual
    `ringedKoszulSliceSection`; `sliceTheta` and `slice_unit` impose the
    same comparison on every slice. `sourceRestriction`,
    `targetRestriction`, and `restriction_square` express the required
    commuting square as natural transformations. `furtherTarget` uses
    actual derived `SheafOfModules.overMap`; `further_unit` and
    `further_coherence` use its actual `overFunctorMap` composition iso.
    Conjugation with the slice thetas gives the source coherence too.
    `target_unique` and `target_coherence` spell out uniqueness and
    composition of normalized comparisons, so the square is not an
    arbitrary unnormalized transport. PASS.
13. Empty list: `empty_identity` makes the strict unit invertible for
    r=0. The recursive definitions give constant P=O[0] and Cech=O[0]
    with identity augmentation, while evaluation at one identifies Q
    with O[0]. The `unit` equation therefore identifies theta with the
    identity using the constant-tower/unit identification. PASS.

Additional edge cases: a zero section is allowed (its localization is
zero and its positive Koszul differential is zero); a unit section is
allowed (the localization factor and finite Koszul factors are acyclic);
the zero ring, the zero complex, an empty site, and arbitrary unbounded
complexes are allowed. The initial positive exponent is 1. No field,
characteristic, nonempty-site, or nonempty-list instance occurs. Universe
u is arbitrary and w remains independent of it; no extra equality of
site and localization universes is imposed.

New-node audit: `def-weil-pbc-ringed-koszul-system` introduces precisely
the strict finite tensor system, duals, units, transposition, derived-limit
presentation, and slice transport used above. Its source is 0913 with
0A0A/0941, and its statement describes these actual constructions.
Its chapter, unit, creator, blueprint ancestor/via, status, null match,
empty proof fields, searches, and audit fields meet the new-definition
node rules. I read every definition and helper theorem in its module:
data are double complexes, tensors, functor composition, actual Hom,
actual cone/limit maps, and localization transports. Every postponed
coherence theorem is named, listed in `lean.declarations`, and has its
source and elementary proof in a docstring; these are precisely the
chain-map/functor/cone identities needed by the node's construction.
There is no data-valued sorry or unrelated existence choice. There are
no dependency repair modules in this delivery.

Independent searches: LeanFinder query "Sequential direct system of two
term multiplication complexes, localization telescope, inverse dual tower
of module sheaves" returned localCohomology.diagram/ofDiagram, tilde
localization and tensor/direct-limit lemmas, none this construction.
Loogle `"homComplex"` returned Mathlib's cochains of global morphisms,
which are not the internal sheaf Hom used here. Wrapper grep for
`Koszul.*(limit|tower)|Cech.*Koszul|colim.*dual` found no match.
Direct rg for Koszul, Cech-colimit and strict ringed Koszul variants in
Mathlib, upstream WeilConjectures, project lean/Sheaf, and dag/nodes
found the existing ring exterior Koszul complex and pro-etale intrinsic
completion. I opened their declarations: the former is a complex over
a ring, and the latter requires a scheme, constant coefficients and its
complete-coefficient datum; neither defines this general ringed-site
system. The existing Cech, tensor, Hom and restriction constructions are
all reused. My LeanSearch query for ringed-site homotopy-colimit duality
was unavailable (Internal Server Error); this is not negative evidence.

Interface discrepancy investigated: the local TelescopeColimit source and
current source obtained with `scompile.py --source
Sheaf.Algebra.Homology.TelescopeColimit` spell the 1-minus-shift construction
`telescopeShift`, whereas the usable compiled interface exports
`telescopeShiftColimit`. I tried the source spelling, and both the fresh
scompile and delivery dry run rejected it as an unknown constant. I restored
the worker's original compiled-interface spelling, which had passed the
initial wrapper compile. The construction still denotes the telescope's
1-minus-shift endomorphism, with the same direct sum and transition maps.
No mathematical mismatch was found. The final Lean files and node signature
retain the worker's original content; only this independent review report
is added. No statement_change or citer audit is called for.

All delivered theorem bodies remain `sorry`. Source/blueprint docstrings
are present, and the main theorem docstring records all nine proof steps.
The node's `lean.statement` was checked against the signature in the file.
Compilation and delivery validation are recorded by the required wrappers.

Second-reader validation: after restoring the compiled-interface name,
`scompile.py NN lem-weil-pbc-ringed-cech-koszul-dual-limit` compiled both
delivered sibling modules successfully, with no errors or warnings. The
Koszul construction library check took 53.3 seconds and the comparison
module library check took 20.4 seconds, each within the unchanged 60-second
limit.
