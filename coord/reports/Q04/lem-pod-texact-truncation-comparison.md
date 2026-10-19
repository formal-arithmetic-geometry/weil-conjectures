## Worker report

The module `Sheaf.CategoryTheory.Triangulated.TExactTruncationComparison` states
`CategoryTheory.Triangulated.TStructure.texact_truncation_comparison`, with one `sorry`.
It reuses the real, already constructed upstream natural isomorphisms
`Functor.eTruncLTIso tC tD (m + 1 : ℤ)` and `Functor.eTruncGEIso tC tD m`.
No new definition, dependency repair, or statement correction is needed. Only the item's
`lean` field changes. No mathematics is proved in this delivery.

Sources read: the whole item and both statement-dependency nodes; the current blueprint
`literature/blueprint/main-20261015/blueprint/sec-poincare-duality/sk-lem-finite/` files
`prop-constructible-truncations.md` and `prop-constructible-truncations.proof.md`; BBD
Proposition 1.3.3(i),(ii), printed pp. 29–30, and 1.3.16, printed p. 36 (local PDF).
The generic lemma requires preservation of both halves; no claim that an arbitrary exact
triangulated functor is t-exact is made.

Hypotheses and objects, matched clause by clause:

- The categories C and D have independent object and morphism universes `uC, vC, uD, vD`.
  The `Category`, `Preadditive`, `HasZeroObject`, `HasShift`, additive shift,
  `Pretriangulated`, and `IsTriangulated` instances are exactly the recorded Mathlib
  encoding of `def-weil-triangulated-category`, including the octahedral axiom.
- `tC : TStructure C` and `tD : TStructure D` use the `mathlib_match` of
  `def-weil-t-structure`. `_hC : tC.bounded = ⊤` and `_hD : tD.bounded = ⊤` state that
  all objects are bounded. These hypotheses are retained although the result extends to
  unbounded t-structures. No new nondegeneracy or completeness assumption occurs.
- `F : C ⥤ D`, `[F.CommShift ℤ]`, and `[F.IsTriangulated]` give the exact functor with
  its shift comparison, using the declaration listed by the triangulated-category node.
- `[F.IsTExact tC tD]` is the upstream class whose two fields say, for every object X and
  integer n, `tC.IsLE X n → tD.IsLE (F.obj X) n` and the analogous `IsGE` implication.
  Its full definition was read in the upstream SpectralObject module (lines 39–45).
  The class wrappers express membership in `tC.le n` and `tC.ge n`; no case is dropped.
- `m : ℤ` is arbitrary. `truncLT (m + 1)` is exactly `τ≤m`, not `τ<m`.
  Mathlib's `truncLE` is defined by this very expression. `truncGE m` is `τ≥m`.
  The maps `truncLTι (m + 1)` and `truncGEπ m` are the node's counit and unit.

Conclusions, in their order in the conjunction:

1. For every K, the existing upper comparison followed by the counit at FK equals
   `F.map` of the source counit; `F.map` of the source unit followed by the existing
   lower comparison equals the unit at FK. These are precisely the two displayed
   characterizations, with Lean's left-to-right composition `≫`. The upstream definitions
   are natural isomorphisms, so existence and naturality in K are supplied by their types.
   Integer-indexed extended truncations reduce definitionally to the recorded Mathlib
   truncations, as verified by the clean compilation of these equations.
2. Every natural isomorphism β of the indicated upper-truncation functors satisfying the
   counit characterization equals the existing upper comparison.
3. The analogous uniqueness holds for the lower comparison with its unit characterization.
   These assert uniqueness under just the characterizations, not under extra coherence laws.
4. For every exact t-exact `G : C ⥤ D`, every `η : F ⟶ G`, and every K, both displayed
   squares commute. The expressions are `η.app (τ K) ≫ αG.hom.app K` and
   `αF.hom.app K ≫ τ.map (η.app K)`. There is deliberately no `η.CommShift` assumption.
5. For the identity functor, any pair of natural isomorphisms satisfying the two canonical
   characterizations has identity components. This describes the unique comparisons
   independently of a proof object for the identity functor's t-exactness. These variables
   are characterized comparisons, not arbitrary unnormalized maps. Their existence follows
   either from the identity isomorphisms (with the functor unitors) or the same canonical
   construction applied to the identity. Thus the clause is not vacuous.
6. The final clause quantifies over every third category B in independent universes uB, vB,
   its triangulated structure and bounded t-structure tB, and every exact t-exact H : D ⥤ B.
   Every comparison for `F ⋙ H` satisfying its counit or unit characterization is, at K,
   `H.map (αF.hom.app K) ≫ αH.hom.app (F.obj K)`, for the respective sign.
   Exactness and preservation of the two halves for the composite follow from those of
   F and H; no separate or stronger hypothesis on the composite is added. The comparisons
   quantified here exist by the same upstream construction for the composite, supplying its
   t-exactness structure from the two given structures. Quantifying over characterized
   comparisons avoids introducing another definition or a choice of that structure. Equality
   of all hom components is equality of natural isomorphisms, so this is the node's
   composition law. The target B is quantified inside this clause; it adds no assumption to
   existence and uniqueness for F.

Dependency declarations used (full signatures and docstrings inspected):

- `def-weil-triangulated-category`: its `mathlib_match` is the declaration record, with no
  `lean` required. `Mathlib.CategoryTheory.Triangulated.Pretriangulated` supplies
  `CategoryTheory.Pretriangulated`; `Mathlib.CategoryTheory.Triangulated.Triangulated`
  supplies `CategoryTheory.IsTriangulated`; `Mathlib.CategoryTheory.Triangulated.Functor`
  supplies `Functor.IsTriangulated` and its `CommShift` interface.
- `def-weil-t-structure`: its `mathlib_match` supplies
  `CategoryTheory.Triangulated.TStructure` from
  `Mathlib.CategoryTheory.Triangulated.TStructure.Basic`, with `bounded`, and
  `truncLT`, `truncGE`, `truncLTι`, `truncGEπ` from the TruncLTGE module.
  The integer definition of `truncLE` in TruncLEGT was also inspected.
- The public upstream import
  `WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject`
  provides `Functor.IsTExact`, `Functor.eTruncLTIso`, and `Functor.eTruncGEIso`.
  This real construction is reused, not duplicated. The associated normalization lemmas
  `eTruncLTIsoApp_hom_eTruncLTι_app` and `eTruncGEπ_app_eTruncGEIsoApp_hom` were read.
- The proof-only import is the recorded module of
  `lem-weil-heart-short-exact-triangles`, namely
  `WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology`. Its public ShortExact
  import exposes `exists_iso_triangleLEGE`, `triangle_hom_ext_of_isLE_of_isGE`,
  `truncLEAdjunction`, and `truncGEAdjunction`, whose full signatures and docstrings were
  read. They supply the triangle uniqueness and adjunctions of the nine-step proof.
  The theorem docstring records all nine proof steps, including both cancellation arguments.

Edge cases checked before writing:

- All integer cutoffs, including m = 0 and negative m, are retained. The upper cutoff is
  m+1 and the lower cutoff m; the proof uses cuts (m,m+1) and (m-1,m), respectively.
- Zero objects and the zero triangulated category satisfy the same canonical equations;
  no nonzero-object or nonempty-index assumption is introduced.
- Identity and zero functors cause no exceptional case: uniqueness is still by the canonical
  unit/counit, rather than any epi/mono assumption on a truncation map in the whole category.
- Natural transformations need not be invertible or compatible with shift comparisons.
- Object and morphism universes are independent for each of C, D, and B; no size equality
  or restriction to a particular derived category was introduced.

Searches performed using the prescribed wrapper and read-only source searches:

- `msearch.py ... leanfinder`: query "A t-exact functor between triangulated categories
  commutes naturally with both truncation functors, uniquely compatible with canonical maps
  and with natural transformations and composition". Eight results, including
  `Functor.map_distinguished_exact`, `Functor.distTriang_iff`, and `TStructure.truncGEδLT`;
  none states uniqueness and all three coherence laws.
- `msearch.py ... loogle`: query
  `CategoryTheory.Triangulated.TStructure.truncLE, CategoryTheory.Triangulated.TStructure.truncGE`.
  Six results: the truncation connecting morphism, triangle projections, and induced
  t-structures, not the t-exact-functor comparison theorem.
- `msearch.py ... leansearch`: query "A t-exact functor commutes with both canonical
  truncations, uniquely compatible with their unit and counit and with natural
  transformations, identities, and composition". Eight hits: complex truncation functors,
  `TStructure.truncLT`, and finite-limit/colimit exact functors; no exact match.
- `msearch.py ... grep`: query `trunc.*[Ii]so|[Ii]so.*trunc|IsTExact`, subdirectory
  `CategoryTheory/Triangulated/TStructure`. Twenty hits including
  `isLE_iff_isIso_truncLTι_app`, `truncLEIsoTruncLT`, and extended-truncation comparisons;
  no functorial uniqueness/coherence theorem.
- `rg` over the upstream `WeilConjectures/` for truncation-isomorphism and t-exactness names
  found the real comparisons in `Mathlib/CategoryTheory/Triangulated/TStructure/SpectralObject.lean`.
  The entire definition and normalization/naturality sections were read, together with the
  file's remaining declaration list. These comparisons are used in the new statement.
- `rg` over shared `lean/Sheaf/` found specialized derived/truncation and integral coefficient
  comparisons, not this abstract theorem. A focused search for eTrunc comparisons with
  identity/composition/naturality suffixes found no theorem with the node's full content.
- The node-id search in the upstream source, and the name/id search in
  `dag/lean_names_upstream.json`, found no attachment for this item. The proposed theorem
  name was absent from Mathlib, upstream, and the side library.

Validation: the prescribed `scompile.py Q04 lem-pod-texact-truncation-comparison` compiled
both the wrapper's sandbox form and the module form cleanly (1.8 and 1.9 seconds).
Every universe and variable is explicitly bound; the file has no local notation, local
instance, private declaration, hidden `let`/`show` in a statement, or line over 100 characters.
No `STATEMENT-DISPUTED` or node fault was found.

## Second reading by Q04

Author's separate clause-by-clause pass; the independent reading is the maintainer's,
as specified by the dispatch brief, which prohibits starting another agent.
With the node and final Lean file open, checked the directions of both comparison maps,
all compositions, and each of the six conjunction blocks above. In particular the upper
comparison uses m+1 rather than m, the lower comparison uses m, η has no shift-compatibility
condition, identity is stated on hom components, and H is evaluated at FK in the composite.
The identity/composite clauses quantify over precisely normalized comparisons; their
existence follows from the same existing canonical construction. Both uniqueness clauses
are independent of the later coherence clauses. B's bounded t-structure is quantified only
in the composition clause. No mismatch or source correction was needed. The only new
postponed theorem is the item's own theorem, with its complete nine-step proof docstring.
