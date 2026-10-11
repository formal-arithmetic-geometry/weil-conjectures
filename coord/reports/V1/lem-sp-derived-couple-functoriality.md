## Worker report

The module defines `CoupleMorphism` with degree-preserving maps on the D and E terms and the three commutative squares with alpha, f, and g. It states `derivedCoupleFunctoriality`: page maps for every page (indexed as `n + 2`) extending `tE` and commuting with page differentials; transport of limiting cycle and boundary subobjects; and an induced map on the quotient at infinity. Every hypothesis is explicit in the structure fields, and the three conclusion clauses correspond respectively to all pages, `Z∞/B∞` preservation, and the quotient map.

Dependencies used: `Sheaf.CategoryTheory.ExactCouple` (`CategoryTheory.BigradedExactCouple`, `page`, `pageDifferential`), and `Sheaf.CategoryTheory.ExactCoupleConvergence` (`LimitSubobjects`, `pageInfinity`, `limitBoundary_le_cycle`).

Edge cases checked: page index is represented by `n + 2`, avoiding undefined pages below 2; all bidegrees are integers; zero and limiting subobjects are handled by the existing `LimitSubobjects` and quotient constructions. The statement uses no boundedness or convergence assumptions, matching the source functoriality claim.

Searches: `msearch.py leanfinder` for “derived exact couple construction is functorial morphism induces maps on pages” found only homology-sequence maps and no exact-couple declaration; `msearch.py loogle` for `ExactCouple SpectralSequence derived couple` had no hits; grep of Mathlib and `WeilConjectures`/`lean/Sheaf` found no prior functoriality declaration. Existing exact-couple and convergence declarations were used directly.

## Earlier second reading (a previous round; superseded)

The node was read against the file. `CoupleMorphism` renders exactly the three maps and commutative identities in the node hypothesis, with all bidegrees explicit. The first conclusion clause gives one map on each `E_{n+2}` and the differential commutation equation at the precise target bidegree. The second clause states factorization of the initial map through target `Z∞` and `B∞`. The third clause gives the induced quotient map together with the commuting quotient square. No hypothesis or conclusion clause was omitted.


## Second reading by V1

I read the item JSON, both statement-dependency JSON files and their actual modules
`ExactCouple.lean` and `ExactCoupleConvergence.lean`, and the existing
`ExactCoupleMorphism.lean`. The Stacks checkout is absent on this machine. I obtained
Stacks `homology.tex` from its official GitHub repository into this item's scratchpad
and read the exact-couple section, from definition-exact-couple through
lemma-spectral-sequence-associated-exact-couple and its infinity paragraph.
The source assumes only an abelian category. Its ungraded page numbering starts at 1;
the dependency node's blueprint bigraded convention starts at 2 and shifts g after
 each derivation (Stacks shift-functor variant 0AMJ). No node statement correction
was made. No new nodes or dependency modules are delivered.

Objects, hypotheses and conclusions matched individually:

- The same abelian category: `C : Type u`, `[Category.{v} C]`, `[Abelian C]`.
  Arbitrary object and morphism universes; no smallness, completeness, boundedness,
  or half-plane assumption. Verdict: exact match.
- Two initial exact couples: `X Y : BigradedExactCouple C 0`. I checked the
  dependency's D/E families, alpha (-1,+1), f (+2,-1), g (0,0), zero composites,
  and image/kernel equalities. Its `derived` uses the actual image of incoming alpha
  and kernel/cokernel homology, and `pageCouple n` has type n. Verdict: exact match.
- Degree-preserving t_D and t_E: `T.tD p q`, `T.tE p q` in `CoupleMorphism`.
  No component changes its bidegree. Verdict: exact match.
- The alpha square: `T.alpha_comm`, with target (p-1,q+1). Verdict: exact match
  after reading categorical composition in its left-to-right Lean order.
- The f square: `T.f_comm`, with target (p+2,q-1). Verdict: exact match.
- The g square: `T.g_comm`, with target (p+s,q-s). Initially s=0, hence (p,q).
  Generalizing the same morphism structure to s is needed to state morphisms between
  the derived couples, without inventing a second notion. Verdict: exact match.
- Well-defined induced derived D maps: existential family `M`, the initial D
  equality, and the successor `derivedDInclusion` square. The latter pins each
  successor map to the restriction on the incoming alpha image. Verdict: repaired;
  the draft omitted D maps entirely.
- Well-defined induced derived E maps: initial E equality, kernel inclusion square
  for k, and `derivedEProjection` square linking `(M n).tE` to `(M (n+1)).tE`.
  These characterize the induced homology map, rather than unrelated chain maps.
  Verdict: repaired; the draft had no successive-page compatibility.
- Commutation with the derived structure maps: every `M n` is a `CoupleMorphism`
  of `X.pageCouple n` and `Y.pageCouple n`, so all three squares hold at every
  iterate. Verdict: repaired; draft only asserted differential commutation.
- Every page E_r and d_r: `(M n).tE` is the map on E_(n+2), and the explicit
  differential square has target (p+2+n,q-1-n). This is (p+r,q+1-r).
  Verdict: exact match, including r=2.
- Limiting cycles: `∀ LX LY`, `(LY.Z p q).Factors ((LX.Z p q).arrow ≫ T.tE p q)`.
  I checked `LimitSubobjects.Z_glb` is precisely the intersection of the canonical
  finite cycles, not an arbitrary chosen subobject. Verdict: exact match.
- Limiting boundaries: the analogous B factorization, with `B_lub` the union of
  the canonical finite boundaries. Verdict: exact match.
- Infinity quotient map: `e : X.pageInfinity LX p q ⟶ Y.pageInfinity LY p q`
  together with the restricted cycle map z, its inclusion square, and the cokernel
  projection square. `pageInfinity` is the actual cokernel of B∞ ↪ Z∞, using the
  named theorem `limitBoundary_le_cycle`. Verdict: exact match.
- Limits when they exist: LX and LY now quantify only in the infinity conjunct.
  Finite-page functoriality is unconditional, even if no such limits exist.
  Verdict: repaired; the draft put LX and LY among all-theorem hypotheses.

Edge cases: n=0 gives the initial maps, all n≥0 cover exactly all r≥2; no negative
bidegrees are excluded. Zero couples and zero morphisms are included, as are empty
categories if they admit the stated abelian structure (otherwise the hypothesis has
no instance). No choice of a finite index set, scheme, field, or characteristic occurs.
There is no countable-limit instance assumed: infinity is conditional on exactly the
GLB/LUB data in the dependency. u and v remain independent. No variable or universe
is unbound. No hollow definition or theorem proof other than the required sorry occurs.

Independent searches, with different wording from the first report:

- `msearch.py ... leanfinder "derived exact couple functoriality"`: eight results
  about Ext.mapExactFunctor and ShortComplex.Exact.map; none states this item.
- `msearch.py ... loogle '"ExactCouple"'`: zero hits.
- `msearch.py ... leansearch "morphism of exact couples induces homology maps"`:
  unavailable, Internal Server Error (recorded as unavailable, not as a negative hit).
- `rg 'CoupleMorphism|[Ee]xact[Cc]ouple|derivedCoupleFunctoriality'` over pinned
  Mathlib, upstream WeilConjectures, this repository's lean/Sheaf, and
  dag/lean_names_upstream.json: no existing morphism definition or exact match.
  Existing `coupleMorphism` was opened and read: it gives page/cohomology maps but
  omits derived D maps and their structure squares, and supplies infinity maps only
  under half-plane hypotheses. It cannot replace this general node. Upstream
  SpectralSequence.pageInfinity is a stabilized first-quadrant object, not the
  conditional GLB/LUB quotient here. All usable dependency declarations are reused.

Changes: generalized the existing hypothesis structure to type-s couples; restored
induced derived D/E maps and all structure squares and successor compatibility;
restricted limit hypotheses to the infinity clause; added the missing copyright
header and the complete three-step proof docstring with dependency IDs. Retained
the correct infinity factorization and quotient equations. Updated lean.statement
verbatim to the corrected signature, and recorded both declarations.
Server single-file compilation passed cleanly (no errors or warnings).
