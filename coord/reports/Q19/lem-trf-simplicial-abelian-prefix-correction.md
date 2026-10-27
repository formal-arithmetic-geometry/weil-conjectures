## Worker report

Repair of L's independent stage-2 return at immutable head d8c580417e2e.
The return explicitly requests a Lean module and compilation; this repair follows that
specific stage-2 instruction rather than the generic stage-1-only boilerplate.
The previous sandbox node differed from current live only in split_report. Its added
sentence is removed: every live field, including Q39's split_report, proof, statement,
provenance, searches and reviewed record, is retained verbatim. Only lean is added.
The prior report remains in the sandbox as prior-report.md; citations.json is retained.

Files delivered: lean/Sheaf/AlgebraicTopology/SimplicialAbelianPrefixCorrection.lean,
the item's node JSON with its lean record, and this report. Zero new DAG nodes;
zero new Mathlib leaves. No attachments and no WANTED sources. No statement correction.

The genuine definition CategoryTheory.SimplicialObject.abelianPrefixCorrection uses
natural-number recursion. It starts at the given v and, for r < k, returns
v_r + X.σ r (a_r - X.δ r v_r). For r ≥ k it is constant; restricting to 0 ≤ r ≤ k
is precisely the finite sequence in the node. Its data contain no sorry or choice.
The correction is a construction inside the item's own statement, not a separate
new mathematical notion requiring a new DAG node.

The sole postponed theorem is
CategoryTheory.SimplicialObject.abelianPrefixCorrection_spec. Its proof is exactly
`by sorry`, and its docstring carries all four existing DAG proof steps and their
node citations. Its hypotheses and conclusions match as follows:

- G: Deltaᵒᵖ → Ab is X : SimplicialObject AddCommGrpCat.{u}, with unrestricted u.
  X.δ and X.σ are Mathlib's actual face and degeneracy morphisms.
- The degree n ≥ 2 is parametrized as m + 2 for arbitrary m : Nat. Conversely any
  node degree n has m = n - 2 and m + 2 = n. Thus this changes no degree case.
  The prescribed entries are a : Fin k → X_(m+1), and hk : k ≤ m + 2 is k ≤ n;
  Nat supplies k ≥ 0. The starting v : X_(m+2) is arbitrary.
- ha quantifies every i,j : Fin k with i < j and is exactly
  d_i(a_j) = d_(j-1)(a_i), in degree m. Subtraction on j.val is only used under i<j,
  which forces j>0. No compatibility beyond the prescribed prefix is assumed.
- The first conjunct quantifies every natural r ≤ k and every prescribed i<r:
  d_i(v_r)=a_i. All admissible i are in Fin k since i<r≤k.
- The second conjunct quantifies every transition r : Fin k and defines
  e=a_r-d_r(v_r). For every i<r it states both d_i(e)=0 and d_i(s_r(e))=0;
  it also states d_r(s_r(e))=e. These are all three extra identities of the node.
- The last two conjuncts explicitly state v_0=v and every face of v_k equals a_i.
  The recursion itself is a genuine definition, not a witness with its equations
  postponed as an existence hypothesis.

Statement dependency def-weil-pbc-simplicial-object records
Mathlib.AlgebraicTopology.SimplicialObject.Basic, CategoryTheory.SimplicialObject,
CategoryTheory.SimplicialObject.δ and CategoryTheory.SimplicialObject.σ. Those are
used directly. The proof dependency lem-weil-pbc-simplex-face-face-identity is
Mathlib's SimplexCategory.δ_comp_δ, in SimplexCategory.Basic, already imported by
SimplicialObject.Basic. AddCommGrpCat is imported from Mathlib.Algebra.Category.Grp.Basic.
No separate proof-dependency module import is needed because the existing public
statement import already exposes it.

I searched the read-only project roots WeilConjectures/ and Sheaf/ for the exact
blueprint tag, prefixCorrection and prefix_correction: no existing declaration
states this item. The retained node records earlier real searches and their results;
I read those records, including the second semantic phrasing about compatible prefixes
of simplicial modules. Fresh logged msearch.py searches on 2026-10-24 were:

- leanfinder: "In a simplicial abelian group compatible initial faces are filled by
  recursively adding degeneracies of face errors". Eight hits included
  DoldKan.HigherFacesVanish.induction and comp_σ, simplex generators and pointed
  simplicial-set multiplication. I opened DoldKan/Faces.lean:41-50,160-162 and
  Degeneracies.lean:43-45. HigherFacesVanish concerns zero upper faces of a morphism;
  its induction kills another upper face and does not prescribe compatible lower
  face elements from an arbitrary starting simplex. It is not this statement.
- loogle: `"SimplicialObject", "σ", "δ"`. Twelve hits are individual mixed identities
  and their associated composition lemmas. I read SimplicialObject/Basic.lean:91-199:
  these supply the operators and identities, not the correction sequence or induction.
- grep: `prefix|correction|fill.*face|face.*fill`, subdirectory AlgebraicTopology.
  Zero hits, as printed by the required search command.
- leansearch: "Successive degeneracy corrections in a simplicial abelian group
  realize a compatible prefix of faces from any initial simplex". Eight hits gave
  mixed identities, the degeneracy definition and degenerate simplices; none gives
  the node. These queries and actual results are retained in searches.jsonl.

The prescribed initial stage-1 dry run completed successfully, but it accepted the
metadata-only packet that L returned. That was diagnostic evidence, not completion
of this repair. This packet uses deliver2.py with WEIL_SANDBOX pointing to the
original retained sandbox, since only the stage-2 tool includes the required Lean
module and lean record. Compilation via the prescribed scompile.py wrapper succeeded
cleanly for both the sandbox view and module view (1.4 s and 3.2 s).

## Review by Q19

I read Stacks simplicial.tex, Tag 08NZ, lemma-simplicial-group-kan, the ascending
paragraph at lines 5771-5786, and Tag 0167, lemma-relations-face-degeneracy (1)--(3).
The source starts its nonempty prefix at s_0(a_0). Starting instead with arbitrary
v is valid because the invariant at r=0 is empty; at v=0 the first transition is
exactly the source's start. The current blueprint ancestor lem-trf-local-term-locality
and the chapter/unit records retain the contracting-correspondence route. This is
its inherited auxiliary simplicial input, not a new proof route. There are no new
node sources and no SGA citations.

For DAG step 1, I opened def-weil-pbc-simplicial-object: it defines the functor and
actual order-map faces and degeneracies. I opened lem-weil-pbc-simplex-face-face-identity:
its statement supplies exactly the coface equality that contravariance turns into
the face-face relation. The mixed identities are the displayed elementary order-map
computations in the existing step; they are not incorrectly taken from a definition.
Step 2 uses the same definition for homomorphisms and their degrees and sets the
empty base invariant. Step 3 uses compatibility only for i<r<k, the cited face-face
identity, and the established invariant to give
`d_i e_r = d_(r-1)(a_i-d_i v_r)=0`; the mixed identities then give the two correction
identities. Step 4 adds these equalities to preserve the earlier faces and fix the
new one, completing the induction. Thus every cited statement says what its step
uses. All retained citations.json quotes were rechecked as literal substrings of
the current live node statements. The four proof steps have lengths 647, 365, 524,
and 412 characters, so none conceals a lemma in a step over 2000 characters.

The bounds are explicit: r<k≤n implies r≤n-1, so s_r exists; i<r forces r≥1 for
s_(r-1), and n≥2 types the double faces. In Lean these correspond to m≥0 and the
Fin bounds discharged by omega. The underlying data are always those of X, and no
extra linearity, Kan condition, finiteness, or zero starting simplex was introduced.

I checked k=0 (no a entries, no transitions, v_k=v), k=1 (one correction, d_0s_0=id),
and n=k=2 (m=0; compatibility d_0 a_1=d_0 a_0 ensures the second correction preserves
face zero). A constant simplicial abelian group forces equal prescribed entries
when there are at least two: the first correction gives that entry and later errors
vanish. The zero group satisfies every clause. These checks also test the lowest
actual degree and largest allowed prefix.

## Second reading by Q19

This is Q19's own second pass over the completed node and Lean file; no second agent
was started. The maintainer performs the independent reading under the direct-delivery
brief. I matched every binder and all four conjuncts with the node as detailed above.
In particular the first conjunct includes r=k, the second includes both lower-face
vanishings separately, and the distinguished face is asserted even at r=0.
The Fin k indexing introduces neither an omitted terminal face nor an extra a_k.
The use of degree m+2 is precisely the full n≥2 range, not an additional hypothesis.
The definition gives the recursion without any theorem supplying its data. One
named theorem, and only that theorem, contains sorry; both declarations and the module
have source/blueprint docstrings, and the theorem includes the complete proof plan.

Return H1 is repaired by the module and complete lean record. Return H2 is repaired
by restoring the live split_report verbatim: the substantive change is now the
formal statement and recursive construction. Return H11/report is repaired by
these required report sections and the explicit hypothesis/clause reading above.
The already-approved mathematical split is preserved exactly. No unresolved
mathematical point of the return remains.
