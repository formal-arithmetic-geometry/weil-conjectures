## Worker report

The module `Sheaf.AlgebraicTopology.GappedFaceInnerHornPresentation` defines
`SSet.gappedFaceSubcomplex n J` as the union `⨆ q : J, stdSimplex.face {q.1}ᶜ`,
which is the node's `K_J`, and states
`SSet.gapped_face_inner_horn_presentation` with proof `sorry`.

The Lean statement renders the node clause by clause:

- `n ≥ 2` is `(hn : 2 ≤ n)`.
- The vertex set `[n]` is `Fin (n + 1)`, and `J ⊆ [n]` is
  `J : Set (Fin (n + 1))`.
- The gap is given by `i j k : Fin (n + 1)`, `hij : i < j`, `hjk : j < k`,
  `hi : i ∈ J`, `hj : j ∉ J`, and `hk : k ∈ J`.
- `K_J` is `gappedFaceSubcomplex n J`; its definition is the union of the
  codimension-one faces indexed by `J`.
- A finite filtration is `t : ℕ` and
  `L : Fin (t + 1) → (Δ[n] : SSet.{u}).Subcomplex`, with
  `L 0 = gappedFaceSubcomplex n J` and `L (Fin.last t) = ⊤`.
- For each `h : Fin t`, `hle : L h.castSucc ≤ L h.succ` is the filtration
  inclusion. The attachment has dimension `d`, inner vertex `a`, maps
  `g : Λ[d,a] ⟶ L h.castSucc` and `f : Δ[d] ⟶ L h.succ`, with
  `2 ≤ d`, `0 < a`, `a < Fin.last d`, the commuting square
  `Λ[d,a].ι ≫ f = g ≫ Subcomplex.homOfLE hle`, and
  `IsPushout Λ[d,a].ι g f (Subcomplex.homOfLE hle)`. `IsPushout` in `SSet`
  is the degreewise pushout in sets with the induced simplicial operators.
- For every `Q : SSet.{u}` with `[Quasicategory Q]` and every map
  `f : (gappedFaceSubcomplex n J : SSet) ⟶ Q`, the extension clause is
  `∃ F : Δ[n] ⟶ Q, (gappedFaceSubcomplex n J).ι ≫ F = f`, so the restriction
  is exactly the given map.

The statement dependency used is `Sheaf.CategoryTheory.EnhancedDiagramsCones`,
with declaration `SSet.Enhanced.coneCategory` (and its recorded helper
primitives); the module uses the same Mathlib `SSet`, `stdSimplex.face`,
`horn`, `Quasicategory`, and `IsPushout` declarations rather than private copies.

I checked the edge cases `n = 2` with `J = {0,2}` and gap `0 < 1 < 2`, where the
filtration is the single inner 2-horn attachment; empty `J` is excluded by the
gap hypotheses; and degenerate simplices are included because all subcomplexes
and pushouts are simplicial-set constructions degree by degree. The conditions
`0 < a < d` ensure that every attachment is genuinely inner.

Searches for an existing declaration were made before writing the module:

- `msearch.py leanfinder` for a finite inner-horn filtration of a gapped face
  complement: returned only general simplicial/nerve declarations; no exact
  match.
- `msearch.py loogle` for `SSet.innerAnodyneExtensions`: returned Mathlib's
  saturation infrastructure, but no gapped-face filtration statement.
- `msearch.py grep` for `innerAnodyne|Inner.*horn|horn.*Inner|Pairing.*inner`
  under `Mathlib/AlgebraicTopology/SimplicialSet`: found only general pairing,
  horn, and pushout-product infrastructure; no exact match.
- `rg` over `WeilConjectures` and project `lean/Sheaf` for
  `gappedFaceSubcomplex`, `gapped_face_inner_horn_presentation`, and
  `gapped|generalizedHorn|face.*pairing`: found no existing declaration.

The source is Lurie, *Higher Topos Theory*, Lemma the project server, printed
pp. 305--306 (PDF pp. 322--323), as recorded in the DAG node. No
`STATEMENT-DISPUTED` issue or node fault was found.

## Second reading by N2

I independently opened the item node, its seven proof steps, the delivered module,
the sole statement dependency `def-cbc-enhanced-diagrams-cones`, its recorded
`Sheaf.CategoryTheory.EnhancedDiagramsCones` module, and the Mathlib primitives
it explicitly adopts. There is no repair note for this item, no statement_change,
no new node and no dependency module in the delivery.

Source check: I read HTT Lemma the project server and its entire proof directly at
https://www.math.ias.edu/~lurie/papers/HTT.pdf, printed pp.305--306, PDF pages
322--323 (zero-based). This item has no Stacks source. The lemma assumes exactly
a vertex subset and a gap i<j<k with i,k in J and j outside J; there is no
ambient category, coefficient, finiteness, characteristic or nonemptiness
assumption beyond these. The source's subcomplex spanned by faces not
containing the face on J is exactly the node's face union. Its proof gives the
finite filtration and pushout squares, and the extension conclusion follows
from the defining quasicategory horn fillers. The node agrees with that source.

My object/hypothesis/conclusion checklist, with the Lean rendering and verdict:

1. Small simplicial sets, their maps, standard simplices and face subsets:
   `SSet.{u}`, categorical morphisms, `Δ[n]`, and `stdSimplex.face` are the
   actual Mathlib primitives publicly imported by the dependency module. I
   read its header and `coneCategory` signature: coneCategory itself is a
   coherent comma construction, not the simplex or horn. The relevant notions
   are the existing primitives explicitly adopted by that module and node.
   Verdict: the same objects, with arbitrary universe u and no extra instance.
2. Integer dimension n>=2 and vertex subset J of [n]: `(n : ℕ) (hn : 2 ≤ n)`
   and `(J : Set (Fin (n + 1)))`. Verdict: exact; no decidability or cardinality
   assumption on J is added.
3. Face on S consists of all vertex images contained in S: Mathlib
   `stdSimplex.face` takes a finite vertex set, and its `obj` definition at
   StdSimplex.lean:282 is precisely the image-subset predicate. Every subset
   of Fin (n+1) is finite. Verdict: the same face, including degenerate simplices.
4. K_J is the union of the codimension-one faces omitting q in J:
   `gappedFaceSubcomplex n J := ⨆ q : J, stdSimplex.face {q.1}ᶜ`.
   Here the complemented singleton is a Finset supplied to `face`; the iSup
   is over the subtype of vertices in J. Thus membership means omitting some
   vertex of J, rather than omitting every vertex of J. Verdict: exact real
   construction; no choice, postponed data or hollow definition.
5. The specified gap: `(i j k : Fin (n+1))`, `hij : i < j`, `hjk : j < k`,
   `hi : i ∈ J`, `hj : j ∉ J`, `hk : k ∈ J`. Verdict: every hypothesis is
   present in the same order; no assumption that J is an interval or a horn.
6. A finite filtration by subsets of this same simplex:
   `∃ (t : ℕ) (L : Fin (t+1) → (Δ[n] : SSet.{u}).Subcomplex)` with
   `L 0 = gappedFaceSubcomplex n J`, `L (Fin.last t) = ⊤`, and for every
   `h : Fin t`, `hle : L h.castSucc ≤ L h.succ`. These are adjacent stages;
   transitivity gives the whole increasing chain. Verdict: exact endpoints,
   finite length, inclusion maps and ambient simplex.
7. Each adjacent inclusion is a single inner-horn pushout: existential `d`,
   `a : Fin (d+1)`, maps `g : Λ[d,a] ⟶ L h.castSucc` and
   `f : Δ[d] ⟶ L h.succ`, with `2 ≤ d`, `0 < a`, `a < Fin.last d`.
   Verdict: exact inner range and dimensions; attaching maps are quantified
   separately for each stage, as in the node.
8. The square is the specified pushout: `Λ[d,a].ι ≫ f =
   g ≫ Subcomplex.homOfLE hle` and
   `IsPushout Λ[d,a].ι g f (Subcomplex.homOfLE hle)`. I checked the argument
   order in IsPullback/Defs.lean:78 and the canonical inclusion in
   Subcomplex.lean:74--89. This puts the simplex on the upper right and the
   old stage on the lower left. Colimits of simplicial sets are computed
   pointwise in sets, so this categorical pushout is equivalent to the node's
   degreewise pushout with its induced operators. Verdict: exact square.
9. Extension to every quasicategory with exact original restriction:
   `∀ (Q : SSet.{u}) [Quasicategory Q] (f : (gappedFaceSubcomplex n J : SSet)
   ⟶ Q), ∃ F : Δ[n] ⟶ Q, (gappedFaceSubcomplex n J).ι ≫ F = f`.
   I read `Quasicategory.hornFilling'` and `hornFilling` in Basic.lean:39--53:
   these are precisely inner-horn fillers, without a Kan assumption.
   The filtration witnesses precede Q and f, so the filtration is independent
   of the target and the map, as required. Verdict: every quantifier and
   restriction clause agrees; there is no uniqueness assertion.

Edge cases: n=0 and n=1 are excluded in both statements by n>=2, independently
also by the gap. Empty J, singleton J and full J cannot satisfy the gap.
The construction itself still makes sense for these sets (empty union is
bottom; the full vertex union is the boundary). For n=2, J={0,2}, it is exactly
the inner 2-horn, with one attachment at a=1. For n=3, J={0,2}, gap j=1,
attach first the face on {0,1,2}, then the full simplex; the missing faces are
respectively {0,2} and {0,2,3}. A zero-length filtration is allowed syntactically
but cannot identify this proper K_J with top; no invalid case is introduced.
An empty quasicategory is not excluded: K_J contains vertices under the gap,
so there is no input map into it. No inhabitedness is assumed. Arbitrary u
covers all sizes of Q; standard simplices and horns exist in the same universe,
so no site/morphism universe equality or hidden size restriction occurs.
Zero objects, schemes and characteristic are not objects of this lemma.

Independent duplicate searches (2026-10-17), using queries different from the
worker's:

- `msearch.py leanfinder`: "A simplex subcomplex consisting of simplices whose
  vertex images omit some element of a nonconvex subset is built by finitely
  many inner horn pushouts". Eight hits: horns, boundary, PairingCore,
  Pairing, and nondegenerate-simplex constructors. None states this filtration.
- `msearch.py loogle`: `SSet.stdSimplex.face, SSet.horn`. Twelve hits including
  `horn_eq_iSup`, `face_le_horn_iff`, face inclusion maps and two-dimensional
  horn squares. I read the face and horn definitions and horn_eq_iSup:
  these construct individual horns, not a union for arbitrary gapped J.
- `msearch.py leansearch`: "A union of faces excluding a noninterval set of
  vertices admits a finite filtration by inner horn attachments". Eight hits,
  chiefly the same horn face maps plus an unrelated convex simplicial-complex
  vertex lemma; no exact match.
- Direct `rg` over Mathlib/AlgebraicTopology/SimplicialSet for
  `nonconvex|noninterval|generalized.?[Hh]orn|gapped|union.*face|face.*union`
  found no matching theorem or definition. I also read Inner/Basic.lean
  and Inner/PushoutProduct.lean: the pairing interface assumes an already
  supplied regular inner pairing, while unionProd concerns a product with a
  boundary. Neither supplies this gapped face filtration.
- Direct `rg` over upstream WeilConjectures, project lean/Sheaf and
  dag/lean_names_upstream.json for these concepts, `the project server` and both proposed
  names found no exact match. The project hit EquivalencePrismExtension
  cites Kerodon Proposition the project server, a different source and proposition.

Mismatch found and repaired: the statement itself has no mathematical mismatch.
The worker's proof docstring compressed the seven DAG steps and omitted the
cardinality exclusion argument for the missing j-face. I expanded only that
docstring into all seven steps, including the exact intersection in every degree,
unique degreewise gluing and finite induction with the cited dependency's horn
fillers. The actual definition and theorem signature are unchanged. Every
postponed proof is the single named theorem's `sorry`; no theorem was proved.
The docstrings carry the correct source and blueprint tags, the declarations
have no private/local aliases, and all variables and universes are bound.

Validation: scompile.py compiled the delivered module cleanly, with no errors
or warnings (sandbox 2.3 s; library 1.9 s). The official signature extractor
returns exactly lean.statement; every Lean line is at most 100 characters.
