## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteUnramifiedEtaleLocal` states
`AlgebraicGeometry.exists_etale_closed_immersion_decomposition_of_finite_unramified`.
Its sole proof is `sorry`; it introduces no definitions or instances.

Source checked: Stacks Project, Étale Morphisms, Lemma 04HJ,
`lemma-finite-unramified-etale-local`, statement and proof, read in the available
local source `/home/ubuntu/c1-stacks-review/etale.tex:1758` (the repository's
literature/stacks-project checkout is absent). This states exactly the finite
unramified decomposition into closed immersions after an étale neighbourhood.
The node already correctly allows a residue-field extension; no correction is needed.

Hypothesis and clause correspondence:

- Schemes Y and X and their morphism: `{X Y : Scheme.{u}} (f : Y ⟶ X)`.
- Finite: `[IsFinite f]`.
- Unramified: `[LocallyOfFiniteType f]` and
  `[IsOpenImmersion (pullback.diagonal f)]`, precisely the conjunction recorded
  in def-weil-unramified-morphism. No stronger finite-presentation assumption.
- Arbitrary target point: `(x : X)`.
- Étale neighbourhood: `∃ (U : Scheme.{u}) (g : U ⟶ X), Etale g ∧ ...`.
- Point over x: `∃ (u : U), g u = x ∧ ...`. There is no assertion about residue fields.
- Finite index set J: `∃ (n : ℕ)`, with J represented by `Fin n`.
  Every finite set is bijective with some `Fin n`, so this excludes no decomposition.
- Open subschemes of Y ×_X U: `V : Fin n → (pullback f g).Opens`.
  Each is Mathlib's canonical open subscheme, with inclusion `(V j).ι`.
- Closed as well as open: `∀ j : Fin n, IsClosed (V j).carrier`.
- Pairwise disjoint: `Pairwise (fun j k : Fin n ↦ Disjoint (V j) (V k))`.
- Union the whole fibre product: `(⨆ j : Fin n, V j) = ⊤`.
- Each map to U is a closed immersion:
  `∀ j : Fin n, IsClosedImmersion ((V j).ι ≫ pullback.snd f g)`.

Dependency declarations used, with their full signatures and docstrings read:

- def-pc-scheme: `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`.
- def-weil-finite-integral-morphism: `AlgebraicGeometry.IsFinite`,
  `Mathlib.AlgebraicGeometry.Morphisms.Finite` (the integral clause is irrelevant here).
- def-weil-unramified-morphism: `AlgebraicGeometry.LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, and
  `AlgebraicGeometry.IsOpenImmersion`, `Mathlib.AlgebraicGeometry.OpenImmersion`.
- def-weil-etale-morphism: `AlgebraicGeometry.Etale`,
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- def-pc-fibre-product: `CategoryTheory.Limits.pullback` and `pullback.snd`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
- def-weil-closed-immersion: `AlgebraicGeometry.IsClosedImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.

The two imports provide these definitions transitively. `Scheme.Opens.toScheme`
and `Scheme.Opens.ι` are the existing open-subscheme construction from
`Mathlib.AlgebraicGeometry.Restrict`, also read. No dependency record was unusable.

Edge cases checked: n = 0 is allowed, with empty supremum bottom, and the covering
condition then forces the pullback to be empty. An empty source or a point outside
the image can therefore be handled. An empty target makes the point binder vacuous.
Empty individual pieces are permitted. No connectedness, nonemptiness of the fibre,
Noetherian condition, or field hypothesis is imposed. Scheme universe u is arbitrary;
a natural-number-sized finite indexing loses no finite set. For Spec C → Spec R the
neighbourhood may extend the residue field, as required by the node.

Searches made (2026-10-11):

- msearch.py leanfinder, query “A finite unramified scheme morphism splits etale
  locally as a finite disjoint union of closed immersions”: eight results, concerning
  Etale/IsEtale, formally unramified and smooth criteria; no decomposition statement.
  The remote semantic index uses the old name IsEtale, whereas the actual pinned
  Mathlib declaration is Etale; the source was checked directly.
- msearch.py loogle, query “AlgebraicGeometry.IsFinite,
  AlgebraicGeometry.IsClosedImmersion”: three results, closed immersions finite,
  and finite plus mono characterizations; no match.
- msearch.py grep, query `unramified.*(local|split)|finite.*unramified|04HJ`,
  Mathlib/AlgebraicGeometry: ten hits, étale criteria and formally unramified
  diagonal/local-ring results; no scheme decomposition.
- rg over WeilConjectures and lean/Sheaf for
  `finite.*unramified|unramified.*(local|split)|lem-weil-pbc-finite-unramified-etale-local`:
  tangent criteria, descent, local-ring results, and unrelated unramified characters;
  no existing declaration for this node.
- Exact chosen-name search over Mathlib, WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json for `finite_unramified_etale_local|exists_etale.*closed`:
  no hits.

The docstring carries all five DAG proof steps and their named inputs. No new nodes,
dependency modules, statement corrections, or disputed statements.

## Second reading by F1

I independently read the node, its five proof steps, all six statement-dependency
nodes, and the module. Source: Stacks etale.tex, Lemma 04HJ,
`lemma-finite-unramified-etale-local`, with its proof and the preceding 04HI,
in `/home/ubuntu/c1-stacks-review/etale.tex:1758`. The chapter's Conventions
explicitly say Noetherian hypotheses are reiterated when needed; 04HJ has none.
The repository literature checkout is absent; this local source contains the
named statement and proof. No stage-2 statement correction is present or needed.
The earlier stage-1 correction allowing residue-field extensions is already
part of the base statement and agrees with 04HJ.

Object, hypothesis, and conclusion inventory, with Lean correspondence:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| Schemes Y and X | `{X Y : Scheme.{u}}` | Exact, arbitrary schemes |
| Morphism f from Y to X | `(f : Y ⟶ X)` | Exact orientation |
| f finite | `[IsFinite f]` | Exact affine-local module-finiteness |
| f unramified | `[LocallyOfFiniteType f] [IsOpenImmersion (pullback.diagonal f)]` | Exact conjunction from def-weil-unramified-morphism |
| Every target point x | `(x : X)` before the existential conclusion | Exact quantifier order |
| An etale neighbourhood U with g to X | `∃ (U : Scheme.{u}) (g : U ⟶ X), Etale g ∧ ...` | Exact |
| A point u over x | `∃ (u : U), g u = x ∧ ...` | Exact; no residue-field equality imposed |
| A finite indexing set J | `∃ (n : ℕ)` and `Fin n` | Exact up to reindexing any finite set by its cardinality |
| Open subschemes of Y times_X U | `V : Fin n → (pullback f g).Opens` and `(V j).ι` | Exact canonical restrictions of the fibre product |
| Each piece also closed | `∀ j : Fin n, IsClosed (V j).carrier` | Exact clopen condition |
| Distinct pieces disjoint | `Pairwise (fun j k : Fin n ↦ Disjoint (V j) (V k))` | Exact; disjointness in the opens lattice is disjointness of carriers |
| Union equals the whole pullback | `(⨆ j : Fin n, V j) = ⊤` | Exact union-cover condition |
| Every piece maps to U by a closed immersion | `∀ j : Fin n, IsClosedImmersion ((V j).ι ≫ pullback.snd f g)` | Exact composite with the second projection |

I opened the dependency declarations in the pinned Mathlib, rather than relying
on their names. Scheme.lean:42,74 defines locally affine locally ringed spaces
and their morphisms; Finite.lean:39 defines affine maps finite on affine opens;
FiniteType.lean:43 defines local finite type on affine patches. OpenImmersion.lean:38
uses the locally ringed space open-immersion predicate. Etale.lean:41 defines
affine-locally etale ring maps, and its :140 characterization gives flatness,
formal unramifiedness and local finite presentation, agreeing with the dependency.
ClosedImmersion.lean:45 is a closed embedding with surjective stalk maps, matching
the closed-immersion dependency. HasPullback.lean:95,111,115,128 gives the chosen
pullback, its projections and universal property. Restrict.lean:46,52 provides
the open subscheme and its inclusion. All dependencies are usable as recorded;
there is no private replacement, new definition node, or dependency module.

Edge cases: `n = 0` is permitted; the empty supremum is bottom, so the cover
requires the pullback to be empty. This includes empty Y and x outside f's image.
Empty X gives no x, so the assertion is vacuous. Empty pieces are permitted.
No ring, field, characteristic, connectedness, Noetherian, finite-presentation,
or nonempty-fibre hypothesis is added. `u` is an explicitly declared arbitrary
universe; both schemes can be placed in a common universe, and open restrictions,
pullbacks and the etale neighbourhood remain in it. Finite indexing by `Fin n`
does not restrict an indexing universe. In particular Spec C over Spec R can use
a neighbourhood extending the residue field. All variables are visibly bound.

Independent searches (2026-10-11), using different wording from the worker:

- msearch leansearch: "A finite unramified map of schemes admits near each base
  point an etale cover splitting its source into clopen pieces that are closed
  immersions". Service returned Internal Server Error; recorded unavailable,
  with no mathematical verdict assigned to it.
- msearch loogle: `AlgebraicGeometry.IsFinite, AlgebraicGeometry.Etale`.
  One hit: `AlgebraicGeometry.exists_etale_isCompl_of_quasiFiniteAt`.
  I opened ZariskisMainTheorem.lean:49-53: it gives one complementary open pair,
  a finite map on one piece and a point lifting x. It neither splits all pieces
  nor gives closed immersions to the neighbourhood, so is not this statement.
- msearch leanfinder: "An unramified finite scheme map becomes a union of closed
  embeddings after changing the base by an etale neighbourhood". Eight hits:
  etale composition/cancellation and formally unramified diagonal criteria;
  no decomposition theorem. The index uses the old IsEtale alias; the actual
  pinned declaration Etale was read directly.
- msearch grep in Mathlib AlgebraicGeometry:
  `decomposition|disjoint.*closed|closed.*disjoint|04HJ`.
  Only an unrelated DirectSum.Decomposition use in ProjectiveSpectrum/Scheme.
- rg in WeilConjectures, repository lean/Sheaf and dag/lean_names_upstream.json:
  `finite.*unramified|unramified.*finite|04HJ|etale.*decompos|closed_immersion_decomposition|lem-weil-pbc-finite-unramified-etale-local`.
  Hits were ring-theoretic unramified results, diagonal criteria, and the
  stronger-hypothesis finite-etale splitter citing this node in its docstring;
  no existing declaration for this finite-unramified statement.

The docstring follows all five node steps: finite fibre and separatedness;
04HI decomposition with remainder; closed image of the remainder; shrinking
the etale base and identifying the pullback; restricting the pieces and
base-changing their closed immersions. Both docstrings name 04HJ and the
blueprint id. The imports supply the finite and etale predicates and their
dependencies. There is one named theorem with proof `sorry`, no definitions,
instances, other proof bodies, or unbound variables. No mismatch was found;
I changed only this report by appending the independent reading and searches.

Validation: scompile.py compiled the sole module on the server in 1.7 seconds,
exit code 0, with no diagnostic warnings or errors. The node's lean.statement
is verbatim the theorem signature before `:=`; the declaration and node record
were left unchanged.
