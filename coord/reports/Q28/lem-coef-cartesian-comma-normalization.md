## Worker report

This stage-2 delivery states `SSet.Enhanced.cartesian_comma_normalization` in
`Sheaf.CategoryTheory.CartesianCommaNormalization`. Its proof is `sorry`; the eleven
helper definitions have real data. There is no statement correction, dependency repair,
new DAG node, or statement dispute. The node copy changes only `lean`.

The earlier worker's stale-dispatcher diagnosis confused stages: Q02's reviewed merge
is the stage-1 split. The current node is split and reviewed but has no `lean` record.
This delivery retains Q02's statement and eight proof steps verbatim.

Hypothesis and clause correspondence:

| Node | Lean rendering |
| --- | --- |
| Ordinary category A, one containing universe | `{A : Type u} [SmallCategory A]`, with every simplicial construction in `max u v`. Independent `v` permits R to be larger than A. An ordinary category with different initial object/morphism universes can be placed in their maximum; no equality with R's universe is required. |
| T has objects u:a→b and squares u=g u' f | Existing `TerminalTwistedArrow`, `TerminalTwistedSquare`, and `terminalTwistedArrowCategory`: their fields are source, target, arrow, sourceMap, targetMap, and `sourceMap ≫ y.arrow ≫ targetMap = x.arrow`. |
| K=N(T), B=N(A)^op, π sends the target backwards | Existing `terminalTwistedIndex`, `terminalTwistedBase`, and `terminalTwistedProjection`. The base is the ordinary nerve of Aᵒᵖ, the standard representation of N(A)^op. ULift changes simplex universes only. |
| p:R→B is cartesian | `[Quasicategory R]`, `p`, and `hp`. The existential Quasicategory instance on B is a proposition expressing the existing fibration predicate, not additional mathematical data or a restriction on A. |
| k:K→R, pk=π | `k` and `hk : k ≫ p = terminalTwistedProjection A`. |
| Every (1_a,g) is sent to a cartesian edge | `hcart`, with all a,b,d,x,y,g and the equality `y ≫ g = x`; `IsCartesianEdge` is applied to k of exactly the square `(1_a,g)`. |
| No terminal-object hypothesis | No t_a, IsTerminal, terminal preservation, or terminal-resolution predicate occurs in the signature. Only the index definitions are reused from the parent module. |
| r lies over c | `c`, `r`, and `hr : p.app _ r = terminalTwistedBaseVertex c`. |
| R_{r/} consists of maps Δ⁰⋆Δᵐ→R with apex r | `coherentJoinCoslice (SSet.yonedaEquiv.symm r)` in `normalizationComma`; its existing projection is restriction to the remaining block. |
| C_r=K×_R R_{r/} | `normalizationComma` is the actual categorical pullback; simplicial-set pullbacks are degreewise. `normalizationCommaIndex` is its first projection. |
| A vertex is (u,β), with projected β=w^op | `normalizationCommaLeg` reads β by evaluating the join map on `joinPointTopSimplex 0`. The vertex clause quantifies x and w and identifies them by its two displayed equalities. These are coordinates for every vertex, not extra hypotheses: the nerve supplies x, and hk/hr make the endpoints of pβ precisely c and x.target, uniquely determining w. |
| There is a functor H and η:H→id | Existential simplicial maps `H` and `η : normalizationComma k r ⊗ Δ[1] ⟶ normalizationComma k r`, with `ι₀ ≫ η = H` and `ι₁ ≫ η = 𝟙 _`. By the existing internal-Hom convention this cylinder map is exactly a coherent transformation. |
| H(u,β)=(wu,h), p(h)=1_c | The first two conclusions for every vertex: its projected index equals `normalizedTwistedObject x w`, whose arrow is `x.arrow ≫ w`, and its leg projects to `mk₁ (𝟙 (op c))`. h is the actual `normalizationCommaLeg` of H(z), not an unrelated existential edge. |
| η has twisted pair (1_a,w) and triangle β≃k(1_a,w)h | The next equality identifies the index of `normalizationComponent η z` with `normalizationTwistedComponent x w`. Its second pullback coordinate is an actual join map Δ⁰⋆Δ¹→R. Its faces are β and h by the endpoint equations, and its remaining face is k of the displayed square by the pullback equation. This retains the triangle itself, not only its homotopy class. |
| For a comma edge (f,g), w'=wg | The edge clause gives `w' = f.targetMap ≫ w`, the same composition in Lean order. Its antecedents identify the projected edge and both endpoint base legs; they add no restrictions on which comma edges are covered. |
| H sends that edge to (f,1_c) | The existential `g : normalizedTwistedObject x w ⟶ normalizedTwistedObject y w'` has `g.sourceMap = f.sourceMap`, `g.targetMap = 𝟙 c`, and its nerve edge is the actual projected H(z). The existential avoids dependent endpoint transports, and fixes both maps completely. |
| Every face, degeneracy and higher coherence is retained | H and η are actual simplicial maps; the comma is the join pullback in all degrees. No independent objectwise choices or homotopy-category substitute occur. |
| For every β, the space of factorizations with triangle is contractible | The vertex clause asserts `KanComplex` and `IsContractible` of `normalizationFactorizationSpace p β e`, with e exactly k(1_a,w). KanComplex renders “space”; IsContractible uses the dependency's weak-contractibility convention. |

The last construction is explicit. An n-simplex is an `(n+2)`-simplex of R, i.e. a
map Δⁿ⋆Δ¹→R. Its face omitting the penultimate vertex is the repeated β, its last
edge is e, and its whole image under p is the repeated base triangle with identity
first leg. The initial Δⁿ is constant at r because it is already the initial face
of repeated β. Thus vertices are precisely pairs (h, triangle β≃eh) with p(h)=1_c.
`normalizationTriangleOrdinals` appends the two fixed final vertices; its functor
laws are proved as well-definedness. `normalizationFactorizationSubcomplex` imposes
the fixed-boundary equations after every simplex operator, so its operators are
restrictions. These conditions are exactly the same boundary restrictions on all
faces and degeneracies, with no extra filler choices or constraints on the interior.
For n=0 the three equations say δ₁σ=β, δ₀σ=e and pσ=σ₀(pβ).

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: Mathlib SSet, Quasicategory,
  standard simplices, nerve, KanComplex and monoidal products are publicly supplied;
  `SSet.Enhanced.appendLast` and `SSet.Enhanced.IsContractible` are used directly.
  Its recorded main declaration `SSet.Enhanced.coneCategory` and its docstring were
  read; that interval-comma construction is deliberately not substituted for this
  node's ordered-join comma.
- `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases`: publicly supplies
  the original `SSet.Enhanced.cartesianFibration` and `IsCartesianEdge` from
  `InfinityFibrations`. The recorded `cocartesianFibrationOver` is not used to change
  the cartesian/quasicategory hypotheses here.
- `Sheaf.CategoryTheory.RelativeCosliceLeftFibration`: `CoherentJoinSimplex`,
  `coherentJoinCoslice`, and `coherentCosliceProjection`, with exactly their full
  join-extension and initial-boundary definitions. Its public imports supply
  `orderedJoinFunctor`, `orderedJoinInl`, `orderedJoinInr`, and `joinPointTopSimplex`.
- `Sheaf.CategoryTheory.CartesianTerminalTwistedResolution`: only
  `TerminalTwistedArrow`, `TerminalTwistedSquare`, their category instance,
  `terminalTwistedBase`, `terminalTwistedIndex`, `terminalTwistedProjection`, and
  `terminalTwistedBaseVertex`. Their full source was opened. None of the parent's
  existence, uniqueness, terminal or finality assertions is used as a hypothesis.

Proof imports retain the already-stated DAG proof dependencies:
`Sheaf.AlgebraicTopology.SelectivelyMarkedTerminalCylinder`,
`Sheaf.CategoryTheory.InfinityCocartesianCompositionInitiality`,
`Sheaf.Paper.TrivialKanHomotopyEquivalence`, and
`Sheaf.CategoryTheory.SimplicialHomotopyEquivalenceWeak`.
The trivial-Kan definition and monomorphism-lifting dependency are Mathlib's
`SSet.modelCategoryQuillen.I.rlp` and `SSet.rlp_monomorphisms`, supplied transitively.
`lem-coef-cartesian-marked-slice-restriction` has no published Lean record yet;
it is a proof dependency only, so its import is omitted, not replaced by a hypothesis.

Import-cycle notice for the maintainer: the parent module already owns the ordinary
index definitions needed here. Redefining them would violate one-definition-per-notion.
This module therefore imports that module, and does not add the downstream theorem
as a DAG statement dependency. In accord with stages/2-statements.md §3 rule 7,
the parent's future proof-only import of this module must be omitted, since it would
close an import cycle. Its eventual proof can use this lemma after an authorized
shared-definition extraction; this delivery neither edits the parent's node/module
nor waits on its theorem. This is a library packaging issue, not a mathematical
circularity: the present statement uses only the real index constructions.

Edge cases checked before writing: empty A gives no c or r in a specified fiber;
an empty comma over a nonempty base still has its unique empty H and η; no
inhabitance of the comma is assumed. For the terminal A the normalization is an
identity-index operation and requires no terminals in R. If w is an identity, e is
the image of a degenerate index edge, and its triangle space still keeps β and
the specified degenerate base triangle. Ordinary nerves of fibered categories give
the familiar unique ordinary cartesian factorization. For p=id the prescribed
base simplex determines the factorization simplex, which checks orientation and
nonemptiness. In degree zero the factorization boundary is the expected triangle;
for higher degrees the whole initial face is fixed, not only its vertices.
Independent u and v cover the required large R case.

Searches performed:

- `msearch.py leanfinder`, query “Coherent normalization of the twisted arrow comma
  quasicategory over a cartesian fibration with cartesian source fixed edges”:
  eight hits, including `CoGrothendieck.domainCartesianLift`, `Nerve.quasicategory`
  and strict-Segal constructions. Opened Grothendieck.lean and HasFibers.lean;
  their ordinary cartesian lifts/factorization are not coherent comma normalization.
- `msearch.py loogle`, query `"StructuredArrow", "Cartesian"`: zero hits.
- `msearch.py grep`, query `cartesian.*normaliz|normaliz.*comma|TwistedArrow`:
  zero Mathlib hits.
- `msearch.py leansearch`, query “Cartesian fibrations yield a coherent endpoint
  normalization functor on a twisted arrow join comma with contractible spaces of
  factorizations”: eight hits about ordinary fibered categories and unrelated
  normalization/factorization; none is the quasicategory statement. In particular
  `HasFibers.fiber_factorization` only gives an ordinary single-arrow factorization.
- `rg` of Mathlib CategoryTheory for twisted-arrow terminology found no ordinary
  twisted-index definition. `rg` of the source WeilConjectures tree for the exact
  node id and twisted normalization/comma terminology found no matching theorem.
- `rg` of `lean/Sheaf/CategoryTheory` found the parent's ordinary twisted-index
  definitions and the different edgewise-subdivision `twistedArrow`. The parent
  helper definitions are reused. Its terminal-resolution finality theorem has
  terminal hypotheses and is not this statement. `CartesianMappingFiber` concerns
  incoming mapping spaces, not the entire join comma normalization.
- `rg` of `dag/lean_names_upstream.json` found no duplicate of the reused ordinary
  index or the new declaration; `rg` of both source/project trees for the new helper
  names found no duplicates. No new definition node is needed: every helper here
  is an explicit construction introduced by this item's own statement.

Validation: the prescribed `scompile.py` compiled the delivered file in both sandbox
and library modes, each in about two seconds, with no errors or warnings. Every
variable and universe is explicitly bound and `autoImplicit` is false. Only the
main theorem has `sorry`. The prescribed delivery dry run passed server preflight
and both compiles at e9a3804cba; the delivery wrapper rechecks the final packet.

## Second reading by Q28

Independent maintainer reading of immutable delivery
302744e1d194020e8f8d100096397c2482c1133b, 2026-10-17. This section replaces the
worker's placeholder; the Worker report above records the original delivery.

I opened the item, all three statement dependencies and their Lean modules, the
reused ordinary twisted-index declarations, the blueprint source place, and HTT
Proposition 3.1.1.11 (printed p.151) and Lemma 3.2.1.9 (printed p.173).
The blueprint source is an ancestry location, rather than a verbatim statement of
this agent-extracted simplicial lemma. The explicit node and its eight proof steps
supply the statement, and the HTT results support the full coherent construction.
Kerodon 01BZ confirms the relative coslice convention.

Clause checks against the actual declarations:

- A and its arrows: `TerminalTwistedArrow` has source, target and an actual arrow;
  `TerminalTwistedSquare` has precisely f forwards and g backwards, with
  `sourceMap ≫ y.arrow ≫ targetMap = x.arrow`. Its category composes these maps.
  `terminalTwistedIndex`, `terminalTwistedBase` and `terminalTwistedProjection`
  are the lifted ordinary nerves and target projection. No terminal assumption
  accompanies any of those definitions.
- R is a quasicategory; p is cartesian by the existing horn/lift predicate in
  `InfinityFibrations`, reexported by the recorded dependency module. `hp`'s
  existential base instance expresses the same condition on the ordinary nerve.
  `hk` is precisely pk=π. `hcart` ranges over every source-fixed square, and its
  commutativity proof field follows from the supplied equality h.
- c, r and `hr` are exactly a specified point of the c-fiber. There is no terminal
  object, terminal-preservation, inhabitance or smallness assumption on R over A.
- `normalizationComma` is the actual pullback along the join coslice's last-block
  projection. Its vertex leg is evaluated on the mixed join edge, so it is β.
  Every such vertex has coordinates x and w in the two ordinary nerves. Thus the
  coordinate implications in the theorem cover every object, without new hypotheses.
- H is an actual simplicial endomap. η is an actual cylinder map with endpoints H
  and identity. Its component's pullback coordinate is a join Δ⁰⋆Δ¹ triangle.
  The index equality fixes `(1,w)`; the endpoints and pullback equation fix β, h
  and k(1,w), respectively. This supplies the triangle, rather than only its class.
- H's index is x.arrow≫w and its leg projects to the identity at c. The arrow clause
  gives `w' = f.targetMap ≫ w` and a square with source map f.sourceMap and target
  map identity. These are exactly w'=wg and `(f,1_c)` in Lean composition order.
  Faces, degeneracies and higher compatibility are retained by the simplicial maps.
- For every β the actual triangle space is asserted Kan and weakly contractible.
  In degree n its data are one R_(n+2) simplex; deleting vertex n+1 leaves repeated
  β, its final edge is e, and its entire p-image is the prescribed collapsed β.
  The first equation fixes the entire initial Δⁿ at r. At n=0 these become
  δ₁σ=β, δ₀σ=e, pσ=σ₀(pβ). Double appendLast gives exactly join operators.
  Requiring the conditions after all operators does not add data or restrictions:
  the fixed faces, final edge, and collapsed base commute with each operator.
- Independent u and v with max u v allow R to be larger than A. A category with
  differing original object and morphism universes can be placed in their maximum;
  there is no forced equality with the total-space universe. All variables are bound.

Edge cases: empty A gives no specified c; empty comma requires no inhabitance and
has the unique empty maps H and η; the cylinder-lift proof fixes r even there.
For a terminal A, arbitrary fibers R are allowed. Identity w gives a degenerate
index edge, which remains cartesian. For p=id, the fixed base determines the triangle.
For ordinary nerves, the triangle records ordinary cartesian factorization. Degree
zero and all higher repeated initial faces have the expected orientation.

Independent rg searches in Mathlib CategoryTheory, upstream WeilConjectures
CategoryTheory and the group's Sheaf CategoryTheory for twisted-comma,
comma-normalization, and the helper names found the reused ordinary index and
related mapping-fiber theorem, but no duplicate of this coherent statement or
factorization space. The existing ordinary HasFibers/Grothendieck constructions
are not arbitrary join-comma normalization. The worker's LeanSearch, Loogle,
LeanFinder and grep records were read. Independent LeanSearch queried "a functor
on a comma infinity category normalizes codomains by cartesian factorization";
its five hits were ordinary Comma.map/full_map/commaCategory/faithful_map/preLeft.
Independent Loogle queried `"IsCartesian", "factor"` and returned no hits.
Mathlib's Comma.Basic and HasFibers.fiber_factorization were opened and are
ordinary categorical constructions, not this quasicategorical normalization. No new notion or prerequisite is missing
from the statement. The unpublished marked-slice theorem is a proof dependency,
not an additional hypothesis needed to state this theorem. The documented future
proof-import cycle is permitted by stages/2-statements.md rule 7.

Mechanical repairs: H6's no-local-proof gate was not literally satisfied: the
component square, double-append functor laws, boundary subcomplex stability and
index bounds had inline proofs; hcart also used inline simplification. The fixes
extract seven named well-definedness obligations, all with sorry proofs and
source/blueprint/proof docstrings. Definitions retain all their explicit data.
The main theorem changes only its square proof term; its mathematical type is
unchanged. All declarations are listed in the complete replacement lean record,
whose statement is the exact replacement signature. No DAG statement correction
or universe repair is needed. The original second-reading placeholder (H11) is
replaced by this actual independent reading.

Validation: the immutable module compiled via the prescribed scompile.py with exit
0 and no diagnostics, sandbox 2.6 s and library 2.8 s. The replacement compiled
via the same wrapper with exit 0 and no diagnostics, sandbox 2.6 s and library
5.3 s. The local-overlay launcher wrapper was also attempted; it rejected a
replaced local_artifacts overlay and requested server confirmation; that fallback
completed successfully, compiling the replacement in 2.7 s without diagnostics.
The read-only `stage2_delivery.check_lean_text` and `check_record` checks returned
empty failure lists; the signature was also compared byte for byte. No global
build, direct SSH command, project-clone edit, Git mutation, live Lean write,
claim, merge, or delivery was performed. The module has no overlong lines and
all theorem bodies, including well-definedness obligations, are exactly sorry.
