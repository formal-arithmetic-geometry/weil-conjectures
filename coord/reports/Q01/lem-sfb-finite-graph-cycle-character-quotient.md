## Worker report

The module Sheaf.Combinatorics.FiniteGraphCycleCharacterQuotient states
FiniteGraphCycleCharacter.quotientEquiv, with its proof postponed by sorry.
It gives the group isomorphism, its evaluation formula, signed permutation
compatibility, and the orientation-change identifications. Its three helper
definitions have real data: boundary and signedEdges use Mathlib's standard
basis and Module.Basis.constr; coboundary uses pointwise multiplication and
inversion of evaluation homomorphisms. These are constructions explicitly
introduced by the item's own statement, recorded in lean.declarations.
No additional mathematical hypothesis, new DAG node or dependency repair is needed.
Only lean changes in the item; the accepted stage-1 split is preserved.

Hypotheses and clauses, read against the node:

- Finite sets V,E are arbitrary universes u,v with [Finite V] [Fintype E].
  A Fintype is used only to write the finite evaluation product. Every finite
  edge set admits such an enumeration. [DecidableEq V] is used for the displayed
  signs; every finite set has decidable equality. Neither supplies nonemptiness
  or connectedness. Arbitrary s,t : E → V and _hne : ∀ e, s e ≠ t e give exactly
  looplessness. Distinct edge indices are never identified, allowing parallel edges.
- The free integer modules of functions are E → ℤ and V → ℤ. boundary s t is
  (Pi.basisFun ℤ E).constr ℤ applied to the difference of the standard target
  and source vectors. Thus its value on b_e is exactly b_t(e) - b_s(e).
  LinearMap.ker (boundary s t) is the integral cycle lattice H.
- A : Type w with [CommGroup A] is an arbitrary multiplicative abelian group.
  No divisibility, characteristic, torsion or field hypothesis is imposed.
- coboundary s t A is the actual homomorphism a ↦ (a(t(e))*a(s(e))⁻¹)_e,
  built from Pi.evalMonoidHom. Its MonoidHom.range is im δ; the domain of Φ
  is the Mathlib quotient group (E → A) ⧸ (coboundary s t A).range.
- Φ is a MulEquiv to Multiplicative H →* A. Multiplicative changes the notation
  of H's addition to multiplication, so these are exactly maps taking sums
  to products, with Mathlib's pointwise group law. This is the Hom group defined
  explicitly in the node (not module-linear maps into a multiplicative group).
- The first conjunct is Φ([z])(h) = ∏ e, z(e) ^ h(e), with integer exponents.
  QuotientGroup.mk' is the canonical quotient map and Multiplicative.ofAdd
  is the canonical notation-change equivalence.
- The second conjunct quantifies over σV,σE : Equiv.Perm and both possible
  ordered descriptions of unordered endpoint preservation. Looplessness makes
  these cases exclusive. The conditional is 1 precisely when
  s(σE(e)) = σV(s(e)), and -1 otherwise, exactly the node's ε.
- S is a linear endomorphism of H with ambient value signedEdges σE ε h.
  signedEdges extends b_e ↦ ε(e) b_σE(e) using the standard basis. Thus S
  asserts preservation of H by this prescribed action, rather than assuming
  or arbitrarily selecting an action. The next equation is the pointwise
  equality Φ([σ*z])(h)=Φ([z])(S h), i.e. precomposition by σ_*.
  As Φ is injective, this representative formula also implies that pullback
  respects quotient classes; it is independent of the representative z.
- The last conjunct quantifies over every orientation s',t' with unchanged
  unordered endpoints at each edge. J is the linear equivalence from the new
  cycle lattice to the old one, with diagonal coefficient η(e)=1 if s'=s
  and -1 otherwise. Ψ is the quotient group equivalence in that same direction.
  Its formula Ψ([z^η]_new)=[z]_old identifies the coordinates by inversion
  on precisely the reversed edges. The last equality asserts that
  Φold ∘ Ψ is evaluation on new cycles after transporting them by J.
  Equivalently Φnew([z])(h)=Φold(Ψ[z])(Jh), so evaluation, the signed cycle
  action and the quotient identification agree for every orientation.

Dependency declarations read and used:

- def-weil-pbc-free-module records Module.Free in
  Mathlib.LinearAlgebra.FreeModule.Basic. Its full signature and docstring were
  read: a free module has a basis indexed by an arbitrary type. The module
  imports it and uses the standard function-space basis Pi.basisFun in
  Mathlib.LinearAlgebra.StdBasis, with Module.Basis.constr from
  Mathlib.LinearAlgebra.Basis.Defs. There is no competing free-module definition.
- Mathlib.Algebra.Group.Pi.Lemmas: Pi.evalMonoidHom and MonoidHom.pi.
  Mathlib.Algebra.Group.Hom.Instances provides pointwise group operations on
  homomorphisms. Mathlib.GroupTheory.QuotientGroup.Basic provides the quotient
  group and its canonical map. Full signatures of the construction APIs were read.
- Proof dependency lem-sfb-finite-graph-incidence-inner-inverse has no Lean
  record or mathlib_match in the current DAG. It is used only in the natural-language
  proof, not as a statement hypothesis or hidden axiom; therefore no unavailable
  import is introduced. The theorem docstring records all six accepted proof steps.

Edge cases checked mathematically: empty V and E give the unique quotient
and character; empty E with isolated vertices also gives trivial groups;
a single edge gives H=0 and surjective δ; two parallel equally oriented edges
have cycles (n,-n) and evaluation (z1/z2)^n; reversing one of those edges inverts
exactly its coordinate and negates exactly its lattice coordinate. Disconnected
unions are allowed, including isolated vertices. The trivial coefficient group
and finite nondivisible coefficient groups cause no problem: the integral
retraction extends characters without divisibility. Endpoint reversal of an
edge has sign -1. Universes u,v,w are independent. All variables are explicit
and autoImplicit is disabled. No statement fault or dispute was found.

Source: read literature/stacks-project/curves.tex, lemma-glue-points (Tag 0C1M),
including its units-ratio exact sequence. This is a motivation for the auxiliary
agent-written graph assertion, as the node already explicitly records; it is
not represented as a verbatim Stacks theorem. Also read the current blueprint
unit sk-thm-sf-ctf-stability and direct-images proof (3); neither is changed.
The old Q43 report is a stage-1 split report. The stage-handoff paragraph in
coord/brief-stage2.md explicitly permits this stage-2 statement delivery.
The queue lists this item at stage 2 and its live Lean record is null.

Searches performed before writing:

- msearch.py leanfinder: "For a finite oriented graph edge labels modulo vertex
  coboundaries are characters of its integral cycle lattice". Eight hits include
  groupHomology.IsCycle₁, SimpleGraph.lapMatrix_ker_basis and CharacterModule.ofSpanSingleton.
  None states the graph quotient for arbitrary commutative coefficients.
- msearch.py leansearch: "Characters of integral graph cycles correspond to edge
  labels modulo vertex coboundaries". Eight hits concern SimpleGraph.EdgeLabeling,
  its evaluation, and TopEdgeLabeling. These do not supply this multigraph theorem.
- msearch.py loogle: "MonoidHom.pi, Pi.evalMonoidHom, MonoidHom.mul, MonoidHom.inv".
  Zero hits, unknown identifier MonoidHom.inv. Local source reading located
  pointwise inversion of MonoidHom in Hom.Instances, used directly.
- msearch.py grep: "cycle.*character|character.*quotient|incidence", Combinatorics.
  Twenty-five incidence hits include Hypergraph.Basic, Graph.Basic and unoriented
  SimpleGraph incidence notions; none is this quotient/evaluation theorem.
- rg over live lean/WeilConjectures, lean/Sheaf/Combinatorics and
  lean/Sheaf/GroupTheory for finite graph, incidence, coboundary and cycle-character
  names: only the separate graph-homology rigidity theorem concerns this graph
  context; it asserts rigidity, not the quotient. Searching WeilConjectures for
  the exact item id gave no declaration. The chosen namespace is absent from
  Mathlib, WeilConjectures, Sheaf and dag/lean_names_upstream.json.

Validation: scompile.py compiled the delivered file in module mode as both a
sandbox module and its intended library module. The first pass diagnosed a missing
Finite V on boundary; that was repaired, with the theorem's vertex enumeration
changed to Finite V. The subsequent pass compiled cleanly with no errors or warnings.
Only quotientEquiv has a postponed proof. Dry-run and delivery checks are performed
through deliver2.py; no direct Git commands or writes in the read-only project.

## Second reading by Q01

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
