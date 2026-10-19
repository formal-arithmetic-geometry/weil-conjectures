## Worker report

The shared `newtargets-dag` base already contains the complete Q68 stage-2
statement for `lem-pur-system-clopen-tensor-compatibility`, with module
`Sheaf.Paper.SystemClopenTensorCompatibility` and declaration
`WeilConjectures.SystemTensorMate.system_clopen_tensor_compatibility`. This Q70
packet preserves that node and declaration verbatim; it introduces no new node,
changes no statement, and supplies no proof beyond the declaration's `sorry`.
The module compiles cleanly through the prescribed `scompile.py` wrapper.

The declaration renders the node hypotheses as follows. `K : FiniteFieldDatum`
supplies the fixed finite field, characteristic, and algebraic closure;
`[Fact l.Prime]` and `_hl : l ≠ K.p` give the prime and characteristic
conditions. `E : Type (u + 1)`, `[Field E]`, `[Algebra ℚ_[l] E]`, and
`[FiniteDimensional ℚ_[l] E]` give the finite extension. The coefficient
sequence and strict semilinear system categories are provided by
`TensorOperations l E`; `H : D l E A` and `Q : D l E F` are arbitrary unbounded
system-derived inputs.

The schemes `A B C F : Scheme.{u}` carry the four `Over (Spec (.of K.k))`
instances and the separated, locally finite type, and quasi-compact instances
on their structural maps. The maps `k : A ⟶ B`, `r : A ⟶ C`, `p : B ⟶ F`, and
`i : C ⟶ F` carry the stated `IsOver` instances. The hypotheses
`[IsOpenImmersion k]`, `[IsOpenImmersion i]`, `[QuasiCompact k]`,
`[QuasiCompact i]`, `[IsProper r]`, `[IsProper p]`, and
`h : k ≫ p = r ≫ i` are exactly the geometric square assumptions; no
cartesian-square assumption is added.

The conclusion is the displayed equality in the system derived category. The
left composite is the open tensor comparison `o.delta i`, followed by the
open extension of `o.projection r`, followed by the proper/open mate
`o.gamma`. The right composite is the tensor of `o.gamma` with the identity,
followed by `o.projection p`, followed by the derived direct-image map of the
open comparison and square pullback comparison. The arguments to `gamma` and
the target objects are exactly those in the node, so the common source and
 target are the prescribed `i_! R_r H ⊗ Q` and `R_p k_!(H ⊗ P_r P_i Q)`.
No invertibility of either `gamma` or `projection` is asserted, and equality is
before finite evaluation or inverse limit.

Dependency declarations read:

- `Sheaf.Paper.FiniteFieldFiber`, `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, whose coefficient
  extension data supplies the finite extension inputs.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`, `AlgebraicGeometry.Scheme.ProEt`
  for the small pro-etale site.
- `Sheaf.Paper.SemilinearDerivedSections`, including
  `WeilConjectures.SemilinearSections.D` and the published strict-system model.
- `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus`, including the
  clopen component projection and its normalization declarations.
- `Sheaf.SixFunctors.OpenTensorNormalization`, including the normalized open
  tensor comparison.
- `Sheaf.Paper.SystemTensorMateArrows`, including
  `WeilConjectures.SystemTensorMate.TensorOperations`, `pushDerived`, `gamma`,
  `projection`, `delta`, and `square`.
- `def-weil-scheme-morphism-properties` and `def-weil-size-convention` are
  convention nodes and contribute their stated instance and universe
  requirements. The proof-only `lem-sf-proper-open-projection-mate` has no
  recorded Lean module and is cited only in the declaration's proof docstring.

Edge cases checked against the statement and declaration include identity,
empty, and disjoint-component open immersions; the zero input objects;
sequence exponent one; non-flat quotient transitions; arbitrary non-cartesian
squares satisfying the displayed commutativity; and arbitrary unbounded
systems. The clopen projector is allowed to be zero on the complementary
component. No evaluation-faithfulness or boundedness premise is introduced.

Searches made for an independent declaration or duplicate notion:

- `msearch.py ... leanfinder "proper open tensor mate interchange strict
  semilinear systems"`: eight general tensor/mate hits, no exact declaration.
- `msearch.py ... loogle "mateEquiv, tensor, open extension, derived category"`:
  query rejected by Loogle syntax; no absence conclusion was drawn.
- `msearch.py ... grep "clopen.*tensor|proper.*open.*tensor" CategoryTheory`:
  zero hits.
- `rg` over the upstream `WeilConjectures` checkout and this project's
  `lean/Sheaf` found only the published
  `system_clopen_tensor_compatibility` declaration; no second independent
  statement was found.

There is no `STATEMENT-DISPUTED` issue, no source correction, and no dependency
module or new definition node in this packet. The packet is a duplicate handoff
because the item was already promoted on the shared base by Q68.

## Second reading by Q70

Independent maintainer second reading, 2026-10-18, of immutable delivery
9bb0c3484e49250ecce853e931f49c88b7e2913b. This section records the maintainer's
reading; it does not claim a second Q70 worker participated.

I read the item node, all ten statement-dependency nodes, the delivered module,
and the actual declarations underlying the operations in the read-only group
clone. I checked the sources more-etale.tex, lemma-shriek-proper-and-open
(Tag 0F7B), sites-modules.tex, lemma-j-shriek-and-tensor (Tag 0E8I), and
sites-cohomology.tex, equation-projection-formula-map (Tag 0B56).
The system identity is explicitly an agent refinement, not an unbounded
pro-etale-system theorem attributed to Stacks. The proof-only node
lem-sf-proper-open-projection-mate has the requisite intrinsic system clause.

Hypothesis and conclusion audit:

- Finite-field data: K : FiniteFieldDatum supplies the finite base field and
  its algebraic closure. Fact l.Prime and _hl give the coefficient prime and
  its distinction from the characteristic. E, Field, Algebra and
  FiniteDimensional supply precisely the finite extension. The existing
  Padic coefficientExtensionIntegers, coefficientExtensionUniformizer,
  coefficientExtensionRing and coefficientExtensionTransition give the
  valuation ring, quotients and quotient transitions.
- Site and categories: SystemTensorMate.R, S and D use the actual constant
  coefficient sheaves on the vertical sequence site of Scheme.ProEt.
  Natural-number index n means positive exponent n+1. D is the ordinary
  unbounded derived category of module systems, not systems in derived
  categories. The dependency's semilinear module and tensor models are reused.
- Operations: TensorOperations presents exact ordinary left adjoints to the
  specified sectionwise direct image, exact open extension, and the existing
  modeled derived tensor. Its ordinary_unit fixes the tensor comparison by
  the scalar-normalized lax tensor map. TensorComparisonModel fixes its
  derived comparison on total summands of flat-term K-flat representatives.
  Quantifying over these presentations adds no mathematical restriction:
  tensorOperations_nonempty supplies existence, and their universal and
  representative normalizations specify the canonical operations.
- Geometry: A, B, C, F represent the node's A, B, C, D. All four Over
  instances and separated, locally finite type and quasi-compact structure
  maps are present. k, r, p, i have the four IsOver instances, the two
  quasi-compact open hypotheses, two proper hypotheses, and commutativity h.
  There is no cartesian-square, boundedness, flatness, Tor, constructibility,
  normalization or etale-origin hypothesis.
- Clopen arrow: ordinaryAlpha is selected from alpha_existsUnique, whose
  open-restriction equation fixes the clopen component projection. The
  clopen lift follows from squareLift_clopen; its complement contributes
  zero. alpha localizes that actual ordinary transformation. gamma is its
  mate under the canonical derived adjunctions, in the stated unit/alpha/
  counit order. This is a unique characterization, not an arbitrary arrow.
- Projection and open tensor: projection is literally the transpose of mu
  followed by counit tensor identity. delta is the inverse of the specified
  open-unit transpose deltaInv. OpenTensorNormalization covers arbitrary
  unbounded systems and arbitrary coefficient transitions.
- Equality: the left composite is delta_i, J_i(projection_r), gamma at
  H tensor P_r P_i Q. The right composite is gamma_H tensor identity,
  projection_p, then R_p(delta_k followed by the tensor of square.hom).
  square has orientation P_k P_p -> P_r P_i, so both composites have exactly
  the source and target in the node. Neither gamma nor projection is
  inverted. This is an equality before evaluation or inverse limit.

Edge cases: empty schemes and opens, identity opens and vertical maps,
noncartesian proper/open squares, refinement squares selecting one clopen
component, zero H or Q, exponent one, nonflat quotient transitions, and
unbounded inputs are included. Exponent zero is not a coefficient level of
this node. Scheme/site object and morphism universes remain u+1 and u;
coefficients live in u+1 and the standard derived category in u+2. No equality
of site object and morphism universes is imposed. Finite extensions may be
represented in this coefficient universe by the usual lift; the size
convention is respected. autoImplicit is false and all variables are bound.

I independently searched the group lean/Sheaf tree, upstream WeilConjectures,
and Mathlib/CategoryTheory with proper/open/projection and clopen/tensor
variants. The existing same-node Q68 declaration is the one being handed
on, not a new second definition; other hits are related finite or generic
mate constructions. The worker records semantic, Loogle and textual searches,
including the rejected Loogle query without drawing an absence conclusion.
All ten statement dependencies have usable recorded interfaces or explicit
convention records. There are no new nodes, dependency repairs or statement
corrections in this delivery.

The module and theorem docstrings give source places, the blueprint id and
all four proof steps. Its only theorem proof is sorry. The normalized theorem
signature agrees verbatim with lean.statement (ignoring whitespace layout),
and all lines are at most 100 characters. No hollow definition, arbitrary
comparison, pro-etale substitute, or dropped infinity/dg/model machinery is
introduced. Intersection of the snapshot nodes' statement/proof dependency
ids with origin/newtargets-dag:coord/route-pivot-dropped.txt is empty. The
item has no route-pivot repair note at that ref.

Compiler reproduction: ran
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q70
lem-pur-system-clopen-tensor-compatibility
snapshot/lean/Sheaf/Paper/SystemClopenTensorCompatibility.lean
from the review directory, passing the immutable file. Exit status 0; output
reported sandbox Sheaf/Stage2/Sandbox0.lean in 15.5 seconds and library
Sheaf/Paper/SystemClopenTensorCompatibility.lean in 16.0 seconds, with no
diagnostics. The installed wrapper currently delegates to its server overlay
compiler, which reports a private .lbuild; this was wrapper-managed compilation,
not a direct ssh invocation or a live/global build. The original report's
compile claim is therefore reproduced. No Lean source changed in this review.

Finding and repair: H11 (also the substantive report requirement of H1): the
original second-reading section was only a disclaimer that no reading had
occurred. Replaced that placeholder with this actual independent reading.
No mathematical or Lean correction was needed. The complete replacement
report is supplied as a stage-2 merge_delivery.py report fix.
