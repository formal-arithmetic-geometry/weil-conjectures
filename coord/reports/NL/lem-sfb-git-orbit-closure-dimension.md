## Worker report

The module `Sheaf.AlgebraicGeometry.SemistableOrbitClosureDimension` states
`AlgebraicGeometry.semistable_orbit_closure_dimension`, with one `sorry` and no other
postponed proof. The four fully constructed helper definitions expose the orbit map,
its full topological image, the union of invariant-section nonvanishing loci, and the
same orbit as a subset of that semistable locus. These are interfaces for the notions
already in the item and its linearization dependency, not new independent notions.
All 15 proof steps of the node are reproduced in the theorem docstring.

Hypothesis and clause correspondence:

- Algebraically closed field: `{k : Type u} [Field k] [IsAlgClosed k]`.
- Matrix size: `(r : ℕ) (hr : 2 ≤ r)`, including r = 2 and every characteristic.
- G = PGL: `G : Grp (Over (Spec (.of k)))` with
  `hG : IsProjectiveLinearQuotient k r G.X`. This landed definition characterizes
  the fppf sheafification of GL modulo scalar units: natural injective homomorphisms
  from the scalar quotient and local surjectivity on every test scheme. It fixes the
  mathematical group scheme without supplying extra SL-cover data. The old free
  quotient-map and kernel-inclusion binders π and j have been removed.
- Projective finite-type scheme over k: `Z : Over (Spec (.of k))`,
  `[IsHProjective Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]`.
  H-projective is exactly the finite projective-space embedding convention of the node.
- Algebraic G-action: `a : ModObj G.X Z`, including unit and associativity laws.
- Ample linearized invertible module: `A : Z.left.Modules`, `[A.IsInvertible]`,
  `hA : Scheme.Modules.IsAmple Z.left A`, and
  `D : GroupSchemeLinearization.Linearization a A`.
- Semistable rational point: `z : PGLLinearization.fieldTest k k ⟶ Z` with
  `hz : D.IsSemistable k z`. This is the recorded positive-degree invariant-section
  definition, tested on all scheme-valued points for invariance.
- Orbit = image of the orbit map: `GITOrbitGeometry.orbit a z` is `Set.range` of
  `orbitMap`. The source `G × Spec k` is canonically G; using it avoids an arbitrary
  identification of the field-test object with the terminal object in the slice.
  This image contains all topological points, not merely its closed rational points.
- Local closedness: `IsLocallyClosed (GITOrbitGeometry.orbit a z)` in Z.
- Dimension formula: `topologicalKrullDim orbit + topologicalKrullDim stabilizer =
  topologicalKrullDim G.X.left`. This additive version says exactly dim orbit = dim G
  minus dim stabilizer: all three nonempty spaces have finite nonnegative dimensions
  under the hypotheses. No truncation of infinite dimensions or tangent-space dimension
  is used. The stabilizer is precisely `GroupSchemeLinearization.stabilizer a k z`,
  the existing equalizer, retaining its nilpotents.
- Unique closed orbit in the closure INSIDE semistability: `∃! O : Set (semistableLocus D)`
  such that O is `semistableOrbit D y` for a semistable k-point y, `IsClosed O`, and
  `O ⊆ closure (semistableOrbit D z)`. The closure and closedness are in the subtype
  topology of the semistable locus. Uniqueness is of the orbit subset, not of its
  rational representative (which would be false).
- Every boundary orbit has strictly smaller dimension: the last universal quantifier
  covers every k-point y with its FULL orbit contained in
  `closure (orbit a z) \ orbit a z`, in the ambient Z, and concludes the strict
  `topologicalKrullDim` inequality. It thus includes boundary orbits outside semistability,
  as the accepted proof's Step 8 explicitly requires.
- Nonreduced Z and stabilizers: there is no reducedness or smoothness hypothesis on
  either Z or its stabilizers, and no reduction in the stabilizer construction.
- Dimension convention: all dimensions use the dependency's `topologicalKrullDim`,
  including the subspace topology on orbit images. It measures Krull dimension of
  underlying schemes, invariant under adding nilpotents.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: `Field` (line 180).
- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, its morphisms and opens.
- WeilConjectures.AlgebraicGeometry.Morphisms.Projective: `AlgebraicGeometry.IsHProjective`.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: `AlgebraicGeometry.LocallyOfFiniteType`;
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact: `AlgebraicGeometry.QuasiCompact`.
- WeilConjectures.AlgebraicGeometry.Modules.Invertible:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
- WeilConjectures.AlgebraicGeometry.Ample: `AlgebraicGeometry.Scheme.Modules.IsAmple` and
  `AlgebraicGeometry.Scheme.Modules.nonvanishingLocus`.
- Mathlib.Topology.KrullDimension: `topologicalKrullDim : WithBot ℕ∞`.
- Sheaf.AlgebraicGeometry.GroupSchemeLinearization: `act`, `Linearization`,
  `Linearization.IsInvariant`, `Linearization.IsSemistable`, and `stabilizer`.
- Sheaf.AlgebraicGeometry.ProjectiveLinearQuotient:
  `AlgebraicGeometry.IsProjectiveLinearQuotient`, whose full signature and docstring
  were read in the current main source, along with its definition node.

The two direct definition dependencies are `def-sfb-group-scheme-linearization` and
`def-sfb-projective-linear-quotient`. The former theorem-node addition
`lem-sfb-projective-matrix-central-cover` is removed. The original base dependency
`lem-sfb-hilbert-plucker-pgl-linearization` remains as the node's source convention for
semistability; its Lean module contributes no declaration to this signature, so its
unused import is removed as the reviewer advised.

No old dependency record was replaced. All stated proof-dependency modules,
including the Mathlib leaves, are imported without `public`. The two still unstated proof
nodes `lem-wf-affine-constructible-open` and `lem-wf-affine-product-reduced` have no module
to import; their uses remain explicit in the complete proof docstring.

Edge cases checked before writing: empty Z and empty semistable locus make the quantified
semistable point impossible; fixed points give dimension zero orbits with stabilizer G;
a closed orbit has empty boundary, making the boundary assertion vacuous; different
representatives of one closed orbit give the same O, hence do not invalidate uniqueness;
nonreduced finite stabilizers in characteristic dividing r still have dimension zero;
nonreduced ambient schemes are not excluded. No characteristic restriction, independent
test universe or hidden auto-bound variable was introduced. All universes are explicit,
with autoImplicit and relaxedAutoImplicit disabled.

Searches for an existing statement or interface:

- msearch leanfinder, query: "Orbits of an algebraic group are locally closed, dimension
  equals group minus stabilizer, unique closed orbit in semistable orbit closure".
  Eight results concern abstract/topological group orbits and blocks; none is this theorem.
- msearch loogle, query: "topologicalKrullDim, IsLocallyClosed": zero hits.
- msearch grep, query: "orbit|stabilizer|semistable", Mathlib AlgebraicGeometry:
  six elliptic-curve scalar-orbit references, no orbit-dimension/GIT theorem.
- msearch leansearch, query: "algebraic group orbit locally closed semistable orbit
  closure unique closed orbit": eight abstract-action results, no match.
- rg of WeilConjectures and Sheaf for orbit/closed orbit/dimension and for
  orbitMap, orbitImage, semistableSet and semistableLocus: no existing general helper
  names. SmoothGroupOrbitGeometry gives the general locally closed orbit and dimension
  clauses but not the projective semistable uniqueness clause; AffinePGLQuotientOrbitTopology
  concerns only affine quotients, not the present projective Z.
- rg for the node id in WeilConjectures: no hit.

Source checked: Morrison §3.3 Corollary 11(3), printed p.17, online at
https://arxiv.org/pdf/0810.2340 (the named local PDF is absent); Milne, Algebraic Groups,
local PDF printed pp.26--28, especially Propositions 1.65 and 1.66. The current blueprint
unit `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`
was read for scope. No statement correction or STATEMENT-DISPUTED flag is needed.

## Second reading by NL

I reopened the node and the resulting Lean file for a separate clause-by-clause pass.
This is a self-review; the dispatcher expressly prohibits starting another agent, and
the maintainer supplies the independent review. The correspondence above was checked
against the actual binders and conjunctions, not inferred from the declaration name.
The ambient boundary and the semistable closure use their respective topologies;
uniqueness binds a set, not y. The helper semistable locus uses the recorded nonvanishing
predicate and the same invariant-section definition as the point predicate. Every
nonreduced case is retained. On the repair pass, I also reopened the landed quotient
definition: its test schemes, scalar quotient, naturality, injectivity and local
surjectivity give exactly PGL. The repaired binder is `IsProjectiveLinearQuotient k r G.X`;
π and j occur nowhere in the signature. No mismatch requiring a statement change was found.

## Returned delivery repair

H2 / theorem-stmt_dep, immutable returned head a7bcf8276c95: replaced
`ProjectiveMatrixCentralCover.Presentation k r hr G π j` by the existing definition
`IsProjectiveLinearQuotient k r G.X`. Removed π and j, which were used only to
parameterize the former presentation. Replaced the added theorem dependency by the
landed `def-sfb-projective-linear-quotient`. Removed the public import of the theorem
module and the unused HilbertPluckerPGLLinearization import (the advisory).
No file or record belonging to either landed theorem was edited. No new node or
copied definition is needed. The helper definitions and all four conclusions are
unchanged, as are the full 15 proof steps. The revised PGL hypothesis describes the
same scalar-quotient group scheme and includes every characteristic.

Comparison with current main: the base item still has no Lean record, and its original
statement, proof, proof_deps and eight stmt_deps are retained exactly. The packet is
rebuilt from that current node, with only lean and the two direct definition
dependencies added. The old theorem dependency is absent from the repaired packet.
All other hypotheses and conclusions were rechecked against the accepted correspondence
above. This addresses the specific return rather than rebasing an unchanged module.

Validation of the repaired packet: scompile.py passed for both sandbox and library
module on the server with no errors or unexpected warnings. The repaired deliver2.py
--no-push dry run returned OK at 4d9da9ed2d9, passing preflight and compilation.
