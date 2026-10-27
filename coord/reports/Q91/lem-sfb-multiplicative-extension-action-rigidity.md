## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.MultiplicativeExtensionActionRigidity`
states `AlgebraicGeometry.multiplicativeExtensionAction_eq_snd`. Its single theorem has
proof `sorry`; it adds no definitions. The natural-language statement is unchanged.
The only added statement dependency is the already landed
`def-sfb-diagonalizable-group`, whose canonical Hopf-spectrum construction is used.
No new nodes, dependency repairs, or statement corrections are necessary.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Algebraically closed field F: `{F : Type u} [Field F] [IsAlgClosed F]`.
- E, Q, G are F-group schemes: objects of `Over (Spec (.of F))`, each with
  the recorded `GrpObj` structure. These objects include their structure morphisms.
- All groups are affine: the three `IsAffine _.left` instances.
- Finite type: `LocallyOfFiniteType _.hom` and `QuasiCompact _.hom`, separately
  for E, Q and G, exactly the recorded definition's conjunction. The kernel is the
  canonical closed subgroup of E, so is affine of finite type without extra hypotheses.
- Smoothness and connectedness of G: `[Smooth G.hom] [ConnectedSpace G.left]`.
  `ConnectedSpace` includes nonemptiness. No such assumptions are imposed on E, N or Q.
- q is a group-scheme homomorphism: `(q : E ⟶ Q) [IsMonHom q]`.
- The coordinate-ring map is faithfully flat: `hflat : q.left.appTop.hom.FaithfullyFlat`.
  This is Mathlib's ring-map predicate, i.e. faithful flatness of its target as a module
  using the algebra structure induced by that exact ring map. Flatness is exactness of
  tensoring and faithfulness is detection of zero modules; no pointwise surjectivity
  on A-valued points is substituted.
- N is the scheme-theoretic kernel: every occurrence uses `GrpObj.ker q`, the actual
  pullback of q and the unit. Its canonical inclusion is `GrpObj.kerι q`.
- Multiplicative type of N and Q: `hN` and `hQ` quantify over `M : Type u` with
  `AddCommGroup M` and `AddGroup.FG M` and require a group-object isomorphism to
  `diagonalizableGroup F M`. The recorded D(M) is the Hopf spectrum of
  `AddMonoidAlgebra F M`, with coproduct e_m ↦ e_m tensor e_m, counit 1 and inverse
  e_m ↦ e_(-m). These are group-scheme isomorphisms, not only scheme isomorphisms
  or equivalences of rational points.
- Centrality of N: `hcentral` says `(n ≫ GrpObj.kerι q) * e =
  e * (n ≫ GrpObj.kerι q)` on every test F-scheme T.
- The action a: `[ModObj G E]` supplies the actual F-morphism
  `ModObj.smul (M := G) (X := E)` and its unit and associative action laws.
- Acting by group automorphisms: `hmul` says `g • (e * e') = (g • e) * (g • e')`
  on every test scheme. The action of inverse g is inverse to the action of g by
  the `ModObj` laws and `GrpObj G`, so these multiplicative maps are bijective.
  A multiplicative map between groups preserves the identity automatically.
  Thus this is equivalent to the node's automorphism condition, with no additional
  structure or hypothesis. Naturality follows from evaluating a scheme morphism;
  `ModObj.comp_smul` is the existing naturality identity.
- Preserving N: `hpreserve` says the action on an included kernel point factors
  through the same kernel inclusion. Evaluating on the universal point of G × N
  produces the restriction morphism G × N → N; monicity of the inclusion gives
  its action laws. The inclusion is stable under inverse g as well, so preservation
  means a genuine restricted action, not merely an unrelated lift.
- Conclusion: `ModObj.smul (M := G) (X := E) = snd G E`, equality of the actual
  F-morphisms G ×_F E → E.

The node formulates centrality, multiplicativity and preservation on affine test schemes
Spec A. The Lean uses every test F-scheme. This does not strengthen the hypotheses:
these identities are local on affine opens of T; kernel factorization is the pullback
condition and glues uniquely. Conversely, all Spec A occur among the tests. Both schemes
and F are in universe u, the project's scheme convention. Every finite-type group and
finitely generated character group admits this size; no independent small universe of
algebra tests is imposed. In particular the affine universal test scheme is allowed.

Dependency declarations and their source interfaces read:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` (splitting of every polynomial,
  equivalent to the node's root condition); no chosen algebraic closure is required.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, `Grp`, `Grp.mk`;
  `Mathlib.CategoryTheory.Monoidal.Mon`: `IsMonHom`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`: the recorded specialization
  to `Over (Spec (.of F))` and the canonical kernel interface, defined in
  `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp` as the fibre product
  of q and the unit. `GrpObj.ker`, `GrpObj.kerι` and its group instance are used directly.
- `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`: `Hom.group` on T-valued points;
  `Mathlib.CategoryTheory.Monoidal.Mod`: `ModObj` with `smul`, `one_smul`, `mul_smul`;
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Mod`: `Hom.smul`, `Hom.mulAction`,
  `ModObj.comp_smul`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`.
- `Sheaf.AlgebraicGeometry.DiagonalizableGroup`: `diagonalizableGroup`, the already
  landed declaration of `def-sfb-diagonalizable-group`.
- `Mathlib.RingTheory.RingHom.FaithfullyFlat`: `RingHom.FaithfullyFlat`.

Proof-only imports cover the stated proof-dependency records: `pullbackSpecIso` in
`Mathlib.AlgebraicGeometry.Pullbacks`, faithfully-flat base change in
`Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`, `Flat.SpecMap_iff` in
`Mathlib.AlgebraicGeometry.Morphisms.Flat`, spectrum surjectivity in
`Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`, and the fpqc covering, stability and
subcanonical-descent interfaces in `Mathlib.AlgebraicGeometry.Sites.Fpqc`.
The two rigidity proof-dependency nodes have no Lean record in the read repository,
so there is no module to import for them. They are proof prerequisites only; the
statement uses none of their declarations. Their role is fully described in the
proof docstring for subsequent stage-3 work.

Source read: Milne iAG2017, printed pp.243–245 (PDF pages 255–257), including Theorem
12.36 and Corollaries 12.37–12.41, and the Chapter 12 erratum at the end of the PDF.
The erratum explicitly requires N central in H, exactly `hcentral`. The docstring gives
all five accepted proof steps, including the fpqc composite-cover check and the
difference-map factorization rather than the incorrect literal factorization of a.
The current blueprint unit `literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-thm-sf-ctf-stability/_section.md` was read; its statement is not changed.
The mandated CompactObject example module is now withdrawn (no declarations remain);
the current stage-2 module conventions are followed.

Edge cases checked before writing: trivial G, N or Q and M = 0 are allowed; G = Spec F
is connected and gives the trivial action law. Positive characteristic and p-torsion
in M are unrestricted, so nonreduced μ_p is covered. E, N and Q need not be smooth,
connected or reduced. G cannot be empty because it has a unit, and connectedness
also records nonemptiness. Nonreduced algebras and arbitrary test schemes are retained.
A genuinely disconnected acting group can act by nontrivial discrete automorphisms,
so the connectedness hypothesis is substantive. Removing hmul would admit translation
on G_m; retaining it is essential. Centrality is used precisely in multiplicativity
of the descended difference. No false or ambiguous statement was found.

Searches (2026-10-24):

- `msearch.py ... leanfinder "A connected smooth affine group acts trivially on a
  central extension of multiplicative type group schemes preserving the kernel"`:
  8 hits, abstract `GroupExtension.conjAct` and Galois-category actions; no match.
- `msearch.py ... loogle '"GrpObj", "action"'`: 0 hits.
- `msearch.py ... grep 'multiplicative.?type|[Dd]iagonalizable' AlgebraicGeometry`:
  0 hits in Mathlib.
- `msearch.py ... leansearch "A connected algebraic group acts trivially by
  automorphisms on a central extension of diagonalizable group schemes"`: 8 hits,
  abstract group actions, extensions and Galois-category statements; no match.
- `rg` for multiplicative, diagonalizable and action rigidity in both
  `lean/WeilConjectures` and `lean/Sheaf` found the already landed D(M), finite
  diagonalizable groups and the consumer `multiplicativeIsogeny_comp`, but no
  theorem with this statement. Searching the node id in `lean/WeilConjectures`
  found no declaration. Names searched in `dag/lean_names_upstream.json` did not
  supply the theorem. Mathlib's `ModObj` was reused instead of an action definition.
- DAG searches located `def-sfb-diagonalizable-group`, whose recorded construction
  is reused and added to stmt_deps; no new definition node is needed.

Validation: `scompile.py Q91 lem-sfb-multiplicative-extension-action-rigidity <module>`
passed both sandbox and library-path compiles (1.9 s and 2.0 s). All variables and
universes are explicit and `autoImplicit` is false. All lines are at most 100 columns.

## Second reading by Q91

A separate pass over the node and completed signature checked each correspondence
above. The initial draft already used the exact kernel and the explicit finite-type
conjunction. The audit checked that hN/hQ use group-object isomorphisms, not bare
scheme isomorphisms, and that hpreserve supplies a restricted action by universal
kernel factorization. It also checked that hmul plus action inverses really gives
automorphisms and that all-scheme testing is equivalent to all-algebra testing.
No signature mismatch was found; no statement correction was made. This is a
self-audit, not a claimed independent agent review: the dispatcher brief prohibits
starting other agents and assigns the independent review to the maintainer.
