## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.FlagLineEulerAlternant` states
`AlgebraicGeometry.flag_line_euler_alternant`, with the sole theorem proof `sorry`.
The eight `FlagEuler` helpers have actual definitions and belong to this node's
cohomological character construction. No definition data or auxiliary theorem is
postponed. No statement correction, new node, or dependency repair is needed.

Source read: Milne, Algebraic Groups (2017), printed pp.479--480, Section 22d,
including 22.48's quotient relation and 22.50's antisymmetry operator. The source's
positive-root sign is corrected as already specified in the node: the bundle for
chi = -lambda has fibre -w lambda and cotangent weights w alpha. The current
blueprint unit `_section.md` and `sk-thm-sf-ctf-stability-direct-images.proof.md`
were read under literature/blueprint/latest. This is the inherited supporting
input of direct-images step (3), not the unit's own statement. The existing
CompactObject example module has been withdrawn; its node now points upstream.
The current module follows the required module/public-import/exposed-section form.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Algebraically closed field: `{F : Type u} [Field F] [IsAlgClosed F]`.
- The group S (called G in Lean): `G : Grp (Over (Spec (.of F)))`.
  `hG : IsSemisimpleGroupScheme G.X` expands to smoothness, connectedness,
  affineness, locally finite type plus quasi-compactness, and triviality of
  every smooth connected solvable normal closed subgroup, using its actual
  scheme-theoretic derived series. `hsc` is the dependency's full quantified
  simple-connectedness condition: semisimple source, monoid homomorphism,
  surjective underlying morphism, finite kernel, and commuting kernel points
  over every commutative F-algebra, imply `IsIso f`. Thus nonreduced finite
  central kernels are included.
- T, B and their inclusions: `T B`, `iT`, `iB`, `j`, `hT`, `hsplit`, `hB`, `hj`.
  These say maximal torus, a split-torus isomorphism of some finite rank,
  Borel subgroup and the commuting inclusion triangle. The two commutativity
  instances expose the existing additive character/cocharacter Hom groups;
  their existence is supplied by reductive_borel_pair_structure.
- The root datum from the specified pair is `Φ`, `P : RootDatum Φ ... ...`,
  `b : P.Base`, `[P.IsReduced]`. `haG` and `haB` identify the actual conjugation
  actions; `hroot` identifies P's root with the actual character; `hpair`
  specifies the integer pairing by composition with the integer power map;
  `hweights` says exactly all nonzero adjoint character weights occur; `hpositive`
  identifies b's positive roots with the Lie(B) character weights. These are
  the recorded reductive-borel-pair-structure interface, not abstract root data
  detached from the group.
- `ρ` is an actual additive character, and `hρ : 2 • ρ = ...` is the integral
  half-sum equation. It does not divide by 2 in F and permits characteristic 2.
- `p`, `hp` and `hpu` describe the Borel projection extending identity on T and
  killing the unipotent radical. `hpu` tests all smooth connected normal
  unipotent closed subgroup schemes, hence exactly gives the radical condition.
  Conversely the radical is the largest such subgroup, so the projection
  supplied by reductive_borel_pair_structure satisfies these equations.
- `lam` is any character. There is no positivity, dominance, nonzero-weight,
  characteristic-zero or positive-characteristic hypothesis. `χ`, `hχ` say
  chi = -(p composed with lambda). Thus Presentation's right action
  `(g,z)b = (gb,chi(b)^(-1)z)` is precisely `(gb,lambda(p(b))z)`.
- `Q`, `π`, `hQ`, `hQft`, `hQqc`, `hπf`, `hπs`, `hπi`, `hπt` are the actual
  proper finite-type quotient and faithfully flat right-multiplication torsor
  of the recorded dependency, expressed by invariance and its kernel-pair
  pullback. They unpack the named quotient S/B; they impose no extra geometric
  restrictions. `L : AssociatedCharacterLineBundle.Presentation ... χ` retains
  its actual sheaf, total space, quotient action, representing section functor,
  specified trivialization and natural geometric left action. Invertibility
  and coherence follow from the dependency, and are not extra assumptions.
- `Scheme.Modules.scalarCohomology Q.hom L.L i` is literally right-derived
  global sections in O_Q-modules with scalars restricted to F. This is the
  R^i Gamma stipulated in the node, not a stand-in finite vector space.
  The existing node `def-sc-field-linear-module-cohomology-operations` is added
  to stmt_deps because this delivery uses its already landed operations.
- First conclusion: every actual cohomology space is `Module.Finite F ...`.
  Second conclusion: an N exists beyond which each such space is `Subsingleton`.
  This is precisely eventual vanishing, and is an assertion rather than an input.
- `I`, finite and decidable instances, `e`, `r`, and `IsMonHom (r i)` give rational
  group-scheme representations on finite bases of these very cohomology spaces.
  They encode exactly counital coassociative rational coactions. The action
  is pinned, not arbitrary: for each F-point s the coefficient iso θ is specified
  after pullback along the faithfully flat torsor by IsTranslationCoefficient.
  That condition pulls θ back in the specified trivialization and compares it
  to the unchanged coordinate under g -> s^(-1)g. The subsequent equality
  identifies the action matrix on EVERY cohomology vector with inverse-translation
  pullback followed by θ on cohomology. Since G is smooth affine finite type over
  an algebraically closed field, its F-points are Zariski dense and determine
  all regular matrix entries of each r. Thus this pins the rational action,
  including its values after every scalar extension, not just an abstract
  representation with a convenient character. PullbackComparison intertwines
  normalized adjunction units; no arbitrary pullback isomorphism is introduced.
- `FlagEuler.weightSpace` is the intersection of kernels imposing
  `r_A(t)v = chi_A(t) tensor v` for EVERY F-algebra and EVERY torus point.
  Testing the universal point is the coaction equality v -> v tensor chi.
  Nonreduced algebras are included; these are not Lie-algebra/differential weights.
  `DirectSum.IsInternal ...` states that summing the actual subspaces is an
  isomorphism onto H^i; `Set.Finite` states finite weight support.
- `FlagEuler.character` is a finitely supported sum of monomials with coefficients
  `(Module.finrank F (weightSpace ...) : ℤ)`. The Euler sum is the displayed
  `∑ᶠ i, (-1 : ℤ)^i • character ...`. With the preceding finite supports and
  vanishing this is the ordinary finite alternating sum, not a convergence
  convention or reduction to the coefficient field.
- W is Mathlib's `P.weylGroup`, the subgroup generated by the root reflections.
  The perfect pairing makes its action on X faithful; it is canonically the
  group of X-automorphisms in the statement. `Finite P.weylGroup` is asserted.
  `alternant P ν` sums the action of each w on the actual lattice, multiplying
  by `LinearMap.det` over ℤ. An integer lattice basis identifies this determinant
  with the determinant on X tensor ℚ; no coefficients are cast to F.
- The final equality is exactly `q_lam * alternant P (-ρ) =
  alternant P (-lam - ρ)` in `AddMonoidAlgebra ℤ X`.

Dependencies read and used:

- Mathlib.Algebra.Field.Defs: `Field`; Mathlib.FieldTheory.IsAlgClosed.Basic:
  `IsAlgClosed` (and the algebraic-closure dependency's full recorded match).
- Mathlib.CategoryTheory.Monoidal.Grp: `GrpObj`, `Grp`, and pointwise group laws;
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs: the specialization over
  Spec F, `IsNormalSubgroupScheme`, `IsClosedSubgroupScheme`, finite kernels.
- Sheaf.AlgebraicGeometry.RhoSectionModules: `IsRhoBorelPair` and
  `exists_rho_section_modules`, with its full simple-connectedness signature;
  its inherited `IsSemisimpleGroupScheme`, `RhoSection.characterValue`,
  and `GeneralLinearGroup.RationalHom` interfaces are reused.
- Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure:
  `reductive_borel_pair_structure` and `semisimpleGroupScheme_isReductive`.
  Their full signatures/docstrings give exactly the unpacked root and quotient data.
- Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousLineBundleSections:
  `exists_homogeneousLineBundle_sections` and its public imported
  AssociatedCharacterLineBundle.Presentation, with the recorded quotient sign,
  geometric actions and normalization of the trivialization.
- WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations:
  `scalarCohomology`, `scalarCohomologyMap`, `scalarCohomologyPullback`,
  `scalarPullbackAdjunction`; each definition and its full signature was read.
- Mathlib.LinearAlgebra.RootSystem.WeylGroup: `RootPairing.weylGroup`;
  RootSystem.Hom: `RootPairing.Equiv.weightEquiv`; determinant, direct sums,
  group algebra and finsum are Mathlib's constructions.
- The only additional stated proof dependency is
  Sheaf.AlgebraicGeometry.GroupScheme.SimplyConnectedCharacterLattice:
  `simplyConnected_character_lattice` (ordinary import). The other four
  currently unstated fixed-geometry/reflection/denominator/fixed-point proof
  dependencies are retained by id in the proof docstring; no missing module
  is invented or imported.

Searches actually run with msearch.py (logged in searches.jsonl):

1. leanfinder: "Integral torus character of sheaf cohomology of a homogeneous
   line bundle on a flag variety satisfies Weyl alternant formula": eight
   Lie-module trace/weight-chain and Killing-coroot results. None states a
   rational algebraic-group sheaf-cohomology character identity.
2. loogle: `"weyl", "character"`: zero hits.
3. grep: `alternant|Euler.*character|weyl.*character`: 13 hits, consisting of
   Dirichlet Euler products, alternating ranks of exact sequences/complexes
   and incidence-algebra Euler characteristic, not this statement.
4. grep: `RationalHom.*weight|weightSpace.*RationalHom|flag_line_euler_alternant`:
   zero hits. Local rg over WeilConjectures and Sheaf for this and alternant,
   plus the exact item id, also found no duplicate. Existing split-torus and
   Gm weight-space interfaces use Laurent/group-algebra coactions, not actual
   group-scheme Hom characters with a rational matrix representation.

Edge cases checked before drafting: rank zero (empty positive roots, rho=0,
trivial Weyl group, point flag and q=1); trivial lambda; SL2 with positive Borel
root 2 (lambda=1 gives H0 weights -1,+1 and
(e^(-1)+e) (e^(-1)-e) = e^(-2)-e^2; lambda=-1 has all cohomology zero;
lambda=-2 has q=-1, giving the same signed formula); zero cohomology spaces
use empty bases and zero character; arbitrary negative/nondominant weights;
characteristic 2 (integer determinant and half-sum equation remain integral),
and nonreduced test algebras. No edge case is excluded by the binders.

Validation: scompile.py compiled both sandbox and named library module cleanly
within the per-file 60 s limit (latest clean run: 18.0 and 11.1 seconds). No
warnings other than the allowed theorem sorry; the initial pullback-composition
orientation error and the one long line were corrected. No global build or
read-only source edit was performed.

## Second reading by Q14

This is the dispatcher's single-worker setting, which expressly prohibits starting
another agent. Accordingly this section records a fresh in-thread rereading,
not a claim of an independent worker review; the maintainer's independent review
is still required. Reopened the node, source and final file, and checked every
binder and clause using the correspondence above. Checked the hsc kernel
centrality includes all scalar extensions; hweights/hpositive identify actual
characters rather than Lie differentials; hχ negates the extended character,
not the Borel choice; and θ's equation uses the canonical pullback comparison
and the correct directions of pullbackComp. The fresh reading found and fixed
those composition directions in the first draft, replaced the reserved lambda
binder by `lam`, replaced the reserved MonObj η pattern binder by `eta`, and
inserted the canonical map from the affine F test scheme to the monoidal unit
when evaluating the representation. Rechecked determinant coefficients lie in
ℤ, Weyl finiteness and cohomology boundedness are conclusions, and no
finite-dimensionality or dominance is assumed. All eight helper declarations
have source/blueprint docstrings and real construction bodies; the only sorry
is the requested theorem. The item's TeX statement, proof and proof_deps are
unchanged. The only added statement dependency is the already landed field-linear
cohomology operations actually used by the statement.
