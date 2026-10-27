## Worker report

The module `Sheaf.RepresentationTheory.RelativeTorusBundleWeights` states the entire
node in four theorem declarations, all with `sorry`. Six auxiliary definitions in
namespace `SplitTorus` give real constructions belonging to this node's own explicit
notions: weight kernels, the canonical scalar-extended coaction, quotient restriction,
invariants, the subgroup sum, and residue-field fibre dimension. No auxiliary proof
is postponed, and no new axiom, independent notion, or dependency module is introduced.
The node copy changes only `lean`; all ten declarations are listed there.

Source checked: Brian Conrad, *Reductive Group Schemes*, author PDF
https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, Proposition 3.1.9 proof (1),
printed pp.86--87 (PDF pages 85--86), and Lemma 2.2.4 proof, printed p.66 (PDF page 65).
The first passage gives vector-bundle weights, direct-summand local freeness, base
change, and simultaneous nearby rank constancy. The second explains the grading
interpretation and the invariant subbundle's arbitrary base-change compatibility.
The latest blueprint unit is
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`;
this item is an auxiliary supporting node, not that unit's own statement.

Hypothesis and clause correspondence:

- Any commutative ring A is `{A : Type u} [CommRing A]`, with no nonzero or domain
  hypothesis. V has `[AddCommGroup V] [Module A V]`, in an independent universe v.
- The rank r is `(r : ℕ)` without a positivity hypothesis. Its character lattice
  is `Fin r → ℤ`, the ordinary product model of Z^r.
- A[M] is Mathlib `AddMonoidAlgebra A (Fin r → ℤ)`, not a replacement ring. Its
  existing Hopf structure has multiplication of basis elements by addition,
  `Coalgebra.comul e^m = e^m tensor e^m`, and counit equal to 1 on each e^m.
- Finite projectivity is `[Module.Finite A V] [Module.Projective A V]`. This is
  exactly the direct-summand-of-finite-free condition: Mathlib
  `Module.Finite.exists_comp_eq_id_of_projective` gives the finite-free retraction;
  conversely a finite-free retract is finite and projective. No constant-rank or
  globally free assumption is made.
- The A-linear coaction is the linear-map binder rho. `hcoassoc` is the actual
  equality `(assoc) (rho tensor 1) rho = (1 tensor comul) rho`; `hcounit` is
  `rid (1 tensor counit) rho = id`. Both hypotheses occur on each of the four
  theorems. The field-only HopfAction interface is not applicable over arbitrary A,
  so the equations are stated directly instead of defining a duplicate coaction.
- `weightSpace rho m` is the kernel of rho minus the map sending v to v tensor
  `AddMonoidAlgebra.single m 1`. Thus membership is exactly the displayed V_m
  equation, including over the zero ring.
- The first theorem's `Function.Bijective (DirectSum.coeLinearMap (weightSpace rho))`
  says the specified sum map of inclusions is an isomorphism, rather than just
  existence of an unspecified module isomorphism. Its next conjunct is
  `Set.Finite {m | weightSpace rho m ≠ ⊥}`, and its next conjunct asserts both
  `Module.Finite` and `Module.Projective` for every weight submodule.
- The first theorem's last conjunct gives, for every s, an open U containing s
  with `∀ p ∈ U, ∀ m, fibreDimension rho m p = fibreDimension rho m s`. This is
  one neighborhood for all weights, not separate neighborhoods depending on m.
  `fibreDimension` is `Module.finrank` over `p.asIdeal.ResidueField` of its tensor
  with the actual weight module. These are the source's residue fields via
  `AlgebraicGeometry.Scheme.Spec.residueFieldIso`; the recorded proof dependency
  `AlgebraicGeometry.spec_field_point_residue_field` states the canonical affine
  residue-field identification and the compatible map from A. No new residue field
  definition is supplied. `PrimeSpectrum A` is the underlying space of the
  recorded `Spec (CommRingCat.of A)`.
- `relative_torus_bundle_weights_baseChange` quantifies over `(S : Type w)
  `[CommRing S] [Algebra A S]` for an independent universe w. Such an Algebra
  specifies an arbitrary ring map A to S; no flatness, injectivity, or nonzero
  assumption occurs. Scalar extension is written `S tensor_A V`, canonically
  symmetric to the source's `V tensor_A S`. `baseChangeCoaction` is rho.baseChange
  composed with the actual Mathlib tensor-distribution equivalence and
  `AddMonoidAlgebra.scalarTensorEquiv A S`. It gives the canonical extended action,
  not a new coaction chosen arbitrarily or assumed as additional input.
- That theorem asserts injectivity of `(weightSpace rho m).subtype.baseChange S`
  and equality `(weightSpace rho m).baseChange S = weightSpace (baseChangeCoaction S rho) m`.
  Mathlib's submodule baseChange is precisely the image of that natural tensor
  inclusion. Together the two clauses give the required identification under
  natural inclusions, retaining its injectivity even for nonflat scalar extension.
- L is an `AddSubgroup (Fin r → ℤ)`; `[Module.Free ℤ ((Fin r → ℤ) ⧸ L)]` is exactly
  the stipulated freeness of M/L. `restrictCoaction` composes rho with `1 tensor q`,
  where `q = AddMonoidAlgebra.mapDomainLinearMap A A (QuotientAddGroup.mk' L)` sends
  e^m to e^(m mod L). It is the linear map underlying the quotient Hopf ring map;
  contravariance of the recorded `AlgebraicGeometry.Spec.map` gives the indicated
  subgroup scheme inclusion. `invariants rho L` is the zero-weight kernel of this
  restricted coaction. It does not use invariants of the group's A-valued points.
- `relative_torus_bundle_weights_invariants` says the actual subgroup-indexed sum
  `subgroupSum rho L` is injective and has range exactly `invariants rho L`. Thus
  it identifies the invariant module with the direct sum over m in L, with the
  natural inclusion into V.
- `relative_torus_bundle_weights_invariants_baseChange` asserts injectivity of the
  scalar-extended invariant inclusion and equality of its image with invariants
  of the canonical extended coaction restricted using the same L. This is the
  arbitrary base-change clause for the invariant module, again with no flatness.

Dependency declarations read and used:

- Statement dependency `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and
  `AlgebraicGeometry.Spec.map`, module `Mathlib.AlgebraicGeometry.Scheme`, read
  with their docstrings at lines 469--480. The underlying topological space in
  the rank clause is `PrimeSpectrum A`. The quotient Hopf map is used on
  coactions directly, as in proof step 7; no extraneous scheme construction is
  required to express restriction of the representation.
- Statement dependency `def-weil-residue-field`: `Scheme.residueField` and
  `Scheme.Hom.residueFieldMap`, module `Mathlib.AlgebraicGeometry.ResidueField`,
  read with their signatures and docstrings. Affine residue fields are expressed
  by the canonical equivalent `Ideal.ResidueField` model, as justified above.
- Proof dependency `lem-weil-pbc-finite-projective-rank-locally-constant` is the
  Mathlib match `Module.isLocallyConstant_rankAtStalk`, module
  `Mathlib.RingTheory.Spectrum.Prime.FreeLocus`, read at lines 224--228. Its import
  is a plain proof import.
- Proof dependency `lem-weil-pbc-spec-field-point-residue-field` is
  `AlgebraicGeometry.spec_field_point_residue_field`, module
  `WeilConjectures.AlgebraicGeometry.SpecFieldPointResidueField`; its full signature
  and proof docstring were read. Imported as a plain proof dependency.
- Direct Mathlib constructions used: `DirectSum.coeLinearMap`, `DirectSum.toModule`,
  `TensorProduct.AlgebraTensorModule.distribBaseChange`,
  `AddMonoidAlgebra.scalarTensorEquiv`, `LinearMap.baseChange`,
  `Submodule.baseChange`, and `AddMonoidAlgebra.mapDomainLinearMap`.

Edge cases checked before and during the second reading: A = 0 has empty spectrum
and zero modules, so the last clause is vacuous. V = 0 has empty weight support,
and zero-dimensional fibres. r = 0 has the one-element character lattice, and the
counit forces only its trivial weight. L = 0 gives invariants of the full torus,
and L = M gives all of V. A finite generating list can be empty. Disconnected A
and varying projective ranks are retained by the open-neighborhood statement.
Nonflat ring maps and S = 0 are allowed. No root, characteristic, reducedness,
Noetherian, field, or geometric-connectedness assumption is introduced.

Searches for an existing statement/notion:

- msearch LeanFinder, query `split torus comodule over additive monoid algebra
  decomposes into weight submodules commuting with base change`: 8 hits, including
  AddMonoidAlgebra.decomposeAux_single and Lie-module weight spaces. They concern
  grading of the algebra itself, Lie-module weights, or Maschke's theorem, not
  general-ring Hopf-comodule weights and the node's compatibility assertions.
- msearch LeanSearch, query `comodule of a group algebra has a weight decomposition`:
  8 hits, polynomial weighted decomposition and Lie weights; no matching statement.
- msearch Loogle, query `Coalgebra, Comodule, AddMonoidAlgebra`: no hits;
  `Comodule` is unknown to this search service.
- msearch grep, query `Comodule|Coaction|weightSpace|WeightSpace`, subdirectory
  RingTheory: zero hits. Direct rg of Mathlib found its Hopf, coalgebra, tensor,
  direct-sum and rank APIs, but no general comodule weight-decomposition statement.
- rg in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` for
  coaction/comodule, group algebra, and torus weights: existing HopfAction has a
  Field base and semilinear data, so cannot encode arbitrary-ring A here.
  `GmRepresentation.weightSpace` (read in full) is only over fields and for the
  one-dimensional Laurent group algebra. `TorusCharacterTangent.weightSpace`
  (read with its signature and docstring) concerns tangent spaces and point-tested
  characters over a field. Neither gives this node's arbitrary-ring, arbitrary-rank
  Hopf-kernel interface. Their theorems do not imply the full node as an existing
  exact declaration. Lie-module weight spaces are a different notion.
- rg of the proposed namespace and complete declaration names in Mathlib,
  `lean/WeilConjectures`, `lean/Sheaf`, and the upstream-name index found no clash.
  `grep -rn lem-sfb-relative-torus-bundle-weights lean/WeilConjectures` found no
  upstream attachment. Search tool records are also in sandbox searches.jsonl.

No statement dispute or node correction was needed. The four postponed theorem
proofs each carry source and proof-step docstrings. The module compiled through
scompile.py in both sandbox and actual library module mode with no errors or
unexpected warnings; the first attempt exposed a missing DirectSum notation scope,
which was fixed. No live repository file was edited and no direct git command or
global build was run.

## Second reading by Q29

This is the author's separate verification pass; the maintainer supplies independent
review under the dispatcher brief. I reread the JSON statement against all four
signatures and the definitions they unfold. The initial coassociativity, counit,
finite-projective, and rank-zero binders exactly match the node. I specifically
checked that the first theorem uses the natural direct-sum map, not an unspecified
isomorphism, and one open neighborhood simultaneously for all characters. The two
base-change statements include injectivity as well as image equality, which is
needed to render "under natural inclusions" for nonflat maps. The quotient map uses
M/L and the zero character, and its direct sum is indexed by L itself. The freeness
hypothesis is on M/L. All six helper definitions have concrete bodies and match
notions explicitly introduced by this node; none asserts an independent theorem.
The affine residue-field model is canonically the scheme residue field by the
recorded dependency; using the existing Ideal.ResidueField algebra avoids inserting
an arbitrary or separately chosen coefficient action. The already landed G_m
field-only and tangent-space definitions were checked and do not provide this
arbitrary-ring interface. No hypothesis, conclusion, or node field was changed
by this reading. The public imports expose the two recorded statement dependencies;
the two additional proof dependencies are plain imports.
