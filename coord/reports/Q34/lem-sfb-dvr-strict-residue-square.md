## Worker report

The module `Sheaf.RingTheory.DvrStrictResidueSquare` states
`IsDiscreteValuationRing.exists_strict_residue_square` with a single `sorry`.
Its helper `IsDiscreteValuationRing.IsFiniteWeakSolution` defines, with real data,
the weak-solution convention included in this very node. No statement correction,
new node, or dependency repair is made. In particular, the earlier stage-1
`statement_change` and all existing metadata are retained unchanged.

Hypothesis and clause correspondence:

- The original DVRs are the independent-universe types `A : Type u`, `B : Type v`
  with `CommRing`, `IsDomain`, and `IsDiscreteValuationRing` instances.
- The specified map is `algebraMap A B`. `hinj` is its injectivity and
  `IsLocalHom (algebraMap A B)` expresses locality. For local rings this is
  equivalent to contraction of the target maximal ideal being the source maximal ideal.
- The fraction fields are `K : Type w`, `L : Type x`, with `Field`, the respective
  `Algebra` and `IsFractionRing` instances. `Algebra K L` gives the field embedding;
  `IsScalarTower A B L` and `IsScalarTower A K L` require it to extend the specified
  DVR map. These are compatibility data, not extra mathematical hypotheses.
- The weak-solution helper uses `Module.Finite F M`, equivalent to finite
  dimensionality over a field. It does not require separability of the solution.
- `integralClosure D M` is R. `eppUpperClosure T F H M` is C: the integral closure
  of T in `eppReducedTensor F H M = (H tensor[F] M) / nilradical`.
  These are actual integral closures and the quotient by all nilpotent elements.
- For every ideal `q` of C with `q.IsMaximal`, contraction is
  `q.comap (eppNormalizationMap D T F H M)`. This map is the canonical
  normalization map, restricting `m ↦ 1 tensor m` followed by reduction; it is
  not an arbitrary map supplied by a hypothesis.
- The first existential in the helper asserts maximality of this contraction n,
  then `IsDomain (Localization.AtPrime n)` and `IsDiscreteValuationRing` there.
  The second existential gives the same two properties for `Localization.AtPrime q`.
  Thus both local DVR requirements are present, including the lower one.
- The ideal equality in the helper is precisely n C_q = q C_q: the left map is
  R to C followed by C to its localization, and the right map is the latter alone.
- The outer existential supplies `Aₛ`, `Bₛ`, their ring/domain/DVR structures, and
  `Algebra A Aₛ`, `Algebra B Bₛ`, `Algebra Aₛ Bₛ`, `Algebra A Bₛ`.
  The two `IsScalarTower` witnesses say both composites A to Bₛ equal the same
  structural map, so the specified square commutes.
- Each of its three new arrows has both an explicit `Function.Injective` conclusion
  and an `IsLocalHom` witness. No injectivity of an arbitrary chosen map is hidden.
- The two `IsSepClosure` conclusions use the canonical residue algebra structures
  of the respective local maps. They say the induced extensions are separable
  algebraic and the upper residues are separably closed, rather than only asserting
  abstract isomorphism to unrelated closure fields.
- `Ideal.map (algebraMap A Aₛ) (IsLocalRing.maximalIdeal A) =
  IsLocalRing.maximalIdeal Aₛ` is exactly the uniformizer-preservation clause.
  A generator of the original maximal ideal therefore generates the new one.
- `Kₛ`, `Lₛ` and their fraction-field, algebra, and scalar-tower witnesses are the
  fraction fields of the new DVRs and the induced field extensions.
  `Algebra.IsSeparable K Kₛ` and `Algebra.IsSeparable L Lₛ` include algebraicity.
  All field maps agree with the DVR maps by their scalar towers; uniqueness of
  fraction-field extension makes the induced fraction-field square commute.
- The final implication places `PerfectField (IsLocalRing.ResidueField A)` solely
  before the descent assertion. Its premise is an existential finite weak solution
  H/Kₛ for Aₛ to Bₛ, and its conclusion an existential finite weak solution N/K
  for A to B, using the exact same helper. Perfection is not a premise of square
  existence, and no conclusion claims that the particular H descends unchanged.
- There is no completeness, perfection of the upper residue field, perfect-core
  hypothesis, or essentially-finite-type hypothesis in this theorem.

Dependencies read and used:

- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`
  (and `irreducible_iff_uniformizer` for the clause comparison).
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, `algebraMap`; the field-extension
  encoding of `def-pc-field-extension`.
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure`.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`, with its algebra
  structure and nilradical quotient as in the existing Epp helpers.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`.
- `Mathlib.FieldTheory.Separable`: `Algebra.IsSeparable`, whose own documentation
  and `isAlgebraic` instance establish that it includes algebraicity.
- The recorded `def-pd-separable-closure` module,
  `WeilConjectures.Mathlib.FieldTheory.IsSepClosed`, explicitly identifies the notion
  with Mathlib `IsSepClosure`; its `IsSepClosure.exists_intermediateField_mem`
  gives the directed-union description. The statement uses that same `IsSepClosure`.
- `Mathlib.RingTheory.LocalRing.ResidueField.Basic`: the canonical local-map
  residue-field algebra instance, read with its full signature.
- `Mathlib.FieldTheory.Perfect`: `PerfectField`.
- `Sheaf.RingTheory.EppEssentiallyFiniteTypeTraits`: only `eppReducedTensor`,
  `eppUpperClosure`, and `eppNormalizationMap`. Their complete definitions were read.
  The helper does not use `exists_epp_essentially_finite_type_traits` and does not
  inherit any of that theorem's hypotheses. Reusing them avoids a second definition
  of the normalization diagram. The surrounding Epp node is downstream in the DAG,
  so it must not be added as a statement dependency or waited on. A future reverse
  proof-only import from that Epp module to this module must be omitted if it closes
  a module import cycle, under stages/2-statements.md section 3 rule 7. No cycle is
  present in the delivered imports.
- Available proof-dependency modules are imported privately:
  `Sheaf.Paper.StrictHenselizationFunctoriality`
  (`AlgebraicGeometry.strictHenselizationFunctoriality`),
  `WeilConjectures.RingTheory.StrictHenselizationTriples`
  (`AlgebraicGeometry.Scheme.strictHenselization_triples`), and
  `Sheaf.RingTheory.IntegralClosureIndEtaleBaseChange`
  (`TensorProduct.toIntegralClosure_bijective_of_indEtale`).
  The four other non-Mathlib proof dependencies have no recorded Lean module yet.
  The final uniformizer-power input is already in the imported Mathlib DVR module.
  The docstring preserves the complete seven-step DAG proof for stage 3.

Edge cases checked before writing: residue characteristic zero and positive
characteristic; imperfect lower residue (square still exists, descent remains
conditional); nonperfect upper residue; arbitrary ramification of A to B;
noncomplete rings; nonseparable finite weak solutions; nontrivial nilpotents in
the generic tensor product; multiple upper normalized branches; identity DVR maps;
and degree-one weak solutions. DVR instances already exclude zero rings and fields.
The independent input ring and fraction-field universes are retained. Existential
algebraic extensions can be taken in `Type (max u v w x)` by their usual cardinal
bounds and transport; the helper itself permits all five universes independently.
No unrestricted test-algebra quantifier lives in a smaller universe.

Searches (prescribed msearch.py wrapper, group Q34 and this item):

- LeanFinder: "Compatible separable residue closures of discrete valuation rings
  and descent of finite weak solutions". Eight hits on residue separability,
  residue maps, and unramifiedness; no square/descent theorem.
- Loogle: `IsDiscreteValuationRing, IsSepClosure`. No hits.
- Mathlib grep: `WeakSolution|weakSolution|strictHensel`, restricted to RingTheory.
  No hits.
- LeanSearch: "Compatible separable residue closures of discrete valuation rings
  with descent of weak ramification solutions". Eight hits including `IsSepClosure`,
  `separableClosure`, and its algebraicity/separability; no square/descent theorem.
- Direct `rg` of project `lean/WeilConjectures` and `lean/Sheaf` for
  `WeakSolution|weakSolution|weak.solution`, followed by `eppNormalizationMap` and
  `eppReducedTensor`, found the Epp helpers used here, but no weak-solution predicate.
  The prescribed search for this node id in `lean/WeilConjectures` found no declaration.
- Collision check for `IsFiniteWeakSolution|exists_strict_residue_square` in Mathlib,
  both project source trees, and `dag/lean_names_upstream.json`: no hits.

Sources opened: local Stacks `more-algebra.tex`, the entire statement and proof of
`lemma-solution-after-strict-henselization` (09ET), and `definition-solution` (09EN),
with the tag table checked. The existing node already records the restricted
perfect-lower-residue descent; this delivery preserves it, without asserting the
unrestricted weak-solution transfer that its stage-1 correction rejected.
There is no new STATEMENT-DISPUTED finding.

Validation: prescribed `scompile.py` compiled both its sandbox wrapper and the
actual library module successfully. The initial implicit-use name warning on the
maximality witness was repaired by naming it `_hn`; the repeated compile is clean.
Only the main theorem has `sorry`; definitions contain no postponed data or proofs.

## Second reading by Q34

A separate second pass by the same dispatched worker reopened the node and the
finished module; no second agent was started, as required by the brief. The
maintainer's independent review remains external to this delivery. I compared the
seven statement dependency notions and each clause in the list above against the
actual signature and helper body. Both localized DVRs, maximal contraction, all
three injection/locality assertions, square compatibility, canonical residue
extensions, lower maximal-ideal equality, and the conditional finite-weak-solution
descent are present. I also checked that scalar-tower witnesses specify the
induced maps, rather than introducing unrelated field embeddings, and that the
Epp theorem's completeness and essential-finite-type hypotheses do not leak into
this statement. The only source-reference defect found was the helper docstring's
initial tag 09EQ (a different lemma); corrected to 09EN, the definition of solution.
No mathematical statement was changed and no additional axiom was introduced.
