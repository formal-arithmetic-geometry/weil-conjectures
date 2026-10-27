## Worker report

The module `Sheaf.RingTheory.EppNormalBaseBranchConjugacy` states
`IsDiscreteValuationRing.epp_normal_base_branch_conjugacy`, with its entire proof
postponed by `sorry`. The node is unchanged except for its `lean` record. No new
notions, helper definitions, dependency modules, or statement corrections are needed.

The precise hypothesis correspondence is:

- The complete DVRs A and B are independent carriers `Type u` and `Type v`, each
  with `CommRing`, `IsDomain`, `IsDiscreteValuationRing`, and
  `IsAdicComplete (IsLocalRing.maximalIdeal ...) ...`.
- The given injection A -> B is `[Algebra A B]` and `hinj`; its locality is
  `[IsLocalHom (algebraMap A B)]`. These are substantive hypotheses, not maps
  substituted for the specified inclusion.
- K and L are fields, with the respective `Algebra` and `IsFractionRing` instances.
  `[Algebra K L]`, `[Algebra A L]`, and the two scalar towers say that K -> L is
  the fraction-field inclusion induced by A -> B. A map of fields is injective.
- K_1 is named E. `[Algebra K E] [FiniteDimensional K E] [Normal K E]` says
  exactly finite normal extension, with no separability hypothesis. Mathlib Normal
  means algebraicity and splitting of each minimal polynomial; for algebraic
  extensions this is equivalent to the irreducible-root formulation in the node.
  `[Algebra A E] [IsScalarTower A K E]` specifies its canonical A-algebra structure.

The objects and every clause of the conclusion are rendered as follows:

- A_1 is the actual `integralClosure A E`; B_1 is the actual
  `integralClosure B ((L ⊗[K] E) ⧸ nilradical (L ⊗[K] E))`. The B-algebra
  structure is induced through B -> L and the left tensor inclusion. The quotient
  by `nilradical` is exactly reduction by all nilpotents, including inseparable
  tensor products. These expressions use Mathlib notions, not new definitions.
- `E ≃ₐ[K] E` is Aut_K(K_1). The existential `lowerAction`, `tensorAction`, and
  `upperAction` are monoid homomorphisms to groups of ring automorphisms, so they
  include identity and composition laws. Their three displayed formulas specify
  restriction of sigma, the reduced tensor action l tensor a -> l tensor sigma(a),
  and restriction of that action to B_1. The formulas determine all three actions
  uniquely: pure tensors generate the tensor ring and its quotient. In particular
  these are canonical actions, not arbitrarily chosen actions satisfying transitivity.
- The map `f` has the formula a -> class(1 tensor a) on every a in A_1; this
  uniquely pins down the canonical A_1 -> B_1 normalization map. The next conjunct
  expresses its compatibility with the actions. No additional map is assumed.
- For every pair of maximal ideals `q q'`, there exists sigma such that
  `Ideal.map (upperAction σ).toRingHom q = q'`: transitivity on exactly the
  maximal ideals, using the forward image convention for the action.
- `m.IsMaximal` and `∀ n, n.IsMaximal → n = m` specify the unique maximal ideal
  of A_1 without assuming a local-ring instance on its normalization in advance.
  The following `Ideal.map ... m = m` conjunct states that every automorphism fixes it.
- The existential positive natural number `e` is common to all maximal q. For
  each such q, the quantified equivalence for every natural n states precisely
  that extension of m along A_1 -> B_1 -> `Localization.AtPrime q` equals the
  nth power of `Ideal.map (algebraMap B_1 (Localization.AtPrime q)) q` iff n=e.
  Thus the exponent exists, is unique, and is independent of q. This is the
  node's definition of ramification, rather than a potentially different
  numerical ramification API.
- The final implication says that equality of the two extended maximal ideals
  at any maximal q gives e=1. Together with the preceding equivalence, it gives
  that equality at every maximal ideal, exactly the last clause of the node.

Dependency declarations read and used:

- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing` in
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`, requiring separately IsDomain
  and extending the local and principal-ideal-ring classes with a nonzero maximal ideal.
- `def-weil-pbc-adically-complete-ring`: `IsAdicComplete` in
  `Mathlib.RingTheory.AdicCompletion.Basic`; both Hausdorffness and precompleteness
  are included. Here the ideal is the maximal ideal, as in the source.
- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`, with fields
  and coherent algebra maps explicitly bound.
- `def-weil-pbc-integral-closure`: `integralClosure`,
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`, carrier `{x | IsIntegral R x}`.
- `def-weil-pbc-module-tensor-product`: `TensorProduct`,
  `Mathlib.LinearAlgebra.TensorProduct.Defs`; commutative algebra structure and
  quotient algebra instances come from `Mathlib.RingTheory.TensorProduct.Quotient`.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime`,
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, localization at the prime complement.

The declared proof dependencies are imported, with plain imports for proof-only
modules: `PrincipalIdealRing.isNoetherianRing`,
`PrincipalIdealRing.to_uniqueFactorizationMonoid`, and
`UniqueFactorizationMonoid.instIsIntegrallyClosed`; `isNagataRing_of_complete_local`
in `WeilConjectures.RingTheory.NagataOfCompleteLocal`; `IsNagataRing` and `IsN2`
in the corresponding NagataRing and JapaneseDomain modules;
`Algebra.finite_over_complete_local_product` in
`WeilConjectures.RingTheory.FiniteOverCompleteLocalProduct`;
`IsDiscreteValuationRing.ringKrullDim_eq_one` in
`Mathlib.RingTheory.DiscreteValuationRing.TFAE`;
`Algebra.TensorProduct.productMap` and `ext` in the Maps and Basic modules;
and `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible` in DVR Basic.
Their recorded signatures and docstrings were read. Three proof-only nodes have
no recorded declarations: `lem-sfb-dvr-algebraic-normalization-structure`,
`lem-sfb-finite-normalization-local-dvr`, and
`lem-sfb-normal-tensor-invariant-powers`. Their statements and proof plans remain
named in this theorem's proof docstring; there is no module to import for them.
None supplies an object required to type this statement. The existing
EppEssentiallyFiniteTypeTraits module was also read: its reduced tensor and
normalization map are the same constructions expanded here using Mathlib's
notions; importing that downstream theorem node would create an inappropriate
upward dependency. No duplicate helper is declared in this delivery.

Edge cases checked mathematically before writing: E=K gives the original one
branch and its ordinary ramification index, not necessarily 1. A=B is allowed.
A purely inseparable finite normal E/K has trivial automorphism group and a
single branch; reduced tensor quotients still make sense. In characteristic zero
there is no unnecessary p or characteristic assumption. In the separable split
two-branch example (real coefficients extended to complex coefficients, with
complete power-series DVRs), conjugation swaps the two branches. L/K can have
arbitrary transcendence degree and be infinite. All five carrier universes are
independent. The common exponent is positive because a uniformizer maps to a
nonzero nonunit under a local injection; exponent zero cannot occur. A DVR is
nonzero and not a field, so neither a zero ring nor an empty branch collection
is accidentally introduced as a new case by the hypotheses.

Searches made through the prescribed msearch wrapper, Q88 and this item:

1. LeanFinder: “A finite normal field extension acts transitively on maximal
   ideals of the integral closure in a reduced tensor product of complete
   discrete valuation rings”. Eight hits, including
   `Ideal.isPretransitive_of_isGaloisGroup`, `Ideal.exists_comap_galRestrict_eq`,
   and `IsGaloisGroup.iff_isFractionRing`. None states this result for a possibly
   inseparable normal extension and the reduced tensor algebra, with the
   completeness and ramification conclusions.
2. Loogle: `Ideal.map, RingEquiv, IsDiscreteValuationRing`: zero hits.
3. Mathlib grep: `branch.*conjug|normal.*tensor|isPretransitive_of_isGalois`
   in RingTheory: zero hits.
4. LeanSearch: “Automorphisms of a finite normal extension act transitively on
   normalized branches of complete discrete valuation rings”. Eight hits,
   including `IntermediateField.normal_iff_forall_map_eq`,
   `IsLocalRing.ResidueField.mapAut`, `galRestrict`, and
   `minpoly.exists_algEquiv_of_root`; none is this combined statement.
5. Local rg of `lean/WeilConjectures`, `lean/Sheaf`, and
   `dag/lean_names_upstream.json` for the item id, prospective declaration name,
   normal/branch/conjugacy, reduced tensor, ramification equivalence and
   transitivity terms found no exact declaration. Relevant existing downstream
   Epp helpers and separate tame/Galois ramification modules were inspected.

No STATEMENT-DISPUTED flag: the source proof's false fixed-field equality in the
inseparable case was already repaired by stage 1's invariant-positive-power
input. The theorem statement does not repeat that false equality and needs no
correction. Stacks more-algebra.tex at lemma-galois-relative and
lemma-special-case was opened locally, so no network source retrieval was needed.

Validation: scompile.py compiled both the module-mode sandbox and actual library
module successfully, without warnings (4.4 s and 4.0 s on the first successful
check). A syntax error in the last existential binder was repaired before that
successful check. The final explicit dependency imports passed the deliver2.py --no-push dry run:
preflight and per-file compilation both passed (dry-run commit 7f49f2b225c).

## Second reading by Q88

A separate self-review pass compared the actual theorem signature and node clause
by clause after successful compilation. The A/B completeness and local injection,
fraction-field towers, finite normal E/K without separability, actual integral
closures and nilradical reduction, canonical action formulas, transitivity, unique
fixed lower maximal ideal, every branch and every exponent n, and the one-index-1
implication are all present. The formula on f determines exactly the canonical
normalization inclusion. The ramification equation uses q extended to B_1 localized
at q, not an unrelated maximal ideal or a substitute numerical invariant. No
mathematical mismatch was found. Direct public imports of Algebra.Defs and
TensorProduct.Defs were added to make the recorded statement dependencies explicit.
This is a self-review by the dispatcher-started worker, not a claim of independent
agent review; the brief prohibits starting other agents. The maintainer's
independent delivery review remains the independent reading.
