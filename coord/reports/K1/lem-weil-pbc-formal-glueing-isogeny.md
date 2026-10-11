## Worker report

The module `lean/Sheaf/RingTheory/FormalGlueingIsogeny.lean` states
`FormalGlueing.exists_map_to_of_torsion_baseChange` (part 1) and
`FormalGlueing.exists_map_from_of_torsion_baseChange` (part 2). Both include part 3.
Their only proofs are `sorry`; there are no new definitions, new nodes,
dependency replacements, or statement corrections.

Source read: Stacks Project More on Algebra, Lemma 0ALK and its full proof,
https://stacks.math.columbia.edu/tag/0ALK, also the local source
`/home/ubuntu/c1-stacks-review/more-algebra.tex`, lines 24880–24959.
The recorded additional canonical comparisons follow the node's proof via
05E9, flat tensor exactness, and right exactness.

Hypothesis and clause correspondence:

- Commutative rings and their map: `{R : Type u} {S : Type v}` with
  `[CommRing R] [CommRing S] [Algebra R S]`; the map is `algebraMap R S`.
  Every ring map supplies precisely this algebra structure via `RingHom.toAlgebra`.
- Flatness: `hflat : (algebraMap R S).Flat`, using the recorded `RingHom.Flat`.
- The finitely generated ideal: `(I : Ideal R) (hI : I.FG)`.
- The induced quotient isomorphism: `hquot : Function.Bijective
  (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map)`.
  This is the canonical ring map R/I → S/IS, not an arbitrary quotient isomorphism.
- Given R-module: `P` with `[AddCommGroup P] [Module R P]`.
- Given S-module: `Q` with `[AddCommGroup Q] [Module S Q]`;
  `[Module R Q] [IsScalarTower R S Q]` specify restriction of its S-action along
  the ring map. These are compatible scalar structures, not a flatness or
  finiteness assumption on Q. The tower forces r • x = algebraMap R S r • x.
- In part 1, P = N, Q = M′, and `φ' : Q →ₗ[S] S ⊗[R] P`.
  In part 2, P = M, Q = N′, and `φ' : S ⊗[R] P →ₗ[S] Q`.
- The torsion hypotheses are `hker` and `hcoker`: for every element of
  `(φ'.restrictScalars R).ker` and of the quotient by
  `(φ'.restrictScalars R).range`, there exists n with every r ∈ I^n killing
  that element. Restricting scalars before forming kernel/range gives exactly
  the underlying R-modules. This is the node's elementwise definition verbatim,
  expanded without introducing a second definition. Allowing n = 0 is equivalent
  to positive n: I^0 = R kills only zero, which is also killed by I.
- The new module is `∃ T : ModuleCat.{max u v w} R` (T = M in part 1, T = N
  in part 2), so both its additive group and R-module structure are supplied.
- In part 1 the map and equivalence are `ψ : T →ₗ[R] P` and
  `β : Q ≃ₗ[S] S ⊗[R] T`; compatibility is
  `(ψ.baseChange S).comp β.toLinearMap = φ'`.
- In part 2 they are `ψ : P →ₗ[R] T` and `β : S ⊗[R] T ≃ₗ[S] Q`;
  compatibility is `β.toLinearMap.comp (ψ.baseChange S) = φ'`.
- Part 3 torsion is the first two subsequent conjuncts, for `ψ.ker` and the
  quotient of its target by `ψ.range`, with the same elementwise condition.
- The canonical kernel comparison is an R-linear equivalence `k` satisfying
  `∀ x, (k x).val = (1 : S) ⊗ₜ[R] x.val`. This specifies the canonical map
  completely, including its target kernel, without hiding a well-definedness proof.
- The canonical cokernel comparison is an R-linear equivalence `c` satisfying
  `∀ y, c (ψ.range.mkQ y) =
  ((ψ.baseChange S).restrictScalars R).range.mkQ ((1 : S) ⊗ₜ[R] y)`.
  The quotient projection is surjective, so this specifies the canonical map
  completely, not merely the existence of an unrelated equivalence.
- The last two `Nonempty` conjuncts give the resulting R-linear kernel and
  cokernel equivalences with φ′. The compatibility equality for β determines
  the usual transport through β; these consequences are redundant with the
  preceding canonical equivalences and do not add a stronger hypothesis.

Dependency declarations used and inspected:

- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, its full definition and
  docstring (the R-module S is flat), with `RingHom.flat_algebraMap_iff`.
  The associated `Module.Flat` definition and its injectivity characterization
  in `Mathlib.RingTheory.Flat.Basic` were also inspected.
- `Mathlib.LinearAlgebra.TensorProduct.Tower`: `LinearMap.baseChange`, with
  its complete signature/docstring and `baseChange_tmul`; tensor product carrier
  `S ⊗[R] P`. This is exactly the dependency's recorded convention: the node's
  order P ⊗ S is related by `TensorProduct.comm`, and x ⊗ 1 becomes 1 ⊗ x.
- `Ideal.quotientMap` in `Mathlib.RingTheory.Ideal.Quotient.Operations` supplies
  the canonical quotient ring map; `ModuleCat` supplies the existential module.

Edge cases checked before writing: I = 0 (all modules are torsion, and the
quotient hypothesis makes R → S an isomorphism); I = R (torsion forces the
kernels and cokernels to vanish, including when S is the zero ring);
zero modules and zero rings; n = 0 (equivalent to the positive-exponent
convention); no nontriviality, Noetherianity, faithfulness or finite-module
assumptions are imposed. The common module universe `max u v w` can contain
both ring carriers and arbitrary input modules by increasing w; the existential
module can be built in that same universe by the glueing construction. There
is no independent smaller test-object universe and no bound on the number
of generators. The proof docstrings use `1 + ∑ eᵢ` so the empty generating
set causes no invalid positive-degree monomial argument.

Searches for an existing statement (actual tool results are in searches.jsonl):

- `leansearch` query `Formal glueing descent of a linear map with ideal power torsion kernel and cokernel along a flat ring map isomorphic modulo the ideal`: service unavailable: Internal Server Error.
- `leanfinder` query `Formal glueing of module homomorphisms with I power torsion kernel and cokernel`: 8 hits; AdicCompletion.transitionMap, AdicCompletion.incl, AdicCompletion.transitionMap_comp_reduceModIdeal, Hausdorffification.of, Submodule.factorPowSucc, IsAdicComplete.StrictMono.factorPow_comp_eq_of_factorPow_comp_succ_eq, AdicCompletion.exists_smodEq_pow_smul_top_and_mkQ_eq, AdicCompletion.lift.
- `loogle` query `LinearMap.baseChange, Module.IsTorsion`: 0 hits; .
- `grep` query `formal.glue|Beauville|isogeny`: 0 hits; .

LeanFinder returned adic-completion transition and lifting maps, not either
formal glueing assertion. Loogle and Mathlib grep returned no hits.
`rg` of the source project's WeilConjectures and this project's lean/Sheaf
for `lem-weil-pbc-formal-glueing-isogeny`, `formal.glue.*isogen`, and
`application.formal.glue` found no existing statement. The broader search
`formal.glue|0ALK|IsTorsion|IsTorsionBy` found the formal glueing DATA module
and unrelated torsion-by-an-ideal statements, not this descent lemma.
The upstream source has no matching declaration for this node's blueprint id.
No existing definition has been copied.

Validation: the server compiled the complete module cleanly (2.2 seconds).
No statement dispute or node fault was found. The empty-generator edge of
the node's proof is handled in the proof docstrings as described above.

## Second reading by K1

Independent reading of the node copy and both declarations in
`lean/Sheaf/RingTheory/FormalGlueingIsogeny.lean`. I read Stacks More on Algebra,
Lemma 0ALK (`lemma-application-formal-glueing`) and its whole proof in the
available local source `/home/ubuntu/c1-stacks-review/more-algebra.tex`,
lines 24880–24959, and Lemmas 05E9 and 05EC at lines 24264 and 24301.
The repository's literature/stacks-project directory is absent on this machine;
the local .tex copy supplies the cited text. The source introduces exactly the
flat map, finitely generated ideal and induced quotient isomorphism; there is
no ambient Noetherian, faithful-flatness, nonzero-ring, or finite-module
assumption. No statement correction is present or needed.

The node's object/hypothesis/conclusion list, matched item by item:

1. Commutative rings R and S and their ring homomorphism: section variables
   `{R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]`, with
   `algebraMap R S` as the homomorphism. Pass: every ring homomorphism defines
   such an algebra structure; this does not restrict the node to fields.
2. Flat ring map: `hflat : (algebraMap R S).Flat`. Pass: I opened the dependency
   node def-weil-pbc-flat-ring-map and its recorded Mathlib declaration
   `RingHom.Flat` in RingHom/Flat.lean:27. It is `Module.Flat R S` for the
   algebra defined by the map. The algebraMap equivalence and Module.Flat's
   injective-tensor characterization agree with the node's definition.
3. Finitely generated ideal I: `(I : Ideal R) (hI : I.FG)`. Pass: this concerns
   only I, not all ideals of R.
4. The induced map R/I → S/IS is an isomorphism: `hquot : Function.Bijective
   (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S)
   Ideal.le_comap_map)`. Pass: I read quotientMap's signature and its value
   on representatives in Ideal/Quotient/Operations.lean:596. The target ideal
   is the extension IS and this is the specified induced map, not a freely
   chosen isomorphism of the two quotient rings.
5. Base change of modules and maps: `S ⊗[R] P` and `ψ.baseChange S`. Pass:
   I opened def-weil-module-base-change and its recorded declaration
   `LinearMap.baseChange`, including its surrounding variables and tmul
   formula in TensorProduct/Tower.lean:661. The recorded convention explicitly
   uses this order; TensorProduct.comm converts the paper's P ⊗ S to it.
   In particular the paper's x ⊗ 1 becomes `1 ⊗ₜ[R] x`.
6. Part (1), objects and map: `P` is N, `Q` is M′, and
   `φ' : Q →ₗ[S] S ⊗[R] P`. The additive-group/module instances supply exactly
   the given modules. `[Module R Q] [IsScalarTower R S Q]` specify restriction
   of scalars: applying the tower identity to r, 1 and x forces the R-action
   to equal the S-action through algebraMap. Pass: no extra property of Q.
7. Part (1), torsion hypotheses: `hker` quantifies over
   `(φ'.restrictScalars R).ker`, and `hcoker` over the quotient by its range.
   Both say `∀ x, ∃ n : ℕ, ∀ r ∈ I ^ n, r • x = 0`. Pass: the exponent depends
   on x, every member of the ideal power kills x, and no uniform exponent is
   assumed. These are the underlying R-modules of the S-kernel and cokernel.
8. Part (1), existence and compatibility: `∃ T : ModuleCat R` (M), followed by
   `ψ : T →ₗ[R] P`, `β : Q ≃ₗ[S] S ⊗[R] T`, and
   `(ψ.baseChange S).comp β.toLinearMap = φ'`. Pass: the direction of β and
   the order of composition are exactly those in the node. ModuleCat bundles
   the existential additive group and module structure; I read Basic.lean:56.
9. Part (2), objects and map: in the second theorem `P` is M, `Q` is N′, and
   `φ' : S ⊗[R] P →ₗ[S] Q`, with the same ring, ideal and torsion hypotheses.
   Pass: the input roles have changed as the node requires.
10. Part (2), existence and compatibility: `∃ T : ModuleCat R` (N),
    `ψ : P →ₗ[R] T`, `β : S ⊗[R] T ≃ₗ[S] Q`, and
    `β.toLinearMap.comp (ψ.baseChange S) = φ'`. Pass: every existential comes
    after the given objects and hypotheses, and both arrows have the right
    direction.
11. Part (3), torsion of the descended kernel and cokernel: the first two
    conjuncts after compatibility in each theorem quantify over `ψ.ker` and
    the quotient of its target by `ψ.range`, respectively. Pass: they use the
    same elementwise I-power torsion condition as the hypotheses.
12. Part (3), canonical kernel isomorphism: `∃ k : ψ.ker ≃ₗ[R]
    ((ψ.baseChange S).restrictScalars R).ker` with
    `∀ x, (k x).val = (1 : S) ⊗ₜ[R] x.val`. Pass: the equation fixes the
    canonical map on every kernel element; an arbitrary equivalence would
    not suffice, but that weakening is not present here.
13. Part (3), canonical cokernel isomorphism: `∃ c` between the two range
    quotients, with `c (ψ.range.mkQ y)` equal to the base-changed quotient's
    `mkQ ((1 : S) ⊗ₜ[R] y)` for every target element y. Pass: mkQ is
    surjective, so this fixes precisely the canonical map on the entire
    cokernel. The targets are P in part (1), T in part (2).
14. Part (3), resulting isomorphisms with the given map: the last two
    `Nonempty` conjuncts provide R-linear equivalences with the kernel and
    cokernel of `φ'.restrictScalars R`. Pass: compatibility with β transports
    the preceding canonical comparisons. In (1), β identifies kernels and
    the ranges in S ⊗ P coincide; in (2), the kernels coincide and β carries
    the ranges to one another. Thus these existence clauses express the
    node's “hence” conclusions and introduce no stronger condition.

Edge cases: I = 0, including an empty generating family, is allowed. Every
module is then I-power torsion (take exponent 1), and hquot makes R → S
bijective. I = R is allowed: torsion means the element is zero, so hker and
hcoker say φ′ is an isomorphism; neither faithful flatness nor nontriviality
is silently required. Zero modules and zero rings are allowed. Allowing
n = 0 adds only elements killed by I^0 = R, hence only zero elements, which
are also killed by exponent 1. There is no characteristic restriction.
Schemes and index families are not input objects of this node. All universe
variables u, v, w are bound; the common `max u v w` accommodates the two rings,
arbitrary input modules and the constructed module. Smaller carriers can be
lifted to this common universe; no test-algebra quantifier is made vacuous by
an independent smaller universe. The proof docstrings already use positive
`1 + ∑ eᵢ`, which handles an empty generating family correctly (the node's
sum-only proof argument needs that minor empty-family adjustment).

Independent searches, recorded by msearch.py in searches.jsonl:

- LeanFinder: “Descent of homomorphisms of modules along a flat algebra
  isomorphism modulo a finitely generated ideal with power torsion kernel
  and quotient”: eight hits, namely flat-module factorization criteria,
  formally smooth flatness, localization flatness and adic-completion
  flatness; none states either descent assertion.
- Loogle: `LinearMap.baseChange, Function.Bijective`: zero hits.
- Mathlib grep: `glueing|gluing|algebraiz|isogen` in RingTheory returned
  unrelated algebraize commands; the focused full-Mathlib search
  `Beauville|Laszlo|formal.glue|formal.gluing` returned zero hits.
- Direct rg in repository lean/Sheaf, upstream WeilConjectures and
  dag/lean_names_upstream.json for glueing/gluing/0ALK and the declaration
  names found FormalGlueingData and unrelated sheaf/scheme gluing, not this
  statement. A focused torsion/baseChange search found only torsion-sheaf
  base change and abelian-variety geometric-point torsion. The first worker's
  recorded LeanSearch request was unavailable; that failure is not treated
  as evidence of absence. These additional successful semantic, type-pattern
  and text searches corroborate that no existing declaration realizes this
  node. No private definition is introduced.

No new definition nodes or dependency modules are delivered, so H12/H13
have no additional objects to check. There are no definitions at all in this
module, hence no hollow data. Both theorem proofs are exactly `by sorry`.
Both docstrings give the source and blueprint id and cover all seven proof
steps: localization, constructing the glueing datum and morphism,
algebraization/full faithfulness, the inverse construction for part (2),
torsion of the descended kernel/cokernel, flat/right-exact tensor comparison
and torsion base-change comparison, and transport through β. The imports
supply the flat-map predicate, quotient-map hypothesis, tensor base change,
and existential module, respectively. Header, namespace and line lengths
follow the project conventions. The node's lean.statement is verbatim the
first theorem signature; lean.declarations lists both parts.

Mismatches found: none in either Lean statement. Changes: appended this
independent second reading and its searches only; retained both declarations,
their docstrings and the node unchanged. Validation: single-file scompile.py,
then deliver2.py --no-push and the final delivery, as required.
