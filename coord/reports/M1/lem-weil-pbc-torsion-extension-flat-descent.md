## Worker report

The module Sheaf.RingTheory.TorsionExtensionFlatDescent states
LinearMap.exists_torsion_extension_flat_descent; its sole proof is `sorry`.
No definition, new node, dependency replacement, or statement correction is needed.

Hypothesis and conclusion correspondence:
- Commutative rings and the ring map: `R`, `S`, `[CommRing R]`, `[CommRing S]`,
  `[Algebra R S]`; the map is `algebraMap R S`. An arbitrary ring map supplies this
  algebra structure via `RingHom.toAlgebra`, so no ring map is excluded.
- Flatness: `_hflat : (algebraMap R S).Flat`.
- Finitely generated ideal: `I : Ideal R`, `_hI : I.FG`.
- Isomorphism on the quotients: `_hquot : Function.Bijective (Ideal.quotientMap
  (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map)`.
  `I.map` is the generated extended ideal, and bijectivity of this ring homomorphism
  is precisely that the canonical ring map is an isomorphism.
- R-modules N and Q: `[AddCommGroup N] [Module R N]` and the corresponding binders for Q.
- I-power torsion with positive exponent: `_hQ : ∀ x : Q, ∃ n : ℕ, 1 ≤ n ∧
  ∀ r ∈ I ^ n, r • x = 0`. This uses the elementary ideal action directly.
- S-module middle term and S-linear end maps: `M'` with its additive group and module
  instances, `ι : S ⊗[R] N →ₗ[S] M'`, `π : M' →ₗ[S] S ⊗[R] Q`.
- Given short exactness: `_hι`, `_hιπ`, `_hπ` express injectivity, Function.Exact,
  and surjectivity respectively. Function.Exact equates the range with the zero fibre.
- Descended extension: the existential E, its AddCommGroup and Module R structures,
  `j : N →ₗ[R] E`, `q : E →ₗ[R] Q`, and the corresponding three exactness conjuncts.
- Isomorphism and commuting diagrams: `θ : S ⊗[R] E ≃ₗ[S] M'`,
  `θ.toLinearMap.comp (j.baseChange S) = ι`, and
  `π.comp θ.toLinearMap = q.baseChange S`.

Dependency declarations: Mathlib.RingTheory.RingHom.Flat, RingHom.Flat;
Mathlib.LinearAlgebra.TensorProduct.Tower, LinearMap.baseChange and TensorProduct.
Their signatures and docstrings were read in the source checkout. Tensor factors use
Mathlib's left-factor scalar extension, identified with the node's right-factor order
by TensorProduct.comm, exactly as def-weil-module-base-change records. Ideal.quotientMap
comes from Mathlib.RingTheory.Ideal.Quotient.Operations. No private copies are introduced.
N, Q, and M' have independent universes. E is in max u w x: every extension of Q by N
has a carrier equivalent to N × Q after choosing fibres, hence this bound loses no case.

Edge cases: I = 0 makes every Q torsion and the quotient assumption makes R → S an
isomorphism. I = top forces Q = 0; the extension then descends as N. Zero N, zero Q,
and the zero ring are allowed. The positive bound excludes n = 0 without excluding the
zero element, which is killed by every positive ideal power. No finiteness is imposed
on N or Q; no faithful flatness is assumed.

Searches: msearch leanfinder, “Extensions by ideal power torsion modules descend along
flat ring maps inducing an isomorphism modulo a finitely generated ideal”, returned
adic-completion flatness and exactness results, no extension-descent theorem.
msearch loogle, “LinearMap.baseChange, Function.Exact”, returned no hits.
msearch grep, “torsion.*extension|extension.*flat.*descent”, returned only torsion-group
extension closure, unrelated. rg with the same pattern in WeilConjectures returned no
hits, including a search for the exact node id. In lean/Sheaf it found the cyclic
special case and the conditional direct-sum assembly theorem, neither the present
arbitrary torsion quotient statement. Their modules were inspected to check conventions.
The upstream name index was checked for the proposed name; no duplicate declaration.

The local literature .tex files are absent; the source was read at
https://stacks.math.columbia.edu/tag/05EH, whose Ext isomorphism specializes to
surjectivity on Ext¹, exactly the extension-existence conclusion here.
No statement fault or STATEMENT-DISPUTED issue was found. The declaration docstring
contains all five proof steps and names the DAG lemmas needed for stage 3.

## Second reading by M1

I independently read the sandbox node and module, both statement-dependency nodes,
and the recorded Mathlib declarations. The local Stacks .tex files are absent.
I read the labelled lemma-neighbourhood-extensions in the upstream dualizing.tex
and more-algebra.tex, as well as the published tags
[05EH](https://stacks.math.columbia.edu/tag/05EH),
[05EG](https://stacks.math.columbia.edu/tag/05EG), and
[05ER](https://stacks.math.columbia.edu/tag/05ER).
The source allows general commutative rings and arbitrary modules. It imposes no
Noetherian, faithful-flatness, finite-generation-of-modules, or characteristic
condition. The node deliberately states only surjectivity of the Ext-one comparison,
as existence of an extension with an endpoint-preserving base-change isomorphism.
This is also the interpretation explicitly given in the proof of 05EG.

The object/hypothesis/conclusion checklist, in the node's order:

1. Commutative rings R and S and an arbitrary ring map phi: the binders
   `{R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]`
   use `algebraMap R S` for phi. Every commutative-ring homomorphism induces such
   an algebra structure via `RingHom.toAlgebra`. Verdict: same objects and map.
2. Flat phi: `_hflat : (algebraMap R S).Flat`. I read RingHom/Flat.lean: its
   definition is Module.Flat R S with the R-action supplied by phi.toAlgebra;
   `RingHom.flat_algebraMap_iff` identifies it with flatness for the given algebra.
   This is precisely def-weil-pbc-flat-ring-map. Verdict: exact hypothesis.
3. Finitely generated ideal I: `(I : Ideal R) (_hI : I.FG)`.
   Verdict: exactly the stated ideal and finiteness assumption.
4. The induced map R/I to S/IS is an isomorphism: `_hquot` is bijectivity of
   `Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S)
   Ideal.le_comap_map`. I read quotientMap in Ideal/Quotient/Operations.lean:
   it sends the class of r to the class of phi(r), and `I.map` is the generated
   image ideal. Bijectivity of this ring homomorphism is equivalent to a ring
   isomorphism with that underlying map. Verdict: exact, canonical map.
5. Arbitrary R-modules N and Q: the Type w and Type x binders with AddCommGroup
   and Module R structures. Verdict: no extra finiteness or torsion condition on N.
6. Q is I-power torsion: `_hQ : ∀ x : Q, ∃ n : ℕ, 1 ≤ n ∧
   ∀ r ∈ I ^ n, r • x = 0`. An ideal annihilates x precisely when every element
   acts by zero. The exponent depends on x, as in the node.
   Verdict: exact hypothesis, no uniform exponent added.
7. Base changes of modules and maps: `S ⊗[R] N`, `S ⊗[R] Q`, and
   `j.baseChange S`, `q.baseChange S`. I read TensorProduct.leftModule and
   LinearMap.baseChange in Defs.lean and Tower.lean; the latter maps s tensor n
   to s tensor f(n). This is def-weil-module-base-change's recorded left-factor
   encoding, equivalent to the node's right-factor encoding by tensor symmetry.
   Verdict: the shared dependency notion is used, without a private replacement.
8. Given S-module M' and S-linear maps iota and pi: `{M' : Type y}` with its
   structures, `ι : S ⊗[R] N →ₗ[S] M'`, and
   `π : M' →ₗ[S] S ⊗[R] Q`. Verdict: exactly the given extension's objects/maps.
9. Given short exactness: `_hι`, `_hιπ`, `_hπ` are Function.Injective,
   Function.Exact, Function.Surjective. I read Algebra/Exact/Basic.lean:
   Exact means pi(m) = 0 iff m is in the image of iota.
   Verdict: exactly all three parts of short exactness.
10. Existence of an R-module E and R-linear j and q: the existential E, its
    AddCommGroup and Module R structures, `j : N →ₗ[R] E`, `q : E →ₗ[R] Q`.
    Verdict: structures and maps are genuinely supplied in the conclusion.
11. Descended short exactness: `Function.Injective j ∧ Function.Exact j q ∧
    Function.Surjective q`. Verdict: all three clauses are present.
12. S-linear isomorphism from E's base change to M':
    `∃ θ : S ⊗[R] E ≃ₗ[S] M'`. Verdict: actual linear equivalence, not only
    equality of unlabelled middle terms or a bare map.
13. Both endpoint equations: `θ.toLinearMap.comp (j.baseChange S) = ι` and
    `π.comp θ.toLinearMap = q.baseChange S`. Verdict: the exact two equations
    with the correct order of composition. All given objects precede the
    existential extension and its comparison; no uniqueness clause is added.

Edge cases: I = bottom makes every Q torsion, and the quotient-map hypothesis
then makes phi an isomorphism. I = top makes Q zero, and the extension is the
one with middle term N after base change. Zero N, zero Q, and zero M' are allowed
whenever the given short exactness holds. The zero ring is allowed; no Nontrivial
instance occurs. A zero element has a positive annihilating exponent. Allowing
n = 0 would add no torsion elements, since I^0 is top and hence kills only zero;
the current positive bound agrees verbatim with the node. Characteristics are
unrestricted. There is no index set or scheme binder, so empty index sets and
empty schemes introduce no additional case in this statement.

Universes u, v, w, x, y are explicitly declared and independent for R, S, N, Q,
M'. E is in Type (max u w x). This is sufficient: a short exact extension of Q
by N has, after choosing one representative of each fibre, a carrier equivalent
to N × Q; transport its module structure and lift that carrier to max u w x.
Thus the output bound does not restrict the supplied middle term M' or exclude
an extension class. There are no test-object quantifiers with a smaller universe.

Independent searches used different terms from the worker's report:
- msearch leanfinder: "short exact sequence descends scalar extension isomorphism
  modulo ideal torsion quotient". Eight hits, including ModuleCat.smulShortComplex,
  QuotSMulTop.map_exact and tensor quotient equivalences; none states this descent.
- msearch loogle: `"baseChange", "Exact"`. Ten hits, for cotangent exact sequences,
  IsBaseChange.of_left_exact/of_right_exact and categorical base-change exactness;
  none gives existence of the descended extension.
- msearch grep: `neighbourhood.*extension|torsion.*descent|descen.*torsion`.
  Only CommGroup finite-torsion descent hits, unrelated to modules and extensions.
- Direct rg of WeilConjectures, lean/Sheaf, Mathlib's Algebra/Homology and
  RingTheory/Flat, and dag/lean_names_upstream.json using
  `ext.*(flat|torsion)|descent.*extension|extension.*descen` and the proposed name.
  No general theorem or duplicate declaration name exists. I opened the actual
  signatures in CyclicExtensionFlatDescent, DirectSumExtensionAssembly and
  ExtOneDirectSum: the first is the cyclic quotient special case, the second
  assumes summand descent, and the third compares direct-sum extension classes.
  None is this item. The two recorded statement dependencies are already usable;
  there are no new nodes or dependency modules in this delivery to review.

No mismatch was found and no mathematical statement, Lean module, or node record
was changed. The sole theorem proof is sorry; there are no definitions or auxiliary
proved declarations. The header, topic, namespace, source docstrings, and the five
docstring proof steps agree with the node, including the transported kernel lift,
quotient extension, and both final endpoint checks. All imports serve the displayed
signature. I checked that lean.statement equals the source signature verbatim and
that no line exceeds 100 characters. This section is the only review change.
