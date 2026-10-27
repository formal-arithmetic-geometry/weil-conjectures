## Worker report

The module `Sheaf.Algebra.Homology.DoubleEvaluationFiniteComponents` states
`CochainComplex.DoubleEvaluation.finite_components`. Its theorem and the two universe-generalized Hom differential lemmas have
`sorry` proofs. The support, component types, and ordinary tensor bifunctor have real
data. The tensor bifunctor uses the existing `TensorProduct` and its existing
`lTensor`/`rTensor`; its functor laws and zero preservation are structural proof
fields, with no postponed data. No new independent mathematical notion is added.

Hypothesis-by-hypothesis correspondence:

- `R : Type r` with `[CommRing R]` is the commutative coefficient ring.
- `P J I : CochainComplex (ModuleCat.{v} R) ℤ` are exactly the three ordinary
  module cochain complexes. The ring universe `r` and carrier universe `v`
  are independent; a common carrier universe accommodates any three complexes.
- `u ℓ a b : ℤ` and `hab : a ≤ b` are the four bounds and their stated ordering.
- `hfree : ∀ s, ∃ m, Nonempty (Module.Basis (Fin m) R (P.X s))` says every term
  has a finite basis. Enumerating a finite basis by `Fin m` is equivalent to
  existence of a basis indexed by any finite set; there is no positive-rank
  requirement. This uses the basis notion of the recorded free-module node.
- `hP`, `hJ`, and `hI` state termwise vanishing above `u`, below `ℓ`, and outside
  `[a,b]`, respectively, using `Subsingleton` of the underlying module.
  A subsingleton module is precisely a zero module. No chosen identification
  with a particular zero object is demanded.
- There is no injectivity, projectivity of J/I, nonzero-ring hypothesis, or
  extra condition on a differential. `n : ℤ` is arbitrary.

Clause-by-clause correspondence:

- `support u ℓ a b n` is the set of triples with `p+r+s=n`, `a≤p≤b`,
  `r≤-ℓ`, `s≤u`, in that order; the first conclusion says it is finite.
- The next conclusion gives both lower bounds `n-b+ℓ≤s`, `n-b-u≤r`, and
  repeats their stated upper bounds.
- The conclusion quantified over `k s` says the factor
  `P.X s →ₗ[R] J.X (s+k)` is subsingleton outside `ℓ-k≤s≤u`. Thus the
  product defining A has exactly the asserted potentially nonzero range.
- `moduleHomComplexOfUniverses J I` is H, `moduleHomComplexOfUniverses P J`
  is A. The two outer source/target terms are exactly T and B in degree n.
  `mapBifunctor` uses direct-sum totalization of the ordinary tensor bifunctor.
- `eT` is the asserted linear equivalence from T to the direct sum of
  `sourceComponent P J I t.val`. Its inverse on `DirectSum.lof t (g⊗x)`
  is fixed to the total tensor inclusion of the single cochain g, so it is
  the canonical component identification, not an unspecified isomorphism.
  Here the single cochain has degree p+r and source degree -r; its target
  degree is p since -r+(p+r)=p. The tensor inclusion has degree (p+r)+s=n.
- `eB` is the asserted linear equivalence from B to the direct sum of
  `targetComponent P J I t.val`. Its coordinate evaluated at f is the
  outer Hom coordinate of beta applied to the single f in A^{p-n}.
  The support equation makes s+(p-n)=-r, exactly the node's indices.
- `c t` is a linear equivalence of the two component modules. Its formula
  on pure tensors is `negOnePow (s*(r+1)) • g (f x)`, the specified sign
  `(-1)^{s(r+1)}`. The action is by integer units, so negative exponents
  have their ordinary parity meaning and characteristic two is covered.
- For every finite basis `e : Module.Basis ι R (P.X s)`, with independent
  index universe `w`, the `ιe` clause supplies the coordinate inclusions.
  The identity `ιe i v x = e.repr x i • v` gives exactly
  `ιe i v (e j) = δ_ij v` and determines these maps uniquely.
- `(c t).symm β = epsilon • ∑ i, (β.comp (ιe i)) ⊗ₜ e i` is precisely
  the inverse formula, for every component beta and every finite basis.
- `E` is an equivalence T^n ≃ B^n. The final equation
  `eB (E z) t = c t (eT z t)` identifies it with the direct sum of the
  signed components under the two canonical identifications. The equivalence
  types assert the two-sided inverse laws, including those of the total map.
- This is an assertion about linear equivalences of modules, not an
  isomorphism of complexes or derived objects. Adding differential
  compatibility would strengthen this particular node's last sentence.

Dependencies read and used:

- `def-weil-abstract-derived-category`: recorded
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory` and
  `HasDerivedCategory`; its underlying complex notion is Mathlib
  `CochainComplex`. The recorded module is publicly imported.
- `def-sc-module-total-hom-complex`: recorded
  `WeilConjectures.Algebra.Homology.ModuleHomComplex`,
  `CochainComplex.moduleHomComplex`, read in full. Its universe restriction
  is accommodated by the helper declarations in the item module described
  below. The item imports that upstream module and uses the same `HomComplex.Cochain`, `δ_hom`,
  `Cochain.v`, and `Cochain.single`.
- `def-pc-tensor-complex-sheaves`: recorded
  `Mathlib.Algebra.Homology.BifunctorShift`, `CochainComplex.mapBifunctor`
  and `ιMapBifunctor`, specializing the generic bifunctor totalization to
  ordinary modules. The cochain signs remain Mathlib's signs.
- `def-weil-pbc-free-module`: recorded
  `Mathlib.LinearAlgebra.FreeModule.Basic`, `Module.Free`; its basis notion
  is used directly as `Module.Basis`. A finite basis is explicit in hfree.
- `def-weil-pbc-module-tensor-product`: Mathlib match `TensorProduct`,
  `TensorProduct.mk`, `lift`, `ext'`, `LinearMap.rTensor`, `rTensorHom`;
  the definitions and signatures in Defs/Basic/Map were read. There is no
  missing Lean record to repair: the mathlib_match gives the needed notion.
- Proof-only `lem-weil-pbc-tensor-finite-product`: Mathlib match
  `TensorProduct.piLeft`, in `Mathlib.LinearAlgebra.TensorProduct.Pi`, read
  and imported privately. Its finite product comparison is used in the
  proof docstring, including the empty family.

The source read was `literature/stacks-project/more-algebra.tex`,
`lemma-internal-hom-evaluate-isomorphism` (Tag 0A68), proof of case (2),
lines 28562 onward, and `lemma-evaluate-and-more`, lines 18164 onward.
The latter gives the parity sign r+qr; renaming its third index to s
is exactly s(r+1) in this node. The finite-free component inverse is the
basis expansion of these canonical maps, as specified in the node's proof.
All nine proof steps are carried in the theorem docstring.

Edge cases checked before and during statement review: empty support and
empty s intervals; empty finite basis (rank zero); zero P/J/I; the zero ring;
a=b; arbitrary negative degrees and negative sign exponents; characteristic
two; and the degree-zero rank-one case. All are allowed by the binders.
There is no use of an infinite-product/Hom interchange: the support bounds
make each product used in the reindexing finite. No statement correction or
STATEMENT-DISPUTED fault was needed.

Searches actually run (the wrapper records are in sandbox searches.jsonl):

- `msearch.py ... leanfinder` query: "Bounded above finite free complex P
  bounded below J bounded I degreewise Hom(J,I) tensor P isomorphic to
  Hom(Hom(P,J),I)". Eight hits, including HasGoodTensor, HasTensor and the
  double-id corepresentability statements; none is this finite-support
  comparison with the given component maps.
- `msearch.py ... loogle` query: `"HomologicalComplex", "tensor"`.
  Twelve tensor-totalization infrastructure hits; no double evaluation.
- `msearch.py ... grep` query:
  `double.*Hom|Hom.*Hom.*tensor|evaluate.*isomorphism`, subdirectory
  `Algebra/Homology`: five hits in Double.lean, all unrelated two-term
  complexes.
- `msearch.py ... leansearch` query: "Module valued total Hom complex with
  arbitrary coefficient and module universes". Eight hits: existing Cochain,
  its Module instance, δ infrastructure and totalization, but no bundled
  independent-universe moduleHomComplex interface.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for doubleEvaluation,
  double_evaluation, finite_components, moduleHomComplex, and the new helper
  names. Existing ringed/sheaf comparisons have different objects and
  conclusions; none supplies this theorem. `grep -rn` of the item id in
  WeilConjectures found no declaration. `dag/lean_names_upstream.json`
  searches for the proposed namespace and universe-interface name found none.
- `rg` for tensor bifunctors in the project and Mathlib showed the ordinary
  `curriedTensor (ModuleCat.{u} R)` implementation in Monoidal.Basic has
  the ring and module universe equal. The private linearTensorRight in
  FlatEquationalCriterionOfUniverses is not a public reusable bifunctor.
  The helper here supplies only functor packaging for the existing tensor,
  not a second tensor product or total complex construction.

Validation: the initial equal-universe formulation compiled. The final
independent-universe formulation is compiled per file by `scompile.py`,
including the item module containing its universe helpers; no global build was run.
One missing colimits import and two unused `ext` patterns were diagnosed
and repaired; no linter is disabled. The dry run below checks the final
packet again, including the single delivered library module.

## Repair of H13

The returned head f8a73d4ad15d replaced the proved record of
`def-sc-module-total-hom-complex` with the generalized interface, dropping
its original declarations. This was a dependency-record regression.
The dependency node copy now matches the live file byte-for-byte, including
primary declaration `CochainComplex.moduleHomComplex` and the proved
`moduleHom_shape` / `moduleHom_square`. There is no dependency-record delta.

As requested in the return, `moduleHom_shapeOfUniverses`,
`moduleHom_squareOfUniverses`, and `moduleHomComplexOfUniverses` now reside
in `Sheaf.Algebra.Homology.DoubleEvaluationFiniteComponents` and are listed
in the item's `lean.declarations`. Their docstrings retain
`def-sc-module-total-hom-complex` and Tag 0A8H. The separate
`ModuleHomComplexOfUniverses` module is removed from this packet. These
helpers use exactly Mathlib's `HomComplex.Cochain` and `δ_hom`, accommodating
independent ring and carrier universes without changing any existing API.
Their two proof obligations have complete proof docstrings and belong to
the total-Hom construction already represented by the dependency node.
The data of the complex is explicit. The item theorem's signature and
proof docstring are unchanged; no statement or dependency-list correction
is needed, and no new node or dependency module is delivered.

## Second reading by Q69

A separate rereading pass compared the node text, the complete item and upstream source files,
and the Stacks source after elaboration. This is a self-review pass: the brief
forbids spawning agents and says the maintainer performs the independent
review; no independent worker review is claimed here.

The pass checked every bound and sign against the correspondence above.
In particular, it checked that t.2.1 is r (not the tensor degree p+r), that
beta's outer coordinate is p-n, and that the single f has target -r. It
checked the inverse quantifies over every finite basis and independent
basis-index universe, rather than selecting a basis in the hypotheses.
It found the upstream Hom and monoidal ModuleCat APIs imposed equal ring
and carrier universes; these were replaced by the equivalent generalized
Hom interface and ordinary tensor functor packaging. A second compilation
confirmed the generalized consumer elaborates. No differential-compatibility
conclusion was added to this expressly modulewise node. No other mismatch
was found; there are no new nodes or changed natural-language statements.

Repair self-check: compared the saved packet with the current live node and
read the upstream total-Hom source, including its proved shape and square
lemmas. The original item differed from live only in `lean`; the repaired
item retains that field boundary. The dependency JSON is byte-identical
to live. All three moved declarations retain their full signatures and
construction, and the finite-components signature is verbatim unchanged.
The item still publicly imports the recorded upstream module, so its
original declarations remain available to consumers. The independent
maintainer review already accepted every mathematical clause of the item;
this repair addresses its sole H13 point without altering those clauses.

Repaired-packet validation: the single delivered module passed the server
compiler and deliver2.py --no-push returned OK (b5505001e34). The staged
set contains only the item node, item module, and this report; the restored
dependency file produces no Git delta. The standalone self-check confirmed
verbatim theorem signature, unchanged non-lean node fields, explicit variables,
line widths at most 100, and exactly three named sorry theorem proofs.
