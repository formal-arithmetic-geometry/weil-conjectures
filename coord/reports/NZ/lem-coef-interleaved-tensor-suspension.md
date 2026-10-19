## Worker report

Repaired the immutable delivery 51322f4b6b56, retaining its coefficient complex,
single-generator complex, direct-sum tensor totalizations, iterated tensor maps,
and integer sign exponent. The initial saved-packet dry run passed mechanically
(commit b74d149c6e, nothing pushed), but the returned H3/H8 defects remained in
its actual statement and documentation. This repair changes the Lean interface
and documentation substantively; it is not an unchanged re-push. Only the
item's `lean` field differs from the current shared node. No node statement,
proof, dependencies, or target statement is changed.

The module is `Sheaf.Algebra.Homology.InterleavedTensorSuspension`; the sole
postponed theorem is `CategoryTheory.interleavedTensorSuspension`. All eighteen
helpers have real data, and all nineteen declarations are recorded in
`lean.declarations`. The additional helpers belong to this comparison's own
interface: they specify its actual homogeneous pure tensors, rather than an
independent mathematical notion requiring another node.

Hypothesis and clause correspondence, read against the entire node:

| Node clause | Lean rendering |
| --- | --- |
| Size convention | Explicit universe `u`; `Coeff := ULift.{u} ℤ` and `ModuleCat.{u} Coeff` place the integer coefficients and arbitrary abelian groups in the universe required by Mathlib's monoidal module API. Every abelian group in this universe has its unique integer-module structure, transported along the lifted integer ring isomorphism. Thus this encoding imposes no mathematical restriction. |
| Arbitrary integer cochain complexes | `CoefficientComplex := CochainComplex (ModuleCat.{u} Coeff.{u}) ℤ`. There are no boundedness or flatness instances. |
| Every natural n, and n+2 factors | The theorem binds `(n : ℕ)` and its comparison family ranges over every `K : Fin (n + 2) → CoefficientComplex.{u}`. |
| Free E in degree -1 with zero differential | `suspensionGenerator` is Mathlib's single complex on the rank-one free module in degree `-1`; `suspensionElement` is the actual integer `1` transported by `HomologicalComplex.singleObjXSelf`. |
| Tensor differential and direct-sum totalization | `tensorComplex` uses `CochainComplex.mapBifunctor` with `curriedTensor`; this is Mathlib's total complex with the usual Koszul signs and coproducts in each total degree. |
| Ordinary V_n | `ordinaryTensor n K := iteratedTensor (n + 1) K`, recursively left-associated, contains all n+2 factors in their stated order. |
| Interleaved W_n | `interleavedTensor` inserts exactly n+1 copies of E in the stated order. Its zero case is `(K₀ ⊗ E) ⊗ K₁`. |
| Homogeneous inputs and their total degree | `a : Fin (n + 2) → ℤ`, `x : ∀ j, (K j).X (a j)`, and recursive `tensorDegree (n + 1) a` give arbitrary homogeneous elements and the sum of all their degrees. |
| Pure tensors are the prescribed actual elements | `tensorComplexPure` applies `TensorProduct.tmul` and `HomologicalComplex.ιMapBifunctor`; `iteratedTensorPure` iterates this inclusion. `shiftedOrdinaryTensorPure` uses the canonical shift-component isomorphism. `interleavedTensorPure` inserts the actual `suspensionElement` at each step. None of these inclusions includes a sign. |
| The prescribed alpha_n | `signExponent n a := (n : ℤ) + ∑ j, ((n + 1 - j.1 : ℕ) : ℤ) * a j`. Since `j < n+2`, the coefficient is exactly the integer n+1-j. |
| Forward sign formula | The first conjunct says `(Φ K).hom.f ... (shiftedOrdinaryTensorPure n K a x) = (signExponent n a).negOnePow • interleavedTensorPure n K a x`. `Int.negOnePow` is exactly the integer unit `(-1)^alpha`, including negative alpha. |
| Isomorphism V_n[n+1] to W_n | Each `Φ K` has type `(ordinaryTensor n K)⟦(n + 1 : ℤ)⟧ ≅ interleavedTensor n K`. It is an isomorphism of complexes, not merely graded objects or a quasi-isomorphism. |
| Inverse removes generators with the same sign | The second conjunct says `(Φ K).inv.f ... (interleavedTensorPure n K a x) = (signExponent n a).negOnePow • shiftedOrdinaryTensorPure n K a x`. This explicitly prescribes the inverse on all homogeneous interleaved pure tensors. |
| Naturality in all degree-zero factor maps | `∃ Φ : ∀ K, ...` occurs before the universal quantifiers over `K`, `L`, and `f : ∀ j, K j ⟶ L j`. The third conjunct is the square using `ordinaryTensorMap`, its shifted map, and `interleavedTensorMap`. The single chosen `Φ L` is independent of `f`. |
| Explicit internal differential identity | The fourth conjunct displays `(n + 1 : ℤ).negOnePow • (ordinaryTensor n K).d ...` between the canonical shift-component identifications, followed by the same `(Φ K).hom`. Its left side is `(Φ K).hom.f i ≫ W.d i j`. Thus it states exactly d_W Phi = Phi ((-1)^(n+1) d_V), with component transport shown explicitly. |
| No flatness or boundedness | No such hypotheses are present. All tensors use direct-sum totalization, so arbitrary unbounded complexes are included. |

Dependencies read and used:

- `def-weil-size-convention` has a convention record, not a declaration;
  explicit universe polymorphism implements it.
- `def-weil-pbc-module-tensor-product` is a Mathlib leaf. Its recorded
  `TensorProduct`, `TensorProduct.mk`, `TensorProduct.lift`, `lift.tmul`,
  `TensorProduct.ext'`, and `LinearMap.rTensor` signatures/docstrings were read
  in `Mathlib.LinearAlgebra.TensorProduct.Defs`, `.Basic`, and `.Map`.
  `TensorProduct.tmul` is used directly; `ModuleCat`'s `curriedTensor` is
  defined by these same tensor products and induced maps.
- `def-weil-abstract-derived-category` records Mathlib's `DerivedCategory` and
  `HasDerivedCategory` in `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
  Their signatures/docstrings were read. This item concerns complexes before
  localization, using that node's cochain-complex and shift conventions;
  no derived-category object is needed. The actual shift is the existing
  `CochainComplex.shiftFunctorObjXIso` and shift instance from
  `Mathlib.Algebra.Homology.HomotopyCategory.Shift`, where
  `shiftFunctor_obj_d'` explicitly has differential `n.negOnePow • K.d`.
- `CochainComplex.mapBifunctor` is defined in
  `Mathlib.Algebra.Homology.BifunctorShift`, whose import is needed even
  though the underlying general totalization is in `.Bifunctor`.
  `HomologicalComplex.mapBifunctorMap` and `ιMapBifunctor` give its maps
  and summand inclusions. `CochainComplex.singleFunctors` and
  `HomologicalComplex.singleObjXSelf` give E and its generator.

Source read: [Drinfeld, DG quotients of DG categories](https://arxiv.org/pdf/math/0210114),
§3.1, equations (3.1)-(3.2), and §3.6(i). Section 3.1 supplies the interleaved
word construction; §3.6(i) relates the quotient calculation to the bar
resolution. As the node itself records, this exact arbitrary-length sign
normalization and its proof are agent-explicit, rather than a quoted theorem
of the paper. Here E has zero differential: this lemma addresses the internal
word differential, not the additional contraction faces of the full quotient.
The theorem docstring includes the node's four proof steps, their dependencies,
the inverse sign calculation, naturality, the two differential exponents and
their difference 2n+2, and the unboundedness argument.

Edge cases checked: n=0 gives one generator and alpha=degree(a₀), with a -1
shift differential. At n=1 there are two inserted generators. Arbitrary
negative degrees and negative alpha are allowed by `Int.negOnePow`. Zero
factors cause no excluded case, and arbitrary torsion groups are allowed.
A finite Python parity check covered n=0 through 4, every degree tuple with
entries from -2 through 2, and all differentiated factors (112300 differential
cases); it confirmed the total degree, squared inverse sign, and exponent
difference 2n+2. The mathematical identities are also written in the proof
docstring; the finite check is only an edge-case check, not a Lean proof.

Searches for an existing comparison were retained and refreshed:

- Saved `msearch.py` / `leanfinder`: “Natural isomorphism interleaved tensor
  products of arbitrary cochain complexes with degree minus one integer
  generators and shift with explicit Koszul signs”. It found the binary
  `mapBifunctorShift₁Iso` / `mapBifunctorShift₂Iso` infrastructure and related
  component formulas; none gives the displayed arbitrary-length comparison.
- Refreshed `msearch.py` / `leanfinder`: “Canonical arbitrary length
  interleaved cochain tensor suspension isomorphism with forward and inverse
  pure tensor Koszul sign formulas natural in all chain maps”. Eight hits,
  including those binary isomorphisms and `HomologicalComplex.ιTensorObj`;
  no exact match. The existing general inclusions are reused through
  `HomologicalComplex.ιMapBifunctor`.
- Refreshed `msearch.py` / `loogle`:
  `HomologicalComplex.ιMapBifunctor, CochainComplex.shiftFunctorObjXIso`;
  zero combined-query hits. Both declarations were located and read directly
  in the Mathlib source and are used in the module.
- Refreshed `msearch.py` / `grep`:
  `interleav|suspension.*sign|tensor.*shift|shift.*tensor` in
  `Algebra/Homology`; zero service hits. Direct `rg` located the actual
  shift/tensor APIs, so this service result is not treated as their absence.
- Direct project `rg` for the item id found no upstream declaration. Searches
  for `interleav|interleavedTensorSuspension|signExponent` in upstream
  `WeilConjectures` and shared `lean/Sheaf` found only unrelated interleaved
  colimit diagrams upstream; no existing tensor-suspension comparison.
  Mathlib `rg` for the inclusion, single, shift, and sign names located the
  declarations used above.

There is no statement dispute or node correction. Clean `scompile.py` passed
for the final module in both its sandbox and actual module-path compilation,
with no warnings. The only `sorry` is the named main theorem.

## Returned points repaired

H3: The first and second conjuncts now specify the forward and inverse signs
on actual homogeneous pure tensors. The existential now chooses one family
`Φ` for every K before any factor map is quantified. The naturality square
uses this same family, and the internal differential equation explicitly
includes the required shifted sign. No target comparison may depend on the
map being tested.

H8: Every helper, including all map constructors and the six new homogeneous
element/degree helpers, now has a source/blueprint docstring. The theorem
contains the full four-step natural-language proof plan, with the termwise
sign computation and the n=0/unbounded cases.

## Second reading by Q32

Author's repair self-check, as this dispatcher brief forbids starting another
agent; independent immutable-head review belongs to the maintainer. I reread
the node and the complete repaired file. The saved statement's first mismatch
was absence of both explicit tensor sign formulas; these are now its first
two conjuncts, using `tensorComplexPure`, `suspensionElement`, and the canonical
shift-component transport. Its second mismatch was a target comparison chosen
inside the quantifier over maps; the new family `Φ` is chosen outside every
such quantifier. The old chain-map equation hid the shift sign; the new fourth
conjunct shows it explicitly. I checked the coefficient order in alpha, the
n+2 input count, n+1 inserted generators, the positive shift convention, and
both directions of the formulas against the node. Every helper's data is
constructed and every declaration has a source/blueprint docstring. No
mathematical hypothesis or conclusion of the node was changed.


### Independent immutable-head maintainer reading

Reviewed immutable head 706e5485675ad281a85385c2e3339870ec6f6b68 against
its snapshot, all three statement dependencies, Drinfeld §§3.1 (3.1)–(3.2)
and 3.6(i), and the exact Mathlib declarations. The clause table in the
Worker report is correct: lifted integer modules cover arbitrary abelian
groups at each universe; the single complex and its transported 1 give E
and epsilon; the recursive tensors preserve order and insert n+1 copies;
the pure tensors use actual unsigned summand inclusions; both signs and the
single natural family have the required quantifier order; the final equation
has the correct shifted differential. No flatness or boundedness is assumed.
At n=0 the sign is (-1)^degree(a0); negative degrees, torsion and zero factors
are included. Independent parity checking covered 112300 differential cases.

Mechanical H6 repair: replaced the three local omega proofs of degree-index
equalities in interleavedTensorPure by applications of existing Mathlib
sub_add_eq_add_sub, sub_eq_add_neg, sub_sub and equality congruence. These are
only index transports; the data and the main theorem signature are unchanged.
The only theorem still has proof sorry. All nineteen declarations have
source/blueprint docstrings, the four-step proof plan is present, and the
node lean.statement is verbatim equal to the unchanged signature. Searches
of Mathlib homology, upstream WeilConjectures and shared lean/Sheaf found no
existing arbitrary-length sign-normalized comparison. No new prerequisite,
statement correction or universe repair is necessary. The original and fixed
modules were checked with scompile.py; detailed command/results and final
verification are recorded in the independent review.md.


## Review by NZ

I reread the landed module and node against the target statement and all three dependency records. The signature preserves every hypothesis and clause: arbitrary n and n+2 complexes, the degree-minus-one generator, the explicit forward and inverse signs on homogeneous pure tensors, one comparison family chosen before naturality maps, and the shifted internal differential identity. The unchanged theorem compiles cleanly with scompile.py, and this packet changes only the author metadata and a documentation comment after synchronization with the already landed Q32 content.

## Second reading by NZ

Independent immutable-delivery maintainer reading of
2178e349d2baf6c98f6c35a5d491b85832fd5129, completed on 2026-10-17.
This section replaces the delivered placeholder; it records the present
independent review, not an additional worker reading.

I read packet.md first, then the immutable item node, all three statement
dependency nodes, the full delivered module and report, Drinfeld's cited
sections, and the exact Mathlib definitions and docstrings used. The Worker
report's clause table is correct. In particular:

- Explicit universe u and Coeff = ULift.{u} Z encode arbitrary abelian groups
  as ModuleCat.{u} Coeff: the lifted integer action is uniquely determined.
  No universe equality between independently sized mathematical objects,
  finiteness, flatness or boundedness assumption is imposed.
- n : Nat and K : Fin (n+2) -> CoefficientComplex quantify all stated inputs.
  CoefficientComplex is the existing integer-indexed CochainComplex; its
  morphisms are degree-zero chain maps.
- suspensionGenerator is the actual single complex of the rank-one module
  in degree -1, with zero differential; suspensionElement is its transported 1.
- tensorComplex uses mapBifunctor and curriedTensor, hence actual module
  tensor products and coproduct totalization. ComplexShapeSigns gives signs
  1 and (-1)^p for the two differential terms. tensorMap uses the induced
  mapBifunctorMap, rather than arbitrary chosen maps.
- iteratedTensor and ordinaryTensor retain all n+2 factors in their order;
  interleavedTensor inserts exactly n+1 copies of E. The associated maps
  apply the supplied maps on K and identities on E.
- tensorDegree is the sum of degrees. tensorComplexPure uses tmul followed
  by the unsigned summand inclusion; the recursive pure tensors therefore
  are the actual displayed tensors. shiftedOrdinaryTensorPure only applies
  the canonical shift-component identification.
- signExponent has coefficient n+1-j at every j, including coefficient zero
  at the last factor. Natural subtraction does not truncate a negative
  coefficient since j is in Fin (n+2). Int.negOnePow supports negative alpha.
- The first two conjuncts prescribe exactly the forward and inverse signs
  on homogeneous pure tensors. The existential selects one isomorphism
  family before quantification over all factor maps, so the third conjunct
  is the required naturality. Inverse naturality follows from the same
  isomorphism square.
- The fourth conjunct is the differential equation with the explicit
  (-1)^(n+1) and the correct canonical component transports. The isomorphism
  is in the category of complexes, not just graded groups or a localization.

I checked n=0 (one E, alpha=degree(a0), shift differential -d), n=1,
negative degrees, negative alpha, zero and torsion factors, and unbounded
complexes. There is no empty list of factors in the node, since n+2 >= 2.
Direct sums ensure finite support even for unbounded inputs. Independently,
112300 differentiated-factor cases for n=0..4 and degrees -2..2 confirmed
the degree and inverse signs and the exponent difference 2n+2. The symbolic
exponent calculation in the node proves the same parity identity for all n.

Source audit: Drinfeld section 3.1 (3.1)-(3.2) supplies the interleaved word
and its internal differential, and section 3.6(i) explains the bar comparison.
The full dg quotient additionally has contraction terms from d(epsilon_U)=id;
this lemma and its zero-differential E describe the internal word part only.
The node explicitly identifies its normalization as agent-explicit, rather
than claiming that the paper states this exact formula. The flatness needed
for the paper's derived bar comparison is unnecessary for this elementary
isomorphism. I also read the dependency blueprint sources and Stacks algebra.tex
section-tensor-product, and the relevant derived.tex section.

The dependency interfaces are usable without repair: size is a convention;
TensorProduct, tmul, mk, lift, ext' and LinearMap.rTensor give the recorded
module tensor product; DerivedCategory and HasDerivedCategory give the
recorded localization, while the part used here is its cochain shift
convention. Read exact APIs: ModuleCat monoidal tensorObj/tensorHom,
HomologicalComplex.single/singleObjXSelf, CochainComplex.singleFunctors,
mapBifunctor, iotaMapBifunctor, mapBifunctorMap, TotalComplexShape signs,
shiftFunctor, shiftFunctorObjXIso, and Int.negOnePow.

Independent rg searches for interleaving, suspension signs and Koszul
suspension in Mathlib homology, upstream WeilConjectures and group lean/Sheaf
found no separate implementation of this comparison. The group tree contains
this same delivered implementation; upstream interleaved-colimit results are
unrelated. Existing binary tensor/shift APIs are reused. The Worker report
records LeanSearch, LeanFinder/Loogle and grep searches. All eighteen helpers
contain real data and belong to this theorem's interface; no missing helper,
unstated DAG prerequisite, dependency repair or source correction is needed.

All nineteen declarations are listed in lean.declarations and carry source
and blueprint docstrings; the module docstring is present and the theorem's
four proof steps agree with the node. Its only proof body is sorry. The
applications of existing arithmetic equalities are index transports, with
no new local arithmetic theorem proof. No line exceeds 100 characters.
The node lean.statement is verbatim the theorem signature with source
whitespace normalized, from theorem through the last type expression.

Reproduction command (from the immutable review directory):

    python3 /home/ubuntu/weil-launcher-nt/scompile.py NZ lem-coef-interleaved-tensor-suspension snapshot/lean/Sheaf/Algebra/Homology/InterleavedTensorSuspension.lean

Exit status 0, no errors or warnings. The prescribed wrapper checked
Sheaf/Stage2/Sandbox0.lean (2.3 s) and the actual library path
Sheaf/Algebra/Homology/InterleavedTensorSuspension.lean (2.6 s).
The currently installed wrapper runs a server-side private overlay, despite
the older brief's local-overlay description; no direct ssh was invoked.
No global build, live Lean edit, repository mutation or branch change was made.

Finding and correction: the original exact NZ second-reading section was
only a disclaimer that no reading occurred (H1/H11 under the explicit review
requirement). Replaced that section with this substantive independent audit.
No mathematical, Lean, node-record or universe change is necessary.
