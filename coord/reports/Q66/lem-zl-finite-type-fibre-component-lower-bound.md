## Worker report

The module `Sheaf.RingTheory.FiniteTypeFibreComponentLowerBound` states the
affine component lower bound from Stacks Tag 0B2L (2)(a).  It quantifies a field `k`, finite
type `k`-algebras `B` and `C`, a domain structure on `C`, an algebra homomorphism `φ`, and a
maximal ideal `m` whose residue-field structure map from `k` is bijective.  The ideal generated
by the images of `m` is rendered by `Ideal.map φ.toRingHom m`, and `C/J` is rendered by the
commutative-ring quotient `C ⧸ Ideal.map φ.toRingHom m`.  Its irreducible components are
`W ∈ irreducibleComponents (PrimeSpectrum (C ⧸ Ideal.map φ.toRingHom m))`.

The conclusion supplies natural numbers `dC` and `dA` witnessing the finite nonnegative ring
dimensions of `C` and `B / ker φ`, and requires every component
to have topological Krull dimension at least `dC - dA`.  If the quotient is the zero ring,
`PrimeSpectrum` has no points and the component universal statement is vacuous, as required.
The kernel is exactly `RingHom.ker φ.toRingHom`, so the quotient is `B/P` from the node.

The statement uses the following dependency declarations (all are Mathlib records from the
node): `Algebra.FiniteType` (`Mathlib.RingTheory.FiniteType`),
`irreducibleComponents` (`Mathlib.Topology.Irreducible`), `AlgebraicGeometry.Spec` as the
recorded affine-spectrum notion (the Lean statement uses its underlying `PrimeSpectrum`),
`topologicalKrullDim` (`Mathlib.Topology.KrullDimension`), and `ringKrullDim`
(`Mathlib.RingTheory.KrullDimension.Basic`).  The topological instance for prime spectra is
provided by `Mathlib.RingTheory.Spectrum.Prime.Topology`.

Edge cases checked: `m` is allowed to be any maximal ideal, including the zero ideal for a
field; `C` is a domain so its kernel quotient is nonzero and its ring dimension is nonnegative;
`C ⧸ J = 0` gives an empty prime spectrum and hence no components; `dA = 0` gives
the lower bound `dC`; `dC = 0` and `dC = dA` give the lower bound zero. Natural subtraction gives the same inequality as
integer subtraction: for a negative difference the inequality is automatic since an irreducible
component is nonempty and has nonnegative dimension; for a nonnegative difference they agree.
In fact the source generic transcendence-degree calculation gives `dA ≤ dC`, but this is
not added as an extra conclusion.

Searches made: `msearch.py ... leanfinder "finite type algebra fibre component dimension lower bound"`
returned only transcendence-degree, smoothness, finite-fibre, and inertia-degree declarations,
with no matching theorem; `msearch.py ... grep "topologicalKrullDim|ringKrullDim|irreducibleComponents" Mathlib`
returned no direct component-bound declaration; `rg` over `WeilConjectures/` and project
`lean/Sheaf` found no declaration of this affine lower bound.  The existing nearby declarations
are dimension-at-point/component and generic finite-type tools, not this statement.

Compilation: `scompile.py Q66 lem-zl-finite-type-fibre-component-lower-bound` passes with no
errors or warnings other than the expected `sorry` declaration warning.

Final source and convention check: read `varieties.tex` at the labelled lemma
`lemma-dimension-fibres-locally-algebraic` (Tag 0B2L), including its generic-point proof.
The affine spectrum is the underlying space of `AlgebraicGeometry.Spec`; its recorded
module is publicly imported. The theorem is in namespace `Algebra`, in the `RingTheory`
topic. All universes and variables are explicitly bound. Every available proof-dependency
module is imported without `public`, and the docstring carries all seven DAG proof steps.
The only theorem proof in the delivered module is `sorry`. No node fields other than
`lean` change, and no new or dependency modules are needed.

Additional search: `msearch.py ... loogle '"ringKrullDim", Algebra.FiniteType'`
returned zero hits. Direct `rg` for the item id and fibre-component lower-bound names in
upstream, side sources, and the upstream names index found no matching declaration.
The grep search over Mathlib was refined to `RingTheory/KrullDimension` to inspect
quotient-dimension and height inequalities separately from this component bound.

The finite-type dependency record was concurrently updated to `RingHom.FiniteType`; the
explicit `Algebra.FiniteType k B` and `Algebra.FiniteType k C` used here are its underlying
algebra-instance predicate on the given field structure maps, as allowed by that node.

The refined Mathlib grep returned 25 hits on field dimensions, regular-element quotients,
module support, and local-ring/PID dimensions; none bounds every closed-fibre component.
`msearch.py ... leansearch "Every irreducible component of the rational closed fibre of a map
of finite type algebras over a field has dimension at least source dimension minus image
dimension"` returned eight hits on embeddings, component preimages, Noetherian finiteness,
fibre correspondences, and finite morphisms; none states this dimension estimate.

Hypothesis and conclusion correspondence:

| Node clause | Lean |
| --- | --- |
| Arbitrary field `k` | `(k : Type u) [Field k]` |
| Commutative finite type `k`-algebras `B,C` | `[CommRing B] [Algebra k B] [Algebra.FiniteType k B]` and the same for `C` |
| `C` integral domain | `[IsDomain C]` |
| Unital `k`-algebra map | `(φ : B →ₐ[k] C)` |
| Kernel `P` | `RingHom.ker φ.toRingHom` |
| Maximal ideal `m` | `(m : Ideal B) (hm : m.IsMaximal)` |
| Specified structure map is an isomorphism | `Function.Bijective (algebraMap k (B ⧸ m))` |
| Ideal generated by images of `m` | `Ideal.map φ.toRingHom m`, the span of the image |
| Every fibre component | `∀ W : Set (PrimeSpectrum ...), W ∈ irreducibleComponents ... → ...` |
| Component dimension with subspace topology | `topologicalKrullDim W` on the subset subtype |
| Finite nonnegative ring dimensions | `∃ dC dA : ℕ, ringKrullDim C = ... ∧ ringKrullDim (B ⧸ ker φ) = ... ∧ ...` |
| Required lower bound | `((dC - dA : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim W` |
| Zero quotient gives vacuity | The empty prime spectrum has no irreducible components |

The distinct universes `u v w` impose no equality between the field and the two rings.
The structure map in the rationality hypothesis is the canonical map, not an arbitrary
isomorphism between the underlying rings.

## Second reading by Q66

Independent maintainer second reading of immutable delivery
`58a2d4ec2b84d80c6a716e940ae05454b2958f9b`, performed 2026-10-18.
The reader did not author this delivery. The worker report above is preserved.

Source read: Stacks `varieties.tex`, lines 3953-4018, Tag 0B2L,
`lemma-dimension-fibres-locally-algebraic`, including the hypotheses and proof of
(2)(a). Affine finite type algebras give locally algebraic schemes; a domain gives
an irreducible source and the image closure is Spec(B/ker φ). At the generic point
of a closed-fibre component the local fibre dimension equals that component's
dimension. Thus the node is precisely the specified affine rational-fibre
consequence of the source, with no omitted source assumption.

| Node object, hypothesis or conclusion | Checked Lean rendering and verdict |
| --- | --- |
| Field k | `(k : Type u) [Field k]`; exact, arbitrary characteristic. |
| Commutative finite type k-algebras B and C | Separate `Type v`, `Type w`, `CommRing`, `Algebra k`, and `Algebra.FiniteType k` instances; exact. |
| C is an integral domain | `[IsDomain C]`; includes nontriviality as intended. |
| Unital k-algebra homomorphism φ | `B →ₐ[k] C`; includes compatibility with the specified structure maps. |
| P = ker φ | `RingHom.ker φ.toRingHom`; the actual kernel, without an injectivity assumption. |
| Maximal ideal m | `(m : Ideal B) (hm : m.IsMaximal)`; exact propositional hypothesis. |
| Structure map k → B/m is an isomorphism | `Function.Bijective (algebraMap k (B ⧸ m))`; bijectivity of this canonical ring map is equivalent to the required isomorphism. |
| J generated by φ(m) | `Ideal.map φ.toRingHom m`; definition is the span of the image, not merely its set image. |
| Closed-fibre spectrum | `PrimeSpectrum (C ⧸ Ideal.map φ.toRingHom m)`; definitionally the underlying topological space of the recorded affine Spec. |
| Every irreducible component W | `∀ W : Set ..., W ∈ irreducibleComponents ... → ...`; maximal nonempty irreducible subsets, exactly the node. |
| Subspace topological dimension of W | `topologicalKrullDim W`; set-to-type coercion supplies the induced topology. |
| Both ring dimensions finite nonnegative integers | `∃ dC dA : ℕ`, followed by both equalities in `WithBot ℕ∞`; witnesses are uniform for all W. |
| dim W ≥ dim C − dim(B/P) | `((dC - dA : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim W`; exact here: B/P embeds in C and the finite-type dimension/trdeg theorem plus the lifted tower identity gives dA ≤ dC. |
| C/J = 0 | Empty prime spectrum has no nonempty irreducible component; the universal component assertion is vacuous, while the two ring-dimension witnesses remain required. |

All five immutable statement dependency records were read. Their exact sources
were opened: `Mathlib/RingTheory/FiniteType.lean` (`Algebra.FiniteType` at 39,
`RingHom.FiniteType` at 217 and `finiteType_algebraMap`),
`Mathlib/Topology/Irreducible.lean` (`IsIrreducible` at 52 and
`irreducibleComponents` at 107), `Mathlib/AlgebraicGeometry/Scheme.lean`
(`Spec` at 470), `Mathlib/AlgebraicGeometry/Spec.lean` (`Spec.topObj` at 58),
`Mathlib/Topology/KrullDimension.lean` (`topologicalKrullDim` at 39), and
`Mathlib/RingTheory/KrullDimension/Basic.lean` (`ringKrullDim` at 30).
The finite-type record now names RingHom.FiniteType, but its defining predicate
is Algebra.FiniteType on the induced algebra structure; the algebraMap lemma
confirms the rendering used here. This is no private replacement definition.
Sources for these notions were also read: Stacks 00F3 (`algebra.tex`:518),
004V (`topology.tex`:855), 0055 (`topology.tex`:1392), 00KE
(`algebra.tex`:14327), and the recorded affine-spectrum blueprint source with
its 01HW affine-scheme context.

The declaration docstring covers all seven node proof steps in order:

1. The kernel is prime because C is a nonzero domain; quotient and compatible
   scalar structures give A ↪ C and the fraction-field inclusion. Generation
   descent and restriction of scalars are elementary finite-generation arguments.
2. `finiteType_domain_ringKrullDim_eq_trdeg` applies to C and B/P. The tower
   theorem, including `lift_trdeg_add_eq` for distinct universes, identifies the
   nonnegative difference with trdeg_K L. No universe equality is needed.
3. `IsLocalization.tensor`/`tensorRight` and
   `isDomain_of_le_nonZeroDivisors` supply the generic-fibre localization and
   domain; the node explains the residue-field identification, quotient action,
   tensor swap, and finite generation. All hypotheses follow from injectivity.
4. `topologicalKrullDimAt_eq_ringKrullDim_add_trdeg` applies to the finite type
   K-algebra F at its zero prime. Its local ring and residue field are L, so
   local dimension is the computed d. The map to κ(0) is the localization
   inclusion, so the fibre point really is the zero prime.
5. Rationality identifies κ(m) with k through the structure map. The explicitly
   described tensor/quotient inverse maps give the actual closed fibre C/J;
   they kill the generators of J. The zero-ring case is handled separately.
6. `PrimeSpectrum.zeroLocus_minimalPrimes`, the prime/irreducible-closed
   correspondence, and `dimension_at_point_components` apply to H. Minimality
   means only W contains its generic point. Contraction to m uses maximality;
   the specified spectrum homeomorphism preserves local dimension by matching
   open neighbourhoods and `IsHomeomorph.topologicalKrullDim_eq`.
7. `fibre_dimension_bounded_open_upstairs` applies to B → C (finite type by
   Step 1) with the finite natural dimension n from Step 6.
   `PrimeSpectrum.closure_singleton` shows that its neighbourhood contains the
   zero prime of C. The bound there gives d ≤ dim W.

The named proof dependency statements and available module signatures were
read in the read-only group clone when not included in the extracted snapshot.
They match the uses above. No missing helper or unusable interface requiring
§1(A)/(B), or source correction requiring §1(C), was found. No new nodes,
dependency modules, or statement_change occur in this delivery.

Edge cases checked: B = k, m = 0, and C = k[x_1,...,x_n] gives equality n;
C = k and a rational maximal kernel gives zero; k[t] → k[x,y], t ↦ xy,
at m = (t), gives two one-dimensional components and lower bound 1;
k[s,t] → k[x], s ↦ x, t ↦ 0, has a nonzero kernel and lower bound 0;
at m = (s,t-1) that map has J = C and an empty fibre. Nonreduced closed
fibres are allowed. No algebraic closure, perfectness, injectivity of φ,
flatness, equidimensionality of the fibre, or separate Noetherian assumption
is imposed. Universes u, v, w and all binders are explicit.

Independent duplicate searches used alternate wording (`fiber`, `fibre`,
component dimension, quotient/height, and kernel) in Mathlib's KrullDimension
and AlgebraicGeometry sources, upstream WeilConjectures, and group lean/Sheaf.
The worker report records LeanSearch, LeanFinder/Loogle and grep searches.
No matching declaration existed in the delivery parent. A current-group
`Sheaf.DeligneLaumon.FiniteTypeFibreComponentLowerBound` with declaration
`finiteTypeFibreComponentLowerBound` was inspected; git history places its
addition in later batch 8651b88264 (2026-10-18 04:01 +0800), after this delivery
(03:53 +0800), and the delivery parent lacks it. This later landing is not
an H4 defect in the immutable delivery. Current landing must respect that
already-landed binding rather than install two competing implementations.

Compiler reproduction, using the immutable delivered file:

`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q66 lem-zl-finite-type-fibre-component-lower-bound snapshot/lean/Sheaf/RingTheory/FiniteTypeFibreComponentLowerBound.lean`

Exit 0. The wrapper reported sandbox compilation in 1.5 s and library
`Sheaf/RingTheory/FiniteTypeFibreComponentLowerBound.lean` in 1.7 s, with no
errors or warnings. It used a private overlay under
`/dev/shm/nt-tmp/nt-local-compile-r27foki3/.lbuild` and the normal 60-second
per-file limit. The installed wrapper delegates the overlay/server confirmation
to nt_srv_compile.py; no direct ssh command, lake build, live Lean write, or
repository mutation was performed by the reviewer.

The item lean.statement was compared programmatically with the file signature
before `:= by`: verbatim equality. The file has 95 lines, maximum width 92,
one theorem with only `sorry`, real source/blueprint module and declaration
docstrings, permitted imports, and the correct topic and namespace. No hollow
definition, arbitrary substitute map, or pro-etale substitute exists. The
current route-pivot dropped list has no intersection with the item's statement
or proof dependencies, and no route-pivot repair note exists for this item.

Finding and correction: H1/H11, the delivered second-reading section was only
a disclaimer and contained no actual reading. This full section replaces it.
The Lean module and node record are mathematically correct and require no
change. Verdict FIX is solely for this complete report replacement.

