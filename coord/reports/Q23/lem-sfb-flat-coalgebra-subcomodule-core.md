## Worker report

The module `Sheaf.RingTheory.FlatCoalgebraSubcomoduleCore` states
`Coalgebra.flat_subcomodule_core`, with one `sorry`, exactly the stable-core lemma.
No definitions, new nodes, dependency modules, or statement corrections are needed.
The repository and compiled library were read only; all authored files are in this
item's sandbox. All compilation used the prescribed `scompile.py` wrapper.

Source read: Milne, Basic Theory of Affine Group Schemes (2012), VIII, Aside 4.7,
printed p.117 (zero-based PDF page 116),
https://www.jmilne.org/math/CourseNotes/AGS.pdf . The stable-core lemma is the
lemma before the finite-generation argument. The latter uses Noetherianity;
the kernel argument establishing the stable core does not. The docstring gives
all five proof steps in the accepted node, including the omitted stability argument.

Hypothesis and clause correspondence:

- `R : Type u` and `[CommRing R]` give the arbitrary commutative ring, including
  the zero ring. `C : Type v`, `[AddCommGroup C]`, `[Module R C]` give its module.
- `[Coalgebra R C]` supplies precisely the linear maps `Coalgebra.comul` and
  `Coalgebra.counit`, coassociativity and both counit identities. Its definition
  was read in Mathlib; it imposes neither cocommutativity nor an algebra structure.
- `[Module.Flat R C]` expresses preservation of injections upon tensoring with C.
  `Module.Flat.rTensor_preserves_injective_linearMap` gives precisely that condition
  for arbitrary module universes; its converse is recorded by
  `Module.Flat.iff_rTensor_preserves_injective_linearMap`. There is no finiteness
  condition on C despite the equivalent finite-test presentation of the class.
- `M : Type w`, `[AddCommGroup M]`, `[Module R M]`, and
  `ρ : M →ₗ[R] M ⊗[R] C` give the arbitrary module and its specified linear map.
- `hρassoc` is `(ρ tensor 1)ρ = (1 tensor Δ)ρ`, using the canonical associator
  to make both codomains `M tensor (C tensor C)`.
- `hρcounit` is `(1 tensor ε)ρ = id`, followed by `TensorProduct.rid R M`.
- `W : Submodule R M` is the given submodule. `K : Submodule R M` with `hK`
  names exactly the submodule `(range (W.subtype.rTensor C)).comap ρ`.
  This is a definitional parameterization of the displayed set W-circle, not
  an assumption of stability or containment. Such K always exists by Mathlib's
  actual inverse-image construction; membership is definitionally the node's
  condition `ρ(m) ∈ image(i_W tensor 1)`. Thus it also renders the assertion
  that the displayed set is a submodule without postponing construction data.
- The first conjunct `K ≤ W` is the required containment.
- `∃ ρK : K →ₗ[R] K ⊗[R] C` supplies the restricted linear map.
  Its first conjunct `K.subtype.rTensor C ∘ₗ ρK = ρ ∘ₗ K.subtype`
  is the required inclusion square, with `j = K.subtype`.
- The next two conjuncts are the restricted coassociativity and counit identities,
  with exactly the same canonical associator and right-unit identification.
- `∀ ρK', square → ρK' = ρK` is uniqueness from the inclusion square alone;
  it does not assume that the competing map already satisfies the coaction laws.
- The last conjunct quantifies over every `U : Submodule R M`. `U ≤ W` is
  the given containment; `U ≤ (range (U.subtype.rTensor C)).comap ρ` is
  precisely `ρ(U) ⊆ image(i_U tensor 1)`; the conclusion is `U ≤ K`.
- The three universes u, v, w are independent and explicit. `autoImplicit` is
  disabled. No Noetherian, finitely generated, free, or torsion-free hypotheses
  are imposed on any module or ring.

Dependency declarations used:

- `def-weil-pbc-module-tensor-product` is a Mathlib leaf, with no Lean record:
  `TensorProduct` in `Mathlib.LinearAlgebra.TensorProduct.Defs`,
  `TensorProduct.mk`, `TensorProduct.lift`, `TensorProduct.ext'`, and
  `LinearMap.rTensor` in `Mathlib.LinearAlgebra.TensorProduct.Map`.
  Their definitions, signatures and docstrings were read, along with
  `LinearMap.lTensor`, `TensorProduct.assoc`, and `TensorProduct.rid`.
  `Mathlib.RingTheory.Coalgebra.Basic` publicly imports the tensor API.
- Proof dependency `lem-weil-pbc-flat-tensor-exact` matches
  `Module.Flat.rTensor_exact` and `Module.Flat.lTensor_exact` in
  `Mathlib.RingTheory.Flat.Basic`, imported publicly because its `Flat`
  class occurs in the statement.
- Proof dependency `lem-weil-pbc-tensor-right-exact` matches `rTensor_exact`
  and `lTensor_exact` in `Mathlib.LinearAlgebra.TensorProduct.RightExactness`.
  Its module is already publicly imported by `Flat.Basic`. Both exactness
  declarations were read; no project proof-dependency modules were omitted.
- `Submodule.comap` and `LinearMap.range`, whose actual constructions and
  membership signatures were read, express inverse image and image directly.

Edge cases checked mathematically before writing:

- W=0: its tensor-inclusion image is zero; the counit makes ρ injective,
  so K=0 and the restricted map is the unique zero-domain map.
- W=M: the tensor inclusion is surjective, so K=M and ρ itself is the map.
- M=0 or the zero ring: all modules in question are zero as appropriate;
  no nontriviality assumption excludes these cases.
- C=0: counitality forces M=0, so the statement still applies.
- C=R with the usual coalgebra and trivial coaction: K=W; arbitrary torsion
  in M causes no problem.
- Over a field, take C with two group-like basis elements and M=C. For the
  diagonal line W spanned by e0+e1 the core is zero, so the formulation does
  not mistakenly identify every W with its core.

Searches (2026-10-24):

- `msearch.py ... leanfinder "For a comodule over a flat coalgebra over a
  commutative ring the inverse image of W tensor C under coaction is the
  largest subcomodule inside W"`: 8 hits, including PicardGroup submoduleAlgebra,
  flat tensor equalizers, coalgebra tensor instances, and
  `le_comap_range_rTensor`; none states the stable-core result.
- `msearch.py ... loogle "Coalgebra, Submodule"`: 3 hits, skew-primitive
  submodules and quotient coalgebras by coideals; none concerns this core.
- `msearch.py ... grep "comodule|subcomodule|coaction"`: zero Mathlib hits.
- `msearch.py ... leansearch "The inverse image of W tensor C under the
  coaction of a comodule over a flat coalgebra is the largest subcomodule
  contained in W"`: 8 hits, including `Submodule.comap` (reused),
  `le_comap_range_rTensor`, and unrelated variants; no full theorem.
- `rg` of `comodule|subcomodule|coaction|submoduleCore` in both
  `lean/WeilConjectures` and `lean/Sheaf`: upstream affine descent concerns
  scheme coactions; project finite-subcomodule statements concern fields and
  finite dimension; relative Hopf-module statements concern Hopf algebras and
  left coactions. Read `FiniteSubcomodule`, `RelativeHopfModuleData`, and
  `RelativeHopfModuleKernels`; none states the arbitrary flat-coalgebra core.
- Required `grep -rn` of the item id in `lean/WeilConjectures`: no hit.
- `rg` of `coactionCore|submoduleCore|flat_coalgebra_subcomodule_core` in
  project/upstream Lean and `dag/lean_names_upstream.json`: no hit.

Validation: `scompile.py Q23 lem-sfb-flat-coalgebra-subcomodule-core <file>`
passed both the sandbox and actual library-module modes (1.2 s and 1.5 s).
No errors or unexpected warnings. Only a named theorem is postponed; no data
is postponed. No statement dispute or node fault was found.

## Second reading by Q23

This is the author's second reading; the dispatcher prohibits subagents and
assigns the independent review to the maintainer. I reopened the node and final
module and checked each clause against the correspondence above. In particular,
K is fixed by the explicit inverse-image equality, both coaction identities
use the right tensor ordering and canonical identifications, uniqueness tests
all linear maps satisfying only the square, and maximality quantifies over
all stable U contained in W. The `Coalgebra` class includes exactly the three
coalgebra identities and does not impose cocommutativity. The flatness class
introduces no finite-generation assumption. All universes are explicit and
independent. No mismatch was found and no node correction was made.
