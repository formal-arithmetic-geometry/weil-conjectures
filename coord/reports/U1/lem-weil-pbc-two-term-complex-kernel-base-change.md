## Worker report

Module: `Sheaf.RingTheory.TwoTermKernelBaseChange`.
Declarations: `LinearMap.exists_twoTermKernelBaseChange_equiv` and
`LinearMap.bijective_twoTermKernelBaseChange_algebra`. Both are statement-only, with `sorry`.
No new definitions, dependency modules, or statement corrections are needed.

Hypothesis and clause matching:

- A commutative ring B: `(B : Type u) [CommRing B]`.
- The B-modules C, N₁, N₀: their `AddCommGroup` and `Module B` instances.
  The universe `u` is arbitrary and may be chosen large enough to contain all four objects;
  it makes no finite-dimensional, finite-rank, or small-index-set assumption.
- The homomorphism δ: `(δ : N₁ →ₗ[B] N₀)`.
- N₀ free: `[Module.Free B N₀]`; no freeness or flatness is imposed on N₁ or C.
- H₁ = ker δ: `LinearMap.ker δ`.
- H₀ = coker δ: `N₀ ⧸ LinearMap.range δ`, the standard module cokernel.
- Tor₁(H₀,C) = 0: `hTor₁`, using `IsZero` on the first-variable derived
  tensor functor `Tor' (ModuleCat B) 1`, evaluated on the two modules.
- Tor₂(H₀,C) = 0: `hTor₂`, the identical expression in degree 2.
- The kernel after tensoring: `LinearMap.ker (δ.rTensor C)`;
  `rTensor C` is exactly δ ⊗ id_C.
- The canonical map is an isomorphism: the conclusion exhibits a B-linear equivalence `e`.
  Its additional equality for EVERY tensor `x` specifies the actual map, rather than an
  arbitrary abstract isomorphism: its composition with the target subtype is the tensor of
  `(LinearMap.ker δ).subtype`. In particular, h ⊗ c maps to h.val ⊗ c.
- The parenthetical C-linearity clause: the second statement uses `[CommRing C] [Algebra B C]`
  (commutative algebras, as in the Stacks commutative-algebra source).
  `δ.tensorKer C C` is Mathlib's C-linear map
  `C ⊗[B] ker δ →ₗ[C] ker (AlgebraTensorModule.lTensor C C δ)`.
  Its bijectivity means precisely that it is a C-linear isomorphism. This is the SAME map
  with tensor factors commuted: the standard `TensorProduct.comm B` equivalences send
  h ⊗ c to c ⊗ h on both source and ambient target, and the generator formula
  `LinearMap.tensorKer_tmul` sends c ⊗ h to c ⊗ h.val. Under these equivalences,
  multiplication on the first C factor is exactly the action c'·(h ⊗ c)=h ⊗ c'c
  in the node. No flatness assumption is needed to define `tensorKer`.

Dependency used: `def-weil-pbc-tor-modules` has status `mathlib` and records
`CategoryTheory.Tor'` in `Mathlib.CategoryTheory.Monoidal.Tor`.
Its full signature and docstring were read, along with its definition using the left derived
functors of tensoringRight. The imported ModuleCat Abelian, Monoidal.Basic and Projective
modules supply the required structures. The existing `LinearMap.tensorKer`, its full
signature, defining bilinear map, and generator formula were read in
`Mathlib.RingTheory.Flat.Equalizer`. The same file's `tensorKerEquiv` requires flatness and
therefore does not state this node. The proof docstrings carry all five node proof steps,
including the exact-sequence and free dimension-shifting node references.

Source check: the local literature checkout contains only lists and import tools, so the
final paragraph was opened at https://stacks.math.columbia.edu/tag/00S2 instead. It explicitly
assumes a free degree-zero term and vanishing in BOTH Tor degrees; it concludes the asserted
kernel identification. No source correction is needed.

Edge cases checked: the zero ring; C = 0; N₀ = 0; N₁ = 0; δ = 0; a surjective δ;
free modules of infinite rank. None is excluded by the binders. With N₀ = 0 the cokernel and
Tor hypotheses vanish and the assertion identifies N₁ ⊗ C with itself. With δ = 0 the
inclusion is the identity on N₁; with δ surjective the usual right-exact sequence and the
Tor vanishing give the claimed kernel. No assumption that C is flat occurs.

Searches made through `/home/ubuntu/weil-launcher/msearch.py`:

- leanfinder: `kernel of two term complex commutes with tensor when Tor one and two of
  cokernel vanish`: eight results, chiefly `CategoryTheory.Tor'`, its evaluation formulas,
  and tensor right-exactness; no matching theorem.
- loogle: `LinearMap.rTensor, LinearMap.ker`: three results, `rTensor_mkQ`,
  `TensorProduct.map_ker`, and a faithfully-flat exactness reflection lemma; no match.
- grep: `Tor|tensorKer` in `RingTheory/Flat`: `tensorKer` and flatness-based material;
  the categorical-flatness file has the TODO to relate flatness and Tor. No Tor-vanishing
  kernel theorem.
- leansearch: `kernel commutes with tensor product Tor vanishing cokernel`:
  service unavailable (Internal Server Error); no search verdict assigned.
- `rg` in the source's WeilConjectures tree, the project's lean/Sheaf tree, and
  dag/lean_names_upstream.json for `twoTermKernelBaseChange|tensorKer|kernel.*base.change`:
  no matching theorem. Existing JacobiZariskiHomologySequence cites this node as a proof
  ingredient, but does not state the general result. Upstream uses tensorKerEquiv only
  in flat situations. Searching the exact node id in WeilConjectures found no declaration.

Validation: `scompile.py U1 lem-weil-pbc-two-term-complex-kernel-base-change
<module>` compiled the complete file on the server in 1.6 seconds, exit code 0, with no
warnings. All variables and the universe are explicitly bound.

## Second reading by U1

Independent reading on 2026-10-11. I opened the node copy and the repository node,
the complete Lean module, and the sole statement dependency
`def-weil-pbc-tor-modules`. There are no new nodes, dependency modules, or
`statement_change` records in this delivery.

Source: I fetched the Stacks `algebra.tex` into the item's scratchpad and read
`lemma-exact-sequence-NL` (Tag 00S2), including its hypotheses and final proof
paragraph (current lines 35467--35485). I also opened
https://stacks.math.columbia.edu/tag/00S2. The source works with commutative rings
and ring maps; the final paragraph is the general two-term-module argument used
by this node. It requires N₀ free and both Tor vanishings; it imposes no finite
rank, Noetherian, nonzero-ring, or flatness hypothesis. Its two short exact
sequences and dimension shift give precisely this node's canonical kernel map.
The source's algebra application is commutative, matching `[CommRing C]`.

Object/hypothesis/conclusion inventory and matching (all PASS):

1. B is an arbitrary commutative ring: `(B : Type u) [CommRing B]`.
2. C is an arbitrary B-module: `(C : Type u) [AddCommGroup C] [Module B C]`.
   No algebra or flatness instance is requested in the module statement.
3. N₁ and N₀ are B-modules: their `Type u`, `AddCommGroup`, and `Module B`
   binders. No restriction on N₁ beyond being a module.
4. δ is a B-module homomorphism: `(δ : N₁ →ₗ[B] N₀)`.
5. N₀ is free: `[Module.Free B N₀]`. This permits arbitrary-rank free modules.
6. H₁ is ker δ: `LinearMap.ker δ`, the standard submodule of N₁.
7. H₀ is coker δ: `N₀ ⧸ LinearMap.range δ`, the standard quotient by the image.
8. Tor₁ᴮ(H₀,C) vanishes: `hTor₁ : IsZero (((Tor' (ModuleCat B) 1).obj
   (ModuleCat.of B (N₀ ⧸ LinearMap.range δ))).obj (ModuleCat.of B C))`.
9. Tor₂ᴮ(H₀,C) vanishes: `hTor₂`, with exactly the same arguments and degree 2.
   I read `CategoryTheory.Tor'` in `Mathlib.CategoryTheory.Monoidal.Tor`: it
   derives tensoringRight in the FIRST variable, exactly the dependency node's
   projective resolution of H₀ tensored with C. I also read
   `ProjectiveResolution.isoLeftDerivedObj` in Abelian/LeftDerived: its target
   is homology of the tensored projective resolution. `IsZero` concerns a
   ModuleCat object, not a bare type. The imported ModuleCat Abelian, monoidal,
   and projective modules supply the required categorical structures.
10. Tensor differential δ ⊗ id_C: `δ.rTensor C`, a B-linear map between the
    displayed module tensor products. Target: `LinearMap.ker (δ.rTensor C)`.
11. The canonical map from H₁ ⊗ C is an isomorphism: the existential
    `e : (LinearMap.ker δ ⊗[B] C) ≃ₗ[B] LinearMap.ker (δ.rTensor C)`
    supplies exactly that isomorphism. The following `∀ x` equality with
    `(LinearMap.ker δ).subtype.rTensor C x` fixes its underlying map on EVERY
    tensor, hence in particular h ⊗ c maps to h.val ⊗ c. It cannot assert only
    an unrelated abstract equivalence. Coercion from the target subtype is
    injective, so the equality uniquely characterizes the canonical map.
12. If C is a B-algebra the SAME map is C-linear: the second declaration
    takes `[CommRing C] [Algebra B C]` and asserts bijectivity of
    `δ.tensorKer C C`, which is already a C-linear map by its type.
    I read `tensorKer`, `tensorKerBil`, and `tensorKer_tmul` in
    Mathlib/RingTheory/Flat/Equalizer.lean, including the section variables.
    This map needs no flatness and sends c ⊗ h to c ⊗ h.val. Tensor symmetry
    exchanges both source factors and both ambient target factors, sending
    the first statement's h ⊗ c to c ⊗ h. It intertwines δ.rTensor C with
    δ.lTensor C, so also identifies their kernels. The C-action on the first
    factor then becomes h ⊗ (c' * c), precisely the node's action. Bijectivity
    of this existing C-linear map is equivalent to a C-linear isomorphism;
    this separate algebra specialization adds no hypothesis to clause 11.

Quantifiers have the required order: objects, module structures, freeness, δ,
the two vanishings, then the equivalence and its map characterization. All
variables and universe parameters are bound. A common arbitrary universe u
permits any set-sized collection of these four objects by taking u at least
their universe levels; there is no test-object quantifier that becomes vacuous.

Edge cases: the zero ring is allowed (no Nontrivial instance); C, N₁, or N₀
may be zero. If C = 0, both tensor sides are zero. If N₀ = 0, H₀ = 0 and the
map identifies N₁ ⊗ C with itself. If N₁ = 0, both kernels are zero. If δ = 0,
the map is the tensor of the identity on N₁; if δ is surjective, H₀ = 0 and
the free target makes the exact sequence split. Infinite-rank free modules
and free modules indexed by the empty set are allowed. No characteristic is
restricted. Schemes, an index set for limits, and an n-variable are absent;
there is no excluded empty-scheme or n = 0 case to check here.

Independent searches with words differing from the worker's queries:

- `msearch.py ... leanfinder "injectivity of tensor of kernel from vanishing
  derived tensor cokernel degrees 1 2"`: eight results, including
  `lTensor_injective_of_exact_of_exact_of_rTensor_injective` and
  `LinearMap.lTensor_injective_of_exact_of_flat`; no matching Tor theorem.
- `msearch.py ... loogle "LinearMap.tensorKer"`: tensorKer and its generator
  and coercion formulas, plus tensorKerEquiv_apply. The latter assumes flatness.
- `msearch.py ... leansearch "Tor vanishing in degrees one and two implies
  base change of a kernel is an isomorphism"`: Internal Server Error;
  unavailable, with no mathematical verdict assigned.
- `rg` on Mathlib for Tor vanishing: Monoidal/Tor contains only projective
  vanishing; the Rep lemmas concern representations. The Equalizer module's
  kernel equivalence requires `[Module.Flat R M]`, unlike this node.
- `rg` on WeilConjectures and lean/Sheaf for tensorKer, kernel/base-change,
  and Tor': upstream Flat/Equalizer and Finiteness/Descent use flat base
  change. I opened these relevant places. I opened the project's
  JacobiZariskiHomologySequence: it uses this node in its proof and states the
  specialized cotangent sequence, not this general theorem. MinimalPresentationTor,
  GradedNakayamaFree, and stalk tensor comparisons are also other statements.
- `rg` on dag/lean_names_upstream.json and both Lean trees for the two full
  declaration names: no pre-existing declaration of either name. No replacement
  by an existing general theorem was found.

H4--H9: every notion uses Mathlib, notably the dependency's recorded Tor'.
There is no new or hollow definition, private copy, file-local notation,
instance, or abbreviation. Both proofs are exactly `by sorry`. Module and
statement docstrings name the source and blueprint id. The first proof
explains all five node steps, with the exact-sequence and dimension-shifting
node references; the second explicitly uses those steps and explains the
C-action. Imports supply the used structures; namespace, topic, and line
width conform. The node's `lean.statement` matches the main signature verbatim.

Mismatches found: none. Changed only this report by appending the independent
second reading; preserved the correct Lean and node record.

Validation: independent `scompile.py` compiled the complete 76-line module
cleanly in 1.5 seconds (exit code 0), without warnings. A direct text comparison
confirmed that `lean.statement` is verbatim the main declaration signature.
