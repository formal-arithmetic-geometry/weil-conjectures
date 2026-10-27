## Worker report

The module `Sheaf.RingTheory.LocalSquareZeroSmallExtensionReduction` states
`Algebra.local_square_zero_lifting_of_small_artinian_tests`, with one `sorry` and no
new definitions. The item statement and all its existing dependencies are unchanged.
No dependency repairs or new nodes are needed.

Source read: `literature/stacks-project/more-algebra.tex`, `lemma-fs-local`, Tag 0DYG,
particularly the complete proof of (3) implies (2); `algebra.tex`,
`definition-small-extension`, Tag 02HS. The latter defines a small extension by
surjectivity and kernel length one, and immediately identifies its kernel as principal,
nonzero and killed by the maximal ideal. The Lean uses this length formulation, as does
`AlgebraicGeometry.smooth_on_open_iff_artinian_lifting` in the upstream library.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The commutative local rings R and S are the explicitly bound `R : Type u`, `S : Type v`,
  with `CommRing` and `IsLocalRing` instances. Mathlib's local-ring predicate is equivalent
  to existence of exactly one maximal ideal, including nontriviality.
- The local map R → S is `[Algebra R S] [IsLocalHom (algebraMap R S)]`.
  `IsLocalRing.local_hom_TFAE` and `IsLocalRing.maximalIdeal_comap` identify locality
  with the node's inverse-image-of-maximal-ideal equality. Every commutative ring map
  induces an algebra structure, so this representation does not restrict the map.
- S Noetherian is `[IsNoetherianRing S]`, exactly the declaration of
  `def-weil-pbc-noetherian-ring` in `Mathlib.RingTheory.Noetherian.Defs`. Its full
  definition and docstring were read: every ideal is finitely generated.
- The complete small-extension test is `hlift`. Its rings B' and B have independent
  commutative-ring, local-ring and Artinian instances. `IsArtinianRing` is the descending
  chain condition on ideals, as in the node.
- `p : B' →ₐ[R] B` and `Function.Surjective p` give a surjection compatible with the
  chosen structure maps. `Module.length B' (RingHom.ker p.toRingHom) = 1` is precisely
  the nonzero, maximal-ideal-annihilated, residue-dimension-one kernel condition. Indeed,
  `Module.length_eq_one_iff` identifies it with a simple module. For a commutative local
  ring any simple module is a one-dimensional vector space over its residue field:
  a nonzero element generates it, with annihilator the unique maximal ideal. Conversely,
  such a vector space is simple. Thus no small extension is added or omitted. There is
  no separately assumed square-zero condition on p: it follows because its proper kernel
  lies in the maximal ideal which annihilates it.
- `[Algebra R B'] [IsLocalHom (algebraMap R B')]` is every local map R → B'. The algebra
  structure on B and the algebra homomorphism p express the resulting R-algebra B. This
  structure is forced by surjectivity and compatibility. The node does not separately
  require a local R → B binder; it follows from the local structure map and the local
  surjection p.
- `g : S →ₐ[R] B` and `[IsLocalHom g.toRingHom]` give the required local R-algebra map.
  `Function.Bijective (IsLocalRing.ResidueField.map g.toRingHom)` says its actual induced
  map S/n → B/m_B is an isomorphism; no arbitrary unrelated field isomorphism is supplied.
- `∃ g' : S →ₐ[R] B', p.comp g' = g` is exactly the lift assumed for each small test.
  No extra condition on the lift is requested.
- The general test ring is `A : Type w`, with commutative local R-algebra structure and
  local structure map. There is NO Artinian, Noetherian, finite-length or finiteness binder
  on A. The explicit N, `hN : 1 ≤ N`, and `hnil : maximalIdeal A ^ N = ⊥` encode precisely
  the nilpotence hypothesis; quantifying over each such N is equivalent to using an
  existential witness of nilpotence.
- `J : Ideal A` with `hJ : J ^ 2 = ⊥` is every square-zero ideal, including zero.
  `[IsLocalRing (A ⧸ J)]` exposes the unique local structure on the quotient for the residue
  map API. It is not an additional restriction on J: J² = 0 in a nonzero local ring
  implies J is proper (indeed J lies in the maximal ideal), the quotient is nonzero, and
  `IsLocalRing.of_surjective'` applied to the quotient map gives this unique Prop instance.
  The statement is valid for every such instance and proof irrelevance identifies them.
- `v : S →ₐ[R] A ⧸ J`, its `IsLocalHom` instance and `hres` are exactly the local
  R-algebra map inducing the stipulated residue-field isomorphism.
- The conclusion `∃ w : S →ₐ[R] A, (Ideal.Quotient.mkₐ R J).comp w = v` is exactly the
  requested R-algebra lift through the canonical quotient, with neither uniqueness nor
  additional lift data asserted.

Universes: R, S and the general test A have independent u, v, w. The small-extension
hypothesis ranges over `Type (max u v w)`, hence is never confined to a universe too small
for these rings. Enlarging any initial universes accommodates all the test rings of an
application. The products and subspaces in the source argument stay within this universe.
All variables and universes are bound explicitly; `autoImplicit` is false.

Dependency declarations used:

- Statement dependency: `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`.
- Proof dependency import: `Mathlib.RingTheory.Ideal.KrullsHeightTheorem`,
  `IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing`, the recorded
  Mathlib match of `lem-weil-pbc-noetherian-local-quotient-artinian-local`.
- Proof dependency import: `Mathlib.LinearAlgebra.Basis.VectorSpace`,
  `Submodule.exists_isCompl`, recorded by `lem-trf-vector-subspace-complement`.
  Their signatures and source were read. These two imports are plain proof imports;
  the Mathlib imports exposing the signature's types and operations are public.
- Standard APIs: `IsLocalHom`, `IsLocalRing.ResidueField.map`, `IsArtinianRing`,
  `Module.length`, `RingHom.ker`, `AlgHom.comp`, `Ideal.Quotient.mkₐ`.
  No private copy of any dependency notion is introduced.

Edge cases checked before writing: J = 0 is allowed; N = 1 makes A a field and forces
J = 0; the zero ring is correctly excluded by the node's unique-maximal-ideal meaning of
local ring; the small-test kernel is nonzero since it has length one; arbitrarily large
residue fields and infinite-dimensional square-zero ideals are allowed. For example
A = k ⊕ V with square-zero V of infinite dimension has nilpotent maximal ideal but need
not be Artinian; it is covered without any dimension binder. Mixed characteristic and
arbitrary R are retained; there is no Noetherian requirement on R. No statement fault or
STATEMENT-DISPUTED issue was found.

Searches actually run (via prescribed `msearch.py NZ` for this item):

- LeanFinder: “For a local map to a Noetherian ring, lifting along all small Artinian
  extensions with fixed residue field implies square zero lifting over every local ring
  with nilpotent maximal ideal”. Eight hits: HenselianLocalRing,
  Algebra.FormallySmooth.lift, isArtinianRing_iff_isNilpotent_maximalIdeal,
  Algebra.FormallySmooth.flat_of_algHom_of_isNoetherianRing,
  Algebra.FormallySmooth.exists_lift, HenselianRing,
  Algebra.FormallyUnramified.iff_comp_injective_of_small, Algebra.FormallySmooth.mk_lift.
  None states this reduction; formal smoothness is a stronger input than the small tests.
- Loogle: `IsArtinianRing, IsLocalRing, AlgHom`. Zero hits.
- LeanSearch: “Small Artinian extension tests imply lifting over arbitrary square zero
  local extensions with nilpotent maximal ideal and fixed residue field”. Eight hits:
  Algebra.FormallySmooth.exists_lift; liftOfDerivationToSquareZero and its apply lemma;
  TrivSqZeroExt.lift_def; Algebra.FormallySmooth.lift; TrivSqZeroExt.lift,
  TrivSqZeroExt.lift_apply_inr and TrivSqZeroExt.liftEquivOfComm_apply. None states the item.
- msearch grep: `smallExtension|small_extension|small.*[Aa]rtin|square.zero.*lifting`,
  restricted to Mathlib RingTheory. Zero hits.
- Direct rg in both `lean/WeilConjectures` and `lean/Sheaf`:
  `smallExtension|SmallExtension|small_extension|small extension`, and
  `0DYG|small.extension|square.zero.lift`. Found the more specialized marked Artinian
  test category, smoothness-near-a-prime criteria, and the parent
  `AdicSmoothFixedResidueLifting` that cites this item in its proof. None states the
  arbitrary local square-zero reduction. The marked test category assumes Noetherian R
  and a finite-type marked residue extension, so importing it would restrict the statement.
- Exact node-id grep in `lean/WeilConjectures`: no occurrence. DAG and upstream source
  inspection gave no existing exact declaration for this item. The prescribed compact
  object example is now a withdrawn empty module; its node and the current module-mode
  instructions were read, and a current statement module was also read for layout.

Compilation: prescribed scompile.py compiled the module in sandbox mode and library mode
on the server in 2.7 s and 2.9 s respectively; no errors or non-sorry warnings.

## Second reading by NZ

Self-check with the complete node and Lean module reopened; no separate worker was started,
as the dispatcher brief explicitly forbids doing so. The maintainer supplies the independent
review. Rechecked in particular the potential mismatches: length one is equivalent to all
three kernel conditions, rather than just square zero; the residue map is the map induced
by g or v; no local or residue condition is imposed on the requested lifts; A has neither
Artinian nor Noetherian assumptions; the quotient's local-ring instance is forced by the
square-zero hypothesis; and the small tests use a dominating universe. The docstring
contains all six proof steps, including the hyperplanes, their product, and the complement
retraction, so it does not assume finite-dimensionality of J. No mismatch was found and
no source statement was changed.
