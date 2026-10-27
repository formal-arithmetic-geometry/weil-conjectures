## Worker report

The module `Sheaf.RingTheory.HopfAlgebra.ReducedTargetDominantFlatness` states
`HopfAlgebra.faithfullyFlat_of_injective_of_isReduced`. It has one theorem, with
`sorry` as its entire proof, and no new definitions. Only the item's `lean` field
changes. No statement correction, new node, or dependency repair is needed.

Source read: Milne, *Algebraic Groups* (2017), Proposition 1.65(a), printed
pp.26--27; Proposition 1.68, Corollary 1.69, Proposition 1.70, printed p.28;
and the first paragraph of the proof of Theorem 3.31, printed p.73. The last
passage explicitly identifies A = O(H), B = O(G), obtains dominance from the
inclusion, and applies 1.69 and 1.70 when H is reduced. The source imposes no
reducedness on G. The module docstring reproduces all eight DAG proof steps,
including the localized-kernel calculation, closed-point lifting, coset argument,
component reduction for generic flatness, translated-open cover, and affine
faithful-flatness criterion.

Clause-by-clause rendering:

- The base field is `(k : Type u) [Field k] [IsAlgClosed k]`. It is the given
  algebraically closed field, not a replacement by a chosen algebraic closure.
- The two unital commutative k-algebras are `(A : Type v) (B : Type w)` with
  `[CommRing A] [CommRing B] [HopfAlgebra k A] [HopfAlgebra k B]`. The Hopf
  instances extend `Bialgebra`, which supplies the k-algebra structure. No
  additional algebra instance is introduced, so all maps use that structure.
- The node's comultiplication and counit algebra maps are
  `Bialgebra.comulAlgHom k A` and `Bialgebra.counitAlgHom k A`, and likewise for B.
  `Bialgebra` asserts that the underlying linear comultiplication and counit
  preserve multiplication and unit. `Coalgebra.coassoc` is coassociativity under
  `TensorProduct.assoc`; `rTensor_counit_comp_comul` and
  `lTensor_counit_comp_comul` are the two unit-identification counit laws.
- The antipode is `HopfAlgebra.antipodeAlgHom k A`, likewise for B. Although
  `HopfAlgebraStruct.antipode` is initially linear, in the commutative case the
  proved `antipode_mul_distrib` and `antipode_one` make it an algebra map in
  `Mathlib.RingTheory.HopfAlgebra.Convolution`. The two `HopfAlgebra` fields
  `mul_antipode_rTensor_comul` and `mul_antipode_lTensor_comul` are exactly the
  two equations mu(S tensor 1) Delta = eta epsilon and
  mu(1 tensor S) Delta = eta epsilon. Thus the interface expresses the node's
  entire Hopf notion, without requiring cocommutativity.
- Both algebras are finitely generated over k:
  `hA : (algebraMap k A).FiniteType` and
  `hB : (algebraMap k B).FiniteType`. This uses the dependency's recorded
  `RingHom.FiniteType`, equivalent for an algebra map to `Algebra.FiniteType`.
- The homomorphism's algebra part is `(i : A →ₐ[k] B)`. The hypothesis `hcomul`
  says Delta_B i = (i tensor i) Delta_A using
  `Algebra.TensorProduct.map i i`. `hcounit` says epsilon_B i = epsilon_A.
  `hantipode` says S_B i = i S_A. These are precisely the three compatibility
  clauses in the node, not arbitrary comparison maps.
- Injectivity is `hi : Function.Injective i`.
- Reducedness is `[IsReduced A]`. Its field says every nilpotent element is
  zero, which agrees with the node's positive-exponent condition. In a unital
  algebra with a counit to the nonzero field, exponent zero cannot introduce a
  new nilpotent element.
- The conclusion is `i.toRingHom.FaithfullyFlat`, the dependency's recorded
  ring-map notion, using the A-module structure on B induced by this very i.
- There is no hypothesis on reducedness of B, connectedness, smoothness, or
  characteristic, and no equality between u, v, and w.

Statement dependencies read and used:

- `def-weil-field`: `Field`, defined in `Mathlib.Algebra.Field.Defs`.
- `def-weil-algebraic-closure`: the relevant clause is `IsAlgClosed`, defined in
  `Mathlib.FieldTheory.IsAlgClosed.Basic` and supplied by the recorded
  `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure` module. Its `exists_root`
  theorem and docstring identify the nonconstant-polynomial formulation.
- `lem-weil-pbc-algebra-tensor-pushout-universal-property`:
  `Mathlib.RingTheory.TensorProduct.Basic` supplies `TensorProduct`, its
  commutative ring and algebra structures, `includeLeft`, `includeRight`, and
  `Algebra.TensorProduct.ext`; `Mathlib.RingTheory.TensorProduct.Maps` supplies
  `Algebra.TensorProduct.productMap` and its pure-tensor formula and restriction
  laws. The same tensor product is used in `Bialgebra` and `hcomul`.
- `def-weil-pbc-finite-type-algebra`: `RingHom.FiniteType`, from
  `Mathlib.RingTheory.FiniteType`. Its full definition uses `Algebra.FiniteType`
  for `f.toAlgebra`; `finiteType_algebraMap` confirms the specialization.
- `def-weil-pbc-faithfully-flat-ring-map`: `Module.FaithfullyFlat`, from
  `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`, and `RingHom.FaithfullyFlat`,
  from `Mathlib.RingTheory.RingHom.FaithfullyFlat`. The latter is exactly the
  former for `i.toRingHom.toAlgebra`; `faithfullyFlat_algebraMap_iff` is the
  ordinary algebra-map interface.

All recorded statement-dependency signatures and docstrings were read in the
local live-source mirror. Public imports expose the statement notions; plain
imports provide the stated proof dependencies. In particular:
`Mathlib.AlgebraicGeometry.Group.Affine` (`AlgebraicGeometry.hopfSpec`),
`Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `...QuasiCompact`,
`Mathlib.AlgebraicGeometry.AffineScheme`, `...Morphisms.QuasiSeparated`,
`Mathlib.AlgebraicGeometry.Properties`, `...IdealSheaf.Subscheme`,
`...Scheme`, `Mathlib.CategoryTheory.Monoidal.Grp`,
`Mathlib.RingTheory.Spectrum.Prime.Noetherian`, `Mathlib.Topology.NoetherianSpace`,
`Mathlib.AlgebraicGeometry.Morphisms.Flat`,
`Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`,
`WeilConjectures.Mathlib.RingTheory.Nullstellensatz`
(`exists_algHom_ker_eq_of_isMaximal` and the other recorded clauses), and
`WeilConjectures.AlgebraicGeometry.GenericFlatness`
(`AlgebraicGeometry.exists_nonempty_open_flat_restrict`).
`lem-wf-affine-constructible-open` has no recorded Lean declaration or Mathlib
match and so has no module to import yet; its mathematical statement is only
used by the postponed proof. No import cycle was introduced.

Searches actually run:

- msearch LeanFinder, query: "An injective homomorphism of finitely generated
  commutative Hopf algebras over an algebraically closed field with reduced
  domain is faithfully flat". Eight hits give general faithful-flatness,
  injectivity, and spectrum criteria, not this theorem. A preliminary query
  "Hopf algebra comultiplication k algebra map tensor product" found the actual
  Mathlib Hopf and bialgebra interfaces, including `HopfAlgebra.ofAlgHom`.
- msearch LeanSearch, query: "An injective morphism of finite type commutative
  Hopf algebras over an algebraically closed field with reduced domain is
  faithfully flat". Eight hits give `RingHom.FaithfullyFlat`, flatness, spectrum
  surjectivity, and its consequences, not the required Hopf theorem.
- msearch Loogle, query: `"HopfAlgebra", "FaithfullyFlat"`. Zero hits.
  Preliminary query `AlgHom TensorProduct map` was rejected with a type-pattern
  application mismatch; that failed query was not treated as absence evidence.
- msearch Mathlib grep, query:
  `Hopf.*[Ff]lat|[Ff]lat.*Hopf|dominant.*flat|flat.*dominant`.
  Four hits in `SchemeTheoreticallyDominant.lean`, none this statement.
- Direct `rg` over `lean/WeilConjectures` and `lean/Sheaf` for `HopfAlgebra` and
  `BialgHom` located the existing Hopf conventions, notably
  `Sheaf.RingTheory.HopfAlgebra.ReducedCoreNilpotentFibre`; these use the same
  Mathlib Hopf notion. Searches for
  `faithfullyFlat_of_injective_of_isReduced|faithfullyFlat.*[Hh]opf|[Hh]opf.*faithfullyFlat|dominant.*flat`
  found no existing theorem. The item's id occurs only as a proof-plan reference
  in `SimplyConnectedMultiplicativeLifting.lean`; the prescribed grep of the
  item's id in `lean/WeilConjectures` found none. The chosen declaration name
  also has no match in Mathlib or `dag/lean_names_upstream.json`.

Edge-case checks before and during writing:

- A = B = k with the identity map is included (zero algebra generators allowed).
  Both Hopf instances are the standard self-Hopf structures.
- The counit A → k (and B → k) rules out the zero ring. No extra nonemptiness or
  nontriviality assumption has to be added.
- In characteristic p, k → k[t]/(t^p) for the additive infinitesimal group is
  included: B need not be reduced; it is a nonzero finite-dimensional k-space,
  hence faithfully flat over the field, as expected.
- Frobenius k[t] → k[t], t ↦ t^p, is allowed as an injective Hopf map in positive
  characteristic; it is finite free and faithfully flat. No separability or
  smoothness-of-the-map assumption was inserted.
- A finite constant group has a disconnected reduced coordinate algebra such
  as k × k. Such Hopf algebras remain allowed. The proof plan uses a nonempty
  integral open of one component, not irreducibility of all of H.
- u, v, w are explicitly declared and independent. There is no test-object
  quantifier that becomes empty in a smaller universe.

Validation: the prescribed `scompile.py Q135
lem-sfb-reduced-target-dominant-group-flatness <file>` succeeded for both the
sandbox module and its library module name, in 1.4 s and 1.3 s respectively,
with no errors or warnings. All Lean lines are at most 100 characters.
No STATEMENT-DISPUTED flag or mathematical node fault was found.

## Second reading by Q135

This is the worker's separate rereading of the node, source passages and completed
module; no additional agent was started, as required by the dispatcher brief.
The maintainer supplies the independent review after delivery.

The direction was rechecked: reduced A is the coordinate algebra of the target
H, while B is the source G, so `[IsReduced A]` is correctly placed. The two
finite-type hypotheses concern the structure maps from k, rather than i, and
both appear. The k-algebra structure inherited from each Hopf instance is the
one used in `algebraMap`, tensor products, and every compatibility equation.
All three map equations have precisely the source's order of composition.
`antipodeAlgHom` uses the actual antipode, with its algebra-homomorphism property
already proved in Mathlib for commutative algebras. No opposite-ring or
cocommutativity requirement has slipped in. The conclusion uses i's underlying
ring map, so its scalar action is fixed rather than separately chosen. The
nilpotent-source and disconnected-target cases remain permitted. No mismatch
was found and no statement changes were made on this rereading.
