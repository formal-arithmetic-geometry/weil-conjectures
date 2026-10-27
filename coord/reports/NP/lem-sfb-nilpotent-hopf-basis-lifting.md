## Worker report

The module `Sheaf.RingTheory.HopfAlgebra.NilpotentBasisLifting` states
`HopfAlgebra.bijective_lift_quotient_basis_of_nilpotent_augmentation`, with its whole
proof `sorry`. It introduces no definitions and changes only the item's `lean` field.
The source was read in the local Milne PDF, printed pp. 73--74 (PDF pp. 85--86),
including the displayed sum map and the unrestricted index set J.

Hypothesis and clause correspondence:

- The algebraically closed field k is `(k : Type u) [Field k] [IsAlgClosed k]`.
- The two commutative unital Hopf k-algebras are `(A : Type v) (B : Type w)` with
  `[CommRing A] [CommRing B] [HopfAlgebra k A] [HopfAlgebra k B]`.
  Mathlib's Hopf structure extends `Bialgebra`, hence `Algebra` and `Coalgebra`;
  its comultiplication and counit are algebra maps, and its coalgebra fields give
  coassociativity and both counit identities under the canonical tensor identifications.
  Its two antipode fields give exactly the two multiplication identities in the node.
  Although the stored antipode is linear, for commutative algebras
  `HopfAlgebra.antipodeAlgHom` in the publicly imported Convolution module gives
  that same antipode as an algebra map. Thus this interface neither adds nor drops
  the algebra-map requirement on S.
- Both finite-type assumptions are retained separately as
  `hA : (algebraMap k A).FiniteType` and `hB : (algebraMap k B).FiniteType`, using
  the dependency's recorded `RingHom.FiniteType` rather than a replacement notion.
- The k-algebra map preserving comultiplication and counit is `i : A →ₐc[k] B`.
  These are the defining compatibility fields of `BialgHom`. Its injectivity is
  `hi : Function.Injective i`; antipode compatibility is the explicit
  `hS : ∀ a, i (antipode k a) = antipode k (i a)`.
- The ideal I is written directly as `RingHom.ker (Bialgebra.counitAlgHom k A)`.
  The integer and its positivity are `(n : ℕ) (hn : 1 ≤ n)`; nilpotence is `hI`,
  the equality of its nth ideal power with `⊥`. Only nonnegative exponents occur
  in the node, so ℕ expresses the stated integer range exactly.
- The extended ideal i(I)B is
  `(RingHom.ker (Bialgebra.counitAlgHom k A)).map i.toAlgHom.toRingHom`.
  `Ideal.map` is defined to be the ideal span of the image, not the raw image.
- An arbitrary index set and its specified lifts are `(J : Type z) (e : J → B)`.
  The quotient basis is `b : Module.Basis J k (B ⧸ ...)`, and `he` equates each
  vector to the residue of `e j` under `Ideal.Quotient.mkₐ k`. Quantifying a basis
  with these equations is exactly saying that those residue classes form a basis.
- The conclusion is `Function.Bijective (fun c : J →₀ A ↦
  c.sum (fun j a ↦ i a * e j))`. Here `J →₀ A` is the direct sum of copies of A,
  and its sum is precisely the displayed finite sum. With the required scalar
  action through i, `a • x = i a * x`, this function is A-linear: distributivity
  gives additivity, and multiplicativity of i gives scalar compatibility termwise.
  Bijectivity of this specified function therefore says exactly that the specified
  A-linear map is an isomorphism, without choosing an unrelated module action
  or replacing the conclusion by abstract freeness. No extra linearity assumption
  is needed.

Dependency declarations used (all recorded dependencies have Mathlib interfaces):

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs.
- `def-weil-algebraic-closure`: `IsAlgClosed`,
  Mathlib.FieldTheory.IsAlgClosed.Basic, publicly imported through the recorded
  Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure module. The node needs the
  algebraically closed predicate, not a chosen closure of a different field.
- `lem-weil-pbc-algebra-tensor-pushout-universal-property`:
  `Algebra.TensorProduct.instCommRing`, `instAlgebra`, `tmul_mul_tmul`,
  `includeLeft`, `includeRight`, `ext` in Mathlib.RingTheory.TensorProduct.Basic;
  `productMap` and `productMap_apply_tmul` in Mathlib.RingTheory.TensorProduct.Maps.
  These are the tensor product and algebra structures used by the Hopf interfaces.
- `def-weil-pbc-finite-type-algebra`: `RingHom.FiniteType`,
  Mathlib.RingTheory.FiniteType (and its underlying `Algebra.FiniteType`).
- `def-weil-pbc-algebra-hom-quotient`: `AlgHom`,
  Mathlib.Algebra.Algebra.Hom; `Ideal.Quotient.algebra`, `Ideal.Quotient.mkₐ`,
  Mathlib.RingTheory.Ideal.Quotient.Operations; `Ideal.map`, `RingHom.ker`,
  Mathlib.RingTheory.Ideal.Maps; ordinary multiplication and powers of ideals.
- `def-weil-pbc-free-module`: `Module.Free`,
  Mathlib.LinearAlgebra.FreeModule.Basic, and its underlying `Module.Basis`,
  Mathlib.LinearAlgebra.Basis.Defs. The latter stores the unique finite-coordinate
  representation as a linear equivalence with `J →₀ k`.

The available proof-dependency modules are imported privately:
Mathlib.RingTheory.Flat.FaithfullyFlat.Basic (`Module.FaithfullyFlat`),
Mathlib.LinearAlgebra.TensorProduct.RightExactness (`rTensor_exact`, `lTensor_exact`,
and the module tensor product API), and Mathlib.RingTheory.RingHom.Flat
(`RingHom.Flat` / `Module.Flat`). The proof-only nodes
`lem-sfb-finite-hopf-self-injective` and `lem-sfb-split-coideal-faithfully-flat`
have no recorded Lean declaration yet, so there is no module to import for them;
they remain explicit inputs in the docstring proof plan. They are not needed to
type the statement.

Edge cases checked: J is neither finite nor nonempty by assumption, and has its
own universe z; no relation between the universes of k, A, B and J is imposed.
For empty J the basis hypothesis asserts a zero quotient. The extended ideal is
nilpotent and proper in the nonzero Hopf algebra B, so that hypothesis is impossible;
the theorem still quantifies the empty case without introducing a nonemptiness
restriction. For n = 1 the augmentation ideal vanishes and the theorem reduces
to the ordinary k-basis assertion, since A identifies with k by its counit.
n = 0 is excluded exactly by `hn`. There is no characteristic restriction.
Zero Hopf algebras over the field are already impossible by the counit identity,
not excluded by an additional hypothesis. Both possibly empty finite algebra
generating sets and infinite families of lifts are retained.

Searches made on 2026-10-24 with the prescribed msearch.py wrapper:

- LeanFinder: "An injective homomorphism of commutative Hopf algebras with nilpotent
  augmentation ideal makes arbitrary lifts of a quotient basis a module basis".
  Eight hits: SubmersivePresentation bases, cotangent bases, and
  `IsLocalRing.basisQuotient`; no Hopf basis-lifting theorem.
- Loogle: `HopfAlgebra, Module.Basis`: zero hits.
- Mathlib grep: `Hopf.*[Ff]ree|[Ff]ree.*Hopf|Hopf.*[Bb]asis`: zero hits.
- LeanSearch: "Lifting a basis modulo the nilpotent augmentation ideal of a Hopf
  subalgebra gives a module basis". Eight hits, including
  `IsLocalRing.span_eq_top_of_tmul_eq_basis`, `Module.Basis.mk`, `ModN.basis`,
  `Representation.freeAsModuleBasis`, and `Module.Basis.sumQuot`; none is this claim.
- `rg` in lean/WeilConjectures and lean/Sheaf for Hopf, nilpotent-basis and
  augmentation-basis combinations, and the exact item id. The relevant existing
  result `Module.basis_iff_basisQuotient_of_nilpotent` was read in full: it assumes
  flatness over a local ring, so it does not itself state the Hopf result.
  The reduced-core nilpotent-fibre module concerns a different quotient and was
  also read. No existing exact statement was found. The chosen full declaration
  name was searched in the project, Mathlib and dag/lean_names_upstream.json and
  had no hits. No new independent notion was introduced, hence no new DAG nodes.

No statement correction or statement dispute is needed. The source's invalid
direct-summand argument is already diagnosed in the accepted DAG; the theorem
docstring carries its six-step repaired proof rather than that invalid argument.

Validation: scompile.py compiled both the sandbox probe and the final library module
cleanly (2.0 s and 1.8 s), without warnings or errors. Every universe and variable
is bound explicitly; there are no local notations, local instances, private helpers,
or definitions with postponed data.

## Second reading by NP

An in-thread second pass reopened the node and compared its hypotheses and displayed
map against the completed file. This is a self-check; the dispatched worker was
instructed not to start agents, and the maintainer supplies the independent review.
The pass checked the two finite-type binders separately, the inherited k-algebra
structures, all three Hopf-map compatibilities, the actual kernel and ideal span,
the positive exponent, the pointwise residue-basis equation, and the exact
finite-support sum. It specifically checked that the conclusion concerns this map
and does not merely assert existence of some free-module presentation. No mismatch
was found and no statement change was made. The scalar action through i is visible
in every summand as multiplication by `i a`; thus no arbitrary action is implicit.
