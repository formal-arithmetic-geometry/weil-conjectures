## Worker report

The module `Sheaf.RingTheory.ElkikFiniteEtaleAwayCompletion` states
`CommRingCat.elkik_finiteEtaleAway_completion`, with its proof postponed by `sorry`.
Its helper `CommRingCat.finiteEtaleAwayProperty` is a concrete conjunction defining
exactly the objects in the two full subcategories introduced in this theorem.
There are no other postponed results, no chosen algebraization data, and no
replacement of the canonical tensor-product functor by an arbitrary functor.
Only the item's `lean` field changes. No new nodes or dependency repairs are needed.

Source read: ILO, *Travaux de Gabber*, Exposé V, Theorem 1.2.4, printed p.64,
including the preceding henselian-pair discussion. The theorem says that finite
schemes étale over the complementary open are equivalent after completion.
Taking affine coordinate rings gives the stated equivalence of algebra categories
(the two contravariances reverse both categories). The node states precisely this
algebra formulation; no source hypothesis or conclusion needs correction.

Hypotheses and clauses, with the node and complete declaration open:

- A commutative Noetherian ring is `(B : CommRingCat.{u}) [IsNoetherianRing B]`.
  `CommRingCat` supplies the commutative ring structure; there is no domain,
  nonzero-ring, local-ring, or excellence assumption.
- An ideal and henselian pair are `(I : Ideal B) [HenselianRing B I]`, using the
  recorded root-lifting/Jacobson-radical formulation of the henselian-pair notion.
- The completion is `AdicCompletion I B`, with Mathlib's canonical commutative
  ring and `B`-algebra structures, not an arbitrary ring with a completion map.
  Its defining compatible sequences have coordinates modulo `I^n`.
- A commutative `B`-algebra is an object `C : Under B`; its structural map is
  `C.hom`, and the existing `CommRingCat` instance gives `Algebra B C`.
- Finite as a module is the first conjunct `Module.Finite B C` of
  `finiteEtaleAwayProperty B I C`, never finiteness of the underlying set or
  merely finite generation as an algebra.
- Étale over `Spec B` minus `V(I)` is the second conjunct: `Etale` of
  `morphismRestrict (Spec.map C.hom)` to the open with underlying set
  `(PrimeSpectrum.zeroLocus (I : Set B))ᶜ`. Its openness is the actual theorem
  `PrimeSpectrum.isClosed_zeroLocus`, applied to this ideal.
- Morphisms are all `B`-algebra homomorphisms: the category is the Mathlib
  `ObjectProperty.FullSubcategory` of `Under B`, so no condition is imposed on
  morphisms beyond the commuting structural-map triangle. `CommRingCat.toAlgHom`
  and `AlgHom.toUnder` give exactly the familiar algebra-hom encoding.
- The target category uses the identical predicate over
  `CommRingCat.of (AdicCompletion I B)` with the extended ideal
  `I.map (algebraMap B (AdicCompletion I B))`, i.e. `I` times the completed ring.
- The object and morphism maps are Mathlib's `tensorProd B (of (AdicCompletion I B))`:
  its object is the completed ring tensor `C`, and its morphism is tensoring
  an algebra homomorphism with the identity on the completed ring.
- The existential `h` asserts that this specific functor lands in the target
  full subcategory. It is a proof-valued witness in the theorem's conclusion,
  not an assumption and not an arbitrary base-change operation. The actual
  functor is `ObjectProperty.lift` of the source inclusion followed by tensor.
- That exact lifted functor is asserted to satisfy `.IsEquivalence`.
- The final `∀ E, ∃ C, Nonempty (... ≅ E.obj)` renders the explicit particular
  conclusion. The isomorphism is in `Under (of (AdicCompletion I B))`, hence
  is an isomorphism of completed-ring algebras, not just abstract rings or
  modules. `C` is an object of the source full subcategory, retaining both
  module finiteness and the étale-away condition.

Every variable and universe is explicitly bound; `set_option autoImplicit false`
enforces this. The universe `u` is arbitrary; the ring, its completion and the
algebra categories use the same ambient universe. Every finite algebra over a
ring has a representative in that universe (it is a quotient of a finite free
module), so this is the customary universe presentation of the whole category
of finite algebras rather than an arithmetic size hypothesis.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (the recorded
  `def-weil-pbc-noetherian-ring`), defined as `IsNoetherian B B`.
- `WeilConjectures.Mathlib.RingTheory.Henselian`: the recorded henselian
  terminology module. Its imported `Mathlib.RingTheory.Henselian.HenselianRing`
  is the global declaration `HenselianRing` used in the theorem, with
  `jac` and monic simple-root lifting. The full class signature was read.
  Strictly henselian and local-ring notions in that dependency are not needed.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`,
  its commutative ring instance and its canonical algebra instance
  (`algebraMap_apply` identifies it with `AdicCompletion.of`).
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`, expressing a finitely
  generated top submodule.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`;
  obtained through the étale-morphism import, exactly as the dependency record.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`,
  defined affine-locally by étale ring maps, and the actual target restriction.
- `Mathlib.LinearAlgebra.TensorProduct.Defs` / `.Basic`: `TensorProduct` and
  its bilinear map, used by `Mathlib.Algebra.Category.Ring.Under.Basic`'s
  `CommRingCat.tensorProd`. The latter constructs the tensor-product algebra
  and tensors the algebra homomorphisms, providing the canonical functor.
- `Mathlib.CategoryTheory.ObjectProperty.FullSubcategory`: `FullSubcategory`,
  `ι`, and `lift`; `Mathlib.CategoryTheory.Equivalence`: `Functor.IsEquivalence`.

The module imports the currently stated proof-dependency modules without `public`:
`AdicCompletion.AsTensorProduct`, `RingTheory.FiniteType`,
`IntegralClosure.Algebra.Basic`, upstream `IntegralOverHenselianPair` and
`AdicCompletionNoetherian`, `AdicCompletion.Completeness`, and scheme-morphism
`Affine` and `Proper`. Étale base change and composition are already in the
public étale import. The hom-lifting, completed Jacobian torsion, Jacobian
algebraization and proper-clopen-lift proof nodes have no current declaration;
no nonexistent import is invented for them. The theorem docstring reproduces
all six DAG proof steps and their node citations for the future proof.

Edge cases checked before finalizing the statement:

- `I = 0`: the complementary open is empty, so every finite algebra qualifies;
  completion at zero gives the original ring. No global étale requirement
  was accidentally substituted for étale away from the ideal.
- Nilpotent `I`: again `V(I)` is the whole spectrum and the restriction is
  empty; finite algebras with nilpotents and ramification are included.
- A complete base: the canonical tensor-product functor gives the expected
  equivalence; completeness is not imposed as an extra hypothesis on `B`.
- The zero ring and the zero algebra (empty spectrum) are allowed. There is
  no `Nontrivial` binder, no nonempty-open binder, and no faithfulness condition
  on the algebra structure map.
- `I = ⊤` in a nonzero ring cannot satisfy the henselian-pair condition, since
  its `jac` field requires containment in the Jacobson radical; the zero-ring
  case is still allowed. There is no unnecessary proper-ideal assumption.
- Objects may be ramified on `V(I)`; only the stated open restriction is
  required to be étale.

Searches made for an existing declaration:

- `msearch.py` LeanFinder: “finite algebras etale outside an ideal of a henselian
  noetherian ring equivalent after adic completion”. Eight hits, including
  `Algebra.mem_etaleLocus_iff`, `Algebra.exists_etale_of_isEtaleAt`, and
  standard étale lifting/localization declarations. None gives the finite
  algebra completion equivalence.
- `msearch.py` Loogle: `AdicCompletion, HenselianRing`. Zero hits.
- `msearch.py` Mathlib grep: `elkik|finiteEtaleAway|etaleAway|EtaleAway`.
  Zero hits.
- Direct `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `elkik|Elkik|finiteEtaleAway|[Ee]taleAway` and the item id: only unrelated
  Popescu/rig-algebraization material and an étale-away module import.
- A further exact-name search for `finiteEtaleAwayProperty` and
  `elkik_finiteEtaleAway_completion` in Mathlib, both project roots, and
  `dag/lean_names_upstream.json` found no declarations or name clashes.
- Read Mathlib's `Algebra/Category/Ring/Under/Basic.lean` in full to reuse the
  existing algebra-category and tensor-product functor rather than define
  private copies. Read `ObjectProperty/FullSubcategory.lean`'s category and
  lift signatures before writing the statement.

The item's `lean_removed` record explains the deleted historical module; its
old review is not used as evidence that any declaration survives. Current
source searches confirm that the new statement creates no duplicate notion.
The object predicate belongs to the category explicitly introduced by this
node and is listed in `lean.declarations` as an owning-node helper.

Validation: the prescribed `scompile.py NB lem-per-elkik-finite-etale-away-completion`
compiled this module as both sandbox and library source with exit status zero,
no errors and no unexpected warnings (1.6 and 1.7 seconds respectively).
No `STATEMENT-DISPUTED` issue or node fault was found.

## Second reading by NB

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
