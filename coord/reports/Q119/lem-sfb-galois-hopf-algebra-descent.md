## Worker report

The delivery states finite Galois descent of commutative Hopf algebras in
`Sheaf.FieldTheory.GaloisHopfAlgebraDescent`, declaration
`CommHopfAlgCat.finite_galois_hopf_algebra_descent`. Its only theorem has proof
`sorry`. The accompanying definition module has actual data and no postponed proofs.
The existing item's natural-language statement and accepted proof are unchanged.

I read Milne, Algebraic Groups (2017), Appendix A.64--A.66, printed pp.580--581
(PDF pp.592--593). A.64 explicitly gives the Hopf-algebra equivalence after
vector-space descent. The node expands the operations, natural maps and finite
generation. No topology is needed for the finite Galois group: every action is
continuous with its finite discrete topology.

Hypotheses and clauses, matched against the Lean file:

| Node | Lean rendering |
| --- | --- |
| Fields k and L, field extension L/k | `(k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L]` |
| Finite degree | `[FiniteDimensional k L]` |
| Separable algebraic and normal | `[IsGalois k L]`, whose fields are `Algebra.IsSeparable k L` and `Normal k L`; normality means every mapped minimal polynomial splits |
| Galois group fixes k pointwise | `L ≃ₐ[k] L` |
| Arbitrary commutative Hopf k-algebras | `CommHopfAlgCat.{max u v w} k` |
| Comultiplication, counit, antipode and all Hopf identities | Mathlib `HopfAlgebra`, `Coalgebra` and `Bialgebra` within `CommHopfAlgCat`; the commutative antipode is `HopfAlgebra.antipodeAlgHom` |
| Additive multiplicative bijections and group law | New definition `SemilinearAction.ρ : (L ≃ₐ[k] L) →* (B ≃+* B)` |
| Semilinear scalar rule | `SemilinearAction.scalar`, together with ring multiplicativity and `Algebra.smul_def` |
| Antipode compatibility | `SemilinearAction.antipode` |
| Counit transforms by sigma on L | `SemilinearAction.counit`, with `σ (Coalgebra.counit b)` on the right |
| Diagonal semilinear tensor compatibility | `SemilinearAction.comul`, using Mathlib `TensorProduct.map` of the two sigma-semilinear linear maps |
| Target category, L-linear equivariant Hopf maps | `GaloisObject`, `GaloisObject.Hom.hom : B.obj ⟶ C.obj` and `.equivariant`, with the explicit category instance |
| Scalar extension equivalence | `∃ E : CommHopfAlgCat k ≌ GaloisObject k L` and `t A : (E.functor.obj A).obj ≃ₐc[L] L ⊗[k] A` |
| Standard scalar-extended Hopf operations | The right side of `t A` uses Mathlib's tensor `HopfAlgebra L (L ⊗[k] A)`; `t A` is a bialgebra equivalence, hence a Hopf isomorphism |
| Standard action sigma(lambda tensor a) = sigma(lambda) tensor a | First conjunct, intertwining with `TensorProduct.map σ.toLinearEquiv.toLinearMap LinearMap.id` |
| Scalar extension of morphisms | Second conjunct, intertwining with `TensorProduct.map LinearMap.id f.hom.toLinearMap` |
| Quasi-inverse is the invariant algebra | `i B : E.inverse.obj B ≃ₐ[k] B.invariants`; `B.invariants` is the actual fixed-point subalgebra, with inherited operations |
| Inverse on morphisms is restriction | Third conjunct, `(i C ((E.inverse.map f).hom a)).val = f.hom.hom (i B a).val` |
| Unit a maps to 1 tensor a | Fourth conjunct, applying `i` and `t` to `(E.unitIso.app A).hom.hom a` |
| Counit lambda tensor b maps to lambda b | Fifth conjunct, applying `(E.counitIso.app B).hom.hom.hom` to the inverse `t` identification, giving `r • (i B a).val` |
| Natural Hopf unit/counit and triangle identities | `E.unitIso`, `E.counitIso` and the fields of `CategoryTheory.Equivalence`; their components are isomorphisms in the stated Hopf categories |
| Descended Hopf operations on invariants | Transport the Hopf structure on `E.inverse.obj B` through the specified algebra isomorphism `i B`; the Hopf property of `t` and the normalized Hopf counit identify their extensions with the original operations of B |
| Restriction to finitely generated algebras | The last two conjuncts identify `(algebraMap k A).FiniteType` with finite type of the extended object, and finite type of B with that of its inverse |
| Tensor meaning | Mathlib algebra tensor products, with the cited multiplication and universal property |

The equivalence is stated with explicit, normalized identifications rather than a
choice of functor left unspecified. The `i` and `t` identifications also determine
the descended operations on the literal invariant subalgebra. Indeed their tensor
extension and the counit give the map lambda tensor b maps to lambda b as a Hopf
isomorphism. Comultiplication, counit and antipode must therefore be the restrictions
and tensor descent of the original operations; faithful extension makes these unique.
No separate existence choice is hidden in a definition.

Dependency declarations read and reused:

- `Mathlib.Algebra.Field.Defs`: `Field`, full docstring and signature.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra` and its structure map, and
  `RingHom.toAlgebra` for the restricted scalar structure.
- `Mathlib.FieldTheory.Separable`: `Algebra.IsSeparable`, `IsSeparable`, and its
  algebraicity implication; `Mathlib.FieldTheory.Normal.Defs`: `Normal`;
  `Mathlib.FieldTheory.Galois.Basic`: `IsGalois`, the exact package used here.
- `Mathlib.AlgebraicGeometry.Group.Affine`: the canonical coordinate Hopf instance
  recorded by lem-sfb-affine-group-coordinate-hopf, lines 337--343. Its actual
  algebraic structures are the Mathlib ones in `CommHopfAlgCat`.
- `Mathlib.RingTheory.Coalgebra.Basic`: `Coalgebra.coassoc` and the two counit
  identities; `Mathlib.RingTheory.Bialgebra.Basic`: `counitAlgHom`, `comulAlgHom`;
  `Mathlib.RingTheory.HopfAlgebra.Basic`: the two inverse identities;
  `Mathlib.RingTheory.HopfAlgebra.Convolution`: `antipodeAlgHom`.
- `Mathlib.RingTheory.TensorProduct.Basic`: `Algebra.TensorProduct.instCommRing`,
  `tmul_mul_tmul`, `includeLeft`, `includeRight`, `ext`;
  `Mathlib.RingTheory.TensorProduct.Maps`: `productMap` and its pure-tensor formula.
- `Mathlib.RingTheory.FiniteType`: the recorded `RingHom.FiniteType`, used literally
  on algebra maps, and its equivalent `Algebra.FiniteType`.
- `Mathlib.LinearAlgebra.TensorProduct.Tower`: recorded proof inputs
  `TensorProduct.AlgebraTensorModule.distribBaseChange` and `LinearMap.baseChange`.
- `Mathlib.RingTheory.HopfAlgebra.TensorProduct`: the standard tensor Hopf structure;
  `Mathlib.Algebra.Category.CommHopfAlgCat`: objects, Hopf maps, and equivalences.
- `Mathlib.Algebra.Algebra.Subalgebra.Operations`: `FixedPoints.subalgebra`, reused
  for the invariant algebra, not redefined by a separate carrier construction.

All recorded statement dependencies are used through their Mathlib interfaces.
`Mathlib.AlgebraicGeometry.Group.Affine` and
`Mathlib.LinearAlgebra.TensorProduct.Tower` are proof imports. The proof-only node
lem-sfb-finite-galois-vector-space-descent has no recorded usable Lean module in
the read snapshot, so there is no such module to import; it is retained verbatim
in the theorem docstring and DAG proof dependencies. It is not needed to type
this statement, which uses existing tensor products and quantified equivalences.

Edge cases checked before writing and again against the final signatures:

- L = k gives the trivial action and the usual tensor-unit and invariant formulas.
- B = L has counit id; its conjugate satisfies epsilon(sigma b) = sigma(epsilon b).
  No erroneous requirement epsilon sigma = epsilon was imposed.
- A = k and B = L cover zero algebra generators; both finite-type iff clauses apply.
- Infinite-dimensional and infinitely generated Hopf algebras are included; finite
  type appears only in conclusions, never in object or field hypotheses.
- Positive characteristic, including characteristic dividing the Galois degree,
  is unrestricted; no averaging or inverse degree is present.
- The zero ring cannot carry a Hopf algebra over a field, because the unital
  counit would map it to the nonzero field. No extra nontriviality assumption is
  imposed beyond the Hopf structure already present.
- Universes u, v and w are explicitly declared. Algebras use `max u v w` so the
  scalar extension and its invariant algebra stay in the same category and w
  allows arbitrary size. There is no equality imposed on the field universes.
- All variables are bound explicitly and `autoImplicit` is false. There are no
  local notations, private definitions, or extra assumed comparison maps.

Searches performed with msearch.py and direct source searches:

- LeanFinder: "Finite Galois descent equivalence of commutative Hopf algebras
  with semilinear action invariants" returned eight field invariant/Galois-group
  results, none stating Hopf descent.
- Loogle: "CommHopfAlgCat, HopfAlgebra, Algebra.TensorProduct.map" returned zero hits.
- Mathlib grep: "baseChange|Semilinear|descent" in RingTheory/HopfAlgebra returned
  zero hits. Direct source reading found and reused the ordinary tensor structure.
- LeanSearch: "category of commutative Hopf algebras with semilinear Galois action"
  returned ordinary Hopf categories, without a semilinear Hopf category.
- New-notion LeanFinder query: "commutative Hopf algebra with a semilinear action
  of the Galois group preserving comultiplication counit antipode and category of
  equivariant Hopf homomorphisms" returned eight ordinary Hopf-algebra/category
  results. Those structures are reused inside the new notion.
- New-notion LeanSearch query: "semilinear Galois actions on commutative Hopf
  algebras and their invariant subalgebra" returned `FixedPoints.subalgebra` and
  Galois field invariant facts. The fixed-point construction is reused.
- New-notion Mathlib grep: "semilinear|Semilinear|GaloisObject|GaloisAction" in
  RingTheory/HopfAlgebra returned zero hits.
- `rg` of both WeilConjectures and Sheaf for semilinear/Hopf combinations found no
  category or theorem for this item. Searching the item id in WeilConjectures and
  dag/lean_names_upstream.json found no declaration.
- DAG search found related Hopf-action modules, rational representations,
  specialized group-algebra invariants and vector-space descent. None defines
  this category of arbitrary semilinear Hopf algebras. In particular
  MultiplicativeCharacterData defines only the specialized group-algebra model.
- `tools/blueprint_refs.py search 'semilinear Hopf'` and search 'Galois descent'
  both returned zero blueprint nodes. The ancestor command returned null, inherited
  by this item's current blueprint provenance; the new node preserves it with via.

No statement dispute or source correction is needed. Server scompile.py compiled
both modules separately, including the delivery's private dependency overlay,
with no errors or warnings. The theorem's expected sorry warning is allowed.

## New nodes

`def-sfb-semilinear-hopf-algebra` defines semilinear Hopf actions, their category
with equivariant L-linear Hopf maps, and their actual invariant subalgebra, from
Milne A.64--A.66. It uses existing `CommHopfAlgCat`, ring equivalences, tensor maps
and `FixedPoints.subalgebra`. The three search kinds and their actual logged
results are attached to its JSON record. Existing DAG Hopf-action and relative
Hopf-module definitions concern coactions/representations, not this category.
Its module is `Sheaf.FieldTheory.SemilinearHopfAlgebra`; the item gains this
single statement dependency. All eight declarations belonging to this notion
are listed in its Lean record and carry source/blueprint docstrings.

## Second reading by Q119

Author's second pass, not an independent worker review: no other agents were
started. I reopened both modules and the node, matched every hypothesis and
clause in the table above, and checked that the two final iff clauses give both
sides of the finite-generation restriction. The initial carrier implementation
of invariants was replaced by Mathlib's `FixedPoints.subalgebra` after LeanSearch
found it. Compiler feedback was repaired by completing definitional equalities
in the semilinear maps and category composition. The final category uses Hopf
maps and the tensor identification is a Hopf isomorphism, so the operation
descent is not reduced to algebra or vector-space descent. The field scalar
rule, the nontrivial counit action, and both canonical unit/counit formulas are
present. The maintainer's review supplies the independent reading.
