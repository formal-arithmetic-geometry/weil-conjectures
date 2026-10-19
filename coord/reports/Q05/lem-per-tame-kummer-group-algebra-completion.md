## Worker report

The module Sheaf.RingTheory.TameKummerGroupAlgebraCompletion states the reviewed
Q125 stage-1 node without changing its statement or dependency lists. That review
is a stage-1 split, not a recorded Lean statement; the previous stale-dispatch
objection therefore does not prevent this stage-2 delivery. No result is proved:
the one theorem has proof `sorry`. The three helper declarations construct the
canonical tensor-product type, commutative ring and E-algebra from Mathlib data.
Their instance bodies unfold this type and use the actual tensor-product instances.
No ring or map is chosen from an existence assertion.

Hypotheses and clauses, checked against the node and file:

- Abelian groups L and M are `CommGroup L`, `CommGroup M`, written multiplicatively
  instead of additively. `Group.FG L` and `Group.FG M` retain finite generation,
  without imposing torsion freeness. `f : L →* M` and `Function.Injective f` give
  the inclusion. Its cokernel is `M ⧸ f.range`, finite by the `Finite` binder.
- The positive integer is `N : ℕ` with `0 < N`. Annihilation of the cokernel is
  `∀ m : M, m ^ N ∈ f.range`. Invertibility in E is `IsUnit (N : E)`.
- The coefficient ring is `E : Type u` with `CommRing E`; no nonzero hypothesis is
  imposed for the first assertions. The character is `ρ : L →* Eˣ`.
- `MonoidAlgebra ℤ L` and `MonoidAlgebra ℤ M` are Mathlib's genuine integral group
  rings. `MonoidAlgebra.lift ℤ E L ((Units.coeHom E).comp ρ)` evaluates `[l]` at
  ρ(l), and `mapDomainRingHom ℤ f` sends `[l]` to `[f(l)]`. Their `toAlgebra`
  structures are used in `characterBaseChange` to form the exact tensor product
  `TensorProduct (MonoidAlgebra ℤ L) E (MonoidAlgebra ℤ M)`. Its ring and E-algebra
  instances are the standard tensor instances, so multiplication is componentwise
  on pure tensors and the coefficient map is `a ↦ a ⊗ 1`.
- `Nonempty (Module.Basis (M ⧸ f.range) E (characterBaseChange ...))` states
  freeness with a basis indexed by the finite quotient. This is exactly finite
  freeness of the stated rank and retains the zero-ring case.
- `Algebra.Etale E (characterBaseChange ...)` states E → U is étale. This is the
  affine ring version of the recorded scheme étale definition, related by
  `HasRingHomProperty @AlgebraicGeometry.Etale RingHom.Etale` in Mathlib's Etale
  module, and `RingHom.etale_algebraMap`.
- The remaining conclusion is universally conditional on `Nontrivial E`,
  `IsNoetherianRing E`, `IsLocalRing E`, and
  `IsAdicComplete (IsLocalRing.maximalIdeal E) E`. These hypotheses are not required
  for the earlier finite-free and étale conclusions.
- The index is exactly `{m : Ideal U // m.IsMaximal}`, explicitly finite in the
  conclusion. `A` assigns each index a bundled commutative ring. Existential
  `algebras`, `locals`, and `localMaps` supply the E-algebra and local-ring
  structures and the induced local coefficient homomorphisms. These witnesses
  occur in the conclusion, not as additional hypotheses.
- `e : U ≃ₐ[E] (∀ i, A i)` gives the product as an E-algebra. Each factor is
  `Nontrivial`, `IsNoetherianRing`, local via `locals`, and complete at its own
  maximal ideal. `Module.Finite E (A i) ∧ Algebra.Etale E (A i)` is finite étale.
- The comap under `(Pi.evalRingHom ... i).comp e.toRingHom` of the factor's
  maximal ideal equals `i.1`. Thus the maximal-ideal index has its specified
  mathematical identification, rather than being an arbitrary finite label set.
- The canonical residue extension is available from the existential local
  coefficient maps, using Mathlib's `IsLocalRing.ResidueField` algebra instance.
  `Module.Finite` over `IsLocalRing.ResidueField E` states finiteness, and
  `Algebra.IsSeparable` states algebraic separability for that same extension.

Dependency declarations read and used:

- def-weil-pbc-module-tensor-product: `TensorProduct`, in
  Mathlib.LinearAlgebra.TensorProduct.Defs; its ring form and scalar algebras are
  Mathlib.RingTheory.TensorProduct.Basic, exported by the étale imports.
- lem-weil-pbc-algebra-tensor-pushout-universal-property:
  `Algebra.TensorProduct.instCommRing`, `tmul_mul_tmul`, `includeLeft`,
  `includeRight`, `productMap`, `ext` (Mathlib.RingTheory.TensorProduct.Basic/Maps).
- def-weil-etale-morphism: `AlgebraicGeometry.Etale`,
  Mathlib.AlgebraicGeometry.Morphisms.Etale, via its affine ring-map equivalence.
- def-weil-pbc-noetherian-ring: `IsNoetherianRing`,
  Mathlib.RingTheory.Noetherian.Defs.
- def-weil-pbc-adic-completion: `IsAdicComplete`,
  Mathlib.RingTheory.AdicCompletion.Basic, equivalent to bijectivity of the
  canonical map into `AdicCompletion`.
- def-weil-pbc-free-module: Mathlib.LinearAlgebra.FreeModule.Basic, `Module.Free`
  and `Module.Basis`. The indexed basis gives the freeness and precise rank together.
- def-weil-residue-field: Mathlib.AlgebraicGeometry.ResidueField,
  `Scheme.residueField`, whose defining expression is `IsLocalRing.ResidueField`
  of the stalk; the corresponding local-algebra residues here use that same
  quotient construction directly, not a second residue-field notion.
- def-weil-pbc-separable-algebraic-extension: `Algebra.IsSeparable`,
  Mathlib.FieldTheory.Separable.

The proof-only imports include all the already recorded proof interfaces:
`Algebra.finite_over_complete_local_product` (Sheaf.RingTheory.FiniteOverCompleteLocalProduct),
`Scheme.finite_product_principal_open`
(Sheaf.AlgebraicGeometry.Morphisms.FiniteProductPrincipalOpen),
`AdjoinRoot.powerBasis'`, `StandardEtalePair`, étale composition/open immersion,
scheme coproducts, integral maximal-ideal contraction, and étale residue
separability. Mathlib's scheme étale import transitively supplies the scheme
coproducts and FormallyUnramified residue instance. Completion definitions are
already imported publicly. The docstring gives all seven reviewed proof steps,
combining the cyclic-tower construction and its derivative argument into steps 2–3.

Edge cases checked before and after writing:

- L=M, and the trivial groups: quotient has one element, U=E; no generators are
  needed for the étale tower.
- Torsion groups: for example Z/2 → Z/4 and E=Z_3 with a compatible unit character;
  no torsion-free, free-group or splitting hypothesis appears.
- E=0: permitted for the first assertions, excluded only in the conditional local
  conclusion. The coset-indexed basis makes sense over the zero ring.
- N=0 is excluded explicitly; N=1 forces quotient trivial. Positive characteristic
  is allowed precisely when N maps to a unit; bad characteristics are excluded.
- Nonzero complete local E gives a nonzero U from the basis, so the maximal-ideal
  product cannot be an empty product. Factor nontriviality is explicitly included.
- Independent universes u, v, w remain independent. The tensor product lives in
  `Type (max u w)`, since the balancing ring's universe does not enlarge its carrier;
  factors are in that same universe, without forcing any universe equality.

Searches made:

- msearch.py leanfinder: "Base change of integral group algebras along a character
  for finite index abelian groups is finite free etale". Eight hits include
  Algebra.Etale.baseChange and Algebra.Etale.iff_exists_algEquiv_prod. The former
  presupposes étaleness of the original algebra; the latter assumes a field base.
  Neither states the finite-index character algebra assertion.
- msearch.py loogle: `"MonoidAlgebra", "Etale"`; zero hits.
- msearch.py grep: `MonoidAlgebra.*[Ee]tale|[Ee]tale.*MonoidAlgebra`; zero hits.
- rg on the source WeilConjectures and lean/Sheaf and upstream-name index:
  `group.?[Aa]lgebra|characterBaseChange|tame_group_algebra`, and exact node id.
  No matching theorem or character base-change definition. Existing completed
  augmentation algebras, monoid normality modules and representation modules have
  different constructions; CompletedInvertibleKummerMonoidExtension only cites
  this node in its proof. Read MonoidAlgebra.lift and mapDomainRingHom signatures
  and their implementations before using these canonical maps.
- msearch.py leansearch: "A finite index inclusion of abelian groups with invertible
  quotient exponent gives a finite free etale character base change of integral
  group algebras". Eight hits: subgroup finite-index/finite-quotient equivalences,
  quotient Fintype instances, and Algebra.Etale.baseChange. No hit establishes
  étaleness or finite freeness of this character algebra. The returned signatures
  were read. The node's earlier LeanSearch records give the same conclusion.

Source read: ILO VI 2.2 printed p.72 (physical PDF page 78), including the
invertible-exponent diagonalizable group action and the groupification cokernel.
The complete-local portion follows the reviewed Stacks 0325 / 02G8 proof recorded
in this node, with the actual FiniteOverCompleteLocalProduct interface read.
No statement correction, disputed statement, new node or dependency repair is needed.

## Second reading by Q05

Author self-check, with the current node and module open; independent maintainer
review remains required. Rechecked each binder and each conjunction against the
mapping above. Multiplicative notation changes neither the abelian group nor
cokernel. The conditional local hypotheses occur only after the unconditional
basis and étaleness statements. The product is an E-algebra equivalence and the
maximal-ideal comap clause ties each index to its projection. Residue finiteness
and separability use the canonical coefficient-induced algebra. No conclusion
assumes the groups are torsion free. During compilation the type universe was
corrected from max u v w to the actual tensor carrier max u w; no input universe
was restricted. Instance definitions were unfolded before synthesis to keep the
canonical balancing structures fixed. No mathematical mismatch remains.
