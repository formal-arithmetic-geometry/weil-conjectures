## Worker report

The new module `Sheaf.RingTheory.EtaleTensorSplitting` states
`Algebra.exists_etaleLocalization_tensor_splitting`, with its whole proof `sorry`.
It formalizes the node unchanged. It introduces no definitions, helper theorems,
new nodes, dependency repairs, or statement corrections.

The preceding worker's dry-run failure concerned an unchanged stage-1 node.
The kept sandbox had only dispatcher brief markers, no Lean module, node copy,
or report. This delivery supplies the stage-2 module and the `lean` record.
The existing stage-1 split and its N0/L review are retained verbatim.

Hypotheses and clauses, in the order of the node:

- The commutative rings and the homomorphism `A → C` are `(A C : Type u)` with
  `[CommRing A] [CommRing C] [Algebra A C]`; the homomorphism is `algebraMap A C`.
- Freeness with a finite basis is `[Module.Free A C] [Module.Finite A C]`.
  Mathlib's `Module.Free` means existence of a basis; for a free finite module,
  a finite basis exists (`Module.finBasis` in FreeModule/Finite/Basic.lean).
  Conversely a finite basis gives both instances. No particular basis is chosen.
- The element is `(h : C)` and `B = C_h` is the actual quotient construction
  `Localization.Away h`, with its canonical localization algebra map.
  Its `A`-algebra structure is the scalar-tower structure through `C`.
- The étaleness assumption is exactly `[AlgebraicGeometry.Etale
  (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
  (algebraMap A (Localization.Away h))))]`, using the node's scheme formulation.
- `T` is `C ⊗[A] Localization.Away h`, using Mathlib's commutative tensor ring.
  The source algebra instance of `@AlgEquiv` is explicitly
  `Algebra.TensorProduct.rightAlgebra (R := A) (A := C)
  (B := Localization.Away h)`. It sends `b` to `1 ⊗ b`, as required; the default
  tensor algebra structure through the left factor is not used for this action.
- The specified multiplication map is `Algebra.TensorProduct.productMap
  (IsScalarTower.toAlgHom A C (Localization.Away h))
  (AlgHom.id A (Localization.Away h))`. Its pure-tensor formula, by the defining
  declaration and `productMap_apply_tmul`, is `c ⊗ b ↦ algebraMap C B c * b`.
- The commutative `B`-algebra `D` is the existential `(D : Type u)
  (_ : CommRing D) (_ : Algebra (Localization.Away h) D)`.
- The isomorphism `θ` is an `AlgEquiv` over `Localization.Away h` from the tensor
  ring to `Localization.Away h × D`, with the ordinary componentwise product
  algebra structure in the codomain and the explicit right action in the source.
- `pr₁ ∘ θ = μ` is the pointwise equality `∀ t : C ⊗[A] Localization.Away h,
  (θ t).1 = Algebra.TensorProduct.productMap ... t`. This quantifies over every
  tensor, not merely pure tensors, and is precisely equality of the underlying
  maps. The node asks for no property of the complementary algebra beyond this.

Dependency declarations read and used:

- `def-weil-pbc-free-module`: `Module.Free`,
  `Mathlib.LinearAlgebra.FreeModule.Basic` (imported via FreeModule.Finite.Basic).
- `def-weil-ring-localization-away`: `Localization.Away`,
  `Mathlib.GroupTheory.MonoidLocalization.Away`, with its ring structure from
  `Mathlib.RingTheory.Localization.Away.Basic`.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `.Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme` (imported via Morphisms.Etale).
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale`,
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `lem-weil-pbc-algebra-tensor-pushout-universal-property`: its Mathlib match
  `Algebra.TensorProduct.instCommRing`, `tmul_mul_tmul`, `includeLeft`,
  `includeRight`, `productMap`, `productMap_apply_tmul`, `ext`, in
  `Mathlib.RingTheory.TensorProduct.Basic` and `.Maps`.

All other proof dependencies are Mathlib leaves. Their declarations were read:
`Algebra.Etale.baseChange` and `Algebra.FormallyEtale.iff_of_surjective`
(Mathlib.RingTheory.Etale.Basic),
`AlgebraicGeometry.Scheme.isOpenImmersion_SpecMap_localizationAway`
(Mathlib.AlgebraicGeometry.OpenImmersion), `AlgebraicGeometry.Etale.of_comp`,
`.etale_comp` and the open-immersion instance (Morphisms.Etale),
`Algebra.FinitePresentation.ker_fG_of_surjective`
(Mathlib.RingTheory.FinitePresentation),
`Ideal.isIdempotentElem_iff_of_fg` (Mathlib.RingTheory.Ideal.IdempotentFG), and
`IsLocalization.away_of_isIdempotentElem` (Localization.Away.Basic).
The proof-only imports retain these interfaces for stage 3, including transitive
imports of FinitePresentation and the localization interface.

Source checked: `literature/stacks-project/flat.tex`,
`lemma-trick-fitting-ideal` (Tag 0812), especially the paragraph asserting
`C tensor_A C_h ≅ C_h ⊕ C'` as `C_h`-algebras. The node specializes the finite
locally free source hypothesis to finite free, as already stated; it explicitly
specifies the multiplication projection. The five proof steps are reproduced
in the theorem's docstring with their DAG dependencies. Only the theorem proof
is postponed.

Edge cases checked mathematically before writing:

- Zero rings are allowed; there is no `Nontrivial` hypothesis on any ring.
  Finite bases may be empty. If `C` is zero, so are `B` and `T`; choose zero `D`.
- If `h` is nilpotent (in particular zero), `B` and `T` are zero rings, so again
  zero `D` gives the decomposition. No nonempty-spectrum restriction appears.
- If `h = 1` and `C/A` is étale, this is the usual diagonal splitting.
- If `C = A` and `h = 1`, the complementary factor may be zero. No nontrivial
  assumption on `D` incorrectly excludes this case.
- No field, characteristic, rank, or positive-rank assumption is added.
  The universe `u` is explicitly declared; the tensor and a complementary corner
  ring live in `Type u`. No relation between site universes is involved.

Searches performed with `/home/ubuntu/weil-launcher-nt/msearch.py`:

- `leanfinder`: "finite free algebra C with etale localization C_h has
  C tensor_A C_h isomorphic to C_h times D compatible with multiplication".
  Eight hits, including `Algebra.Etale.baseChange`,
  `Algebra.FormallyUnramified.elem`, and field-algebra product criteria.
  None states this localization splitting with its first projection.
- `loogle`: `Algebra.FormallyUnramified.exists_algEquiv_prod`.
  One hit, source read in Mathlib/RingTheory/Unramified/Basic.lean:334 onward.
  It assumes the whole algebra is essentially finite type and formally
  unramified, concerns its self tensor product, and does not itself give the
  node's asymmetric localization tensor with specified projection.
- `grep`: `exists_algEquiv_prod|rightAlgebra` in `RingTheory/TensorProduct`.
  Seven hits. This found exactly the existing second-factor algebra structure;
  it is used directly rather than redeclared.
- `leansearch`: "A finite free algebra C with etale localization C_h has
  C tensor_A C_h isomorphic to C_h times D with first projection multiplication".
  Eight hits, including localization tensor equivalences, etale base change,
  and `Algebra.TensorProduct.prodRight`. None is the node's theorem.
- Direct `rg` searches of upstream `WeilConjectures/` and project `lean/Sheaf/`
  for the item id, splitting/decomposition and localization names found no exact
  statement. Upstream `WeilConjectures/Mathlib/RingTheory/Etale/Section.lean`
  has `Algebra.Etale.exists_algEquiv_prod_of_algHom`; its full statement and
  docstring were read. It requires the whole source to be etale over the
  retraction's base, and additionally concludes etaleness of the complement.
  Here only `A → C_h` is assumed etale; `C tensor_A C_h` need not be etale over
  `C_h`. Thus that theorem cannot be recorded as this node's statement.
- Direct name/id searches in `dag/lean_names_upstream.json`, Mathlib, upstream,
  and the project found no existing declaration with the new theorem's name.

No statement dispute, missing notion, or unusable dependency was found.

Validation: scompile.py compiled the sandbox form and library-path form cleanly
(only the expected postponed theorem proof). Every universe and variable is
explicitly bound; no scratch `#check`, local notation, or local instance remains.

## Second reading by Q52

Author's second pass, not an independent review; the maintainer supplies the
independent review under the direct-delivery brief. Reread the node and the
compiled module together. Checked the finite-free assumption, actual away
localization, exact spectrum-etaleness instance, second-factor tensor algebra,
existence of a commutative complementary algebra and its algebra structure,
and the pointwise first-projection equality against every clause above.
The explicit `rightAlgebra` argument prevents a swap to the first-factor action.
`productMap` uses localization and the identity in the required order. All five
natural-language proof steps appear in the docstring. Found no mismatch and
made no changes to the natural statement, dependencies, or proof plan.
