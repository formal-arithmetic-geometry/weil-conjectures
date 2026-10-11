## Worker report

The module `Sheaf.RingTheory.SymmetricAlgebraBaseChange` states
`SymmetricAlgebra.baseChange_bijective` and the principal-localization clause as
`SymmetricAlgebra.exists_away_baseChange`. Both proofs are `sorry`; no definitions
or proof-bearing instances are introduced. The six steps of the node's proof are
included in the declaration docstrings.

Hypotheses and clauses, in node order:

- Commutative rings R and S are `{R : Type u} {S : Type v}` with `[CommRing R]`
  and `[CommRing S]`; the specified ring homomorphism is encoded by `[Algebra R S]`.
  Every commutative-ring homomorphism supplies this structure, with no injectivity,
  nontriviality, flatness, or finiteness condition.
- The arbitrary R-module M is `{M : Type w} [AddCommGroup M] [Module R M]`.
  The three universes are explicit and independent; no size case is excluded.
- The source symmetric algebra is `SymmetricAlgebra R M`, and its inclusion is
  `SymmetricAlgebra.ι R M`; the target is
  `SymmetricAlgebra S (S ⊗[R] M)` with inclusion `ι S (S ⊗[R] M)`.
  These are the exact Mathlib notions recorded by the symmetric-algebra dependency.
- The R-algebra homomorphism β is a binder with type
  `SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra S (S ⊗[R] M)`.
  Its defining generator identity is the hypothesis `hβ`:
  `∀ m : M, β (ι R M m) = ι S (S ⊗[R] M) (1 ⊗ₜ[R] m)`.
  This is the node's introduction of β, not an added restriction on R, S or M.
  Existence and uniqueness of this β are already the symmetric-algebra universal
  property; no second definition of it is needed.
- The indicated S-algebra homomorphism is
  `AlgHom.liftEquiv R S (SymmetricAlgebra R M)
    (SymmetricAlgebra S (S ⊗[R] M)) β`.
  By Mathlib's `AlgHom.liftEquiv_tmul`, its value on `s ⊗ₜ a` is `s • β a`,
  precisely multiplication by the scalar s in the target algebra.
- Being an isomorphism is `Function.Bijective` of this bundled algebra homomorphism.
  Bijectivity of an algebra homomorphism is equivalent to having an algebra inverse
  (`AlgEquiv.ofBijective`); thus this states the isomorphism of the specified map,
  rather than an unspecified isomorphism of the two objects.
- For the parenthetical localization case, `exists_away_baseChange` binds any `f : R`.
  `Localization.Away f` is R_f, and
  `LocalizedModule (Submonoid.powers f) M` is M_f.
  The source algebra is
  `Localization (Algebra.algebraMapSubmonoid (SymmetricAlgebra R M) (Submonoid.powers f))`.
  The image of the powers submonoid is the powers of the image of f, so this is
  literally Sym_R(M)_f. Mathlib's canonical `IsLocalization.localizationAlgebra`
  instance supplies its R_f-algebra structure. The conclusion existentially binds
  an `≃ₐ[Localization.Away f]` to `SymmetricAlgebra (Localization.Away f) M_f`.
  The final generator identity sends the localization of `ι R M m` to the inclusion
  of `LocalizedModule.mkLinearMap (Submonoid.powers f) M m`, namely m/1.
  This fixes the canonical localization comparison (its values on fractions follow
  from R_f-linearity and the algebra universal properties).

Dependency declarations read and used:

- `lem-weil-pbc-symmetric-algebra-universal-property`: all recorded declarations in
  `Mathlib.LinearAlgebra.SymmetricAlgebra.Basic`: `SymmetricAlgebra`,
  `SymmetricAlgebra.ι`, `SymmetricAlgebra.lift`, `SymmetricAlgebra.lift_ι_apply`,
  `SymmetricAlgebra.algHom_ext`. The quotient and commutative-ring instances were
  also read. Its notation in the theorem is exactly that dependency's Mathlib match.
- `lem-weil-pbc-algebra-tensor-base-change-universal-property`:
  `AlgHom.liftEquiv`, `AlgHom.liftEquiv_tmul`, `AlgHom.liftEquiv_symm_apply` in
  `Mathlib.RingTheory.TensorProduct.Basic`. The node's record reverses the written
  orientation in its prose, but the equivalence itself is fully usable: forward
  direction in the pinned file is from R-algebra maps to S-algebra maps.
  The extensionality declaration is `Algebra.TensorProduct.ext_ring`, not the
  node's prose spelling `AlgHom.ext_ring`; the usable universal property suffices.
- `lem-weil-pbc-module-base-change-universal-property`:
  `LinearMap.liftBaseChangeEquiv`, `LinearMap.liftBaseChange`,
  `LinearMap.liftBaseChange_tmul`, `LinearMap.liftBaseChangeEquiv_symm_apply`.
  These are actually in `Mathlib.RingTheory.TensorProduct.Basic`, not the recorded
  `Mathlib.LinearAlgebra.TensorProduct.Basic` file. Full signatures and docstrings
  were read in their actual file. They explain the inverse in the theorem docstring.
- `lem-weil-pbc-localization-tensor`:
  `IsLocalization.Away.tensorEquiv`, `IsLocalization.Away.tensorRightEquiv`,
  `LocalizedModule.equivTensorProduct` and its pure-tensor formulas, all in
  `Mathlib.RingTheory.Localization.BaseChange`. They give precisely the algebra
  and module identifications used in the localization corollary. The canonical
  algebra-on-localization instance was read in `Mathlib.RingTheory.Localization.Basic`.

Edge cases checked mathematically before writing:

- M = 0: both symmetric algebras reduce to their coefficient rings; the comparison
  is S ⊗_R R ≅ S. No nonzero or finite-generation hypothesis is imposed.
- A zero ring R or S is permitted; the resulting module/algebra collapses as
  required. In particular the zero ring S is not excluded by a `Nontrivial` instance.
- Localization f = 0 collapses both sides to the zero algebra; f = 1 is the
  identity localization; nilpotent f also collapses both sides. The statement never
  assumes f nonzero, regular, or invertible.
- All characteristics and modules of arbitrary rank are included.

Searches performed (2026-10-11):

- `msearch.py ... leanfinder`: "The symmetric algebra commutes with extension of
  scalars S tensor_R Sym_R M is Sym_S of S tensor_R M". Eight results, including
  `IsSymmetricAlgebra.comp_equiv`, `SymmetricAlgebra.isSymmetricAlgebra_ι`, and
  symmetric tensor-power definitions; none state base change.
- `msearch.py ... loogle`: `SymmetricAlgebra, TensorProduct`. Only
  `SymmetricAlgebra.comul_ι`; no match.
- `msearch.py ... leansearch`: "symmetric algebra commutes with base change of rings".
  Service unavailable (Internal Server Error); no result to evaluate.
- `msearch.py ... grep`: `SymmetricAlgebra.*(baseChange|localiz)|baseChange.*SymmetricAlgebra`.
  Zero Mathlib hits.
- `rg` of `SymmetricAlgebra|symmetric.algebra` in the upstream `WeilConjectures`
  and project's `lean/Sheaf`: no base-change declaration; project citations in
  QuasiCoherentSymmetricAlgebra, ImprovePresentation and other modules only use
  this DAG node in proof descriptions. `rg` of the item id in upstream finds none.
- `rg` for the two proposed full-name suffixes and `SymmetricAlgebra.*baseChange`
  in `dag/lean_names_upstream.json`, Mathlib, upstream and Sheaf finds no collision.

Source checked at [Stacks 0C6F](https://stacks.math.columbia.edu/tag/0C6F), because
this machine's literature checkout has no `stacks-project/algebra.tex`. It explicitly
states the symmetric-algebra localization conclusion. Its hint links to
[Stacks 00DL](https://stacks.math.columbia.edu/tag/00DL), the tensor-localization lemma;
the node's source says 00DE, which is actually the tensor–Hom adjunction. This is a
source citation fault, not a statement fault. The node statement is unchanged.
No STATEMENT-DISPUTED issue, no new nodes, and no dependency modules are needed.

Validation: the module compiled cleanly on the server with `scompile.py T1
lem-weil-pbc-symmetric-algebra-base-change <module>` (1.4 seconds), with no errors
or warnings. Delivery dry run is the next gate; the independent second reader will
write the second-reading section and deliver.

## Second reading by T1

I read the node statement, its Stacks source place, and the module
`Sheaf.RingTheory.SymmetricAlgebraBaseChange` independently.

- The commutative rings `R` and `S`, the `R`-algebra structure on `S`, and the
  arbitrary `R`-module `M` render as `{R : Type u} {S : Type v} {M : Type w}` with
  `[CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M]`.
  No injectivity, nonzero, flatness, finite-generation, or characteristic assumption
  is present.
- The source and target symmetric algebras render as
  `SymmetricAlgebra R M` and `SymmetricAlgebra S (S ⊗[R] M)`, with inclusions
  `ι R M` and `ι S (S ⊗[R] M)`, using the recorded symmetric-algebra dependency.
- The map `β` and its generator condition render exactly as the explicit
  `R`-algebra homomorphism binder and `hβ : ∀ m, β (ι R M m) =
  ι S (S ⊗[R] M) (1 ⊗ₜ[R] m)`.
- The comparison map renders exactly as
  `AlgHom.liftEquiv R S (SymmetricAlgebra R M)
  (SymmetricAlgebra S (S ⊗[R] M)) β`, and the conclusion is its
  `Function.Bijective`, matching the stated `S`-algebra isomorphism and formula
  `s ⊗ a ↦ s • β a`.
- The localization parenthetical renders as an existential algebra equivalence from
  `Localization (Algebra.algebraMapSubmonoid (SymmetricAlgebra R M)
  (Submonoid.powers f))` over `Localization.Away f` to
  `SymmetricAlgebra (Localization.Away f)
  (LocalizedModule (Submonoid.powers f) M)`, for arbitrary `f : R`. This is the
  precise Mathlib form of `Sym_R(M)_f ≅ Sym_{R_f}(M_f)`.

The edge cases remain covered: `M = 0`, zero rings, arbitrary characteristics and
ranks, and `f = 0`, `f = 1`, or nilpotent `f`; no `Nontrivial`, regularity, or
invertibility hypothesis was introduced. Universes are independent and no index
set or scheme is involved.

I checked Stacks Lemma 0C6F: it states localization of tensor, symmetric, and
exterior algebras for any multiplicative subset and module, with proof omitted.
The node additionally records the standard universal-property proof of general base
change. The node's citation to 00DE is bibliographically imprecise (00DE is the
Hom-tensor adjunction), but this does not alter the node's mathematical statement.

I repeated the existing-definition searches with `msearch.py` (LeanFinder,
Loogle, and LeanSearch) and `rg` over Mathlib, `WeilConjectures`, `lean/Sheaf`, and
`dag/lean_names_upstream.json`; no declaration of symmetric-algebra base change or
its localization was found. The recorded dependency declarations are the actual
Mathlib universal-property and localization declarations and are used directly.

One mismatch was found and repaired. The worker's `exists_away_baseChange` had an
extra conjunct asserting the image of every generator. The node's parenthetical
requires only the localization isomorphism, so that conjunct strengthened the
statement (H3). I removed the generator equation from the theorem conclusion and
updated its docstring; the main `baseChange_bijective` signature was already exact.
No other mismatch, hollow definition, unbound variable, or duplicate notion was
found.
