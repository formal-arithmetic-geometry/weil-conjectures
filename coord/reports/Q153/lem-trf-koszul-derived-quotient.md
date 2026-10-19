## Worker report

The module `Sheaf.RingTheory.KoszulDerivedQuotient` states
`RingTheory.KoszulDerivedQuotient.isIso_comparison`. Its only theorem proof is
`sorry`. It defines the concrete polynomial diagram, its ordinary tensor/quotient
isomorphism, and the canonical derived comparison as helper declarations owned by
this node; every helper is listed in `lean.declarations`. No new DAG node or
dependency replacement is required. The natural statement is unchanged.

Hypotheses and clauses, with the node and source open:

- “R a commutative ring” is `{R : Type u} [CommRing R]`; there is no Noetherian,
  flatness, proper-ideal, or nontriviality assumption.
- “r ≥ 0 and f₁,…,fᵣ ∈ R” is `{r : ℕ} (f : Fin r → R)`, including `r = 0`.
- Koszul-regularity is exactly
  `(hreg : RingTheory.Sequence.IsKoszulRegular f)` from the recorded dependency.
  This means vanishing of all positive homology of the existing Koszul complex.
- `P = ℤ[x₁,…,xᵣ]` is `PolynomialRing r = MvPolynomial (Fin r) (ULift.{u} ℤ)`.
  The universe lift is a ring-isomorphic copy of the integers, needed to apply
  the dependency's same-universe coefficient API; it puts no restriction on R.
- `P → R`, `xᵢ ↦ fᵢ`, is `polynomialMap f`, Mathlib's `MvPolynomial.eval₂Hom`
  with coefficient map `Int.castRingHom R` composed with `ULift.ringEquiv`.
- `J = (x₁,…,xᵣ)` is `variableIdeal r`, literally `Ideal.span (Set.range X)`.
- `ℤ = P/J`, with its P-module action, is `zeroSection r`, literally
  `ModuleCat.of P (P ⧸ variableIdeal r)`; `zeroSectionComplex r` places it in
  degree zero using `CochainComplex.singleFunctor`. Thus the zero-section action
  is canonical, rather than a separately assumed action on an abstract ring.
- `B = R/(f₁,…,fᵣ)` is literally `R ⧸ Ideal.span (Set.range f)` in the theorem's
  comparison target. `ordinaryModuleIso f` uses the standard balanced
  tensor/quotient isomorphism and the equality between the image of J and this
  ideal. Its pure-tensor formula is `a ⊗ (b ⊗ p̄) ↦ class(ab p(f))`.
- The derived tensor lives in `DerivedCategory (ModuleCat.{u} R)`, using the
  recorded `def-weil-abstract-derived-category`. Its independent morphism
  universe is `wR`; the P-module derived category has independent universe `wP`.
- `ringComplex R` is exactly `R[0]`. The raw functor is
  `((ModuleCat.mixedTensor (polynomialMap f)).flip.map₂CochainComplex).flip.obj
  (ringComplex R)`: the same factor order and R-action as clause (2) of
  `lem-pc-derived-tensor-second-factor-functor`.
- `L` and `ε` quantify over a left-derived functor of precisely this raw
  functor. The class binder `L.IsLeftDerivedFunctor ε (quasiIso …)` is the
  dependency's universal property, not a mathematical restriction on the ring
  or sequence: the dependency supplies such L and ε. Universal quantification
  states the conclusion for every counit-compatible choice, hence also for
  its published K-flat computation. No K-flatness of R over P is assumed.
- The canonical map is the actual composite `comparison f L ε`:
  `ε.app (zeroSectionComplex r) ≫ Q.map (ordinaryComplexIso f).hom`.
  The ordinary isomorphism removes the degree-zero second factor through
  `mapBifunctorSingle₂Iso`, moves the single complex through the module
  functor by `singleMapHomologicalComplex`, then applies `ordinaryModuleIso`.
  Thus the codomain is exactly `Q.obj (B[0])`, not an unspecified object.
- “is an isomorphism” is `IsIso (comparison f L ε)`. No arbitrary comparison
  arrow or mere existence of an unnormalized isomorphism is substituted.

Dependency declarations read and used:

- `Sheaf.RingTheory.KoszulRegularSequence`,
  `RingTheory.Sequence.IsKoszulRegular` (and the module's full four definitions).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `HasDerivedCategory`,
  `DerivedCategory`, and `DerivedCategory.Q` with the localization instance.
- `Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor`,
  `DerivedCategory.exists_derivedTensor_second_factor_functor`: read the full
  theorem, including its left-derived, exactness, K-flat computation, and
  counit compatibility clauses. Its module publicly supplies the mixed tensor.
- Proof import `Sheaf.RingTheory.RegularSequenceKoszulRegular`,
  `RingTheory.Sequence.isKoszulRegularOn_of_isWeaklyRegular`, including its
  `IsRegular` consequences.
- Proof import `Sheaf.Algebra.Homology.BoundedFlatKFlat`,
  `CochainComplex.acyclic_mapBifunctor_of_boundedAbove_flat`.
- Proof import `Sheaf.RingTheory.KoszulBaseChangeIso`,
  `ExteriorAlgebra.nonempty_koszulBaseChangeIso`, with no flatness condition.
- `ExteriorAlgebra.koszulComplex` from the existing Koszul complex dependency is
  already public through the regularity module. The recorded upstream file is
  absent from the older local checkout; I read its complete current source via
  `scompile.py --source WeilConjectures.AlgebraicGeometry.KoszulComplex`, and
  compared its signature/docstring with `Sheaf.Paper.KoszulComplex`, which is
  what the published regularity import uses. They give the same named complex.

Additional construction APIs read: `ModuleCat.mixedTensor`,
`ModuleCat.tensorEquivExtendScalars`,
`Algebra.TensorProduct.quotIdealMapEquivTensorQuot`,
`Ideal.quotientEquivAlgOfEq`, `CochainComplex.mapBifunctorSingle₂Iso`, and
`HomologicalComplex.singleMapHomologicalComplex`. These are used directly,
without replacement notions. Helper abbreviations only specialize these APIs
to the polynomial diagram already named by the item.

Source and edge checks:

I read `literature/stacks-project/cotangent.tex`, `lemma-mod-regular-sequence`
(Tag 08SJ), especially the polynomial Koszul resolution and the displayed
identity B = R tensor-derived_P ℤ. Its proof matches all five steps in the
node; those steps are reproduced in the theorem docstring.
For r=0 the ideal is zero, P is the lifted integer ring, and comparison is
scalar extension of the zero-section unit to R, followed by R ≅ R/(0).
For a unit generator the quotient and the Koszul complex are acyclic; no
nonzero quotient is required. For R=0 all constructions are defined and the
comparison is between zero objects. For R=ℤ with f=(2), the polynomial map
need not be flat and is allowed. For R=ℤ/4 with f=(2), positive Koszul homology
is nonzero, so the essential regularity hypothesis fails as expected. The
statement imposes no characteristic restriction. There is no statement fault
or STATEMENT-DISPUTED issue.

Searches made before writing:

- `msearch.py … leanfinder "A Koszul regular sequence identifies the quotient
  with derived tensor product over integer polynomials along the zero section"`:
  eight hits, including ordinary presentation tensor models and Kähler tensor
  maps; none gives the derived quotient comparison.
- `msearch.py … loogle '"Koszul"'`: zero hits.
- `msearch.py … grep 'Koszul.*resolution|derived.*quotient' RingTheory`:
  zero hits.
- `msearch.py … leansearch "The quotient by a Koszul regular sequence is
  derived base change of the zero section of the integer polynomial ring"`:
  eight hits on ordinary regularity/base change, Kähler differentials, quotient
  identity and derived localization; none states this theorem.
- `rg` of `lean/Sheaf` and upstream `WeilConjectures` for derived Koszul
  quotients, mixed tensors and Koszul augmentations found the existing mixed
  total tensor, Tor-independent augmentation, projective Koszul resolution,
  and scalar-extension interfaces. I read the closest candidates; none states
  the specified polynomial derived comparison. The ordinary quotient/tensor
  identification is reused from Mathlib rather than restated as a theorem.
- `grep -rn lem-trf-koszul-derived-quotient` in upstream `WeilConjectures`:
  no match. Declaration-name searches in upstream sources,
  `dag/lean_names_upstream.json` and project modules found no collision with
  the new namespace and helper names.

Validation: `scompile.py Q153 lem-trf-koszul-derived-quotient` compiles the file
cleanly in sandbox mode (3.1 s) and its actual library module name (3.3 s),
with no errors or warnings. The sole postponed theorem is `isIso_comparison`.
The module has explicit universes and `set_option autoImplicit false`, no
private declarations, no file-local notation, and no file-local instances.

## Second reading by Q153

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
