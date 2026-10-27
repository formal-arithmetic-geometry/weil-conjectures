## Worker report

The module `Sheaf.RingTheory.RegularLocalComplementaryQuotientsTor` states
`RingTheory.regularLocal_complementary_quotients_tor`, with `sorry` as its only proof.
There are no definitions or helper theorems, no new nodes, and no dependency repairs.
The existing node changes only in `lean`. No statement fault or dispute was found.

Source read: `literature/stacks-project/intersection.tex`, lemma-transversal,
Tag 0B1I, especially the regular-parameter, quotient, Koszul and Tor calculation
at lines 796–849. Also checked the current blueprint ancestor
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-sf-rf-shriek-preservation/thm-trf-frobenius-fixed-points.md`
and its proof. This item is a local algebra tool in that proof, not the unit's own statement.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The commutative regular local ring is `(A : Type u) [CommRing A]
  [IsRegularLocalRing A]`. The class includes localness and Noetherianity.
  The maximal ideal and residue field are the actual Mathlib
  `IsLocalRing.maximalIdeal A` and `IsLocalRing.ResidueField A`, not extra objects.
- The nonnegative integers are `(r s : ℕ)`; `hdim` says precisely
  `ringKrullDim A = ((r+s : ℕ) : WithBot ℕ∞)`. No positive-dimension assumption occurs.
- The proper ideals are `(I J : Ideal A)` with `hI : I ≠ ⊤` and `hJ : J ≠ ⊤`.
  `Ideal`, `Ideal.span`, and `A ⧸ I` supply the node's inline ideal, generated-ideal
  and quotient notions, with their existing additive and multiplicative structures.
- Both regular local quotient assumptions are the instances
  `[IsRegularLocalRing (A ⧸ I)]` and `[IsRegularLocalRing (A ⧸ J)]`.
  `hIdim` is dimension `s`, `hJdim` dimension `r`, and
  `htrans : I ⊔ J = IsLocalRing.maximalIdeal A` is exactly `I+J=m`.
- The existential full ordered parameter family is `f : Fin (r+s) → A`.
  `IsLocalRing.IsRegularSystemOfParameters (List.ofFn f)` says both that it
  generates the maximal ideal and that its length is the Krull dimension.
- `g : Fin r → A` with `g = fun i ↦ f (Fin.castAdd s i)` is exactly the first `r`
  entries, avoiding any dependent casts in later clauses. `I = Ideal.span
  (Set.range g)` is the prefix ideal equality.
- `Sequence.IsRegular A (List.ofFn g)` gives the successive injectivities and
  nonzero final quotient over `A`. `Sequence.IsRegular (A ⧸ J)
  (List.ofFn (fun i ↦ Ideal.Quotient.mk J (g i)))` gives precisely regularity
  of the images over `A/J`, with the actual quotient-ring action.
- The original `ExteriorAlgebra.koszulComplex A r g` is used throughout.
  The `Module.Free` and `Module.Finite` conclusions in every degree express
  finite free terms, and `IsZero ...X n` for `r<n` expresses its finite length.
- `ε` is a chain map from that very complex to `(A/I)[0]`; `QuasiIso ε` says it
  is a resolution. Its degree-zero formula is the quotient map after the actual
  exterior-degree-zero equivalence `exteriorPower.zeroEquiv`. Maps to a single
  degree-zero complex have no other components to choose. This is the specified
  quotient augmentation, not an arbitrary abstract isomorphism or a new complex.
- The tensor complex is the recorded `ExteriorAlgebra.koszulComplexTensor A r g
  (A ⧸ J)`. Its homology is `IsZero` at every `0<n`.
- The chain map `δ` from this tensor complex to `(A/(I⊔J))[0]` is a
  quasi-isomorphism, with formula on all pure tensors
  `x ⊗ (a mod J) ↦ (exteriorPower.zeroEquiv x * a) mod (I⊔J)`.
  This specifies the canonical identification of degree-zero homology with
  `A/(I+J)`, while also asserting all other homology vanishes. Pure tensors
  generate the degree-zero tensor module, so the formula determines this map.
- An `A`-module isomorphism `e : A/(I⊔J) ≅ ResidueField A` is normalized by
  `e.hom (a mod (I⊔J)) = IsLocalRing.residue A a`. This renders `A/(I+J)=κ`
  through its canonical map, without assuming a definitional equality of ideals.
- Positive Tor vanishing uses the dependency's specified `CategoryTheory.Tor'`
  in `ModuleCat.{u} A`, derived in the first variable, evaluated at the two actual
  quotient modules. All statements and isomorphisms here are `A`-linear.
- Degree-zero Tor is an isomorphism `eTor` to the same residue field. The
  auxiliary existential `eTensor` is the standard quotient tensor isomorphism,
  determined on quotient pure tensors by the residue of the product. The equality
  `eTor.hom = (Functor.fromLeftDerivedZero ...).app ... ≫ eTensor.hom`
  specifies the canonical Tor-zero identification via Mathlib's actual canonical
  derived-to-underived map. It adds no input assumption or choice of map.
- Every Tor has `Module.length A ... ≠ ⊤`, so converting these lengths with
  `ENat.toNat` does not discard infinity. The last conclusion is the integer sum
  `∑ i ∈ Finset.range (r+1), (-1 : ℤ)^i * (Module.length A ...).toNat = 1`.
  This is the alternating length sum through the resolution's length `r`;
  positive Tor vanishing makes every further term zero. Thus it is exactly the
  sum in the node, including degree zero and its positive sign.

Dependency declarations read and reused:

- `def-weil-regular-scheme`: its record is the scheme clause
  `Sheaf.AlgebraicGeometry.IsRegularScheme`, which was read. Its unchanged
  `mathlib_match` explicitly supplies the ring clauses in
  `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularLocalRing` extends
  `IsLocalRing` and `IsNoetherianRing` and equates the maximal-ideal generator
  rank with dimension. This item uses only that ring clause. Importing the
  unrelated scheme interface would be unused; no dependency repair is needed.
- `def-weil-pbc-krull-dimension-ring`: `Mathlib.RingTheory.KrullDimension.Basic`,
  `ringKrullDim`, supremum of strict prime chains, valued in `WithBot ℕ∞`.
- `def-weil-pbc-regular-sequence`: `Mathlib.RingTheory.Regular.RegularSequence`,
  `RingTheory.Sequence.IsRegular` and its `IsWeaklyRegular` parent, with full
  signature and successive quotient and `top_ne_smul` conditions read.
- `def-weil-pbc-koszul-complex`:
  `WeilConjectures.AlgebraicGeometry.KoszulComplex`,
  `ExteriorAlgebra.koszulComplex` and `ExteriorAlgebra.koszulComplexTensor`;
  their actual exterior powers, contraction differentials, natural-number indexing,
  and tensor definitions were read.
- `def-weil-pbc-tor-modules`: `Mathlib.CategoryTheory.Monoidal.Tor`,
  `CategoryTheory.Tor'`; its definition by the flip of the first-variable
  left-derived tensor functor was read. The module-category monoidal and
  projective instances are imported from Mathlib. Quotients and residue field
  all have universe `u`, so this introduces no equality of independent universes.
- `def-weil-pbc-module-length`: `Mathlib.RingTheory.Length`, `Module.length`;
  this is a mathlib-status dependency whose `mathlib_match` supplies the
  declaration without a `lean` record. Read its strict-submodule-chain definition.
- `def-weil-pbc-regular-system-of-parameters`:
  `WeilConjectures.RingTheory.IsRegularSystemOfParameters`,
  `IsLocalRing.IsRegularSystemOfParameters`, span maximal ideal and length dimension.
- Proof-only imports are the recorded upstream modules
  `WeilConjectures.RingTheory.RegularLocalQuotientKernelParameters`
  (`RingTheory.exists_parameters_regularLocalQuotient`),
  `WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence`
  (`IsRegularLocalRing.isRegular_and_quotients_of_generators`), and
  `WeilConjectures.RingTheory.RegularSequenceKoszulRegular`
  (`RingTheory.Sequence.isKoszulRegularOn_of_isWeaklyRegular` and the two
  `IsRegular` corollaries). Their docstrings and full signatures were read.
  They are ordinary imports, since they serve the future proof only.

Other APIs used are Mathlib's `ChainComplex.single₀`, `QuasiIso`,
`exteriorPower.zeroEquiv`, and `Functor.fromLeftDerivedZero` (the definition in
`Mathlib.CategoryTheory.Abelian.LeftDerived`, read at lines 300–322).
No existing interface was copied. The module docstring explains the homological
conventions, and the theorem docstring contains all five DAG proof steps.

Edge cases checked before writing:

- `r=0`: `g` is empty, `I=0`, `J=m`; the Koszul complex is `A[0]`, its tensor is
  `(A/J)[0]`, and the sum over `range 1` retains the degree-zero term.
- `s=0`: the prefix is the full parameter system, `I=m`, `A/I=κ`, and `J=0`.
  The tensor calculation and sum have the expected form.
- `r=s=0`: `A` is a field, both ideals are zero and all augmentations are the
  canonical degree-zero isomorphisms. No empty-sequence case is excluded.
- Every characteristic is allowed; no characteristic or residue-field size assumption.
- Zero ring and unit ideals are excluded by the actual localness/properness
  hypotheses, as in the source. No extra nontriviality hypothesis was added.
- The ring universe is arbitrary `u`; all objects are its actual quotients,
  exterior powers or tensor modules, so the module universe convention loses no case.

Searches actually run:

- `msearch.py ... leanfinder` with query
  `Regular local quotients of complementary dimensions whose ideals sum to the maximal ideal have vanishing positive Tor`:
  eight hits, including `ringKrullDim_add_length_eq_ringKrullDim_of_isRegular`,
  `Sequence.IsWeaklyRegular.isRegular_of_isLocalizedModule_of_mem`, and
  `Algebra.FormallySmooth.iff_injective_lTensor_residueField`. None states the
  complementary-quotient Tor calculation or the full augmentation conclusions.
- `msearch.py ... loogle '"Tor", "IsRegularLocalRing"'`: zero hits.
- `msearch.py ... grep 'Tor.*[Rr]egular|[Cc]omplementary.*quotient|koszul.*quotient' RingTheory`:
  four hits, in regular-sequence permutation and regular linear-map lemmas;
  none concerns this Tor computation.
- `msearch.py ... leansearch` with query
  `For complementary regular local quotients with ideals summing to the maximal ideal positive Tor vanishes and degree zero Tor is the residue field`:
  eight hits on residue fields, local tensor detection, and dimension drop;
  none gives the lemma.
- `rg -n 'koszul.*(ugment|esolution|eroth|ero|omology)|Koszul.*(ugment|esolution)|complementary.*quotient' lean/WeilConjectures lean/Sheaf`
  found existing Koszul resolution and tensor-homology infrastructure, but not
  this statement. Read `ExteriorAlgebra.exists_koszul_projective_resolution` and
  `exists_koszul_normalized_projective_resolution`; neither gives complementary
  quotient regularity, the tensor calculation, residue identification, or length sum.
- `grep -rn 'lem-trf-regular-local-complementary-quotients-tor' lean/WeilConjectures`:
  no match. Name collision search for
  `RegularLocalComplementaryQuotientsTor|regularLocal_complementary_quotients_tor`
  in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  no match. Related Frobenius material mentions the proof strategy but does not
  provide this local-algebra theorem.

Validation: prescribed `scompile.py Q40 ...` compiled both the sandbox probe and
actual library module cleanly (2.6 seconds and 2.0 seconds), with no errors or
unexpected warnings. Earlier elaboration errors from a missing public import of
`ExteriorPower.Basic` and dot-notation parsing were repaired before this clean run.
Every universe and variable is explicit and `autoImplicit` is disabled.

## Second reading by Q40

A second self-check reopened the node and final source and matched each hypothesis
and conclusion as listed above. This is a self-check; the maintainer supplies the
independent review required by the dispatch brief. No independent worker was spawned.
The check specifically verified the prefix uses `Fin.castAdd s`, the quotient
images use `Ideal.Quotient.mk J`, the resolution is normalized by the quotient
formula, the tensor target is first `A/(I⊔J)` and then the actual residue field,
and Tor uses `Tor'`, not `Tor`. It also verified finite lengths before `toNat`,
and that the alternating sum includes degree zero when `r=0`. No mathematical
change to the node was needed. Only the missing public exterior-power import and
canonical-map syntax required correction during compilation.
