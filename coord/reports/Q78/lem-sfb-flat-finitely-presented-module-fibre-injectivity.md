## Worker report

The module `Sheaf.RingTheory.FlatFinitelyPresentedModuleFibreInjectivity` states
`Module.flat_finitePresentation_universallyInjective_of_fibres`, with one `sorry`
and no new definitions. It renders the node unchanged. Source read directly:
`literature/stacks-project/flat.tex`, equation-star (lines 7208ff) and Tag 0AT9,
lemma-universally-injective-if-flat (lines 7303ff). The source explicitly allows an
arbitrary flat A-module as target and only an A-linear arrow. The docstring records
all six proof steps of the DAG, including quotient reduction, weak association,
pure spreadout, denominator clearing, ideal-power filtration and annihilator argument.

Clause-by-clause correspondence:

- Commutative rings A and B and the homomorphism A → B: `{A : Type u}`,
  `{B : Type v}`, `[CommRing A]`, `[CommRing B]`, `[Algebra A B]`. An algebra
  structure on a commutative ring is precisely a chosen homomorphism here.
- Finite presentation of A → B: `[Algebra.FinitePresentation A B]`, the exact
  recorded declaration of def-weil-pbc-finitely-presented-algebra. Its finite
  polynomial generators and finitely generated kernel give the node's presentation.
- Multiplicative subset containing 1 and closed under multiplication:
  `(S : Submonoid B)`. No exclusion of zero is imposed.
- C = S⁻¹B: the actual quotient localization `Localization S`, with its canonical
  B-algebra and induced A-algebra, used directly as the module coefficient ring.
- N a C-module with the induced A-module structure: `[AddCommGroup N]`,
  `[Module (Localization S) N]`, `[Module A N]`,
  `[IsScalarTower A (Localization S) N]`. The tower expresses the specified
  restriction of scalars; it is not an additional mathematical hypothesis.
- N finitely presented over C: `[Module.FinitePresentation (Localization S) N]`.
  Its finite generators and finite kernel generators are equivalent to a cokernel
  C^r → C^q with finite r and q. No A-module finiteness is assumed.
- N flat over A: `[Module.Flat A N]`.
- Arbitrary flat A-module M: `{M : Type x}`, `[AddCommGroup M]`, `[Module A M]`,
  `[Module.Flat A M]`. There is no B- or C-action on M.
- A-linear arrow: `(f : N →ₗ[A] M)`, not a B-linear arrow.
- Injectivity over each prime residue field: `hfib : ∀ (p : Ideal A)
  [p.IsPrime], Function.Injective (f.rTensor p.ResidueField)`. Every prime ideal
  is included. `Ideal.ResidueField` is the residue field of A_p and Mathlib's
  `IsFractionRing (A ⧸ p) p.ResidueField` instance identifies it as Frac(A/p),
  with the canonical A-action. This is the same residue field as the node's.
- Conclusion for every A-module Q: `∀ (Q : Type (max u v w x y))
  [AddCommGroup Q] [Module A Q], Function.Injective (f.rTensor Q)`.
  `LinearMap.rTensor` is `TensorProduct.map f LinearMap.id`, so its action is
  exactly n ⊗ q ↦ f(n) ⊗ q. The fresh universe y ranges arbitrarily high, and
  the maximum avoids a test universe too small for the input data. Any smaller
  module can be lifted to that universe without changing the claim.
- No Noetherian, domain, local-ring, nonzero-ring, A-module finite-generation or
  additional target-action hypothesis appears. Universes u,v,w,x,y are explicit;
  there are no auto-bound variables and no local notation or local instances.

Dependency declarations read and used:

- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation` (public).
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat` and `Module.Flat` (public);
  the module-flatness declaration is provided by its public import of Flat.Basic.
- `Mathlib.LinearAlgebra.TensorProduct.Map`: `LinearMap.rTensor`, with the
  tensor construction in Defs and universal property in Basic (public).
- Additional existing notions: `Module.FinitePresentation` from
  `Mathlib.Algebra.Module.FinitePresentation`; `Localization` from
  `Mathlib.RingTheory.Localization.Basic`; `Ideal.ResidueField` from
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal` (all public).
- Proof-only imports match recorded proof dependencies: `Module.Flat.baseChange`
  from `Mathlib.RingTheory.Flat.Stability`; `Module.Flat.rTensor_exact` and
  `Module.Flat.lTensor_exact` already come from the public flatness dependency;
  `Ideal.nonempty_minimalPrimes` from `Mathlib.RingTheory.Ideal.MinimalPrime.Basic`;
  `Module.weakly_associated_atPrime_iff` from `Sheaf.RingTheory.WeakAssLocalization`;
  `Module.universallyInjective_of_residueField_injective` from
  `Sheaf.RingTheory.LocalUniversalInjectiveResidue`.
- The current records of lem-sfb-flat-target-ideal-quotient-injectivity-test and
  lem-sfb-local-finite-presentation-pure-spreadout have no Lean module, so there
  is no module to import for those proof-only dependencies. Neither is needed to
  type this statement. Their steps remain in the proof docstring for stage 3.

Edge cases checked before writing: the zero base ring has empty prime spectrum,
  but every unital module over it is zero, so the fibre hypothesis is harmless.
  If S contains zero, Localization S and its unital modules are zero; this is
  allowed. S = {1} gives the unlocalized case. N = 0 or Q = 0 gives injectivity
  automatically. If M = 0, the fibre condition has its intended force on N.
  Zero-generator and zero-relation finite presentations are included. No lower
  bound on rank, dimension or characteristic is introduced. Distinct ring and
  module universes are retained.

Searches performed (via the prescribed msearch.py, plus direct source searches):

- LeanFinder: "A map from a flat finitely presented module over a localized
  finitely presented algebra to a flat module injective on every residue field
  is universally injective". Eight hits, including Module.flat_of_isLocalized_span,
  Module.Flat.toAlgebra_injective and faithfully flat descent. None states the
  residue-field criterion with this localized finitely presented source.
- Loogle: "Module.Flat, Function.Injective, TensorProduct". Twelve hits, including
  Module.Flat.rTensor_preserves_injective_linearMap and tensor map injectivity.
  Those assume injectivity before tensoring; they do not prove it from fibres.
- Mathlib grep: "universally.*inject|inject.*residue|pure.*spread" in RingTheory.
  Twenty hits, mainly formal smoothness and finite-free split injectivity over a
  local ring. No match for the node.
- LeanSearch: "A map of flat modules, whose source is finitely presented over a
  localization of a finitely presented algebra, injective on every residue field
  is universally injective". Eight hits: flatness, faithfully flat descent and
  localization functor injectivity criteria; no exact statement.
- `rg` over lean/WeilConjectures and lean/Sheaf for fibre/fiber injectivity,
  universallyInjective_of, and the item id; direct item-id search of
  lean/WeilConjectures returned none. Read the nearby
  `Module.flat_finitePresentation_universallyInjective_of_closedFiber_injective`:
  it assumes local rings and a B-linear arrow to a B-module and therefore is
  a different result. The projective-source local criterion is a proof dependency,
  not the target statement. The chosen module and declaration names have no match
  in Mathlib or either project library.

No statement correction, new node, dependency-interface repair, or mathematical
statement dispute is required. All shared source files remain untouched.

Validation: scompile.py is used for every compile; dry-run and delivery use deliver2.py.
The initial parser issue with reserved Σ was fixed by using the ordinary binder S.

Final scompile.py check: both sandbox and named-library compilation passed with no
errors and no warnings. The initial compile corrected only a parser-level binder name.

## Second reading by Q78

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
